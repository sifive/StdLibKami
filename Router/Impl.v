Require Import Kami.AllNotations.
Require Import StdLibKami.Router.Ifc.

Section Impl.
  Context {params: Params}.
  
  Local Definition routedReg := (Router.Ifc.name ++ ".routedReg")%string.
  
  Local Open Scope kami_expr_scope.
  Local Open Scope kami_action_scope.
  
  Section withTy.
    Context (ty: Kind -> Type).
    
    Local Definition pollRuleGenerator (clientCallback: forall {ty}, ty respK -> ActionT ty Void) (dev: Fin.t numDevices): ActionT ty Void :=
      System [
        DispString _ "[Router.pollRuleGenerator]\n"
      ];
      Read alreadyRoutedReg: Bool <- routedReg;
      If !#alreadyRoutedReg then (
        LETA resp: Maybe respK <- (nth_Fin devices dev).(devicePoll);
        LET respDat: respK <- (#resp @% "data");
        If (#resp @% "valid") then (
            System [
              DispString _ ("[Router.pollRuleGenerator] forwarding response from device: " ++ natToHexStr (proj1_sig (Fin.to_nat dev)) ++ "\n")
            ];
            LETA _ <- clientCallback respDat;
            Write routedReg: Bool <- $$true;
            Retv
        );
        Retv
      );
      Retv.

    Local Definition pollingDone: ActionT ty Void :=
      System [
        DispString _ "[Router.pollingDone]\n"
      ];
      Write routedReg: Bool <- $$false;
      Retv.

    Local Definition sendReq (req: ty OutReq) : ActionT ty Bool :=
      System [
        DispString _ "[Router.req]\n"
      ];
      GatherActions (map (fun i =>
                            LET req_real: reqK <- #req @% "req";
                            If ($(proj1_sig (Fin.to_nat i)) == #req @% "dtag")
                            then
                              System [
                                DispString _ "[Router.req] sending request to device: ";
                                DispHex (#req @% "dtag");
                                DispString _ "\n"
                              ];
                              (nth_Fin devices i).(deviceReq) req_real
                            else Ret $$false as ret;
                            Ret #ret
                         ) (getFins numDevices)) as accepted; Ret (@Kor _ Bool accepted).
  End withTy.
  
  Local Definition pollRules (clientCallback: forall ty, ty respK -> ActionT ty Void) :=
    (map (fun dev ty => pollRuleGenerator ty clientCallback dev) (getFins numDevices)) ++ [pollingDone].

  Local Definition regs: list RegInitT := makeModule_regs ( Register routedReg: Bool <- false )%kami.
  
  Definition impl: Ifc
    := {| Ifc.regs := regs ;
          Ifc.regFiles := nil ;
          Ifc.sendReq := sendReq;
          Ifc.pollRules := pollRules |}.

End Impl.
