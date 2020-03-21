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
      Read alreadyRoutedReg: Bool <- routedReg;
      If !#alreadyRoutedReg then (
        LETA resp: Maybe respK <- (nth_Fin devices dev).(devicePoll);
        LET respDat: respK <- (#resp @% "data");
        If (#resp @% "valid") then (
            LETA _ <- clientCallback respDat;
            Write routedReg: Bool <- $$true;
            Retv
        );
        Retv
      );
      Retv.

    Local Definition pollingDone: ActionT ty Void :=
      Write routedReg: Bool <- $$false;
      Retv.

    Local Definition sendReq (req: ty OutReq) : ActionT ty Bool :=
      GatherActions (map (fun i =>
                            LET req_real: reqK <- #req @% "req";
                            If ($(proj1_sig (Fin.to_nat i)) == #req @% "dtag")
                            then
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
