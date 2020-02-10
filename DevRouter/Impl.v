Require Import Kami.AllNotations.
Require Import StdLibKami.DevRouter.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section SimpleDevRouter.
  Context `{DevRouterParams}.
  Local Definition routed := (StdLibKami.DevRouter.Ifc.name ++ ".routed")%string.
  
  Section withParams.
    Open Scope kami_expr_scope.
    Open Scope kami_action_scope.
    Section withTy.
      Context (ty: Kind -> Type).
      Definition pollRuleGenerator (clientCallback: forall {ty}, ty respK -> ActionT ty Void) (dev: Fin.t numDevices): ActionT ty Void :=
      System [
        DispString _ "[DevRouter.pollRuleGenerator]\n"
      ];
      Read alreadyRouted: Bool <- routed;
      If !#alreadyRouted then (
        LETA resp: Maybe respK <- (nth_Fin devices dev).(memDevicePoll);
        LET respDat: respK <- (#resp @% "data");
        If (#resp @% "valid") then (
            System [
              DispString _ ("[DevRouter.pollRuleGenerator] forwarding response from device: " ++ nat_decimal_string (proj1_sig (Fin.to_nat dev)) ++ "\n")
            ];
            LETA _ <- clientCallback respDat;
            Write routed: Bool <- $$true;
            Retv
        );
        Retv
      );
      Retv.
    Definition pollingDone: ActionT ty Void :=
      System [
        DispString _ "[DevRouter.pollingDone]\n"
      ];
      Write routed: Bool <- $$false;
      Retv.

    (* TODO: NOTE: LLEE: calls to memDeviceReq etc will be actual method calls in synth ver. *)
    Definition devRouterReq
      (req: ty DevRouterReq)
      : ActionT ty Bool :=
      System [
        DispString _ "[DevRouter.devRouterReq]\n"
      ];
      GatherActions (map (fun i =>
                            LET req_real: reqK <- #req @% "req";
                            If ($(proj1_sig (Fin.to_nat i)) == #req @% "tag")
                            then
                              System [
                                DispString _ "[DevRouter.devRouterReq] sending request to device: ";
                                DispHex (#req @% "tag");
                                DispString _ "\n"
                              ];
                              (nth_Fin devices i).(memDeviceReq) req_real
                            else Ret $$false as ret;
                            Ret #ret
                         ) (getFins numDevices)) as accepted; Ret (CABool Or accepted).
    End withTy.
    Definition pollRules (clientCallback: forall ty, ty respK -> ActionT ty Void) := (map (fun dev ty => pollRuleGenerator ty clientCallback dev) (getFins numDevices)) ++ [pollingDone].

    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    Definition regs: list RegInitT := makeModule_regs ( Register routed: Bool <- false ).
    
    Instance simpleDevRouter
      :  DevRouter
      := {| DevRouter.Ifc.regs := regs ;
            DevRouter.Ifc.regFiles := nil ;
            DevRouter.Ifc.devRouterReq := devRouterReq;
            DevRouter.Ifc.pollRules := pollRules |}.

  End withParams.
End SimpleDevRouter.
