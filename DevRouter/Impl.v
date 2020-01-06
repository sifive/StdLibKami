Require Import Kami.AllNotations.
Require Import StdLibKami.DevRouter.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section SimpleDevRouter.
  Context `{DevRouterParams}.
  Class DevRouterImplParams :=
    {
      (* A bool register indicating whether we've routed a response
         from a device yet *)
      routed: string;
    }.
  
  Section withParams.
    Context `{DevRouterImplParams}.
    Open Scope kami_expr_scope.
    Open Scope kami_action_scope.
    Section withTy.
      Context (ty: Kind -> Type).
      Definition pollRuleGenerator (clientCallback: forall {ty}, ty respK -> ActionT ty Void) (dev: Fin.t numDevices): ActionT ty Void :=
      Read alreadyRouted: Bool <- routed;
      If !#alreadyRouted then (
        LETA resp: Maybe respK <- (nth_Fin devices dev).(memDevicePoll);
        LET respDat: respK <- (#resp @% "data");
        If (#resp @% "valid") then (
            LETA _ <- clientCallback respDat;
            Write routed: Bool <- $$true;
            Retv
        );
        Retv
      );
      Retv.
    Definition pollingDone: ActionT ty Void :=
      Write routed: Bool <- $$false;
      Retv.

    Definition devRouterReq
      (req: ty DevRouterReq)
      : ActionT ty Bool :=
      GatherActions (map (fun i =>
                            LET req_real: reqK <- #req @% "req";
                            If ($(proj1_sig (Fin.to_nat i)) == #req @% "tag")
                            then (nth_Fin devices i).(memDeviceReq) req_real
                            else Ret $$false as ret;
                            Ret #ret
                         ) (getFins numDevices)) as accepted; Ret (CABool Or accepted).
    End withTy.
    Definition pollRules (clientCallback: forall ty, ty respK -> ActionT ty Void) := (map (fun dev ty => pollRuleGenerator ty clientCallback dev) (getFins numDevices)) ++ [pollingDone].

    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    Definition regs: list RegInitT := makeModule_regs ( Register routed: Bool <- false ).
    
    Instance simpleDevRouter: DevRouter := Build_DevRouter regs pollRules devRouterReq.
  End withParams.
End SimpleDevRouter.
