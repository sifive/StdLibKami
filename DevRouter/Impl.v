Require Import Kami.AllNotations.
Require Import StdLibKami.DevRouter.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section SimpleDevRouter.
  Context `{DevRouterParams}.
  Class DevRouterImplParams :=
    {
      (* A bool register indicating whether we've routed a response
         from a device back to the guy to the left TODO: what's his
         name *)
      routed: string;
    }.
  
  Section withParams.
    Context `{DevRouterImplParams}.
    Open Scope kami_expr_scope.
    Open Scope kami_action_scope.
    Definition pollRuleGenerator (dev: Fin.t numDevices): ActionT ty Void :=
      Read alreadyRouted: Bool <- routed;
      If !#alreadyRouted then (
        LETA resp: Maybe respK <- (nth_Fin devices dev).(devPoll);
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
    Definition pollRules := map pollRuleGenerator (getFins numDevices) ++ [pollingDone].
    
    Definition devRouterReqGen (dev: Fin.t numDevices) (req: ty reqK): ActionT ty Bool :=
      LETA res: Bool <- (nth_Fin devices dev).(devReq) req;
      Ret #res.
    Definition devRouterReqs := map devRouterReqGen (getFins numDevices). 

    Definition simpleDevRouter: DevRouter := Build_DevRouter pollRules devRouterReqs.
  End withParams.
End SimpleDevRouter.
