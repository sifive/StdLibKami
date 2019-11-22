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
    
    Definition devRouterReqGen (dev: Fin.t numDevices) (req: ty reqK): ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                                                                "info" :: reqResK } :=
      LETA res: STRUCT_TYPE { "ready" :: Bool;
                              "info" :: reqResK } <- (nth_Fin devices dev).(devReq) req;
      Ret #res.
    End withTy.
    Definition pollRules := (map (fun dev ty => pollRuleGenerator ty dev) (getFins numDevices)) ++ [pollingDone].
    Definition devRouterReqs := map (fun dev ty => devRouterReqGen ty dev) (getFins numDevices).
    
    Definition simpleDevRouter: DevRouter := Build_DevRouter pollRules devRouterReqs.
  End withParams.
End SimpleDevRouter.
