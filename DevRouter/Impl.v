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

    Definition devRouterReqs (req: ty (STRUCT_TYPE {
                                           "dtag" :: Bit (Nat.log2_up numDevices);
                                           "req" :: reqK})): ActionT ty Bool :=
      GatherActions (map (fun i =>
                            LET req_real: reqK <- #req @% "req";
                            If ($(proj1_sig (Fin.to_nat i)) == #req @% "dtag")
                            then (nth_Fin devices i).(devReq) req_real
                            else Ret $$false as ret;
                            Ret #ret
                         ) (getFins numDevices)) as accepted; Ret (CABool Or accepted).
    End withTy.
    Definition pollRules := (map (fun dev ty => pollRuleGenerator ty dev) (getFins numDevices)) ++ [pollingDone].
    
    Definition simpleDevRouter: DevRouter := Build_DevRouter pollRules devRouterReqs.
  End withParams.
End SimpleDevRouter.
