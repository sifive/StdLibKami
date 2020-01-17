Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.Reorderer.Ifc.
Section Reorderer.
  Context `{ReordererParams}.
  Class ReordererImplParams :=
    {
      (* Methods for interacting with the response buffer (holding Maybe
     Insts). *)
      rfRead: string;
      rfWrite: string;
      (* methods for interacting with the address memory, which keeps
     track of the address each request corresponds to *)
      arfRead: string;
      arfWrite: string;
      handlingName: string;
      givingName: string;
    }.

  Section withParams.
    Context `{ReordererImplParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.
    
    Section withTy.

    (* Conceptual rule *)
   Definition handle
     (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void)
     ty
     : ActionT ty Void
     := Read handling: ReordererReqId <- handlingName;
        Call MRes: Maybe respK <- rfRead(#handling: ReordererReqId);
        Call req: ReordererReq <- arfRead(#handling: ReordererReqId);
        LET resp
          :  ReordererRes
          <- STRUCT {
               "vaddr" ::= #req @% "data";
               "inst"  ::= #MRes @% "data"
             };
        If #MRes @% "valid"
          then
            LETA _ <- prefetcherCallback (resp : ty ReordererRes);
            Write handlingName <- #handling + $1;
            Retv;
        Retv.

   (* Action the arbiter will call when giving us (the reorderer) the
      response to a prior request *)
   Definition reordererCallback ty (resp: ty ReordererArbiterRes): ActionT ty Void :=
    LET idx: ReordererReqId <- #resp @% "tag";
    LET res: respK <- #resp @% "resp";
    Call rfWrite(STRUCT { "addr" ::= #idx;
                          "data" ::= Valid #res } : WriteRq reqIdSz (Maybe respK));
    Retv.

   (* TODO: Completely broken. *)
   (* Action the prefetcher will ultimately use to make an order-preserving request for instructions at some address *)
   Definition sendReq
     ty
     (memReq
       : ty ReordererArbiterReq ->
         ActionT ty ReordererArbiterImmRes)
      (p: ty ReordererReq)
     :  ActionT ty ReordererImmRes
     := Read giving: ReordererReqId <- givingName;
        Read handling: ReordererReqId <- handlingName;
        LET arbiterReq
          :  ReordererArbiterReq
          <- STRUCT {
               "tag" ::= #giving;
               "req" ::= #p @% "req"
             };
        If (#giving + $1) != #handling
          then (* we can give a new reqid without forgetting the next one to service *)
            LETA res <- memReq arbiterReq;
            If #res @% "ready"
              then
                Write givingName: ReordererReqId <- #giving + $1;
                Call rfWrite(STRUCT { "addr" ::= #giving;
                                      "data" ::= Invalid } : WriteRq reqIdSz (Maybe respK));
                Call arfWrite
                  (STRUCT {
                     "addr" ::= #giving;
                     "data" ::= #p
                   } : WriteRq reqIdSz ReordererReq);
                Retv;
           Ret #res
         else
           Ret (STRUCT {
             "ready" ::= $$false;
             "info"  ::= $$(getDefaultConst ImmRes)
           } : ReordererImmRes @# ty)
         as ret;
         Ret #ret.
   End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    
    Definition regs: list RegInitT := makeModule_regs ( Register handlingName: ReordererReqId <- $ 0 ++
                                                        Register givingName: ReordererReqId <- $ 0 ).
    
   Instance implReorderer: Reorderer :=
     {|
       Reorderer.Ifc.regs := regs;
       Reorderer.Ifc.regFiles := []; (* TODO: LLEE *)
       Reorderer.Ifc.handle := handle;
       Reorderer.Ifc.reordererCallback := reordererCallback;
       Reorderer.Ifc.sendReq := sendReq
     |}.
  End withParams.
End Reorderer.
