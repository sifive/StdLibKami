Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.Reorderer.Ifc.
Section Reorderer.
  Context `{ReordererParams}.
  Class ReordererImplParams :=
    {
      (* Methods for interacting with the response buffer (holding Maybe Insts). *)
      rfName: string;
      rfRead: string;
      rfWrite: string;
      (* methods for interacting with the address memory, which keeps
         track of the address each request corresponds to *)
      arfName: string;
      arfRead: string;
      arfWrite: string;

      enqPtr: string;
      deqPtr: string;
    }.

  Section withParams.
    Context `{ReordererImplParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition reqIdLen := Nat.pow 2 reqIdSz.
    
    Section withTy.

      (* Conceptual rule *)
      Definition responseToPrefetcher
                 (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void)
                 ty
      : ActionT ty Void
        := Read deqPFull: ReordererPtr <- deqPtr;
           Read enqPFull: ReordererPtr <- enqPtr;
           LET deqP: ReordererReqId <- UniBit (TruncLsb _ 1) #deqPFull;
           Call inst: Maybe MInst <- rfRead(#deqP: ReordererReqId);
           Call vaddr: VAddr <- arfRead(#deqP: ReordererReqId);
           LET resp
           :  ReordererRes
                <- STRUCT {
                  "vaddr" ::= #vaddr;
                  "inst"  ::= #inst @% "data"
                };
           If (#deqPFull != #enqPFull) && #inst @% "valid"
           then
             LETA _ <- prefetcherCallback (resp : ty ReordererRes);
             Write deqPtr <- #deqPFull + $1;
             Retv;
           Retv.

      (* Action the arbiter will call when giving us (the reorderer) the
         response to a prior request *)
      Definition reordererCallback ty (resp: ty ReordererArbiterRes): ActionT ty Void :=
        LET idx: ReordererReqId <- #resp @% "tag";
        LET res: MInst <- #resp @% "resp";
        Call rfWrite(STRUCT { "addr" ::= #idx;
                              "data" ::= Valid #res } : WriteRq reqIdSz (Maybe MInst));
        Retv.

      Definition sendReq
                 ty
                 (memReq
                  : ty ReordererArbiterReq ->
                    ActionT ty ReordererImmRes)
                 (req: ty ReordererReq)
        :  ActionT ty ReordererImmRes
        := Read enqPFull: ReordererPtr <- enqPtr;
           Read deqPFull: ReordererPtr <- deqPtr;
           LET enqP: ReordererReqId <- UniBit (TruncLsb _ 1) #enqPFull;
           LET deqP: ReordererReqId <- UniBit (TruncLsb _ 1) #deqPFull;
           LET arbiterReq
           :  ReordererArbiterReq
                <- STRUCT {
                  "tag" ::= #enqP;
                  "req" ::= #req @% "paddr"
                };
           If (#deqPFull + $(Nat.pow 2 reqIdSz)) != #enqPFull
           then (* we can give a new reqid without forgetting the next one to service *)
             LETA res <- memReq arbiterReq;
             If #res @% "ready"
             then
               Write enqPtr <- #enqPFull + $1;
               Call rfWrite(STRUCT { "addr" ::= #enqP;
                                     "data" ::= Invalid } : WriteRq reqIdSz (Maybe MInst));
               Call arfWrite
                 (STRUCT {
                    "addr" ::= #enqP;
                    "data" ::= #req @% "vaddr"
                  } : WriteRq reqIdSz VAddr);
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
    
    Definition regs: list RegInitT := makeModule_regs ( Register enqPtr: ReordererPtr <- $ 0 ++
                                                        Register deqPtr: ReordererPtr <- $ 0 ).

    Definition regFiles: list RegFileBase :=
      [ 
        @Build_RegFileBase false 1 rfName
                           (Async [rfRead]) rfWrite reqIdSz (Maybe MInst) (@RFNonFile _ _ None);
          
        @Build_RegFileBase false 1 arfName
                           (Async [arfRead]) arfWrite reqIdSz VAddr (@RFNonFile _ _ None)
      ].
    

    Instance implReorderer: Reorderer :=
      {|
        Reorderer.Ifc.regs := regs;
        Reorderer.Ifc.regFiles := regFiles;
        Reorderer.Ifc.responseToPrefetcher := responseToPrefetcher;
        Reorderer.Ifc.callback := reordererCallback;
        Reorderer.Ifc.sendReq := sendReq
      |}.
  End withParams.
End Reorderer.
