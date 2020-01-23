Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Require Import StdLibKami.Prefetcher.Ifc.

Section Prefetch.
  Context `{fifoTopParams : FifoTopParams}.
  Context `{prefetcherParams: PrefetcherParams}.

  Context (fifoTop: FifoTop.Ifc.FifoTop).

  Local Definition PAddr := Bit PAddrSz.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition flush ty: ActionT ty Void :=
    @FifoTop.Ifc.flush _ fifoTop ty.
  
  Definition getIsCompleting ty: ActionT ty (Maybe VAddr) :=
    @FifoTop.Ifc.getIsCompleting _ fifoTop ty.

  Definition resetCompleting ty: ActionT ty Void :=
    @FifoTop.Ifc.resetCompleting _ fifoTop ty.

  Definition memCallback (ty : Kind -> Type) (reordererRes: ty PrefetcherRes)
    :  ActionT ty Void
    := LET entryData
         :  PrefetcherFifoEntry
         <- STRUCT {
              "vaddr" ::= (toShortVAddr (#reordererRes @% "vaddr" : VAddr @# ty));
              "info"  ::= #reordererRes @% "info";
              "inst"  ::= (#reordererRes @% "inst": Maybe Inst @# ty)
            };
       LETA _ <- @FifoTop.Ifc.enq _ fifoTop ty entryData;
       Retv.

  Definition doPrefetch
      ty
      (memReq
        : ty PrefetcherReq ->
          ActionT ty Bool)
      (prefetcherReq: ty PrefetcherReq)
    :  ActionT ty Bool
    := LETA retval <- memReq prefetcherReq;
       LET dummy: Void <- $0;
       LETA _ <- @FifoTop.Ifc.enqOutstanding _ fifoTop _;
       Ret #retval.

  Definition fetchInstruction ty : ActionT ty DeqRes
    := LETA res : DeqRes <- @FifoTop.Ifc.deq _ fifoTop ty;
       Ret #res.

  Definition isFull ty: ActionT ty Bool
    := @FifoTop.Ifc.isFullOutstanding _ fifoTop _.

  Open Scope kami_scope.
  Open Scope kami_expr_scope.

  Definition regs := @FifoTop.Ifc.regs _ fifoTop.
  Definition regFiles := @FifoTop.Ifc.regFiles _ fifoTop.

  Instance prefetcher: Prefetcher := {| Prefetcher.Ifc.regs := regs;
                                        Prefetcher.Ifc.regFiles := regFiles;
                                        Prefetcher.Ifc.flush := flush;
                                        Prefetcher.Ifc.getIsCompleting := getIsCompleting;
                                        Prefetcher.Ifc.resetCompleting := resetCompleting;
                                        Prefetcher.Ifc.isFull := isFull;
                                        Prefetcher.Ifc.memCallback := memCallback;
                                        Prefetcher.Ifc.fetchInstruction := fetchInstruction;
                                        Prefetcher.Ifc.doPrefetch := doPrefetch |}.
End Prefetch.
