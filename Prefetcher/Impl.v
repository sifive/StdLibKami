Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Impl.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Require Import StdLibKami.Prefetcher.Ifc.
Section Prefetch.

  Context `{FifoTopParams}.
  Context {ImmRes: Kind}.

  Class PrefetcherImplParams
    := {
         PAddrSz : nat;
         instFifoTop: FifoTop.Ifc.FifoTop
       }.

  Section withParams.
    Context `{PrefetcherImplParams}.

    Local Definition PAddr := Bit PAddrSz.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition flush ty: ActionT ty Void :=
      LET inv: Maybe PAddr <- Invalid;
      LETA _ <- FifoTop.Ifc.flush instFifoTop;
      (* TODO: shouldn't setIsCompleting be called flush if its needed here? *)
      (* LETA _ <- FifoTop.Ifc.setIsCompleting instFifoTop inv; *)
      Retv.
    
   Definition getIsCompleting ty: ActionT ty (Maybe VAddr) :=
     LETA completing: Maybe VAddr <- FifoTop.Ifc.getIsCompleting instFifoTop;
     Ret #completing.

    Definition memCallback (ty : Kind -> Type) (reordererRes: ty (PrefetcherReordererRes PAddrSz))
      :  ActionT ty Void
      := LET entryData
           :  PrefetcherFifoEntry
           <- STRUCT {
                "vaddr" ::= (#reordererRes @% "req" @% "req" : VAddr @# ty);
                "data"  ::= (#reordererRes @% "resp" @% "data" : Inst @# ty)
              };
         LET entry
           :  Maybe PrefetcherFifoEntry
           <- STRUCT {
                "valid" ::= #reordererRes @% "resp" @% "valid";
                "data"  ::= #entryData
              };
         LETA _ : Bool <- FifoTop.Ifc.enq instFifoTop entry;
         Retv.

    Definition doPrefetch
        (memReq
          : forall {ty},
            ty (PrefetcherReordererReq PAddrSz) ->
            ActionT ty (PrefetcherReordererImmRes ImmRes))
        {ty} (prefetcherReq: ty (PrefetcherReq PAddrSz))
      :  ActionT ty Bool
      := LET reordererReq
           :  PrefetcherReordererReq PAddrSz
           <- STRUCT {
                "req"  ::= #prefetcherReq @% "vaddr";
                "data" ::= #prefetcherReq @% "paddr"
              };
         LETA reordererImmRes
           :  PrefetcherReordererImmRes ImmRes
           <- memReq reordererReq;
         Ret (#reordererImmRes @% "ready").

    Definition fetchInstruction ty : ActionT ty DeqRes
      := LETA res : DeqRes <- FifoTop.Ifc.deq instFifoTop;
         Ret #res.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.

    Definition regs: list RegInitT := FifoTop.Ifc.regs instFifoTop.
    
    Definition prefetcher
      := Build_Prefetcher
           regs
           flush
           getIsCompleting
           memCallback
           fetchInstruction
           doPrefetch.

  End withParams.

End Prefetch.
