Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Require Import StdLibKami.Prefetcher.Ifc.
Section Prefetch.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Context `{FifoTopParams}.
  Context {reqResK: Kind}.
  Class PrefetcherImplParams :=
    {
      instFifoTop: FifoTop.Ifc.FifoTop
    }.
  Section withParams.
    Context `{PrefetcherImplParams}.
    Section withTy.
    Context {ty: Kind -> Type}.

    (** * Instruction buffer FIFO actions *)
    Local Definition InstIsEmpty: ActionT ty Bool := (FifoTop.Ifc.isEmpty instFifoTop).
    Local Definition InstIsFull: ActionT ty Bool := (FifoTop.Ifc.isFull instFifoTop).
    Local Definition InstDeq: ActionT ty DeqRes := (FifoTop.Ifc.deq instFifoTop).
    Local Definition InstEnq: ty AddrInst -> ActionT ty Bool := (FifoTop.Ifc.enq instFifoTop).
    Local Definition InstFlush: ActionT ty Void := (FifoTop.Ifc.flush instFifoTop).
    End withTy.

  Definition flush ty: ActionT ty Void :=
    LET inv: Maybe PAddr <- Invalid;
    LETA _ <- InstFlush;
    LETA _ <- FifoTop.Ifc.setIsCompleting instFifoTop inv;
    Retv.
  
 Definition getIsCompleting ty: ActionT ty (Maybe PAddr) :=
   LETA completing: Maybe PAddr <- FifoTop.Ifc.getIsCompleting instFifoTop;
   Ret #completing.

  Definition memCallback ty (m: ty FullAddrMaybeInst): ActionT ty Void :=
    LET addr <- #m @% "req";
    LET mInst <- #m @% "resp";
    LET m' <- STRUCT { "addr" ::= STRUCT { "valid" ::= #mInst @% "valid";
                                           "data" ::= toShortPAddr addr };
                       "inst" ::= #mInst @% "data" };
    LETA _ <- InstEnq m'; (* we assume that this can't fail, since the
                             earlier memory request would have failed
                             if there were not room to fulfill it *)
    Retv.

  (* The main action related to prefetching, does various things based
     on the current prefetcher state. Will be the body of a rule in
     the final pipeline. *)
  Definition doPrefetch
             (memReq: forall {ty},
                 ty PAddr -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                      "info" :: reqResK })
             {ty} (addr: ty PAddr): ActionT ty Bool :=
    LET short: ShortPAddr <- (toShortPAddr addr);
    LET fullAddrFirst: PAddr <- toFullPAddr short;
    LETA res: STRUCT_TYPE { "ready" :: Bool;
                            "info" :: reqResK }
                          <- memReq fullAddrFirst;
    LET doDequeue : Bool <- (#res @% "ready");
    Ret #doDequeue.

  Definition fetchInstruction ty: ActionT ty DeqRes :=
    LETA top: DeqRes <- InstDeq;
    Ret #top.

  Open Scope kami_scope.
  Open Scope kami_expr_scope.

  Definition regs: list RegInitT := FifoTop.Ifc.regs instFifoTop.
  
  Definition prefetcher := Build_Prefetcher
                             regs
                             flush
                             getIsCompleting
                             memCallback
                             fetchInstruction
                             doPrefetch.
  End withParams.
End Prefetch.
