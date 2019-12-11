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
     AddrSize: nat; (* log len of the FIFO backing the address prefetch buffer *)
     InstSize: nat; (* log len of the FIFO backing the FIFO+Top backing the instruction buffer *)
      (* Memory request can succeed or fail; in the event of a failure we
         need to try again, and in the event of success the memory unit
         will write the requested instruction directly into the
         instruction queue *)
     addrFifo: @Fifo ShortPAddr;
     outstandingReqSz: nat;
     instFifoTop: @FifoTop.Ifc.FifoTop _ outstandingReqSz
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

    Local Definition getOutstandingReqCtr: ActionT ty (Bit outstandingReqSz) := (FifoTop.Ifc.getOutstandingReqCtr instFifoTop).
    Local Definition getDropCtr: ActionT ty (Bit outstandingReqSz) := (FifoTop.Ifc.getDropCtr instFifoTop).

    Local Definition setOutstandingReqCtr: ty (Bit outstandingReqSz) -> ActionT ty Void := (FifoTop.Ifc.setOutstandingReqCtr instFifoTop).
    Local Definition setDropCtr: ty (Bit outstandingReqSz) -> ActionT ty Void := (FifoTop.Ifc.setDropCtr instFifoTop).
    End withTy.

  Definition flush ty: ActionT ty Void :=
    LETA outstanding: Bit outstandingReqSz <- getOutstandingReqCtr;
    LETA _ <- InstFlush;
    LETA _ <- setDropCtr outstanding;
    Call "SetIsCompleting"(Invalid: Maybe PAddr);
    Retv.
  
 Definition getIsCompleting ty: ActionT ty (Maybe PAddr) :=
    Call completing: Maybe PAddr <- "GetIsCompleting"();
    Ret #completing.

  Definition memCallback ty (m: ty FullAddrMaybeInst): ActionT ty Void :=
    LETA outstanding: Bit outstandingReqSz <- getOutstandingReqCtr;
    LETA drop: Bit outstandingReqSz <- getDropCtr;
    LET newDrop: Bit outstandingReqSz <- #drop - $1;
    LET newOutstanding: Bit outstandingReqSz <- #outstanding - $1;
    LET addr <- #m @% "req";
    LET mInst <- #m @% "resp";
    If (#drop == $0) then (
      LET m' <- STRUCT { "addr" ::= STRUCT { "valid" ::= #mInst @% "valid";
                                             "data" ::= toShortPAddr addr };
                         "inst" ::= #mInst @% "data" };
      LETA _ <- InstEnq m'; (* we assume that this can't fail, since the earlier memory request would have failed if there were not room to fulfill it *)
      Retv
    ) else (
      LETA _ <- setDropCtr newDrop;
      Retv
    );

    LETA _ <- setOutstandingReqCtr newOutstanding;
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
    LETA outstanding: Bit outstandingReqSz <- getOutstandingReqCtr;
    LETA res: STRUCT_TYPE { "ready" :: Bool;
                            "info" :: reqResK }
                          <- memReq fullAddrFirst;
    LET doDequeue : Bool <- (#res @% "ready");
    LET newOutstanding: Bit outstandingReqSz <- #outstanding + (IF #doDequeue then $1 else $0);
    LETA _ <- setOutstandingReqCtr newOutstanding;
    Ret #doDequeue.

  Definition fetchInstruction ty: ActionT ty DeqRes :=
    LETA top: DeqRes <- InstDeq;
    LET topMAddr: Maybe PAddr <- (#top @% "addr");
    LET topMInst: Maybe Inst <- #top @% "inst";
    Ret #top.
  
  Definition prefetcher := Build_Prefetcher
                             flush
                             getIsCompleting
                             memCallback
                             fetchInstruction
                             doPrefetch.
  End withParams.
End Prefetch.
