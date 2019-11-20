Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Require Import StdLibKami.Prefetcher.Ifc.
Section Prefetch.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Context `{FifoTopParams}.
  Class PrefetcherImplParams :=
    {
     AddrSize: nat; (* log len of the FIFO backing the address prefetch buffer *)
     InstSize: nat; (* log len of the FIFO backing the FIFO+Top backing the instruction buffer *)
      (* Memory request can succeed or fail; in the event of a failure we
         need to try again, and in the event of success the memory unit
         will write the requested instruction directly into the
         instruction queue *)
     memReq: forall {ty}, ty PAddr -> ActionT ty Bool;
     addrFifo: @Fifo ShortPAddr;
     outstandingReqSz: nat;
     instFifoTop: @FifoTop.Ifc.FifoTop _ outstandingReqSz
     }.
  Section withParams.
    Context `{PrefetcherImplParams}.
    Section withTy.
    Context (ty: Kind -> Type).
    (** * Address prefetch buffer FIFO actions *)
    Local Definition AddrIsEmpty: ActionT ty Bool := (Fifo.Ifc.isEmpty addrFifo).
    Local Definition AddrIsFull: ActionT ty Bool := (Fifo.Ifc.isFull addrFifo).
    Local Definition AddrFirst: ActionT ty (Maybe ShortPAddr) := (Fifo.Ifc.first addrFifo).
    Local Definition AddrEnq: ty ShortPAddr -> ActionT ty Bool := (Fifo.Ifc.enq addrFifo).
    Local Definition AddrFlush: ActionT ty Void := (Fifo.Ifc.flush addrFifo).
    Local Definition AddrDeq: ActionT ty (Maybe ShortPAddr) := (Fifo.Ifc.deq addrFifo).

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

  Definition flush: ActionT ty Void :=
    LETA outstanding: Bit outstandingReqSz <- getOutstandingReqCtr;
    LETA _ <- AddrFlush;
    LETA _ <- InstFlush;
    LETA _ <- setDropCtr outstanding;
    Call "SetIsCompleting"(Invalid: Maybe PAddr);
    Retv.
  
  Definition getIsCompleting: ActionT ty (Maybe PAddr) :=
    Call completing: Maybe PAddr <- "GetIsCompleting"();
    Ret #completing.

  Definition addAddr (addr: ty PAddr): ActionT ty Bool :=
    LET shortened <- (toShortPAddr addr);
    LETA res: Bool <- AddrEnq shortened;
    Ret #res.
  
  Definition memCallback (m: ty AddrInst): ActionT ty Void :=
    LETA outstanding: Bit outstandingReqSz <- getOutstandingReqCtr;
    LETA drop: Bit outstandingReqSz <- getDropCtr;
    LET newDrop: Bit outstandingReqSz <- #drop - $1;
    LET newOutstanding: Bit outstandingReqSz <- #outstanding - $1;

    If (#drop == $0) then (
      LETA _ <- InstEnq m; (* we assume that this can't fail, since the earlier memory request would have failed if there were not room to fulfill it *)
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
  Definition doPrefetch: ActionT ty Void :=
    LETA addrFirst: Maybe ShortPAddr <- AddrFirst;
    LET short: ShortPAddr <- #addrFirst @% "data";
    LET fullAddrFirst: PAddr <- toFullPAddr short;
    LETA outstanding: Bit outstandingReqSz <- getOutstandingReqCtr;
    If (#addrFirst @% "valid") then (
      LETA res: Bool <- memReq fullAddrFirst;
      Ret #res
    ) else (
      Ret $$false
    ) as doDequeue;
    LET newOutstanding: Bit outstandingReqSz <- #outstanding + (IF #doDequeue then $1 else $0);
    LETA _ <- setOutstandingReqCtr newOutstanding;
    If #doDequeue then (LETA _ <- AddrDeq; Retv);
    Retv.

  Definition fetchInstruction: ActionT ty DeqRes :=
    LETA top: DeqRes <- InstDeq;
    LET topMAddr: Maybe PAddr <- (#top @% "addr");
    LET topMInst: Maybe Inst <- #top @% "inst";
    LET flushAddr: Bool <- (#topMAddr @% "valid") && !(#topMInst @% "valid");
    
    If #flushAddr then (LETA _ <- AddrFlush; Retv);
    Ret #top.
  End withTy.                     
  Definition prefetcher := Build_Prefetcher
                             flush
                             getIsCompleting
                             addAddr
                             memCallback
                             fetchInstruction
                             doPrefetch.
  End withParams.
End Prefetch.
