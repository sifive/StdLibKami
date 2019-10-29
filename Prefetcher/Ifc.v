Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Section prefetcher.
  Context `{FifoTopParams}.
  Context (ty: Kind -> Type).
  Record Prefetcher: Type :=
    {
      flush: ActionT ty Void;
      getIsCompleting: ActionT ty (Maybe PAddr);
      addAddr: ty PAddr -> ActionT ty Bool;
      memCallback: ty AddrInst -> ActionT ty Void;
      fetchInstruction: ActionT ty DeqRes;
      (* Rule *)
      doPrefetch: ActionT ty Void
    }.
End prefetcher.      
