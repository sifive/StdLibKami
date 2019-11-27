Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Section prefetcher.
  Context `{FifoTopParams}.
  Context (reqResK: Kind). (* TODO: move? *)
  Record Prefetcher: Type :=
    {
      flush: forall {ty}, ActionT ty Void;
      getIsCompleting: forall {ty}, ActionT ty (Maybe PAddr);
      memCallback: forall {ty}, ty AddrInst -> ActionT ty Void;
      fetchInstruction: forall {ty}, ActionT ty DeqRes;
      (* Rule *)
      doPrefetch (memReq: forall {ty},
                     ty PAddr -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                          "info" :: reqResK }):
        forall {ty}, ty PAddr -> ActionT ty Bool;
    }.
End prefetcher.
