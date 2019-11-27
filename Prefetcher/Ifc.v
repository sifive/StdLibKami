Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Section prefetcher.
  Context `{FifoTopParams}.
  Context (reqResK: Kind). (* TODO: move? *)
  (* n.b.: these fields are so named to be consistent with the
     generic naming convention used in the reorderer *)
  Definition FullAddrInst: Kind := STRUCT_TYPE
                                     { "req" :: PAddr;
                                       "resp" :: Inst }.
  Record Prefetcher: Type :=
    {
      flush: forall {ty}, ActionT ty Void;
      getIsCompleting: forall {ty}, ActionT ty (Maybe PAddr);
      memCallback: forall {ty}, ty FullAddrInst -> ActionT ty Void;
      fetchInstruction: forall {ty}, ActionT ty DeqRes;
      (* Rule *)
      doPrefetch (memReq: forall {ty},
                     ty PAddr -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                          "info" :: reqResK }):
        forall {ty}, ty PAddr -> ActionT ty Bool;
    }.
End prefetcher.
