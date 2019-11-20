Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.

Class FifoTopParams :=
  {
    PAddrSz: nat;
    PAddr := Bit PAddrSz;
    CompInstSz: nat;
    CompInst := Bit CompInstSz;
    InstSz: nat := CompInstSz + CompInstSz;
    Inst := Bit InstSz
  }.

Section FifoTopInterface.
  Context `{FifoTopParams}.
  (* Physical address with the two least significant bits clipped off;
     those bits are unnecessary since we will always be accessing
     32-bit chunks of memory. *)
  Definition ShortPAddrSz := (PAddrSz - 2)%nat.
  Definition ShortPAddr := Bit ShortPAddrSz.
  Definition TopEntry: Kind := STRUCT_TYPE { "addr" :: ShortPAddr ;
                                             "upper" :: Maybe CompInst;
                                             "lower" :: Maybe CompInst }.

  Definition AddrInst: Kind := STRUCT_TYPE { "addr" :: ShortPAddr ;
                                             "inst" :: Inst }.
  Definition DeqRes: Kind := STRUCT_TYPE { "addr" :: Maybe PAddr ;
                                           "inst" :: Maybe Inst }.
  Context {outstandingReqSz: nat}.
  Record FifoTop: Type :=
    {
      getOutstandingReqCtr: forall {ty}, ActionT ty (Bit outstandingReqSz);
      setOutstandingReqCtr: forall {ty}, ty (Bit outstandingReqSz) -> ActionT ty Void;

      getDropCtr: forall {ty}, ActionT ty (Bit outstandingReqSz);
      setDropCtr: forall {ty}, ty (Bit outstandingReqSz) -> ActionT ty Void;

      getIsCompleting: forall {ty}, ActionT ty Bool;
      setIsCompleting: forall {ty}, ty (Maybe PAddr) -> ActionT ty Void;
      isEmpty: forall {ty}, ActionT ty Bool;
      isFull: forall {ty}, ActionT ty Bool;
      deq: forall {ty}, ActionT ty DeqRes;
      enq: forall {ty}, ty AddrInst -> ActionT ty Bool;
      flush: forall {ty}, ActionT ty Void
    }.
End FifoTopInterface.
