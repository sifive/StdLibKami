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
  Context {ty: Kind -> Type}.
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
      getOutstandingReqCtr: ActionT ty (Bit outstandingReqSz);
      setOutstandingReqCtr: ty (Bit outstandingReqSz) -> ActionT ty Void;

      getDropCtr: ActionT ty (Bit outstandingReqSz);
      setDropCtr: ty (Bit outstandingReqSz) -> ActionT ty Void;

      getIsCompleting: ActionT ty Bool;
      setIsCompleting: ty (Maybe PAddr) -> ActionT ty Void;
      isEmpty: ActionT ty Bool;
      isFull: ActionT ty Bool;
      deq: ActionT ty DeqRes;
      enq: ty AddrInst -> ActionT ty Bool;
      flush: ActionT ty Void
    }.
End FifoTopInterface.
