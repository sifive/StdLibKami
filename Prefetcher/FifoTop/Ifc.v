Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.

Class FifoTopParams :=
  {
    VAddrSz : nat;
    CompInstSz: nat
  }.

Section FifoTopInterface.
  Context `{FifoTopParams}.

  Definition VAddr    := Bit VAddrSz.
  Definition CompInst := Bit CompInstSz.
  Definition InstSz   := CompInstSz + CompInstSz.
  Definition Inst     := Bit InstSz.

  (* Physical address with the two least significant bits clipped off;
     those bits are unnecessary since we will always be accessing
     32-bit chunks of memory. *)
  Definition ShortVAddrSz := (VAddrSz - 2)%nat.

  Definition ShortVAddr := Bit ShortVAddrSz.

  Definition PrefetcherFifoEntry
    := STRUCT_TYPE {
         "vaddr" :: VAddr;
         "data"  :: Inst
       }.

  Definition TopEntry: Kind
    := STRUCT_TYPE {
         "vaddr" :: Maybe ShortVAddr;
         "upper" :: Maybe CompInst;
         "lower" :: Maybe CompInst
       }.

  (* The result type for a dequeue carries a DeqError;
     The DeqError type has the following semantics:
     NoError |-> No problems; in the "inst" field is a full instruction corresponding to "addr".
     IncompleteError |-> We only have the lower half of a 32 bit instruction in the top register,
                        and need 16 bits at the address contiguous to "addr" to complete it;
                        caller must prefetch addr returned.
     EmptyError |-> The Fifo + Top is empty.
     DevError |-> There was a device access exception for the address;
                  the client should handle an access exception for that address in this case
  *)
  Definition DeqErrorSz: nat := Nat.log2_up 4.
  Definition DeqError: Kind := Bit DeqErrorSz.
  Definition NoError: nat := 0.
  Definition IncompleteError: nat := 1.
  Definition EmptyError: nat := 2.
  Definition DevError: nat := 3.

  Definition DeqRes
    := STRUCT_TYPE {
         "error" :: DeqError;
         "vaddr" :: VAddr;
         "inst"  :: Inst
       }.

  Record FifoTop: Type :=
    {
      regs: list RegInitT;
      getIsCompleting: forall {ty}, ActionT ty (Maybe VAddr);
      isEmpty: forall {ty}, ActionT ty Bool;
      isFull: forall {ty}, ActionT ty Bool;
      deq: forall {ty}, ActionT ty DeqRes;
      enq: forall {ty}, ty (Maybe PrefetcherFifoEntry) -> ActionT ty Bool;
      flush: forall {ty}, ActionT ty Void
    }.
End FifoTopInterface.
