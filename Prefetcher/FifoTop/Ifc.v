Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.

Class FifoTopParams :=
  {
    VAddrSz : nat;
    CompInstSz: nat;
    ImmRes: Kind;
    isCompressed: forall ty, Bit CompInstSz @# ty -> Bool @# ty;
    isErr: forall ty, ImmRes @# ty -> Bool @# ty
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

  Definition toFullVAddr {ty} (short: ShortVAddr @# ty): VAddr @# ty := ZeroExtendTruncLsb _ ({< short, $$(natToWord 2 0) >})%kami_expr.
  
  Definition toShortVAddr {ty} (long: VAddr @# ty): ShortVAddr @# ty := ZeroExtendTruncMsb _ (long)%kami_expr.
    
  Definition PrefetcherFifoEntry
    := STRUCT_TYPE {
         "vaddr" :: ShortVAddr;
         "info"  :: ImmRes;  
         "inst"  :: Maybe Inst
       }.

  Definition TopEntry: Kind
    := STRUCT_TYPE {
         "vaddr" :: ShortVAddr;
         "info"  :: ImmRes;
         "noErr" :: Bool;
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
   *)
  
  Definition NoError: nat := 0.
  Definition IncompleteError: nat := 1.
  Definition EmptyError: nat := 2.
  Definition DeqErrorSz: nat := Nat.log2_up 3.
  Definition DeqError: Kind := Bit DeqErrorSz.

  Definition DeqRes
    := STRUCT_TYPE {
         "error" :: DeqError;
         "vaddr" :: VAddr;
         "info"  :: ImmRes;
         "noErr" :: Bool;
         "inst"  :: Inst
       }.

  Class FifoTop: Type :=
    {
      regs: list RegInitT;
      regFiles: list RegFileBase;
      getIsCompleting: forall {ty}, ActionT ty (Maybe VAddr);
      resetCompleting: forall {ty}, ActionT ty Void;
      isEmpty: forall {ty}, ActionT ty Bool;
      isFull: forall {ty}, ActionT ty Bool;
      deq: forall {ty}, ActionT ty DeqRes;
      enq: forall {ty}, ty PrefetcherFifoEntry -> ActionT ty Bool;
      enqOutstanding: forall {ty}, ActionT ty Bool;
      isFullOutstanding: forall {ty}, ActionT ty Bool;
      flush: forall {ty}, ActionT ty Void
    }.
End FifoTopInterface.
