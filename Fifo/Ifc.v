Require Import Kami.AllNotations.
Section FifoInterface.
  Context (k: Kind).
  Record Fifo: Type :=
    {
      regs: list RegInitT;
      isEmpty: forall {ty}, ActionT ty Bool;
      isFull: forall {ty}, ActionT ty Bool;
      first: forall {ty}, ActionT ty (Maybe k);
      deq: forall {ty}, ActionT ty (Maybe k);
      enq: forall {ty}, ty k -> ActionT ty Bool;
      flush: forall {ty}, ActionT ty Void
    }.
End FifoInterface.
