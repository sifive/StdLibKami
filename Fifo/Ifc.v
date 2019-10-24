Require Import Kami.AllNotations.
Section FifoInterface.
  Context {ty: Kind -> Type}.
  Context (k: Kind).
  Record Fifo: Type :=
    {
      isEmpty: ActionT ty Bool;
      isFull: ActionT ty Bool;
      first: ActionT ty (Maybe k);
      deq: ActionT ty (Maybe k);
      enq: ty k -> ActionT ty Bool;
      flush: ActionT ty Void
    }.
End FifoInterface.
