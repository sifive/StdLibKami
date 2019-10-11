Require Import Kami.AllNotations.
Section FifoInterface.
  (* TODO: have one name prefix and construct read and write names
     from those using single underscore *)
  Context {ty: Kind -> Type}.
  Context {k: Kind}.
  Record Fifo (size: nat): Type := {
                 enqPtr: string;
                 deqPtr: string;
                 readName: string;
                 writeName: string;

                 isEmpty: ActionT ty Bool;
                 isFull: ActionT ty Bool;
                 first: ActionT ty (Maybe k);
                 deq: ActionT ty (Maybe k);
                 enq: k @# ty -> ActionT ty Bool;
                 flush: ActionT ty Void
               }.
End FifoInterface.
