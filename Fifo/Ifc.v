Require Import Kami.AllNotations.
Section FifoInterface.
  Class FifoParams :=
    {
      name: string;
      k : Kind;
    }.

  Section fifoParams.
    Context (fifoParams: FifoParams). 

    Class Fifo: Type :=
      {
        getLen: nat;
        regs: list RegInitT;
        regFiles: list RegFileBase;
        isEmpty: forall {ty}, ActionT ty Bool;
        isFull: forall {ty}, ActionT ty Bool;
        first: forall {ty}, ActionT ty (Maybe k);
        deq: forall {ty}, ActionT ty (Maybe k);
        enq: forall {ty}, ty k -> ActionT ty Bool;
        flush: forall {ty}, ActionT ty Void
      }.
  End fifoParams.
End FifoInterface.
