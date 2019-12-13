Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section Freelist.
  Context {len: nat}.

  Let k := Bit (Nat.log2_up len).
  Record FreeList: Type :=
    {
      regs: list RegInitT;
      length: nat;
      initialize: forall {ty}, ActionT ty Void;
      nextToAlloc: forall {ty}, ActionT ty (Maybe k);
      alloc: forall {ty}, ty k -> ActionT ty Bool;
      free: forall {ty}, ty k -> ActionT ty Void;
    }.
End Freelist.
