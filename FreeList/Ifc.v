Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section Freelist.
  Context {ty: Kind -> Type}.
  Context {len: nat}.

  Let k := Bit (Nat.log2_up len).
  Record FreeList: Type :=
    {
      length: nat;
      initialize: ActionT ty Void;
      nextToAlloc: ActionT ty (Maybe k);
      alloc: ty k -> ActionT ty Bool;
      free: ty k -> ActionT ty Void;
    }.
End Freelist.
