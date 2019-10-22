Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section Freelist.
  Context {ty: Kind -> Type}.
  Context {k: Kind}.
  Record FreeList: Type :=
    {
      initialize: ActionT ty Void;
      alloc: ActionT ty (Maybe k);
      free: k @# ty -> ActionT ty Void;
    }.
End Freelist.
