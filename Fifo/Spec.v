Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.

Section Spec.
  Context {ifcParams : Ifc.Params}.

  Local Definition listName := (name ++ ".list")%string.

  Local Notation Natgeb n m := (negb (Nat.ltb n m)).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  
  Local Definition getHead ty (ls : list (ty k)): k @# ty :=
    match ls with
    | [] => $$(getDefaultConst k)
    | x :: _ => #x
    end.

  Local Definition snocInBound ty (a : ty k) (ls : list (ty k)) : list (ty k) :=
    if (Nat.ltb (length ls) size) then snoc a ls else ls.
  
  Local Definition nlist ty := NativeKind (nil : list (ty k)).
  
  Local Definition isEmpty ty: ActionT ty Bool :=
    ReadN data: nlist ty <- listName;
    Ret $$(emptyb data).

  Local Definition isFull ty: ActionT ty Bool :=
    ReadN data: nlist ty <- listName;
    Ret $$(Natgeb (length data) size).
  
  Local Definition numFree ty: ActionT ty (Bit lgSize) :=
    ReadN data: nlist ty <- listName;
    Ret $(size - (length data)).
  
  Local Definition first ty: ActionT ty (Maybe k) :=
    ReadN data: nlist ty <- listName;
    Ret (STRUCT { "valid" ::= $$(negb (emptyb data)); "data" ::= getHead _ data } : Maybe k @# ty).

  Local Definition deq ty: ActionT ty (Maybe k) :=
    ReadN data: nlist ty <- listName;
    WriteN listName: nlist ty <- Var _ (nlist ty) (tl data);
    Ret (STRUCT { "valid" ::= $$(negb (emptyb data)); "data" ::= getHead _ data } : Maybe k @# ty).
  
  Local Definition enq ty (new: ty k): ActionT ty Bool :=
    ReadN data: nlist ty <- listName;
    WriteN listName: nlist ty <- Var _ (nlist ty) (snocInBound ty new data);
    Ret $$(Nat.ltb (length data) size).

  Local Definition flush ty: ActionT ty Void :=
    WriteN listName: nlist ty <- Var _ (nlist ty) nil;
    Retv.

  Local Definition regs : list RegInitT := makeModule_regs (RegisterNDef listName: list (type k) <- (nil: list (type k)))%kami.

  Definition spec: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := nil;
      Ifc.isEmpty := isEmpty;
      Ifc.isFull := isFull;
      Ifc.numFree := numFree;
      Ifc.first := first;
      Ifc.deq := deq;
      Ifc.enq := enq;
      Ifc.flush := flush
    |}.
  
End Spec.
