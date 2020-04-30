Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.

Section Spec.
  Context {ifcParams : Ifc.Params}.

  Local Definition listName := (name ++ ".list")%string.

  Local Notation Natgeb n m := (negb (Nat.ltb n m)).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition getHead ty (ls : list (type k)) : k @# ty :=
    FromNative k (Var ty (NativeKind (evalConstT Default)) (hd (evalConstT Default) ls)).

  Local Definition snocInBound (a : type k) (ls : list (type k)) : list (type k) :=
    if (Nat.ltb (length ls) size) then snoc a ls else ls.
  
  Local Definition nlist := NativeKind (nil : list (type k)).
  
  Local Definition isEmpty ty: ActionT ty Bool :=
    ReadN data: nlist <- listName;
    Ret $$(emptyb data).

  Local Definition isFull ty: ActionT ty Bool :=
    ReadN data: nlist <- listName;
    Ret $$(Natgeb (length data) size).
  
  Local Definition numFree ty: ActionT ty (Bit (lgSize + 1)) :=
    ReadN data: nlist <- listName;
    Ret $(size - (length data)).
  
  Local Definition first ty: ActionT ty (Maybe k) :=
    ReadN data: nlist <- listName;
    Ret (STRUCT { "valid" ::= $$(negb (emptyb data));
                  "data" ::= getHead _ data } : Maybe k @# ty).

  Local Definition deq ty: ActionT ty (Maybe k) :=
    ReadN data: nlist <- listName;
    WriteN listName: nlist <- (IF !$$(emptyb data)
                               then Var _ nlist (tl data)
                               else Var _ nlist data);
    Ret (STRUCT { "valid" ::= $$(negb (emptyb data));
                  "data" ::= getHead _ data } : Maybe k @# ty).
  
  Local Definition enq ty (new: ty k): ActionT ty Bool :=
    ReadN data: nlist <- listName;
    LET val <- ToNative #new;
    WriteN listName: nlist <- Var _ nlist (snocInBound val data);
    Ret $$(Nat.ltb (length data) size).

  Local Definition flush ty: ActionT ty Void :=
    WriteN listName: nlist <- Var _ nlist nil;
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
