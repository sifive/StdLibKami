Require Import Kami.AllNotations.
Require Import StdLibKami.GenericFifo.Ifc.

Section GenSpec.
  Context {ifcParams : Ifc.Params}.

  Class Params := { regList : list RegInitT }.

  Context {params : Params}.

  Local Definition listName := (name ++ ".list")%string.
  Local Definition nonDetLenName := (name ++ ".nonDetLen")%string.
  Local Definition nonDetEmptyName := (name ++ ".nonDetEmpty")%string.
  
  Local Notation Natgeb n m := (negb (Nat.ltb n m)).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition getHead ty (ls : list (type k)) : k @# ty :=
    FromNative k (Var ty (NativeKind (evalConstT Default)) (hd (evalConstT Default) ls)).
  
  Local Definition nlist := NativeKind (nil : list (type k)).

  Local Definition propagate ty: ActionT ty Void :=
    Nondet lengthN: Bit (lgSize + 1);
    Nondet emptyN: Bool;
    Write nonDetLenName: Bit (lgSize + 1) <- #lengthN;
    Write nonDetEmptyName: Bool <- #emptyN;
    Retv.

  Local Definition numFree ty: ActionT ty (Bit (lgSize + 1)) :=
    Read lengthN: Bit (lgSize + 1) <- nonDetLenName;
    ReadN data: nlist <- listName;
    Ret (IF (#lengthN < $(size - (length data)))
         then #lengthN
         else $(size - (length data))).
  
  Local Definition isEmpty ty: ActionT ty Bool :=
    Read emptyN: Bool <- nonDetEmptyName;
    ReadN data: nlist <- listName;
    Ret (#emptyN || $$(emptyb data)).

  Local Definition isFull ty: ActionT ty Bool :=
    Read lengthN: Bit (lgSize + 1) <- nonDetLenName;
    ReadN data: nlist <- listName;
    Ret ((IF (#lengthN < $(size - (length data)))
          then #lengthN
          else $(size - (length data))) == $0).
  
  Local Definition first ty: ActionT ty (Maybe k) :=
    Read emptyN: Bool <- nonDetEmptyName;
    ReadN data: nlist <- listName;
    Ret ((IF !(#emptyN || $$(emptyb data))
          then (STRUCT { "valid" ::= $$true;
                         "data" ::= getHead _ data})
          else Const ty Default) : Maybe k @# ty).

  Local Definition deq ty: ActionT ty (Maybe k) :=
    Read emptyN: Bool <- nonDetEmptyName;
    ReadN data: nlist <- listName;
    Nondet newEmptyN: Bool;
    WriteN listName: nlist <- (IF !(#emptyN || $$(emptyb data))
                               then Var _ nlist (tl data)
                               else Var _ nlist data);
    Write nonDetEmptyName: Bool <- (IF !(#emptyN || $$(emptyb data))
                                    then #newEmptyN
                                    else #emptyN);
    Ret ((IF !(#emptyN || $$(emptyb data))
          then (STRUCT { "valid" ::= $$true;
                         "data" ::= getHead _ data})
          else Const ty Default) : Maybe k @# ty). 
  
  Local Definition enq ty (new: ty k): ActionT ty Bool :=
    Read lengthN: Bit (lgSize + 1) <- nonDetLenName;
    ReadN data: nlist <- listName;
    Nondet newLengthN: Bit (lgSize + 1);
    LET val <- ToNative #new;
    WriteN listName: nlist <- (IF !((IF (#lengthN < $(size - (length data)))
                                     then #lengthN
                                     else $(size - (length data))) == $0)
                               then Var _ nlist (snoc val data)
                               else Var _ nlist data);
    Write nonDetLenName: Bit (lgSize + 1) <- (IF !((IF (#lengthN < $(size - (length data)))
                                                    then #lengthN
                                                    else $(size - (length data))) == $0)
                                              then #newLengthN
                                              else #lengthN);
    Ret ((IF (#lengthN < $(size - (length data)))
          then #lengthN
          else $(size - (length data))) == $0).

  Local Definition flush ty: ActionT ty Void :=
    WriteN listName: nlist <- Var _ nlist nil;
    Write nonDetEmptyName: Bool <- $$true;
    Write nonDetLenName: Bit (lgSize + 1) <- $0;
    Retv.

  Local Definition regs : list RegInitT :=
    makeModule_regs (RegisterNDef listName: list (type k) <- (nil: list (type k)))%kami.

  Definition spec: Ifc :=
    {|
      Ifc.propagate := propagate;
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
  
End GenSpec.
