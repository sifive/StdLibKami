Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.

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

  Local Definition snocInBound (a : type k) (ls : list (type k)) : list (type k) :=
    if (Nat.ltb (length ls) size) then snoc a ls else ls.

  Local Definition nonDet ty: ActionT ty Void :=
    Nondet lengthN: (Bit (Nat.log2_up (size + 1)));
    Nondet emptyN: Bool;
    Write nonDetLenName: (Bit (Nat.log2_up (size + 1))) <- #lengthN;
    Write nonDetEmptyName: Bool <- #emptyN;
    Retv.
  
  Local Definition nlist := NativeKind (nil : list (type k)).

  Local Definition numFree ty: ActionT ty (Bit (Nat.log2_up (size + 1))) :=
    ReadN data: nlist <- listName;
    Read lengthN: (Bit (Nat.log2_up (size + 1))) <- nonDetLenName;
    Ret (IF (#lengthN < $(size - (length data)))
         then #lengthN else $(size - (length data))).
  
  Local Definition isEmpty ty: ActionT ty Bool :=
    Read emptyN: Bool <- nonDetEmptyName;
    ReadN data: nlist <- listName;
    Ret (#emptyN || $$(emptyb data)).

  Local Definition isFull ty: ActionT ty Bool :=
    ReadN data: nlist <- listName;
    Read lengthN: (Bit (Nat.log2_up (size + 1))) <- nonDetLenName;
    Ret (#lengthN == $0 || $$(Nat.eqb (length data) size)).
  
  Local Definition first ty: ActionT ty (Maybe k) :=
    ReadN data: nlist <- listName;
    LETA empty: Bool <- isEmpty ty;
    Ret (STRUCT { "valid" ::= #empty;
                  "data" ::= (IF !#empty
                              then getHead _ data
                              else Const ty Default )} : Maybe k @# ty).

  Local Definition deq ty: ActionT ty (Maybe k) :=
    ReadN data: nlist <- listName;
    LETA empty: Bool <- isEmpty ty;
    Ret (STRUCT { "valid" ::= #empty;
                  "data" ::= (IF !#empty
                              then getHead _ data
                              else Const ty Default)} : Maybe k @# ty).
  
  Local Definition enq ty (new: ty k): ActionT ty Bool :=
    ReadN data: nlist <- listName;
    LETA full: Bool <- isFull ty;
    LET val <- ToNative #new;
    WriteN listName: nlist <- (IF !#full
                                  then Var _ nlist (snocInBound val data)
                                  else Var _ nlist data);
    Ret #full.

  Local Definition flush ty: ActionT ty Void :=
    WriteN listName: nlist <- Var _ nlist nil;
    Retv.

  Local Definition regs : list RegInitT :=
    makeModule_regs (RegisterNDef listName: list (type k) <- (nil: list (type k)))%kami.

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
  
End GenSpec.
