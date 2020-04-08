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
  Local Definition nonDetFullName := (name ++ ".nonDetFull")%string.
  
  Local Notation Natgeb n m := (negb (Nat.ltb n m)).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  
  Local Definition getHead ty (ls : list (type k)) : k @# ty :=
    FromNative k (Var ty (NativeKind (evalConstT Default)) (hd (evalConstT Default) ls)).

  Local Definition snocInBound (a : type k) (ls : list (type k)) : list (type k) :=
    if (Nat.ltb (length ls) size) then snoc a ls else ls.

  Local Definition nonDet ty: ActionT ty Void :=
    Nondet lengthN: (Bit lgSize);
    Nondet emptyN: Bool;
    Nondet fullN: Bool;
    Write nonDetLenName: (Bit lgSize) <- #lengthN;
    Write nonDetEmptyName: Bool <- #emptyN;
    Write nonDetFullName: Bool <- #fullN;
    Retv.
  
  Local Definition nlist := NativeKind (nil : list (type k)).

  Local Definition numFree ty: ActionT ty (Bit lgSize) :=
    ReadN data: nlist <- listName;
    Read lengthN: (Bit lgSize) <- nonDetLenName;
    Ret (IF (#lengthN < $(size - (length data))) then #lengthN else $(size - (length data))).
  
  Local Definition isEmpty ty: ActionT ty Bool :=
    Read emptyN: Bool <- nonDetEmptyName;
    LETA freeNum: (Bit lgSize) <- numFree ty;
    Ret (#emptyN || (#freeNum == $size)).

  Local Definition isFull ty: ActionT ty Bool :=
    Read fullN: Bool <- nonDetFullName;
    LETA freeNum: (Bit lgSize) <- numFree ty;
    Ret (#fullN || (#freeNum == $0)).
  
  Local Definition first ty: ActionT ty (Maybe k) :=
    ReadN data: nlist <- listName;
    LETA empty: Bool <- isEmpty ty;
    Ret (STRUCT { "valid" ::= #empty;
                  "data" ::= getHead _ data } : Maybe k @# ty).

  Local Definition deq ty: ActionT ty (Maybe k) :=
    ReadN data: nlist <- listName;
    LETA empty: Bool <- isEmpty ty;
    Ret (STRUCT { "valid" ::= #empty;
                  "data" ::= getHead _ data } : Maybe k @# ty).
  
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
