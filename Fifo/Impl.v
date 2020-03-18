Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Fifo1.

Section Impl.
  Context {ifcParams : Ifc.Params}.

  Class Params := { sizePow2: Nat.pow 2 (Nat.log2_up size) = size ;
                    regArray  : @RegArray.Ifc.Ifc {| RegArray.Ifc.name := name ++ ".regArray" ;
                                                     RegArray.Ifc.k := k ;
                                                     RegArray.Ifc.size := size;
                                                     RegArray.Ifc.init := None |} }.

  Context {params: Params}.

  Local Definition twoSize := 2 * size.

  Local Definition deqPtrName := (name ++ ".deqPtr")%string.
  Local Definition enqPtrName := (name ++ ".enqPtr")%string.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition fastModSize ty (w : Bit (lgSize + 1) @# ty): Bit lgSize @# ty :=
    UniBit (TruncLsb lgSize 1) w.

  Local Definition isEmpty ty: ActionT ty Bool :=
    Read deq: Bit (lgSize + 1) <- deqPtrName;
    Read enq: Bit (lgSize + 1) <- enqPtrName;
    Ret (#deq == #enq).

  Local Definition isFull ty: ActionT ty Bool :=
    Read deq: Bit (lgSize + 1) <- deqPtrName;
    Read enq: Bit (lgSize + 1) <- enqPtrName;
    Ret ((#deq + $size) == #enq).
  
  Local Definition numFree ty: ActionT ty (Bit lgSize) :=
    Read deq: Bit (lgSize + 1) <- deqPtrName;
    Read enq: Bit (lgSize + 1) <- enqPtrName;
    Ret (UniBit (TruncLsb _ 1) ($size - (#enq - #deq))).
  
  Local Definition first ty: ActionT ty (Maybe k) := 
    LETA empty: Bool <- isEmpty ty;
    Read deq: Bit (lgSize + 1) <- deqPtrName;
    LET idx: Bit lgSize <- (fastModSize #deq);
    LETA dat: k <- read regArray ty idx;
    Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe k @# ty).

  Local Definition deq ty: ActionT ty (Maybe k) :=
    LETA data: Maybe k <- first ty;
    Read deq: Bit (lgSize + 1) <- deqPtrName;
    Write deqPtrName: Bit (lgSize + 1) <- #deq + (IF #data @% "valid" then $1 else $0);
    Ret #data.

  Local Definition enq ty (new: ty k): ActionT ty Bool :=
    Read enq: Bit (lgSize + 1) <- enqPtrName;
    LET idx: Bit lgSize <- (fastModSize #enq);
    LETA full: Bool <- isFull ty;
    If !#full then (
      LET writeRq <- STRUCT { "addr" ::= #idx; "data" ::= #new };
      LETA _ <- write regArray _ writeRq;
      Write enqPtrName: Bit (lgSize + 1) <- #enq + $1;
      Retv
      );
    Ret !#full.
    
  Local Definition flush ty: ActionT ty Void :=
    Write deqPtrName: Bit (lgSize + 1) <- $0;
    Write enqPtrName: Bit (lgSize + 1) <- $0;
    Retv.

  Local Definition regs: list RegInitT := makeModule_regs ( Register deqPtrName: Bit (lgSize + 1) <- Default ++
                                                            Register enqPtrName: Bit (lgSize + 1) <- Default )%kami
                                                          ++ RegArray.Ifc.regs regArray.

  Definition impl: Ifc :=
    if (size =? 1)%nat then
      Fifo1.impl else
      {|
      Ifc.regs := regs;
      Ifc.regFiles := RegArray.Ifc.regFiles regArray;
      Ifc.isEmpty := isEmpty;
      Ifc.isFull := isFull;
      Ifc.numFree := numFree;
      Ifc.first := first;
      Ifc.deq := deq;
      Ifc.enq := enq;
      Ifc.flush := flush
    |}.
End Impl.
