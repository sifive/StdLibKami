Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.

Section DoubleFifo.
  Context {ifcParams : Ifc.Params}.

  Class Params := { sizePow2: Nat.pow 2 (Nat.log2_up size) = size ;
                    regArrayL : @RegArray.Ifc.Ifc {| RegArray.Ifc.name := name ++ ".regArrayL" ;
                                                     RegArray.Ifc.k := k ;
                                                     RegArray.Ifc.size := size;
                                                     RegArray.Ifc.init := None |};
                    regArrayR : @RegArray.Ifc.Ifc {| RegArray.Ifc.name := name ++ ".regArrayR" ;
                                                     RegArray.Ifc.k := k ;
                                                     RegArray.Ifc.size := size;
                                                     RegArray.Ifc.init := None |} }.

  Context {params: Params}.

  Local Definition twoSize := 2 * size.

  Local Definition deqLPtrName := (name ++ ".deqLPtr")%string.
  Local Definition enqLPtrName := (name ++ ".enqLPtr")%string.
  Local Definition deqRPtrName := (name ++ ".deqRPtr")%string.
  Local Definition enqRPtrName := (name ++ ".enqRPtr")%string.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition fastModSize ty (w : Bit (lgSize + 1) @# ty): Bit lgSize @# ty :=
    UniBit (TruncLsb lgSize 1) w.

  Local Definition isEmptyL ty: ActionT ty Bool :=
    Read deqL: Bit (lgSize + 1) <- deqLPtrName;
    Read enqL: Bit (lgSize + 1) <- enqLPtrName;
    Ret (#deqL == #enqL).

  Local Definition isEmptyR ty: ActionT ty Bool :=
    Read deqR: Bit (lgSize + 1) <- deqRPtrName;
    Read enqR: Bit (lgSize + 1) <- enqRPtrName;
    Ret (#deqR == #enqR).

  Local Definition isFullL ty: ActionT ty Bool :=
    Read deqL: Bit (lgSize + 1) <- deqLPtrName;
    Read enqL: Bit (lgSize + 1) <- enqLPtrName;
    Ret ((#deqL + $size) == #enqL).
  
  Local Definition isFullR ty: ActionT ty Bool :=
    Read deqR: Bit (lgSize + 1) <- deqRPtrName;
    Read enqR: Bit (lgSize + 1) <- enqRPtrName;
    Ret ((#deqR + $size) == #enqR).

  Local Definition numFreeL ty: ActionT ty (Bit lgSize) :=
    Read deqL: Bit (lgSize + 1) <- deqLPtrName;
    Read enqL: Bit (lgSize + 1) <- enqLPtrName;
    Ret (UniBit (TruncLsb _ 1) ($size - (#enqL - #deqL))).

  Local Definition numFreeR ty: ActionT ty (Bit lgSize) :=
    Read deqR: Bit (lgSize + 1) <- deqRPtrName;
    Read enqR: Bit (lgSize + 1) <- enqRPtrName;
    Ret (UniBit (TruncLsb _ 1) ($size - (#enqR - #deqR))).
  
  Local Definition firstL ty: ActionT ty (Maybe k) := 
    LETA emptyL: Bool <- isEmptyL ty;
    Read deqL: Bit (lgSize + 1) <- deqLPtrName;
    LET idx: Bit lgSize <- (fastModSize #deqL);
    LETA dat: k <- read regArrayL ty idx;
    Ret (STRUCT { "valid" ::= !#emptyL; "data" ::= #dat} : Maybe k @# ty).
  
  Local Definition firstR ty: ActionT ty (Maybe k) := 
    LETA emptyR: Bool <- isEmptyR ty;
    Read deqR: Bit (lgSize + 1) <- deqLPtrName;
    LET idx: Bit lgSize <- (fastModSize #deqR);
    LETA dat: k <- read regArrayR ty idx;
    Ret (STRUCT { "valid" ::= !#emptyR; "data" ::= #dat} : Maybe k @# ty).

  Local Definition deqR ty: ActionT ty (Maybe k) :=
    LETA data: Maybe k <- firstR ty;
    Read deqR: Bit (lgSize + 1) <- deqRPtrName;
    Write deqRPtrName: Bit (lgSize + 1) <- #deqR + (IF #data @% "valid" then $1 else $0);
    Ret #data.

  Local Definition enqL ty (new: ty k): ActionT ty Bool :=
    Read enqL: Bit (lgSize + 1) <- enqLPtrName;
    LET idx: Bit lgSize <- (fastModSize #enqL);
    LETA fullL: Bool <- isFullL ty;
    If !#fullL then (
      LET writeRq <- STRUCT { "addr" ::= #idx; "data" ::= #new };
      LETA _ <- write regArrayL _ writeRq;
      Write enqLPtrName: Bit (lgSize + 1) <- #enqL + $1;
      Retv
      );
    Ret !#fullL.

  Local Definition enqR_deqL ty : ActionT ty Void :=
    Read enqR: Bit (lgSize + 1) <- enqRPtrName;
    LET idx: Bit lgSize <- (fastModSize #enqR);
    LETA fullR: Bool <- isFullR ty;
    LETA data: Maybe k <- firstL ty;
    Read deqL: Bit (lgSize + 1) <- deqLPtrName;
    Write deqLPtrName: Bit (lgSize + 1) <- #deqL + (IF #data @% "valid" then $1 else $0);  
    If (!#fullR && #data @% "valid") then (
      LET writeRq <- STRUCT { "addr" ::= #idx; "data" ::= #data @% "data" };
      LETA _ <- write regArrayR _ writeRq;
      Write enqRPtrName: Bit (lgSize + 1) <- #enqR + $1;
      Retv
      );
    Retv.
                    
  Local Definition flush ty: ActionT ty Void :=
    Write deqLPtrName: Bit (lgSize + 1) <- $0;
    Write enqLPtrName: Bit (lgSize + 1) <- $0;
    Write deqRPtrName: Bit (lgSize + 1) <- $0;
    Write enqRPtrName: Bit (lgSize + 1) <- $0;
    Retv.

  Local Definition regs: list RegInitT := makeModule_regs
                          ( Register deqLPtrName: Bit (lgSize + 1) <- Default ++
                            Register enqLPtrName: Bit (lgSize + 1) <- Default ++
                            Register deqRPtrName: Bit (lgSize + 1) <- Default ++
                            Register enqRPtrName: Bit (lgSize + 1) <- Default )%kami
                            ++ RegArray.Ifc.regs regArrayL ++ RegArray.Ifc.regs regArrayR.

  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := RegArray.Ifc.regFiles regArrayL
                      ++ RegArray.Ifc.regFiles regArrayR;
      Ifc.isEmpty := isEmptyL;
      Ifc.isFull := isFullR;
      Ifc.numFree := numFreeL;
      Ifc.first := firstR;
      Ifc.deq := deqR;
      Ifc.enq := enqL;
      Ifc.flush := flush
    |}.
End DoubleFifo.
