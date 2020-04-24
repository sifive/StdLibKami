Require Import Kami.AllNotations.
Require Import StdLibKami.GenericFifo.Ifc.
Require Import StdLibKami.GenericFifo.Impl.

Section DoubleFifo.
  
  Context {ifcParams : GenericFifo.Ifc.Params}.

  Class Params := { sizeL : nat;
                    sizeR : nat;
                    sizeSum : (@size ifcParams) = sizeL + sizeR;
                    Lfifo : @GenericFifo.Ifc.Ifc (GenericFifo.Ifc.Build_Params
                                                    (append (@name ifcParams) "L")
                                                    (@k ifcParams)
                                                    sizeL);
                    Rfifo : @GenericFifo.Ifc.Ifc (GenericFifo.Ifc.Build_Params
                                                    (append (@name ifcParams) "R")
                                                    (@k ifcParams)
                                                    sizeR);
                    }.

  Context {params: Params}.

  Local Notation ifcParamsL := (GenericFifo.Ifc.Build_Params (append (@name ifcParams) "L")
                                                             (@k ifcParams)
                                                             sizeL).
  
  Local Notation ifcParamsR := (GenericFifo.Ifc.Build_Params (append (@name ifcParams) "R")
                                                             (@k ifcParams)
                                                             sizeR).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition propagate ty : ActionT ty Void :=
    LETA fullR: Bool <- (GenericFifo.Ifc.isFull Rfifo);
    LETA emptyL: Bool <- (GenericFifo.Ifc.isEmpty Lfifo);
    If !(#fullR || #emptyL) then (
      LETA val: Maybe k <- (GenericFifo.Ifc.deq Lfifo);
      LET data <- #val @% "data";
      LETA _ : Bool <- (GenericFifo.Ifc.enq Rfifo data);
      Retv
      );
    Retv.

  Local Definition isEmpty ty: ActionT ty Bool := isEmpty Rfifo.

  Local Definition isFull ty: ActionT ty Bool := isFull Lfifo.

  Local Definition numFree ty: ActionT ty (Bit ((@lgSize ifcParams) + 1)) :=
    LETA numL : Bit (lgSize + 1) <- (GenericFifo.Ifc.numFree Lfifo);
    Ret (ZeroExtendTruncLsb _ #numL).

  Local Definition first ty: ActionT ty (Maybe k) := first Rfifo.

  Local Definition deq ty: ActionT ty (Maybe k) := deq Rfifo.

  Local Definition enq ty (new: ty k): ActionT ty Bool := enq Lfifo new.

  Local Definition flush ty: ActionT ty Void :=
    LETA _ <- (GenericFifo.Ifc.flush Rfifo);
    LETA _ <- (GenericFifo.Ifc.flush Lfifo);
    Retv.

  Local Definition regs: list RegInitT := (GenericFifo.Ifc.regs Lfifo)
                                            ++ (GenericFifo.Ifc.regs Rfifo).

  Definition impl: Ifc :=
    {|
      GenericFifo.Ifc.propagate := propagate;
      GenericFifo.Ifc.regs := regs;
      GenericFifo.Ifc.regFiles := (GenericFifo.Ifc.regFiles Lfifo)
                                    ++ (GenericFifo.Ifc.regFiles Rfifo);
      GenericFifo.Ifc.isEmpty := isEmpty;
      GenericFifo.Ifc.isFull := isFull;
      GenericFifo.Ifc.numFree := numFree;
      GenericFifo.Ifc.first := first;
      GenericFifo.Ifc.deq := deq;
      GenericFifo.Ifc.enq := enq;
      GenericFifo.Ifc.flush := flush
    |}.

End DoubleFifo.
