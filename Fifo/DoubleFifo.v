Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.

Section DoubleFifo.
  
  Context {ifcParams : Ifc.Params}.
  (* Variable sizeL sizeR : nat. *)
  (* Local Definition ifcParamsL := *)
  (*   Ifc.Build_Params (append name "L") k sizeL. *)
  (* Local Definition ifcParamsR := *)
  (*   Ifc.Build_Params (append name "R") k sizeR. *)

  Class Params := { sizeL : nat;
                    sizeR : nat;
                    sizeSum : (@size ifcParams) = sizeL + sizeR;
                    Lfifo : @Fifo.Ifc.Ifc (Ifc.Build_Params (append (@name ifcParams) "L")
                                                            (@k ifcParams)
                                                            sizeL);
                    Rfifo : @Fifo.Ifc.Ifc (Ifc.Build_Params (append (@name ifcParams) "R")
                                                            (@k ifcParams)
                                                            sizeR);
                    }.

  Context {params: Params}.

  Local Notation ifcParamsL := (Ifc.Build_Params (append (@name ifcParams) "L")
                                                            (@k ifcParams)
                                                            sizeL).
  
  Local Notation ifcParamsR := (Ifc.Build_Params (append (@name ifcParams) "R")
                                                            (@k ifcParams)
                                                            sizeR).
  
  Local Lemma lgSize_sumL :
    ((@lgSize ifcParamsL) + 1)
    + ((lgSize + 1) - ((@lgSize ifcParamsL) + 1)) = (lgSize + 1).
  Proof.
    symmetry.
    apply le_plus_minus.
    unfold lgSize.
    apply plus_le_compat_r, Nat.log2_up_le_mono.
    rewrite sizeSum; unfold size; lia.
  Qed.

  Local Lemma lgSize_sumR :
    ((@lgSize ifcParamsR) + 1)
    + ((lgSize + 1) - ((@lgSize ifcParamsR) + 1)) = (lgSize + 1).
  Proof.
    symmetry.
    apply le_plus_minus.
    unfold lgSize.
    apply plus_le_compat_r, Nat.log2_up_le_mono.
    rewrite sizeSum; unfold size; lia.
  Qed.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition isEmpty ty: ActionT ty Bool := isEmpty Rfifo.

  Local Definition isFull ty: ActionT ty Bool := isFull Lfifo.
  
  Local Definition numFree ty: ActionT ty (Bit ((@lgSize ifcParams) + 1)) :=
    LETA numL : Bit (lgSize + 1) <- (Ifc.numFree Lfifo);
    LETA numR : Bit (lgSize + 1) <- (Ifc.numFree Rfifo);
    Ret (IF (#numL < $(sizeL))
         then (castBits lgSize_sumL (ZeroExtend _ #numL))
         else ($sizeL + castBits lgSize_sumR (ZeroExtend _ #numR))).
  
  Local Definition first ty: ActionT ty (Maybe k) := first Rfifo.

  Local Definition deq ty: ActionT ty (Maybe k) := deq Rfifo.

  Local Definition enq ty (new: ty k): ActionT ty Bool := enq Lfifo new.

  Local Definition fillRule ty : ActionT ty Void :=
    LETA fullR: Bool <- (Ifc.isFull Rfifo);
    LETA emptyL: Bool <- (Ifc.isEmpty Lfifo);
    If !(#fullR && #emptyL) then (
      LETA val: Maybe k <- (Ifc.deq Lfifo);
      LET data <- #val @% "data";
      LETA _ : Bool <- (Ifc.enq Rfifo data);
      Retv
      );
    Retv.
                    
  Local Definition flush ty: ActionT ty Void :=
    LETA _ <- (Ifc.flush Rfifo);
    LETA _ <- (Ifc.flush Lfifo);
    Retv.

  Local Definition regs: list RegInitT := (Ifc.regs Lfifo) ++ (Ifc.regs Rfifo).

  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := (Ifc.regFiles Lfifo) ++ (Ifc.regFiles Rfifo);
      Ifc.isEmpty := isEmpty;
      Ifc.isFull := isFull;
      Ifc.numFree := numFree;
      Ifc.first := first;
      Ifc.deq := deq;
      Ifc.enq := enq;
      Ifc.flush := flush
    |}.
  
End DoubleFifo.
