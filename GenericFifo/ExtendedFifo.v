Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.GenericFifo.Ifc.

Section Spec.
  Context {ifcParams : Fifo.Ifc.Params}.

  Class Params := {fifo : @Fifo.Ifc.Ifc ifcParams;
                   genericFifo : @GenericFifo.Ifc.Ifc (GenericFifo.Ifc.Build_Params
                                                         (@Fifo.Ifc.name ifcParams)
                                                         (@Fifo.Ifc.k ifcParams)
                                                         (@Fifo.Ifc.size ifcParams))}.
  (* Class Params := {genericParams : @GenericFifo.Ifc.Ifc (GenericFifo.Ifc.Build_Params *)
  (*                                                          (@Fifo.Ifc.name ifcParams) *)
  (*                                                          (@Fifo.Ifc.k ifcParams) *)
  (*                                                          (@Fifo.Ifc.size ifcParams))}. *)
  Context {params : Params}.

  Local Notation genericParams := (GenericFifo.Ifc.Build_Params
                                     (@Fifo.Ifc.name ifcParams)
                                     (@Fifo.Ifc.k ifcParams)
                                     (@Fifo.Ifc.size ifcParams)).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition propagate ty: ActionT ty Void :=
    Retv.
  
  Local Definition isEmpty ty: ActionT ty Bool :=
    (@Fifo.Ifc.isEmpty ifcParams fifo ty).

  Local Definition isFull ty: ActionT ty Bool :=
    (@Fifo.Ifc.isFull ifcParams fifo ty).
  
  Local Definition numFree ty: ActionT ty (Bit ((@lgSize genericParams) + 1)) :=
    (@Fifo.Ifc.numFree ifcParams fifo ty).
  
  Local Definition first ty: ActionT ty (Maybe (@k genericParams)) :=
    (@Fifo.Ifc.first ifcParams fifo ty).

  Local Definition deq ty: ActionT ty (Maybe (@k genericParams)) :=
    (@Fifo.Ifc.deq ifcParams fifo ty).
  
  Local Definition enq ty (new: ty (@k genericParams)): ActionT ty Bool :=
    (@Fifo.Ifc.enq ifcParams fifo ty new).

  Local Definition flush ty: ActionT ty Void :=
    (@Fifo.Ifc.flush ifcParams fifo ty).

  Local Definition regs : list RegInitT := (@Fifo.Ifc.regs ifcParams fifo).

  Definition Extension: Ifc :=
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
  
End Spec.
