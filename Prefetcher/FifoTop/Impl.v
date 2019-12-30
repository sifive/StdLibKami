(* TODO: LLEE rename to Impl.v *)
Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Section AsyncFifoTop.
  Context `{FifoTopParams}.
  Class AsyncFifoTopParams :=
    {
      backingFifo: @Fifo PrefetcherFifoEntry;
      topReg: string;
      isCompleting: string;
    }.
  Section withParams.
    Context `{AsyncFifoTopParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.
    
    Definition toFullVAddr {ty} (short: ty ShortVAddr): VAddr @# ty := ZeroExtendTruncLsb _ ({< #short, $$(natToWord 2 0) >}).
  
    Definition toShortVAddr {ty} (long: ty VAddr): ShortVAddr @# ty := ZeroExtendTruncMsb _ #long.
    
    Section withTy.
    Context (ty: Kind -> Type).
    
    Definition GetIsCompleting: ActionT ty (Maybe VAddr) :=
      Read completing: Maybe VAddr <- isCompleting;
      Ret #completing.

    Definition SetIsCompleting (p: ty (Maybe VAddr)): ActionT ty Void :=
      Write isCompleting: Maybe VAddr <- #p;
      Retv.

    Local Definition TopIsEmpty: ActionT ty Bool :=
      Read top: TopEntry <- topReg;
      (* COQBUG: typeclass instance resolution fails *)
      LET upper: Maybe (@CompInst H) <- #top @% "upper";
      Ret !(#upper @% "valid"). (* we maintain the invariant that the upper portion of the top register is valid for any non-empty Fifo *)
  
    Definition isEmpty: ActionT ty Bool :=
      LETA topEmpty: Bool <- TopIsEmpty;
      LETA fifoEmpty: Bool <- (Fifo.Ifc.isEmpty backingFifo);
      Ret (#topEmpty && #fifoEmpty).

    Definition isFull: ActionT ty Bool :=
      LETA fifoFull: Bool <- (Fifo.Ifc.isFull backingFifo);
      Ret #fifoFull.
  
    (*
      NOTE: this is RISC-V specific and shouldn't be in
      StdLibKami. If the following definitions depend on this,
      then the Prefetcher needs to be moved to ProcKami.
    *)
    Local Definition isCompressed (inst : CompInst @# ty)
      := (ZeroExtendTruncLsb 2 inst != $$(('b"11") : word 2)).

    (* TODO: LLEE place cut text back in as comment. *)
    Definition deq : ActionT ty DeqRes
      := Ret $$(getDefaultConst (DeqRes)).
   
    (* TODO: LLEE place cut text back in as comment. *)
    Definition enq (new: ty (Maybe PrefetcherFifoEntry)) : ActionT ty Bool
      := Ret $$true.

    Definition flush: ActionT ty Void :=
      LETA _ <- (Fifo.Ifc.flush backingFifo);
      Write topReg
        :  TopEntry
        <- STRUCT {
             "vaddr"  ::= $$(getDefaultConst (Maybe ShortVAddr));
             "upper" ::= Invalid;
             "lower" ::= Invalid
           };
      Retv.
    
    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.

    Definition regs: list RegInitT := makeModule_regs ( Register topReg: TopEntry <- Default ++
                                                        Register isCompleting: Maybe VAddr <- Default )
                                      ++ Fifo.Ifc.regs backingFifo.
    
    Definition asyncFifoTop: FifoTop.Ifc.FifoTop := 
      {|
        FifoTop.Ifc.regs := regs;
        FifoTop.Ifc.getIsCompleting := GetIsCompleting;
        FifoTop.Ifc.isEmpty := isEmpty;
        FifoTop.Ifc.isFull := isFull;
        FifoTop.Ifc.deq := deq;
        FifoTop.Ifc.enq := enq;
        FifoTop.Ifc.flush := flush;
      |}.
  End withParams.
End AsyncFifoTop.
