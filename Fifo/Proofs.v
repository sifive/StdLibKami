Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.Proofs.
  
Record FifoCorrect {FParams} (imp spec : @Fifo.Ifc.Ifc FParams) : Type :=
  {
    fifoRegs : list (Attribute FullKind);
    fifoR : RegsT -> RegsT -> Prop;
    isEmptyCorrect : EffectlessRelation fifoR (@isEmpty _ imp type) (@isEmpty _ spec type);
    isEmptyWb : ActionWb fifoRegs (@isEmpty _ imp type);
    isFullCorrect : EffectlessRelation fifoR (@isFull _ imp type) (@isFull _ spec type);
    isFullWb : ActionWb fifoRegs (@isFull _ imp type);
    numFreeCorrect : EffectlessRelation fifoR (@numFree _ imp type) (@numFree _ spec type);
    numFreeWb : ActionWb fifoRegs (@numFree _ imp type);
    firstCorrect : EffectlessRelation fifoR (@first _ imp type) (@first _ spec type);
    firstWb : ActionWb fifoRegs (@first _ imp type);
    deqCorrect : EffectfulRelation fifoR (@deq _ imp type) (@deq _ spec type);
    deqWb : ActionWb fifoRegs (@deq _ imp type);
    enqCorrect : forall val, EffectfulRelation fifoR (@enq _ imp type val) (@enq _ spec type val);
    enqWb : forall val, ActionWb fifoRegs (@enq _ imp type val);
    flushCorrect : EffectfulRelation fifoR (@flush _ imp type) (@flush _ spec type);
  }.

Section Proofs1.
  Context {ifcParams' : Fifo.Ifc.Params}.
  Variable Hsize1 : size = 1.
  Variable impl1Params impl2Params : Impl.Params.
  Local Definition fifoImpl1 := @Fifo.Impl.impl ifcParams' impl1Params.
  Local Definition fifoImpl2 := @Fifo.Impl.impl ifcParams' impl2Params.

  Record myFifoImpl1R  (o_i o_s : RegsT) : Prop :=
    {
      implRegs : RegsT;
      fifo1_bval : bool;
      fifo1_dval : type k;
      implRegVal : implRegs = [(Fifo1.validRegName,
                                existT _ (SyntaxKind Bool) fifo1_bval);
                              (Fifo1.dataRegName,
                               existT _ (SyntaxKind k) fifo1_dval)];
      Ho_iCorrect1 : o_i = implRegs;
      Ho_sCorrect1 : o_s = implRegs;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.

  Ltac Record_destruct :=
    match goal with
    |[ H : myFifoImpl1R _ _ |- _] => destruct H
    end.

  Goal FifoCorrect fifoImpl1 fifoImpl2.
    rewrite <- Nat.eqb_eq in Hsize1.
    all : econstructor 1 with (fifoR := myFifoImpl1R)
                              (fifoRegs := [(Fifo1.validRegName,
                                             SyntaxKind Bool);
                                            (Fifo1.dataRegName,
                                             SyntaxKind k)]).
    all : red; unfold fifoImpl1, fifoImpl2, impl, spec, regArray,
               isEmpty, flush, enq, deq, numFree, isFull, first,
               Impl.isEmpty, Impl.flush, Impl.enq, Impl.deq, Impl.numFree,
               Impl.isFull, Impl.first.
    all : try rewrite Hsize1; unfold Fifo1.impl, Fifo1.isEmpty,
                         Fifo1.isFull, Fifo1.flush, Fifo1.numFree, Fifo1.first,
                         Fifo1.deq, Fifo1.enq; intros; try Record_destruct.
    - hyp_consumer1'; basic_goal_consumer'.
    - hyp_consumer1'.
      Ltac extractGKAs :=
        let var := fresh "x" in
        let vfst := fresh "x" in
        let vsnd := fresh "x" in
        let p1 := fresh "x" in
        let p2 := fresh "x" in
        let Heq := fresh "H" in
        let HIn := fresh "H" in
        let Heq1 := fresh "H" in
        let Heq2 := fresh "H" in
        match goal with
        | [HNoDup : NoDup (map fst ?o),
                    H1 : In (?a, ?b) (map (fun x => (fst x, projT1 (snd x))) ?o) |- _]
          => rewrite in_map_iff in H1; destruct H1 as [var [Heq HIn]];
             destruct var as [vfst vsnd]; destruct vsnd as [p1 p2];
             cbn [fst snd projT1] in Heq;
             apply inversionPair in Heq;
             inversion_clear Heq as [Heq1 Heq2]; subst;
             repeat resolve_In
        end.
      repeat extractGKAs.
      goal_consumer2; eauto.
    - hyp_consumer1'.
      basic_goal_consumer'.
    - hyp_consumer1'.
      repeat extractGKAs.
      goal_consumer2; eauto.
    - hyp_consumer1'.
      basic_goal_consumer'.
    - hyp_consumer1'.
      repeat extractGKAs.
      goal_consumer2; eauto.
    - hyp_consumer1'.
      basic_goal_consumer'.
    - hyp_consumer1'.
      repeat extractGKAs.
      goal_consumer2.
    - hyp_consumer1'.
      basic_goal_consumer'.
      econstructor; basic_goal_consumer.
    - hyp_consumer1'.
      repeat extractGKAs.
      goal_consumer2.
    - hyp_consumer1'.
      cbn [fst] in *.
      basic_goal_consumer'.
      econstructor; basic_goal_consumer.
    - hyp_consumer1'.
      repeat extractGKAs.
      goal_consumer2.
    - hyp_consumer1'.
      basic_goal_consumer'.
      econstructor; basic_goal_consumer.
  Qed.
End Proofs1.

Section Proofs2.
  Context {ifcParams' : Fifo.Ifc.Params}.
  Variable Hsize1 : size <> 1.
  Variable impl1Params impl2Params : Impl.Params.
  Local Definition regArray1 := @regArray ifcParams' impl1Params.
  Local Definition regArray2 := @regArray ifcParams' impl2Params.
  Local Definition fifoImpl1' := @Fifo.Impl.impl ifcParams' impl1Params.
  Local Definition fifoImpl2' := @Fifo.Impl.impl ifcParams' impl2Params.
  
  Variable HRegArrayCorrect : RegArrayCorrect regArray1 regArray2.

  Record myFifoImplR (regArrayR : RegsT -> RegsT -> Prop) regArrayRegs
         (o_i o_s : RegsT) : Prop :=
    {   
      implRegs : RegsT;
      enqVal : word (Fifo.Ifc.lgSize + 1);
      deqVal : word (Fifo.Ifc.lgSize + 1);
      regArray1Regs : RegsT;
      regArray2Regs : RegsT;
      implRegVal : implRegs = [(Fifo.Impl.deqPtrName,
                                existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) deqVal);
                              (Fifo.Impl.enqPtrName,
                               existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) enqVal)];
      Ho_iCorrect : o_i = implRegs ++ regArray1Regs;
      Ho_sCorrect : o_s = implRegs ++ regArray2Regs;
      Ho_iNoDup : NoDup (map fst o_i);
      Ho_sNoDup : NoDup (map fst o_s);
      HRegArrayRegs : getKindAttr regArray1Regs = regArrayRegs;
      HRegArray : regArrayR regArray1Regs regArray2Regs;
    }.
  
  Ltac Record_destruct :=
    match goal with
    |[ H : myFifoImplR _ _ _ _ |- _] => destruct H
    end.

  Goal FifoCorrect fifoImpl1' fifoImpl2'.
    destruct HRegArrayCorrect.
    rewrite <- Nat.eqb_neq in Hsize1.
    all : econstructor 1 with (fifoR := myFifoImplR regArrayR regArrayRegs)
                        (fifoRegs := [(Fifo.Impl.deqPtrName,
                                       (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))));
                                      (Fifo.Impl.enqPtrName,
                                       (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))))]
                                       ++ regArrayRegs).
    all : red; unfold fifoImpl1', fifoImpl2', impl, spec, regArray,
               isEmpty, flush, enq, deq, numFree, isFull, first,
               Impl.isEmpty, Impl.flush, Impl.enq, Impl.deq, Impl.numFree,
               Impl.isFull, Impl.first.
    all : try rewrite Hsize1; unfold Fifo1.impl, Fifo1.isEmpty,
                         Fifo1.isFull, Fifo1.flush, Fifo1.numFree, Fifo1.first,
                         Fifo1.deq, Fifo1.enq; intros; try Record_destruct.
    all : unfold regArray1, Impl.isEmpty in *.
    - hyp_consumer1'.
      basic_goal_consumer'.
    - hyp_consumer1'.
      apply SubList_map_iff in H1; dest.
      rewrite <- H5.
      goal_consumer2.
    - hyp_consumer1'.
      basic_goal_consumer.
    - hyp_consumer1'.
      apply SubList_map_iff in H1; dest.
      rewrite <- H5.
      goal_consumer2.
    - hyp_consumer1'.
      basic_goal_consumer.
    - hyp_consumer1'.
      apply SubList_map_iff in H1; dest.
      rewrite <- H5.
      goal_consumer2.
    - hyp_consumer1'.
      basic_goal_consumer'; repeat my_simpl_solver'.
    - hyp_consumer1'.
      repeat resolve_In.
      goal_consumer2.
      basic_goal_consumer'.
    - hyp_consumer1'.
      basic_goal_consumer'.
      econstructor; eauto; normalize_key_concl'.
    - hyp_consumer1'.
      repeat resolve_In.
      goal_consumer2.
      basic_goal_consumer'.
    - hyp_consumer1'.
      + basic_goal_consumer'.
        econstructor; eauto; normalize_key_concl'; repeat rewrite doUpdRegs_preserves_keys;
          normalize_key_concl'.
        gka_doUpdReg_red; normal_solver; auto.
      + basic_goal_consumer'.
        econstructor; eauto; normalize_key_concl'.
    - hyp_consumer1'.
      + repeat resolve_In.
        goal_consumer2.
        basic_goal_consumer'.
      + repeat resolve_In.
        rewrite SubList_map_iff in H1; dest.
        rewrite <- H2.
        goal_consumer2.
    - hyp_consumer1'.
      cbn [fst] in *.
      basic_goal_consumer'.
      econstructor; eauto; normalize_key_concl'.
      Unshelve.
      all : eauto; try exact nil; try exact WO.
  Qed.
  
End Proofs2.
