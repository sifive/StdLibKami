Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.Proofs.

Lemma MaybeEvalPointwise {k} (e1 e2 : Expr type (SyntaxKind (Maybe k))) :
  evalExpr (e1 @% "valid")%kami_expr = evalExpr (e2 @% "valid")%kami_expr ->
  evalExpr (e1 @% "data")%kami_expr = evalExpr (e2 @% "data")%kami_expr ->
  evalExpr e1 = evalExpr e2.
Proof.
  simpl; intros.
  apply functional_extensionality_dep; intros.
  fin_dep_destruct x; auto.
  fin_dep_destruct y; auto.
  inv y.
Qed.

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
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2; eauto.
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2; eauto.
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2; eauto.
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2.
    - hyp_consumer; goal_consumer1.
      econstructor; repeat normal_solver; repeat my_risky_solver.
    - hyp_consumer; goal_consumer2.
    - hyp_consumer; goal_consumer1.
      econstructor; repeat normal_solver; repeat my_risky_solver.
    - hyp_consumer; goal_consumer2.
    - hyp_consumer; goal_consumer1.
      econstructor; repeat normal_solver; repeat my_risky_solver.
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
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2.
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2.
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2.
    - hyp_consumer; goal_consumer1.
    - hyp_consumer; goal_consumer2; goal_consumer1.
    - hyp_consumer; goal_consumer1.
      econstructor; eauto; normalize_key_concl.
    - hyp_consumer; goal_consumer2; goal_consumer1.
    - hyp_consumer; goal_consumer1; econstructor; eauto; normalize_key_concl;
      repeat rewrite doUpdRegs_preserves_keys; normalize_key_concl.
      gka_doUpdReg_red; normal_solver; auto.
    - hyp_consumer; goal_consumer2; goal_consumer1.
    - hyp_consumer; goal_consumer1.
      econstructor; eauto; normalize_key_concl.
      Unshelve.
      all : eauto; try exact nil; try exact WO.
  Qed.
  
End Proofs2.

Section Proofs3.
  
  Context {ifcParams' : Fifo.Ifc.Params}.
  Variable implParams : Impl.Params.
  Local Definition fifoImpl := @Fifo.Impl.impl ifcParams' implParams.
  Local Definition fifoSpec := @Fifo.Spec.spec ifcParams'.

  Section Size1.
    Variable Hsize1 : size = 1.

    Record myFifoR  (o_i o_s : RegsT) : Prop :=
      {
        implRegs : RegsT;
        specRegs : RegsT;
        fifo1_bval : bool;
        fifo1_dval : type k;
        implRegVal : implRegs = [(Fifo1.validRegName,
                                  existT _ (SyntaxKind Bool) fifo1_bval);
                                (Fifo1.dataRegName,
                                 existT _ (SyntaxKind k) fifo1_dval)];
        specRegVal : specRegs = [(Spec.listName,
                                  existT (fullType type) (Spec.nlist type) (if fifo1_bval
                                                                            then [fifo1_dval]
                                                                            else nil))];
        Ho_iCorrect1 : o_i = implRegs;
        Ho_sCorrect1 : o_s = specRegs;
        Ho_iNoDup1' : NoDup (map fst o_i);
      }.

    Ltac Record_destruct :=
      match goal with
      |[ H : myFifoR _ _ |- _] => destruct H
      end.
    
    Goal FifoCorrect fifoImpl fifoSpec.
      rewrite <- Nat.eqb_eq in Hsize1.
      all : econstructor 1 with (fifoR := myFifoR)
                                (fifoRegs := [(Fifo1.validRegName,
                                               SyntaxKind Bool);
                                              (Fifo1.dataRegName,
                                               SyntaxKind k)]).
      all : red; unfold fifoImpl, fifoSpec, impl, spec, regArray,
                 isEmpty, flush, enq, deq, numFree, isFull, first,
                 Impl.isEmpty, Impl.flush, Impl.enq, Impl.deq, Impl.numFree,
                 Impl.isFull, Impl.first,
                 Spec.isEmpty, Spec.flush, Spec.enq, Spec.deq, Spec.numFree,
                 Spec.isFull, Spec.first.
      all : try rewrite Hsize1; unfold Fifo1.impl, Fifo1.isEmpty,
                                Fifo1.isFull, Fifo1.flush, Fifo1.numFree, Fifo1.first,
                                Fifo1.deq, Fifo1.enq; intros; try Record_destruct.
      all : rewrite Nat.eqb_eq in Hsize1.
      - hyp_consumer; goal_consumer1.
        destruct x; auto.
      - hyp_consumer; goal_consumer2; eauto.
      - hyp_consumer; goal_consumer1.
        destruct x; simpl; symmetry.
        + rewrite negb_true_iff, Nat.ltb_ge.
          lia.
        + rewrite negb_false_iff, Nat.ltb_lt.
          lia.
      - hyp_consumer; goal_consumer2; eauto.
      - hyp_consumer; goal_consumer1.
        destruct x; simpl; rewrite Hsize1; arithmetizeWord; auto.
      - hyp_consumer; goal_consumer2; eauto.
      - hyp_consumer; goal_consumer1.
        destruct x; cbn[Spec.getHead emptyb negb]; apply functional_extensionality_dep; intros;
          fin_dep_destruct x; auto; fin_dep_destruct y; auto.
      - hyp_consumer; goal_consumer2.
      - hyp_consumer; goal_consumer1.
        +  destruct x; cbn[Spec.getHead emptyb negb]; apply functional_extensionality_dep; intros;
             fin_dep_destruct x; auto; fin_dep_destruct y; auto.
        + econstructor; eauto; normalize_key_concl.
          destruct x; simpl; auto.
      - hyp_consumer; goal_consumer2.
      - hyp_consumer; goal_consumer1.
        + destruct x; simpl; symmetry.
          * rewrite Nat.ltb_ge; lia.
          * rewrite Nat.ltb_lt; lia.
        + econstructor; eauto; normalize_key_concl.
          destruct x; cbv[Spec.snocInBound]; rewrite Hsize1; simpl; reflexivity.
      - hyp_consumer; goal_consumer2.
      - hyp_consumer; goal_consumer1.
        econstructor; eauto; normalize_key_concl.
    Qed.
  
  End Size1.

  Section SizeGT1.
    Variable Hsize1 : size <> 1.
    
  End SizeGT1.

End Proofs3.
