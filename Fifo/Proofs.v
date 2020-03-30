Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.Proofs.

Lemma emptyb_true {A : Type} (l : list A) :
  emptyb l = true <-> l = nil.
Proof.
  red; split; destruct l; intros; auto; discriminate.
Qed.

Lemma emptyb_false {A : Type} (l : list A) :
  emptyb l = false <-> exists x, In x l.
Proof.
  red; split; destruct l; intros; auto; try discriminate.
  - exists a; left; reflexivity.
  - dest; inv H.
Qed.

Lemma emptyb_true_len {A : Type} (l : list A) :
  emptyb l = true <-> length l = 0.
Proof.
  rewrite length_zero_iff_nil; apply emptyb_true.
Qed.

Lemma emptyb_false_len {A : Type} (l : list A) :
  emptyb l = false <-> 0 < length l.
Proof.
  rewrite emptyb_false; red; split; intros; dest.
  - destruct l; [inv H| simpl; lia].
  - destruct l; [simpl in H; lia| exists a; left; reflexivity].
Qed.

Lemma hd_error_Some {A : Type} (l : list A) (a : A) :
  hd_error l = Some a <-> l = a :: tl l.
Proof.
  red; split; intros.
  - destruct l; inv H; reflexivity.
  - rewrite H; reflexivity.
Qed.

Lemma hd_error_None {A : Type} (l : list A) :
  hd_error l = None <-> l = nil.
Proof.
  red; split; intros.
  - destruct l; auto; discriminate.
  - destruct l; auto; discriminate.
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
  (* Context {raIfcParams' : RegArray.Ifc.Params}. *)
  
  Variable pow2 : Nat.pow 2 (Nat.log2_up size) = size.
  Local Definition implParams : Fifo.Impl.Params := 
    {|Impl.sizePow2 :=  pow2
      ; Impl.regArray := RegArray.Spec.spec|}.
  
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
        destruct x; cbn[Spec.getHead emptyb negb]; apply functional_extensionality_dep;
          intros; fin_dep_destruct x; auto; fin_dep_destruct y; auto.
      - hyp_consumer; goal_consumer2.
      - hyp_consumer; goal_consumer1.
        +  destruct x; cbn[Spec.getHead emptyb negb]; apply functional_extensionality_dep;
             intros; fin_dep_destruct x; auto; fin_dep_destruct y; auto.
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
    Definition listInSpec (len start : nat) (arr : Fin.t size -> type k) :=
      cutList len (rotateList start (convertToList arr)).

    Record myFifoSpecR (o_i o_s : RegsT) : Prop :=
    {   
      implRegs : RegsT;
      specRegs : RegsT;
      regArray : RegsT;
      queueLen : Z;
      enqVal : word (Fifo.Ifc.lgSize + 1);
      deqVal : word (Fifo.Ifc.lgSize + 1);
      arrayVal : Fin.t size -> type k;
      HqueueLen : queueLen = wordVal _ (enqVal ^- deqVal);
      Hbound : (queueLen <= Z.of_nat size)%Z;
      implRegVal : implRegs = [(Fifo.Impl.deqPtrName,
                                existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) deqVal);
                              (Fifo.Impl.enqPtrName,
                               existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) enqVal)];
      regArrayVal : regArray = [((name ++ ".regArray")%string,
                                  existT _ (SyntaxKind (Array size k)) arrayVal)];
      specRegVal : specRegs = [(Spec.listName,
                                     existT (fullType type) (Fifo.Spec.nlist type)
                                            (listInSpec (Z.to_nat queueLen) (wordToNat deqVal)
                                                        arrayVal))];
      Ho_iCorrect : o_i = implRegs ++ regArray;
      Ho_sCorrect : o_s = specRegs;
      Ho_iNoDup' : NoDup (map fst o_i);
    }.

    Ltac Record_destruct :=
      match goal with
      |[ H : myFifoSpecR _ _ |- _] => destruct H
      end.
    
    Goal FifoCorrect fifoImpl fifoSpec.
      assert (size <> 0) as P.
      { destruct size; auto. }
      assert (2 ^ (lgSize + 1) <> 0) as P0.
      { unfold lgSize; intro P0.
        rewrite Nat.pow_add_r, pow2 in P0.
        destruct size; simpl in pow2; try lia.
        simpl in P0; lia.
      }
      rewrite <- Nat.eqb_neq in Hsize1.
      all : econstructor 1 with (fifoR := myFifoSpecR)
                                (fifoRegs := [(Fifo.Impl.deqPtrName,
                                               SyntaxKind (Bit (Fifo.Ifc.lgSize + 1)));
                                              (Fifo.Impl.enqPtrName,
                                               SyntaxKind (Bit (Fifo.Ifc.lgSize + 1)));
                                              (Spec.arrayName,
                                               (SyntaxKind (Array size k)))]).
      all : red; unfold fifoImpl, fifoSpec, impl, spec, regArray,
                 isEmpty, flush, enq, deq, numFree, isFull, first,
                 Impl.isEmpty, Impl.flush, Impl.enq, Impl.deq, Impl.numFree,
                 Impl.isFull, Impl.first,
                 Spec.isEmpty, Spec.flush, Spec.enq, Spec.deq, Spec.numFree,
                 Spec.isFull, Spec.first.
      all : try rewrite Hsize1; rewrite Nat.eqb_neq in Hsize1.
      all : unfold Ifc.read, Ifc.write, regArray, implParams, Spec.spec, Spec.read, Spec.write,
        Impl.isEmpty, Ifc.size, Ifc.k; intros; try Record_destruct.
      - hyp_consumer.
        goal_consumer1; simpl.
        destruct weq; subst; simpl; symmetry; unfold listInSpec.
        + rewrite Z.sub_diag, Zmod_0_l, cutList_nil_0; reflexivity.
        + rewrite emptyb_false_len, cutList_length;
            [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
          specialize (Nat.le_0_l
                        (Z.to_nat ((wordVal (lgSize + 1) x1
                                    - wordVal (lgSize + 1) x) mod 2 ^ Z.of_nat (lgSize + 1))))
            as P1.
          destruct (le_lt_or_eq _ _ P1); auto.
          exfalso.
          apply neq_wordVal in n; apply n.
          specialize (wordBound _ x) as P2; specialize (wordBound _ x1) as P3.
          rewrite boundProofZIff in *.
          simpl in Hbound.
          symmetry in H0.
          assert (0 = Z.to_nat 0) as TMP by lia; rewrite TMP in H0; clear TMP.
          apply Z2Nat.inj in H0; try lia; [|apply Z.mod_pos_bound; lia].
          apply Znumtheory.Zmod_divide_minus in H0; try lia.
          rewrite Z.sub_0_r in H0; unfold Z.divide in H0; dest.
          unfold lgSize in *.
          rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *.
          destruct (Z_dec 0 x0) as [[P2 | P2] | P2]; try lia.
          * apply Zlt_le_succ in P2; simpl in P2; try lia.
            apply (Z.mul_le_mono_nonneg_r _ _ (Z.of_nat size * 2)) in P2; lia.
          * apply Z.gt_lt in P2.
            rewrite Z.lt_le_pred in P2; simpl in P2.
            apply (Z.mul_le_mono_nonneg_r _ _ (Z.of_nat size * 2)) in P2; lia.
      - hyp_consumer.
        goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer1; simpl.
        destruct weq; simpl; symmetry; unfold listInSpec.
        + rewrite negb_true_iff, Nat.ltb_ge, cutList_length;
            [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
          destruct (Zle_lt_or_eq _ _ Hbound); simpl in *; try lia.
          exfalso; rewrite <- e in H0; simpl in H0.
          rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
          Zminus_mod_idemp_l, Z.add_simpl_l, Z.mod_small in H0; try lia.
          unfold lgSize in *.
          rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
        + rewrite negb_false_iff, Nat.ltb_lt, cutList_length;
            [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
          destruct (Zle_lt_or_eq _ _ Hbound); simpl in *; try lia.
          exfalso.
          apply neq_wordVal in n; apply n; simpl.
          rewrite <- H0, Zplus_mod_idemp_l.
          repeat rewrite Zplus_mod_idemp_r.
          rewrite Zplus_minus, (wordBound _ x1); reflexivity.
      - hyp_consumer.
        goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer1; simpl; unfold listInSpec; rewrite cutList_length;
          [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
        arithmetizeWord; destruct x, x1; simpl in *.
        rewrite Zminus_mod_idemp_l.
        rewrite (Z.mod_small
                   (Z.of_nat size - (wordVal0 - wordVal) mod 2 ^ Z.of_nat (lgSize + 1))
                   (2 ^ Z.of_nat (lgSize + 1))).
        + rewrite Nat2Z.inj_sub, Z2Nat.id; try lia.
          apply Z.mod_pos_bound.
          unfold lgSize in *.
          rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
        + unfold lgSize in *.
          rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; try lia.
          specialize (Z.mod_pos_bound (wordVal0 - wordVal) (Z.of_nat size * 2) ltac:(lia)) as P1;
            lia.
      - hyp_consumer.
        goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer1.
        apply functional_extensionality_dep.
        intros; fin_dep_destruct x.
        + simpl; destruct weq; subst; simpl; symmetry; unfold listInSpec.
          * rewrite negb_false_iff, Z.sub_diag, Zmod_0_l, cutList_nil_0; reflexivity.
          * rewrite negb_true_iff, emptyb_false_len, cutList_length;
              [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
            specialize (Nat.le_0_l
                          (Z.to_nat ((wordVal (lgSize + 1) x10
                                     - wordVal (lgSize + 1) x6)
                                       mod 2 ^ Z.of_nat (lgSize + 1)))) as P1.
            destruct (le_lt_or_eq _ _ P1); auto.
            exfalso.
            specialize (wordBound _ x6) as P2; specialize (wordBound _ x10) as P3.
            rewrite boundProofZIff in *.
            apply neq_wordVal in n; apply n.
            unfold lgSize in *.
            rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; try lia.
            assert (0 = Z.to_nat 0) as TMP by auto; rewrite TMP in H1 at 1; clear TMP.
            apply Z2Nat.inj in H1; [|lia |apply Z.mod_pos_bound; lia ].
            symmetry in H1.
            apply Z.mod_divide in H1; try lia; unfold Z.divide in H1; dest.
            destruct (Z_dec 0 x) as [[P2 | P2] | P2]; try lia.
            -- apply Zlt_le_succ in P2; simpl in P2; try lia.
               apply (Z.mul_le_mono_nonneg_r _ _ (Z.of_nat size * 2)) in P2; lia.
            -- apply Z.gt_lt in P2.
               rewrite Z.lt_le_pred in P2; simpl in P2.
               apply (Z.mul_le_mono_nonneg_r _ _ (Z.of_nat size * 2)) in P2; lia.
        + fin_dep_destruct y; auto; unfold Spec.getHead; simpl; destruct weq; simpl;
            unfold listInSpec.
          * rewrite e, Z.sub_diag, Zmod_0_l, cutList_nil_0; reflexivity.
          * destruct lt_dec.
            -- simpl in Hbound.
              admit.
            -- exfalso.
               unfold lgSize in *.
               rewrite <- Zpow_of_nat, pow2 in *.
               apply n0.
               specialize (Z.mod_pos_bound
                             (wordVal (Nat.log2_up size + 1) x6)
                             (Z.of_nat size)
                             ltac:(lia)) as P1; lia.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        goal_consumer1.
        + apply functional_extensionality_dep.
          intros; fin_dep_destruct x.
          * simpl.
            destruct weq; subst; simpl; symmetry; unfold listInSpec.
            -- rewrite Z.sub_diag, Zmod_0_l, cutList_nil_0; reflexivity.
            -- rewrite negb_true_iff.
               rewrite emptyb_false_len, cutList_length;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               specialize (Nat.le_0_l
                             (Z.to_nat ((wordVal (lgSize + 1) x19
                                         - wordVal (lgSize + 1) x13)
                                          mod 2 ^ Z.of_nat (lgSize + 1))))
                 as P1.
               destruct (le_lt_or_eq _ _ P1); auto.
               exfalso.
               apply neq_wordVal in n; apply n.
               specialize (wordBound _ x13) as P2; specialize (wordBound _ x19) as P3.
               rewrite boundProofZIff in *.
               simpl in Hbound.
               symmetry in H1.
               assert (0 = Z.to_nat 0) as TMP by lia; rewrite TMP in H1; clear TMP.
               apply Z2Nat.inj in H1; try lia; [|apply Z.mod_pos_bound; lia].
               apply Znumtheory.Zmod_divide_minus in H1; try lia.
               rewrite Z.sub_0_r in H1; unfold Z.divide in H1; dest.
               unfold lgSize in *.
               rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *.
               destruct (Z_dec 0 x) as [[P2 | P2] | P2]; try lia.
               ++ apply Zlt_le_succ in P2; simpl in P2; try lia.
                  apply (Z.mul_le_mono_nonneg_r _ _ (Z.of_nat size * 2)) in P2; lia.
               ++ apply Z.gt_lt in P2.
                  rewrite Z.lt_le_pred in P2; simpl in P2.
                  apply (Z.mul_le_mono_nonneg_r _ _ (Z.of_nat size * 2)) in P2; lia.
          * fin_dep_destruct y; auto; unfold Spec.getHead; simpl; destruct weq; simpl;
            unfold listInSpec.
            -- rewrite e, Z.sub_diag, Zmod_0_l, cutList_nil_0; reflexivity.
            -- destruct lt_dec.
               ++ admit.
               ++ exfalso.
                  unfold lgSize in *.
                  rewrite <- Zpow_of_nat, pow2 in *.
                  apply n0.
                  specialize (Z.mod_pos_bound
                                (wordVal (Nat.log2_up size + 1) x13)
                                (Z.of_nat size)
                                ltac:(lia)) as P1; lia.
        + admit.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        rewrite <- H0 in *.
        + goal_consumer1.
          * simpl.
            destruct weq; symmetry; unfold listInSpec.
            -- clear H27 H28.
               rewrite Nat.ltb_ge, cutList_length;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound); simpl in *; try lia.
               exfalso; rewrite <- e in H4; simpl in H4.
               rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
               Zminus_mod_idemp_l, Z.add_simpl_l, Z.mod_small in H4; try lia.
               unfold lgSize in *.
               rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
            -- clear H27 H28; simpl.
               rewrite Nat.ltb_lt, cutList_length;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound); simpl in *; try lia.
               exfalso.
               apply neq_wordVal in n; apply n; simpl.
               rewrite <- H4, Zplus_mod_idemp_l.
               repeat rewrite Zplus_mod_idemp_r.
               rewrite Zplus_minus, (wordBound _ x10); reflexivity.
          * admit.
        + goal_consumer1.
          * simpl.
            destruct weq; symmetry; unfold listInSpec; simpl.
            -- rewrite Nat.ltb_ge, cutList_length;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound); simpl in *; try lia.
               exfalso; rewrite <- e in H0; simpl in H0.
               rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
               Zminus_mod_idemp_l, Z.add_simpl_l, Z.mod_small in H0; try lia.
               unfold lgSize in *.
               rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
            -- rewrite Nat.ltb_lt, cutList_length;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound); simpl in *; try lia.
               exfalso.
               apply neq_wordVal in n; apply n; simpl.
               rewrite <- H0, Zplus_mod_idemp_l.
               repeat rewrite Zplus_mod_idemp_r.
               rewrite Zplus_minus, (wordBound _ x10); reflexivity.
          * admit.
      - hyp_consumer.
        + goal_consumer2.
        + goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer2.
        econstructor 1 with (enqVal := $ 0) (deqVal := $ 0); eauto.
        + simpl; rewrite Zmod_0_l; lia.
        + simpl; doUpdRegs_red; reflexivity.
        + simpl; doUpdRegs_red; unfold listInSpec.
          rewrite cutList_nil_0; reflexivity.
        + rewrite doUpdRegs_preserves_keys; normalize_key_concl.
    Admitted.
    
  End SizeGT1.

End Proofs3.
