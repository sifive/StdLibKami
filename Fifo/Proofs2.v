Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.Spec.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import StdLibKami.Fifo.CorrectDef.

Section Proofs.
  
  Context {ifcParams' : Fifo.Ifc.Params}.
  
  Variable pow2 : Nat.pow 2 (Nat.log2_up size) = size.
  Local Definition implParams : Fifo.Impl.Params := 
    {|Impl.sizePow2 :=  pow2
      ; Impl.regArray := RegArray.Spec.spec|}.
  
  Local Definition fifoImpl := @Fifo.Impl.impl ifcParams' implParams.
  Local Definition fifoSpec := @Fifo.Spec.spec ifcParams'.

  Section Size1.
    Variable Hsize1 : size = 1.

    Record myFifoR  (implRegs specRegs : RegsT) (fifo1_bval : bool) (fifo1_dval : type k)
           (o_i o_s : RegsT) : Prop :=
      {
        implRegVal'' : implRegs = [(Fifo1.validRegName,
                                  existT _ (SyntaxKind Bool) fifo1_bval);
                                (Fifo1.dataRegName,
                                 existT _ (SyntaxKind k) fifo1_dval)];
        specRegVal : specRegs = [(Spec.listName,
                                  existT (fullType type) Spec.nlist (if fifo1_bval
                                                                            then [fifo1_dval]
                                                                            else nil))];
        Ho_iCorrect1' : o_i = implRegs;
        Ho_sCorrect1' : o_s = specRegs;
        Ho_iNoDup1' : NoDup (map fst o_i);
      }.

    Ltac Record_destruct :=
      match goal with
      |[ H : exists _ _ _ _, myFifoR _ _ _ _ _ _ |- _] =>
       let implRegs := fresh "implRegs" in
       let specRegs := fresh "specRegs" in
       let fifo1_bval := fresh "fifo1_bval" in
       let fifo1_dval := fresh "fifo1_dval" in
       let H0 := fresh "H" in
       destruct H as [implRegs [specRegs [fifo1_bval [fifo1_dval H0]]]]; destruct H0
      end.
    
    Goal FifoCorrect fifoImpl fifoSpec.
      rewrite <- Nat.eqb_eq in Hsize1.
      all : econstructor 1 with (fifoR := (fun o1 o2 =>
                                             (exists implRegs specRegs
                                                     fifo1_bval fifo1_dval,
                                                 myFifoR implRegs specRegs
                                                         fifo1_bval fifo1_dval o1 o2)))
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
      - hyp_consumer; goal_consumer2; eauto.
    Qed.
  
  End Size1.

  Section SizeGT1.
    Variable Hsize1 : size <> 1.
    Definition listInSpec (len start : nat) (arr : Fin.t size -> type k) :=
      firstn len (rotateList start (convertToList arr)).

    Record myFifoSpecR (implRegs specRegs regArray : RegsT) (queueLen : Z)
           (enqVal deqVal : word (Fifo.Ifc.lgSize + 1)) (arrayVal : Fin.t size -> type k)
           (o_i o_s : RegsT) : Prop :=
    {
      HqueueLen : queueLen = wordVal _ (enqVal ^- deqVal);
      Hbound : (queueLen <= Z.of_nat size)%Z;
      gt1_implRegVal : implRegs = [(Fifo.Impl.deqPtrName,
                                existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) deqVal);
                              (Fifo.Impl.enqPtrName,
                               existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) enqVal)];
      regArrayVal : regArray = [((name ++ ".regArray")%string,
                                  existT _ (SyntaxKind (Array size k)) arrayVal)];
      gt_1specRegVal : specRegs = [(Spec.listName,
                                     existT (fullType type) Fifo.Spec.nlist
                                            (listInSpec (Z.to_nat queueLen)
                                                        (Z.to_nat ((wordVal _ deqVal)
                                                         mod (2 ^ Z.of_nat (Nat.log2_up size))))
                                                        arrayVal))];
      gt_Ho_iCorrect : o_i = implRegs ++ regArray;
      gt_Ho_sCorrect : o_s = specRegs;
      Ho_iNoDup' : NoDup (map fst o_i);
    }.

    Ltac Record_destruct :=
      match goal with
      |[ H : exists _ _ _ _ _ _ _,
           myFifoSpecR _ _ _ _ _ _ _ _ _ |- _] =>
       let implRegs := fresh "implRegs" in
       let specRegs := fresh "specRegs" in
       let regArray := fresh "regArray" in
       let queueLen := fresh "queueLen" in
       let enqVal := fresh "enqVal" in
       let deqVal := fresh "deqVal" in
       let arrayVal := fresh "arrayVal" in
       let H0 := fresh "H" in
       destruct H as [implRegs
                        [specRegs
                           [regArray
                              [queueLen [enqVal [deqVal [arrayVal H0]]]]]]]; destruct H0
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
      all : econstructor 1 with (fifoR := (fun o1 o2 =>
                                             (exists implRegs specRegs regArray queueLen
                                                     enqVal deqVal arrayVal,
                                                 myFifoSpecR implRegs specRegs regArray
                                                             queueLen enqVal deqVal arrayVal
                                                             o1 o2)))
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
                 Spec.read, Spec.isEmpty, Spec.flush, Spec.enq, Spec.deq, Spec.numFree,
                 Spec.isFull, Spec.first.
      all : try rewrite Hsize1; rewrite Nat.eqb_neq in Hsize1.
      all : unfold Ifc.read, Ifc.write, regArray, 
            implParams, Spec.spec, Spec.read, Spec.write,
            Impl.isEmpty, RegArray.Spec.spec, Spec.read, Spec.write, RegArray.Ifc.size,
            RegArray.Ifc.k; intros; try Record_destruct.
      - hyp_consumer.
        goal_consumer1; simpl.
        destruct weq; subst; simpl; symmetry; unfold listInSpec.
        + rewrite Z.sub_diag, Zmod_0_l, firstn_O; reflexivity.
        + rewrite emptyb_false_len, firstn_length_le;
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
          simpl in Hbound0.
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
        + rewrite negb_true_iff, Nat.ltb_ge, firstn_length_le;
            [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
          destruct (Zle_lt_or_eq _ _ Hbound0); simpl in *; try lia.
          exfalso; rewrite <- e in H0; simpl in H0.
          rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
          Zminus_mod_idemp_l, Z.add_simpl_l, Z.mod_small in H0; try lia.
          unfold lgSize in *.
          rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
        + rewrite negb_false_iff, Nat.ltb_lt, firstn_length_le;
            [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
          destruct (Zle_lt_or_eq _ _ Hbound0); simpl in *; try lia.
          exfalso.
          apply neq_wordVal in n; apply n; simpl.
          rewrite <- H0, Zplus_mod_idemp_l.
          repeat rewrite Zplus_mod_idemp_r.
          rewrite Zplus_minus, (wordBound _ x1); reflexivity.
      - hyp_consumer.
        goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer1; simpl; unfold listInSpec; rewrite firstn_length_le;
          [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
        arithmetizeWord; destruct x, x1; simpl in *.
        rewrite Zminus_mod_idemp_l.
        rewrite (Z.mod_small
                   (Z.of_nat size - (wordVal0 - wordVal) mod 2 ^ Z.of_nat (lgSize + 1))
                   (2 ^ Z.of_nat (lgSize + 1))).
        + rewrite Nat2Z.inj_sub, Z2Nat.id; try lia.
          * rewrite <- (Z.mod_small
                          (Z.of_nat size - (wordVal0 - wordVal) mod 2 ^ Z.of_nat (lgSize + 1))
                          (2 ^ Z.of_nat (lgSize + 1))) at 1; auto; split; try lia.
            unfold lgSize in *.
            rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *.
            specialize (Z.mod_pos_bound (wordVal0 - wordVal) (Z.of_nat size * 2) ltac:(lia))
              as TMP; lia.
          * apply Z.mod_pos_bound.
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
          * rewrite negb_false_iff, Z.sub_diag, Zmod_0_l, firstn_O; reflexivity.
          * rewrite negb_true_iff, emptyb_false_len, firstn_length_le;
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
        + fin_dep_destruct y; auto; unfold Spec.getHead; simpl; destruct weq; unfold listInSpec.
          * rewrite e, Z.sub_diag, Zmod_0_l, firstn_O; reflexivity.
          * destruct lt_dec.
            -- simpl in Hbound0.
               specialize (wordBound _ x10) as P1.
               specialize (wordBound _ x6) as P2.
               rewrite boundProofZIff in *.
               cbn [getBool negb].
               assert (x10 <> x6) as n' by auto; clear n.
               apply neq_wordVal in n'.
               specialize (hdCorrect x19 P1 P2 Hbound0 pow2 n') as P3.
               rewrite hd_error_Some in P3.
               unfold lgSize in *.
               destruct (firstn _ _); [discriminate|].
               inv P3; simpl.
               f_equal.
               apply of_nat_ext.
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
            -- rewrite Z.sub_diag, Zmod_0_l, firstn_O; reflexivity.
            -- rewrite negb_true_iff.
               rewrite emptyb_false_len, firstn_length_le;
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
               simpl in Hbound0.
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
            -- rewrite e, Z.sub_diag, Zmod_0_l, firstn_O; reflexivity.
            -- destruct lt_dec.
               ++ simpl in Hbound0.
                  specialize (wordBound _ x19) as P1.
                  specialize (wordBound _ x13) as P2.
                  rewrite boundProofZIff in *.
                  cbn [getBool negb].
                  assert (x19 <> x13) as n' by auto; clear n.
                  apply neq_wordVal in n'.
                  specialize (hdCorrect x29 P1 P2 Hbound0 pow2 n') as P3.
                  rewrite hd_error_Some in P3.
                  unfold lgSize in *.
                  destruct (firstn _ _); [discriminate|].
                  inv P3; simpl.
                  f_equal.
                  apply of_nat_ext.
               ++ exfalso.
                  unfold lgSize in *.
                  rewrite <- Zpow_of_nat, pow2 in *.
                  apply n0.
                  specialize (Z.mod_pos_bound
                                (wordVal (Nat.log2_up size + 1) x13)
                                (Z.of_nat size)
                                ltac:(lia)) as P1; lia.
        + econstructor 1; auto; normalize_key_concl; simpl.
          * destruct weq; simpl.
            -- simpl in Hbound0.
               rewrite Zmod_0_l, Z.add_0_r; repeat rewrite Zminus_mod_idemp_r; auto.
            -- simpl in Hbound0.
               rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zminus_mod_idemp_r.
               specialize (wordBound _ x13) as P1.
               specialize (wordBound _ x19) as P2.
               rewrite boundProofZIff in *.
               assert (x19 <> x13) as n' by auto.
               apply neq_wordVal in n'.
               specialize (cutLen_pred P2 P1 Hbound0 pow2 n') as P3; unfold lgSize in *.
               rewrite P3; lia.
          * repeat f_equal.
            specialize (wordBound _ x13) as P1.
            specialize (wordBound _ x19) as P2.
            rewrite boundProofZIff in *.
            destruct weq; simpl; subst; unfold listInSpec, lgSize in *.
            -- rewrite Z.sub_diag, Zmod_0_l, Z.add_0_r.
               repeat rewrite Zminus_mod_idemp_r.
               rewrite Z.sub_diag, Zmod_0_l; repeat rewrite firstn_O; reflexivity.
            -- rewrite tailCorrect; auto.
               rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zminus_mod_idemp_r.
               assert (x19 <> x13) as n' by auto.
               apply neq_wordVal in n'.
               specialize (cutLen_pred P2 P1 Hbound0 pow2 n') as P3; unfold lgSize in *.
               rewrite P3, Z2Nat.inj_sub; try lia.
               rewrite rotateList_periodic at 1.
               unfold convertToList at 1.
               rewrite <- list_arr_length.
               do 2 f_equal.
               rewrite Zmod_mod', <- Zpow_of_nat, Nat2Z.id, pow2;
                 [| rewrite <-Zpow_of_nat, pow2; lia
                  | apply Z.mod_pos_bound; lia].
               dest.
               rewrite Nat2Z.inj_add, Z.pow_add_r, <-Zpow_of_nat, pow2, Z.pow_1_r in *; try lia.
               apply Zlt_le_succ in H7.
               rewrite <- Z.add_1_r in H7.
               destruct (Zle_lt_or_eq _ _ H7).
               ++ rewrite (Z.mod_small (_ + _) _); try lia.
                  rewrite <- (Nat2Z.id size) at 3;
                    rewrite <- (Nat2Z.id size) at 5.
                  repeat rewrite <- Zmod_mod'; try lia.
                  ** rewrite Z.add_mod_idemp_l; lia.
                  ** apply OMEGA2; [apply Z.mod_pos_bound|]; lia.
               ++ rewrite H8, Z_mod_same_full, Nat.mod_0_l; auto.
                  rewrite <- (Nat2Z.id size) at 3.
                  rewrite <- Zmod_mod', Zplus_mod_idemp_l, Zmod_mod'
                  , H8, Z.mul_comm, <- Zmod_mod', Z.mod_mul; try lia.
                  apply OMEGA2; [apply Z.mod_pos_bound|]; lia.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        rewrite <- H0 in *.
        + goal_consumer1.
          * simpl.
            destruct weq; symmetry; unfold listInSpec.
            -- clear H27 H28.
               rewrite Nat.ltb_ge, firstn_length_le;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound0); simpl in *; try lia.
               exfalso; rewrite <- e in H4; simpl in H4.
               rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
               Zminus_mod_idemp_l, Z.add_simpl_l, Z.mod_small in H4; try lia.
               unfold lgSize in *.
               rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
            -- clear H27 H28; simpl.
               rewrite Nat.ltb_lt, firstn_length_le;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound0); simpl in *; try lia.
               exfalso.
               apply neq_wordVal in n; apply n; simpl.
               rewrite <- H4, Zplus_mod_idemp_l.
               repeat rewrite Zplus_mod_idemp_r.
               rewrite Zplus_minus, (wordBound _ x10); reflexivity.
          * simpl in H17; rewrite negb_true_iff in H17.
            destruct weq; try discriminate; clear H17.
            apply neq_wordVal in n.
            simpl in n.
            specialize (wordBound _ x10) as P1.
            specialize (wordBound _ x8) as P2.
            rewrite boundProofZIff in *.
            simpl in Hbound0.
            assert (((wordVal (Nat.log2_up size + 1) x10 - wordVal (Nat.log2_up size + 1) x8)
                       mod 2 ^ Z.of_nat (Nat.log2_up size + 1))%Z <> Z.of_nat size) as P3.
            { intro; apply n; unfold lgSize in *.
              rewrite <- H4, Zplus_mod_idemp_l;
                repeat rewrite Zplus_mod_idemp_r.
              rewrite Zplus_minus, Z.mod_small; auto.
            }
            econstructor 1; auto; normalize_key_concl; simpl.
            -- specialize (cutLen_succ x27 P1 P2 Hbound0 pow2) as P4; unfold lgSize in *.
               rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zminus_mod_idemp_l, P4; lia.
            -- repeat f_equal.
               unfold Spec.snocInBound, listInSpec.
               destruct Nat.ltb eqn:G.
               ++ rewrite Nat.ltb_lt, firstn_length_le in G;
                    [| unfold convertToList; rewrite rotateLength, <- list_arr_length; lia].
                  unfold lgSize in *.
                  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zminus_mod_idemp_l.
                  rewrite (listSnoc x27 P1 P2 Hbound0 pow2); auto.
                  repeat f_equal.
                  apply functional_extensionality; intro.
                  apply if_bool_2.
                  destruct eqb eqn:G0, weq; auto.
                  ** exfalso.
                     apply n0.
                     rewrite eqb_eq in G0; rewrite G0, to_nat_of_nat; simpl.
                     arithmetizeWord.
                     destruct x10; simpl.
                     rewrite Z2Nat.id, Zmod_mod; auto.
                     apply Z.mod_pos_bound.
                     rewrite <- Zpow_of_nat, pow2; lia.
                  ** exfalso.
                     rewrite Fin_eqb_neq in G0.
                     apply G0.
                     arithmetizeWord; destruct x10; simpl in *.
                     rewrite <- Zpow_of_nat, <- mod_Zmod, <- (Z2Nat.id (wordVal mod _)) in H4
                     ; try lia.
                     apply Nat2Z.inj in H4.
                     rewrite Zmod_mod', Nat2Z.id in H4; try lia.
                     rewrite (Nat.mod_small (proj1_sig _)) in H4.
                     --- apply to_nat_inj.
                         rewrite <- H4, to_nat_of_nat; simpl.
                         rewrite <- (Nat2Z.id (2 ^ _)), <- Zmod_mod', Zpow_of_nat; try lia.
                     --- rewrite pow2.
                         apply fin_to_nat_bound.
               ++ exfalso.
                  rewrite Nat.ltb_ge, firstn_length_le in G.
                  ** apply P3.
                     apply inj_le in G.
                     rewrite Z2Nat.id in G; try lia.
                     apply Z.le_antisymm; auto.
                  ** unfold convertToList; rewrite rotateLength, <- list_arr_length; lia.
        + goal_consumer1.
          * simpl.
            destruct weq; symmetry; unfold listInSpec.
            -- rewrite Nat.ltb_ge, firstn_length_le;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound0); simpl in *; try lia.
               exfalso; rewrite <- e in H0; simpl in H0.
               rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
               Zminus_mod_idemp_l, Z.add_simpl_l, Z.mod_small in H0; try lia.
               unfold lgSize in *.
               rewrite <- Zpow_of_nat, Nat.pow_add_r, pow2, Nat2Z.inj_mul in *; simpl in *; lia.
            -- rewrite Nat.ltb_lt, firstn_length_le;
                 [|simpl in *; rewrite rotateLength, <- list_arr_length; lia].
               destruct (Zle_lt_or_eq _ _ Hbound0); simpl in *; try lia.
               exfalso.
               apply neq_wordVal in n; apply n; simpl.
               rewrite <- H0, Zplus_mod_idemp_l.
               repeat rewrite Zplus_mod_idemp_r.
               rewrite Zplus_minus, (wordBound _ x10); reflexivity.
          * simpl in H17; rewrite negb_false_iff in H17.
            destruct weq; try discriminate; clear H17.
            specialize (wordBound _ x10) as P1.
            specialize (wordBound _ x8) as P2.
            rewrite boundProofZIff in *.
            simpl in Hbound0.
            assert (((wordVal (Nat.log2_up size + 1) x10 - wordVal (Nat.log2_up size + 1) x8)
                       mod 2 ^ Z.of_nat (Nat.log2_up size + 1))%Z = Z.of_nat size) as P3.
            { rewrite <- e; simpl.
              unfold lgSize in *.
              rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zminus_mod_idemp_l, Z.add_simpl_l,
              <- Zpow_of_nat, Nat.pow_add_r, Nat.pow_1_r, pow2, <- mod_Zmod, Nat.mod_small; lia.
            }
            econstructor 1; auto; normalize_key_concl; simpl.
            repeat f_equal.
            unfold Spec.snocInBound, listInSpec.
            destruct Nat.ltb eqn:G; auto.
            exfalso.
            rewrite Nat.ltb_lt, firstn_length_le in G;
              [| unfold convertToList; rewrite rotateLength, <- list_arr_length; lia].
            unfold lgSize in *; lia.
      - hyp_consumer.
        + goal_consumer2.
        + goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer2.
        econstructor 1 with (enqVal := $ 0) (deqVal := $ 0); eauto.
        + simpl; rewrite Zmod_0_l; lia.
        + simpl; doUpdRegs_red; reflexivity.
        + simpl; doUpdRegs_red; unfold listInSpec.
          rewrite firstn_O; reflexivity.
        + rewrite doUpdRegs_preserves_keys; normalize_key_concl.
      - hyp_consumer.
        goal_consumer2; eauto.
    Qed.

  End SizeGT1.

End Proofs.
