Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.CorrectDef.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.GenericSpec.
Require Import StdLibKami.Fifo.DoubleFifo.
Require Import StdLibKami.Fifo.CorrectDef.
Require Import StdLibKami.Fifo.Proofs2.


Definition valsToSnd {k : Kind} (l : list (type k)) :=
  map (fun x => existT (fullType type) (SyntaxKind k)
                       (nth_default (evalConstT Default) l x)) (seq 0 (length l)).

Section Proofs.
  Context {ifcParams : Fifo.Ifc.Params}.
  Context {dblParams : Fifo.DoubleFifo.Params}.

  Local Definition fifoImpl := @Fifo.DoubleFifo.impl ifcParams dblParams.
  Local Definition fifoSpec := @Fifo.GenericSpec.spec ifcParams.
  Local Notation ifcParamsL := (Ifc.Build_Params (append (@name ifcParams) "L")
                                                 (@k ifcParams)
                                                 sizeL).
  Local Notation ifcParamsR := (Ifc.Build_Params (append (@name ifcParams) "R")
                                                 (@k ifcParams)
                                                 sizeR).
  Local Definition fifoSpecL := @Fifo.GenericSpec.spec ifcParamsL.
  Local Definition fifoSpecR := @Fifo.GenericSpec.spec ifcParamsR.
  
  Variable HCorrectL : FifoCorrect Lfifo fifoSpecL.
  Variable HCorrectR : FifoCorrect Rfifo fifoSpecR.
  
  Variable HsizePos : size <> 0.
  
  Record myGenFifoR  (fifoRR fifoLR : RegsT -> RegsT -> Prop)
         (fifoRegsL fifoRegsR : list (string * FullKind))
         (o_i o_s : RegsT) : Prop :=
    {
      o_i1 : RegsT;
      o_i2 : RegsT;
      o_s1 : RegsT;
      o_s2 : RegsT;
      implRegsL : RegsT;
      implRegsR : RegsT;
      implRegValL : list (type k);
      implRegValR : list (type k);
      specRegVals : list (type k);
      nonDetEmpVal : bool;
      nonDetEmpValL : bool;
      nonDetEmpValR : bool;
      lenVal : word (lgSize + 1);
      lenValL : word ((@lgSize ifcParamsL) + 1);
      lenValR : word ((@lgSize ifcParamsR) + 1);
      HlenL : length implRegValL <= sizeL;
      HlenR : length implRegValR <= sizeR;
      HlenVal : lenVal =
                if (wltu lenValL $(sizeL - (length implRegValL)))
                then $(wordToNat lenValL)
                else $(sizeL - (length implRegValL));
      HimplRegVal : specRegVals = implRegValR ++ implRegValL;
      HnonDetEmpVal : nonDetEmpVal = (nonDetEmpValR || emptyb implRegValR);
      Ho_sCorrect : o_s =
                    [(GenericSpec.nonDetEmptyName, existT _ (SyntaxKind Bool) nonDetEmpVal);
                    (GenericSpec.listName, existT _ GenericSpec.nlist specRegVals);
                    (GenericSpec.nonDetLenName, existT _ (SyntaxKind (Bit (lgSize + 1))) lenVal)];
      Ho_s1Correct : o_s1 =
                     [((@GenericSpec.nonDetEmptyName ifcParamsL),
                       existT _ (SyntaxKind Bool) nonDetEmpValL);
                     ((@GenericSpec.listName ifcParamsL),
                      existT _ GenericSpec.nlist implRegValL);
                     ((@GenericSpec.nonDetLenName ifcParamsL),
                      existT _ (SyntaxKind (Bit (lgSize + 1))) lenValL)];
      Ho_s2Correct : o_s2 =
                     [((@GenericSpec.nonDetEmptyName ifcParamsR),
                       existT _ (SyntaxKind Bool) nonDetEmpValR);
                     ((@GenericSpec.listName ifcParamsR),
                      existT _ GenericSpec.nlist implRegValR);
                     ((@GenericSpec.nonDetLenName ifcParamsR),
                      existT _ (SyntaxKind (Bit (lgSize + 1))) lenValR)];
      Ho_iApp : o_i = o_i2 ++ o_i1;
      HRegs1 : getKindAttr o_i1 = fifoRegsL;
      HRegs2 : getKindAttr o_i2 = fifoRegsR;
      HfifoR1 : fifoLR o_i1 o_s1;
      HfifoR2 : fifoRR o_i2 o_s2;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.
  

  Ltac Record_destruct :=
    match goal with
    | [H : myGenFifoR _ _ _ _ _ _ |- _] =>
      destruct H
    end.

  Goal FifoCorrect fifoImpl fifoSpec.
    (*destruct HCorrectL, HCorrectR.*)
    econstructor 1 with (fifoR := myGenFifoR (fifoR HCorrectR) (fifoR HCorrectL)
                                             (fifoRegs HCorrectL) (fifoRegs HCorrectR))
                        (fifoRegs := (fifoRegs HCorrectL) ++ (fifoRegs HCorrectR)).
    all : unfold EffectfulRelation, EffectlessRelation, ActionWb,
          fifoImpl, fifoSpec, impl, spec,
          isEmpty, isFull, numFree, first, deq, enq, flush,
          GenericSpec.isEmpty, GenericSpec.isFull, GenericSpec.numFree, GenericSpec.first,
          GenericSpec.deq, GenericSpec.enq, GenericSpec.flush,
          DoubleFifo.isEmpty, DoubleFifo.isFull, DoubleFifo.numFree, DoubleFifo.first,
          DoubleFifo.deq, DoubleFifo.enq, DoubleFifo.flush.
    all: intros; try Record_destruct; try destruct HCorrectL, HCorrectR;
      cbn [CorrectDef.fifoRegs CorrectDef.fifoR] in *;
      unfold fifoSpecR, fifoSpecL, spec,  GenericSpec.enq, GenericSpec.deq,
      GenericSpec.first, GenericSpec.isEmpty,
      GenericSpec.isFull, GenericSpec.flush, GenericSpec.numFree in *;
      cbn [isEmpty isFull flush enq deq first numFree] in *;
      unfold GenericSpec.nonDetEmptyName in *.
    - hyp_consumer.
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0); simpl.
      rewrite <- orb_assoc.
      f_equal.
      destruct implRegValR, implRegValL; simpl; auto.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0); simpl.
      rewrite sizeSum, app_length.
      destruct weq, wltu eqn:G; subst; simpl; auto.
      + rewrite wltu_ge in G.
        do 2 rewrite wordToNat_natToWord in G.
        * assert (sizeL - length implRegValL = 0) as P by lia; rewrite P; simpl; auto.
        * apply zero_lt_pow2.
        * unfold lgSize, size.
          apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));[|apply Nat.pow_lt_mono_r; lia].
          apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2].
        * unfold lgSize, size.
          apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));[|apply Nat.pow_lt_mono_r; lia].
          apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2].
     + rewrite wltu_lt in G.
       assert (Nat.eqb (length implRegValL) sizeL = false) as P.
       { rewrite Nat.eqb_neq; intro Q; rewrite Q, diag in *.
         rewrite wordToNat_natToWord in G; try lia.
         apply zero_lt_pow2.
       }
       rewrite P.
       destruct weq; simpl.
       * exfalso.
         rewrite <- neq0_wneq0 in n; apply n.
         assert (forall {sz} (w1 w2 : word sz),
                    w1 = w2 ->
                    wordToNat w1 = wordToNat w2) as P0.
         { clear; intros; f_equal; auto. }
         specialize (P0 _ _ _ e).
         do 2 rewrite wordToNat_natToWord in P0; [exact P0 |apply zero_lt_pow2 | | ].
         -- specialize (wordBound _ x) as P1; apply boundProofZ in P1.
            unfold lgSize in *.
            rewrite sizeSum at 1.
            unfold size in P1.
            unfold wordToNat in *; destruct x; simpl in *; dest.
            rewrite pow2_of_nat in H5.
            rewrite <- (Z2Nat.id wordVal), <- Nat2Z.inj_lt in H5; auto.
            apply (Nat.lt_le_trans _ (2 ^ (Nat.log2_up sizeL + 1))); auto.
            apply pow2_le, plus_le_compat_r, Nat.log2_up_le_mono; lia.
         -- specialize (wordBound _ x) as P1; apply boundProofZ in P1.
            unfold lgSize in *.
            rewrite sizeSum at 1.
            unfold size in P1.
            unfold wordToNat in *; destruct x; simpl in *; dest.
            rewrite pow2_of_nat in H5.
            rewrite <- (Z2Nat.id wordVal), <- Nat2Z.inj_lt in H5; auto.
            apply (Nat.lt_le_trans _ (2 ^ (Nat.log2_up sizeL + 1))); auto.
            apply pow2_le, plus_le_compat_r, Nat.log2_up_le_mono; lia.
       * symmetry; rewrite Nat.eqb_neq in *; intro; apply P; lia.
     + destruct Nat.eqb eqn:G0.
       * rewrite Nat.eqb_eq in G0; rewrite G0, diag; simpl; reflexivity.
       * rewrite Nat.eqb_neq in G0.
         destruct weq; simpl.
         -- exfalso.
            apply G0.
            arithmetizeWord.
            unfold wordToNat, lgSize in *; simpl in *.
            rewrite sizeSum in H5.
            rewrite Zmod_0_l, Z.mod_small in H5.
            ++ rewrite <- (Z2Nat.id 0%Z) in H5; [|lia].
               apply Nat2Z.inj in H5; simpl in H5; lia.
            ++ split; [lia|].
               rewrite <- Zpow_of_nat.
               apply inj_lt.
               apply (Nat.le_lt_trans _ (sizeL + sizeR));[lia|].
               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                 [apply log2_up_pow2|apply Nat.pow_lt_mono_r;lia].
         -- symmetry; rewrite Nat.eqb_neq; intro; apply G0; lia.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x1); simpl.
      destruct wltu eqn:G.
      + rewrite wltu_lt in G.
        destruct (wltu ($ (wordToNat x0)) _) eqn:G0.
        * unfold lgSize, ZeroExtendTruncLsb.
          destruct lt_dec.
          -- rewrite evalExpr_castBits, nat_cast_eq_rect.
             unfold size at 2 4.
             rewrite (f_equal_dep (fun n : nat => word n)
                                     (fun n =>
                                        (wconcat (wzero (Nat.log2_up size + 1
                                                    - (Nat.log2_up sizeL + 1))) x0))
                                     (ZeroExtendTruncLsb_subproof l)).
                arithmetizeWord.
                unfold wordToNat, lgSize, size; rewrite Z2Nat.id; auto.
                specialize (Word.wordBound _ x0) as P; apply boundProofZ in P; dest; auto.
          -- assert (Nat.log2_up size = Nat.log2_up sizeL) as P.
             { rewrite Nat.nlt_ge in n.
               destruct (le_lt_or_eq _ _ n); [|unfold size in *; lia].
               exfalso.
               rewrite sizeSum in H0.
               specialize (Nat.log2_up_le_mono sizeL (sizeL + sizeR) ltac:(lia)) as TMP.
               rewrite (Nat.add_le_mono_r _ _ 1) in TMP.
               unfold size in H0.
               lia.
             }
             simpl.
             rewrite evalExpr_castBits, nat_cast_eq_rect.
             specialize (f_equal_dep (fun n : nat => word n)
                                     (fun n => $(wordToNat x0))
                                     (ZeroExtendTruncLsb_subproof0 n)) as P0.
             simpl in *.
             rewrite natToWord_wordToNat in P0; rewrite P0.
             unfold truncLsb; rewrite P.
             rewrite diag, Nat.add_0_r.
             repeat rewrite natToWord_wordToNat.
             apply eq_wordVal; simpl; rewrite Z.mod_small; auto.
             specialize (wordBound _ x0) as P1; apply boundProofZ in P1; dest; auto.
        * exfalso.
          rewrite wltu_ge, sizeSum, app_length, <- Nat.nlt_ge in G0; apply G0.
          repeat rewrite wordToNat_natToWord.
          -- rewrite wordToNat_natToWord in G;[lia|].
             unfold lgSize, size.
             apply (Nat.le_lt_trans _ sizeL);[lia|].
             apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
             apply Nat.pow_lt_mono_r; lia.
          -- unfold lgSize; rewrite sizeSum.
             apply (Nat.le_lt_trans _ (sizeL + sizeR));[lia|].
             apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
               [apply log2_up_pow2|].
             apply Nat.pow_lt_mono_r; lia.
          -- apply (Nat.lt_le_trans _ (2 ^ ((Nat.log2_up sizeL) + 1))).
             ++ specialize (wordBound _ x0) as P; apply boundProofZ in P; dest.
                unfold lgSize, size in H5.
                unfold wordToNat in *; destruct x0; simpl in *; dest.
                rewrite pow2_of_nat in H5.
                rewrite <- (Z2Nat.id wordVal), <- Nat2Z.inj_lt in H5; auto.
             ++ unfold lgSize; rewrite sizeSum.
                apply pow2_le, Nat.add_le_mono_r, Nat.log2_up_le_mono; lia.
      + destruct (wltu _ ($ (size - length (implRegValR ++ implRegValL)))) eqn:G1.
        * unfold lgSize, ZeroExtendTruncLsb.
          destruct lt_dec.
          -- rewrite evalExpr_castBits, nat_cast_eq_rect; simpl.
             rewrite (f_equal_dep (fun n : nat => word n)
                                  (fun n =>
                                     (wconcat (wzero (Nat.log2_up size + 1
                                                             - (Nat.log2_up sizeL + 1)))
                                              $ (sizeL - Datatypes.length implRegValL)))
                                  (ZeroExtendTruncLsb_subproof l)).
             arithmetizeWord.
             rewrite (Z.mod_small _  (2 ^ Z.of_nat (Nat.log2_up sizeL + 1))); auto.
             split; [lia|].
             rewrite pow2_of_nat.
             apply inj_lt, (Nat.le_lt_trans _ sizeL); [lia|].
             apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL))); [apply log2_up_pow2|].
             apply Nat.pow_lt_mono_r; lia.
          -- assert (Nat.log2_up size = Nat.log2_up sizeL) as P.
             { rewrite Nat.nlt_ge in n.
               destruct (le_lt_or_eq _ _ n); [|unfold size in *; lia].
               exfalso.
               rewrite sizeSum in H0.
               specialize (Nat.log2_up_le_mono sizeL (sizeL + sizeR) ltac:(lia)) as TMP.
               rewrite (Nat.add_le_mono_r _ _ 1) in TMP.
               unfold size in H0.
               lia.
             }
             simpl.
             rewrite evalExpr_castBits, nat_cast_eq_rect; simpl.
             specialize (f_equal_dep (fun n : nat => word n)
                                     (fun n => $ (sizeL - Datatypes.length implRegValL))
                                     (ZeroExtendTruncLsb_subproof0 n)) as P0.
             simpl in *.
             rewrite P0.
             unfold truncLsb; rewrite P.
             rewrite diag, Nat.add_0_r.
             apply eq_wordVal; simpl; rewrite Z.mod_small; auto.
             apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
        * assert (size - length (implRegValR ++ implRegValL) = sizeL - length implRegValL)
                 as P.
          {
            assert (length implRegValR = sizeR) as P.
            { rewrite wltu_ge, sizeSum, app_length in G1.
              do 2 rewrite wordToNat_natToWord in G1;[ lia| | |];
                   unfold lgSize; rewrite sizeSum;
                     apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                       try apply log2_up_pow2;
                       apply Nat.pow_lt_mono_r; lia.
            }
            rewrite sizeSum, app_length, P; lia. }
          rewrite P.
          unfold lgSize, ZeroExtendTruncLsb.
          destruct lt_dec.
          -- rewrite evalExpr_castBits, nat_cast_eq_rect; simpl.
             rewrite (f_equal_dep (fun n : nat => word n)
                                  (fun n =>
                                     (wconcat (wzero (Nat.log2_up size + 1
                                      - (Nat.log2_up sizeL + 1)))
                                              $ (sizeL - Datatypes.length implRegValL)))
                                  (ZeroExtendTruncLsb_subproof l)).
             arithmetizeWord.
             rewrite (Z.mod_small _  (2 ^ Z.of_nat (Nat.log2_up sizeL + 1))); auto.
             split; [lia|].
             rewrite pow2_of_nat.
             apply inj_lt, (Nat.le_lt_trans _ sizeL); [lia|].
             apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL))); [apply log2_up_pow2|].
             apply Nat.pow_lt_mono_r; lia.
          -- assert (Nat.log2_up size = Nat.log2_up sizeL) as P0.
             { rewrite Nat.nlt_ge in n.
               destruct (le_lt_or_eq _ _ n); [|unfold size in *; lia].
               exfalso.
               rewrite sizeSum in H0.
               specialize (Nat.log2_up_le_mono sizeL (sizeL + sizeR) ltac:(lia)) as TMP.
               rewrite (Nat.add_le_mono_r _ _ 1) in TMP.
               unfold size in H0.
               lia.
             }
             simpl.
             rewrite evalExpr_castBits, nat_cast_eq_rect; simpl.
             specialize (f_equal_dep (fun n : nat => word n)
                                     (fun n => $ (sizeL - Datatypes.length implRegValL))
                                     (ZeroExtendTruncLsb_subproof0 n)) as P1.
             simpl in *.
             rewrite P1.
             unfold truncLsb; rewrite P0.
             rewrite diag, Nat.add_0_r.
             apply eq_wordVal; simpl; rewrite Z.mod_small; auto.
             apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + goal_consumer1.
        rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0).
        apply functional_extensionality_dep.
        intros; fin_dep_destruct x1.
        * simpl.
          destruct implRegValR, implRegValL, x; simpl; auto.
        * fin_dep_destruct y; auto; simpl.
          destruct implRegValR, implRegValL, x; simpl; auto.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      + rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0).
        apply functional_extensionality_dep.
        intros; fin_dep_destruct x1.
        * simpl.
          destruct implRegValR, implRegValL, x; simpl; auto.
        * fin_dep_destruct y; auto; simpl.
          destruct implRegValR, implRegValL, x; simpl; auto.
      + econstructor 1; normalize_key_concl; simpl;
            try intro; repeat rewrite doUpdRegs_preserves_keys; eauto.
        * rewrite doUpdRegs_DisjKey; try solve_keys; auto.
        * rewrite doUpdReg_preserves_getKindAttr; auto.
        * rewrite doUpdRegs_DisjKey; try solve_keys.
          exact HfifoR1.
        * repeat rewrite doUpdReg_nil in *; rewrite doUpdRegs_nil in *.
          exact HdoUpdRegsR.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0) in *.
      goal_consumer1; simpl.
      + destruct weq; subst; simpl.
        * destruct wltu eqn:G; auto.
          rewrite wltu_ge in G.
          destruct (le_lt_or_eq _ _ G).
          -- exfalso.
             setoid_rewrite (wordToNat_natToWord _ 0) in H0;[lia|].
             apply zero_lt_pow2.
          -- destruct weq; auto; simpl.
             exfalso.
             do 2 rewrite wordToNat_natToWord in H0;
                  [ rewrite H0 in *; apply n; auto| | |]; simpl in *;
                    try apply zero_lt_pow2;
                    unfold lgSize, size;
                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL))).
                ++ apply (Nat.le_trans _ sizeL); try lia; apply log2_up_pow2.
                ++ apply Nat.pow_lt_mono_r; lia.
                ++ apply (Nat.le_trans _ sizeL); try lia; apply log2_up_pow2.
                ++ apply Nat.pow_lt_mono_r; lia.
        * destruct weq; simpl.
          -- destruct wltu eqn:G.
             ++ exfalso.
                apply neq_wordVal in n; apply n; simpl.
                unfold wordToNat in e.
                destruct x; simpl in *.
                arithmetizeWord; simpl in H10.
                rewrite Zmod_0_l; auto.
                rewrite Zmod_0_l, pow2_of_nat, <- mod_Zmod in H10;
                  [|specialize (zero_lt_pow2 (lgSize + 1)) as TMP; lia].
                rewrite Nat.mod_small in H10;
                  [rewrite Z2Nat.id in H10|]; try lia.
                unfold lgSize; rewrite sizeSum.
                dest.
                unfold lgSize, size in H11, H13.
                rewrite pow2_of_nat in H11, H13.
                rewrite <- (Z2Nat.id wordVal) in H13; auto.
                rewrite <- (Z2Nat.id wordVal0) in H11; auto.
                rewrite <- Nat2Z.inj_lt in H11, H13.
                apply (Nat.lt_le_trans _ (2 ^ (Nat.log2_up sizeL + 1))),
                Nat.pow_le_mono_r, plus_le_compat_r, Nat.log2_up_le_mono; lia.
             ++ rewrite Nat.eqb_eq.
                arithmetizeWord; simpl in H6.
                rewrite Zmod_0_l, pow2_of_nat, <- mod_Zmod in H6;
                  [|specialize (zero_lt_pow2 (lgSize + 1)) as TMP; lia].
                rewrite Nat.mod_small in H6; try lia.
                unfold lgSize; rewrite sizeSum.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                  [apply log2_up_pow2| apply Nat.pow_lt_mono_r; lia].
          -- destruct Nat.eqb eqn:G.
             ++ exfalso.
                rewrite Nat.eqb_eq in G; rewrite G, diag in *.
                destruct wltu eqn:G0.
                ** rewrite wltu_lt in G0.
                   rewrite wordToNat_natToWord in G0; [lia|].
                   apply zero_lt_pow2.
                ** apply n0; reflexivity.
             ++ symmetry.
                rewrite app_length, sizeSum.
                rewrite Nat.eqb_neq in *; intro; apply G; lia.
      + econstructor 1; auto; normalize_key_concl; simpl;
          try intro; repeat rewrite doUpdRegs_preserves_keys; auto; simpl in *.
        6 : { revert HdoUpdRegsR.
              doUpdRegs_red; intro.
              destruct String.eqb eqn:G in HdoUpdRegsR.
              - unfold GenericSpec.listName in G.
                rewrite String.eqb_eq, append_remove_prefix in G.
                discriminate.
              - destruct String.eqb eqn:G0 in HdoUpdRegsR.
                + exfalso.
                  rewrite String.eqb_eq in G0;
                    unfold GenericSpec.nonDetLenName, GenericSpec.listName in *.
                  apply append_remove_prefix in G0; discriminate.
                + apply HdoUpdRegsR.
        }
        6 : { rewrite doUpdRegs_DisjKey; [|solve_keys].
              apply HfifoR2.
        }
        * unfold GenericSpec.snocInBound, size.
          (* instantiate (1 := (if negb *)
          (*                         (getBool (weq x $ (0)) *)
          (*                          || (Datatypes.length implRegValL =? sizeL)%nat) *)
          (*                     then *)
          (*                       if Datatypes.length implRegValL <? sizeL *)
          (*                       then snoc val implRegValL *)
          (*                       else implRegValL *)
          (*                     else implRegValL)). *)
          destruct weq; simpl; auto.
          destruct Nat.eqb eqn:G; simpl; auto.
          destruct Nat.ltb eqn:G0; auto.
          rewrite Nat.eqb_neq in G.
          rewrite snoc_rapp, app_length; simpl; lia.
        * (* instantiate (1 := implRegValR); *) auto.
        * (* instantiate (1 := x). *)
          (* instantiate (1 := nonDetEmpValR). *)
          repeat f_equal.
          -- repeat destruct weq; simpl; auto; subst.
             ++ destruct wltu eqn:G.
                ** exfalso.
                   apply n; rewrite wordToNat_natToWord; auto.
                   apply zero_lt_pow2.
                ** exfalso.
                   rewrite wltu_ge in G.
                   do 2 rewrite wordToNat_natToWord in G; try apply zero_lt_pow2.
                   --- destruct (le_lt_or_eq _ _ G); [lia|].
                       rewrite H0 in n; apply n; reflexivity.
                   --- unfold lgSize, size.
                       apply (Nat.le_lt_trans _ sizeL); [lia|].
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));
                         [apply log2_up_pow2|apply Nat.pow_lt_mono_r;lia].
                   --- unfold lgSize, size.
                       apply (Nat.le_lt_trans _ sizeL); [lia|].
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));
                         [apply log2_up_pow2|apply Nat.pow_lt_mono_r;lia].
             ++ destruct wltu eqn:G.
                ** exfalso.
                   clear HdoUpdRegsR.
                   apply neq_wordVal in n; apply n.
                   unfold wordToNat in e.
                   arithmetizeWord; simpl in *.
                   rewrite Zmod_0_l.
                   rewrite Zmod_0_l, pow2_of_nat, <- mod_Zmod in H10;
                     [|specialize (zero_lt_pow2 (lgSize + 1)) as TMP; lia].
                   rewrite Nat.mod_small in H10;
                     [rewrite Z2Nat.id in H10|]; try lia.
                   unfold lgSize; rewrite sizeSum.
                   dest.
                   unfold lgSize, size in H11, H13.
                   rewrite pow2_of_nat in H11, H13.
                   rewrite <- (Z2Nat.id wordVal) in H13; auto.
                   rewrite <- (Z2Nat.id wordVal0) in H11; auto.
                   rewrite <- Nat2Z.inj_lt in H11, H13.
                   apply (Nat.lt_le_trans _ (2 ^ (Nat.log2_up sizeL + 1))),
                   Nat.pow_le_mono_r, plus_le_compat_r, Nat.log2_up_le_mono; lia.
                ** destruct Nat.eqb eqn:G0; simpl; auto.
                   exfalso.
                   rewrite Nat.eqb_neq in G0; apply G0.
                   arithmetizeWord; simpl in H10.
                   rewrite Zmod_0_l, pow2_of_nat, <- mod_Zmod in H10;
                     [|specialize (zero_lt_pow2 (lgSize + 1)) as TMP; lia].
                   rewrite <- (Z2Nat.id 0) in H10; [|lia].
                   apply Nat2Z.inj in H10.
                   rewrite Nat.mod_small in H10; try lia.
                   unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ sizeL); [lia|].
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     [apply log2_up_pow2| apply Nat.pow_lt_mono_r; lia].
             ++ rewrite app_length, sizeSum.
                destruct Nat.eqb eqn:G; simpl.
                ** rewrite Nat.eqb_eq in G; rewrite G in *.
                   exfalso.
                   rewrite diag in *; simpl in *.
                   destruct wltu eqn:G0 in n0; [|apply n0; reflexivity].
                   rewrite wltu_lt, wordToNat_natToWord in G0; [lia |apply zero_lt_pow2].
                ** destruct (Nat.eqb (_ + _) _) eqn:G0; simpl.
                   --- exfalso.
                       rewrite Nat.eqb_eq in G0.
                       rewrite Nat.eqb_neq in G.
                       lia.
                   --- unfold GenericSpec.snocInBound; rewrite sizeSum, app_length.
                       destruct Nat.ltb eqn:G1.
                       +++ destruct (Nat.ltb (length implRegValL)) eqn:G2.
                           *** repeat rewrite snoc_rapp.
                               rewrite app_assoc; reflexivity.
                           *** exfalso.
                               unfold size in G2.
                               rewrite Nat.ltb_ge in G2.
                               rewrite Nat.eqb_neq in G.
                               lia.
                       +++ exfalso.
                           rewrite Nat.eqb_neq in G0.
                           rewrite Nat.ltb_ge in G1.
                           lia.
          -- destruct wltu eqn:G.
             ++ destruct (wltu _ ($ (_ - length (if (negb _) then _ else _)))) eqn:G0; auto.
                destruct weq in G0; simpl in *; [rewrite G0 in *; discriminate|].
                destruct Nat.eqb eqn:G1 in G0; simpl in *; [rewrite G0 in *; discriminate|].
                rewrite wltu_lt in G.
                rewrite wltu_ge in G0.
                unfold GenericSpec.snocInBound in G0.
                destruct Nat.ltb eqn:G2; [| lia].
                rewrite snoc_rapp, app_length in G0; simpl in *.
                destruct weq; simpl; [contradiction|].
                rewrite G1; simpl.
                unfold GenericSpec.snocInBound, size; setoid_rewrite G2.
                rewrite Nat.eqb_neq, Nat.ltb_lt in *.
                rewrite snoc_rapp, app_length; simpl.
                rewrite wordToNat_natToWord in G0, G.
                ** destruct (le_lt_or_eq _ _ G0); [|rewrite H0 in *; reflexivity].
                   exfalso.
                   apply lt_le_S in H0.
                   rewrite Nat.add_1_r, minus_Sn_m, Nat.sub_succ in H0; lia.
                ** unfold lgSize, size.
                   apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                     [|apply Nat.pow_lt_mono_r; lia].
                   apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2].
                ** unfold lgSize, size.
                   apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                     [|apply Nat.pow_lt_mono_r; lia].
                   apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2].
             ++ rewrite wltu_ge in G.
                destruct wltu eqn:G0; simpl.
                ** exfalso.
                   unfold GenericSpec.snocInBound, size in G0.
                   rewrite wltu_lt in G0.
                   destruct weq in G0; simpl in *; [lia|].
                   destruct Nat.eqb eqn:G1 in G0; simpl in *; [lia|].
                   destruct Nat.ltb eqn:G2 in G0; [|lia].
                   rewrite snoc_rapp, app_length in G0; simpl in *.
                   specialize (Nat.le_lt_trans _ _ _ G G0) as P.
                   do 2 rewrite wordToNat_natToWord in P; [lia| | | ];
                        unfold lgSize, size;
                        apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                        try (apply Nat.pow_lt_mono_r; lia);
                        apply (Nat.le_trans _ sizeL); try lia; apply log2_up_pow2.
                ** rewrite wltu_ge in G0.
                   destruct weq; simpl in *; auto.
                   destruct Nat.eqb eqn:G1; simpl in *; auto.
                   unfold GenericSpec.snocInBound.
                   destruct Nat.ltb eqn:G2; auto.
                   exfalso.
                   rewrite Nat.ltb_lt in G2.
                   admit.
        * rewrite doUpdReg_preserves_getKindAttr; auto.
        * rewrite doUpdRegs_DisjKey; try solve_keys; auto.
        (* * repeat rewrite doUpdReg_nil in *. *)
        (*   instantiate (1 := nonDetEmpValL). *)
        (*   unfold oneUpdReg in HdoUpdRegsR; simpl in *. *)
        (*   unfold GenericSpec.listName, GenericSpec.nonDetLenName, *)
        (*   GenericSpec.nonDetEmptyName in *. *)
        (*   rewrite String.eqb_refl in *. *)
        (*   repeat (destruct String.eqb eqn:G in HdoUpdRegsR; *)
        (*           [rewrite String.eqb_eq, append_remove_prefix in G; discriminate| clear G]). *)
        (*   simpl in *. *)
        (*   apply HdoUpdRegsR. *)
        (* * rewrite doUpdRegs_DisjKey; try solve_keys; auto. *)
        (*   exact HfifoR2. *)
    - hyp_consumer.
      goal_consumer2.
    - unfold GenericSpec.listName, GenericSpec.nonDetLenName in *.
      hyp_consumer.
      goal_consumer1; auto.
      + econstructor 1; normalize_key_concl;
          try intro; repeat rewrite doUpdRegs_preserves_keys; auto.
        * instantiate (1 := nil); simpl; lia.
        * instantiate (1 := nil); simpl; lia.
        * instantiate (1 := (if wltu lenValL $ (sizeL - Datatypes.length implRegValL)
                             then $ (wordToNat lenValL)
                             else $ (sizeL - Datatypes.length implRegValL))).
          rewrite orb_true_r.
          repeat f_equal; simpl.
          rewrite Nat.sub_0_r.
          destruct wltu eqn:G.
          -- rewrite wltu_lt in G.
             destruct wltu eqn:G0; repeat rewrite natToWord_wordToNat in *; auto.
             exfalso.
             rewrite wltu_ge in G0.
             specialize (Nat.le_lt_trans _ _ _ G0 G) as P.
             do 2 rewrite wordToNat_natToWord in P; try lia;
                  unfold lgSize, size;
                  apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                  try (apply Nat.pow_lt_mono_r; lia);
                  try (apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2]).
          -- clear G; destruct wltu eqn:G;
              [rewrite wordToNat_natToWord; auto;
               unfold lgSize, size;
                 apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                 try (apply Nat.pow_lt_mono_r; lia);
                 try (apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2])|].
            rewrite wltu_ge in G.
            destruct (le_lt_or_eq _ _ G).
            ++ exfalso.
               do 2 rewrite wordToNat_natToWord in H13; try lia;
                    unfold lgSize, size;
                    apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                    try (apply Nat.pow_lt_mono_r; lia);
                    try (apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2]).
            ++  do 2 rewrite wordToNat_natToWord in H13; try rewrite H13 at 2; try lia; auto;
                     unfold lgSize, size;
                     apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeL)));
                     try (apply Nat.pow_lt_mono_r; lia);
                     try (apply (Nat.le_trans _ sizeL); [lia |apply log2_up_pow2]).
        * rewrite doUpdRegs_DisjKey.
          -- rewrite doUpdReg_preserves_getKindAttr; auto.
          -- intro; rewrite doUpdRegs_preserves_keys; revert k; fold (DisjKey x0 o_i1).
             solve_keys.
        * rewrite doUpdReg_preserves_getKindAttr; auto.
          -- rewrite doUpdRegs_DisjKey; auto.
             solve_keys.
          -- rewrite doUpdRegs_preserves_keys; auto.
          -- rewrite doUpdRegs_DisjKey; auto.
             solve_keys.
        * rewrite doUpdRegs_DisjKey;
            [|intro; rewrite doUpdRegs_preserves_keys; revert k; fold (DisjKey x0 o_i1);
              solve_keys].
          revert HdoUpdRegsR0.
          doUpdRegs_red; intro.
          destruct String.eqb eqn:G in HdoUpdRegsR0.
          -- rewrite String.eqb_eq in G.
             destruct String.eqb eqn:G0 in G;
               [rewrite String.eqb_eq, append_remove_prefix in G0; discriminate
               |rewrite append_remove_prefix in G; discriminate].
          -- clear G.
             destruct String.eqb eqn:G in HdoUpdRegsR0;
               [rewrite String.eqb_eq, append_remove_prefix in G; discriminate|].
          admit.
        * rewrite (@doUpdRegs_DisjKey o_i2 x7); [|solve_keys].
          revert HdoUpdRegsR; doUpdRegs_red; intro.
          destruct String.eqb eqn:G.
          -- rewrite String.eqb_eq in G.
             destruct String.eqb eqn:G0 in G;
               [rewrite String.eqb_eq, append_remove_prefix in G0; discriminate
               |rewrite append_remove_prefix in G; discriminate].
          -- clear G.
             destruct String.eqb eqn:G in HdoUpdRegsR;
               [rewrite String.eqb_eq, append_remove_prefix in G; discriminate|].
             apply HdoUpdRegsR.
    - hyp_consumer.
      goal_consumer2.
      Unshelve.
      all : (exact false||exact $0).
  Admitted.
End Proofs.
