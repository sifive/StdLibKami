Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.GenericFifo.Ifc.
Require Import StdLibKami.GenericFifo.Spec.
Require Import StdLibKami.GenericFifo.DoubleFifo.
Require Import StdLibKami.GenericFifo.CorrectDef.


Definition valsToSnd {k : Kind} (l : list (type k)) :=
  map (fun x => existT (fullType type) (SyntaxKind k)
                       (nth_default (evalConstT Default) l x)) (seq 0 (length l)).

Section Proofs.
  Context {ifcParams : GenericFifo.Ifc.Params}.
  Context {dblParams : GenericFifo.DoubleFifo.Params}.

  Local Definition fifoImpl := @GenericFifo.DoubleFifo.impl ifcParams dblParams.
  Local Definition fifoSpec := @GenericFifo.Spec.spec ifcParams.
  Local Notation ifcParamsL := (GenericFifo.Ifc.Build_Params (append (@name ifcParams) "L")
                                                             (@k ifcParams)
                                                             sizeL).
  Local Notation ifcParamsR := (GenericFifo.Ifc.Build_Params (append (@name ifcParams) "R")
                                                             (@k ifcParams)
                                                             sizeR).
  Local Definition fifoSpecL := @GenericFifo.Spec.spec ifcParamsL.
  Local Definition fifoSpecR := @GenericFifo.Spec.spec ifcParamsR.
  
  
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
      HlenVal : lenVal = if (wltu lenValL $(sizeL - (length implRegValL)))
                         then $(wordToNat lenValL)
                         else $(sizeL - (length implRegValL));
      HimplRegVal : specRegVals = implRegValR ++ implRegValL;
      HnonDetEmpVal : nonDetEmpVal = (nonDetEmpValR || emptyb implRegValR);
      Ho_sCorrect : o_s =
                    [(Spec.nonDetEmptyName, existT _ (SyntaxKind Bool) nonDetEmpVal);
                    (Spec.listName, existT _ Spec.nlist specRegVals);
                    (Spec.nonDetLenName, existT _ (SyntaxKind (Bit (lgSize + 1))) lenVal)];
      Ho_s1Correct : o_s1 =
                     [((@Spec.nonDetEmptyName ifcParamsL),
                       existT _ (SyntaxKind Bool) nonDetEmpValL);
                     ((@Spec.listName ifcParamsL),
                      existT _ Spec.nlist implRegValL);
                     ((@Spec.nonDetLenName ifcParamsL),
                      existT _ (SyntaxKind (Bit (lgSize + 1))) lenValL)];
      Ho_s2Correct : o_s2 =
                     [((@Spec.nonDetEmptyName ifcParamsR),
                       existT _ (SyntaxKind Bool) nonDetEmpValR);
                     ((@Spec.listName ifcParamsR),
                      existT _ Spec.nlist implRegValR);
                     ((@Spec.nonDetLenName ifcParamsR),
                      existT _ (SyntaxKind (Bit (lgSize + 1))) lenValR)];
      Ho_iApp : o_i = o_i2 ++ o_i1;
      HRegs1 : getKindAttr o_i1 = fifoRegsL;
      HRegs2 : getKindAttr o_i2 = fifoRegsR;
      HfifoR1 : fifoLR o_i1 o_s1;
      HfifoR2 : fifoRR o_i2 o_s2;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.
  
  Variable HCorrectL : GenericFifoCorrect Lfifo fifoSpecL.
  Variable HCorrectR : GenericFifoCorrect Rfifo fifoSpecR.

  Ltac Record_destruct :=
    match goal with
    | [H : myGenFifoR _ _ _ _ _ _ |- _] =>
      destruct H
    end.
  
 Goal GenericFifoCorrect fifoImpl fifoSpec.
    econstructor 1 with (fifoR := myGenFifoR (fifoR HCorrectR) (fifoR HCorrectL)
                                             (fifoRegs HCorrectL) (fifoRegs HCorrectR))
                        (fifoRegs := (fifoRegs HCorrectL) ++ (fifoRegs HCorrectR)).
    all : unfold EffectfulRelation, EffectlessRelation, ActionWb,
          fifoImpl, fifoSpec, impl, spec,
          isEmpty, isFull, numFree, first, deq, enq, flush,
          Spec.propagate, Spec.isEmpty, Spec.isFull, Spec.numFree, Spec.first,
          Spec.deq, Spec.enq, Spec.flush, DoubleFifo.propagate,
          DoubleFifo.isEmpty, DoubleFifo.isFull, DoubleFifo.numFree, DoubleFifo.first,
          DoubleFifo.deq, DoubleFifo.enq, DoubleFifo.flush.
    all: intros; try Record_destruct; try destruct HCorrectL, HCorrectR;
      cbn [CorrectDef.fifoRegs CorrectDef.fifoR] in *;
      unfold fifoSpecR, fifoSpecL, spec,  Spec.enq, Spec.deq,
      Spec.first, Spec.isEmpty,
      Spec.isFull, Spec.flush, Spec.numFree, Spec.propagate in *;
      cbn [propagate isEmpty isFull flush enq deq first numFree] in *;
      unfold Spec.nonDetEmptyName in *.
    - hyp_consumer;
        try rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x3),
        (Eqdep.EqdepTheory.UIP_refl _ _ x1) in *.
      unfold Spec.nonDetLenName, Spec.listName in *.
      + repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
        instantiate (1 := (nonDetEmpValR
                           || emptyb
                                (if evalUniBool Neg (getBool (isEq (Bit (lgSize + 1))
                                                                   x0 (evalConstT $ (0))))
                                 then
                                   snoc
                                     ((if
                                          evalUniBool Neg
                                          (evalKorOp Bool
                                                     [evalExpr (Var type _  x4);
                                                      evalExpr (Const _ (emptyb implRegValL))]
                                                     (evalConstT Default))
                                        then
                                          evalExpr
                                            STRUCT {"valid" ::= Const type true;
                                                    "data" ::= Spec.getHead type
                                                    implRegValL}%kami_expr
                                        else evalConstT Default) (FS F1)) implRegValR
                                 else implRegValR))).
        instantiate (1 := (if wltu lenValL
                    $ (sizeL - length
                                 (if
                                     negb
                                       (evalKorOp Bool
                                                  [evalExpr (Var type (SyntaxKind Bool) x4);
                                                   evalExpr (Const type (emptyb implRegValL))]
                                                  (evalConstT Default))
                                   then tl implRegValL
                                   else implRegValL))
                           then $ (wordToNat lenValL)
                           else
                             $ (sizeL - length
                                          (if
                                              negb
                                                (evalKorOp Bool
                                                           [evalExpr
                                                              (Var type (SyntaxKind Bool) x4);
                                                            evalExpr
                                                              (Const type (emptyb implRegValL))]
                                                           (evalConstT Default))
                                            then tl implRegValL
                                            else implRegValL)))).
        revert HdoUpdRegsR0.
        repeat (repeat doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver).
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
           rewrite append_remove_prefix in G; discriminate
          | clear G].
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq, append_remove_prefix in G; discriminate| clear G].
        intros.
        cbn [evalExpr evalUniBool evalConstT evalKorOp evalBinBit evalBinBitBool] in *.
        revert HdoUpdRegsR.
        repeat (repeat doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver).
        destruct String.eqb eqn:G;
        [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
         rewrite append_remove_prefix in G; discriminate
         | clear G].
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq, append_remove_prefix in G; discriminate| clear G].
        intros.
        econstructor 1; normalize_key_concl;
          try intro; repeat rewrite doUpdRegs_preserves_keys.
        4 : { reflexivity. }
        6 : { rewrite (@doUpdRegs_DisjKey _ x29); [|solve_keys].
              apply HdoUpdRegsR. }
        6 : { rewrite (@doUpdRegs_DisjKey _ x22).
              - apply HdoUpdRegsR0.
              - intro.
                rewrite doUpdRegs_preserves_keys.
                revert k; fold (DisjKey x22 o_i2).
                solve_keys. }
        -- destruct x4, implRegValL; simpl in *; auto; lia.
        -- destruct isEq; simpl in *; auto.
           destruct (x4 || emptyb implRegValL) eqn:G; simpl; try discriminate.
           rewrite snoc_rapp, app_length; simpl.
           destruct wltu eqn:G0 in n.
           ++ rewrite wltu_lt, wordToNat_natToWord in G0; try lia.
              unfold lgSize, size.
                apply (Nat.le_lt_trans _ sizeR); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeR)));
                  [apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
           ++ rewrite wltu_ge, wordToNat_natToWord in G0.
              ** unfold lgSize, size in n.
                 apply neq_wordVal in n.
                 simpl in n.
                 rewrite Z.mod_0_l, Z.mod_small in n;
                   [ | split
                     | specialize (Z_of_nat_pow_2_gt_0 ((Nat.log2_up sizeR + 1))) as TMP];
                   try lia.
                 rewrite <- Zpow_of_nat.
                 apply inj_lt.
                 apply (Nat.le_lt_trans _ sizeR); [lia|].
                 apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeR)));
                   [apply log2_up_pow2|].
                 apply Nat.pow_lt_mono_r; lia.
              ** unfold lgSize, size.
                 apply (Nat.le_lt_trans _ sizeR); [lia|].
                 apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeR)));
                   [apply log2_up_pow2|].
                 apply Nat.pow_lt_mono_r; lia.
        -- do 4 f_equal.
           simpl in H16.
           destruct isEq; simpl in *; auto.
           ** clear HdoUpdRegsR0.
              destruct (x4 || emptyb implRegValL) eqn:G; simpl;
                [rewrite orb_true_r in H16; simpl in H16; discriminate|].
              destruct weq in H16; simpl in H16; try discriminate.
              rewrite e in n; contradiction.
           ** destruct (x4 || emptyb implRegValL) eqn:G3; simpl.
              --- rewrite negb_true_iff, orb_true_r in H16; discriminate.
              --- rewrite orb_false_iff in G3; dest.
                  destruct implRegValL; simpl in *; try discriminate.
                  clear H16.
                  destruct weq; simpl; auto.
                  exfalso.
                  rewrite e in n.
                  destruct wltu eqn:G in n; [contradiction|].
                  rewrite wltu_ge, wordToNat_natToWord, wordToNat_natToWord in G;
                    [destruct (le_lt_or_eq _ _ G); try lia; rewrite H10 in *; contradiction
                    |apply zero_lt_pow2 | ].
                  unfold lgSize, size.
                  apply (Nat.le_lt_trans _ (2^ (Nat.log2_up sizeR)));
                    [|apply Nat.pow_lt_mono_r; lia].
                  apply (Nat.le_trans _ sizeR); [lia |apply log2_up_pow2].
           ** destruct isEq; simpl in *; try discriminate.
              clear HdoUpdRegsR0.
              destruct (x4 || emptyb implRegValL) eqn:G; simpl; try discriminate.
              destruct implRegValL; [rewrite orb_true_r in G; discriminate|].
              rewrite snoc_rapp, app_cons, app_assoc; reflexivity.
          -- rewrite doUpdReg_preserves_getKindAttr, doUpdRegs_DisjKey; auto;
               [ |rewrite doUpdRegs_preserves_keys
                 |rewrite doUpdRegs_DisjKey ]; try solve_keys; auto.
          -- rewrite doUpdRegs_DisjKey, doUpdReg_preserves_getKindAttr; auto.
             intro; rewrite doUpdRegs_preserves_keys; revert k; fold (DisjKey x22 o_i2);
               solve_keys.
          -- auto.
          -- auto.
          -- auto.
          -- simpl in H6; repeat rewrite append_remove_prefix in H6.
             destruct H6 as [? | [? |? ] ]; try discriminate; contradiction.
     + repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
        instantiate (1 := (nonDetEmpValR || emptyb implRegValR)).
        instantiate (1 := (if wltu lenValL $ (sizeL - Datatypes.length implRegValL)
                           then $ (wordToNat lenValL)
                           else $ (sizeL - Datatypes.length implRegValL))).
       goal_consumer1.
        econstructor 1; normalize_key_concl; auto;
          try intro; repeat rewrite doUpdRegs_preserves_keys; eauto.
        reflexivity.
    - hyp_consumer.
      + goal_consumer2.
      + goal_consumer2.
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
      destruct weq; subst; simpl; auto.
      + destruct weq; simpl; auto.
        exfalso.
        destruct wltu eqn:G in e; subst; simpl in *.
        * rewrite wltu_lt in G.
          destruct wltu eqn:G0 in n.
          -- rewrite wltu_lt in G0.
             destruct wltu eqn:G1.
             ++ rewrite wordToNat_natToWord in n; [contradiction|apply zero_lt_pow2].
             ++ rewrite wltu_ge in G1; lia.
          -- rewrite wltu_ge in G0; destruct wltu eqn:G1 in G0.
             ++ exfalso.
                do 3 rewrite wordToNat_natToWord in G0.
                ** destruct (le_lt_or_eq _ _ G0); try lia.
                   rewrite H0 in n; contradiction.
                ** apply zero_lt_pow2.
                ** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                ** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                ** unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR));[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     [apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
                ** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                ** unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR));[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     [apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR));[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     [apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
             ++ rewrite wltu_ge in G1; lia.
        * rewrite wltu_ge in G.
          destruct wltu eqn:G0 in n.
          -- rewrite wltu_lt in G0.
             destruct wltu eqn:G1;
               [rewrite wltu_lt in G1; lia|rewrite wltu_ge in G1].
             apply neq_wordVal in n.
             apply eq_word in e; simpl in *.
             rewrite Zmod_0_l in *; rewrite Z.mod_small in *
             ; [|split |split]; try lia; unfold lgSize.
             ++ unfold size.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ rewrite sizeSum.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
          -- rewrite wltu_ge in G0.
             destruct wltu eqn:G1;
               [rewrite wltu_lt in G1; lia|rewrite wltu_ge in G1].
             apply eq_word in e; simpl in *.
             rewrite Zmod_0_l in *; rewrite Z.mod_small in *
             ; [|split]; try lia; unfold lgSize, size.
             ++ unfold wordToNat in G0; simpl in G0.
                rewrite e, Zmod_0_l, Z.mod_small in G0;
                  [|split; try lia].
                ** rewrite Nat2Z.id in G0.
                   destruct (le_lt_or_eq _ _ G0); [lia|].
                   rewrite H0 in n; simpl in n; contradiction.
                ** unfold lgSize; rewrite sizeSum.
                   rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                   ;[apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
             ++ unfold size.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
      + destruct weq; auto.
        exfalso.
        destruct wltu eqn:G; [rewrite wltu_lt in G| rewrite wltu_ge in G].
        * destruct wltu eqn:G0; [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
          -- apply neq_wordVal in n.
             unfold wordToNat in *.
             specialize (wordBound _ x) as P.
             rewrite boundProofZIff in P.
             arithmetizeWord; destruct x; simpl in *; dest.
             rewrite Z.mod_0_l in H5; rewrite Z.mod_small in n, H5
             ;[rewrite Z2Nat.id in H5; rewrite H5 in *; auto| |
               |specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P; lia| | ]
             ; try (split; lia).
             ++ rewrite Z2Nat.id; [split|]; auto.
                unfold lgSize; rewrite sizeSum.
                apply (Z.lt_le_trans _ (2 ^ Z.of_nat (Nat.log2_up (sizeL) + 1))); auto.
                apply Z.pow_le_mono_r, inj_le, plus_le_compat_r; [lia|].
                apply Nat.log2_up_le_mono; lia.
             ++ rewrite Z2Nat.id; [split|]; auto.
                unfold lgSize; rewrite sizeSum.
                apply (Z.lt_le_trans _ (2 ^ Z.of_nat (Nat.log2_up (sizeL) + 1))); auto.
                apply Z.pow_le_mono_r, inj_le, plus_le_compat_r; [lia|].
                apply Nat.log2_up_le_mono; lia.
          -- rewrite sizeSum, app_length in e.
             arithmetizeWord; simpl in H5.
             rewrite wordToNat_natToWord in G;
               [rewrite Z.mod_0_l, Z.mod_small in H5; try lia|].
             ++ split; [lia|].
                unfold lgSize; rewrite sizeSum.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P; lia.
             ++ unfold lgSize, size.
                apply (Nat.le_lt_trans _ sizeL);[lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
        * destruct wltu eqn:G0; [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
          -- apply neq_wordVal in n.
             unfold wordToNat in *.
             specialize (wordBound _ x) as P.
             rewrite boundProofZIff in P.
             arithmetizeWord; destruct x; simpl in *; dest.
             rewrite Z.mod_0_l in H5; rewrite Z.mod_small in n, H5
             ;[rewrite H5 in *; auto| |
               |specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P; lia| | ]
             ; try split; try lia.
             ++ unfold lgSize; rewrite sizeSum.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ unfold lgSize, size.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ unfold lgSize; rewrite sizeSum.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ unfold lgSize, size.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
          -- rewrite sizeSum, app_length in e.
             arithmetizeWord; simpl in H5.
             rewrite Z.mod_0_l in *;
               [ | unfold lgSize, size;
                   specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P
                 | specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P]; try lia.
             rewrite Z.mod_small in H5, n; [|split|split]; try lia.
             ++ unfold lgSize, size.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ unfold lgSize; rewrite sizeSum.
                rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
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
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0).
      simpl.
      destruct (x || emptyb implRegValR) eqn:G; simpl; auto.
      rewrite app_emptyb.
      apply orb_false_elim in G; dest; rewrite H5 in *.
      simpl.
      apply functional_extensionality_dep.
      intros; fin_dep_destruct x1; auto.
      fin_dep_destruct y; auto; simpl.
      destruct implRegValR, implRegValL, x; simpl; auto; discriminate.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0) in *.
      repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
      + simpl.
        destruct (x || emptyb implRegValR) eqn:G; simpl; auto.
        rewrite app_emptyb.
        apply orb_false_elim in G; dest; rewrite H10 in *.
        simpl.
        apply functional_extensionality_dep.
        intros; fin_dep_destruct x1; auto.
        fin_dep_destruct y; auto; simpl.
        destruct implRegValR, implRegValL; simpl; auto; discriminate.
      + instantiate (1 := (x3 || emptyb (tl implRegValR))).
        revert HdoUpdRegsR.
        unfold Spec.listName, Spec.nonDetLenName.
        repeat (repeat doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver).
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq, append_remove_prefix in G; discriminate| clear G].
        destruct String.eqb eqn:G;
        [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
         rewrite append_remove_prefix in G; try discriminate
        |rewrite String.eqb_neq in G; destruct String.eqb eqn:G0;
         [rewrite String.eqb_eq, append_remove_prefix in G0; try discriminate| contradiction] ].
        clear G0 G.
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
           rewrite append_remove_prefix in G; try discriminate
          |rewrite String.eqb_neq in G; destruct String.eqb eqn:G0;
           [rewrite String.eqb_eq, append_remove_prefix in G0; try discriminate| clear G G0]].
        intro.
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq, append_remove_prefix in G; discriminate| clear G].
        destruct String.eqb eqn:G;
        [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
         rewrite append_remove_prefix in G; try discriminate
        |rewrite String.eqb_neq in G; destruct String.eqb eqn:G0;
         [rewrite String.eqb_eq, append_remove_prefix in G0; try discriminate| contradiction] ].
        clear G0 G.
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
           rewrite append_remove_prefix in G; try discriminate
          |rewrite String.eqb_neq in G; destruct String.eqb eqn:G0;
           [rewrite String.eqb_eq, append_remove_prefix in G0; try discriminate| clear G G0]].
        econstructor 1; normalize_key_concl; simpl; auto;
          try intro; repeat rewrite doUpdRegs_preserves_keys; auto.
        6 : { rewrite doUpdRegs_DisjKey; try solve_keys; auto.
              apply HfifoR1. }
        6 : apply HdoUpdRegsR.
        all : auto.
        * simpl.
          destruct (x || emptyb implRegValR) eqn:G; simpl; auto.
          destruct implRegValR; simpl in *; auto.
          lia.
        * do 4 f_equal; simpl.
          -- destruct (x || emptyb implRegValR) eqn:G; simpl; auto.
             rewrite orb_false_iff in G; dest.
             rewrite app_emptyb, H10; reflexivity.
          -- destruct (x || emptyb implRegValR) eqn:G; simpl; auto.
             rewrite orb_false_iff in G; dest.
             rewrite app_emptyb; rewrite H10; simpl.
             destruct implRegValR; simpl in *; try discriminate; auto.
        * rewrite doUpdRegs_DisjKey; try solve_keys; auto.
        * rewrite doUpdReg_preserves_getKindAttr; auto.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0) in *.
      repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
      + simpl; destruct weq; subst; simpl.
        * destruct wltu eqn:G; [rewrite wltu_lt in G|rewrite wltu_ge in G]; subst.
          -- clear HdoUpdRegsR.
             destruct weq; simpl in *; auto.
             exfalso.
             destruct wltu eqn:G0 in n.
             ++ rewrite wordToNat_natToWord in n; [contradiction|].
                apply zero_lt_pow2.
             ++ rewrite wltu_ge in G0.
                do 3 rewrite wordToNat_natToWord in G0.
                ** destruct (le_lt_or_eq _ _ G0); try lia.
                   rewrite H6 in n; contradiction.
                ** apply zero_lt_pow2.
                ** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                ** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                ** unfold lgSize; rewrite sizeSum;
                     apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                       try apply log2_up_pow2;
                       apply Nat.pow_lt_mono_r; lia.
                ** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                ** unfold lgSize; rewrite sizeSum;
                     apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                       try apply log2_up_pow2;
                       apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize; rewrite sizeSum;
                     apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                       try apply log2_up_pow2;
                       apply Nat.pow_lt_mono_r; lia.
          -- destruct weq; auto; simpl.
             exfalso.
             destruct wltu eqn:G0; [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
             ++ apply neq_wordVal in n.
                apply eq_word in e; simpl in *.
                rewrite Z.mod_0_l in *.
                rewrite Z.mod_small in n;
                  [rewrite Z.mod_small in e; [contradiction|]|]; try split; try lia.
                ** unfold lgSize, size.
                   rewrite <- Zpow_of_nat.
                   apply inj_lt.
                   apply (Nat.le_lt_trans _ sizeL);[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
                ** rewrite <- Zpow_of_nat.
                   apply inj_lt.
                   unfold lgSize; rewrite sizeSum;
                     apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                       try apply log2_up_pow2;
                       apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize, size.
                   specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P; lia.
                ** unfold lgSize; rewrite sizeSum.
                   specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1)) as P; lia.
             ++ do 2 rewrite wordToNat_natToWord in G0.
                ** apply neq_wordVal in n.
                   apply eq_word in e; simpl in *.
                   unfold lgSize in *.
                   rewrite sizeSum in n, G0.
                   unfold size in e.
                   rewrite Z.mod_0_l in *;
                     [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P; lia
                      |specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1)) as P;
                       lia].
                   rewrite Z.mod_small in n, e; try split; try lia.
                   --- rewrite <- Zpow_of_nat.
                       apply inj_lt.
                       apply (Nat.le_lt_trans _ sizeL);[lia|].
                       apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                       apply Nat.pow_lt_mono_r; lia.
                   --- rewrite <- Zpow_of_nat.
                       apply inj_lt.
                       apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                           try apply log2_up_pow2;
                           apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     try apply log2_up_pow2;
                     apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     try apply log2_up_pow2;
                     apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize; rewrite sizeSum.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia;
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     try apply log2_up_pow2;
                     apply Nat.pow_lt_mono_r; lia.
        * destruct weq; simpl; auto.
          exfalso.
          destruct wltu eqn:G in e; [rewrite wltu_lt in G| rewrite wltu_ge in G].
          -- destruct wltu eqn:G0.
             ++ apply neq_wordVal in n.
                apply eq_word in e; simpl in *.
                rewrite Z.mod_0_l in n, e; unfold lgSize;
                  [| rewrite sizeSum;
                     specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1)) as P;
                     lia
                   | unfold size;
                     specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P; lia].
                specialize (wordBound _ x) as P; rewrite boundProofZIff in P; dest.
                unfold wordToNat in e.
                rewrite Z2Nat.id in e; auto.
                rewrite Z.mod_small in e; [rewrite e in n; contradiction|].
                split; auto.
                unfold lgSize in *.
                setoid_rewrite sizeSum.
                unfold size in H6.
                apply (Z.lt_le_trans _ (2 ^ Z.of_nat (Nat.log2_up sizeL + 1))); auto.
                apply Z.pow_le_mono_r, inj_le, plus_le_compat_r, Nat.log2_up_le_mono; lia.
             ++ apply neq_wordVal in n.
                apply eq_word in e; simpl in *.
                rewrite Z.mod_0_l in n, e; unfold lgSize;
                  [| rewrite sizeSum;
                     specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1)) as P;
                     lia
                   | unfold size;
                     specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P; lia].
                rewrite Z.mod_small in e; [rewrite e in n; contradiction|].
                split; [lia|].
                unfold lgSize; rewrite sizeSum.
                rewrite <- Zpow_of_nat.
                apply inj_lt.
                apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                  [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
          -- destruct wltu eqn:G0.
             ++ rewrite wltu_lt in G0.
                rewrite sizeSum, app_length in e.
                apply eq_word in e; simpl in e.
                rewrite Z.mod_0_l, Z.mod_small in e;
                  rewrite wordToNat_natToWord in G0; try lia.
                ** unfold lgSize, size.
                   apply (Nat.le_lt_trans _ sizeL);[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
                ** split; try lia.
                   unfold lgSize; rewrite sizeSum.
                   rewrite <- Zpow_of_nat.
                   apply inj_lt.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
                ** unfold lgSize, size.
                   apply (Nat.le_lt_trans _ sizeL);[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
                ** unfold lgSize; rewrite sizeSum.
                   specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1)) as P;
                     lia.
                ** unfold lgSize, size.
                   apply (Nat.le_lt_trans _ sizeL);[lia|].
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
                   apply Nat.pow_lt_mono_r; lia.
             ++ apply neq_wordVal in n.
                apply eq_word in e; simpl in *.
                unfold lgSize, size in n.
                unfold lgSize in e; rewrite sizeSum, app_length in e.
                rewrite Z.mod_0_l in n, e;
                  [| specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1)) as P;
                     lia
                   | specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P;
                     lia].
                rewrite Z.mod_small in n, e; try lia; split; try lia.
                ** rewrite <- Zpow_of_nat.
                   apply inj_lt.
                   apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                     [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
                ** rewrite <- Zpow_of_nat.
                   apply inj_lt.
                   apply (Nat.le_lt_trans _ sizeL); try lia.
                   apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));
                     [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
      + revert HdoUpdRegsR.
        instantiate (1 := if (wltu x3 $(sizeL - S (length implRegValL)))
                          then $(wordToNat x3)
                          else $(sizeL - S(length implRegValL))).
        unfold Spec.nonDetLenName, Spec.listName in *.
        repeat (repeat doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver).
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq in G; destruct String.eqb eqn:G0;
           rewrite append_remove_prefix in G; try discriminate| clear G].
        destruct String.eqb eqn:G;
          [rewrite String.eqb_eq, append_remove_prefix in G; discriminate| clear G].
        intro.
        econstructor 1; auto; normalize_key_concl; simpl;
          try intro; repeat rewrite doUpdRegs_preserves_keys; auto; simpl in *.
        6 : { apply HdoUpdRegsR. }
        6 : { rewrite doUpdRegs_DisjKey; [|solve_keys].
              apply HfifoR2. }
        all : auto.
        * destruct weq; simpl; auto.
          rewrite snoc_rapp, app_length; simpl.
          destruct wltu eqn:G;
            [rewrite wltu_lt in G| rewrite wltu_ge in G].
          -- clear HdoUpdRegsR.
             apply neq_wordVal in n.
             unfold wordToNat in G.
             simpl in *.
             unfold lgSize, size in n.
             rewrite Z.mod_0_l in n;
               [|specialize (Z_of_nat_pow_2_gt_0 ((Nat.log2_up sizeL) + 1)) as P; lia].
             rewrite Z.mod_small in G; try lia.
             split; try lia.
             unfold lgSize, size.
             rewrite <- Zpow_of_nat.
             apply inj_lt.
             apply (Nat.le_lt_trans _ sizeL);[lia|].
             apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
             apply Nat.pow_lt_mono_r; lia.
          -- clear HdoUpdRegsR.
             apply neq_wordVal in n.
             simpl in *.
             unfold lgSize, size in n.
             rewrite Z.mod_0_l in n;
               [|specialize (Z_of_nat_pow_2_gt_0 ((Nat.log2_up sizeL) + 1)) as P; lia].
             rewrite Z.mod_small in n; try lia.
             split; try lia.
             unfold lgSize, size.
             rewrite <- Zpow_of_nat.
             apply inj_lt.
             apply (Nat.le_lt_trans _ sizeL);[lia|].
             apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));[apply log2_up_pow2|].
             apply Nat.pow_lt_mono_r; lia.
        * repeat f_equal.
          -- destruct weq.
             ++ destruct weq; simpl; auto.
                exfalso.
                destruct wltu eqn:G; [rewrite wltu_lt in G|rewrite wltu_ge in G].
                ** rewrite e in *; simpl in *.
                   destruct wltu eqn:G0; [rewrite wltu_lt in G0|rewrite wltu_ge in G0].
                   --- rewrite wordToNat_natToWord in n; [contradiction|apply zero_lt_pow2].
                   --- apply neq_wordVal in n; simpl in n.
                       unfold lgSize in n; rewrite sizeSum, app_length in n.
                       rewrite Z.mod_0_l in n;
                         [|specialize (Z_of_nat_pow_2_gt_0 ((Nat.log2_up (sizeL + sizeR) + 1)))
                            as P; lia].
                       rewrite Z.mod_small in n.
                       +++ rewrite sizeSum, app_length in G0.
                           do 3 rewrite wordToNat_natToWord in G0; try lia.
                           *** apply zero_lt_pow2.
                           *** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                           *** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                           *** unfold lgSize; rewrite sizeSum.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                                 [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
                           *** rewrite wordToNat_natToWord; apply zero_lt_pow2.
                           *** unfold lgSize; rewrite sizeSum.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                                 [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
                           *** unfold lgSize; rewrite sizeSum.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                                 [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
                       +++ split; try lia.
                           rewrite <- Zpow_of_nat.
                           apply inj_lt.
                           apply (Nat.le_lt_trans _ (sizeL + sizeR)); try lia.
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                             [apply log2_up_pow2| apply Nat.pow_lt_mono_r]; lia.
                ** destruct wltu eqn:G0; [rewrite wltu_lt in G0|rewrite wltu_ge in G0].
                   --- 
                     clear HdoUpdRegsR.
                     apply neq_wordVal in n.
                     apply eq_word in e; simpl in *.
                     rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                     ; [|split |split]; try lia; unfold lgSize.
                     +++ unfold size.
                         rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                         apply (Nat.le_lt_trans _ sizeL); [lia|].
                         apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));
                           [apply log2_up_pow2|].
                         apply Nat.pow_lt_mono_r; lia.
                     +++ rewrite sizeSum.
                         rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                         apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                         apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                         ;[apply log2_up_pow2|].
                         apply Nat.pow_lt_mono_r; lia.
                   --- clear HdoUpdRegsR.
                     apply eq_word in e; simpl in *.
                     rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                     ; [|split]; try lia; unfold lgSize, size.
                       +++ unfold wordToNat in G0; simpl in G0.
                           rewrite e, Zmod_0_l, Z.mod_small in G0;
                             [|split; try lia].
                           *** rewrite Nat2Z.id in G0.
                               destruct (le_lt_or_eq _ _ G0); [lia|].
                               rewrite H6 in n; simpl in n; contradiction.
                           *** unfold lgSize; rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                       +++ unfold size.
                           rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                           apply (Nat.le_lt_trans _ sizeL); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));
                             [apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
             ++ simpl.
                destruct weq; auto; simpl.
                ** exfalso.
                   destruct wltu eqn:G; [rewrite wltu_lt in G| rewrite wltu_ge in G].
                   --- destruct wltu eqn:G0; [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
                       +++ clear HdoUpdRegsR.
                           apply neq_wordVal in n.
                           unfold wordToNat in *.
                           specialize (wordBound _ x) as P.
                           rewrite boundProofZIff in P.
                           arithmetizeWord; simpl in *; dest.
                           rewrite Z.mod_0_l in H11; rewrite Z.mod_small in n, H11
                           ;[rewrite Z2Nat.id in H11; rewrite H11 in *; auto| |
                             |specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P; lia| | ]
                           ; try (split; lia).
                           *** rewrite Z2Nat.id; [split|]; auto.
                               unfold lgSize; rewrite sizeSum.
                               apply (Z.lt_le_trans _ (2 ^ Z.of_nat (Nat.log2_up (sizeL) + 1)));
                                 auto.
                               apply Z.pow_le_mono_r, inj_le, plus_le_compat_r; [lia|].
                               apply Nat.log2_up_le_mono; lia.
                           *** rewrite Z2Nat.id; [split|]; auto.
                               unfold lgSize; rewrite sizeSum.
                               apply (Z.lt_le_trans _ (2 ^ Z.of_nat (Nat.log2_up (sizeL) + 1)));
                                 auto.
                               apply Z.pow_le_mono_r, inj_le, plus_le_compat_r; [lia|].
                               apply Nat.log2_up_le_mono; lia.
                       +++ rewrite sizeSum, app_length in e.
                           arithmetizeWord; simpl in H13.
                           rewrite wordToNat_natToWord in G;
                             [rewrite Z.mod_0_l, Z.mod_small in H13; try lia|].
                           *** split; [lia|].
                               unfold lgSize; rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P; lia.
                           *** unfold lgSize, size.
                               apply (Nat.le_lt_trans _ sizeL);[lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)));
                                 [apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                   --- destruct wltu eqn:G0; [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
                       +++ clear HdoUpdRegsR.
                           apply neq_wordVal in n.
                           unfold wordToNat in *.
                           specialize (wordBound _ x) as P.
                           rewrite boundProofZIff in P.
                           arithmetizeWord; simpl in *; dest.
                           rewrite Z.mod_0_l in H11; rewrite Z.mod_small in n, H11
                           ;[rewrite H11 in *; auto| |
                             |specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P; lia| | ]
                           ; try split; try lia.
                           *** unfold lgSize; rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** unfold lgSize, size.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ sizeL); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** unfold lgSize; rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** unfold lgSize, size.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ sizeL); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                       +++ clear HdoUpdRegsR.
                           rewrite sizeSum, app_length in e.
                           apply neq_wordVal in n; simpl in n.
                           arithmetizeWord; simpl in H13.
                           rewrite Z.mod_0_l in *;
                             [ | unfold lgSize, size;
                                 specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P
                               | specialize (Z_of_nat_pow_2_gt_0 (lgSize + 1)) as P]; try lia.
                           rewrite Z.mod_small in H13, n; [|split|split]; try lia.
                           *** unfold lgSize; rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                ** repeat rewrite snoc_rapp.
                   rewrite app_assoc; reflexivity.
          -- clear HdoUpdRegsR.
             destruct weq; simpl.
             ++ destruct wltu eqn:G;
                  [rewrite wltu_lt in G| rewrite wltu_ge in G].
                ** destruct wltu eqn:G0;
                     [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
                   --- destruct weq; simpl.
                       +++ rewrite e0 in *.
                           destruct wltu eqn:G1; auto.
                           exfalso.
                           rewrite wltu_ge in G1; try lia.
                       +++ exfalso.
                           unfold wordToNat in *.
                           arithmetizeWord; simpl in *.
                           unfold lgSize in *; rewrite sizeSum in H13; unfold size in n.
                           rewrite Z.mod_0_l in *;
                             [
                             |specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up sizeL + 1)) as P; lia
                             |specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up (sizeL + sizeR) + 1))
                               as P; lia ].
                           rewrite Z.mod_small in H13; [lia|].
                           split; [lia|].
                           unfold size in H10.
                           dest.
                           rewrite Z2Nat.id; auto.
                           apply (Z.lt_le_trans _ (2 ^ Z.of_nat (Nat.log2_up sizeL + 1))); auto.
                           apply Z.pow_le_mono_r, inj_le, plus_le_compat_r, Nat.log2_up_le_mono;
                             lia.
                   --- destruct wltu eqn:G1;
                         [rewrite wltu_lt in G1| rewrite wltu_ge in G1].
                       +++ exfalso.
                           destruct weq; simpl in *; try lia.
                           apply neq_wordVal in n.
                           apply eq_word in e; simpl in *.
                           rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                           ; [|split |split]; try lia; unfold lgSize.
                           *** rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                                 [apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** unfold size.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ sizeL); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                       +++ destruct weq; simpl in *; auto.
                           exfalso.
                           apply neq_wordVal in n.
                           apply eq_word in e; simpl in *.
                           rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                           ; [|split |split]; try lia; unfold lgSize.
                           *** rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                                 [apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** unfold size.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ sizeL); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                ** destruct wltu eqn:G0;
                     [rewrite wltu_lt in G0| rewrite wltu_ge in G0].
                   --- exfalso.
                       specialize (wordBound _ x) as P; rewrite boundProofZIff in P.
                       rewrite sizeSum, app_length in G.
                       do 2 rewrite wordToNat_natToWord in G;
                            [rewrite wordToNat_natToWord in G0; try lia | | | ].
                       +++ unfold lgSize, size.
                           apply (Nat.le_lt_trans _ sizeL); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                           ;[apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
                       +++ dest; unfold wordToNat.
                           rewrite <- Zpow_of_nat in H10.
                           rewrite <- (Z2Nat.id ((wordVal (lgSize + 1) x))), <- Nat2Z.inj_lt
                             in H10; auto.
                           unfold lgSize, size in H10.
                           unfold lgSize; setoid_rewrite sizeSum.
                           unfold size.
                           apply (Nat.lt_le_trans _ (2 ^ (Nat.log2_up sizeL + 1))); auto.
                           apply Nat.pow_le_mono_r, plus_le_compat_r, Nat.log2_up_le_mono
                           ; lia.
                       +++ unfold lgSize; rewrite sizeSum.
                           apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                             [apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
                       +++ unfold lgSize; rewrite sizeSum.
                           apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                             [apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
                   --- destruct wltu eqn:G1;
                         [rewrite wltu_lt in G1|rewrite wltu_ge in G1].
                       +++ destruct weq; simpl in *; exfalso.
                           *** rewrite e0 in G1.
                               rewrite wordToNat_natToWord in G1; try lia.
                               apply zero_lt_pow2.
                           *** rewrite sizeSum, app_length in e.
                               apply neq_wordVal in n.
                               apply eq_word in e; simpl in *.
                               rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                               ; [|split |split]; try lia; unfold lgSize.
                               ---- rewrite sizeSum.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold size.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ sizeL); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                       +++ destruct weq; simpl in *; auto.
                           rewrite sizeSum, app_length in e.
                           apply neq_wordVal in n.
                           apply eq_word in e; simpl in *.
                           rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                           ; [|split |split]; try lia; unfold lgSize.
                           *** rewrite sizeSum.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
                           *** unfold size.
                               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                               apply (Nat.le_lt_trans _ sizeL); [lia|].
                               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                               ;[apply log2_up_pow2|].
                               apply Nat.pow_lt_mono_r; lia.
             ++ destruct wltu eqn:G;
                  [rewrite wltu_lt in G|rewrite wltu_ge in G].
                ** destruct wltu eqn:G0;
                     [rewrite wltu_lt in G0|rewrite wltu_ge in G0].
                   --- destruct wltu eqn:G1;
                         [rewrite wltu_lt in G1|rewrite wltu_ge in G1].
                       +++ destruct weq; simpl in *.
                           *** exfalso.
                               rewrite e in n.
                               rewrite wordToNat_natToWord in n; [contradiction|].
                               apply zero_lt_pow2.
                           *** destruct wltu eqn:G2;
                                 [rewrite wltu_lt in G2|rewrite wltu_ge in G2]; auto.
                               rewrite snoc_rapp, app_length in G2; simpl in G2.
                               rewrite (Nat.add_1_r (length implRegValL))in G2.
                               lia.
                       +++ destruct weq; simpl in *.
                           *** exfalso.
                               rewrite e in n.
                               rewrite wordToNat_natToWord in n; [contradiction|].
                               apply zero_lt_pow2.
                           *** destruct wltu eqn:G2;
                                 [rewrite wltu_lt in G2
                                 |rewrite wltu_ge in G2; rewrite snoc_rapp, app_length;
                                  simpl; rewrite (Nat.add_1_r (length implRegValL));
                                  reflexivity].
                               exfalso.
                               rewrite snoc_rapp, app_length in G2; simpl in G2.
                               rewrite (Nat.add_1_r (length implRegValL))in G2.
                               lia.
                   --- destruct wltu eqn:G1;
                         [rewrite wltu_lt in G1|rewrite wltu_ge in G1].
                       +++ destruct weq; simpl in *.
                           *** exfalso.
                               apply neq_wordVal in n.
                               apply eq_word in e; simpl in *.
                               rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                               ; [|split |split]; try lia; unfold lgSize.
                               ---- rewrite sizeSum.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _
                                                           (2 ^ (Nat.log2_up (sizeL + sizeR))));
                                      [apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold size.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ sizeL); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                           *** destruct wltu eqn:G2;
                                 [rewrite wltu_lt in G2|rewrite wltu_ge in G2]; auto.
                               exfalso.
                               rewrite snoc_rapp, app_length in G2; simpl in G2.
                               rewrite (Nat.add_1_r (length implRegValL))in G2.
                               lia.
                       +++ destruct weq; simpl in *.
                           *** exfalso.
                               apply neq_wordVal in n.
                               apply eq_word in e; simpl in *.
                               rewrite Zmod_0_l in *; rewrite Z.mod_small in *
                               ; [|split |split]; try lia; unfold lgSize.
                               ---- rewrite sizeSum.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold size.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ sizeL); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                           *** destruct wltu eqn:G2;
                                 [rewrite wltu_lt in G2
                                 |rewrite wltu_ge in G2; rewrite snoc_rapp, app_length;
                                  simpl; rewrite (Nat.add_1_r (length implRegValL));
                                  reflexivity].
                               exfalso.
                               rewrite snoc_rapp, app_length in G2; simpl in G2.
                               rewrite (Nat.add_1_r (length implRegValL))in G2.
                               lia.
                ** destruct wltu eqn:G0;
                     [rewrite wltu_lt in G0|rewrite wltu_ge in G0].
                   --- exfalso.
                       specialize (wordBound _ x) as P; rewrite boundProofZIff in P.
                       rewrite sizeSum, app_length in G.
                       do 2 rewrite wordToNat_natToWord in G;
                            [rewrite wordToNat_natToWord in G0; try lia | | | ].
                       +++ unfold lgSize, size.
                           apply (Nat.le_lt_trans _ sizeL); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                           ;[apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
                       +++ dest; unfold wordToNat.
                           rewrite <- Zpow_of_nat in H10.
                           rewrite <- (Z2Nat.id ((wordVal (lgSize + 1) x))), <- Nat2Z.inj_lt
                             in H10; auto.
                           unfold lgSize, size in H10.
                           unfold lgSize; setoid_rewrite sizeSum.
                           unfold size.
                           apply (Nat.lt_le_trans _ (2 ^ (Nat.log2_up sizeL + 1))); auto.
                           apply Nat.pow_le_mono_r, plus_le_compat_r, Nat.log2_up_le_mono
                           ; lia.
                       +++ unfold lgSize; rewrite sizeSum.
                           apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                             [apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
                       +++ unfold lgSize; rewrite sizeSum.
                           apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                           apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))));
                             [apply log2_up_pow2|].
                           apply Nat.pow_lt_mono_r; lia.
                   --- destruct wltu eqn:G1;
                         [rewrite wltu_lt in G1|rewrite wltu_ge in G1].
                       +++ destruct weq; simpl in *.
                           *** exfalso.
                               rewrite sizeSum, app_length in G, n.
                               do 2 rewrite wordToNat_natToWord in G;
                                    [apply neq_wordVal in n; apply eq_word in e; simpl in *;
                                     rewrite Z.mod_0_l, Z.mod_small in n, e | | |]; try lia.
                               ---- split; [lia|].
                                    unfold lgSize, size.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ sizeL); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- split; [lia|].
                                    unfold lgSize; rewrite sizeSum.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold lgSize, size.
                                    specialize (Z_of_nat_pow_2_gt_0 ((Nat.log2_up sizeL + 1)))
                                      as P; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    specialize (Z_of_nat_pow_2_gt_0
                                                  ((Nat.log2_up (sizeL + sizeR) + 1))) as P; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                           *** destruct wltu eqn:G2;
                                 [rewrite wltu_lt in G2|rewrite wltu_ge in G2]; auto.
                               exfalso.
                               rewrite snoc_rapp, app_length in G2; simpl in G2.
                               rewrite (Nat.add_1_r (length implRegValL))in G2.
                               lia.
                       +++ destruct weq; simpl in *.
                           *** exfalso.
                               rewrite sizeSum, app_length in G, n.
                               do 2 rewrite wordToNat_natToWord in G;
                                    [apply neq_wordVal in n; apply eq_word in e; simpl in *;
                                     rewrite Z.mod_0_l, Z.mod_small in n, e | | |]; try lia.
                               ---- split; [lia|].
                                    unfold lgSize, size.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ sizeL); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- split; [lia|].
                                    unfold lgSize; rewrite sizeSum.
                                    rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold lgSize, size.
                                    specialize (Z_of_nat_pow_2_gt_0 ((Nat.log2_up sizeL + 1)))
                                      as P; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    specialize (Z_of_nat_pow_2_gt_0
                                                  ((Nat.log2_up (sizeL + sizeR) + 1))) as P; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                               ---- unfold lgSize; rewrite sizeSum.
                                    apply (Nat.le_lt_trans _ (sizeL + sizeR)); [lia|].
                                    apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up (sizeL + sizeR))))
                                    ;[apply log2_up_pow2|].
                                    apply Nat.pow_lt_mono_r; lia.
                           *** destruct wltu eqn:G2;
                                 [rewrite wltu_lt in G2|rewrite wltu_ge in G2].
                               ---- exfalso.
                                    rewrite snoc_rapp, app_length in G2; simpl in G2.
                                    rewrite (Nat.add_1_r (length implRegValL))in G2.
                                    lia.
                               ---- rewrite snoc_rapp, app_length; simpl.
                                    rewrite (Nat.add_1_r (length implRegValL)); reflexivity.
        * rewrite doUpdReg_preserves_getKindAttr; auto.
        * rewrite doUpdRegs_DisjKey; try solve_keys; auto.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      econstructor 1; auto; normalize_key_concl; simpl;
        try intro; repeat rewrite doUpdRegs_preserves_keys; auto; simpl in *.
      + instantiate (1 := nil); simpl; lia.
      + instantiate (1 := nil); simpl; lia.
      + instantiate (1 := $0).
        rewrite orb_true_r.
        repeat f_equal; simpl.
        * destruct wltu eqn:G;
            [rewrite wltu_lt in G|rewrite wltu_ge in G].
          -- rewrite wordToNat_natToWord; auto.
             apply zero_lt_pow2.
          -- do 2 rewrite wordToNat_natToWord in G.
             ++ destruct (le_lt_or_eq _ _ G); [lia|].
                rewrite H15; reflexivity.
             ++ apply zero_lt_pow2.
             ++ unfold lgSize, size.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
             ++ unfold lgSize, size.
                apply (Nat.le_lt_trans _ sizeL); [lia|].
                apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up sizeL)))
                ;[apply log2_up_pow2|].
                apply Nat.pow_lt_mono_r; lia.
      + rewrite doUpdRegs_DisjKey.
        * rewrite doUpdReg_preserves_getKindAttr; auto.
        * intro; rewrite doUpdRegs_preserves_keys; revert k; fold (DisjKey x0 o_i1).
          clear - H2 H14.
          solve_keys.
      + rewrite doUpdReg_preserves_getKindAttr; auto.
        * rewrite doUpdRegs_DisjKey; auto.
          clear - H2 H17.
          solve_keys.
        * rewrite doUpdRegs_preserves_keys; auto.
        * rewrite doUpdRegs_DisjKey; auto.
          clear - H2 H17.
          solve_keys.
      + rewrite doUpdRegs_DisjKey;
          [|intro; rewrite doUpdRegs_preserves_keys; revert k; fold (DisjKey x0 o_i1);
          clear - H2 H14; solve_keys].
        revert HdoUpdRegsR0.
        doUpdRegs_red; intro.
        apply HdoUpdRegsR0.
      + rewrite (@doUpdRegs_DisjKey o_i2 x7); [|clear - H2 H17; solve_keys].
        revert HdoUpdRegsR; doUpdRegs_red; intro.
        apply HdoUpdRegsR.
    - hyp_consumer.
      goal_consumer2.
      Unshelve.
      all : eauto; (exact false||exact $0).
 Qed.
End Proofs.
