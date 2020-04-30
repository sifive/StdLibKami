Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Spec.
Require Import StdLibKami.Fifo.CorrectDef.
Require Import StdLibKami.GenericFifo.ExtendedFifo.
Require Import StdLibKami.GenericFifo.Ifc.
Require Import StdLibKami.GenericFifo.Spec.
Require Import StdLibKami.GenericFifo.CorrectDef.

Section Proofs.
  Context {fifoIfcParams : Fifo.Ifc.Params}.
  Context {extendedFifoParams : @GenericFifo.ExtendedFifo.Params fifoIfcParams}.
  (*Context {genIfcParams : GenericFifo.Ifc.Params}.*)

  Local Notation genericFifoParams := (GenericFifo.Ifc.Build_Params
                                         (@Fifo.Ifc.name fifoIfcParams)
                                         (@Fifo.Ifc.k fifoIfcParams)
                                         (@Fifo.Ifc.size fifoIfcParams)).
  
  Local Definition fifoImpl := @GenericFifo.ExtendedFifo.Extension fifoIfcParams
                                                                   extendedFifoParams.
  Local Definition fifoSpec := @GenericFifo.Spec.spec genericFifoParams.
  Local Definition fifoSpecf := @Fifo.Spec.spec fifoIfcParams.
  
  Record myGenFifoR  (o_sf : RegsT) (nonDetEmpVal : bool)
         (specRegVals : list (type Fifo.Ifc.k))
         (lenVal : word (Fifo.Ifc.lgSize + 1))
         (fifoR : RegsT -> RegsT -> Prop)
         (fifoRegs: list (string * FullKind))
         (o_i o_s : RegsT) : Prop :=
    {
      HRegs : getKindAttr o_i = fifoRegs;
      Ho_sCorrect : o_s =
                    [((@Spec.nonDetEmptyName genericFifoParams), existT _ (SyntaxKind Bool) nonDetEmpVal);
                    ((@Spec.listName genericFifoParams), existT _ (@Spec.nlist genericFifoParams) specRegVals);
                    ((@Spec.nonDetLenName genericFifoParams), existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) lenVal)];
      Ho_sfCorrect : o_sf =
                     [((@Fifo.Spec.listName fifoIfcParams), existT _ (@Fifo.Spec.nlist fifoIfcParams) specRegVals)];
      Hlen : length specRegVals <= (@size genericFifoParams);
      HlenVal : lenVal = $(@size genericFifoParams);
      HnonDetEmpVal : nonDetEmpVal = false;
      HfifoR : fifoR o_i o_sf;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.
  Variable HCorrectFifo : FifoCorrect fifo fifoSpecf.

    Ltac Record_destruct :=
    match goal with
    | [H : exists _ _ _ _, myGenFifoR _ _ _ _ _ _ _ _ |- _] =>
      let o_sf := fresh "o_sf" in
      let nonDetEmpVal := fresh "nonDetEmpVal" in
      let specRegVals := fresh "specRegVals" in
      let lenVal := fresh "lenVal" in
      let H0 := fresh "H" in
      destruct H as [o_sf [nonDetEmpVal [specRegVals [lenVal H0]]]];
      destruct H0
    end.
    
    Goal GenericFifoCorrect fifoImpl fifoSpec.
      all : econstructor 1 with (fifoR := (fun o1 o2 =>
                                             (exists o_sf nonDetEmpVal specRegVals lenVals,
                                              myGenFifoR o_sf nonDetEmpVal specRegVals lenVals
                                                (Fifo.CorrectDef.fifoR HCorrectFifo)
                                                (Fifo.CorrectDef.fifoRegs HCorrectFifo)
                                                o1 o2)))
                                (fifoRegs := (Fifo.CorrectDef.fifoRegs HCorrectFifo)).
      all : red; unfold fifoImpl, fifoSpecf, fifo, fifoSpec, isEmpty, flush, enq, deq,
                 numFree, isFull, first, propagate, Extension, spec, ExtendedFifo.propagate,
                 ExtendedFifo.isEmpty, ExtendedFifo.flush, ExtendedFifo.enq, ExtendedFifo.deq,
                 ExtendedFifo.numFree, ExtendedFifo.isFull, ExtendedFifo.first, Spec.propagate,
                 Spec.isEmpty, Spec.flush, Spec.enq, Spec.deq, Spec.numFree, Spec.isFull,
                 Spec.first; intros; try Record_destruct; destruct HCorrectFifo; simpl in *;
        unfold Fifo.Spec.isEmpty, Fifo.Spec.flush, Fifo.Spec.enq, Fifo.Spec.deq,
        Fifo.Spec.numFree, Fifo.Spec.isFull, Fifo.Spec.first in *.
      - hyp_consumer.
        repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
        instantiate (1 := false).
        instantiate (1 := $size).
        do 3 doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver; simpl.
           econstructor 1; eauto; normalize_key_concl.
      - hyp_consumer.
        apply SubList_map_iff in H0; destruct H0 as [x [Heq1 Heq2]].
        goal_consumer2; eauto.
      - hyp_consumer.
        goal_consumer1; simpl; auto.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        goal_consumer1.
        simpl.
        destruct wltu eqn:G; [rewrite wltu_lt in G| rewrite wltu_ge in G].
        + exfalso.
          do 2 rewrite wordToNat_natToWord in G; try lia.
          * unfold lgSize, size.
            apply (Nat.le_lt_trans _ (Fifo.Ifc.size)); [lia|].
            apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
              [apply log2_up_pow2|].
            apply Nat.pow_lt_mono_r; lia.
          * unfold Fifo.Ifc.lgSize.
            apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                  [apply log2_up_pow2|].
            apply Nat.pow_lt_mono_r; lia.
          * unfold Fifo.Ifc.lgSize.
            apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                  [apply log2_up_pow2|].
            apply Nat.pow_lt_mono_r; lia.
        + destruct Nat.ltb eqn:G0; [rewrite Nat.ltb_lt in G0| rewrite Nat.ltb_ge in G0].
          * destruct weq; simpl; auto.
            exfalso.
            apply eq_word in e; simpl in *.
            unfold lgSize, size in e.
            rewrite Z.mod_0_l in e;
              [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P; lia].
            rewrite Z.mod_small in e; [lia|split; [lia|]].
            rewrite pow2_of_nat, <- Nat2Z.inj_lt.
            apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
            apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));[apply log2_up_pow2|].
            apply Nat.pow_lt_mono_r; lia.
          * destruct weq; simpl; auto.
            exfalso.
            apply neq_wordVal in n; simpl in *.
            unfold lgSize, size in n.
            rewrite Z.mod_0_l in n;
              [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P; lia].
            rewrite Z.mod_small in n; [lia|split; [lia|]].
            rewrite pow2_of_nat, <- Nat2Z.inj_lt.
            apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
            apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));[apply log2_up_pow2|].
            apply Nat.pow_lt_mono_r; lia.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        goal_consumer1.
        simpl.
        destruct wltu eqn:G; [rewrite wltu_lt in G| rewrite wltu_ge in G]; auto.
        exfalso.
        do 2 rewrite wordToNat_natToWord in G; try lia.
        * unfold lgSize, size.
          apply (Nat.le_lt_trans _ (Fifo.Ifc.size)); [lia|].
          apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
            [apply log2_up_pow2|].
          apply Nat.pow_lt_mono_r; lia.
        * unfold Fifo.Ifc.lgSize.
          apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
            [apply log2_up_pow2|].
          apply Nat.pow_lt_mono_r; lia.
        * unfold Fifo.Ifc.lgSize.
          apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
            [apply log2_up_pow2|].
          apply Nat.pow_lt_mono_r; lia.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        goal_consumer1.
        simpl.
        destruct (emptyb x) eqn:G ; simpl.
        + apply functional_extensionality_dep.
          intros; fin_dep_destruct x0; auto.
          fin_dep_destruct y; auto; simpl.
          destruct x; simpl in *; auto; try discriminate.
          inv y.
        + apply functional_extensionality_dep.
          intro; fin_dep_destruct x0; auto.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
        + simpl.
          destruct (emptyb x) eqn:G ; simpl.
          * apply functional_extensionality_dep.
            intros; fin_dep_destruct x0; auto.
            fin_dep_destruct y; auto; simpl.
            destruct x; simpl in *; auto; try discriminate.
            inv y.
          * apply functional_extensionality_dep.
            intro; fin_dep_destruct x0; auto.
        + instantiate (1 := false).
          do 3 doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver; simpl.
          econstructor 1; eauto; normalize_key_concl; repeat my_simplifier;
            repeat my_simpl_solver.
          * rewrite doUpdReg_preserves_getKindAttr; auto.
          * destruct x; simpl; [lia|simpl in *; lia].
          * destruct x; auto.
          * revert HdoUpdRegsR.
            repeat doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver; intro.
            simpl in HdoUpdRegsR; assumption.
      - hyp_consumer.
        goal_consumer2.
      - hyp_consumer.
        repeat (repeat goal_split; repeat goal_body; repeat normal_solver).
        + simpl.
          destruct wltu eqn:G; [rewrite wltu_lt in G| rewrite wltu_ge in G].
          * exfalso.
            do 2 rewrite wordToNat_natToWord in G; try lia.
            -- unfold lgSize, size.
               apply (Nat.le_lt_trans _ (Fifo.Ifc.size)); [lia|].
               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                 [apply log2_up_pow2|].
               apply Nat.pow_lt_mono_r; lia.
            -- unfold Fifo.Ifc.lgSize.
               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                 [apply log2_up_pow2|].
               apply Nat.pow_lt_mono_r; lia.
            -- unfold Fifo.Ifc.lgSize.
               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                 [apply log2_up_pow2|].
               apply Nat.pow_lt_mono_r; lia.
          * destruct Nat.ltb eqn:G0; [rewrite Nat.ltb_lt in G0| rewrite Nat.ltb_ge in G0].
            -- destruct weq; simpl; auto.
               exfalso.
               apply eq_word in e; simpl in *.
               unfold lgSize, size in e.
               rewrite Z.mod_0_l in e;
                 [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P; lia].
               rewrite Z.mod_small in e; [lia|split; [lia|]].
               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
               apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));[apply log2_up_pow2|].
               apply Nat.pow_lt_mono_r; lia.
            -- destruct weq; simpl; auto.
               exfalso.
               apply neq_wordVal in n; simpl in *.
               unfold lgSize, size in n.
               rewrite Z.mod_0_l in n;
                 [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P; lia].
               rewrite Z.mod_small in n; [lia|split; [lia|]].
               rewrite pow2_of_nat, <- Nat2Z.inj_lt.
               apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
               apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));[apply log2_up_pow2|].
               apply Nat.pow_lt_mono_r; lia.
        + instantiate (1 := $(@Fifo.Ifc.size fifoIfcParams)).
          revert HdoUpdRegsR.
          repeat doUpdRegs_simpl; doUpdRegs_red; normal_solver; intro.
          econstructor 1; eauto; normalize_key_concl; repeat my_simplifier;
            repeat my_simpl_solver.
          * rewrite doUpdReg_preserves_getKindAttr; auto.
          * simpl.
            destruct weq; simpl; auto.
            destruct wltu eqn:G; [rewrite wltu_lt in G|rewrite wltu_ge in G].
            -- exfalso.
               do 2 rewrite wordToNat_natToWord in G; try lia.
               ++ unfold lgSize, size.
                  apply (Nat.le_lt_trans _ (Fifo.Ifc.size)); [lia|].
                  apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                    [apply log2_up_pow2|].
                  apply Nat.pow_lt_mono_r; lia.
               ++ unfold Fifo.Ifc.lgSize.
                  apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                    [apply log2_up_pow2|].
                  apply Nat.pow_lt_mono_r; lia.
               ++ unfold Fifo.Ifc.lgSize.
                  apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                    [apply log2_up_pow2|].
                  apply Nat.pow_lt_mono_r; lia.
            -- apply neq_wordVal in n; simpl in n.
               unfold lgSize, size in n.
               rewrite Z.mod_0_l in n;
                 [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P; lia].
               rewrite Z.mod_small in n; [|split; [lia|]].
               ++ rewrite snoc_rapp, app_length; simpl; lia.
               ++ rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                  apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
                  apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                    [apply log2_up_pow2|].
                  apply Nat.pow_lt_mono_r; lia.
          * simpl; destruct weq; simpl; [|unfold size]; auto.
          * simpl in *.
            unfold Spec.snocInBound in HdoUpdRegsR.
            destruct weq; simpl.
            -- destruct wltu eqn:G; [rewrite wltu_lt in G|rewrite wltu_ge in G].
               ++ exfalso.
                  do 2 rewrite wordToNat_natToWord in G; try lia.
                  ** unfold lgSize, size.
                     apply (Nat.le_lt_trans _ (Fifo.Ifc.size)); [lia|].
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                       [apply log2_up_pow2|].
                     apply Nat.pow_lt_mono_r; lia.
                  ** unfold Fifo.Ifc.lgSize.
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                       [apply log2_up_pow2|].
                     apply Nat.pow_lt_mono_r; lia.
                  ** unfold Fifo.Ifc.lgSize.
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                       [apply log2_up_pow2|].
                     apply Nat.pow_lt_mono_r; lia.
               ++ destruct Nat.ltb eqn:G0; [rewrite Nat.ltb_lt in G0|rewrite Nat.ltb_ge in G0];
                    auto.
                  exfalso.
                  apply eq_word in e; simpl in e.
                  unfold lgSize, size in e.
                  rewrite Z.mod_0_l in e;
                    [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P
                      ; lia].
                  rewrite Z.mod_small in e; [lia|split; [lia|]].
                  rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                  apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
                  apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                    [apply log2_up_pow2|].
                  apply Nat.pow_lt_mono_r; lia.
            -- destruct wltu eqn:G; [rewrite wltu_lt in G|rewrite wltu_ge in G].
               ++ exfalso.
                  do 2 rewrite wordToNat_natToWord in G; try lia.
                  ** unfold lgSize, size.
                     apply (Nat.le_lt_trans _ (Fifo.Ifc.size)); [lia|].
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                       [apply log2_up_pow2|].
                     apply Nat.pow_lt_mono_r; lia.
                  ** unfold Fifo.Ifc.lgSize.
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                       [apply log2_up_pow2|].
                     apply Nat.pow_lt_mono_r; lia.
                  ** unfold Fifo.Ifc.lgSize.
                     apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                       [apply log2_up_pow2|].
                     apply Nat.pow_lt_mono_r; lia.
               ++ destruct Nat.ltb eqn:G0; [rewrite Nat.ltb_lt in G0|rewrite Nat.ltb_ge in G0];
                    auto.
                  exfalso.
                  apply neq_wordVal in n; simpl in n.
                  unfold lgSize, size in n.
                  rewrite Z.mod_0_l in n;
                    [|specialize (Z_of_nat_pow_2_gt_0 (Nat.log2_up Fifo.Ifc.size + 1)) as P
                      ; lia].
                  rewrite Z.mod_small in n; [lia|split; [lia|]].
                  rewrite pow2_of_nat, <- Nat2Z.inj_lt.
                  apply (Nat.le_lt_trans _ Fifo.Ifc.size); [lia|].
                  apply (Nat.le_lt_trans _ (2 ^ (Nat.log2_up Fifo.Ifc.size)));
                    [apply log2_up_pow2|].
                  apply Nat.pow_lt_mono_r; lia.
      - hyp_consumer; goal_consumer2.
      - hyp_consumer.
        repeat (repeat goal_split; repeat goal_body; repeat normal_solver); [simpl; auto|].
        instantiate (1 := $(@Fifo.Ifc.size fifoIfcParams)).
        instantiate (1 := false).
        revert HdoUpdRegsR.
        repeat (repeat doUpdRegs_simpl; doUpdRegs_red; repeat normal_solver); intro.
        econstructor 1; eauto; normalize_key_concl; repeat my_simplifier;
          repeat my_simpl_solver.
        + rewrite doUpdReg_preserves_getKindAttr; auto.
        + simpl; lia.
      - hyp_consumer; goal_consumer2.
    Qed.

End Proofs.
