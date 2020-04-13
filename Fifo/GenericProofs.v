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
  
  Record myGenFifoR  (o_i o_s : RegsT) : Prop :=
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
      HlenVal : lenVal = if (wltu lenValL $(sizeL - (length implRegValL)))
                         then $(wordToNat lenValL)
                         else (if (Nat.eqb (length implRegValL) sizeL)
                               then $(sizeL + (if (wltu lenValR $(sizeR - (length implRegValR)))
                                               then (wordToNat lenValR)
                                               else (sizeR - (length implRegValR))))
                               else $(sizeL - (length implRegValL)));
      HimplRegVal : specRegVals = implRegValL ++ implRegValR;
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
      Ho_iApp : o_i = o_i1 ++ o_i2;
      HRegs1 : getKindAttr o_i1 = (fifoRegs HCorrectL);
      HRegs2 : getKindAttr o_i2 = (fifoRegs HCorrectR);
      HfifoR1 : (fifoR HCorrectL) o_i1 o_s1;
      HfifoR2 : (fifoR HCorrectR) o_i2 o_s2;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.
  

  Ltac Record_destruct :=
    match goal with
    | [H : myGenFifoR _ _ |- _] =>
      destruct H
    end.

  Goal FifoCorrect fifoImpl fifoSpec.
    destruct HCorrectL, HCorrectR.
    econstructor 1 with (fifoR := myGenFifoR)
                        (fifoRegs := fifoRegs ++ fifoRegs0).
    all : unfold EffectfulRelation, EffectlessRelation, ActionWb,
          fifoImpl, fifoSpec, impl, spec,
          isEmpty, isFull, numFree, first, deq, enq, flush,
          GenericSpec.isEmpty, GenericSpec.isFull, GenericSpec.numFree, GenericSpec.first,
          GenericSpec.deq, GenericSpec.enq, GenericSpec.flush,
          DoubleFifo.isEmpty, DoubleFifo.isFull, DoubleFifo.numFree, DoubleFifo.first,
          DoubleFifo.deq, DoubleFifo.enq, DoubleFifo.flush.
    all: intros; try Record_destruct; destruct HCorrectL, HCorrectR;
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
      destruct weq, wltu eqn:G; simpl.
      + subst; simpl; reflexivity.
      + subst.
        admit.
        (* subst; destruct weq; auto. *)
        (* destruct (wltu ($ (wordToNat $ (0))) _ ) eqn:G0. *)
        (* * exfalso; apply n. *)
        (*   rewrite wordToNat_natToWord; auto. *)
        (*   unfold lgSize, size. *)
        (*   apply zero_lt_pow2. *)
        (* * exfalso. *)
        (*   apply n. *)
        (*   rewrite wltu_ge in G0. *)
        (*   rewrite wordToNat_natToWord in G0. *)
        (*   -- admit. *)
        (*   -- unfold lgSize. *)
        (*      rewrite Nat.pow_add_r, sizeSum. *)
        (*      apply (Nat.le_lt_trans _ _ _ (Nat.le_sub_l (sizeL + sizeR) _)). *)
        (*      apply (Nat.lt_le_trans _ ((sizeL + sizeR) * 2) _). *)
        (*      ++ rewrite <- Nat.add_0_r at 1. *)
        (*         rewrite Nat.mul_comm. *)
        (*         simpl; apply plus_lt_compat_l. *)
        (*         rewrite <- sizeSum; lia. *)
      (*      ++ simpl; apply Nat.mul_le_mono_r, log2_up_pow2. *)
      + admit.
      + admit.
      (* + rewrite e in G. *)
      (*   destruct weq; auto. *)
      (*   exfalso; clear G e. *)
      (*   apply n; clear n; destruct wltu eqn:G, Nat.eqb eqn:G0. *)
      (*   -- destruct (wltu lenValR _) eqn:G1. *)
      (*      ++ *)
      (*        lia. *)
      (*     Nat.le_sub_l *)
      (*     rewrite wordToNat_natToWord in G0. *)
      (*     rewrite wordToNat_natToWord in G0. *)
          
      (*     rewrite wordToNat_natToWord in G0. *)
      (*     arithmetizeWord. *)
      (*     (* this isn't true*) *)
      (*     admit. *)
      (* + destruct weq, wltu; auto. *)
      (*   * destruct Nat.eqb. *)
      (*     -- destruct wltu. *)
      (*        ++ exfalso; apply n. *)
      (*           admit. *)
      (*        ++ exfalso; apply n. *)
      (*           admit. *)
      (*     -- exfalso; apply n. *)
      (*        clear n; arithmetizeWord; simpl in H5; unfold lgSize in *; rewrite sizeSum. *)
      (*        unfold size in H5. *)
      (*        rewrite Zmod_0_l in *. *)
      (*        rewrite <- H5. *)
      (*        (* Compute (2 ^ (Nat.log2_up 4)). *) *)
      (*        (* Compute (evalExpr (UniBit (TruncLsb _ 1) *) *)
      (*        (*                           (Var type (SyntaxKind (Bit (2 + 1))) *) *)
      (*        (*                                (natToWord 3 4)))). *) *)
      (*        (* Z.mod_small. *) *)
      (*        (* , Zmod_0_l; auto. *) *)
      (*        (* ++ split; [apply Nat2Z.is_nonneg|]. *) *)
      (*        (*    rewrite <- Zpow_of_nat. *) *)
      (*        (*    apply inj_lt. *) *)
                
      (*        (*    log2_up_pow2 *) *)
      (*        (* rewrite Z.mod_small in H5. *) *)
          
      (*        admit. *)
      (*   * admit. *)
      (* + admit. *)
      (* + admit. *)
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x1), (Eqdep.EqdepTheory.UIP_refl _ _ x3); simpl.
      repeat rewrite evalExpr_castBits; simpl.
      admit.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + goal_consumer1.
        rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0).
        admit.
      (* + exfalso. *)
      (*   apply append_remove_prefix in H6; discriminate. *)
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + goal_consumer1.
        * admit.
        * admit.
      (* + exfalso. *)
      (*   apply append_remove_prefix in H6; discriminate. *)
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + exfalso.
        admit.
      (*   apply append_remove_prefix in H6; discriminate. *)
      (* + goal_consumer1. *)
      (*   * admit. *)
      (*   * admit. *)
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      admit.
    - hyp_consumer.
      goal_consumer2.
  Admitted.
End Proofs.
