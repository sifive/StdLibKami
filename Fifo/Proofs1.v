Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.CorrectDef.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import StdLibKami.Fifo.CorrectDef.

Section Proofs1.
  Context {ifcParams' : Fifo.Ifc.Params}.
  Variable Hsize1 : size = 1.
  Variable impl1Params impl2Params : Impl.Params.
  Local Definition fifoImpl1 := @Fifo.Impl.impl ifcParams' impl1Params.
  Local Definition fifoImpl2 := @Fifo.Impl.impl ifcParams' impl2Params.

  Record myFifoImpl1R  (implRegs : RegsT) (fifo1_bval : bool) (fifo1_dval : type k)
         (o_i o_s : RegsT) : Prop :=
    {
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
    |[ H : exists _ _ _, myFifoImpl1R _ _ _ _ _ |- _] =>
     let implRegs := fresh "implRegs" in
     let fifo1_bval := fresh "fifo1_bval" in
     let fifo1_dval := fresh "fifo1_dval" in
     let H0 := fresh "H" in
     destruct H as [implRegs [fifo1_bval [fifo1_dval H0]]]; destruct H0
    end.

  Goal FifoCorrect fifoImpl1 fifoImpl2.
    rewrite <- Nat.eqb_eq in Hsize1.
    all : econstructor 1 with (fifoR := (fun o1 o2 =>
                                           (exists implRegs fifo1_bval fifo1_dval,
                                               myFifoImpl1R implRegs
                                                            fifo1_bval fifo1_dval o1 o2)))
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
    - hyp_consumer; goal_consumer2; eauto.
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
         (implRegs : RegsT) (enqVal deqVal : word (Fifo.Ifc.lgSize + 1))
         (regArray1Regs regArray2Regs : RegsT) (o_i o_s : RegsT) : Prop :=
    {
      implRegVal' : implRegs = [(Fifo.Impl.deqPtrName,
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
    |[ H : exists _ _ _ _ _, myFifoImplR _ _ _ _ _ _ _ _ _ |- _] =>
     let implRegs := fresh "implRegs" in
     let enqVal := fresh "enqVal" in
     let deqVal := fresh "deqVal" in
     let regArray1Regs := fresh "regArray1Regs" in
     let regArray2Regs := fresh "regArray2Regs" in
     let H0 := fresh "H" in
     destruct H as [implRegs [enqVal [deqVal [regArray1Regs [regArray2Regs H0]]]]];
     destruct H0
    end.

  Goal FifoCorrect fifoImpl1' fifoImpl2'.
    destruct HRegArrayCorrect.
    rewrite <- Nat.eqb_neq in Hsize1.
    all : econstructor 1 with (fifoR := (fun o1 o2 =>
                                           (exists implRegs enqVal deqVal
                                                  regArray1Regs regArray2Regs,
                                               myFifoImplR regArrayR regArrayRegs implRegs
                                                           enqVal deqVal
                                                           regArray1Regs regArray2Regs o1 o2)))
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
    - hyp_consumer; goal_consumer2; eauto.
      Unshelve.
      all : eauto; try exact nil; try exact WO.
  Qed.
  
End Proofs2.
