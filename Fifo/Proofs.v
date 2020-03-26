Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.Proofs.

  Ltac normalize_key_hyps1 :=
    match goal with
    | [ H : context [map fst (_ ++ _)] |- _] => rewrite map_app in H
    | [ H : forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2)) |- _]
      => fold (DisjKey l1 l2) in H
    | [ H : NoDup (_ ++ _) |- _]
      => rewrite (NoDup_app_Disj_iff string_dec) in H; destruct H as [? [? ?]]
    | [ H : DisjKey (_ ++ _) _ |- _] => rewrite DisjKey_app_split_l in H; destruct H as [? ?]
    | [ H : DisjKey _ (_ ++ _) |- _] => rewrite DisjKey_app_split_r in H; destruct H as [? ?]
    | [ H : ~In _ (_ ++ _) |- _] => rewrite (nIn_app_iff string_dec) in H; destruct H as [? ?]
    | [ H : DisjKey (_ :: _) _ |- _] => rewrite DisjKey_cons_l_str in H; destruct H as [? ?]
    | [ H : DisjKey _ (_ :: _) |- _] => rewrite DisjKey_cons_r_str in H; destruct H as [? ?]
    end.

  Ltac normalize_key_hyps2 :=
    match goal with
    | [ H : context [map fst (_ :: _)] |- _] => rewrite map_cons in H
    | [ H : context [map fst nil] |- _] => rewrite map_nil in H
    | [ H : NoDup (_ :: _) |- _] => rewrite NoDup_cons_iff in H; destruct H as [? ?]
    | [ H : key_not_In _ (_ :: _) |- _] => rewrite key_not_In_cons in H; destruct H as [? ?]
    | [ H : ~In _ (_ :: _) |- _] => rewrite not_in_cons in H; destruct H as [? ?]
    end.

  Ltac normalize_key_hyps' :=
    repeat normalize_key_hyps1;
    repeat normalize_key_hyps2;
    cbn [fst] in *;
    repeat clean_useless_hyp.
  
  Ltac my_simpl_solver' :=
    match goal with
    | [ H : ?P |- ?P] => apply H
    | [ |- DisjKey nil _] => apply DisjKey_nil_l
    | [ |- DisjKey _ nil] => apply DisjKey_nil_r
    | [ |- ?a = ?a] => reflexivity
    | [ |- True] => apply I
    | [ |- NoDup nil] => constructor
    | [ |- ~In _ nil] => intro; my_simpl_solver
    | [ H : False |- _] => exfalso; apply H
    | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity
    | [ H : In _ nil |- _] => inversion H
    | [ |- SubList nil _ ] => apply SubList_nil_l
    | [ |- SubList ?a ?a] => apply SubList_refl
    | [ |- ?a = ?b] => is_evar a; reflexivity
    | [ |- ?a = ?b] => is_evar b; reflexivity
    | [ H: ?a = ?b |- _] => discriminate
    | [H1 : ?a = ?b,
            H2 : ?a <> ?b |- _] => exfalso; apply H2; rewrite H1; reflexivity
    | [H1 : ?a = ?b,
            H2 : ?b <> ?a |- _] => exfalso; apply H2; rewrite H1; reflexivity
    | [|- nil = ?l1 ++ ?l2] => symmetry; apply (app_eq_nil l1 l2); split
    | [|- ?l1 ++ ?l2 = nil] => apply (app_eq_nil l1 l2); split
    end.
  
  Ltac goal_consumer2' :=
    repeat goal_split
    ; repeat goal_body
    ; repeat normal_solver2
    ; repeat my_risky_solver
    ; repeat normal_solver2.

  Ltac normalize_key_concl1 :=
    match goal with
    | [|- context [map fst (_ ++ _)]] => rewrite map_app               
    | [|- forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2))]
      => fold (DisjKey l1 l2)
    | [ |- NoDup (_ ++ _)] => rewrite (NoDup_app_Disj_iff string_dec); repeat split
    | [ |- DisjKey (_ ++ _) _] => rewrite DisjKey_app_split_l; split
    | [ |- DisjKey _ (_ ++ _)] => rewrite DisjKey_app_split_r; split
    | [ |- ~In _ (_ ++ _)] => rewrite (nIn_app_iff string_dec); split
    | [ |- DisjKey (_ :: _) _] => rewrite DisjKey_cons_l_str; split
    | [ |- DisjKey _ (_ :: _)] => rewrite DisjKey_cons_r_str; split
    end.

  Ltac normalize_key_concl2 :=
    match goal with
    | [ |- context [map fst (_ :: _)]] => rewrite map_cons
    | [ |- context [map fst nil]] => rewrite map_nil
    | [ |- NoDup (_ :: _)] => rewrite NoDup_cons_iff; split
    | [ |- key_not_In _ (_ :: _)] => rewrite key_not_In_cons; split
    | [ |- ~In _ (_ :: _)] => rewrite not_in_cons; split
    | [ |- key_not_In _ ?l] =>
      match l with
      | _ => has_evar l; idtac
      | _ => rewrite key_not_In_fst
      end
    | [ |- ~In _ (_ :: _)] => rewrite not_in_cons; split
    | [ |- ~In _ (_ ++ _)] => rewrite (nIn_app_iff string_dec); split
    end.

  Ltac normalize_key_concl' :=
    repeat normalize_key_concl1;
    repeat normalize_key_concl2;
    cbn [fst];
    repeat (solve_keys || my_simpl_solver).
  
  Ltac resolve_wb'' :=
    let HNoDup := fresh "H" in
    let HSubList := fresh "H" in
    match goal with
    | [HSemAction1 :SemAction ?o1 ?a_i _ _ _ _,
                    HActionWb : ActionWb ?myR ?a_i |- _] =>
      assert (NoDup (map fst o1)) as HNoDup
      ;[repeat normalize_key_concl'
       | assert (SubList myR (getKindAttr o1)) as HSubList
         ;[clear HNoDup HSemAction1
           ; repeat normalize_sublist_l
           ; sublist_sol
          | specialize (HActionWb _ _ _ _ _ HNoDup HSubList HSemAction1)
            as [[? [? [? [? ?]]]] ?]
            ; try resolve_sublist2
            ; clear HSemAction1 HNoDup HSubList]]
    | [HSemAction1 : SemAction ?o1 (?a_i _) _ _ _ _,
                     HActionWb : forall _, ActionWb ?myR (?a_i _) |- _] =>
      assert (NoDup (map fst o1)) as HNoDup
      ;[repeat normalize_key_concl'
       | assert (SubList myR (getKindAttr o1)) as HSubList
         ;[clear HNoDup HSemAction1
           ; repeat normalize_sublist_l
           ; sublist_sol
          | specialize (HActionWb _ _ _ _ _ _ HNoDup HSubList HSemAction1)
            as [[? [? [? [? ?]]]] ?]
            ; try resolve_sublist2
            ; clear HSemAction1 HNoDup HSubList]]
    | [HSemAction1 : SemAction ?o1 (?a_i _ _ _ _ _) _ _ _ _,
                     HActionWb :  forall _ _ _ _, ActionWb ?myR (?a_i _ _ _ _ _)|- _] =>
      assert (NoDup (map fst o1)) as HNoDup
      ;[repeat normalize_key_concl'
       | assert (SubList myR (getKindAttr o1)) as HSubList
         ;[clear HNoDup HSemAction1
          | specialize (HActionWb _ _ _ _ _ _ _ _ _ HNoDup HSubList HSemAction1)
            as [[? [? [? [? ?]]]] ?]
            ; try resolve_sublist2
            ; clear HSemAction1 HNoDup HSubList]]
    end.
  
  Ltac resolve_wb_testing :=
    let HNoDup := fresh "H" in
    let HSubList := fresh "H" in
    match goal with
    | [HSemAction1 :SemAction ?o1 ?a_i _ _ _ _,
                    HActionWb : ActionWb ?myR ?a_i |- _] =>
      idtac "found 1 :" HSemAction1 HActionWb
    | [HSemAction1 : SemAction ?o1 (?a_i _) _ _ _ _,
                     HActionWb : forall _, ActionWb ?myR (?a_i _) |- _] =>
      idtac "found 2 :" HSemAction1 HActionWb;
      assert (NoDup (map fst o1)) as HNoDup
      ;[|]
    | [HSemAction1 : SemAction ?o1 (?a_i _ _ _ _ _) _ _ _ _,
                     HActionWb :  forall _ _ _ _, ActionWb ?myR (?a_i _ _ _ _ _)|- _] =>
      idtac "found 3 :" HSemAction1 HActionWb
    end.
  
  Ltac hyp_consumer1' :=
    repeat mySubst;
    normalize_key_hyps';
    repeat (repeat main_body
            ; repeat mySubst
            ; repeat (my_simplifier; repeat clean_useless_hyp)
            ; repeat mySubst
            ; repeat normalize_key_hyps
            ; repeat (my_simplifier; repeat clean_useless_hyp)
            ; repeat (resolve_wb''; repeat clean_useless_hyp)
            ; repeat resolve_rel'
            ; repeat mySubst
            ; repeat (my_simplifier ; repeat clean_useless_hyp))
    ; repeat my_simpl_solver'.

  Ltac goal_body' :=
    match goal with
    | [ |- SemAction _ (Return _) _ _ _ _ ] => econstructor 10
    | [ |- SemAction _ (MCall _ _ _ _) _ _ _ _] => econstructor 1
    | [ |- SemAction _ (LetAction _ _) _ _ _ _] => econstructor 3
    | [ |- SemAction _ (ReadReg _ _ _) _ _ _ _] => econstructor 5
    | [ |- SemAction _ (WriteReg _ _ _) _ _ _ _] => econstructor 6
    | [ |- SemAction _ (IfElse _ _ _ _) _ _ _ _]
      => eapply SemAction_if_split
         ;[ find_if_inside| | | | ]
    | [ |- SemAction _ (LetExpr _ _) _ _ _ _] => econstructor 2
    | [ |- SemAction _ (ReadNondet _ _) _ _ _ _] => econstructor 4
    | [ |- SemAction _ (Sys _ _) _ _ _ _] => econstructor 9
    | [ H : SemAction ?o ?a _ _ _ _ |- SemAction ?o ?a _ _ _ _]
      => apply H
    | [ H : SemAction ?o1 ?a _ _ _ _ |- SemAction ?o2 ?a _ _ _ _]
      => eapply SemActionExpand;[| apply H; sublist_sol]
    end.

  Ltac doUpdRegs_red' :=  
    repeat 
      (match goal with
       | [ |- context [ doUpdRegs nil _]] => rewrite doUpdRegs_nil
       | [ |- context [ doUpdReg nil _]] => rewrite doUpdReg_nil
       | |- context [ oneUpdRegs ?r ?o ] =>
         let TMP := fresh "H" in
         assert (TMP : ~ In (fst r) (map fst o));
         [ repeat
             match goal with
             | |- context [ map fst (doUpdRegs _ _) ] => rewrite doUpdRegs_preserves_keys
             end; solve_keys
         | rewrite (oneUpdRegs_notIn _ _ TMP); clear TMP ]
       | |- context [ doUpdReg ?u ?r ] =>
         let TMP := fresh "H" in
         assert (TMP : ~ In (fst r) (map fst u));
         [ repeat
             match goal with
             | |- context [ map fst (doUpdRegs _ _) ] => rewrite doUpdRegs_preserves_keys
             end; solve_keys
         | rewrite (doUpdReg_notIn _ _ TMP); clear TMP ]; cbn[fst]
       end);
    repeat
      match goal with
      | |- context [oneUpdReg _ _ ] => cbv [oneUpdReg fst]
      | [|- context [?a =? ?a]] => rewrite eqb_refl 
      | H : fst ?r1 = fst ?r2
        |- context [fst ?r1 =? fst ?r2] =>
        rewrite (proj2 (String.eqb_eq (fst r1) (fst r2)) H)
      | H : fst ?r2 = fst ?r1
        |- context [fst ?r1 =? fst ?r2] =>
        rewrite eqb_sym, (proj2 (String.eqb_eq (fst r2) (fst r1)) H)
      | H : fst ?r1 <> fst ?r2
        |- context [fst ?r1 =? fst ?r2] =>
        rewrite (proj2 (String.eqb_neq (fst r1) (fst r2)) H)
      | H : fst ?r2 <> fst ?r1
        |- context [fst ?r1 =? fst ?r2] =>
        rewrite eqb_sym, (proj2 (String.eqb_neq (fst r2) (fst r1)) H) 
      | H : ?a = ?b
        |- context [?a =? ?b] =>
        rewrite (proj2 (String.eqb_eq a b) H)
      | H : ?b = ?a
        |- context [?a =? ?b] =>
        rewrite eqb_sym, (proj2 (String.eqb_eq b a) H)
      | H : ?a <> ?b
        |- context [?a =? ?b] =>
        rewrite (proj2 (String.eqb_neq a b) H)
      | H : ?b <> ?a
        |- context [?a =? ?b] =>
        rewrite eqb_sym, (proj2 (String.eqb_neq b a) H)
      end.

  Ltac basic_goal_consumer' :=
    repeat (repeat goal_split
            ; repeat goal_body'
            ; repeat normal_solver)
    ; repeat (repeat doUpdRegs_simpl
              ; doUpdRegs_red'
              ; repeat normal_solver).
  
  Ltac resolve_In :=
    let TMP := fresh "H" in
    match goal with
    | [ HNoDup : NoDup (map fst ?o),
                 H1 : In (?s, ?a) ?o,
                      H2 : In (?s, ?b) ?o |- _]
      => specialize (NoDup_map_fst HNoDup H1 H2) as TMP; EqDep_subst; clear H1
    end.
  
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
