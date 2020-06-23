Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.ImpExt4.
Require Import PL.DenotationalSemantics.
Require Import PL.SmallStepSemantics.

(** General Theorem for equivalence between a denotational semantics and small step semantics.
    The theorem for the equivalence between a denotational semantics and small step semantics is proven in 2 cases: one for binary denotational semantics, another for ternary denotational semantics *)

(** The overall proof idea is almost the same as taught in class:
    1. Denotation --> Small step:
        By induction and congruence rules.
    2. Small step --> Denotation:
        By proving that taking a small step preserve the result. *)

(* ################################################################# *)
(* Basic Congruence Theorems of Multi-step Relations *)

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus1.
      exact H.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult1.
      exact H.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BEq1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 == a2) (a1' == a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq1.
      exact H.
Qed.

Theorem multi_congr_BEq2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 == a2) (a1 == a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BLe1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 <= a2) (a1' <= a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le1.
      exact H.
Qed.

Theorem multi_congr_BLe2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 <= a2) (a1 <= a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BNot: forall st b b',
  multi_bstep st b b' ->
  multi_bstep st (BNot b) (BNot b').
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_NotStep.
      exact H.
Qed.

Theorem multi_congr_BAnd: forall st b1 b1' b2,
  multi_bstep st b1 b1' ->
  multi_bstep st (BAnd b1 b2) (BAnd b1' b2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_AndStep.
      exact H.
Qed.

Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + unfold constant_func in H.
    rewrite H.
    reflexivity.
  + rewrite <- H.
    etransitivity_n1; [reflexivity |].
    apply AS_Id.
  + etransitivity.
    { apply multi_congr_APlus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_APlus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Plus.
  + etransitivity.
    { apply multi_congr_AMinus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMinus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Minus.
  + etransitivity.
    { apply multi_congr_AMult1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMult2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Mult.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      reflexivity.
    - unfold Sets.full.
      tauto.
  + split.
    - unfold Sets.empty.
      tauto.
    - intros.
      reflexivity.
  + assert (multi_bstep st (a1 == a2) (aeval a1 st == aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BEq1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BEq2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_eq; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Eq_True, H0.
    - apply BS_Eq_False, H0.
  + assert (multi_bstep st (a1 <= a2) (aeval a1 st <= aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BLe1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BLe2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_le; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Le_True, H0.
    - apply BS_Le_False.
      lia.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH2.
        unfold Sets.complement in H; exact H.
      * apply BS_NotFalse.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH1.
        unfold Sets.complement in H; tauto.
      * apply BS_NotTrue.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - assert (multi_bstep st (b1 && b2) b2).
      {
        etransitivity_n1.
        * apply multi_congr_BAnd, IHb11, H.
        * apply BS_AndTrue.
      }
      split; unfold Sets.intersect; intros;
      (etransitivity; [exact H0 |]).
      * apply IHb21; tauto.
      * apply IHb22; tauto.
    - split; unfold Sets.intersect; intros; [ tauto |].
      etransitivity_n1.
      * apply multi_congr_BAnd, IHb12, H.
      * apply BS_AndFalse.
Qed.

Corollary semantic_equiv_bexp1_true: forall st b,
  beval b st -> multi_bstep st b BTrue.
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.
  
Corollary semantic_equiv_bexp1_false: forall st b,
  (Sets.complement (beval b) st -> multi_bstep st b BFalse).
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.

Lemma aeval_preserve: forall st a1 a2,
  astep st a1 a2 ->
  aeval a1 st  = aeval a2 st.
Proof.
  intros.
  induction H.
  + simpl. reflexivity.
  + simpl. unfold Func.add. lia.
  + simpl. unfold Func.add. lia.
  + simpl. unfold Func.add, constant_func. reflexivity.
  + simpl. unfold Func.sub. lia.
  + simpl. unfold Func.sub. lia.
  + simpl. unfold Func.sub, constant_func. reflexivity.
  + simpl. unfold Func.mul. nia.
  + simpl. unfold Func.mul. nia.
  + simpl. unfold Func.mul, constant_func. reflexivity.
Qed.

Theorem semantic_equiv_aexp2: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  induction_1n H.
  + simpl. reflexivity.
  + pose proof aeval_preserve _ _ _ H. lia.
Qed.

Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st  <-> beval b2 st).
Proof.
  intros.
  induction H.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_eq.
    lia.
  + apply aeval_preserve in H0. simpl. unfold Func.test_eq. lia.
  + simpl. unfold Func.test_eq, Sets.full. tauto.
  + simpl. unfold Func.test_eq, Sets.empty. tauto.
  + apply aeval_preserve in H. simpl. unfold Func.test_le. lia.
  + apply aeval_preserve in H0. simpl. unfold Func.test_le. lia.
  + simpl. unfold Func.test_le, Sets.full. tauto.
  + simpl. unfold Func.test_le, constant_func, Sets.empty. lia.
  + simpl. unfold Sets.complement. tauto.
  + simpl. unfold Sets.complement, Sets.full, Sets.empty. tauto.
  + simpl. unfold Sets.complement, Sets.full, Sets.empty. tauto.
  + simpl. unfold Sets.intersect. tauto.
  + simpl. unfold Sets.intersect, Sets.full. tauto.
  + simpl. unfold Sets.intersect, Sets.empty. tauto.
Qed.

Theorem semantic_equiv_bexp3: forall st b TF,
  multi_bstep st b TF ->
  (TF = BTrue -> beval b st) /\
  (TF = BFalse -> ~ beval b st).
Proof.
  intros.
  induction_1n H; simpl; intros.
  + split; intros; subst; simpl; unfold Sets.full, Sets.empty; tauto.
  + pose proof beval_preserve _ _ _ H. tauto.
Qed.

(** Lemmas Finished *)

(* ################################################################# *)
(* Equivalence Between Binary Denotational Semantics & Small Step Semantics *)

Local Open Scope imp.

Module BinEquiv.

(** Any step in simplifying aexp corresponds to a step in simplifying cexp. *)
Theorem multi_congr_CAss: forall st X a a',
  multi_astep st a a' ->
  BinStep.multi_cstep (CAss X a, st) (CAss X a', st).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + BinStep.etransitivity_n1.
    - exact IHrt.
    - apply BinStep.CS_AssStep.
      exact H.
Qed.

(** A step in a single cexp corresponds to a step in a sequence of cexp, which execute the same cexp at first. *)
Theorem multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  BinStep.multi_cstep (c1, st1) (c1', st1') ->
  BinStep.multi_cstep (CSeq c1 c2, st1) (CSeq c1' c2, st1').
Proof.
  intros.
  BinStep.induction_n1 H.
  + reflexivity.
  + BinStep.etransitivity_n1.
    - exact IHrt.
    - apply BinStep.CS_SeqStep.
      exact H.
Qed.

(** Any step in simplifying bexp corresponds to a step in simplifying cexp. *)
Theorem multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  BinStep.multi_cstep
    (CIf b c1 c2, st)
    (CIf b' c1 c2, st).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + BinStep.etransitivity_n1.
    - exact IHrt.
    - apply BinStep.CS_IfStep.
      exact H.
Qed.

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c,
  (forall st1 st2, BinRel.ceval c st1 st2 -> BinStep.multi_cstep (c, st1) (CSkip, st2)) ->
  iter_loop_body b (BinRel.ceval c) n st1 st2 ->
  BinStep.multi_cstep (While b Do c EndWhile, st1) (CSkip, st2).
Proof.
  intros.
  revert st1 st2 H0; induction n; intros.
  + simpl in H0.
    unfold Relation_Operators.test_rel in H0.
    destruct H0.
    subst st2.
    BinStep.etransitivity_1n ; [apply BinStep.CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_false, H1 |].
    BinStep.etransitivity_1n; [apply BinStep.CS_IfFalse |].
    reflexivity.
  + simpl in H0.
    unfold Relation_Operators.concat at 1,
           Relation_Operators.test_rel in H0.
    destruct H0 as [st [[? H0] ?]]; subst st.
    unfold Relation_Operators.concat in H2.
    destruct H2 as [st1' [? ?]].
    BinStep.etransitivity_1n; [apply BinStep.CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H0 |].
    BinStep.etransitivity_1n; [apply BinStep.CS_IfTrue |].
    etransitivity; [apply multi_congr_CSeq, H, H1|].
    BinStep.etransitivity_1n; [apply BinStep.CS_Seq |].
    apply IHn, H2.
Qed.

(** First direction: Denotation --> Small Step *)
Theorem semantic_equiv_com1: forall st1 st2 c,
  BinRel.ceval c st1 st2 -> BinStep.multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H; induction c; simpl; intros; unfold BinRel.ceval,BinRel.sem,ceval_by_sem in H; simpl in H.
  + rewrite H.
    reflexivity.
  + destruct H.
    BinStep.etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply BinStep.CS_Ass; tauto.
  + destruct H as [st' [? ?]].
    etransitivity; [apply multi_congr_CSeq, IHc1, H |].
    BinStep.etransitivity_1n; [ apply BinStep.CS_Seq |].
    apply IHc2, H0.
  + pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H]; destruct H as [st [[? ?] ?]]; subst st.
    - etransitivity; [apply multi_congr_CIf, H0, H2 |].
      BinStep.etransitivity_1n; [apply BinStep.CS_IfTrue |].
      apply IHc1, H3.
    - etransitivity; [apply multi_congr_CIf, H1, H2 |].
      BinStep.etransitivity_1n; [apply BinStep.CS_IfFalse |].
      apply IHc2, H3.
  + destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

(** Any small step from a pair (c1, st1) to (c2, st2) will not change the result of its denotation. *)
Lemma ceval_preserve: forall c1 c2 st1 st2,
  BinStep.cstep (c1, st1) (c2, st2) ->
  forall st3, BinRel.ceval c2 st2 st3 -> BinRel.ceval c1 st1 st3.
Proof.
(** We could prove a stronger conclusion:
      forall st3, ceval c1 st1 st3 <-> ceval c2 st2 st3.
    But this single direction version is enough to use. *)
  intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  revert c1 c2 st1 st2 st3 H0 H1; unfold BinRel.ceval,BinRel.sem,ceval_by_sem; induction H; subst; simpl; intros.
  + apply aeval_preserve in H.
    injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl.
    unfold BinRel.asgn_sem.
    rewrite H.
    tauto.
  + injection H1 as ? ?.
    injection H2 as ? ?.
    subst.
    simpl. simpl in H3.
    unfold BinRel.skip_sem,Relation_Operators.id in H3.
    unfold BinRel.asgn_sem.
    subst.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    unfold BinRel.seq_sem,Relation_Operators.concat in H2.
    unfold BinRel.seq_sem,Relation_Operators.concat.
    destruct H2 as [st2' [? ?]].
    exists st2'.
    assert ((c1, st1) = (c1, st1)). { reflexivity. }
    assert ((c1', st2) = (c1', st2)). { reflexivity. }
    specialize (IHcstep _ _ _ _ st2' H2 H3).
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    exists st2.
    split.
    - reflexivity.
    - exact H2.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    unfold BinRel.if_sem in H2.
    unfold BinRel.if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel in H2.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    apply beval_preserve in H.
    simpl in H2.
    simpl.
    unfold Sets.complement in H2.
    unfold Sets.complement.
    destruct H2 as [[st2' ?] | [st2' ?]]; [left | right];
      exists st2'; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    unfold BinRel.if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    left; exists st2; simpl.
    unfold Sets.full; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    unfold BinRel.if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    right; exists st2; simpl.
    unfold Sets.complement, Sets.empty; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    pose proof BinRel.loop_unrolling b c.
    specialize (H st2 st3).
    tauto.
Qed.

(** Second direction: Small Step --> Denotation *)
Theorem semantic_equiv_com2: forall c st1 st2,
  BinStep.multi_cstep (c, st1) (CSkip, st2) -> BinRel.ceval c st1 st2.
Proof.
  intros.
  remember (CSkip) as c' eqn:H0.
  revert H0; BinStep.induction_1n H; simpl; intros; subst.
  + reflexivity.
  + pose proof ceval_preserve _ _ _ _ H st2.
    tauto.
Qed.

(* ################################################################# *)
(* Final theorem for binary denotational semantics *)
Theorem semantic_equiv: forall c st1 st2,
  BinRel.ceval c st1 st2 <-> BinStep.multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

End BinEquiv.

(* ################################################################# *)
(* Equivalence between ternary denotational semantics & small step semantics *)

(** In the proof, we used a concept “Middle parameter” to denote the step count (or trace) in the corresponding denotational semantics. *)

Module TerEquiv.

Theorem multi_congr_CAss: forall B (mp : mid_param state B) st X a a',
  multi_astep st a a' ->
  TerStep.multi_cstep mp
  (CAss X a, st) (MP_zero mp) (CAss X a', st).
Proof.
  intros.
  induction_n1 H.
  + destruct mp. TerStep.rt_reflexivity.
  + TerStep.etransitivity_n1.
    - exact IHrt.
    - instantiate (b:=false). reflexivity.
    - apply TerStep.CS_AssStep.
      exact H.
Qed.

Theorem multi_congr_CIf: forall B (mp : mid_param state B) st b b' c1 c2,
  multi_bstep st b b' ->
  TerStep.multi_cstep mp
    (CIf b c1 c2, st)
    (MP_zero mp)
    (CIf b' c1 c2, st).
Proof.
  intros.
  induction_n1 H.
  + destruct mp. TerStep.rt_reflexivity.
  + TerStep.etransitivity_n1.
    - exact IHrt.
    - instantiate (b0:=false). reflexivity.
    - apply TerStep.CS_IfStep.
      exact H.
Qed.

Theorem multi_congr_CSeq: forall B (mp : mid_param state B) st1 c1 st1' c1' c2 cnt,
  TerStep.multi_cstep mp (c1, st1) cnt (c1', st1') ->
  TerStep.multi_cstep mp (CSeq c1 c2, st1) cnt (CSeq c1' c2, st1').
Proof.
  intros.
  TerStep.induction_n1 H.
  + TerStep.rt_reflexivity.
  + TerStep.etransitivity_n1.
    - exact IHrt.
    - instantiate (b:=false). reflexivity.
    - apply TerStep.CS_SeqStep.
      exact H.
  + TerStep.etransitivity_n1.
    - exact IHrt.
    - instantiate (b:=true). subst.
      destruct mp. reflexivity.
    - apply TerStep.CS_SeqStep.
      exact H.
Qed.

Lemma semantic_equiv_iter_loop1: forall B (mp : mid_param state B) st1 st2 n b c cnt,
  (forall st1 cnt st2, TerSem.ceval mp c st1 cnt st2 -> TerStep.multi_cstep mp (c, st1) cnt (CSkip, st2)) ->
  TerSem.iter_loop_body mp b (TerSem.ceval mp c) n st1 cnt st2 ->
  TerStep.multi_cstep mp (While b Do c EndWhile, st1) cnt (CSkip, st2).
Proof.
  intros.
  destruct mp; revert st1 st2 cnt H0; induction n; simpl; intros.
  + simpl in H0.
    destruct H0.
    subst st2.
    TerStep.etransitivity_1n ; [apply TerStep.CS_While | reflexivity |].
    TerStep.rt_etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_false, H1 | simpl; rewrite add_zero_l; reflexivity |].
    TerStep.etransitivity_1n; [apply TerStep.CS_IfFalse | |].
    { destruct H1. subst cnt. instantiate (c':=zero). simpl. rewrite add_zero_r. reflexivity. }
    TerStep.rt_reflexivity.
  + simpl in H0.
    unfold TerSem.seq_sem at 1,
           TerSem.test_sem in H0.
    destruct H0 as [t1 [t2 [st [[? [H0 ?]] [? ?]]]]]; subst st.
    destruct H3 as [t1' [t2' [st1' [? [? ?]]]]].
    TerStep.etransitivity_1n; [apply TerStep.CS_While | reflexivity |].
    TerStep.rt_etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H0 | simpl; rewrite add_zero_l; reflexivity |].
    TerStep.etransitivity_1n; [apply TerStep.CS_IfTrue | subst; reflexivity |].
    TerStep.rt_etransitivity; [apply multi_congr_CSeq,H,H1 | subst; reflexivity |].
    TerStep.etransitivity_1n; [apply TerStep.CS_Seq | reflexivity |].
    apply IHn, H3.
Qed.

Theorem semantic_equiv_com1: forall B (mp : mid_param state B) st1 st2 c cnt,
  TerSem.ceval mp c st1 cnt st2 -> TerStep.multi_cstep mp (c, st1) cnt (Skip, st2).
Proof.
  intros.
  destruct mp; revert st1 cnt st2 H; induction c; simpl; unfold TerSem.ceval,TerStep.extend_mp; simpl; intros.
  + destruct H; subst.
    TerStep.rt_reflexivity.
  + destruct H as [? [? ?]].
    TerStep.etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - instantiate (1:=true). simpl. rewrite add_zero_l. apply H1.
    - apply TerStep.CS_Ass; tauto.
  + destruct H as [t1 [t2 [st' [? [? ?]]]]].
    TerStep.rt_etransitivity; [apply multi_congr_CSeq, IHc1, H | apply H1 |].
    TerStep.etransitivity_1n; [ apply TerStep.CS_Seq | reflexivity |].
    apply IHc2, H0.
  + pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H]; destruct H as [t1 [t2 [st [[? [? ?]] [? ?]]]]]; subst st.
    - TerStep.rt_etransitivity; [apply multi_congr_CIf, H0, H2 | simpl; rewrite add_zero_l; reflexivity |].
      TerStep.etransitivity_1n; [apply TerStep.CS_IfTrue | subst; reflexivity |].
      subst. apply IHc1, H4.
    - TerStep.rt_etransitivity; [apply multi_congr_CIf, H1, H2 | simpl; rewrite add_zero_l; reflexivity |].
      TerStep.etransitivity_1n; [apply TerStep.CS_IfFalse | subst; reflexivity |].
      subst. apply IHc2, H4.
  + destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

(** Need 2 lemmas in 2 cases: one lemma for the small step that does not change  step count (or trace), another lemma for the small step that changes step count (or trace). *)
Lemma ceval_preserve_false: forall B (mp : mid_param state B) c1 c2 st1 st2 cnt,
  TerStep.cstep (c1, st1) false (c2, st2) ->
  forall st3, TerSem.ceval mp c2 st2 cnt st3 -> TerSem.ceval mp c1 st1 cnt st3.
Proof.
  intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  remember false as b eqn:Hb.
  revert c1 c2 st1 st2 st3 cnt H0 H1. unfold TerSem.ceval; induction H; subst; intros; destruct mp eqn:Emp.
  + apply aeval_preserve in H.
    injection H0 as ? ?.
    injection H1 as ? ?.
    subst. simpl. simpl in H2.
    unfold TerSem.asgn_sem.
    rewrite H.
    tauto.
  + inversion Hb.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CSeq in H2.
    rewrite ceval_CSeq.
    simpl in H2. unfold TerSem.seq_sem in H2.
    simpl. unfold TerSem.seq_sem.
    destruct H2 as [t1 [t2 [st2' [? [? ?]]]]].
    exists t1,t2,st2'.
    pose proof (IHcstep eq_refl _ _ _ _ _ _ eq_refl eq_refl H0).
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    exists zero,cnt,st2.
    split.
    - rewrite ceval_CSkip. simpl.
      unfold TerSem.skip_sem. tauto.
    - split; [exact H2 | simpl; rewrite add_zero_l; reflexivity].
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf in H2.
    rewrite ceval_CIf.
    simpl in H2. simpl.
    unfold TerSem.if_sem,TerSem.union_sem,TerSem.seq_sem,TerSem.test_sem in H2.
    unfold TerSem.if_sem,TerSem.union_sem,TerSem.seq_sem,TerSem.test_sem.
    apply beval_preserve in H.
    simpl in H2.
    simpl.
    unfold Sets.complement in H2.
    unfold Sets.complement.
    destruct H2 as [[t1 [t2 [st2' ?]]] | [t1 [t2 [st2' ?]]]]; [left | right];
      exists t1,t2,st2'; tauto.
  + inversion Hb.
  + inversion Hb.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    pose proof TerSem.loop_unrolling mp b c.
    subst.
    specialize (H4 cnt st2 st3).
    tauto.
Qed.

Lemma ceval_preserve_true: forall B (mp : mid_param state B) c1 c2 st1 st2 cnt,
  TerStep.cstep (c1, st1) true (c2, st2) ->
  forall st3, TerSem.ceval mp c2 st2 cnt st3 -> TerSem.ceval mp c1 st1 (MP_add mp (MP_one mp st1 st2) cnt) st3.
Proof.
  intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  remember true as b eqn:Hb.
  revert c1 c2 st1 st2 st3 cnt H0 H1. unfold TerSem.ceval; induction H; intros.
  + inversion Hb.
  + injection H1 as ? ?.
    injection H2 as ? ?.
    subst.
    simpl. simpl in H3.
    unfold TerSem.skip_sem in H3.
    unfold TerSem.asgn_sem.
    destruct H3. subst.
    split. tauto. split. tauto. simpl. rewrite (MP_add_zero_r mp). reflexivity.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst. destruct mp.
    simpl. simpl in H2.
    unfold TerSem.seq_sem in H2.
    unfold TerSem.seq_sem.
    destruct H2 as [t1 [t2 [st2' [? [? ?]]]]].
    pose proof (IHcstep eq_refl _ _ _ _ _ _ eq_refl eq_refl H0).
    exists (add (one st1 st2) t1),t2,st2'.
    subst. simpl. split; [tauto|split; [tauto|]]. rewrite <- add_assoc.
    tauto.
  + inversion Hb.
  + inversion Hb.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst. destruct mp.
    left; exists (one st2 st2),cnt,st2; simpl.
    unfold Sets.full,TerSem.test_sem. tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst. destruct mp.
    right; exists (one st2 st2),cnt,st2; simpl.
    unfold TerSem.test_sem,Sets.complement, Sets.empty. tauto.
  + inversion Hb.
Qed.

Theorem semantic_equiv_com2: forall B (mp : mid_param state B) c st1 st2 cnt,
  TerStep.multi_cstep mp (c, st1) cnt (CSkip, st2) -> TerSem.ceval mp c st1 cnt st2.
Proof.
  intros.
  remember (CSkip) as c' eqn:H0.
  revert H0; TerStep.induction_1n H; simpl; intros; subst.
  + unfold TerSem.ceval. simpl. destruct mp. unfold TerSem.skip_sem. tauto.
  + specialize (IHrt eq_refl).
    pose proof ceval_preserve_false _ mp _ _ _ _ _ H st2 IHrt.
    tauto.
  + specialize (IHrt eq_refl).
    pose proof ceval_preserve_true _ mp _ _ _ _ _ H st2 IHrt.
    destruct mp.
    tauto.
Qed.

Theorem semantic_equiv: forall B (mp : mid_param state B) c st1 cnt st2,
  TerSem.ceval mp c st1 cnt st2 <-> TerStep.multi_cstep mp (c, st1) cnt (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

(* ################################################################# *)
(* Final theorem for ternary denotational semantics *)

Theorem semantic_equiv_StepCnt: forall c st1 cnt st2,
  StepCnt.ceval c st1 cnt st2 <-> TerStep.multi_cstep_cnt (c, st1) cnt (CSkip, st2).
Proof.
  apply semantic_equiv.
Qed.

Theorem semantic_equiv_Trace: forall c st1 l st2,
  Trace.ceval c st1 l st2 <-> TerStep.multi_cstep_trace (c, st1) l (CSkip, st2).
Proof.
  apply semantic_equiv.
Qed.

End TerEquiv.

