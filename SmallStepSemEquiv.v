Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.ImpExt4.
Require Import PL.DenotationalSemantics.
Require Import PL.SmallStepSemantics.

(* General Theorem for equivalence between a denotational semantics and small step semantics. *)

(* ################################################################# *)
(** * Congruence Theorems of Multi-step Relations *)

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
Local Open Scope imp.

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

Theorem semantic_equiv_com1: forall st1 st2 c,
  BinRel.ceval c st1 st2 -> BinStep.multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H; induction c; intros.
  + rewrite BinRel.ceval_CSkip in H.
    unfold Relation_Operators.id in H.
    rewrite H.
    reflexivity.
  + rewrite BinRel.ceval_CAss in H.
    destruct H.
    BinStep.etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply BinStep.CS_Ass; tauto.
  + rewrite BinRel.ceval_CSeq in H.
    unfold Relation_Operators.concat in H.
    destruct H as [st' [? ?]].
    etransitivity; [apply multi_congr_CSeq, IHc1, H |].
    BinStep.etransitivity_1n; [ apply BinStep.CS_Seq |].
    apply IHc2, H0.
  + rewrite BinRel.ceval_CIf in H.
    unfold if_sem in H.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H]; destruct H as [st [[? ?] ?]]; subst st.
    - etransitivity; [apply multi_congr_CIf, H0, H2 |].
      BinStep.etransitivity_1n; [apply BinStep.CS_IfTrue |].
      apply IHc1, H3.
    - etransitivity; [apply multi_congr_CIf, H1, H2 |].
      BinStep.etransitivity_1n; [apply BinStep.CS_IfFalse |].
      apply IHc2, H3.
  + rewrite BinRel.ceval_CWhile in H.
    unfold loop_sem in H.
    unfold Relation_Operators.omega_union in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

Print ceval_CAss.

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
  revert c1 c2 st1 st2 st3 H0 H1; induction H; simpl; intros.
  + apply aeval_preserve in H.
    injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite BinRel.ceval_CAss in H2.
    rewrite BinRel.ceval_CAss.
    rewrite H.
    tauto.
  + injection H1 as ? ?.
    injection H2 as ? ?.
    subst.
    rewrite BinRel.ceval_CSkip in H3.
    rewrite BinRel.ceval_CAss.
    unfold Relation_Operators.id in H3.
    subst.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite BinRel.ceval_CSeq in H2.
    rewrite BinRel.ceval_CSeq.
    unfold Relation_Operators.concat in H2.
    unfold Relation_Operators.concat.
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
    rewrite BinRel.ceval_CIf in H2.
    rewrite BinRel.ceval_CIf.
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
    rewrite BinRel.ceval_CIf.
    unfold BinRel.if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    left; exists st2; simpl.
    unfold Sets.full; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite BinRel.ceval_CIf.
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

Theorem semantic_equiv: forall c st1 st2,
  BinRel.ceval c st1 st2 <-> BinStep.multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.
