Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.DenotationalSemantics.

(** In this task, you should first prove a general theorem which can be used to
    prove an equivalence between two recursively defined semantics, and another
    general theorem which can be used to prove an equivalence between a
    recursively defined program semantics and a small step semantics.

    Then, you need to prove the equivalence among three denotational program
    semantics and a small step semantics. *)

Definition bin_step_equiv (X : state -> state -> Prop) 
                          (Y : state -> Z -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists z, Y st1 z st2).

Definition bin_trace_equiv (X : state -> state -> Prop) 
                           (Y : state -> list state -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists l, Y st1 l st2).

(** Following lemma is just for convenience in proof. *)
Lemma BinRel_ceval_fold_while (c: com) (b: bexp):
  forall st1 st2 st3,
    beval b st1 ->
    BinRel.ceval c st1 st3 ->
    BinRel.ceval (While b Do c EndWhile) st3 st2 ->
    BinRel.ceval (While b Do c EndWhile) st1 st2.
Proof.
  intros.
  simpl in H1.
  destruct H1 as [n H1].
  exists (S n).
  simpl.
  exists st1.
  split.
  + unfold Relation_Operators.test_rel. tauto.
  + exists st3. tauto.
Qed.

(** Following module is to prove that every element in the recursive definition
    of "BinRel.ceval" and "StepCnt.ceval" is equivalent. *)
Module BinStepEquiv.

Lemma bin_step_skip_sem_equiv:
  bin_step_equiv (BinRel.ceval CSkip) (StepCnt.ceval CSkip).
Proof.
  unfold bin_step_equiv.
  simpl.
  split; intros.
  + exists 0.
    firstorder.
  + destruct H.
    firstorder.
Qed.

Lemma bin_step_asgn_sem_equiv:
  forall (X: var) (E: aexp),
  bin_step_equiv (BinRel.ceval (CAss X E)) (StepCnt.ceval (CAss X E)).
Proof.
  unfold bin_step_equiv.
  simpl.
  split; intros.
  + exists 1.
    firstorder.
  + destruct H.
    firstorder.
Qed.

Lemma bin_step_seq_sem_equiv  (c1 c2: com):
  bin_step_equiv (BinRel.ceval c1) (StepCnt.ceval c1) ->
  bin_step_equiv (BinRel.ceval c2) (StepCnt.ceval c2) ->
  bin_step_equiv (BinRel.ceval (CSeq c1 c2)) (StepCnt.ceval (CSeq c1 c2)).
Proof.
  unfold bin_step_equiv.
  simpl.
  intros IHc1 IHc2 st1 st2.
  split; intros.
  + inversion H as [st3 H0]. destruct H0 as [H1 H2].
    specialize (IHc1 st1 st3);
      destruct IHc1 as [IHc1 IHc1'];
      specialize (IHc1 H1);
      destruct IHc1 as [a1 IHc1].
    specialize (IHc2 st3 st2);
      destruct IHc2 as [IHc2 IHc2'];
      specialize (IHc2 H2);
      destruct IHc2 as [a2 IHc2].
    exists (a1 + a2).
    simpl; unfold StepCnt.seq_sem.
    exists a1, a2, st3.
    tauto.
  + destruct H as [a H].
    unfold StepCnt.seq_sem in H.
    destruct H as [a1 [a2 [st3 [H1' [H2' Ha]]]]].
    assert (exists (t1 : Z), StepCnt.ceval c1 st1 t1 st3) as H1
      by (exists a1; exact H1').
    specialize (IHc1 st1 st3);
      destruct IHc1 as [IHc1' IHc1];
      specialize (IHc1 H1).
    assert (exists (t2 : Z), StepCnt.ceval c2 st3 t2 st2) as H2
      by (exists a2; exact H2').
    specialize (IHc2 st3 st2);
      destruct IHc2 as [IHc2' IHc2];
      specialize (IHc2 H2).
    clear H1' H2' H1 H2 Ha a a1 a2 IHc1' IHc2'.
    unfold Relation_Operators.concat.
    exists st3.
    tauto.
Qed.

Lemma bin_step_if_sem_equiv (c1 c2: com):
  bin_step_equiv (BinRel.ceval c1) (StepCnt.ceval c1) ->
  bin_step_equiv (BinRel.ceval c2) (StepCnt.ceval c2) ->
  (forall b,
    bin_step_equiv (BinRel.ceval (CIf b c1 c2)) (StepCnt.ceval (CIf b c1 c2))).
Proof.
  unfold bin_step_equiv.
  simpl.
  intros IHc1 IHc2 b st1 st2.
  split; intros.
  - unfold BinRel.if_sem in H.
    destruct H; destruct H as [st1' [HTest H]].
    (** 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2
        prove them respectively. *)
    + destruct HTest. subst st1'.
      specialize (IHc1 st1 st2);
        destruct IHc1 as [IHc1 IHc1'];
        specialize (IHc1 H);
        destruct IHc1 as [a IHc1].
      clear IHc1' IHc2.
      exists (a + 1).
      simpl. left. (* beval b st1 --> c1 *)
      exists 1, a, st1.
      unfold StepCnt.test_sem.
      firstorder.
    + destruct HTest. subst st1'.
      specialize (IHc2 st1 st2);
        destruct IHc2 as [IHc2 IHc2'];
        specialize (IHc2 H);
        destruct IHc2 as [a IHc2].
      clear IHc1 IHc2'.
      exists (a + 1).
      simpl. right. (* beval (! b) st1 --> c2 *)
      exists 1, a, st1.
      unfold StepCnt.test_sem.
      firstorder.
  - destruct H as [a H].
    unfold StepCnt.if_sem in H.
    (** 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2 *)
    (** These 'destruct' are just to split this 'ceval' into 2 hypothesis:
          one for 'beval b/(! b) st1', another for the execution of c1/c2.
        There are a lot of integers a_, standing for the number of steps in
          the execution process, which makes it looks complicated. But they
          are actually of no use in the proof, so we can clear them out. *)
    destruct H;
      destruct H as [a0 [a1 [st1' [HTest [HStep' Ha]]]]];
      destruct HTest as [Hst [Hb ?]];
      subst st1' a0 a.
    + assert (exists (t1 : Z), StepCnt.ceval c1 st1 t1 st2) as HStep
        by (exists a1; exact HStep').
      specialize (IHc1 st1 st2);
        destruct IHc1 as [IHc1' IHc1];
        specialize (IHc1 HStep).
      clear IHc1' IHc2 HStep' HStep.
      simpl. left. (* beval b st1 --> c1 *)
      exists st1.
      unfold Relation_Operators.test_rel.
      tauto.
    + assert (exists (t2 : Z), StepCnt.ceval c2 st1 t2 st2) as HStep
        by (exists a1; exact HStep').
      specialize (IHc2 st1 st2);
        destruct IHc2 as [IHc2' IHc2];
        specialize (IHc2 HStep).
      clear IHc1 IHc2' HStep' HStep a1.
      simpl. right. (* beval (! b) st1 --> c2 *)
      exists st1.
      unfold Relation_Operators.test_rel.
      tauto.
Qed.

Lemma bin_step_while_sem_equiv (c: com):
  bin_step_equiv (BinRel.ceval c) (StepCnt.ceval c) ->
  (forall b,
    bin_step_equiv (BinRel.ceval (CWhile b c)) (StepCnt.ceval (CWhile b c))).
Proof.
  unfold bin_step_equiv.
  simpl.
  intros IHc b st1 st2.
  split; intros.
  + unfold BinRel.loop_sem, Relation_Operators.omega_union in H.
    destruct H as [n H].
    (** As 'n' is unknown, prove this by another induction. *)
    revert st1 st2 H.
    induction n; intros.
    * destruct H as [Hst Hb].
      exists 1. (* In total 1 step *)
      simpl. exists O. (* In total 0 iters *)
      unfold StepCnt.iter_loop_body,
             StepCnt.test_sem.
      tauto.
    * simpl in H.
      unfold Relation_Operators.concat, Relation_Operators.test_rel in H.
      destruct H as [st1' [[Hst Hb] [st3 [H1 H2]]]].
      subst st1'.
      specialize (IHc st1 st3);
        destruct IHc as [IHc IHc'];
        specialize (IHc H1).
      destruct IHc as [ac IHc].
      specialize (IHn _ _ H2).
      destruct IHn as [an IHn].
      clear H1 H2 n.
      unfold StepCnt.loop_sem, StepCnt.omega_union_sem in IHn.
      (** Assume doing 'While b Do c EndWhile' takes [n_iter] iters from st3
          to st2.
          Known that 'ceval c st1 st3', and 'beval b st1', we can assert that
          it takes [n_iter + 1] iters in the process of 'While b Do c
          EndWhile' from st1 to st2. *)
      destruct IHn as [n_iter IHn].
      exists (ac + 1 + an).
      simpl.
      unfold StepCnt.loop_sem, StepCnt.omega_union_sem.
      exists (S n_iter).
      simpl.
      unfold StepCnt.test_sem, StepCnt.seq_sem.
      exists 1, (ac + an), st1.
      split; [tauto | split; [| lia] ].
      exists ac, an, st3.
      tauto.
  + destruct H as [a H].
    unfold StepCnt.loop_sem, StepCnt.omega_union_sem in H.
    destruct H as [n H].
    revert a st1 st2 H.
    induction n; intros.
    * inversion H.
      exists O. (** In total 0 iters *)
      unfold BinRel.iter_loop_body,
             Relation_Operators.test_rel.
      tauto.
    * destruct H as [a0 [a1 [st1' [HTest H]]]].
      destruct HTest as [Hst [Hb Ha0]].
      destruct H as [[ac [an [st3 [Hc' [Hn Ha2]]]]] Ha1].
      subst st1' a0 a1 a.
      assert (exists (t : Z), StepCnt.ceval c st1 t st3) as Hc
        by (exists ac; exact Hc').
      specialize (IHc st1 st3);
        destruct IHc as [IHc' IHc];
        specialize (IHc Hc).
      specialize (IHn _ _ _ Hn).
      clear Hc Hn Hc' ac an n.
      pose proof BinRel_ceval_fold_while _ _ _ _ _ Hb IHc IHn.
      exact H.
Qed.

End BinStepEquiv.

(** Following module is to prove that every element in the recursive definition
    of "BinRel.ceval" and "Trace.ceval" is equivalent. *)
Module BinTraceEquiv.

Lemma bin_trace_skip_sem_equiv:
  bin_trace_equiv (BinRel.ceval CSkip) (Trace.ceval CSkip).
Proof.
  unfold bin_trace_equiv.
  simpl.
  split; intros.
  + exists nil.
    firstorder.
  + destruct H.
    firstorder.
Qed.

Lemma bin_trace_asgn_sem_equiv:
  forall (X: var) (E: aexp),
  bin_trace_equiv (BinRel.ceval (CAss X E)) (Trace.ceval (CAss X E)).
Proof.
  unfold bin_step_equiv.
  simpl.
  split; intros.
  + exists (st2 :: nil).
    firstorder.
  + destruct H.
    firstorder.
Qed.

Lemma bin_trace_seq_sem_equiv  (c1 c2: com):
  bin_trace_equiv (BinRel.ceval c1) (Trace.ceval c1) ->
  bin_trace_equiv (BinRel.ceval c2) (Trace.ceval c2) ->
  bin_trace_equiv (BinRel.ceval (CSeq c1 c2)) (Trace.ceval (CSeq c1 c2)).
Proof.
  unfold bin_trace_equiv.
  simpl.
  intros IHc1 IHc2 st1 st2.
  split; intros.
  + inversion H as [st3 H0]. destruct H0 as [H1 H2].
    specialize (IHc1 st1 st3);
      destruct IHc1 as [IHc1 IHc1'];
      specialize (IHc1 H1);
      destruct IHc1 as [l1 IHc1].
    specialize (IHc2 st3 st2);
      destruct IHc2 as [IHc2 IHc2'];
      specialize (IHc2 H2);
      destruct IHc2 as [l2 IHc2].
    exists (l1 ++ l2).
    simpl; unfold Trace.seq_sem.
    exists l1, l2, st3.
    tauto.
  + destruct H as [l H].
    unfold Trace.seq_sem in H.
    destruct H as [l1 [l2 [st3 [H1' [H2' Hl]]]]].
    assert (exists (t1 : list state), Trace.ceval c1 st1 t1 st3) as H1
      by (exists l1; exact H1').
    specialize (IHc1 st1 st3);
      destruct IHc1 as [IHc1' IHc1];
      specialize (IHc1 H1).
    assert (exists (t2 : list state), Trace.ceval c2 st3 t2 st2) as H2
      by (exists l2; exact H2').
    specialize (IHc2 st3 st2);
      destruct IHc2 as [IHc2' IHc2];
      specialize (IHc2 H2).
    clear H1' H2' H1 H2 Hl l l1 l2 IHc1' IHc2'.
    unfold Relation_Operators.concat.
    exists st3.
    tauto.
Qed.

Lemma bin_trace_if_sem_equiv (c1 c2: com):
  bin_trace_equiv (BinRel.ceval c1) (Trace.ceval c1) ->
  bin_trace_equiv (BinRel.ceval c2) (Trace.ceval c2) ->
  (forall b,
    bin_trace_equiv (BinRel.ceval (CIf b c1 c2)) (Trace.ceval (CIf b c1 c2))).
Proof.
  unfold bin_trace_equiv.
  simpl.
  intros IHc1 IHc2 b st1 st2.
  split; intros.
  - unfold BinRel.if_sem in H.
    destruct H; destruct H as [st1' [HTest H]].
    (** 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2
        prove them respectively. *)
    + destruct HTest; subst st1'.
      specialize (IHc1 st1 st2);
        destruct IHc1 as [IHc1 IHc1'];
        specialize (IHc1 H);
        destruct IHc1 as [l IHc1].
      clear IHc1' IHc2.
      exists ((st1 :: nil) ++ l).
      simpl. left. (* beval b st1 --> c1 *)
      exists (st1 :: nil), l, st1.
      unfold Trace.test_sem.
      firstorder.
    + destruct HTest; subst st1'.
      specialize (IHc2 st1 st2);
        destruct IHc2 as [IHc2 IHc2'];
        specialize (IHc2 H);
        destruct IHc2 as [l IHc2].
      clear IHc1 IHc2'.
      exists ((st1 :: nil) ++ l).
      simpl. right. (* beval (! b) st1 --> c2 *)
      exists (st1 :: nil), l, st1.
      unfold Trace.test_sem.
      firstorder.
  - destruct H as [l H].
    unfold StepCnt.if_sem in H.
    (** 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2 *)
    (** These 'destruct' are just to split this 'ceval' into 2 hypothesis:
          one for 'beval b/(! b) st1', another for the execution of c1/c2.
        There are a lot of integers a_, standing for the number of steps in
          the execution process, which makes it looks complicated. But they
          are actually of no use in the proof, so we can clear them out. *)
    destruct H;
      destruct H as [l0 [l1 [st1' [HTest [HStep' Hl]]]]];
      destruct HTest as [Hst [Hb ?]];
      subst st1' l0 l.
    + assert (exists (t1 : list state), Trace.ceval c1 st1 t1 st2) as HStep
        by (exists l1; exact HStep').
      specialize (IHc1 st1 st2);
        destruct IHc1 as [IHc1' IHc1];
        specialize (IHc1 HStep).
      clear IHc1' IHc2 HStep' HStep l1.
      simpl. left. (* beval b st1 --> c1 *)
      exists st1.
      unfold Relation_Operators.test_rel.
      tauto.
    + assert (exists (t2 : list state), Trace.ceval c2 st1 t2 st2) as HStep
        by (exists l1; exact HStep').
      specialize (IHc2 st1 st2);
        destruct IHc2 as [IHc2' IHc2];
        specialize (IHc2 HStep).
      clear IHc1 IHc2' HStep' HStep l1.
      simpl. right. (* beval (! b) st1 --> c2 *)
      exists st1.
      unfold Relation_Operators.test_rel.
      tauto.
Qed.

Lemma bin_trace_while_sem_equiv (c: com):
  bin_trace_equiv (BinRel.ceval c) (Trace.ceval c) ->
  (forall b,
    bin_trace_equiv (BinRel.ceval (CWhile b c)) (Trace.ceval (CWhile b c))).
Proof.
  unfold bin_trace_equiv.
  simpl.
  intros IHc b st1 st2.
  split; intros.
  + unfold BinRel.loop_sem, Relation_Operators.omega_union in H.
    destruct H as [n H].
    (** As 'n' is unknown, prove this by another induction. *)
    revert st1 st2 H.
    induction n; intros.
    * destruct H as [Hst Hb].
      exists (st1 :: nil). (* In total 1 trace *)
      simpl. exists O. (* In total 0 iters *)
      unfold Trace.iter_loop_body,
             Trace.test_sem.
      tauto.
    * simpl in H.
      unfold Relation_Operators.concat, Relation_Operators.test_rel in H.
      destruct H as [st1' [[Hst Hb] [st3 [H1 H2]]]].
      subst st1'.
      specialize (IHc st1 st3);
        destruct IHc as [IHc IHc'];
        specialize (IHc H1).
      destruct IHc as [lc IHc].
      specialize (IHn _ _ H2).
      destruct IHn as [ln IHn].
      clear H1 H2 n IHc'.
      unfold Trace.loop_sem, Trace.omega_union_sem in IHn.
      (** Assume doing 'While b Do c EndWhile' takes [n_iter] iters from st3
          to st2.
          Known that 'ceval c st1 st3', and 'beval b st1', we can assert that
          it takes [n_iter + 1] iters in the process of 'While b Do c
          EndWhile' from st1 to st2. *)
      destruct IHn as [n_iter IHn].
      exists ((st1 :: nil) ++ lc ++ ln).
      simpl.
      unfold Trace.loop_sem, Trace.omega_union_sem.
      exists (S n_iter).
      simpl.
      unfold Trace.test_sem, Trace.seq_sem.
      exists (st1 :: nil), (lc ++ ln), st1.
      split; [tauto | split; [| firstorder] ].
      exists lc, ln, st3.
      tauto.
  + destruct H as [l H].
    unfold StepCnt.loop_sem, StepCnt.omega_union_sem in H.
    destruct H as [n H].
    revert l st1 st2 H.
    induction n; intros.
    * inversion H.
      exists O. (** In total 0 iters *)
      unfold BinRel.iter_loop_body,
             Relation_Operators.test_rel.
      tauto.
    * destruct H as [l0 [l1 [st1' [HTest H]]]].
      destruct HTest as [Hst [Hl0 Hb]].
      destruct H as [[lc [ln [st3 [Hc' [Hn Hl2]]]]] Hl1].
      subst st1' l0 l1 l.
      assert (exists (t : list state), Trace.ceval c st1 t st3) as Hc
        by (exists lc; exact Hc').
      specialize (IHc st1 st3);
        destruct IHc as [IHc' IHc];
        specialize (IHc Hc).
      specialize (IHn _ _ _ Hn).
      clear Hc Hn Hc' lc ln n IHc'.
      pose proof BinRel_ceval_fold_while _ _ _ _ _ Hb IHc IHn.
      exact H.
Qed.

End BinTraceEquiv.