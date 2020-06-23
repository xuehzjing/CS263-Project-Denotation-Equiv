Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.DenotationalSemantics.

(** In this task, you should first prove a general theorem which can be used to
    prove an equivalence between two recursively defined semantics, and another
    general theorem which can be used to prove an equivalence between a
    recursively defined program semantics and a small step semantics.

    Then, you need to prove the equivalence among three denotational program
    semantics and a small step semantics. *)

<<<<<<< HEAD
=======
(* Some try before the general theorem *)
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999

Definition Bin_Ter_sem_equiv {M: Type}
                             (X : state -> state -> Prop)
                             (Y : state -> M -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists z, Y st1 z st2).

Definition sem_equiv {X Y: Type}
                     (ceval_X: com -> X)
                     (ceval_Y: com -> Y)
<<<<<<< HEAD
                     (EQ: X -> Y -> Prop) : Prop :=
  forall c, EQ (ceval_X c) (ceval_Y c).

Definition skip_sem_equiv {X Y: Type}
                          (S1 : semantic X)
                          (S2 : semantic Y)
                          (EQ: X -> Y -> Prop) : Prop :=
  EQ (semantic_skip S1) (semantic_skip S2).

Definition asgn_sem_equiv {X Y: Type}
                          (S1 : semantic X)
                          (S2 : semantic Y)
                          (EQ: X -> Y -> Prop) : Prop :=
  forall X E,
  EQ (semantic_asgn S1 X E) (semantic_asgn S2 X E).

Definition seq_sem_equiv {X Y: Type}
                         (S1 : semantic X)
                         (S2 : semantic Y)
                         (EQ: X -> Y -> Prop) : Prop :=
  forall c1 c2,
  EQ (ceval_by_sem S1 c1) (ceval_by_sem S2 c1) ->
  EQ (ceval_by_sem S1 c2) (ceval_by_sem S2 c2) ->
  EQ
    (semantic_seq S1 (ceval_by_sem S1 c1) (ceval_by_sem S1 c2))
    (semantic_seq S2 (ceval_by_sem S2 c1) (ceval_by_sem S2 c2)).

Definition if_sem_equiv {X Y: Type}
                        (S1 : semantic X)
                        (S2 : semantic Y)
                        (EQ: X -> Y -> Prop) : Prop :=
  forall b c1 c2,
  EQ (ceval_by_sem S1 c1) (ceval_by_sem S2 c1) ->
  EQ (ceval_by_sem S1 c2) (ceval_by_sem S2 c2) ->
  EQ
    (semantic_if S1 b (ceval_by_sem S1 c1) (ceval_by_sem S1 c2))
    (semantic_if S2 b (ceval_by_sem S2 c1) (ceval_by_sem S2 c2)).

Definition loop_sem_equiv {X Y: Type}
                          (S1 : semantic X)
                          (S2 : semantic Y)
                          (EQ: X -> Y -> Prop) : Prop :=
  forall b c,
  EQ (ceval_by_sem S1 c) (ceval_by_sem S2 c) ->
  EQ
    (semantic_loop S1 b (ceval_by_sem S1 c))
    (semantic_loop S2 b (ceval_by_sem S2 c)).

(* General Theorem for equivalence between two recursively defined semantics *)

Theorem command_equiv__sem_equiv:
  forall {X Y: Type}
         (S1 : semantic X)
         (S2 : semantic Y)
         (EQ : X -> Y -> Prop),
  skip_sem_equiv S1 S2 EQ ->
  asgn_sem_equiv S1 S2 EQ ->
  seq_sem_equiv  S1 S2 EQ ->
  if_sem_equiv   S1 S2 EQ ->
  loop_sem_equiv S1 S2 EQ ->
  sem_equiv (ceval_by_sem S1) (ceval_by_sem S2) EQ.
Proof.
  unfold skip_sem_equiv,
         asgn_sem_equiv,
         seq_sem_equiv,
         if_sem_equiv,
         loop_sem_equiv,
         sem_equiv.
  intros. induction c; intros; simpl.
  - apply H.
  - apply H0.
  - apply H1.
    + intros. apply IHc1.
    + intros. apply IHc2.
  - apply H2.
    + intros. apply IHc1.
    + intros. apply IHc2.
  - apply H3.
    + intros. apply IHc.
Qed.

Theorem Bin_Step_skip_sem_equiv:
  skip_sem_equiv (BinRel.sem) (StepCnt.sem) Bin_Ter_sem_equiv.
Proof.
  unfold skip_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.skip_sem, StepCnt.skip_sem.
  split.
  - intros. exists 0. tauto.
=======
                     (RXY: X -> Y -> Prop) : Prop :=
  forall c, RXY (ceval_X c) (ceval_Y c).

Definition Bin_Ter_skip_sem_equiv {M: Type}
  (SBin : semantic (state -> state -> Prop))
  (STer : semantic (state -> M -> state -> Prop)) : Prop :=
  Bin_Ter_sem_equiv (semantic_skip SBin) (semantic_skip STer).

Definition Bin_Ter_asgn_sem_equiv {M: Type}
  (SBin : semantic (state -> state -> Prop))
  (STer : semantic (state -> M -> state -> Prop)) : Prop :=
  forall X E,
  Bin_Ter_sem_equiv (semantic_asgn SBin X E) (semantic_asgn STer X E).

Definition Bin_Ter_seq_sem_equiv {M: Type}
  (SBin : semantic (state -> state -> Prop))
  (STer : semantic (state -> M -> state -> Prop)) : Prop :=
  forall c1 c2,
  Bin_Ter_sem_equiv (ceval_by_sem SBin c1) (ceval_by_sem STer c1) ->
  Bin_Ter_sem_equiv (ceval_by_sem SBin c2) (ceval_by_sem STer c2) ->
  Bin_Ter_sem_equiv
    (semantic_seq SBin (ceval_by_sem SBin c1) (ceval_by_sem SBin c2))
    (semantic_seq STer (ceval_by_sem STer c1) (ceval_by_sem STer c2)).

Definition Bin_Ter_if_sem_equiv {M: Type}
  (SBin : semantic (state -> state -> Prop))
  (STer : semantic (state -> M -> state -> Prop)) : Prop :=
  forall b c1 c2,
  Bin_Ter_sem_equiv (ceval_by_sem SBin c1) (ceval_by_sem STer c1) ->
  Bin_Ter_sem_equiv (ceval_by_sem SBin c2) (ceval_by_sem STer c2) ->
  Bin_Ter_sem_equiv
    (semantic_if SBin b (ceval_by_sem SBin c1) (ceval_by_sem SBin c2))
    (semantic_if STer b (ceval_by_sem STer c1) (ceval_by_sem STer c2)).

Definition Bin_Ter_loop_sem_equiv {M: Type}
  (SBin : semantic (state -> state -> Prop))
  (STer : semantic (state -> M -> state -> Prop)) : Prop :=
  forall b c,
  Bin_Ter_sem_equiv (ceval_by_sem SBin c) (ceval_by_sem STer c) ->
  Bin_Ter_sem_equiv
    (semantic_loop SBin b (ceval_by_sem SBin c))
    (semantic_loop STer b (ceval_by_sem STer c)).

Theorem Bin_Ter_skip_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_skip_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_skip_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.skip_sem, TerSem.skip_sem.
  split.
  - intros. exists (MP_zero mp). tauto.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
  - intros [z [H1 H2]].
    tauto.
Qed.

<<<<<<< HEAD
Theorem Bin_Step_asgn_sem_equiv:
  asgn_sem_equiv (BinRel.sem) (StepCnt.sem) Bin_Ter_sem_equiv.
Proof.
  unfold asgn_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.asgn_sem,StepCnt.asgn_sem.
  split.
  - intros [H1 H2]. exists 1.
    split. { tauto. }
    intros. split. { apply (H2 _ H). }
    tauto.
  - intros [z [H1 H2]].
    split. { tauto. }
    intros. {apply (H2 _ H). }
Qed.

Theorem Bin_Step_seq_sem_equiv:
  seq_sem_equiv (BinRel.sem) (StepCnt.sem) Bin_Ter_sem_equiv.
Proof.
  unfold seq_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.seq_sem, StepCnt.seq_sem, Relation_Operators.concat.
=======
Theorem Bin_Ter_asgn_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_asgn_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_asgn_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.asgn_sem,TerSem.asgn_sem.
  split.
  - intros [H1 H2]. exists (MP_one mp st1 st2).
    split. { tauto. }
    intros. split. { apply H2. }
    tauto.
  - intros [z [H1 H2]].
    split. { tauto. }
    intros. { apply H2,H. }
Qed.

Theorem Bin_Ter_seq_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_seq_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_seq_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.seq_sem, Relation_Operators.concat.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
  split.
  - intros [st3 [H1 H2]].
    destruct (H st1 st3) as [H1' H1''].
    destruct (H1' H1) as [z1 HE1].
    destruct (H0 st3 st2) as [H2' H2''].
    destruct (H2' H2) as [z2 HE2].
<<<<<<< HEAD
    exists (z1 + z2), z1, z2, st3.
=======
    exists (MP_add mp z1 z2), z1, z2, st3.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
    tauto.
  - intros [z [z1 [z2 [st3 [H1 [H2 Hz]]]]]].
    destruct (H st1 st3) as [H1' H1''].
    destruct (H0 st3 st2) as [H2' H2''].
    exists st3.
    split.
    + apply H1''.
      exists z1. apply H1.
    + apply H2''.
      exists z2. apply H2.
Qed.

<<<<<<< HEAD
Theorem Bin_Step_if_sem_equiv:
  if_sem_equiv (BinRel.sem) (StepCnt.sem) Bin_Ter_sem_equiv.
Proof.
  unfold if_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold semantic_if, BinRel.if_sem, StepCnt.if_sem.
=======
Theorem Bin_Ter_if_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_if_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_if_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold semantic_if, BinRel.if_sem, TerSem.if_sem.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
  unfold Relation_Operators.union,
         Relation_Operators.concat,
         Relation_Operators.test_rel.
  split; intros.
  + destruct H1.
    - destruct H1 as [st3 [[Hst Hb] H1]]. subst st3.
      destruct (H st1 st2) as [H' H''].
      destruct (H' H1) as [zc Hc].
<<<<<<< HEAD
      exists (zc + 1). left.
      exists 1, zc, st1.
      repeat split.
      * unfold StepCnt.test_sem; tauto.
      * exact Hc.
      * lia.
    - destruct H1 as [st3 [[Hst Hb] H1]]. subst st3.
      destruct (H0 st1 st2) as [H' H''].
      destruct (H' H1) as [zc Hc].
      exists (zc + 1). right.
      exists 1, zc, st1.
      repeat split.
      * unfold StepCnt.test_sem; tauto.
      * exact Hc.
      * lia.
  + destruct H1 as [z H1];
      destruct H1;
      unfold StepCnt.seq_sem in H1;
=======
      exists (MP_add mp (MP_one mp st1 st1) zc). left.
      exists (MP_one mp st1 st1), zc, st1.
      repeat split.
      * tauto.
      * exact Hc.
    - destruct H1 as [st3 [[Hst Hb] H1]]. subst st3.
      destruct (H0 st1 st2) as [H' H''].
      destruct (H' H1) as [zc Hc].
      exists (MP_add mp (MP_one mp st1 st1) zc). right.
      exists (MP_one mp st1 st1), zc, st1.
      repeat split.
      * tauto.
      * exact Hc.
  + destruct H1 as [z H1];
      destruct H1;
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
      destruct H1 as [z1 [z2 [st3 [[Hst [Hb ?]] [Hc Hz]]]]];
      subst st3 z1 z.
    - destruct (H st1 st2) as [H' H''].
      left. exists st1.
      repeat split.
      * exact Hb.
      * apply H''.
        exists z2. exact Hc.
    - destruct (H0 st1 st2) as [H' H''].
      right. exists st1.
      repeat split.
      * exact Hb.
      * apply H''.
        exists z2. exact Hc.
Qed.

<<<<<<< HEAD
Theorem Bin_Step_loop_sem_equiv:
  loop_sem_equiv (BinRel.sem) (StepCnt.sem) Bin_Ter_sem_equiv.
Proof.
  unfold loop_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.loop_sem, Relation_Operators.omega_union.
  unfold StepCnt.loop_sem, StepCnt.omega_union_sem.
=======
Theorem Bin_Ter_loop_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_loop_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_loop_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.loop_sem, Relation_Operators.omega_union.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
  split; intros.
  + destruct H0 as [n H0].
    revert st1 st2 H0.
    induction n; intros; simpl in H0.
<<<<<<< HEAD
    - exists 1, O. simpl.
      unfold Relation_Operators.test_rel in H0.
      unfold StepCnt.test_sem.
=======
    - exists (MP_one mp st1 st2), O. simpl.
      unfold Relation_Operators.test_rel in H0.
      unfold TerSem.test_sem.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
      tauto.
    - unfold Relation_Operators.concat, Relation_Operators.test_rel in H0.
      destruct H0 as [st1' [[Hst Hb] [st3 [H1 H2]]]]. subst st1'.
      destruct (IHn _ _ H2) as [zn [n_iter Hn]].
      destruct (H st1 st3) as [H' H''].
      destruct (H' H1) as [zc Hc].
<<<<<<< HEAD
      exists (1 + (zc + zn)), (S n_iter).
      simpl. unfold StepCnt.seq_sem.
      exists 1, (zc + zn), st1.
=======
      exists (MP_add mp (MP_one mp st1 st1) (MP_add mp zc zn)), (S n_iter).
      simpl. unfold TerSem.seq_sem.
      exists (MP_one mp st1 st1), (MP_add mp zc zn), st1.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
      repeat split.
      * exact Hb.
      * exists zc, zn, st3.
        repeat split; [exact Hc | exact Hn].
  + destruct H0 as [z [n H0]].
    revert z st1 st2 H0.
    induction n; intros; simpl in H0.
    - exists O. simpl.
<<<<<<< HEAD
      unfold StepCnt.test_sem in H0.
      unfold Relation_Operators.test_rel.
      tauto.
    - unfold StepCnt.seq_sem, StepCnt.test_sem in H0.
      destruct H0 as [z0 [z1 [st1' [[Hst [Hb Ha0]] H0]]]].
=======
      unfold TerSem.test_sem in H0.
      unfold Relation_Operators.test_rel.
      tauto.
    - destruct H0 as [z0 [z1 [st1' [[Hst [Hb Ha0]] H0]]]].
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
      destruct H0 as [[zc [zn [st3 [Hz' [Hn' Hz2]]]]] Hz1].
      subst st1' z0 z1 z.
      destruct (IHn zn st3 st2 Hn') as [n_iter Hn].
      destruct (H st1 st3) as [H' H''].
      exists (S n_iter). simpl.
      unfold Relation_Operators.concat, Relation_Operators.test_rel.
      exists st1. repeat split. { exact Hb. }
      exists st3. split.
      * apply H''. exists zc. exact Hz'.
      * exact Hn.
Qed.

<<<<<<< HEAD
Theorem Bin_Trace_skip_sem_equiv:
  skip_sem_equiv (BinRel.sem) (Trace.sem) Bin_Ter_sem_equiv.
Proof.
  unfold skip_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.skip_sem, Trace.skip_sem.
  split.
  - intros. exists nil. tauto.
  - intros [l [H1 H2]].
    tauto.
Qed.

Theorem Bin_Trace_asgn_sem_equiv:
  asgn_sem_equiv (BinRel.sem) (Trace.sem) Bin_Ter_sem_equiv.
Proof.
  unfold asgn_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.asgn_sem, Trace.asgn_sem.
  split.
  - intros [H1 H2]. exists (st2 :: nil).
    split. { tauto. }
    intros. split. { apply (H2 _ H). }
    tauto.
  - intros [l [H1 H2]].
    split. { tauto. }
    intros. {apply (H2 _ H). }
Qed.

Theorem Bin_Trace_seq_sem_equiv:
  seq_sem_equiv (BinRel.sem) (Trace.sem) Bin_Ter_sem_equiv.
Proof.
  unfold seq_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.seq_sem, Trace.seq_sem, Relation_Operators.concat.
  split.
  - intros [st3 [H1 H2]].
    destruct (H st1 st3) as [H1' H1''].
    destruct (H1' H1) as [l1 HE1].
    destruct (H0 st3 st2) as [H2' H2''].
    destruct (H2' H2) as [l2 HE2].
    exists (l1 ++ l2), l1, l2, st3.
    tauto.
  - intros [l [l1 [l2 [st3 [H1 [H2 Hl]]]]]].
    destruct (H st1 st3) as [H1' H1''].
    destruct (H0 st3 st2) as [H2' H2''].
    exists st3.
    split.
    + apply H1''.
      exists l1. apply H1.
    + apply H2''.
      exists l2. apply H2.
Qed.

Theorem Bin_Trace_if_sem_equiv:
  if_sem_equiv (BinRel.sem) (Trace.sem) Bin_Ter_sem_equiv.
Proof.
  unfold if_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold semantic_if, BinRel.if_sem, Trace.if_sem.
  unfold Relation_Operators.union,
         Relation_Operators.concat,
         Relation_Operators.test_rel.
  split; intros.
  + destruct H1.
    - destruct H1 as [st3 [[Hst Hb] H1]]. subst st3.
      destruct (H st1 st2) as [H' H''].
      destruct (H' H1) as [lc Hc].
      exists ((st1 :: nil) ++ lc). left.
      exists (st1 :: nil), lc, st1.
      repeat split.
      * unfold Trace.test_sem; tauto.
      * exact Hc.
    - destruct H1 as [st3 [[Hst Hb] H1]]. subst st3.
      destruct (H0 st1 st2) as [H' H''].
      destruct (H' H1) as [lc Hc].
      exists ((st1 :: nil) ++ lc). right.
      exists (st1 :: nil), lc, st1.
      repeat split.
      * unfold Trace.test_sem; tauto.
      * exact Hc.
  + destruct H1 as [l H1];
      destruct H1;
      unfold Trace.seq_sem in H1;
      destruct H1 as [l1 [l2 [st3 [[Hst [? Hb]] [Hc Hl]]]]];
      subst st3 l1 l.
    - destruct (H st1 st2) as [H' H''].
      left. exists st1.
      repeat split.
      * exact Hb.
      * apply H''. exists l2. exact Hc.
    - destruct (H0 st1 st2) as [H' H''].
      right. exists st1.
      repeat split.
      * exact Hb.
      * apply H''. exists l2. exact Hc.
Qed.

Theorem Bin_Trace_loop_sem_equiv:
  loop_sem_equiv (BinRel.sem) (Trace.sem) Bin_Ter_sem_equiv.
Proof.
  unfold loop_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.loop_sem, Relation_Operators.omega_union.
  unfold Trace.loop_sem, Trace.omega_union_sem.
  split; intros.
  + destruct H0 as [n H0].
    revert st1 st2 H0.
    induction n; intros; simpl in H0.
    - exists (st1 :: nil), O. simpl.
      unfold Relation_Operators.test_rel in H0.
      unfold Trace.test_sem.
      tauto.
    - unfold Relation_Operators.concat, Relation_Operators.test_rel in H0.
      destruct H0 as [st1' [[Hst Hb] [st3 [H1 H2]]]]. subst st1'.
      destruct (IHn _ _ H2) as [ln [n_iter Hn]].
      destruct (H st1 st3) as [H' H''].
      destruct (H' H1) as [lc Hc].
      exists ((st1 :: nil) ++ (lc ++ ln)), (S n_iter).
      simpl. unfold Trace.seq_sem.
      exists (st1 :: nil), (lc ++ ln), st1.
      repeat split.
      * exact Hb.
      * exists lc, ln, st3.
        repeat split; [exact Hc | exact Hn].
  + destruct H0 as [l [n H0]].
    revert l st1 st2 H0.
    induction n; intros; simpl in H0.
    - exists O. simpl.
      unfold Trace.test_sem in H0.
      unfold Relation_Operators.test_rel.
      tauto.
    - unfold Trace.seq_sem, Trace.test_sem in H0.
      destruct H0 as [l0 [l1 [st1' [[Hst [Ha0 Hb]] H0]]]].
      destruct H0 as [[lc [ln [st3 [Hl' [Hn' Hl2]]]]] Hl1].
      subst st1' l0 l1 l.
      destruct (IHn ln st3 st2 Hn') as [n_iter Hn].
      destruct (H st1 st3) as [H' H''].
      exists (S n_iter). simpl.
      unfold Relation_Operators.concat, Relation_Operators.test_rel.
      exists st1. repeat split. { exact Hb. }
      exists st3. split.
      * apply H''. exists lc. exact Hl'.
      * exact Hn.
=======
Theorem command_equiv__sem_equiv:
  forall (M: Type)
    (SBin : semantic (state -> state -> Prop))
    (STer : semantic (state -> M -> state -> Prop)),
  Bin_Ter_skip_sem_equiv SBin STer ->
  Bin_Ter_asgn_sem_equiv SBin STer ->
  Bin_Ter_seq_sem_equiv SBin STer ->
  Bin_Ter_if_sem_equiv SBin STer ->
  Bin_Ter_loop_sem_equiv SBin STer ->
  sem_equiv (ceval_by_sem SBin) (ceval_by_sem STer) (Bin_Ter_sem_equiv).
Proof.
  unfold Bin_Ter_skip_sem_equiv,
         Bin_Ter_asgn_sem_equiv,
         Bin_Ter_seq_sem_equiv,
         Bin_Ter_if_sem_equiv,
         Bin_Ter_loop_sem_equiv,
         sem_equiv,Bin_Ter_sem_equiv.
  intros. revert st1 st2. induction c; intros; simpl.
  - apply H.
  - apply H0.
  - apply H1.
    + intros. apply IHc1.
    + intros. apply IHc2.
  - apply H2.
    + intros. apply IHc1.
    + intros. apply IHc2.
  - apply H3.
    + intros. apply IHc.
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
Qed.

Theorem Bin_Step_equiv:
  sem_equiv (BinRel.ceval) (StepCnt.ceval) (Bin_Ter_sem_equiv).
Proof.
<<<<<<< HEAD
  apply (command_equiv__sem_equiv
         BinRel.sem StepCnt.sem Bin_Ter_sem_equiv
         Bin_Step_skip_sem_equiv
         Bin_Step_asgn_sem_equiv
         Bin_Step_seq_sem_equiv
         Bin_Step_if_sem_equiv
         Bin_Step_loop_sem_equiv).
=======
  apply (command_equiv__sem_equiv _ _ _
    (Bin_Ter_skip_sem_equiv_true _)
    (Bin_Ter_asgn_sem_equiv_true _)
    (Bin_Ter_seq_sem_equiv_true  _)
    (Bin_Ter_if_sem_equiv_true   _)
    (Bin_Ter_loop_sem_equiv_true _)).
>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
Qed.

Theorem Bin_Trace_equiv:
  sem_equiv (BinRel.ceval) (Trace.ceval) (Bin_Ter_sem_equiv).
Proof.
<<<<<<< HEAD
  apply (command_equiv__sem_equiv
         BinRel.sem Trace.sem Bin_Ter_sem_equiv
         Bin_Trace_skip_sem_equiv
         Bin_Trace_asgn_sem_equiv
         Bin_Trace_seq_sem_equiv
         Bin_Trace_if_sem_equiv
         Bin_Trace_loop_sem_equiv).
Qed.


(* General Theorem for equivalence between a denotational semantics and small step semantics. *)

Theorem semantic_equiv_com: forall c st1 st2,
  multi_cstep (c, st1) (CSkip, st2) <-> BinRel.ceval c st1 st2.
Admitted.

Theorem semantic_equiv_BinRel__semantic_equiv_com:
  forall (M: Type) (ceval': com -> state -> M -> state -> Prop),
    sem_equiv (BinRel.ceval) (ceval') (Bin_Ter_sem_equiv) ->
  forall c st1 st2,
    multi_cstep (c, st1) (CSkip, st2) <-> exists x, ceval' c st1 x st2.
Proof.
  intros.
  rewrite semantic_equiv_com.
  apply H.
Qed.

Theorem Step_Small_equiv:
  forall c st1 st2,
    multi_cstep (c, st1) (CSkip, st2) <-> exists z, StepCnt.ceval c st1 z st2.
Proof.
  apply semantic_equiv_BinRel__semantic_equiv_com.
  apply Bin_Step_equiv.
Qed.

Theorem Trace_Small_equiv:
  forall c st1 st2,
    multi_cstep (c, st1) (CSkip, st2) <-> exists l, Trace.ceval c st1 l st2.
Proof.
  apply semantic_equiv_BinRel__semantic_equiv_com.
  apply Bin_Trace_equiv.
Qed.
=======
  apply (command_equiv__sem_equiv _ _ _
    (Bin_Ter_skip_sem_equiv_true _)
    (Bin_Ter_asgn_sem_equiv_true _)
    (Bin_Ter_seq_sem_equiv_true  _)
    (Bin_Ter_if_sem_equiv_true   _)
    (Bin_Ter_loop_sem_equiv_true _)).
Qed.

(* General Theorem for equivalence between two recursively defined semantics *)

>>>>>>> c5f618c7f1e5ba9c8f15ceb3b829fe36b2e40999
