Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.DenotationalSemantics.

(** In this task, you should first prove a general theorem which can be used to
    prove an equivalence between two recursively defined semantics, and another
    general theorem which can be used to prove an equivalence between a
    recursively defined program semantics and a small step semantics.

    Then, you need to prove the equivalence among three denotational program
    semantics and a small step semantics. *)

Definition Bin_Ter_sem_equiv {M: Type}
                             (X : state -> state -> Prop)
                             (Y : state -> M -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists z, Y st1 z st2).

Definition sem_equiv {X Y: Type}
                     (ceval_X: com -> X)
                     (ceval_Y: com -> Y)
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
  - intros [z [H1 H2]].
    tauto.
Qed.

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
  split.
  - intros [st3 [H1 H2]].
    destruct (H st1 st3) as [H1' H1''].
    destruct (H1' H1) as [z1 HE1].
    destruct (H0 st3 st2) as [H2' H2''].
    destruct (H2' H2) as [z2 HE2].
    exists (MP_add mp z1 z2), z1, z2, st3.
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

Theorem Bin_Ter_if_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_if_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_if_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold semantic_if, BinRel.if_sem, TerSem.if_sem.
  unfold Relation_Operators.union,
         Relation_Operators.concat,
         Relation_Operators.test_rel.
  split; intros.
  + destruct H1.
    - destruct H1 as [st3 [[Hst Hb] H1]]. subst st3.
      destruct (H st1 st2) as [H' H''].
      destruct (H' H1) as [zc Hc].
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

Theorem Bin_Ter_loop_sem_equiv_true:
  forall {T: Type} (mp: mid_param state T),
  Bin_Ter_loop_sem_equiv (BinRel.sem) (TerSem.sem mp).
Proof.
  intros.
  unfold Bin_Ter_loop_sem_equiv. simpl.
  unfold Bin_Ter_sem_equiv. intros.
  unfold BinRel.loop_sem, Relation_Operators.omega_union.
  split; intros.
  + destruct H0 as [n H0].
    revert st1 st2 H0.
    induction n; intros; simpl in H0.
    - exists (MP_one mp st1 st2), O. simpl.
      unfold Relation_Operators.test_rel in H0.
      unfold TerSem.test_sem.
      tauto.
    - unfold Relation_Operators.concat, Relation_Operators.test_rel in H0.
      destruct H0 as [st1' [[Hst Hb] [st3 [H1 H2]]]]. subst st1'.
      destruct (IHn _ _ H2) as [zn [n_iter Hn]].
      destruct (H st1 st3) as [H' H''].
      destruct (H' H1) as [zc Hc].
      exists (MP_add mp (MP_one mp st1 st1) (MP_add mp zc zn)), (S n_iter).
      simpl. unfold TerSem.seq_sem.
      exists (MP_one mp st1 st1), (MP_add mp zc zn), st1.
      repeat split.
      * exact Hb.
      * exists zc, zn, st3.
        repeat split; [exact Hc | exact Hn].
  + destruct H0 as [z [n H0]].
    revert z st1 st2 H0.
    induction n; intros; simpl in H0.
    - exists O. simpl.
      unfold TerSem.test_sem in H0.
      unfold Relation_Operators.test_rel.
      tauto.
    - destruct H0 as [z0 [z1 [st1' [[Hst [Hb Ha0]] H0]]]].
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
Qed.

Theorem Bin_Step_equiv:
  sem_equiv (BinRel.ceval) (StepCnt.ceval) (Bin_Ter_sem_equiv).
Proof.
  apply (command_equiv__sem_equiv _ _ _
    (Bin_Ter_skip_sem_equiv_true _)
    (Bin_Ter_asgn_sem_equiv_true _)
    (Bin_Ter_seq_sem_equiv_true  _)
    (Bin_Ter_if_sem_equiv_true   _)
    (Bin_Ter_loop_sem_equiv_true _)).
Qed.

Theorem Bin_Trace_equiv:
  sem_equiv (BinRel.ceval) (Trace.ceval) (Bin_Ter_sem_equiv).
Proof.
  apply (command_equiv__sem_equiv _ _ _
    (Bin_Ter_skip_sem_equiv_true _)
    (Bin_Ter_asgn_sem_equiv_true _)
    (Bin_Ter_seq_sem_equiv_true  _)
    (Bin_Ter_if_sem_equiv_true   _)
    (Bin_Ter_loop_sem_equiv_true _)).
Qed.

(* General Theorem for equivalence between two recursively defined semantics *)

