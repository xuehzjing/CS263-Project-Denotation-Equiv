Require Import Coq.Lists.List.
Require Import PL.Imp3.

(** Definition of Denotational Semantics as Binary Relation
    (Begin States, Ending States). *)

Module BinRel.

Import Relation_Operators.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (concat (test_rel (beval b)) then_branch)
    (concat (test_rel (beval (BNot b))) else_branch).

Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         test_rel (beval (BNot b))
  | S n' =>
         concat
           (test_rel (beval b))
           (concat
              loop_body
              (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  omega_union (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

End BinRel.

(** Definition of Denotational Semantics as Trinary Relation
    (Begin States, Execution Time, Ending States). *)

Module StepCnt.

Definition skip_sem: state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = 0.

Definition asgn_sem (X: var) (E: aexp): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    t = 1.

Definition seq_sem (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st3 =>
    exists t1 t2 st2,
      d1 st1 t1 st2 /\ d2 st2 t2 st3 /\ t = t1 + t2.

Definition test_sem (X: state -> Prop): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ X st1 /\ t = 1.

Definition union_sem (d d': state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 =>
    d st1 t st2 \/ d' st1 t st2.

Definition if_sem (b: bexp) (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> Z -> state -> Prop)
  (n: nat)
  : state -> Z -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 => exists n, d n st1 t st2.

Definition loop_sem (b: bexp) (loop_body: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> Z -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

End StepCnt.

(** Definition of Denotational Semantics as Trinary Relation 
    (Begin States, Intermediate Traces, Ending States).
    For conciseness, we assume that an intermediate state trace does not include
    the beginning state but includes the ending state. *)

Module Trace.

Definition skip_sem: state -> list state -> state -> Prop :=
  fun st1 tr st2 =>
    st1 = st2 /\ tr = nil.

Definition asgn_sem (X: var) (E: aexp): state -> list state -> state -> Prop :=
  fun st1 tr st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    tr = st2 :: nil.

Definition seq_sem (d1 d2: state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  fun st1 tr st3 =>
    exists tr1 tr2 st2,
      d1 st1 tr1 st2 /\ d2 st2 tr2 st3 /\ tr = tr1 ++ tr2.

Definition test_sem (X: state -> Prop): state -> list state -> state -> Prop :=
  fun st1 tr st2 =>
    st1 = st2 /\ tr = st1 :: nil /\ X st1.

Definition union_sem (d d': state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  fun st1 tr st2 =>
    d st1 tr st2 \/ d' st1 tr st2.

Definition if_sem (b: bexp) (d1 d2: state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> list state -> state -> Prop)
  (n: nat)
  : state -> list state -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  fun st1 tr st2 => exists n, d n st1 tr st2.

Definition loop_sem (b: bexp) (loop_body: state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> list state -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

End Trace.

Lemma ceval_while (c: com) (b: bexp):
  forall st1 st2 st3,
    beval b st1 ->
    BinRel.ceval c st1 st3 ->
    BinRel.ceval (While b Do c EndWhile) st3 st2 ->
    BinRel.ceval (While b Do c EndWhile) st1 st2.
Proof.
  intros.
  simpl.
  simpl in H1.
  unfold BinRel.loop_sem,
         Relation_Operators.omega_union in H1.
  destruct H1 as [n H1].
  revert st1 st2 st3 H H0 H1.
  induction n; intros.
  + unfold BinRel.loop_sem,
           Relation_Operators.omega_union.
    exists (S O).
    exists st1.
    firstorder.
  + simpl in H1.
    unfold Relation_Operators.concat in H1.
    destruct H1 as [st3' [HTest H1]].
    unfold Relation_Operators.test_rel in HTest.
    destruct HTest as [Hst Hb].
    subst st3'.
    destruct H1 as [st4 [Hc Hiter]].
    pose proof IHn _ _ _ Hb Hc Hiter.
Admitted.


(* General Theorem for equivalence between two recursively defined semantics *)

Definition equiv_between_recur_sem {X: Type} 
                                   (f1: com -> state -> state -> Prop) 
                                   (f2: com -> state -> X -> state -> Prop) : Prop :=
  forall c st1 st2, f1 c st1 st2 <-> (exists a, f2 c st1 a st2).

Theorem equiv_between_normal_time:
  equiv_between_recur_sem BinRel.ceval StepCnt.ceval.
Proof.
  unfold equiv_between_recur_sem; intros.
  revert st1 st2.
  induction c; intros.
  + split; intros.
    - exists 0.
      inversion H; subst.
      simpl; unfold StepCnt.skip_sem.
      tauto.
    - destruct H; inversion H; subst.
      unfold BinRel.ceval.
      reflexivity.
  + split; intros.
    - exists 1.
      inversion H; subst.
      simpl; unfold StepCnt.asgn_sem.
      firstorder.
    - destruct H; inversion H; subst.
      unfold BinRel.ceval.
      firstorder.
  + split; intros.
    - inversion H as [st3 H0].
      destruct H0 as [H1 H2].
      specialize (IHc1 st1 st3).
      destruct IHc1 as [IHc1 IHc1'].
      specialize (IHc1 H1).
      destruct IHc1 as [a1 IHc1].
      specialize (IHc2 st3 st2).
      destruct IHc2 as [IHc2 IHc2'].
      specialize (IHc2 H2).
      destruct IHc2 as [a2 IHc2].
      clear IHc1' IHc2' H H1 H2.
      exists (a1 + a2).
      simpl; unfold StepCnt.seq_sem.
      exists a1, a2, st3.
      tauto.
    - destruct H as [a H].
      simpl in H.
      unfold StepCnt.seq_sem in H.
      assert (exists (t1 : Z) (st3 : state), StepCnt.ceval c1 st1 t1 st3).
      { destruct H as [a1 [a2 [st3 [H1 ?]]]].
        exists a1, st3.
        exact H1. }
      assert (exists (t2 : Z) (st3 : state), StepCnt.ceval c2 st3 t2 st2).
      { destruct H as [a1 [a2 [st3 [? [H2 ?]]]]].
        exists a2, st3.
        exact H2. }
      destruct H as [a1 [a2 [st3 [H1' [H2' Ha]]]]].
      assert (exists (t1 : Z), StepCnt.ceval c1 st1 t1 st3) as HStep1.
      { exists a1. exact H1'. }
      assert (exists (t2 : Z), StepCnt.ceval c2 st3 t2 st2) as HStep2.
      { exists a2. exact H2'. }
      clear H1' H2' Ha H0 H1.
      specialize (IHc1 st1 st3).
      destruct IHc1 as [IHc1' IHc1].
      specialize (IHc1 HStep1).
      specialize (IHc2 st3 st2).
      destruct IHc2 as [IHc2' IHc2].
      specialize (IHc2 HStep2).
      clear IHc1' IHc2' HStep1 HStep2.
      simpl; unfold Relation_Operators.concat.
      exists st3.
      tauto.
  + split; intros.
    - simpl in H.
      unfold BinRel.if_sem, 
             Relation_Operators.union,
             Relation_Operators.concat, 
             Relation_Operators.test_rel in H.
      destruct H; destruct H as [st1' [HTest H]].
      * destruct HTest.
        subst st1'.
        specialize (IHc1 st1 st2).
        destruct IHc1 as [IHc1 IHc1'].
        specialize (IHc1 H).
        destruct IHc1 as [a IHc1].
        clear IHc1' IHc2 H.
        exists (a + 1).
        simpl.
        unfold StepCnt.if_sem,
               StepCnt.union_sem,
               StepCnt.seq_sem,
               StepCnt.test_sem.
        left.
        exists 1, a, st1.
        firstorder.
      * destruct HTest.
        subst st1'.
        specialize (IHc2 st1 st2).
        destruct IHc2 as [IHc2 IHc2'].
        specialize (IHc2 H).
        destruct IHc2 as [a IHc2].
        clear IHc2' IHc1 H.
        exists (a + 1).
        simpl.
        unfold StepCnt.if_sem,
               StepCnt.union_sem,
               StepCnt.seq_sem,
               StepCnt.test_sem.
        right.
        exists 1, a, st1.
        firstorder.
    - destruct H as [a H].
      simpl in H.
      unfold StepCnt.if_sem,
             StepCnt.union_sem,
             StepCnt.seq_sem,
             StepCnt.test_sem in H.
      destruct H.
      * assert (exists (t1 : Z), StepCnt.ceval c1 st1 t1 st2) as HStep.
        { destruct H as [t1 [t2 [st3 [HTest [HStep Ha]]]]].
          destruct HTest as [Hst [Hb Ht]].
          subst st3 t1.
          exists t2.
          exact HStep. }
        specialize (IHc1 st1 st2).
        destruct IHc1 as [IHc1' IHc1].
        specialize (IHc1 HStep).
        clear IHc1' IHc2 HStep.
        simpl.
        unfold BinRel.if_sem,
               Relation_Operators.union,
               Relation_Operators.concat,
               Relation_Operators.test_rel.
        left.
        exists st1.
        firstorder.
      * assert (exists (t1 : Z), StepCnt.ceval c2 st1 t1 st2) as HStep.
        { destruct H as [t1 [t2 [st3 [HTest [HStep Ha]]]]].
          destruct HTest as [Hst [Hb Ht]].
          subst st3 t1.
          exists t2.
          exact HStep. }
        specialize (IHc2 st1 st2).
        destruct IHc2 as [IHc2' IHc2].
        specialize (IHc2 HStep).
        clear IHc1 IHc2' HStep.
        simpl.
        unfold BinRel.if_sem,
               Relation_Operators.union,
               Relation_Operators.concat,
               Relation_Operators.test_rel.
        right.
        exists st1.
        firstorder.
  + split; intros.
    - simpl in H.
      unfold BinRel.loop_sem,
             Relation_Operators.omega_union in H.
      destruct H as [n H].
      revert st1 st2 H.
      induction n; intros.
      * destruct H as [Hst Hb].
        exists 1.
        simpl.
        unfold StepCnt.loop_sem,
               StepCnt.omega_union_sem,
               StepCnt.iter_loop_body,
               StepCnt.test_sem,
               StepCnt.seq_sem.
        exists O.
        tauto.
      * simpl in H.
        unfold Relation_Operators.concat,
               Relation_Operators.test_rel in H.
        destruct H as [st1' [[Hst Hb] [st3 [H1 H2]]]].
        subst st1'.
        specialize (IHc st1 st3).
        destruct IHc as [IHc IHc'].
        specialize (IHc H1).
        specialize (IHn st3 st2).
        specialize (IHn H2).
        destruct IHc as [ac IHc].
        destruct IHn as [an IHn].
        clear IHc' H1 H2 n.
        simpl in IHn.
        unfold StepCnt.loop_sem, StepCnt.omega_union_sem in IHn.
        destruct IHn as [n IHn].
        exists (ac + 1 + an).
        simpl.
        unfold StepCnt.loop_sem,
               StepCnt.omega_union_sem.
        exists (S n).
        simpl.
        unfold StepCnt.test_sem,
               StepCnt.seq_sem.
        exists 1, (ac + an), st1.
        split; [tauto | split; [| lia] ].
        exists ac, an, st3.
        firstorder.
    - simpl in H.
      destruct H as [a H].
      unfold StepCnt.loop_sem,
             StepCnt.omega_union_sem in H.
      simpl.
      unfold BinRel.loop_sem,
             Relation_Operators.omega_union.
      destruct H as [n H].
      revert IHc a st1 st2 H.
      induction n; intros.
      * inversion H.
        unfold BinRel.iter_loop_body,
               Relation_Operators.test_rel.
        exists O.
        tauto.
      * destruct H as [a0 [a1 [st1' [[Hst [Hb Ha0]] [[ac [an [st3 [Hc [Hn Ha2]]]]] Ha1]]]]].
        subst st1' a0 a1 a.
        specialize (IHn IHc _ _ _ Hn).
        destruct IHn as [n0 IHn].
        assert (exists a : Z, StepCnt.ceval c st1 a st3) as Hce.
        { exists ac. exact Hc. }
        specialize (IHc st1 st3).
        destruct IHc as [IHc' IHc].
        specialize (IHc Hce).
        exists (S n0).
        simpl.
        unfold Relation_Operators.concat,
               Relation_Operators.test_rel.
        exists st1.
        split; [tauto |].
        exists st3.
        tauto.
Qed.




Definition Bin_Time_Equiv (X : state -> state -> Prop) 
                          (Y : state -> Z -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists z, Y st1 z st2).
  
Definition Bin_Trace_Equiv (X : state -> state -> Prop) 
                           (Y : state -> list state -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists l, Y st1 l st2).
  
Theorem Bin_Time_Equiv_Theorem (ceval_X: com -> state -> state -> Prop) 
                               (ceval_Y: com -> state -> Z -> state -> Prop) :
  forall c, Bin_Time_Equiv (ceval_X c) (ceval_Y c).
Proof.
  intros.
  induction c.
Abort.

