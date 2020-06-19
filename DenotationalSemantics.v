Require Import Coq.Lists.List.
Require Import PL.Imp3.

(** Definition of Denotational Semantics as Binary Relation
    (Begin States, Ending States). *)

Inductive semantic (X: Type) :=
  | Sem (skip_sem: X)
        (asgn_sem: var -> aexp -> X)
        (seq_sem: X -> X -> X)
        (if_sem: bexp -> X -> X -> X)
        (loop_sem: bexp -> X -> X).

Arguments Sem {X} skip_sem asgn_sem seq_sem if_sem loop_sem.

Definition semantic_skip {X: Type} (S: semantic X) := 
  match S with
  | Sem skip_sem _ _ _ _ => skip_sem
  end.

Definition semantic_asgn {X: Type} (S: semantic X) := 
  match S with
  | Sem _ asgn_sem _ _ _ => asgn_sem
  end.

Definition semantic_seq {X: Type} (S: semantic X) := 
  match S with
  | Sem _ _ seq_sem _ _ => seq_sem
  end.

Definition semantic_if {X: Type} (S: semantic X) := 
  match S with
  | Sem _ _ _ if_sem _ => if_sem
  end.

Definition semantic_loop {X: Type} (S: semantic X) := 
  match S with
  | Sem _ _ _ _ loop_sem => loop_sem
  end.

Fixpoint ceval_by_sem {T: Type} (S: semantic T)
  (c : com) : T :=
  match c with
  | CSkip => semantic_skip S
  | CAss X E => semantic_asgn S X E
  | CSeq c1 c2 => semantic_seq S (ceval_by_sem S c1) (ceval_by_sem S c2)
  | CIf b c1 c2 => semantic_if S b (ceval_by_sem S c1) (ceval_by_sem S c2)
  | CWhile b c => semantic_loop S b (ceval_by_sem S c)
  end.

Module BinRel.

Import Relation_Operators.

Definition skip_sem: state -> state -> Prop := id.

Definition asgn_sem (X: var) (E: aexp): state -> state -> Prop :=
  fun st1 st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y.

Definition seq_sem (c1 c2: state -> state -> Prop)
  : state -> state -> Prop
:= concat c1 c2.

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

Definition sem := Sem skip_sem asgn_sem seq_sem if_sem loop_sem.

Definition ceval := ceval_by_sem sem.

Lemma ceval_CSkip: ceval CSkip = id.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 st2 =>
      st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = concat (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.

Theorem loop_unrolling : forall b c st1 st2,
  ceval (While b Do c EndWhile) st1 st2 <->
  ceval (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf) st1 st2.
Proof.
  intros.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

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

Definition sem := Sem skip_sem asgn_sem seq_sem if_sem loop_sem.

Definition ceval := ceval_by_sem sem.

Lemma ceval_CSkip: ceval CSkip = skip_sem.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 z st2 =>
      st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y /\
        z = 1.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = seq_sem (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.

Lemma loop_sem_unrolling: forall b (R: state -> Z -> state -> Prop) st1 z st2,
  loop_sem b R st1 z st2 <-> 
  if_sem b (seq_sem R (loop_sem b R)) skip_sem st1 z st2.
Proof.
  split; intros.
  + unfold loop_sem, omega_union_sem in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, seq_sem.
      right; simpl.
      unfold skip_sem.
      exists z, 0, st2; split; [exact H | split; [tauto | lia]].
    - simpl in H.
      unfold if_sem, seq_sem.
      left.
      unfold seq_sem in H.
      destruct H as [z1 [z2 [st1' [[Hst [Hb Hz1]] H]]]].
      destruct H as [[z3 [z4 [st3 [Hc [Hiter Hz3]]]]] Hz2].
      subst z1 z2 z st1'.
      exists 1, (z3 + z4), st1; split; [unfold test_sem; tauto | split; [| lia]].
      exists z3, z4, st3; split; [tauto | split; [| lia]].
      unfold loop_sem, omega_union_sem.
      exists n.
      exact Hiter.
  + unfold if_sem, seq_sem in H.
    unfold loop_sem, omega_union_sem.
    destruct H.
    2: {
      exists O.
      simpl.
      unfold skip_sem in H.
      destruct H as [z1 [z2 [st2' [[Hst [Hb Hz1]] [[Hst2 Hz2] Hz]]]]].
      subst z1 z2 z st2' st2.
      unfold test_sem.
      split; [tauto | split; [tauto | lia]].
    }
    destruct H as [z1 [z2 [st1' [[Hst [Hb Hz1]] H]]]].
    destruct H as [[z3 [z4 [st3 [Hc [Hiter Hz3]]]]] Hz2].
    subst z1 z2 z st1'.
    unfold loop_sem, omega_union_sem in Hiter.
    destruct Hiter as [n Hiter].
    exists (S n).
    simpl.
    unfold seq_sem.
    exists 1, (z3 + z4), st1; split; [unfold test_sem; tauto | split; [| tauto]].
    exists z3, z4, st3; tauto.
Qed.

Theorem loop_unrolling : forall b c z st1 st2,
  ceval (While b Do c EndWhile) st1 z st2 <->
  ceval (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf) st1 z st2.
Proof.
  intros.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

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

Definition sem := Sem skip_sem asgn_sem seq_sem if_sem loop_sem.

Definition ceval := ceval_by_sem sem.

Lemma ceval_CSkip: ceval CSkip = skip_sem.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 l st2 =>
      st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y /\
        l = st2 :: nil.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = seq_sem (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.

Lemma loop_sem_unrolling: forall b (R: state -> list state -> state -> Prop) st1 l st2,
  loop_sem b R st1 l st2 <-> 
  if_sem b (seq_sem R (loop_sem b R)) skip_sem st1 l st2.
Proof.
  split; intros.
  + unfold loop_sem, omega_union_sem in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, seq_sem.
      right; simpl.
      unfold skip_sem.
      exists l, nil, st2; split; [exact H | split; [tauto | apply app_nil_end]].
    - simpl in H.
      unfold if_sem, seq_sem.
      left.
      unfold seq_sem in H.
      destruct H as [l1 [l2 [st1' [[Hst [Hb Hl1]] H]]]].
      destruct H as [[l3 [l4 [st3 [Hc [Hiter Hl3]]]]] Hl2].
      subst l1 l2 l st1'.
      exists (st1 :: nil), (l3 ++ l4), st1; split;
        [unfold test_sem; tauto | split; [| reflexivity]].
      exists l3, l4, st3; split; [tauto | split; [| reflexivity]].
      unfold loop_sem, omega_union_sem.
      exists n.
      exact Hiter.
  + unfold if_sem, seq_sem in H.
    unfold loop_sem, omega_union_sem.
    destruct H.
    2: {
      exists O.
      simpl.
      unfold skip_sem in H.
      destruct H as [l1 [l2 [st2' [[Hst [Hb Hl1]] [[Hst2 Hl2] Hl]]]]].
      subst l1 l2 l st2' st2.
      unfold test_sem.
      split; [tauto | split; [reflexivity | tauto]].
    }
    destruct H as [l1 [l2 [st1' [[Hst [Hb Hl1]] H]]]].
    destruct H as [[l3 [l4 [st3 [Hc [Hiter Hl3]]]]] Hl2].
    subst l1 l2 l st1'.
    unfold loop_sem, omega_union_sem in Hiter.
    destruct Hiter as [n Hiter].
    exists (S n).
    simpl.
    unfold seq_sem.
    exists (st1 :: nil), (l3 ++ l4), st1;
      split; [unfold test_sem; tauto | split; [| tauto]].
    exists l3, l4, st3; tauto.
Qed.

Theorem loop_unrolling : forall b c z st1 st2,
  ceval (While b Do c EndWhile) st1 z st2 <->
  ceval (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf) st1 z st2.
Proof.
  intros.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

End Trace.
