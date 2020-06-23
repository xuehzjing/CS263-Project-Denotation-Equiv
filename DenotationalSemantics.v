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

Inductive mid_param (A B: Type) :=
  | MP (zero : B)
       (one : A -> A -> B)
       (add : B -> B -> B)
       (add_zero_l : forall (x : B), add zero x = x)
       (add_zero_r : forall (x : B), add x zero = x)
       (add_assoc : forall (x y z : B), add (add x y) z = add x (add y z)).

Arguments MP {A B}.

Definition MP_zero {A B: Type} (mp: mid_param A B) := 
  match mp with
  | MP zero _ _ _ _ _ => zero
  end.

Definition MP_one {A B: Type} (mp: mid_param A B) := 
  match mp with
  | MP _ one _ _ _ _ => one
  end.

Definition MP_add {A B: Type} (mp: mid_param A B) := 
  match mp with
  | MP _ _ add _ _ _ => add
  end.

Lemma MP_MP_zero: forall {A B: Type} (mp: mid_param A B) zero one add add_zero_l add_zero_r add_assoc,
  mp = MP zero one add add_zero_l add_zero_r add_assoc -> MP_zero mp = zero.
Proof. intros. subst. reflexivity. Qed.

Lemma MP_MP_one: forall {A B: Type} (mp: mid_param A B) zero one add add_zero_l add_zero_r add_assoc,
  mp = MP zero one add add_zero_l add_zero_r add_assoc -> MP_one mp = one.
Proof. intros. subst. reflexivity. Qed.

Lemma MP_MP_add: forall {A B: Type} (mp: mid_param A B) zero one add add_zero_l add_zero_r add_assoc,
  mp = MP zero one add add_zero_l add_zero_r add_assoc -> MP_add mp = add.
Proof. intros. subst. reflexivity. Qed.

Lemma MP_add_zero_l: forall {A B: Type} (mp: mid_param A B),
  forall (x : B), MP_add mp (MP_zero mp) x = x.
Proof. intros. destruct mp. simpl. apply add_zero_l. Qed.

Lemma MP_add_zero_r: forall {A B: Type} (mp: mid_param A B),
  forall (x : B), MP_add mp x (MP_zero mp) = x.
Proof. intros. destruct mp. simpl. apply add_zero_r. Qed.

Lemma MP_add_assoc: forall {A B: Type} (mp: mid_param A B),
  forall (x y z : B), MP_add mp (MP_add mp x y) z = MP_add mp x (MP_add mp y z).
Proof. intros. destruct mp. simpl. apply add_assoc. Qed.

Definition Z_one (_ : state) (_ : state) : Z :=
  1.

Definition Z_mp := MP 0 Z_one Z.add Z.add_0_l Z.add_0_r Zplus_assoc_reverse.

Definition List_one (_ : state) (st : state) : list state :=
  (st :: nil).

Definition List_mp := MP nil List_one
                      (@List.app _)
                      (@List.app_nil_l _)
                      (@List.app_nil_r _)
                      (@List.app_assoc_reverse _).

Fixpoint ceval_by_sem {T: Type} (S: semantic T)
  (c : com) : T :=
  match c with
  | CSkip => semantic_skip S
  | CAss X E => semantic_asgn S X E
  | CSeq c1 c2 => semantic_seq S (ceval_by_sem S c1) (ceval_by_sem S c2)
  | CIf b c1 c2 => semantic_if S b (ceval_by_sem S c1) (ceval_by_sem S c2)
  | CWhile b c => semantic_loop S b (ceval_by_sem S c)
  end.

Lemma ceval_CSkip: forall {T: Type} (S: semantic T),
  ceval_by_sem S CSkip = semantic_skip S.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall {T: Type} (S: semantic T) X E,
  ceval_by_sem S (CAss X E) = semantic_asgn S X E.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall {T: Type} (S: semantic T) c1 c2,
  ceval_by_sem S (c1 ;; c2) = semantic_seq S (ceval_by_sem S c1) (ceval_by_sem S c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall {T: Type} (S: semantic T) b c1 c2,
  ceval_by_sem S (CIf b c1 c2) = semantic_if S b (ceval_by_sem S c1) (ceval_by_sem S c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall {T: Type} (S: semantic T) b c,
  ceval_by_sem S (While b Do c EndWhile) = semantic_loop S b (ceval_by_sem S c).
Proof. intros. simpl. reflexivity. Qed.

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

Theorem loop_unrolling : forall b c st1 st2,
  ceval (While b Do c EndWhile) st1 st2 <->
  ceval (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf) st1 st2.
Proof.
  intros. unfold ceval.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

End BinRel.

(** Definition of Denotational Semantics as Trinary Relation
    (Begin States, Step Counts, Ending States). *)

Module TerSem.

Definition skip_sem {T: Type} (mp: mid_param state T)
  : state -> T -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = MP_zero mp.

Definition asgn_sem {T: Type} (mp: mid_param state T) (X: var) (E: aexp)
  : state -> T -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\
    t = MP_one mp st1 st2.

Definition seq_sem {T: Type} (mp: mid_param state T) (d1 d2: state -> T -> state -> Prop)
  : state -> T -> state -> Prop
:=
  fun st1 t st3 =>
    exists t1 t2 st2,
      d1 st1 t1 st2 /\ d2 st2 t2 st3 /\ t = MP_add mp t1 t2.

Definition test_sem {T: Type} (mp: mid_param state T) (X: state -> Prop): state -> T -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ X st1 /\ t = MP_one mp st1 st2.

Definition union_sem {T: Type} (mp: mid_param state T) (d d': state -> T -> state -> Prop)
  : state -> T -> state -> Prop
:=
  fun st1 t st2 =>
    d st1 t st2 \/ d' st1 t st2.

Definition if_sem {T: Type} (mp: mid_param state T) (b: bexp) (d1 d2: state -> T -> state -> Prop)
  : state -> T -> state -> Prop
:=
  union_sem mp
    (seq_sem mp (test_sem mp (beval b)) d1)
    (seq_sem mp (test_sem mp (beval (! b))) d2).

Fixpoint iter_loop_body {T: Type} (mp: mid_param state T)
  (b: bexp)
  (loop_body: state -> T -> state -> Prop)
  (n: nat)
  : state -> T -> state -> Prop
:=
  match n with
  | O => test_sem mp (beval (! b))
  | S n' => seq_sem mp
              (test_sem mp (beval b))
              (seq_sem mp loop_body (iter_loop_body mp b loop_body n'))
  end.

Definition omega_union_sem {T: Type} (mp: mid_param state T) (d: nat -> state -> T -> state -> Prop)
  : state -> T -> state -> Prop
:=
  fun st1 t st2 => exists n, d n st1 t st2.

Definition loop_sem {T: Type} (mp: mid_param state T) (b: bexp) (loop_body: state -> T -> state -> Prop)
  : state -> T -> state -> Prop
:=
  omega_union_sem mp (iter_loop_body mp b loop_body).

Definition sem {T: Type} (mp: mid_param state T)
:= Sem (skip_sem mp) (asgn_sem mp) (seq_sem mp) (if_sem mp) (loop_sem mp).

Definition ceval {T: Type} (mp: mid_param state T) := ceval_by_sem (sem mp).

Lemma loop_sem_unrolling: forall {T: Type} (mp: mid_param state T) b (R: state -> T -> state -> Prop) st1 x st2,
  loop_sem mp b R st1 x st2 <-> 
  if_sem mp b (seq_sem mp R (loop_sem mp b R)) (skip_sem mp) st1 x st2.
Proof.
  split; intros.
  + unfold loop_sem, omega_union_sem in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, seq_sem.
      right; simpl.
      unfold skip_sem.
      exists x, (MP_zero mp), st2; split; [exact H | split; [tauto | rewrite (MP_add_zero_r mp); reflexivity]].
    - simpl in H.
      unfold if_sem, seq_sem.
      left.
      unfold seq_sem in H.
      destruct H as [l1 [l2 [st1' [[Hst [Hb Hl1]] H]]]].
      destruct H as [[l3 [l4 [st3 [Hc [Hiter Hl3]]]]] Hl2].
      subst l1 l2 x st1'.
      exists (MP_one mp st1 st1), (MP_add mp l3 l4), st1; split;
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
      subst l1 l2 x st2' st2.
      unfold test_sem.
      split; [tauto | split; [ apply Hb | apply (MP_add_zero_r mp)]].
    }
    destruct H as [l1 [l2 [st1' [[Hst [Hb Hl1]] H]]]].
    destruct H as [[l3 [l4 [st3 [Hc [Hiter Hl3]]]]] Hl2].
    subst l1 l2 x st1'.
    unfold loop_sem, omega_union_sem in Hiter.
    destruct Hiter as [n Hiter].
    exists (S n).
    simpl.
    unfold seq_sem.
    exists (MP_one mp st1 st1), (MP_add mp l3 l4), st1;
      split; [unfold test_sem; tauto | split; [| tauto]].
    exists l3, l4, st3; tauto.
Qed.

Theorem loop_unrolling : forall {T: Type} (mp: mid_param state T) b c z st1 st2,
  ceval mp (While b Do c EndWhile) st1 z st2 <->
  ceval mp (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf) st1 z st2.
Proof.
  intros.
  unfold ceval.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

End TerSem.

Module StepCnt.

Definition ceval := TerSem.ceval Z_mp.
Definition loop_unrolling := TerSem.loop_unrolling Z_mp.

End StepCnt.

(** Definition of Denotational Semantics as Trinary Relation 
    (Begin States, Intermediate Traces, Ending States).
    For conciseness, we assume that an intermediate state trace does not include
    the beginning state but includes the ending state. *)

Module Trace.

Definition ceval := TerSem.ceval List_mp.
Definition loop_unrolling := TerSem.loop_unrolling List_mp.

End Trace.
