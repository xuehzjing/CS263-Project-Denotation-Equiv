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
