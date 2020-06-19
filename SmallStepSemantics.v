Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.ImpExt4.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Setoids.Setoid.

Module BinStep.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip%imp, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep ((c1;;c2)%imp, st) ((c1';;c2)%imp, st')
  | CS_Seq : forall st c2,
      cstep ((Skip ;; c2)%imp, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        ((If b  Then c1 Else c2 EndIf)%imp, st)
        ((If b'  Then c1 Else c2 EndIf)%imp, st)
  | CS_IfTrue : forall st c1 c2,
      cstep ((If BTrue Then c1 Else c2 EndIf)%imp, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep ((If BFalse Then c1 Else c2 EndIf)%imp, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        ((While b Do c EndWhile)%imp, st)
        ((If b Then (c;; While b Do c EndWhile) Else Skip EndIf)%imp, st).

Inductive clos_refl_trans {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | rt_step : forall x y : A, R x y -> clos_refl_trans R x y
    | rt_refl : forall x : A, clos_refl_trans R x x
    | rt_trans : forall x y z : A,
               clos_refl_trans R x y ->
               clos_refl_trans R y z -> clos_refl_trans R x z.

Inductive clos_refl_trans_1n {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt1n_refl : forall x, clos_refl_trans_1n R x x
    | rt1n_trans_1n : forall x y z,
          R x y ->
          clos_refl_trans_1n R y z ->
          clos_refl_trans_1n R x z.

Inductive clos_refl_trans_n1 {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rtn1_refl : forall x, clos_refl_trans_n1 R x x
    | rtn1_trans_n1 : forall x y z : A,
          R y z ->
          clos_refl_trans_n1 R x y ->
          clos_refl_trans_n1 R x z.

Lemma rt_trans_1n: forall A (R: A -> A -> Prop) x y z,
  R x y ->
  clos_refl_trans R y z ->
  clos_refl_trans R x z.
Proof.
  intros.
  eapply rt_trans with y; [| exact H0].
  apply rt_step.
  exact H.
Qed.

Lemma rt_trans_n1: forall A (R: A -> A -> Prop) x y z,
  R y z ->
  clos_refl_trans R x y ->
  clos_refl_trans R x z.
Proof.
  intros.
  eapply rt_trans with y; [exact H0 |].
  apply rt_step.
  exact H.
Qed.

Lemma rt1n_step: forall A (R: A -> A -> Prop) x y,
  R x y ->
  clos_refl_trans_1n R x y.
Proof.
  intros.
  apply rt1n_trans_1n with y.
  + exact H.
  + apply rt1n_refl.
Qed.

Lemma rtn1_step: forall A (R: A -> A -> Prop) x y,
  R x y ->
  clos_refl_trans_n1 R x y.
Proof.
  intros.
  apply rtn1_trans_n1 with x.
  + exact H.
  + apply rtn1_refl.
Qed.

Lemma rt1n_trans: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_1n R a b ->
  clos_refl_trans_1n R b c ->
  clos_refl_trans_1n R a c.
Proof.
  intros.
  revert H0.
  induction H.
  + tauto.
  + intros.
    apply rt1n_trans_1n with y.
    - exact H.
    - apply IHclos_refl_trans_1n, H1.
Qed.

Lemma rt1n_trans_again: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_1n R a b ->
  clos_refl_trans_1n R b c ->
  clos_refl_trans_1n R a c.
Proof.
  intros.
  induction H.
  + exact H0.
  + apply IHclos_refl_trans_1n in H0.
    apply rt1n_trans_1n with y.
    - exact H.
    - exact H0.
Qed.

Lemma rtn1_trans: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_n1 R a b ->
  clos_refl_trans_n1 R b c ->
  clos_refl_trans_n1 R a c.
Proof.
  intros.
  induction H0.
  + exact H.
  + apply rtn1_trans_n1 with y; tauto.
Qed.

Lemma rt1n_rt: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans_1n R a b -> clos_refl_trans R a b.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_1n with y; tauto.
Qed.

Lemma rt_rt1n: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b -> clos_refl_trans_1n R a b.
Proof.
  intros.
  induction H.
  + apply rt1n_step, H.
  + apply rt1n_refl.
  + apply rt1n_trans with y; tauto.
Qed.

Lemma rtn1_rt: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans_n1 R a b -> clos_refl_trans R a b.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_n1 with y; tauto.
Qed.

Lemma rt_rtn1: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b -> clos_refl_trans_n1 R a b.
Proof.
  intros.
  induction H.
  + apply rtn1_step, H.
  + apply rtn1_refl.
  + apply rtn1_trans with y; tauto.
Qed.

Lemma rt_rt1n_iff: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b <-> clos_refl_trans_1n R a b.
Proof.
  split; intros.
  + apply rt_rt1n; auto.
  + apply rt1n_rt; auto.
Qed.

Lemma rt_rtn1_iff: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b <-> clos_refl_trans_n1 R a b.
Proof.
  split; intros.
  + apply rt_rtn1; auto.
  + apply rtn1_rt; auto.
Qed.

Instance rt_refl_ins A R: Reflexive (@clos_refl_trans A R).
Proof.
  hnf; intros.
  apply rt_refl.
Qed.

Instance rt_trans_ins A R: Transitive (@clos_refl_trans A R).
Proof.
  hnf; intros.
  eapply rt_trans; eauto.
Qed.
Lemma ind_1N: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x (P: A -> Prop),
  P x ->
  (forall y z (IH: P y), R z y -> RT_R y x -> P z) ->
  (forall y, RT_R y x -> P y).
Proof.
  intros.
  subst RT_R.
  apply rt_rt1n in H2.
  induction H2; auto.
  apply H1 with y; auto.
  apply rt1n_rt; auto.
Qed.

Lemma ind_N1: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x (P: A -> Prop),  
  P x ->
  (forall y z (IH: P y), R y z -> RT_R x y -> P z) ->
  (forall y, RT_R x y -> P y).
Proof.
  intros.
  subst RT_R.
  apply rt_rtn1 in H2.
  induction H2; auto.
  apply H1 with y; auto.
  apply rtn1_rt; auto.
Qed.

Lemma trans_1N: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x y z, R x y -> RT_R y z -> RT_R x z.
Proof.
  intros.
  subst.
  apply rt_trans_1n with y; auto.
Qed.

Lemma trans_N1: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x y z, RT_R x y -> R y z -> RT_R x z.
Proof.
  intros.
  subst.
  apply rt_trans_n1 with y; auto.
Qed.

Ltac induction_1n H :=
  match type of H with
  | ?RT_R ?b ?a =>
    revert_dependent_component b H;
    let b0 := fresh "x" in
    let EQ := fresh "EQ" in
    remember b as b0 eqn:EQ in H;
    revert EQ;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pb := eval pattern b0 in Q in
      match Pb with
      | ?P b0 =>
        revert b0 H;
        refine (ind_1N _ _ RT_R eq_refl a P _ _);
        [ intros_until_EQ EQ;
          match goal with
          | |- ?Base =>
            let Base0 := fresh in
            remember Base as Base0 in |- *;
            first [ injection EQ; clear EQ; intros_and_subst Base0
                  | revert EQ; intros_and_subst Base0
                  | idtac ];
            subst Base0
          end
        | let b0 := fresh "x" in
          let H0 := fresh "H" in
          let IH := fresh "IHrt" in
          first [intros ?b b0 IH H0 ? | intros ? b0 IH H0 ?]; intros_until_EQ EQ; subst b0;
          repeat progress
          match type of H0 with
          | _ ?y ?x => destruct_to_form x y
          end;
          specialize_until_EQ IH
        ]
      end
    end
  end.

Ltac induction_n1 H :=
  match type of H with
  | ?RT_R ?a ?b =>
    revert_dependent_component b H;
    let b0 := fresh "x" in
    let EQ := fresh "EQ" in
    remember b as b0 eqn:EQ in H;
    revert EQ;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pb := eval pattern b0 in Q in
      match Pb with
      | ?P b0 =>
        revert b0 H;
        refine (ind_N1 _ _ RT_R eq_refl a P _ _);
        [ intros_until_EQ EQ;
          match goal with
          | |- ?Base =>
            let Base0 := fresh in
            remember Base as Base0 in |- *;
            first [ injection EQ; clear EQ; intros_and_subst Base0
                  | revert EQ; intros_and_subst Base0
                  | idtac ];
            subst Base0
          end
        | let b0 := fresh "x" in
          let H0 := fresh "H" in
          let IH := fresh "IHrt" in
          first [intros ?b b0 IH H0 ? | intros ? b0 IH H0 ?]; intros_until_EQ EQ; subst b0;
          repeat progress
          match type of H0 with
          | _ ?x ?y => destruct_to_form x y
          end;
          specialize_until_EQ IH
        ]
      end
    end
  end.

Ltac transitivity_1n y :=
  match goal with
  | |- ?RT_R ?x ?z =>
    refine (trans_1N _ _ RT_R eq_refl x y z _ _)
  end.

Ltac etransitivity_1n :=
  match goal with
  | |- ?RT_R ?x ?z =>
    match type of x with
    | ?A => let y := fresh "y" in
            evar (y: A);
            transitivity_1n y;
            subst y
    end
  end.

Ltac transitivity_n1 y :=
  match goal with
  | |- ?RT_R ?x ?z =>
    refine (trans_N1 _ _ RT_R eq_refl x y z _ _)
  end.

Ltac etransitivity_n1 :=
  match goal with
  | |- ?RT_R ?x ?z =>
    match type of x with
    | ?A => let y := fresh "y" in
            evar (y: A);
            transitivity_n1 y;
            subst y
    end
  end.

Definition multi_cstep: com * state -> com * state -> Prop := clos_refl_trans cstep.

End BinStep.

Module TerStep.

Inductive cstep : (com * state) -> bool -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) false (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) true (Skip%imp, st2)
  | CS_SeqStep : forall st c1 z c1' st' c2,
      cstep (c1, st) z (c1', st') ->
      cstep ((c1;;c2)%imp, st) z ((c1';;c2)%imp, st')
  | CS_Seq : forall st c2,
      cstep ((Skip ;; c2)%imp, st) false (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        ((If b  Then c1 Else c2 EndIf)%imp, st)
        false
        ((If b'  Then c1 Else c2 EndIf)%imp, st)
  | CS_IfTrue : forall st c1 c2,
      cstep ((If BTrue Then c1 Else c2 EndIf)%imp, st) true (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep ((If BFalse Then c1 Else c2 EndIf)%imp, st) true (c2, st)
  | CS_While : forall st b c,
      cstep
        ((While b Do c EndWhile)%imp, st)
        false
        ((If b Then (c;; While b Do c EndWhile) Else Skip EndIf)%imp, st).

Inductive clos_refl_trans {A B : Type} (base : A -> bool -> A -> B)
                                       (add : B -> B -> B)
                                       (R : A -> bool -> A -> Prop)
                                       : A -> B -> A -> Prop :=
    rt_step : forall x y b, R x b y -> clos_refl_trans base add R x (base x b y) y
  | rt_refl : forall x, clos_refl_trans base add R x (base x false x) x
  | rt_trans : forall x y z c1 c2,
               clos_refl_trans base add R x c1 y ->
               clos_refl_trans base add R y c2 z -> clos_refl_trans base add R x (add c1 c2) z.

Definition base_cnt (_ : com * state) (b : bool) (_ : com * state) : Z :=
  match b with
  | false => 0
  | true => 1
  end.

Definition multi_cstep_cnt: com * state -> Z -> com * state -> Prop := 
  clos_refl_trans base_cnt Z.add cstep.

Definition base_trace (_ : com * state) (b : bool) (cst : com * state) : list state :=
  match b with
  | false => nil
  | true => match cst with
    | (c, st) => (st :: nil)
    end
  end.

Definition multi_cstep_trace: com * state -> list state -> com * state -> Prop :=
  clos_refl_trans base_trace (@List.app state) cstep.

End TerStep.


