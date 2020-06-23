Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.ImpExt4.
Require Import PL.DenotationalSemantics.

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

Inductive clos_refl_trans {A B : Type} (mp : mid_param A B)
                                       (R : A -> bool -> A -> Prop)
                                       : A -> B -> A -> Prop :=
    rt_step_false : forall x y, R x false y -> clos_refl_trans mp R x (MP_zero mp) y
  | rt_step_true : forall x y, R x true y -> clos_refl_trans mp R x (MP_one mp x y) y
  | rt_refl : forall x, clos_refl_trans mp R x (MP_zero mp) x
  | rt_trans : forall x y z c1 c2,
               clos_refl_trans mp R x c1 y ->
               clos_refl_trans mp R y c2 z ->
               clos_refl_trans mp R x (MP_add mp c1 c2) z.

Inductive clos_refl_trans_1n {A B : Type} (mp : mid_param A B)
                                          (R : A -> bool -> A -> Prop)
                                          : A -> B -> A -> Prop :=
    | rt1n_refl : forall x, clos_refl_trans_1n mp R x (MP_zero mp) x
    | rt1n_trans_1n_false : forall x y z c,
          R x false y ->
          clos_refl_trans_1n mp R y c z ->
          clos_refl_trans_1n mp R x c z
    | rt1n_trans_1n_true : forall x y z c,
          R x true y ->
          clos_refl_trans_1n mp R y c z ->
          clos_refl_trans_1n mp R x (MP_add mp (MP_one mp x y) c) z.

Inductive clos_refl_trans_n1 {A B : Type} (mp : mid_param A B)
                                          (R : A -> bool -> A -> Prop)
                                          : A -> B -> A -> Prop :=
    | rtn1_refl : forall x, clos_refl_trans_n1 mp R x (MP_zero mp) x
    | rtn1_trans_n1_false : forall x y z c,
          R y false z ->
          clos_refl_trans_n1 mp R x c y ->
          clos_refl_trans_n1 mp R x c z
    | rtn1_trans_n1_true : forall x y z c,
          R y true z ->
          clos_refl_trans_n1 mp R x c y ->
          clos_refl_trans_n1 mp R x (MP_add mp c (MP_one mp y z)) z.

Lemma rt_trans_1n_false: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y z c,
  R x false y ->
  clos_refl_trans mp R y c z ->
  clos_refl_trans mp R x c z.
Proof.
  intros.
  rewrite <- (MP_add_zero_l mp c).
  eapply rt_trans with y; [| exact H0].
  apply rt_step_false.
  exact H.
Qed.

Lemma rt_trans_1n_true: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y z c,
  R x true y ->
  clos_refl_trans mp R y c z ->
  clos_refl_trans mp R x (MP_add mp (MP_one mp x y) c) z.
Proof.
  intros.
  eapply rt_trans with y; [| exact H0].
  apply rt_step_true.
  exact H.
Qed.

Lemma rt_trans_n1_false: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y z c,
  R y false z ->
  clos_refl_trans mp R x c y ->
  clos_refl_trans mp R x c z.
Proof.
  intros.
  rewrite <- (MP_add_zero_r mp c).
  eapply rt_trans with y; [exact H0 |].
  apply rt_step_false.
  exact H.
Qed.

Lemma rt_trans_n1_true: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y z c,
  R y true z ->
  clos_refl_trans mp R x c y ->
  clos_refl_trans mp R x (MP_add mp c (MP_one mp y z)) z.
Proof.
  intros.
  eapply rt_trans with y; [exact H0 |].
  apply rt_step_true.
  exact H.
Qed.

Lemma rt1n_step_false: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y,
  R x false y ->
  clos_refl_trans_1n mp R x (MP_zero mp) y.
Proof.
  intros.
  apply rt1n_trans_1n_false with y.
  + exact H.
  + apply rt1n_refl.
Qed.

Lemma rt1n_step_true: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y,
  R x true y ->
  clos_refl_trans_1n mp R x (MP_one mp x y) y.
Proof.
  intros.
  rewrite <- (MP_add_zero_r mp _).
  apply rt1n_trans_1n_true.
  + exact H.
  + apply rt1n_refl.
Qed.

Lemma rtn1_step_false: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y,
  R x false y ->
  clos_refl_trans_n1 mp R x (MP_zero mp) y.
Proof.
  intros.
  apply rtn1_trans_n1_false with x.
  + exact H.
  + apply rtn1_refl.
Qed.

Lemma rtn1_step_true: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y,
  R x true y ->
  clos_refl_trans_n1 mp R x (MP_one mp x y) y.
Proof.
  intros.
  rewrite <- (MP_add_zero_l mp _).
  apply rtn1_trans_n1_true.
  + exact H.
  + apply rtn1_refl.
Qed.

Lemma rt1n_trans: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y z c1 c2,
  clos_refl_trans_1n mp R x c1 y ->
  clos_refl_trans_1n mp R y c2 z ->
  clos_refl_trans_1n mp R x (MP_add mp c1 c2) z.
Proof.
  intros.
  revert H0.
  induction H; intros.
  + rewrite -> (MP_add_zero_l mp). tauto.
  + apply rt1n_trans_1n_false with y.
    - exact H.
    - apply IHclos_refl_trans_1n, H1.
  + rewrite -> (MP_add_assoc mp).
    apply rt1n_trans_1n_true.
    - exact H.
    - apply IHclos_refl_trans_1n, H1.
Qed.

Lemma rtn1_trans: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y z c1 c2,
  clos_refl_trans_n1 mp R x c1 y ->
  clos_refl_trans_n1 mp R y c2 z ->
  clos_refl_trans_n1 mp R x (MP_add mp c1 c2) z.
Proof.
  intros.
  induction H0.
  + rewrite -> (MP_add_zero_r mp). tauto.
  + apply rtn1_trans_n1_false with y; tauto.
  + rewrite <- (MP_add_assoc mp).
    apply rtn1_trans_n1_true; tauto.
Qed.

Lemma rt1n_rt: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y c,
  clos_refl_trans_1n mp R x c y -> clos_refl_trans mp R x c y.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_1n_false with y; tauto.
  + apply rt_trans_1n_true; tauto.
Qed.

Lemma rt_rt1n: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y c,
  clos_refl_trans mp R x c y -> clos_refl_trans_1n mp R x c y.
Proof.
  intros.
  induction H.
  + apply rt1n_step_false, H.
  + apply rt1n_step_true, H.
  + apply rt1n_refl.
  + apply rt1n_trans with y; tauto.
Qed.

Lemma rtn1_rt: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y c,
  clos_refl_trans_n1 mp R x c y -> clos_refl_trans mp R x c y.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_n1_false with y; tauto.
  + apply rt_trans_n1_true; tauto.
Qed.

Lemma rt_rtn1: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y c,
  clos_refl_trans mp R x c y -> clos_refl_trans_n1 mp R x c y.
Proof.
  intros.
  induction H.
  + apply rtn1_step_false, H.
  + apply rtn1_step_true, H.
  + apply rtn1_refl.
  + apply rtn1_trans with y; tauto.
Qed.

Lemma rt_rt1n_iff: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y c,
  clos_refl_trans mp R x c y <-> clos_refl_trans_1n mp R x c y.
Proof.
  split; intros.
  + apply rt_rt1n; auto.
  + apply rt1n_rt; auto.
Qed.

Lemma rt_rtn1_iff: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) x y c,
  clos_refl_trans mp R x c y <-> clos_refl_trans_n1 mp R x c y.
Proof.
  split; intros.
  + apply rt_rtn1; auto.
  + apply rtn1_rt; auto.
Qed.

Lemma rt_refl_zero: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x c,
  (c = MP_zero mp) -> clos_refl_trans mp R x c x.
Proof. intros. subst. apply rt_refl. Qed.

Lemma rt_trans_add: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c1 c2 c3,
    RT_R x c1 y ->
    c3 = MP_add mp c1 c2 ->
    RT_R y c2 z ->
    RT_R x c3 z.
Proof. intros. subst. apply rt_trans with y; tauto. Qed.

Lemma ind_1N: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x (P: A -> B -> Prop),
  P x (MP_zero mp) ->
  (forall y z c (IH: P y c), R z false y -> RT_R y c x -> P z c) ->
  (forall y z c (IH: P y c), R z true y -> RT_R y c x -> P z (MP_add mp (MP_one mp z y) c)) ->
  (forall y c, RT_R y c x -> P y c).
Proof.
  intros.
  subst RT_R.
  apply rt_rt1n in H3.
  induction H3; auto.
  apply H1 with y; auto.
  apply rt1n_rt; auto.
  apply H2; auto.
  apply rt1n_rt; auto.
Qed.

Lemma ind_N1: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x (P: A -> B -> Prop),
  P x (MP_zero mp) ->
  (forall y z c (IH: P y c), R y false z -> RT_R x c y -> P z c) ->
  (forall y z c (IH: P y c), R y true z -> RT_R x c y -> P z (MP_add mp c (MP_one mp y z))) ->
  (forall y c, RT_R x c y -> P y c).
Proof.
  intros.
  subst RT_R.
  apply rt_rtn1 in H3.
  induction H3; auto.
  apply H1 with y; auto.
  apply rtn1_rt; auto.
  apply H2; auto.
  apply rtn1_rt; auto.
Qed.

Lemma trans_1N_false: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c, R x false y -> RT_R y c z -> RT_R x c z.
Proof.
  intros.
  subst.
  apply rt_trans_1n_false with y; auto.
Qed.

Lemma trans_1N_true: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c c', R x true y -> RT_R y c z -> (c' = MP_add mp (MP_one mp x y) c) -> RT_R x c' z.
Proof.
  intros.
  subst.
  apply rt_trans_1n_true; auto.
Qed.

Lemma trans_1N: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c b c', R x b y ->
    (if b then c' = (MP_add mp (MP_one mp x y) c) else c' = c) ->
    RT_R y c z ->
    RT_R x c' z.
Proof.
  intros.
  destruct b; inversion H1; subst.
  apply (trans_1N_true _ _ _ R _ eq_refl x y z c _ H0 H2 eq_refl).
  apply (trans_1N_false _ _ _ R _ eq_refl x y z c H0 H2).
Qed.

Lemma trans_N1_false: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c, RT_R x c y -> R y false z -> RT_R x c z.
Proof.
  intros.
  subst.
  apply rt_trans_n1_false with y; auto.
Qed.

Lemma trans_N1_true: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c c', RT_R x c y -> R y true z -> c' = MP_add mp c (MP_one mp y z) -> RT_R x c' z.
Proof.
  intros.
  subst.
  apply rt_trans_n1_true; auto.
Qed.

Lemma trans_N1: forall A B (mp : mid_param A B) (R: A -> bool -> A -> Prop) (RT_R: A -> B -> A -> Prop),
  (RT_R = clos_refl_trans mp R) ->
  forall x y z c (b: bool) c', RT_R x c y ->
    (if b then c' = (MP_add mp c (MP_one mp y z)) else c' = c) ->
    R y b z ->
    RT_R x c' z.
Proof.
  intros.
  destruct b; inversion H1; subst.
  apply (trans_N1_true _ _ _ R _ eq_refl x y z c _ H0 H2 eq_refl).
  apply (trans_N1_false _ _ _ R _ eq_refl x y z c H0 H2).
Qed.

Ltac induction_1n H :=
  match type of H with
  | ?RT_R ?b ?c ?a =>
    revert_dependent_component b H;
    let b0 := fresh "b" in
    let c0 := fresh "c" in
    let EQb := fresh "EQb" in
    let EQc := fresh "EQc" in
    remember b as b0 eqn:EQb in H;
    remember c as c0 eqn:EQc in H;
    revert EQb EQc;
    revert_component b;
    revert_component c;
    match goal with
    | |- ?Q =>
      let Pbc := eval pattern c0 in Q in
      match Pbc with
      | ?Q' c0 =>
        let Pb := eval pattern b0 in Q' in
        match Pb with
        | ?P b0 =>
          revert b0 c0 H;
          refine (ind_1N _ _ _ _ RT_R eq_refl a P _ _ _);
          [ first [rewrite (MP_MP_zero _ _ _ _ _ _ _ eq_refl)| idtac];
            intros_until_EQ EQb;
            intros_until_EQ EQc;
            match goal with
            | |- ?Base =>
              let Base0 := fresh in
              remember Base as Base0 in |- *;
              first [ injection EQb; clear EQb; intros_and_subst Base0
                    | revert EQb; intros_and_subst Base0
                    | subst b0
                    | idtac ];
              subst Base0
            end;
            match goal with
            | |- ?Base =>
              let Base0 := fresh in
              remember Base as Base0 in |- *;
              first [ injection EQc; clear EQc; intros_and_subst Base0
                    | revert EQc; intros_and_subst Base0
                    | subst c0
                    | idtac ];
              subst Base0
            end
          | let b0 := fresh "x" in
            let c0 := fresh "c" in
            let H0 := fresh "H" in
            let IH := fresh "IHrt" in
            first [intros ?b b0 c0 IH H0 ? | intros ? b0 c0 IH H0 ?];
            intros_until_EQ EQb;
            intros_until_EQ EQc;
            subst b0;
            repeat progress
            match type of H0 with
            | _ ?y ?c ?x => destruct_to_form x y
            end;
            specialize_until_EQ IH;
            specialize_until_EQ IH
          | first [ rewrite (MP_MP_one _ _ _ _ _ _ _ eq_refl);
                    rewrite (MP_MP_add _ _ _ _ _ _ _ eq_refl)
                  | idtac];
            let b0 := fresh "x" in
            let c0 := fresh "c" in
            let H0 := fresh "H" in
            let IH := fresh "IHrt" in
            first [intros ?b b0 c0 IH H0 ? | intros ? b0 c0 IH H0 ?];
            intros_until_EQ EQb;
            intros_until_EQ EQc;
            subst b0;
            repeat progress
            match type of H0 with
            | _ ?y ?c ?x => destruct_to_form x y
            end;
            specialize_until_EQ IH;
            specialize_until_EQ IH
          ]
        end
      end
    end
  end.

Ltac induction_n1 H :=
  match type of H with
  | ?RT_R ?a ?c ?b =>
    revert_dependent_component b H;
    let b0 := fresh "b" in
    let c0 := fresh "c" in
    let EQb := fresh "EQb" in
    let EQc := fresh "EQc" in
    remember b as b0 eqn:EQb in H;
    remember c as c0 eqn:EQc in H;
    revert EQb EQc;
    revert_component b;
    revert_component c;
    match goal with
    | |- ?Q =>
      let Pbc := eval pattern c0 in Q in
      match Pbc with
      | ?Q' c0 =>
        let Pb := eval pattern b0 in Q' in
        match Pb with
        | ?P b0 =>
          revert b0 c0 H;
          refine (ind_N1 _ _ _ _ RT_R eq_refl a P _ _ _);
          [ first [rewrite (MP_MP_zero _ _ _ _ _ _ _ eq_refl)| idtac];
            intros_until_EQ EQb;
            intros_until_EQ EQc;
            match goal with
            | |- ?Base =>
              let Base0 := fresh in
              remember Base as Base0 in |- *;
              first [ injection EQb; clear EQb; intros_and_subst Base0
                    | revert EQb; intros_and_subst Base0
                    | subst b0
                    | idtac ];
              subst Base0
            end;
            match goal with
            | |- ?Base =>
              let Base0 := fresh in
              remember Base as Base0 in |- *;
              first [ injection EQc; clear EQc; intros_and_subst Base0
                    | revert EQc; intros_and_subst Base0
                    | subst c0
                    | idtac ];
              subst Base0
            end
          | let b0 := fresh "x" in
            let c0 := fresh "c" in
            let H0 := fresh "H" in
            let IH := fresh "IHrt" in
            first [intros ?b b0 c0 IH H0 ? | intros ? b0 c0 IH H0 ?];
            intros_until_EQ EQb;
            intros_until_EQ EQc;
            subst b0;
            subst c0;
            repeat progress
            match type of H0 with
            | _ ?x ?c ?y => destruct_to_form x y
            end;
            specialize_until_EQ IH;
            specialize_until_EQ IH
          | first [ rewrite (MP_MP_one _ _ _ _ _ _ _ eq_refl);
                    rewrite (MP_MP_add _ _ _ _ _ _ _ eq_refl)
                  | idtac];
            let b0 := fresh "x" in
            let c0 := fresh "c" in
            let H0 := fresh "H" in
            let IH := fresh "IHrt" in
            first [intros ?b b0 c0 IH H0 ? | intros ? b0 c0 IH H0 ?];
            intros_until_EQ EQb;
            intros_until_EQ EQc;
            subst b0;
            repeat progress
            match type of H0 with
            | _ ?x ?c ?y => destruct_to_form x y
            end;
            specialize_until_EQ IH;
            specialize_until_EQ IH
          ]
        end
      end
    end
  end.

Ltac transitivity_1n_false y :=
  match goal with
  | |- ?RT_R ?x ?c ?z =>
    refine (trans_1N_false _ _ _ _ RT_R eq_refl x y z c _ _)
  end.

Ltac transitivity_1n_true y c :=
  match goal with
  | |- ?RT_R ?x ?c' ?z =>
    first [ refine (trans_1N_true _ _ _ _ RT_R eq_refl x y z c c' _ _ eq_refl)
          | refine (trans_1N_true _ _ _ _ RT_R eq_refl x y z c c' _ _ _)]
  end.

Ltac etransitivity_1n :=
  match goal with
  | |- ?RT_R ?x ?c ?z =>
    match type of x with
    | ?A =>
      match type of c with
      | ?B => let y := fresh "y" in
              let b := fresh "b" in
              let c' := fresh "c'" in
              evar (y: A);
              evar (b: bool);
              evar (c': B);
              refine (trans_1N _ _ _ _ RT_R eq_refl x y z c' b c _ _ _);
              [ | first [ rewrite (MP_MP_one _ _ _ _ _ _ _ eq_refl);
                          rewrite (MP_MP_add _ _ _ _ _ _ _ eq_refl)
                        | idtac] | ];
              subst y b c'
      end
    end
  end.

Ltac transitivity_n1_false y :=
  match goal with
  | |- ?RT_R ?x ?c ?z =>
    refine (trans_N1_false _ _ _ _ RT_R eq_refl x y z c _ _)
  end.

Ltac transitivity_n1_true y c :=
  match goal with
  | |- ?RT_R ?x ?c' ?z =>
    first [ refine (trans_N1_true _ _ _ _ RT_R eq_refl x y z c c' _ _ eq_refl)
          | refine (trans_N1_true _ _ _ _ RT_R eq_refl x y z c c' _ _ _)]
  end.

Ltac etransitivity_n1 :=
  match goal with
  | |- ?RT_R ?x ?c ?z =>
    match type of x with
    | ?A =>
      match type of c with
      | ?B => let y := fresh "y" in
              let b := fresh "b" in
              let c' := fresh "c'" in
              evar (y: A);
              evar (b: bool);
              evar (c': B);
              refine (trans_N1 _ _ _ _ RT_R eq_refl x y z c' b c _ _ _);
              [ | first [ rewrite (MP_MP_one _ _ _ _ _ _ _ eq_refl);
                          rewrite (MP_MP_add _ _ _ _ _ _ _ eq_refl)
                        | idtac] | ];
              subst y b c'
      end
    end
  end.

Ltac rt_reflexivity :=
  match goal with
  | |- ?RT_R ?x ?c ?y =>
    refine (rt_refl_zero _ _ _ _ RT_R eq_refl x c eq_refl)
  end.

Ltac rt_transitivity y c1 c2 :=
  match goal with
  | |- ?RT_R ?x ?c ?z =>
    first [ refine (rt_trans_add _ _ _ _ RT_R eq_refl x y z c1 c2 c _ eq_refl _)
          | refine (rt_trans_add _ _ _ _ RT_R eq_refl x y z c1 c2 c _ _ _)]
  end.

Ltac rt_etransitivity :=
  match goal with
  | |- ?RT_R ?x ?c ?z =>
    match type of x with
    | ?A =>
      match type of c with
      | ?B => let y := fresh "y" in
              let c1 := fresh "c1" in
              let c2 := fresh "c2" in
              evar (y: A);
              evar (c1: B);
              evar (c2: B);
              refine (rt_trans_add _ _ _ _ RT_R eq_refl x y z c1 c2 c _ _ _);
              [ | first [ rewrite (MP_MP_add _ _ _ _ _ _ _ eq_refl)
                        | idtac] | ];
              subst y c1 c2
      end
    end
  end.

Definition extend_one {A B: Type} (one: A -> A -> B) (C: Type) : (C*A) -> (C*A) -> B
:= fun ca1 ca2 =>
     match ca1,ca2 with
     | (c1,a1),(c2,a2) => one a1 a2
     end.

(* Lemma extend_one_preserve : forall {A B: Type} (one: A -> A -> B) (C: Type) a1 a2 c1 c2,
  one a1 a2 =
  (extend_one one C) (c1,a1) (c2,a2).
Proof. intros. reflexivity. Qed. *)

Definition extend_mp {A B: Type} (mp: mid_param A B) (C: Type) : mid_param (C*A) B
:= match mp with
   | MP zero one add add_zero_l add_zero_r add_assoc => 
     MP zero (extend_one one C) add add_zero_l add_zero_r add_assoc
   end.

Definition multi_cstep {T: Type} (mp: mid_param state T): com * state -> T -> com * state -> Prop := 
  clos_refl_trans (extend_mp mp com) cstep.

Definition multi_cstep_cnt: com * state -> Z -> com * state -> Prop := 
  multi_cstep Z_mp.

Definition multi_cstep_trace: com * state -> list state -> com * state -> Prop :=
  multi_cstep List_mp.

Module TestRT.

Definition test_one (_ : Z * Z) (_ : Z * Z) : Z :=
  1.

Inductive test_step : (Z * Z) -> bool -> (Z * Z) -> Prop :=
  | TS_0 : forall a b1 b2, test_step (a, b1) false (a, b2)
  | TS_1 : forall a b, test_step (a, b) true (a + 1, b).

Definition multi_test_step: (Z * Z) -> Z -> (Z * Z) -> Prop := 
  clos_refl_trans (MP 0 test_one Z.add Z.add_0_l Z.add_0_r Zplus_assoc_reverse) test_step.

Example test_step_example: multi_test_step (1,2) 3 (4,5).
Proof.
  intros. rt_transitivity (2, 10) 1 2.
  { etransitivity_1n.
    + apply TS_0.
    + simpl. reflexivity.
    + etransitivity_1n.
      * apply TS_1.
      * unfold test_one. instantiate (c':=0). reflexivity.
      * rt_reflexivity. }
  rt_etransitivity.
  { etransitivity_n1.
    + etransitivity_n1.
      * rt_reflexivity.
      * unfold test_one. simpl. instantiate (b0:=false). reflexivity.
      * apply TS_0.
    + unfold test_one. simpl. instantiate (b:=true). reflexivity.
    + apply TS_1. }
  { instantiate (c2:=1). reflexivity. }
  transitivity_1n_false (3,6).
  { instantiate (1:=0). apply TS_0. }
  transitivity_1n_true (4,6) 0.
  { apply TS_1. }
  transitivity_n1_false (4,6).
  { rt_reflexivity. }
  apply TS_0.
Qed.

Example test_step_equiv_minus_n1: forall a1 b1 a2 b2 c, multi_test_step (a1,b1) c (a2,b2) -> a2-a1=c.
Proof.
  intros.
  remember (a1,b1) as ab1.
  remember (a2,b2) as ab2.
  revert Heqab1 Heqab2.
  revert a1 b1 a2 b2.
  induction_n1 H; intros; subst.
  - inversion Heqab2. lia.
  - inversion H; subst.
    repeat specialize_until_EQ IHrt.
    lia.
  - inversion H; subst.
    unfold test_one.
    repeat specialize_until_EQ IHrt.
    lia.
Qed.

Example test_step_equiv_minus_1n: forall a1 b1 a2 b2 c, multi_test_step (a1,b1) c (a2,b2) -> a2-a1=c.
Proof.
  intros.
  remember (a1,b1) as ab1.
  remember (a2,b2) as ab2.
  revert Heqab1 Heqab2.
  revert a1 b1 a2 b2.
  induction_1n H; intros; subst.
  - inversion Heqab2. lia.
  - inversion H; subst.
    repeat specialize_until_EQ IHrt.
    lia.
  - inversion H; subst.
    unfold test_one.
    repeat specialize_until_EQ IHrt.
    lia.
Qed.

Example test_step_equiv_minus: forall a1 b1 a2 b2 c, multi_test_step (a1,b1) c (a2,b2) -> a2-a1=c.
Proof.
  intros.
  remember (a1,b1) as ab1.
  remember (a2,b2) as ab2.
  revert Heqab1 Heqab2.
  revert a1 b1 a2 b2.
  induction H; intros; simpl; subst.
  - inversion H. subst. lia.
  - inversion H. subst. unfold test_one. lia.
  - inversion Heqab2. lia.
  - destruct y.
    repeat specialize_until_EQ IHclos_refl_trans1.
    repeat specialize_until_EQ IHclos_refl_trans2.
    lia.
Qed.

End TestRT.

End TerStep.
