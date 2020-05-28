Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.DenotationalSemantics.

(** In this task, you should first prove a general theorem which can be used to
    prove an equivalence between two recursively defined semantics, and another
    general theorem which can be used to prove an equivalence between a
    recursively defined program semantics and a small step semantics.

    Then, you need to prove the equivalence among three denotational program
    semantics and a small step semantics. *)

(* Some try before the general theorem *)

Definition Bin_Step_Equiv (X : state -> state -> Prop) 
                          (Y : state -> Z -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists z, Y st1 z st2).
  
Definition Bin_Trace_Equiv (X : state -> state -> Prop) 
                           (Y : state -> list state -> state -> Prop) : Prop :=
  forall st1 st2, X st1 st2 <-> (exists l, Y st1 l st2).
  
Definition sem_equiv {X Y: Type} 
                     (ceval_X: com -> X)
                     (ceval_Y: com -> Y)
                     (RXY: X -> Y -> Prop) : Prop :=
  forall c, RXY (ceval_X c) (ceval_Y c).

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


Theorem equiv_between_normal_time:
  sem_equiv (BinRel.ceval) (StepCnt.ceval) (Bin_Step_Equiv).
Proof.
  unfold sem_equiv, Bin_Step_Equiv.
  split; revert st1 st2.
  (* First half: BinRel.ceval --> StepCnt.ceval *)
  + induction c; intros.
    - exists 0. (* inversion H; subst. *)
      firstorder.
    - exists 1. (* inversion H; subst. *)
      firstorder.
    - inversion H as [st3 H0]. destruct H0.
      specialize (IHc1 _ _ H0). destruct IHc1 as [a1 IHc1].
      specialize (IHc2 _ _ H1). destruct IHc2 as [a2 IHc2].
      exists (a1 + a2).
      simpl; unfold StepCnt.seq_sem.
      exists a1, a2, st3.
      tauto.
    - simpl in H. 
      unfold BinRel.if_sem in H.
      destruct H; destruct H as [st1' [HTest H]].
      (* 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2
         prove them respectively. *)
      * destruct HTest. subst st1'.
        specialize (IHc1 _ _ H). destruct IHc1 as [a IHc1].
        exists (a + 1).
        simpl. left. (* beval b st1 --> c1 *)
        exists 1, a, st1.
        firstorder.
      * destruct HTest. subst st1'.
        specialize (IHc2 _ _ H). destruct IHc2 as [a IHc2].
        exists (a + 1).
        simpl. right. (* beval (! b) st1 --> c2 *)
        exists 1, a, st1.
        firstorder.
    - simpl in H.
      unfold BinRel.loop_sem, Relation_Operators.omega_union in H.
      destruct H as [n H].
      (* As 'n' is unknown, prove this by another induction. *)
      revert st1 st2 H.
      induction n; intros.
      * destruct H as [Hst Hb].
        exists 1. (* In total 1 step *)
        simpl. exists O. (* In total 0 iters *)
        firstorder.
      * simpl in H.
        unfold Relation_Operators.concat, Relation_Operators.test_rel in H.
        destruct H as [st1' [[Hst Hb] [st3 [H1 H2]]]].
        subst st1'.
        specialize (IHc _ _ H1).
        destruct IHc as [ac IHc].
        specialize (IHn _ _ H2).
        destruct IHn as [an IHn].
        clear H1 H2 n.
        simpl in IHn.
        unfold StepCnt.loop_sem, StepCnt.omega_union_sem in IHn.
        (* Assume doing 'While b Do c EndWhile' takes [n_iter] iters
           from st3 to st2. 
           Known that 'ceval c st1 st3', and 'beval b st1', we can
           assert that it takes [n_iter + 1] iters in the process of
           'While b Do c EndWhile' from st1 to st2. *)
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
        firstorder.
  (* Second half: StepCnt.ceval --> BinRel.ceval *)
  + induction c; intros.
    - destruct H. (* inversion H; subst. *)
      firstorder.
    - destruct H. (* inversion H; subst. *)
      firstorder.
    - destruct H as [a H]. simpl in H.
      unfold StepCnt.seq_sem in H.
      destruct H as [a1 [a2 [st3 [H1' [H2' Ha]]]]].
      assert (exists (t1 : Z), StepCnt.ceval c1 st1 t1 st3) as H1
        by (exists a1; exact H1').
      specialize (IHc1 _ _ H1).
      assert (exists (t2 : Z), StepCnt.ceval c2 st3 t2 st2) as H2
        by (exists a2; exact H2').
      specialize (IHc2 _ _ H2).
      clear H1' H2' H1 H2 Ha a a1 a2.
      firstorder.
    - destruct H as [a H].
      simpl in H.
      unfold StepCnt.if_sem in H.
      (* 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2 *)
      (* These 'destruct' are just to split this 'ceval' into 2
           hypothesis: one for 'beval b/(! b) st1', another for
           the execution of c1/c2.
         There are a lot of integers a_, standing for the number
           of steps in the execution process, which makes it 
           looks complicated. But they are actually of no use in
           the proof, so we can clear them out. *)
      destruct H; 
        destruct H as [a0 [a1 [st1' [HTest [HStep' Ha]]]]];
        destruct HTest as [Hst [Hb ?]];
        subst st1' a0 a.
      * assert (exists (t1 : Z), StepCnt.ceval c1 st1 t1 st2) as HStep
          by (exists a1; exact HStep').
        specialize (IHc1 _ _ HStep).
        clear IHc2 HStep HStep' a1.
        simpl. left. (* beval b st1 --> c1 *)
        exists st1.
        firstorder.
      * assert (exists (t2 : Z), StepCnt.ceval c2 st1 t2 st2) as HStep
          by (exists a1; exact HStep').
        specialize (IHc2 _ _ HStep).
        clear IHc1 HStep HStep' a1.
        simpl. right. (* beval (! b) st1 --> c2 *)
        exists st1.
        firstorder.
    - destruct H as [a H].
      simpl in H.
      unfold StepCnt.loop_sem, StepCnt.omega_union_sem in H.
      destruct H as [n H].
      revert a st1 st2 H.
      induction n; intros.
      * inversion H.
        exists O. (* In total 0 iters *)
        firstorder.
      * destruct H as [a0 [a1 [st1' [HTest H]]]].
        destruct HTest as [Hst [Hb Ha0]].
        destruct H as [[ac [an [st3 [Hc' [Hn Ha2]]]]] Ha1].
        subst st1' a0 a1 a.
        assert (exists a : Z, StepCnt.ceval c st1 a st3) as Hc
          by (exists ac; exact Hc').
        specialize (IHc _ _ Hc).
        specialize (IHn _ _ _ Hn).
        clear Hc Hn Hc' ac an n.
        pose proof BinRel_ceval_fold_while _ _ _ _ _ Hb IHc IHn.
        exact H.
Qed.
(* Not using the lemma, the proof becomes:
        unfold BinRel.loop_sem, Relation_Operators.omega_union in IHn.
        (* Assume doing 'While b Do c EndWhile' takes [n_iter] iters
           from st3 to st2. 
           Known that 'ceval c st1 st3', and 'beval b st1', we can
           assert that it takes [n_iter + 1] iters in the process of
           'While b Do c EndWhile' from st1 to st2. *)
        destruct IHn as [n_iter IHn].
        simpl.
        unfold BinRel.loop_sem, Relation_Operators.omega_union.
        exists (S n_iter).
        firstorder. 
   Also not very complicated. *)


Theorem equiv_between_normal_trace:
  sem_equiv (BinRel.ceval) (Trace.ceval) (Bin_Trace_Equiv).
Proof.
  unfold sem_equiv, Bin_Trace_Equiv.
  split; revert st1 st2.
  (* First half: BinRel.ceval --> Trace.ceval *)
  + induction c; intros.
    - exists nil. (* inversion H; subst. *)
      firstorder.
    - exists (st2 :: nil). (* inversion H; subst. *)
      firstorder.
    - inversion H as [st3 H0]. destruct H0.
      specialize (IHc1 _ _ H0). destruct IHc1 as [l1 IHc1].
      specialize (IHc2 _ _ H1). destruct IHc2 as [l2 IHc2].
      exists (l1 ++ l2).
      simpl; unfold StepCnt.seq_sem.
      exists l1, l2, st3.
      tauto.
    - simpl in H. 
      unfold BinRel.if_sem in H.
      destruct H; destruct H as [st1' [HTest H]].
      (* 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2
         prove them respectively. *)
      * destruct HTest. subst st1'.
        specialize (IHc1 _ _ H). destruct IHc1 as [l IHc1].
        exists ((st1 :: nil) ++ l).
        simpl. left. (* beval b st1 --> c1 *)
        exists (st1 :: nil), l, st1.
        firstorder.
      * destruct HTest. subst st1'.
        specialize (IHc2 _ _ H). destruct IHc2 as [l IHc2].
        exists ((st1 :: nil) ++ l).
        simpl. right. (* beval (! b) st1 --> c2 *)
        exists (st1 :: nil), l, st1.
        firstorder.
    - simpl in H.
      unfold BinRel.loop_sem, Relation_Operators.omega_union in H.
      destruct H as [n H].
      (* As 'n' is unknown, prove this by another induction. *)
      revert st1 st2 H.
      induction n; intros.
      * destruct H as [Hst Hb].
        exists (st1 :: nil). (* In total 1 step *)
        simpl. exists O. (* In total 0 iters *)
        firstorder.
      * simpl in H.
        unfold Relation_Operators.concat, Relation_Operators.test_rel in H.
        destruct H as [st1' [[Hst Hb] [st3 [H1 H2]]]].
        subst st1'.
        specialize (IHc _ _ H1).
        destruct IHc as [lc IHc].
        specialize (IHn _ _ H2).
        destruct IHn as [ln IHn].
        clear H1 H2 n.
        simpl in IHn.
        unfold Trace.loop_sem, Trace.omega_union_sem in IHn.
        (* Assume doing 'While b Do c EndWhile' takes [n_iter] iters
           from st3 to st2. 
           Known that 'ceval c st1 st3', and 'beval b st1', we can
           assert that it takes [n_iter + 1] iters in the process of
           'While b Do c EndWhile' from st1 to st2. *)
        destruct IHn as [n_iter IHn]. 
        exists ((st1 :: nil) ++ lc ++ ln).
        simpl.
        unfold StepCnt.loop_sem, StepCnt.omega_union_sem.
        exists (S n_iter).
        simpl.
        unfold Trace.test_sem, Trace.seq_sem.
        exists (st1 :: nil), (lc ++ ln), st1.
        split; [tauto | split; [| firstorder] ].
        exists lc, ln, st3.
        firstorder.
  (* Second half: StepCnt.ceval --> BinRel.ceval *)
  + induction c; intros.
    - destruct H. (* inversion H; subst. *)
      firstorder.
    - destruct H. (* inversion H; subst. *)
      firstorder.
    - destruct H as [l H]. simpl in H.
      unfold StepCnt.seq_sem in H.
      destruct H as [l1 [l2 [st3 [H1' [H2' Hl]]]]].
      assert (exists (t1 : list state), Trace.ceval c1 st1 t1 st3) as H1
        by (exists l1; exact H1').
      specialize (IHc1 _ _ H1).
      assert (exists (t2 : list state), Trace.ceval c2 st3 t2 st2) as H2
        by (exists l2; exact H2').
      specialize (IHc2 _ _ H2).
      clear H1' H2' H1 H2 Hl l l1 l2.
      firstorder.
    - destruct H as [l H].
      simpl in H.
      unfold Trace.if_sem in H.
      (* 2 cases: beval b st1 --> c1 ; beval (! b) st1 --> c2 *)
      (* These 'destruct' are just to split this 'ceval' into 2
           hypothesis: one for 'beval b/(! b) st1', another for
           the execution of c1/c2.
         There are a lot of integers a_, standing for the number
           of steps in the execution process, which makes it 
           looks complicated. But they are actually of no use in
           the proof, so we can clear them out. *)
      destruct H; 
        destruct H as [l0 [l1 [st1' [HTest [HStep' Hl]]]]];
        destruct HTest as [Hst [Hb ?]];
        subst st1' l0 l.
      * assert (exists (t1 : list state), Trace.ceval c1 st1 t1 st2) as HStep
          by (exists l1; exact HStep').
        specialize (IHc1 _ _ HStep).
        clear IHc2 HStep HStep' l1.
        simpl. left. (* beval b st1 --> c1 *)
        exists st1.
        firstorder.
      * assert (exists (t2 : list state), Trace.ceval c2 st1 t2 st2) as HStep
          by (exists l1; exact HStep').
        specialize (IHc2 _ _ HStep).
        clear IHc1 HStep HStep' l1.
        simpl. right. (* beval (! b) st1 --> c2 *)
        exists st1.
        firstorder.
    - destruct H as [l H].
      simpl in H.
      unfold Trace.loop_sem, Trace.omega_union_sem in H.
      destruct H as [n H].
      revert l st1 st2 H.
      induction n; intros.
      * inversion H.
        exists O. (* In total 0 iters *)
        firstorder.
      * destruct H as [l0 [l1 [st1' [HTest H]]]].
        destruct HTest as [Hst [Hl0 Hb]].
        destruct H as [[lc [ln [st3 [Hc' [Hn Hl2]]]]] Hl1].
        subst st1' l0 l1 l.
        assert (exists (t : list state), Trace.ceval c st1 t st3) as Hc
          by (exists lc; exact Hc').
        specialize (IHc _ _ Hc).
        specialize (IHn _ _ _ Hn).
        clear Hc Hn Hc' lc ln n.
        pose proof BinRel_ceval_fold_while _ _ _ _ _ Hb IHc IHn.
        exact H.
Qed.


(* General Theorem for equivalence between two recursively defined semantics *)

