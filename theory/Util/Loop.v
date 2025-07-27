Require Import Lia.
Require Import Compare_dec.

Lemma iter_lemma {X} (f : X -> X) (k : nat) (x : X) :
  Nat.iter k f (f x) = f (Nat.iter k f x).
Proof.
  induction k.
  - reflexivity.
  - simpl; congruence.
Qed.

Record loop_data (X : Type) : Type := {
  measure : X -> nat;
  step : X -> X;

  measure_bound : exists B, forall x, measure x <= B;

  step_measure : forall x, measure x <= measure (step x)
  }.

Arguments measure {_} _ _.
Arguments step {_} _ _.

Arguments step_measure {_} _ _.
Arguments measure_bound {_} _.

Definition rel {X} (l : loop_data X) : X -> X -> Prop :=
  fun a b => measure l b < measure l a.

Fixpoint acc_contra {X} (R S : X -> X -> Prop)
  (f : forall x y, R x y -> S x y) {x}
  (a : Acc S x) {struct a} : Acc R x.
Proof.
  destruct a as [accs].
  constructor.
  intros y r.
  apply f in r.
  apply accs in r.
  apply (acc_contra _ _ _ f).
  exact r.
Defined.

Lemma wf_impl {X} (R S : X -> X -> Prop) :
  (forall x y, R x y -> S x y) ->
  well_founded S ->
  well_founded R.
Proof.
  intros RS HS x.
  specialize (HS x).
  exact (acc_contra R S RS HS).
Qed.

Fixpoint acc_func {X Y} (f : X -> Y)
  (R : Y -> Y -> Prop) {x} (a : Acc R (f x))
  {struct a} : Acc (fun x1 x2 => R (f x1) (f x2)) x.
Proof.
  destruct a.
  constructor.
  intros x' Rx.
  apply H in Rx.
  apply acc_func in Rx.
  auto.
Qed.

Lemma wf_func {X Y} (f : X -> Y)
  (R : Y -> Y -> Prop) (R_wf : well_founded R) :
  well_founded (fun x x' => R (f x) (f x')).
Proof.
  intro x.
  apply acc_func.
  apply R_wf.
Qed.

Lemma rel_wf {X} (l : loop_data X) : well_founded (rel l).
Proof.
  destruct (measure_bound l) as [B HB].
  apply wf_impl with (S := fun n m => measure l m < measure l n <= B).
  - intros; split; auto.
  - apply (wf_func (measure l) (fun a b => b < a <= B)).
    apply PeanoNat.Nat.gt_wf.
Qed.

Fixpoint loop_aux {X} (l : loop_data X) (x : X)
  (a : Acc (rel l) x) {struct a} : X.
  destruct (le_lt_eq_dec _ _ (step_measure l x)).
  - destruct a as [accs].
    apply (loop_aux _ l (step l x)).
    apply accs. exact l0.
  - exact x.
Defined.

Fixpoint loop_aux_ext {X} (l : loop_data X) (x : X)
  (a : Acc (rel l) x) {struct a} :
  forall a',
  loop_aux l x a = loop_aux l x a'.
Proof.
  destruct a, a'; simpl.
  destruct le_lt_eq_dec.
  - apply loop_aux_ext.
  - reflexivity.
Defined.

Definition loop {X} (l : loop_data X) (x : X) : X.
  apply (
  loop_aux l x).
  apply rel_wf.
Defined.

Lemma loop_eq {X} (l : loop_data X) (x : X) :
  loop l x =
    match le_lt_eq_dec _ _ (step_measure l x) with
    | left _ => loop l (step l x)
    | right _ => x
    end.
Proof.
  unfold loop at 1.
  unfold loop_aux.
  destruct (rel_wf l x).
  - destruct (le_lt_eq_dec).
    + unfold loop.
      unfold loop_aux.
      apply loop_aux_ext.
    + reflexivity.
Defined.

Lemma loop_measure_aux {X} (l : loop_data X) : forall n x, n = measure l x ->
  measure l (loop l x) = measure l (step l (loop l x)).
Proof.
  destruct (measure_bound l) as [B HB].
  intro n.
  induction (PeanoNat.Nat.gt_wf B n) as [n _ IHn].
  intros.
  rewrite loop_eq.
  destruct le_lt_eq_dec.
  - rewrite (IHn (measure l (step l x))); [reflexivity| |reflexivity].
    rewrite H.
    split; auto.
  - symmetry; auto.
Qed.

Lemma loop_measure {X} (l : loop_data X) : forall x,
  measure l (loop l x) = measure l (step l (loop l x)).
Proof.
  intros.
  eapply loop_measure_aux; reflexivity.
Qed.

Lemma loop_iter {X} (l : loop_data X) : forall x,
  {n : nat & loop l x = Nat.iter n (step l) x}.
Proof.
  intro x.
  induction (rel_wf l x) as [x _ IHx].
  rewrite loop_eq.
  destruct le_lt_eq_dec.
  - destruct (IHx (step l x)) as [n Hn].
    + auto.
    + exists (S n).
      simpl; rewrite Hn.
      apply iter_lemma.
  - exists 0; reflexivity.
Defined.

Record validity_data {X} (l : loop_data X) : Type := {
  valid : X -> Type;
  step_valid : forall x, valid x -> valid (step l x)
  }.

Arguments valid {_} {_} _ _.
Arguments step_valid {_} _ {_} _.

Lemma iter_step_valid {X} (l : loop_data X) (v : validity_data l) :
  forall n x, valid v x -> valid v (Nat.iter n (step l) x).
Proof.
  induction n; intros x x_v.
  - exact x_v.
  - simpl.
    apply step_valid.
    apply IHn.
    exact x_v.
Defined.

Lemma loop_valid {X} (l : loop_data X) (v : validity_data l) : forall x,
  valid v x -> valid v (loop l x).
Proof.
  intros.
  destruct (loop_iter l x) as [n n_v].
  rewrite n_v.
  now apply iter_step_valid.
Defined.
