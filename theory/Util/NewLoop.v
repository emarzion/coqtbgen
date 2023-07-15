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

  step_measure : forall x, measure (step x) <= measure x
  }.

Arguments measure {_} _ _.
Arguments step {_} _ _.

Arguments step_measure {_} _ _.

Fixpoint loop_aux {X} (l : loop_data X) (x : X)
  (a : Acc (Wf_nat.ltof _ (measure l)) x) {struct a} : X.
Proof.
  destruct (le_lt_eq_dec _ _ (step_measure l x)).
  - destruct a.
    apply (loop_aux X l (step l x)).
    apply H. exact l0.
  - exact x.
Defined.

Fixpoint loop_aux_ext {X} (l : loop_data X) (x : X)
  (a : Acc (Wf_nat.ltof _ (measure l)) x) {struct a} :
  forall a',
  loop_aux l x a = loop_aux l x a'.
Proof.
  destruct a, a'; simpl.
  destruct le_lt_eq_dec.
  - apply loop_aux_ext.
  - reflexivity.
Defined.

Definition loop {X} (l : loop_data X) (x : X) : X :=
  loop_aux l x (Wf_nat.well_founded_ltof X (measure l) x).

Lemma loop_eq {X} (l : loop_data X) (x : X) :
  loop l x =
    match le_lt_eq_dec _ _ (step_measure l x) with
    | left _ => loop l (step l x)
    | right _ => x
    end.
Proof.
  unfold loop at 1.
  unfold loop_aux.
  destruct (Wf_nat.well_founded_ltof X (measure l) x).
  - destruct (le_lt_eq_dec).
    + unfold loop.
      unfold loop_aux.
      apply loop_aux_ext.
    + reflexivity.
Defined.



Lemma loop_measure_aux {X} (l : loop_data X) : forall n x, n = measure l x ->
  measure l (loop l x) = measure l (step l (loop l x)).
Proof.
  intro n.
  induction (Wf_nat.lt_wf n) as [n _ IHn].
  intros.
  rewrite loop_eq.
  destruct le_lt_eq_dec.
  - rewrite (IHn (measure l (step l x))); [reflexivity| |reflexivity].
    rewrite H.
    pose (step_measure l x). lia.
  - symmetry; exact e.
Qed.

Lemma loop_measure {X} (l : loop_data X) : forall x,
  measure l (loop l x) = measure l (step l (loop l x)).
Proof.
  intros.
  eapply loop_measure_aux; reflexivity.
Qed.

Lemma loop_iter_aux {X} (l : loop_data X) : forall n x, n = measure l x ->
  {n : nat & loop l x = Nat.iter n (step l) x}.
Proof.
  intro n.
  induction (Wf_nat.lt_wf n) as [n _ IHn].
  intros.
  rewrite loop_eq.
  destruct le_lt_eq_dec.
  - assert (pf : measure l (step l x) < n).
    { rewrite H.
      pose proof (step_measure l x); lia.
    }
    destruct (IHn (measure l (step l x)) pf (step l x) eq_refl) as [k Hk].
    exists (S k).
    rewrite Hk.
    simpl.
    apply iter_lemma.
  - exists 0; reflexivity.
Defined.

Lemma loop_iter {X} (l : loop_data X) : forall x,
  {n : nat & loop l x = Nat.iter n (step l) x}.
Proof.
  intro x.
  exact (loop_iter_aux l (measure l x) x eq_refl).
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
