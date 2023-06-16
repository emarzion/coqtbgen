Require Import Lia.
From Equations Require Import Equations.

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

Equations loop {X} (l : loop_data X) (x : X) : X by wf (measure l x) :=
  loop l x :=
    match PeanoNat.Nat.eq_dec (measure l x) (measure l (step l x)) with
    | left _ => x
    | right _ => loop l (step l x)
    end.
Next Obligation.
  pose proof (step_measure l x).
  lia.
Defined.

Global Transparent loop.

Lemma loop_measure_aux {X} (l : loop_data X) : forall n x, n = measure l x ->
  measure l (loop l x) = measure l (step l (loop l x)).
Proof.
  intro n.
  induction (lt_wf n) as [n _ IHn].
  intros.
  rewrite loop_equation_1.
  destruct PeanoNat.Nat.eq_dec.
  - auto.
  - erewrite IHn; [| |reflexivity].
    + reflexivity.
    + rewrite H.
      pose (step_measure l x); lia.
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
  induction (lt_wf n) as [n _ IHn].
  intros.
  rewrite loop_equation_1.
  destruct PeanoNat.Nat.eq_dec.
  - exists 0; reflexivity.
  - assert (pf : measure l (step l x) < n).
    { rewrite H.
      pose proof (step_measure l x); lia.
    }
    destruct (IHn (measure l (step l x)) pf (step l x) eq_refl) as [k Hk].
    exists (S k).
    rewrite Hk.
    simpl.
    apply iter_lemma.
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
