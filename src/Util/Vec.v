Require Import Arith.
Import Nat.

Require Import Games.Util.Fin.
Require Import Games.Util.UIP.

Fixpoint Vec (X : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S m => X * Vec X m
  end.

Fixpoint vreplicate {X} {n} (x : X) : Vec X n :=
  match n with
  | 0 => tt
  | S m => (x, vreplicate x)
  end.

Fixpoint vaccess {X} {n} : Fin n -> Vec X n -> X :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => fst
    | inr j => fun v => vaccess j (snd v)
    end
  end.

Fixpoint vupdate {X} {n} : Fin n -> X -> Vec X n -> Vec X n :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => fun x v => (x, snd v)
    | inr j => fun x v => (fst v, vupdate j x (snd v))
    end
  end.

Lemma vaccess_vupdate_eq : forall {X} {n}
  (i : Fin n) v (x : X),
  vaccess i (vupdate i x v) = x.
Proof.
  intros X n i v x.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + simpl.
      apply IHn.
Qed.

Lemma vaccess_vupdate_neq : forall {X} {n}
  (i j : Fin n) v (x : X), i <> j ->
  vaccess i (vupdate j x v) = vaccess i v.
Proof.
  intros X n i j v x ij_neq.
  induction n.
  - destruct i.
  - destruct i as [[]|i'];
    destruct j as [[]|j'].
    + now elim ij_neq.
    + reflexivity.
    + reflexivity.
    + simpl.
      apply IHn.
      intro; elim ij_neq.
      congruence.
Qed.
