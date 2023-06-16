Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import Games.Util.Rel.
Require Import Games.Util.Dist.
Require Import Games.Util.SBetween.
Require Import Games.Util.Dec.
Require Import Games.Util.UIP.

Fixpoint Fin n : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Fixpoint Fin_of_nat {m} (n : nat) : Fin (n + S m) :=
  match n with
  | 0 => inl tt
  | S k => inr (Fin_of_nat k)
  end.

Fixpoint val {n} : Fin n -> nat :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl tt => 0
    | inr j => S (val j)
    end
  end.

(* Definition val_small : forall {n} (i : Fin n), val i < n :=
  fun n => @projT2 nat (fun x => x < n). *)

Lemma val_inj : forall {n} (i j : Fin n),
  val i = val j -> i = j.
Proof.
  induction n; intros.
  { destruct i. }
  { destruct i as [[]|i'];
    destruct j as [[]|j'].
    { reflexivity. }
    { discriminate. }
    { discriminate. }
    { rewrite (IHn i' j').
      { reflexivity. }
      { now inversion H. }
    }
  }
Qed.

Fixpoint all_fin n : list (Fin n) :=
  match n with
  | 0 => []
  | S m => inl tt :: map inr (all_fin m)
  end.

Lemma all_fin_In (n : nat) : forall i : Fin n,
  In i (all_fin n).
Proof.
  induction n.
  - intros [].
  - intros [[]|j].
    + left; reflexivity.
    + right.
      apply in_map.
      apply IHn.
Qed.

Definition fin_dist {n} : Fin n -> Fin n -> nat :=
  fun i j => dist (val i) (val j).

Lemma fin_dist_sym {n} : forall i j : Fin n,
  fin_dist i j = fin_dist j i.
Proof.
  intros.
  apply dist_sym.
Qed.

Definition fin_sbetween {n} : Rel 3 (Fin n) :=
  fun i j k => sbetween (val i) (val j) (val k).

Lemma fin_sbetween_sym {n} : forall i j k : Fin n,
  fin_sbetween i j k -> fin_sbetween k j i.
Proof.
  intros i j k; unfold fin_sbetween; apply sbetween_sym.
Qed.

#[export] Instance Fin_Discrete : forall {n},
  Discrete (Fin n).
Proof.
  intros.
  constructor.
  intros i j.
  destruct (Nat.eq_dec (val i) (val j)).
  - left; apply val_inj; auto.
  - right; congruence.
Defined.

#[export] Instance Fin_Exhaustible : forall {n},
  Exhaustible (Fin n).
Proof.
  intro n.
  constructor.
  induction n.
  - intros P _.
    right; intros [[] _].
  - intros P Pd.
    destruct (Pd (inl tt)).
    + left; exists (inl tt); easy.
    + destruct (IHn (fun i => P (inr i)) (fun i => Pd (inr i))).
      * left. destruct e as [i Hi].
        exists (inr i); exact Hi.
      * right; intros [i Hi].
        destruct i as [[]|j].
        ** exact (n0 Hi).
        ** apply n1.
           exists j.
           exact Hi.
Defined.
