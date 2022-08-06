Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import CoqChess.Util.Rel.
Require Import CoqChess.Util.Dist.
Require Import CoqChess.Util.SBetween.
Require Import CoqChess.Util.Dec.
Require Import CoqChess.Util.UIP.

Definition Fin (n : nat) : Type :=
  { x : nat & x < n }.

Definition val : forall {n}, Fin n -> nat :=
  fun n => @projT1 nat (fun x => x < n).

Definition val_small : forall {n} (i : Fin n), val i < n :=
  fun n => @projT2 nat (fun x => x < n).

Lemma val_inj : forall {n} (i j : Fin n),
  val i = val j -> i = j.
Proof.
  induction n; intros.
  { destruct i; lia. }
  { destruct i,j; simpl in *.
    destruct H.
    f_equal; apply UIP.
  }
Qed.

Definition Fin_0 {n} : Fin (S n).
Proof.
  exists 0.
  lia.
Defined.

Definition Fin_S {n} : Fin n -> Fin (S n).
Proof.
  intros [i Hi].
  exists (S i).
  lia.
Defined.

Definition Fin_case {n} : forall (i : Fin (S n)),
  (i = Fin_0) + {j : Fin n & i = Fin_S j}.
Proof.
  intro i.
  destruct (val i) eqn:?.
  - left.
    apply val_inj; auto.
  - right.
    destruct i as [i Hi].
    destruct i.
    + discriminate.
    + simpl in *.
      assert (i < n) as pf by lia.
      exists (existT _ i pf).
      apply val_inj.
      reflexivity.
Defined.

Fixpoint all_fin n : list (Fin n) :=
  match n with
  | 0 => []
  | S m => Fin_0 :: List.map Fin_S (all_fin m)
  end.

Lemma all_fin_In (n : nat) : forall i : Fin n,
  In i (all_fin n).
Proof.
  induction n.
  - intros [n Hn]; lia.
  - intro i.
    destruct (Fin_case i).
    + left; congruence.
    + right.
      destruct s as [j Hj].
      rewrite Hj.
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
    right; intros [[] _]; lia.
  - intros P Pd.
    destruct (Pd Fin_0).
    + left; exists Fin_0; auto.
    + destruct (IHn (fun j => P (Fin_S j))).
      * intro; apply Pd.
      * left; destruct e as [j Hj].
        exists (Fin_S j); auto.
      * right; intros [i Hi].
        destruct (Fin_case i) as [|[j Hj]].
        ** congruence.
        ** apply n1.
           exists j; congruence.
Defined.


