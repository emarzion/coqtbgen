Require Import Arith.
Import Nat.

Require Import CoqChess.Util.Fin.
Require Import CoqChess.Util.UIP.

Fixpoint Vec (X : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S m => X * Vec X m
  end.

Fixpoint access {X} {n} : forall i, i < n -> Vec X n -> X :=
  match n with
  | 0 => fun i pf =>
    match nlt_0_r i pf with
    end
  | S m => fun i =>
    match i with
    | 0 => fun _ => fst
    | S j => fun pf v => access j (lt_S_n j m pf) (snd v)
    end
  end.

Definition fin_vaccess {X} {n} : Fin n -> Vec X n -> X :=
  fun '(existT _ i pf) => access i pf.

Fixpoint update {X} {n} : forall i, i < n -> X -> Vec X n -> Vec X n :=
  match n with
  | 0 => fun i pf =>
    match nlt_0_r i pf with
    end
  | S m => fun i =>
    match i with
    | 0 => fun _ x v => (x, snd v)
    | S j => fun pf x v => (fst v, update j
      (lt_S_n j m pf) x (snd v))
    end
  end.

Definition fin_vupdate {X} {n} : Fin n -> X -> Vec X n -> Vec X n :=
  fun '(existT _ i pf) => update i pf.

Lemma access_update_eq : forall {X} {n}
  i (pf : i < n) v (x : X),
  access i pf (update i pf x v) = x.
Proof.
  intro X.
  induction n; intros.
  { inversion pf. }
  { destruct i; simpl; auto. }
Qed.

Lemma access_update_neq : forall {X} {n}
  i (pf : i < n) j (pf' : j < n) v (x : X),
  i <> j -> access i pf (update j pf' x v)
  = access i pf v.
Proof.
  intro X.
  induction n; intros.
  { inversion pf. }
  { destruct i, j; auto.
    { elim H; auto. }
    { simpl.
      apply IHn; auto.
    }
  }
Qed.

Lemma fin_vaccess_fin_vupdate_eq : forall {X} {n}
  (i : Fin n) v (x : X),
  fin_vaccess i (fin_vupdate i x v) = x.
Proof.
  intros.
  unfold fin_vaccess, fin_vupdate.
  destruct i.
  apply access_update_eq.
Qed.

Lemma fin_vaccess_fin_vupdate_neq : forall {X} {n}
  (i j : Fin n) v (x : X), i <> j ->
  fin_vaccess i (fin_vupdate j x v) = fin_vaccess i v.
Proof.
  intros.
  unfold fin_vaccess, fin_vupdate.
  destruct i as [i Hi].
  destruct j as [j Hj].
  apply access_update_neq.
  intro pf.
  apply H.
  destruct pf.
  f_equal; apply UIP.
Qed.
