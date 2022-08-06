Require Import CoqChess.Util.Dec.
Require Import CoqChess.Util.Fin.
Require Import CoqChess.Util.Vec.

Definition Mat (X : Type) (m n : nat) : Type :=
  Vec (Vec X n) m.

Definition fin_maccess {X} {m n} : Fin m -> Fin n
  -> Mat X m n -> X :=
  fun i j mat => fin_vaccess j (fin_vaccess i mat).

Definition fin_mupdate {X} {m n} : Fin m -> Fin n
  -> X -> Mat X m n -> Mat X m n :=
  fun i j x mat => fin_vupdate i
    (fin_vupdate j x (fin_vaccess i mat)) mat.

Lemma fin_maccess_fin_mupdate_eq {X} {m n} :
  forall (i : Fin m) (j : Fin n) (mat : Mat X m n) (x : X),
  fin_maccess i j (fin_mupdate i j x mat) = x.
Proof.
  unfold fin_maccess, fin_mupdate.
  intros.
  repeat rewrite fin_vaccess_fin_vupdate_eq; reflexivity.
Qed.

Lemma fin_maccess_fin_mupdate_neq1 {X} {m n} :
  forall (i1 i2 : Fin m) (j1 j2 : Fin n) (mat : Mat X m n) (x : X),
  i1 <> i2 ->
  fin_maccess i1 j1 (fin_mupdate i2 j2 x mat) =
  fin_maccess i1 j1 mat.
Proof.
  unfold fin_maccess, fin_mupdate.
  intros.
  rewrite fin_vaccess_fin_vupdate_neq; auto.
Qed.

Lemma fin_maccess_fin_mupdate_neq2 {X} {m n} :
  forall (i : Fin m) (j1 j2 : Fin n) (mat : Mat X m n) (x : X),
  j1 <> j2 ->
  fin_maccess i j1 (fin_mupdate i j2 x mat) =
  fin_maccess i j1 mat.
Proof.
  unfold fin_maccess, fin_mupdate.
  intros.
  rewrite fin_vaccess_fin_vupdate_eq.
  apply fin_vaccess_fin_vupdate_neq; auto.
Qed.

Lemma fin_maccess_fin_mupdate_neq {X} {m n} :
  forall (i1 i2 : Fin m) (j1 j2 : Fin n) (mat : Mat X m n) (x : X),
  (i1, j1) <> (i2, j2) ->
  fin_maccess i1 j1 (fin_mupdate i2 j2 x mat) =
  fin_maccess i1 j1 mat.
Proof.
  intros.
  destruct (dec (P := i1 = i2)).
  - rewrite e.
    rewrite fin_maccess_fin_mupdate_neq2; congruence.
  - rewrite fin_maccess_fin_mupdate_neq1; auto.
Qed.