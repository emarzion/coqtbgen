Require Import Games.Util.Dec.
Require Import Games.Util.Fin.
Require Import Games.Util.Vec.

Definition Mat (X : Type) (m n : nat) : Type :=
  Vec (Vec X n) m.

Definition mreplicate {X} {m n} (x : X) : Mat X m n :=
  vreplicate (vreplicate x).

Definition maccess {X} {m n} : Fin m -> Fin n
  -> Mat X m n -> X :=
  fun i j mat => vaccess j (vaccess i mat).

Definition mupdate {X} {m n} : Fin m -> Fin n
  -> X -> Mat X m n -> Mat X m n :=
  fun i j x mat => vupdate i
    (vupdate j x (vaccess i mat)) mat.

Lemma maccess_mupdate_eq {X} {m n} :
  forall (i : Fin m) (j : Fin n) (mat : Mat X m n) (x : X),
  maccess i j (mupdate i j x mat) = x.
Proof.
  unfold maccess, mupdate.
  intros.
  repeat rewrite vaccess_vupdate_eq; reflexivity.
Qed.

Lemma maccess_mupdate_neq1 {X} {m n} :
  forall (i1 i2 : Fin m) (j1 j2 : Fin n) (mat : Mat X m n) (x : X),
  i1 <> i2 ->
  maccess i1 j1 (mupdate i2 j2 x mat) =
  maccess i1 j1 mat.
Proof.
  unfold maccess, mupdate.
  intros.
  rewrite vaccess_vupdate_neq; auto.
Qed.

Lemma maccess_mupdate_neq2 {X} {m n} :
  forall (i : Fin m) (j1 j2 : Fin n) (mat : Mat X m n) (x : X),
  j1 <> j2 ->
  maccess i j1 (mupdate i j2 x mat) =
  maccess i j1 mat.
Proof.
  unfold maccess, mupdate.
  intros.
  rewrite vaccess_vupdate_eq.
  apply vaccess_vupdate_neq; auto.
Qed.

Lemma maccess_mupdate_neq {X} {m n} :
  forall (i1 i2 : Fin m) (j1 j2 : Fin n) (mat : Mat X m n) (x : X),
  (i1, j1) <> (i2, j2) ->
  maccess i1 j1 (mupdate i2 j2 x mat) =
  maccess i1 j1 mat.
Proof.
  intros.
  destruct (dec (P := i1 = i2)).
  - rewrite e.
    rewrite maccess_mupdate_neq2; congruence.
  - rewrite maccess_mupdate_neq1; auto.
Qed.
