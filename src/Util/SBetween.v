Require Import CoqChess.Util.Rel.

Definition sbetween : Rel 3 nat :=
  fun x y z =>
      (x < y /\ y < z)
   \/ (z < y /\ y < x).

Lemma sbetween_sym : forall x y z,
  sbetween x y z -> sbetween z y x.
Proof.
  unfold sbetween; tauto.
Qed.
