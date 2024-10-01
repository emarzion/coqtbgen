Require Import Lia.
Require Import List.

Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.

(* stuff that should eventually be added to games *)

Lemma mate_eq {G} {s : GameState G} {pl pl'} {n n'} :
  mate pl s n ->
  mate pl' s n' ->
  n = n'.
Proof.
  intros sm sm'.
  assert (pl = pl') as Heq.
  { destruct sm as [w _].
    destruct sm' as [w' _].
    exact (unique_winner _ _ _ w w').
  }
  rewrite Heq in sm.
  destruct sm as [w [w_d w_m]].
  destruct sm' as [w' [w'_d w'_m]].
  rewrite <- w_d, <- w'_d.
  apply PeanoNat.Nat.le_antisymm.
  - apply w_m.
  - apply w'_m.
Qed.