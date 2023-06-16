Require Import List.

Require Import Games.Game.Player.

Inductive Result : Type :=
  | Win : Player -> Result
  | Draw : Result.

Record Game : Type := {
  GameState : Type;
  Move : GameState -> Type;

  to_play : GameState -> Player;
  exec_move : forall {b}, Move b -> GameState;
  atomic_res : GameState -> option Result;
  enum_moves : forall b, list (Move b);

  enum_all : forall {b} (m : Move b),
    In m (enum_moves b);
  to_play_exec_move : forall b (m : Move b),
    to_play (exec_move m) = opp (to_play b);
  atomic_res_nil : forall b res,
    atomic_res b = Some res -> enum_moves b = nil;
  nil_atomic_res : forall b,
    enum_moves b = nil -> exists res, atomic_res b = Some res
  }.

Arguments GameState _ : assert.
Arguments Move {_} _.

Arguments to_play {_} _.
Arguments exec_move {_} _ _.
Arguments atomic_res {_} _.
Arguments enum_moves {_} _.

Arguments enum_all {_} {_} _.
Arguments to_play_exec_move {_} {_} _.
Arguments atomic_res_nil {_} {_} {_} _.
Arguments nil_atomic_res {_} {_} _.
