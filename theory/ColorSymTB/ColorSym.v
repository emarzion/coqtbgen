Require Import Games.Game.Game.
Require Import Games.Game.Player.

Definition option_map {X Y} (f : X -> Y) (o : option X) : option Y :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Definition mirror_result (r : Result) : Result :=
  match r with
  | Win p => Win (opp p)
  | Draw => Draw
  end.

Class ColorSym (G : Game) : Type := {
  mirror : GameState G -> GameState G;
  mirror_move : forall s,
    Move s -> Move (mirror s);
  to_play_mirror : forall s,
    to_play (mirror s) = opp (to_play s);
  exec_move_mirror_move : forall s (m : Move s),
    exec_move (mirror s) (mirror_move s m) =
    mirror (exec_move s m);
  atomic_res_mirror : forall s,
    atomic_res (mirror s) = option_map mirror_result (atomic_res s)
  }.

Arguments mirror {_} {_} _.
Arguments mirror_move {_} {_} {_} _.
