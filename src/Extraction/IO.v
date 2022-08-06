Require Import String.

Require Import CoqChess.Game.Game.
Require Import CoqChess.Game.Strategy.

CoInductive IO : Type -> Type :=
  | ret : forall {A}, A -> IO A
  | bind : forall {A B}, IO A -> (A -> IO B) -> IO B
  | get_line : IO string
  | print : string -> IO unit
  | exit : IO unit.

Definition engine G : Type :=
  forall s : GameState G, IO (Move s).

Inductive Result (A : Type) : Type :=
  | Ok : A -> Result A
  | Error : string -> Result A.

Arguments Ok {_} _.
Arguments Error {_} _.

CoFixpoint read_engine {G : Game}
  (read : forall s : GameState G, string -> Result (Move s)) : engine G :=
  fun s => bind get_line (fun str =>
    match read s str with
    | Ok move => ret move
    | Error msg => bind (print msg) (fun _ =>
        read_engine read s)
    end).
