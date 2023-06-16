Require Import Extraction.
Set Extraction File Comment "asdf".


(*
Require Import String.

Require Import Games.Game.Game.
Require Import Games.Game.Strategy.

CoInductive IO : Type -> Type :=
  | ret : forall {A}, A -> IO A
  | bind : forall {A B}, IO A -> (A -> IO B) -> IO B
  | get_line : IO string
  | print : string -> IO unit
  | exit : IO unit.

Definition engine `{Game} : Type :=
  forall s : GameState, IO (Move s).

Inductive Result (A : Type) : Type :=
  | Ok : A -> Result A
  | Error : string -> Result A.

Arguments Ok {_} _.
Arguments Error {_} _.

CoFixpoint read_engine `{Game}
  (read : forall s : GameState, string -> Result (Move s)) : engine :=
  fun s => bind get_line (fun str =>
    match read s str with
    | Ok move => ret move
    | Error msg => bind (print msg) (fun _ =>
        read_engine read s)
    end).
*)

