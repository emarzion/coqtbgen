Require Import String.
Require Import Extraction.

Require Import Games.Game.Player.
Require Import Games.Game.Game.
Require Import Games.Game.Strategy.
Require Import Games.Util.Show.
Require Import Games.Game.SampleGame.
Require Import Games.Game.TB.

CoInductive IO : Type -> Type :=
  | ret : forall {A}, A -> IO A
  | bind : forall {A B}, IO A -> (A -> IO B) -> IO B
  | get_line : IO string
  | print : string -> IO unit
  | exit : IO unit.

Definition engine G : Type :=
  forall s : GameState G, IO (Move s).

CoFixpoint play_with_engine {G} (pl : Player) (s : GameState G) `{forall s : GameState G, Show (Move s)}
  (strat : strategy pl s) (eng : engine G) : IO unit.
Proof.
  destruct strat.
  - destruct res.
    + exact (bind (print ("Win for " ++ show p)) (fun _ => exit)).
    + exact (bind (print "Draw") (fun _ => exit)).
  - exact (bind (print ("Move played:" ++ show m)) (fun _ => play_with_engine G pl _ _ strat eng)).
  - exact (bind (print "Enter move:") (fun _ => bind (eng b) (fun m => play_with_engine G pl _ _ (s m) eng))).
Defined.

Inductive Result (A : Type) : Type :=
  | Ok : A -> Result A
  | Error : string -> Result A.

Arguments Ok {_} _.
Arguments Error {_} _.

CoFixpoint read_engine {G}
  (read : forall s : GameState G, string -> Result (Move s)) : engine G :=
  fun s => bind get_line (fun str =>
    match read s str with
    | Ok move => ret move
    | Error msg => bind (print msg) (fun _ =>
        read_engine read s)
    end).

Definition read_RS (str : string) : Result RS :=
  match str with
  | "R" => Ok RS_R
  | "S" => Ok RS_S
  | _ => Error "invalid move."
  end.

Definition read_LS (str : string) : Result LS :=
  match str with
  | "L" => Ok LS_L
  | "S" => Ok LS_S
  | _ => Error "invalid move."
  end.

Definition read_LRS (str : string) : Result LRS :=
  match str with
  | "L" => Ok LRS_L
  | "R" => Ok LRS_R
  | "S" => Ok LRS_S
  | _ => Error "invalid move."
  end.

Definition read_Empty (str : string) : Result Empty_set :=
  Error "invalid move.".

Definition sample_read : forall s, string -> Result (Mv s).
Proof.
  intros [[] []]; simpl; (
  exact read_RS ||
  exact read_LS ||
  exact read_LRS ||
  exact read_Empty
  ).
Defined.

Definition Show_RS : Show RS.
Proof.
  refine {|
    show x :=
      match x with
      | RS_R => "R"
      | RS_S => "S"
      end
  |}.
  intros [] [] pf;
    (reflexivity  || discriminate).
Defined.

Definition Show_LS : Show LS.
Proof.
  refine {|
    show x :=
      match x with
      | LS_L => "L"
      | LS_S => "S"
      end
  |}.
  intros [] [] pf;
    (reflexivity  || discriminate).
Defined.

Definition Show_LRS : Show LRS.
Proof.
  refine {|
    show x :=
      match x with
      | LRS_L => "L"
      | LRS_R => "R"
      | LRS_S => "S"
      end
  |}.
  intros [] [] pf;
    (reflexivity  || discriminate).
Defined.

Definition Show_Empty : Show Empty_set.
Proof.
  refine {|
    show (x : Empty_set) :=
      match x with
      end
  |}.
  intros [].
Defined.

Global Instance Sample_Move_show : forall {s : St}, Show (Mv s).
Proof.
  intros [[] []]; simpl; (
  exact Show_RS ||
  exact Show_LS ||
  exact Show_LRS ||
  exact Show_Empty
  ).
Defined.

Definition interactive_tb_sample (tb_player : Player) (s : St) : IO unit :=
  play_with_engine (G := SampleGame)
  tb_player s (tb_strat s tb_player)
  (@read_engine SampleGame sample_read).

Require Import Extraction.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellString.
Extraction Language Haskell.

Extract Inductive IO => "Prelude.IO"
  [ "Prelude.return"
    "(Prelude.>>=)"
    "Prelude.getLine"
    "Prelude.putStrLn"
    "exitSuccess"
  ].

Extract Constant List.map => "Prelude.map".
(* Extract Constant List.concat => "Prelude.concat". *)
Extract Constant append => "(Prelude.++)".
(* Extract Constant Show_Prod => "(\f g (x,y) -> Prelude.show (f x, g y))". *)
Extract Constant List.length => "Prelude.length".
Extract Constant Compare_dec.le_lt_eq_dec => "(Prelude.<)".

Extraction "TB.hs" interactive_tb_sample.



