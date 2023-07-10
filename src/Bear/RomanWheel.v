Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.

Require Import Games.Util.Show.
Require Import Games.Bear.Graph.
Require Import Games.Bear.BearGame.
Require Import Games.Game.TB.

Inductive Spoke :=
  S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8.

Definition clockwise (s : Spoke) : Spoke :=
  match s with
  | S1 => S2
  | S2 => S3
  | S3 => S4
  | S4 => S5
  | S5 => S6
  | S6 => S7
  | S7 => S8
  | S8 => S1
  end.

Definition c_clockwise (s : Spoke) : Spoke :=
  match s with
  | S1 => S8
  | S2 => S1
  | S3 => S2
  | S4 => S3
  | S5 => S4
  | S6 => S5
  | S7 => S6
  | S8 => S7
  end.

Definition list_spokes :=
  [S1;S2;S3;S4;S5;S6;S7;S8].

Definition show_spoke (s : Spoke) : string := (
  match s with
  | S1 => "1"
  | S2 => "2"
  | S3 => "3"
  | S4 => "4"
  | S5 => "5"
  | S6 => "6"
  | S7 => "7"
  | S8 => "8"
  end)%string.

Inductive SpokeLoc :=
  Mid | L | R.

Definition show_loc (l : SpokeLoc) : string := (
  match l with
  | Mid => "M"
  | L => "L"
  | R => "R"
  end)%string.

Definition list_locs :=
  [Mid;L;R].

Inductive RWVert :=
  | Center
  | SpokeVert (s : Spoke) (l : SpokeLoc).

Global Instance Show_RWVert : Show RWVert.
Proof.
  unshelve econstructor.
  - intro v.
    destruct v eqn:?.
    + exact "Center"%string.
    + exact ("Spoke" ++ show_spoke s ++ show_loc l)%string.
  - apply cheat.
Defined.

Global Instance RWVert_Nonnil : Nonnil RWVert.
Admitted.

Global Instance RWVert_CommaFree : CommaFree RWVert.
Admitted.

Global Instance RWVert_Semicolon : SemicolonFree RWVert.
Admitted.

Definition RomanWheel : Graph.
Proof.
  refine {|
    Vert := RWVert;
    Vert_disc := _;
    Vert_enum := _;

    successors := fun v =>
      match v with
      | Center => map (fun s => SpokeVert s Mid) list_spokes
      | SpokeVert s Mid => [Center; SpokeVert s L; SpokeVert s R]
      | SpokeVert s L => [SpokeVert s R; SpokeVert s Mid; SpokeVert (c_clockwise s) R]
      | SpokeVert s R => [SpokeVert s L; SpokeVert s Mid; SpokeVert (clockwise s) L]
      end
  |}.
  - refine {|
      enum := Center :: List.concat
        (List.map (fun s => List.map (SpokeVert s) list_locs) list_spokes);
      enum_correct := _
    |}.
    apply cheat.
Defined.

Global Instance Show_RWV : Show (Vert RomanWheel) :=
  Show_RWVert.

Definition RW_TB := Bear_TB RomanWheel.

Require Import Games.Util.OMap.

Definition wps : OM (Player.Player * nat) :=
  white_positions (tb RW_TB).

Definition bps : OM (Player.Player * nat) :=
  black_positions (tb RW_TB).

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Extraction Language OCaml.

Extraction "RW.ml" wps bps.



