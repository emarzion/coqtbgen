Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Extraction Language OCaml.

Require Import Games.Util.OMap.
Require Import Games.Bear.Sort.
Require Import Games.Bear.BearGame.
Require Import Games.Bear.RomanWheel.
Require Import Games.Game.TB.

Definition wps : OM (Player.Player * nat) :=
  white_positions (tb RW_TB).

Definition bps : OM (Player.Player * nat) :=
  black_positions (tb RW_TB).

Extraction "TBGen.ml" wps bps.