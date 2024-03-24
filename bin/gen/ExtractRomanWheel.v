Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Require Import ExtrOCamlInt63.
Extraction Language OCaml.

Require Import Games.Util.OMap.
Require Import TBGen.Bear.Sort.
Require Import TBGen.Bear.BearGame.
Require Import TBGen.Bear.RomanWheel.
Require Import Games.Game.TB.

Extraction "TBGen.ml" RW_TB.
