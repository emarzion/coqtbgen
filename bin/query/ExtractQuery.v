Require Import Lia.
Require Import List.
Require Import String.
Import ListNotations.

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Extraction Language OCaml.

Require Import Games.Util.Show.
Require Import Games.Util.OMap.
Require Import Games.Bear.Sort.
Require Import Games.Bear.BearGame.
Require Import Games.Bear.RomanWheel.
Require Import Games.Game.TB.

Definition make_BG_State {G} (pl : Player.Player)
  (b h1 h2 h3 : Graph.Vert G) : option (BG_State G).
Proof.
  destruct (NoDup_dec [b; h1; h2; h3]) as [pf|].
  - apply Some.
    refine {|
      to_play := pl;
      bear :=  b;
      hunters := insertion_sort [h1; h2; h3];
      hunters_sort := _;
      hunters_3 := _;
      hunters_distinct := _;
      bear_not_hunter := _
    |}.
    + apply insertion_sort_sorts.
    + now rewrite insertion_sort_length.
    + apply insertion_sort_NoDup.
      now inversion pf.
    + rewrite insertion_sort_In.
      now inversion pf.
  - exact None.
Defined.

Definition make_RW_State (pl : Player.Player)
  (b h1 h2 h3 : RWVert) : option (BG_State RomanWheel) :=
  @make_BG_State RomanWheel pl b h1 h2 h3.

Definition init_RW_State : BG_State RomanWheel.
Proof.
  refine {|
    to_play := Player.White;
    bear := Center : Graph.Vert RomanWheel;
    hunters :=
      [ SpokeVert S1 Mid
      ; SpokeVert S1 L
      ; SpokeVert S1 R];
  |}.
  - do 2 constructor.
    + repeat constructor.
    + constructor; [|constructor].
      compute; lia.
    + compute; lia.
    + constructor; [|constructor].
      compute; lia.
  - reflexivity.
  - repeat constructor; simpl; auto.
    + intros [|[|]]; auto; discriminate.
    + intros [|]; auto; discriminate.
  - simpl.
    intros [|[|[|]]]; auto; discriminate.
Defined.

Definition print_RW_move {s : BG_State RomanWheel}
  (m : BG_Move s) : string.
Proof.
  destruct m.
  - destruct b.
    exact ("Bear_" ++ show b_dest).
  - destruct h.
    exact ("Hunter_" ++ show h_orig ++ "_" ++ show h_dest).
Defined.

Extraction Blacklist String List.

(*
Extract Constant List.app =>
  "TailRec.app".
Extract Constant List.length =>
  "TailRec.length".
Extract Constant List.map =>
  "TailRec.map".
Extract Constant List.concat =>
  "TailRec.concat".
Extract Constant List.filter =>
  "TailRec.filter".
Extract Constant List.nodup =>
  "TailRec.nodup".
*)

(*
Extract Constant pf_map =>
  "(fun xs f -> TailRec.map (fun x -> f x __) xs)".
*)

Definition RW_exec_move (s : BG_State RomanWheel)
 : BG_Move s -> BG_State RomanWheel :=
  exec_move.

Definition show_RW_State (s : BG_State RomanWheel)
  : string :=
  show s.

Separate Extraction
  make_RW_State
  init_RW_State
  RW_exec_move
  BearGame.enum_moves
  print_RW_move
  show_RW_State
  p_leb.
