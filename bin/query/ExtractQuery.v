Require Import Lia.
Require Import List.
Require Import String.
Import ListNotations.

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Require Import ExtrOCamlInt63.
Extraction Language OCaml.

Require Import Games.Util.Show.
Require Import Games.Util.IntHash.
Require Import Games.Util.OMap.
Require Import TBGen.Bear.Sort.
Require Import TBGen.Bear.BearGame.
Require Import TBGen.Bear.RomanWheel.
Require Import Games.Game.TB.
Require Import Games.Game.OCamlTB.

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

Definition strC : string := "C".
Definition str1L : string := "1L".
Definition str1M : string := "1M".
Definition str1R : string := "1R".
Definition str2L : string := "2L".
Definition str2M : string := "2M".
Definition str2R : string := "2R".
Definition str3L : string := "3L".
Definition str3M : string := "3M".
Definition str3R : string := "3R".
Definition str4L : string := "4L".
Definition str4M : string := "4M".
Definition str4R : string := "4R".
Definition str5L : string := "5L".
Definition str5M : string := "5M".
Definition str5R : string := "5R".
Definition str6L : string := "6L".
Definition str6M : string := "6M".
Definition str6R : string := "6R".
Definition str7L : string := "7L".
Definition str7M : string := "7M".
Definition str7R : string := "7R".
Definition str8L : string := "8L".
Definition str8M : string := "8M".
Definition str8R : string := "8R".

Definition show_RWVert (v : RWVert) : string :=
  match v with
  | Center => strC
  | SpokeVert S1 L => str1L
  | SpokeVert S1 Mid => str1M
  | SpokeVert S1 R => str1R
  | SpokeVert S2 L => str2L
  | SpokeVert S2 Mid => str2M
  | SpokeVert S2 R => str2R
  | SpokeVert S3 L => str3L
  | SpokeVert S3 Mid => str3M
  | SpokeVert S3 R => str3R
  | SpokeVert S4 L => str4L
  | SpokeVert S4 Mid => str4M
  | SpokeVert S4 R => str4R
  | SpokeVert S5 L => str5L
  | SpokeVert S5 Mid => str5M
  | SpokeVert S5 R => str5R
  | SpokeVert S6 L => str6L
  | SpokeVert S6 Mid => str6M
  | SpokeVert S6 R => str6R
  | SpokeVert S7 L => str7L
  | SpokeVert S7 Mid => str7M
  | SpokeVert S7 R => str7R
  | SpokeVert S8 L => str8L
  | SpokeVert S8 Mid => str8M
  | SpokeVert S8 R => str8R
  end.

Global Instance Show_RWVert : Show RWVert. refine {|
  show := show_RWVert;
  show_inj := _;
  |}.
Proof.
  - intros v v'.
    destruct v as [|[] []];
    destruct v' as [|[] []]; try reflexivity.
    all: discriminate.
Defined.

Definition print_RW_move {s : BG_State RomanWheel}
  (m : BG_Move s) : string.
Proof.
  destruct m.
  - destruct b.
    exact ("B" ++ show b_dest).
  - destruct h.
    exact ("H" ++ show h_orig ++ show h_dest).
Defined.

Extraction Blacklist String List.

Definition RW_exec_move (s : BG_State RomanWheel)
 : BG_Move s -> BG_State RomanWheel :=
  exec_move.

Definition query_RW_TB :
  OCamlTablebase (BearGame RomanWheel) ->
  BG_State RomanWheel -> option (Player.Player * nat) :=
  query_TB.

Definition rw_tb_strat (pl : Player.Player)
  (s : Game.GameState (BearGame RomanWheel))
  (tb : OCamlTablebase (BearGame RomanWheel))
 : Strategy.strategy pl s :=
  tb_strat s pl tb.

Set Warnings "-extraction-default-directory".

Separate Extraction
  make_RW_State
  init_RW_State
  RW_exec_move
  BearGame.enum_moves
  print_RW_move
  query_RW_TB
  p_leb
  rw_tb_strat
  create_Move
  is_hunter
  is_bear
  .
