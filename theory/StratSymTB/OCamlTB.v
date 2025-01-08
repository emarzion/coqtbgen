Require Import List.
Import ListNotations.
Require Import Compare_dec.

Require Import Games.Game.Game.
Require Import TBGen.StratSymTB.TB.
Require Import TBGen.Util.OMap.
Require Import TBGen.Util.IntHash.
Require Import Games.Game.Player.
Require Import TBGen.Util.IntMap.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.
Require Import Games.Game.Draw.
Require Import Games.Util.Dec.
Require Import TBGen.StratSymTB.Closed.

Record OCamlTablebase (G : Game) `{IntHash (GameState G)} : Type := {
  tb_whites : OM (Player * nat)%type;
  tb_blacks : OM (Player * nat)%type
  }.

Arguments tb_whites {_} {_} _.
Arguments tb_blacks {_} {_} _.

Definition query_TB {G} `{IntHash (GameState G)} `{Symmetry G}
  (tb : OCamlTablebase G) (s : GameState G) : option (Player * nat) :=
  match to_play s with
  | White => hash_lookup (normalize s) (tb_whites tb)
  | Black => hash_lookup (normalize s) (tb_blacks tb)
  end.

Record CorrectTablebase {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{Symmetry G} P (tb : OCamlTablebase G) := {

  query_mate : forall s pl n,
    query_TB tb s = Some (pl, n) ->
    mate pl s n;

  mate_query : forall s pl n,
    P s ->
    mate pl s n ->
    query_TB tb s = Some (pl, n);

  query_draw : forall s,
    P s ->
    query_TB tb s = None ->
    draw s;

  draw_query : forall s,
    draw s ->
    query_TB tb s = None

  }.

Arguments query_mate {_} {_} {_} {_}.
Arguments query_draw {_} {_} {_} {_}.

Definition certified_TB
  {M} `{IntMap M}
  {G} `{IntHash (GameState G)}
  `{Reversible G}
  `{NiceGame G} `{Symmetry G} `{forall s : GameState G, Discrete (Move s)}
  {P} `{FinPred G P} `{Closed _ P} `{Bisim_closed G auto P} `{Dec1 _ P} :
  OCamlTablebase G :=
  match TB_final with
  | Build_TB _ _ wps bps _ _ =>
    {|
      tb_whites := wps;
      tb_blacks := bps;
    |}
  end.

Lemma certified_TB_whites {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{Reversible G}
  `{NiceGame G} `{Symmetry G} `{forall s : GameState G, Discrete (Move s)}
  {P} `{FinPred G P} `{Closed _ P} `{Bisim_closed G auto P} `{Dec1 _ P} :
  tb_whites certified_TB = white_positions TB_final.
Proof.
  unfold certified_TB.
  destruct TB_final; reflexivity.
Qed.

Lemma certified_TB_blacks {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{Reversible G}
  `{NiceGame G} `{Symmetry G} `{forall s : GameState G, Discrete (Move s)}
  {P} `{FinPred G P} `{Closed _ P} `{Bisim_closed G auto P} `{Dec1 _ P} :
  tb_blacks certified_TB = black_positions TB_final.
Proof.
  unfold certified_TB.
  destruct TB_final; reflexivity.
Qed.

Lemma certified_TB_correct {M} `{IntMap M}
  {G} `{IntHash (GameState G)}
  `{Reversible G}
  `{NiceGame G} `{Symmetry G} `{forall s : GameState G, Discrete (Move s)}
  {P} `{FinPred G P} `{Closed _ P} `{Bisim_closed G auto P} `{Dec1 _ P} :
  CorrectTablebase P certified_TB.
Proof.
  constructor;
  unfold query_TB;
  rewrite certified_TB_whites;
  rewrite certified_TB_blacks.
  - apply TB_final_lookup_mate.
  - apply mate_TB_final_lookup.
  - apply TB_final_lookup_draw.
  - apply draw_TB_final_lookup.
Defined.
