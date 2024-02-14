Require Import List.
Import ListNotations.
Require Import Compare_dec.

Require Import Games.Game.Game.
Require Import Games.Game.TB.
Require Import Games.Util.OMap.
Require Import Games.Util.IntHash.
Require Import Games.Game.Player.
Require Import Games.Util.IntMap.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.
Require Import Games.Game.Draw.
Require Import Games.Util.Dec.

Record OCamlTablebase (G : Game) `{IntHash (GameState G)} : Type := {
  tb_whites : OM (Player * nat)%type;
  tb_blacks : OM (Player * nat)%type
  }.

Arguments tb_whites {_} {_} _.
Arguments tb_blacks {_} {_} _.

Definition query_TB {G} `{IntHash (GameState G)}
  (tb : OCamlTablebase G) (s : GameState G) : option (Player * nat) :=
  match to_play s with
  | White => hash_lookup s (tb_whites tb)
  | Black => hash_lookup s (tb_blacks tb)
  end.

Record CorrectTablebase {M} `{IntMap M}
  {G} `{IntHash (GameState G)} (tb : OCamlTablebase G) := {

  query_mate : forall s pl n,
    query_TB tb s = Some (pl, n) ->
    mate pl s n;

  mate_query : forall s pl n,
    mate pl s n ->
    query_TB tb s = Some (pl, n);

  query_draw : forall s,
    query_TB tb s = None ->
    draw s;

  draw_query : forall s,
    draw s ->
    query_TB tb s = None

  }.

Arguments query_mate {_} {_} {_} {_}.
Arguments query_draw {_} {_} {_} {_}.

Definition certified_TB {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s : GameState G, Discrete (Move s)} :
  OCamlTablebase G :=
  match TB_final with
  | Build_TB _ _ wps bps _ _ =>
    {|
      tb_whites := wps;
      tb_blacks := bps;
    |}
  end.

Lemma certified_TB_whites {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s : GameState G, Discrete (Move s)} :
  tb_whites certified_TB = white_positions TB_final.
Proof.
  unfold certified_TB.
  destruct TB_final; reflexivity.
Qed.

Lemma certified_TB_blacks {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s : GameState G, Discrete (Move s)} :
  tb_blacks certified_TB = black_positions TB_final.
Proof.
  unfold certified_TB.
  destruct TB_final; reflexivity.
Qed.

Lemma certified_TB_correct {M} `{IntMap M}
  {G} `{IntHash (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s : GameState G, Discrete (Move s)} :
  CorrectTablebase certified_TB.
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

Definition p_leb (pl : Player) (r1 r2 : option (Player * nat)) : bool :=
  match pl with
  | White =>
    match r1, r2 with
    | Some (Black, m), Some (Black, n) => leb m n
    | Some (Black, _), _ => true
    | None, None => true
    | None, Some (White, _) => true
    | Some (White, m), Some (White, n) => leb n m
    | _, _ => false
    end
  | Black =>
    match r1, r2 with
    | Some (White, m), Some (White, n) => leb m n
    | Some (White, _), _ => true
    | None, None => true
    | None, Some (Black, _) => true
    | Some (Black, m), Some (Black, n) => leb n m
    | _, _ => false
    end
  end.

Fixpoint max_by {X} (x_leb : X -> X -> bool) (xs : list X) : option X :=
  match xs with
  | [] => None
  | x :: xs' =>
    match max_by x_leb xs' with
    | None => Some x
    | Some y => if x_leb x y then Some y else Some x
    end
  end.

Lemma max_by_ne_Some {X} x_leb (xs : list X) (pf : xs <> []) :
  { x : X & max_by x_leb xs = Some x }.
Proof.
  destruct xs.
  - elim (pf eq_refl).
  - simpl.
    destruct (max_by x_leb xs).
    + destruct (x_leb x x0).
      * exists x0; reflexivity.
      * exists x; reflexivity.
    + exists x; reflexivity.
Defined.

Definition max_by_ne {X} x_leb (xs : list X) (pf : xs <> []) : X :=
  projT1 (max_by_ne_Some x_leb xs pf).

Lemma move_enum_all_ne {G} {s : GameState G} (s_res : atomic_res s = None) : enum_moves s <> [].
Proof.
  intro pf.
  destruct (nil_atomic_res pf); congruence.
Qed.

CoFixpoint tb_strat {M} {G} (s : GameState G) pl
  `{IntMap M}
  `{IntHash (GameState G)}
  (tb : OCamlTablebase G) : strategy pl s.
Proof.
  - destruct (atomic_res s) eqn:s_res.
    + eapply atom_strategy; eauto.
    + destruct (player_id_or_opp_r_t (to_play s) pl) as [s_play|s_play].
      * pose (m := max_by_ne
          (fun m1 m2 => p_leb pl
             (query_TB tb (exec_move s m1))
             (query_TB tb (exec_move s m2))
          ) (enum_moves s) (move_enum_all_ne s_res)).
        exact (eloise_strategy s_res s_play m (@tb_strat _ _ _ pl _ _ tb)).
      * exact (abelard_strategy s_res s_play (fun m =>
          @tb_strat _ _ _ pl _ _ tb)).
Defined.
