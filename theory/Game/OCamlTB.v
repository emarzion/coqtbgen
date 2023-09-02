Require Import List.
Import ListNotations.
Require Import Compare_dec.

Require Import Games.Game.Game.
Require Import Games.Game.TB.
Require Import Games.Util.OMap.
Require Import Games.Util.Show.
Require Import Games.Game.Player.
Require Import Games.Util.StringMap.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.
Require Import Games.Game.Draw.
Require Import Games.Util.Dec.

Record OCamlTablebase (G : Game) `{Show (GameState G)} : Type := {
  tb_whites : OM (Player * nat)%type;
  tb_blacks : OM (Player * nat)%type
  }.

Arguments tb_whites {_} {_} _.
Arguments tb_blacks {_} {_} _.

Definition query_TB {G} `{Show (GameState G)}
  (tb : OCamlTablebase G) (s : GameState G) : option (Player * nat) :=
  match to_play s with
  | White => str_lookup s (tb_whites tb)
  | Black => str_lookup s (tb_blacks tb)
  end.

Record CorrectTablebase {M} `{StringMap M}
  {G} `{Show (GameState G)} (tb : OCamlTablebase G) := {

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

Definition certified_TB {M} `{StringMap M}
  {G} `{Show (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s : GameState G, Discrete (Move s)} :
  OCamlTablebase G := {|
  tb_whites := white_positions TB_final;
  tb_blacks := black_positions TB_final;
  |}.

Lemma certified_TB_correct {M} `{StringMap M}
  {G} `{Show (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s : GameState G, Discrete (Move s)} :
  CorrectTablebase certified_TB.
Proof.
  constructor.
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
  `{StringMap M}
  `{Show (GameState G)}
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
        exact (eloise_strategy s_play m (@tb_strat _ _ _ pl _ _ tb)).
      * exact (abelard_strategy s_play (fun m =>
          @tb_strat _ _ _ pl _ _ tb)).
Defined.

(*
CoInductive Res :=
  | Win_res (pl : Player) : Res
  | Step_res : Res -> Res.

CoInductive bisim : Res -> Res -> Prop :=
  | Win_refl {pl} : bisim (Win_res pl) (Win_res pl)
  | Step_bisim {r1 r2} : bisim r1 r2 -> bisim (Step_res r1) (Step_res r2).

CoFixpoint draw : Res := Step_res draw.

CoInductive pref (pl : Player) : Res -> Res -> Prop :=
  | Win_is_best : forall r, pref pl (Win_res pl) r
  | Loss_is_worst : forall r, pref pl r (Win_res (opp pl))
  | Step_mon : forall r1 r2, pref pl r1 r2 -> pref pl (Step_res r1) (Step_res r2).

CoFixpoint pref_antisym pl : forall r1 r2, pref pl r1 r2 -> pref pl r2 r1 ->
  bisim r1 r2.
Proof.
  intros.
  destruct H.
  - inversion H0.
    + apply Win_refl.
    + elim (opp_no_fp pl); congruence.
  - inversion H0.
    + elim (opp_no_fp pl); congruence.
    + apply Win_refl.
  - inversion H0.
    apply Step_bisim.
    apply (pref_antisym _ _ _ H H3).
Qed.

CoFixpoint trace {G} {pl} (s : GameState G)
  (s1 : strategy pl s) (s2 : strategy (opp pl) s) : Res.
Proof.
  destruct (atomic_res s) eqn:s_res.
  - destruct r.
    + exact (Win_res p).
    + exact draw.
  - destruct (player_id_or_opp_r_t (to_play s) pl).
    + destruct s1.
      * congruence.
      * destruct s2.
        -- congruence.
        -- elim (opp_no_fp pl); congruence.
        -- apply Step_res.
           exact (trace _ _ (exec_move b m) s1 (s m)).
      * elim (opp_no_fp pl); congruence.
    + destruct s1.
      * congruence.
      * elim (opp_no_fp pl); congruence.
      * destruct s2.
        -- congruence.
        -- apply Step_res.
           exact (trace _ _ (exec_move b m) (s m) s2).
        -- elim (opp_no_fp (opp pl)); congruence.
Defined.

Definition optimal {G} {pl} {s : GameState G} (str : strategy pl s) : Prop :=
  forall str', exists opp, pref pl (trace s str opp) (trace s str' opp).


*)


