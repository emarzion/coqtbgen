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

Require Import Games.Game.Result.

CoFixpoint tb_strat {M} {G} (s : GameState G) pl
  `{IntMap M}
  `{IntHash (GameState G)}
  (tb : OCamlTablebase G) : strategy pl s.
Proof.
  - destruct (atomic_res_inf s) as [[r s_res]|s_res].
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

Axiom cheat : forall {X}, X.

CoFixpoint res_le_refl pl : forall r,
  r <<= pl r.
Proof.
  destruct r.
  - destruct (player_id_or_opp pl pl0).
    + destruct H.
      apply Win_is_best.
    + rewrite <- H.
      apply Loss_is_worst.
  - apply Step_mon.
    apply res_le_refl.
Qed.

Require Import Lia.

Lemma mate_0_atom {G} : forall p (s : GameState G),
  mate p s 0 -> atomic_res s = Some (Win p).
Proof.
  intros p s [w [w_d _]].
  destruct w; auto.
  - discriminate w_d.
  - discriminate w_d.
Qed.

Lemma atom_mate_0 {G} : forall p (s : GameState G),
  atomic_res s = Some (Win p) -> mate p s 0.
Proof.
  intros p s pf.
  exists (atom_win pf).
  split; [reflexivity|intro; simpl; lia].
Qed.

Lemma atomic_res_None_invert {M} {G} {s : GameState G}
  `{IntMap M} `{IntHash (GameState G)} (tb : OCamlTablebase G) :
  CorrectTablebase tb ->
  atomic_res s = None ->
  (query_TB tb s = None) +
  { pl : Player & { n : nat & query_TB tb s = Some (pl, S n) } }.
Proof.
  intros C s_res.
  destruct (query_TB tb s) as [[pl n]|] eqn:Q.
  - right; exists pl.
    destruct n as [|n].
    + rewrite (mate_0_atom pl s) in s_res; [discriminate|].
      now apply C.
    + now exists n.
  - now left.
Defined.

CoFixpoint tb_strat_bound {M} {G} {s : GameState G} {pl}
  `{IntMap M} `{IntHash (GameState G)} (tb : OCamlTablebase G)
  (C : CorrectTablebase tb) :
  forall opp,
  (Res_of_tb_res (query_TB tb s)) <<= pl
  (trace (tb_strat s pl tb) opp).
Proof.
  intros opp.
  rewrite (Res_id_eq (trace _ _)).
  unfold Res_id.
  unfold trace.
  unfold tb_strat.
  destruct (atomic_res_inf s) as [[r s_res]|s_res].
  - destruct r.
    + simpl.
      rewrite (mate_query _ C _ _ _ (atom_mate_0 _ _ s_res)).
      simpl.
      apply res_le_refl.
    + rewrite (draw_query _ C _ (atom_draw _ s_res)).
      simpl.
      rewrite (Res_id_eq draw) at 1.
      apply res_le_refl.
  - destruct player_id_or_opp_r_t.
    + destruct opp; try (elim (opp_no_fp pl); congruence).
      fold @trace.
      fold @tb_strat.
      destruct (atomic_res_None_invert tb C s_res) as [Qnone|[pl' [n Qn]]].
      * apply cheat. (**)
      * apply cheat. (**)
    + destruct opp; try (elim (opp_no_fp (opp pl)); congruence).
      fold @trace.
      fold @tb_strat.
      destruct (atomic_res_None_invert tb C s_res) as [Qnone|[pl' [n Qn]]].
      * apply cheat. (**)
      * rewrite Qn.
        simpl.
        apply (res_le_trans _ _ (Step_res
          (Res_of_tb_res (query_TB tb (exec_move b m))))).
        -- apply cheat.
        -- exact (Step_mon _ _ _ (
tb_strat_bound M G _ pl H H0 tb C
  opp)).
Defined.

CoFixpoint tb_strat_bound {M} {G} {s : GameState G} {pl}
  `{IntMap M} `{IntHash (GameState G)} (tb : OCamlTablebase G)
  (C : CorrectTablebase tb) :
  forall opp,
  (Res_of_tb_res (query_TB tb s)) <<= pl
  (trace (tb_strat s pl tb) opp).
Proof.
  intros opp.
  rewrite (Res_id_eq (trace _ _)).
  unfold Res_id.
  unfold trace.
  unfold tb_strat.
  destruct (atomic_res_inf s) as [[r s_res]|s_res].
  - destruct r.
    + simpl.
      rewrite (mate_query _ C _ _ _ (atom_mate_0 _ _ s_res)).
      simpl.
      apply res_le_refl.
    + rewrite (draw_query _ C _ (atom_draw _ s_res)).
      simpl.
      rewrite (Res_id_eq draw) at 1.
      apply res_le_refl.
  - destruct player_id_or_opp_r_t.
    + destruct opp; try (elim (opp_no_fp pl); congruence).
      fold @trace.
      fold @tb_strat.
      destruct (atomic_res_None_invert tb C s_res) as [Qnone|[pl' [n Qn]]].
      * apply cheat. (**)
      * apply cheat. (**)
    + destruct opp; try (elim (opp_no_fp (opp pl)); congruence).
      fold @trace.
      fold @tb_strat.
      destruct (atomic_res_None_invert tb C s_res) as [Qnone|[pl' [n Qn]]].
      * apply cheat. (**)
      * rewrite Qn.
        simpl.
        apply (res_le_trans _ _ (Step_res
          (Res_of_tb_res (query_TB tb (exec_move b m))))).
        -- apply cheat.
        -- apply Step_mon.
           apply tb_strat_bound.
            exact C.
Defined.

CoFixpoint le_cong_r pl : forall r s s', bisim s s' ->
  r <<= pl s' -> r <<= pl s.
Proof.
  intros r s s' Hsim Hle.
  destruct Hsim.
  - exact Hle.
  - inversion Hle.
    + apply Loss_is_worst.
    + apply Step_mon.
      eapply le_cong_r; eauto.
Qed.

Lemma tb_strat_optimal {M} {G} {s : GameState G} {pl}
  `{IntMap M} `{IntHash (GameState G)} (tb : OCamlTablebase G) :
  CorrectTablebase tb ->
  optimal (tb_strat s pl tb).
Proof.
  intros C st.
  exists (tb_strat s (opp pl) tb).
  apply (res_le_trans _ _ (Res_of_tb_res (query_TB tb s))).
  - rewrite <- (opp_invol pl) at 1.
    apply res_flip.
    eapply le_cong_r; [apply trace_comm|].
    now apply tb_strat_bound.
  - now apply tb_strat_bound.
Qed.



