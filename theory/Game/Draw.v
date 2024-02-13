Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.

CoInductive draw {G : Game} : GameState G -> Type :=
  | atom_draw : forall s,
      atomic_res s = Some Draw ->
      draw s
  | play_draw : forall s p,
      to_play s = p ->
      atomic_res s = None ->
      (forall m, draw (exec_move s m) + win (opp p) (exec_move s m)) ->
      forall m, draw (exec_move s m) ->
      draw s.

Lemma win_not_draw {G : Game} : forall (p : Player) (s : GameState G),
  win p s -> draw s -> False.
Proof.
  intros p s w.
  induction w; intro d.
  - destruct d; congruence.
  - destruct d; try congruence.
    destruct (s0 m).
    + auto.
    + apply (opp_no_fp p).
      assert (p0 = p) as Hp by congruence; rewrite Hp in *; clear Hp.
      eapply unique_winner; eauto.
  - destruct d; try congruence.
    exact (H m d).
Qed.

CoFixpoint strategy_of_draw {G : Game} {p : Player} {s : GameState G}
  (d : draw s) : strategy p s.
Proof.
  destruct d.
  - exact (atom_strategy e).
  - destruct (player_id_or_opp_r_t (to_play s) p).
    + eapply eloise_strategy.
      * exact e0.
      * exact e1.
      * eapply strategy_of_draw.
        exact d.
    + eapply (abelard_strategy).
      * exact e0.
      * exact e1.
      * intro m'.
        destruct (s0 m').
        ** eapply strategy_of_draw; auto.
        ** apply strategy_of_win.
           rewrite e in e1.
           rewrite e1 in w.
           rewrite opp_invol in w.
           exact w.
Defined.

CoFixpoint strategy_of_draw_correct {G : Game} {p : Player} (s : GameState G)
  (d : draw s) : drawing_strategy p (strategy_of_draw d).
Proof.
  rewrite (strat_id_eq _).
  unfold strat_id.
  destruct d.
  - unfold strategy_of_draw.
    constructor.
  - unfold strategy_of_draw.
    destruct (player_id_or_opp_r_t (to_play s) p).
    + constructor.
      apply strategy_of_draw_correct.
    + constructor.
      intro.
      destruct (s0 m0).
      * left.
        apply strategy_of_draw_correct.
      * right.
        simpl.
        apply strategy_of_win_correct.
Qed.
