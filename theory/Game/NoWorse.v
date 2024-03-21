Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.
Require Import Games.Game.Draw.

CoInductive no_worse {G : Game} (p : Player) : GameState G -> Type :=
  | atom_draw_no_worse : forall s,
      atomic_res s = Some Draw ->
      no_worse p s
  | atom_win_no_worse : forall s,
      atomic_res s = Some (Win p) ->
      no_worse p s
  | eloise_no_worse : forall s,
      atomic_res s = None ->
      to_play s = p ->
      forall m, no_worse p (exec_move s m) ->
      no_worse p s
  | abelard_no_worse : forall s,
      atomic_res s = None ->
      to_play s = opp p ->
      (forall m, no_worse p (exec_move s m)) ->
      no_worse p s.

CoInductive weak_draw {G : Game} : GameState G -> Type :=
  | atom_weak_draw : forall s,
      atomic_res s = Some Draw ->
      weak_draw s
  | eloise_weak_draw : forall s p,
      atomic_res s = None ->
      to_play s = p ->
      (forall m, no_worse (opp p) (exec_move s m)) ->
      forall m, weak_draw (exec_move s m) ->
      weak_draw s.

CoFixpoint weak_draw_no_worse {G : Game} (p : Player) : forall (s : GameState G),
  weak_draw s -> no_worse p s.
Proof.
  intros s wd_s.
  destruct wd_s.
  - apply atom_draw_no_worse; auto.
  - destruct (player_id_or_opp_r_t p0 p).
    + rewrite e1 in *.
      eapply eloise_no_worse; auto.
      apply weak_draw_no_worse; eauto.
    + rewrite e1 in *.
      apply abelard_no_worse; auto.
      rewrite opp_invol in n.
      exact n.
Defined.

CoFixpoint both_no_worse_weak_draw {G : Game} : forall p (s : GameState G),
  no_worse p s -> no_worse (opp p) s -> weak_draw s.
Proof.
  intros p s nw_ps nw_ops.
  destruct (atomic_res s) eqn:s_res.
  - destruct r.
    + destruct (player_id_or_opp_r_t p0 p).
      * rewrite e in *.
        destruct nw_ops; try congruence.
        elim (opp_no_fp p); congruence.
      * rewrite e in *.
        destruct nw_ps; try congruence.
        elim (opp_no_fp p); congruence.
    + apply atom_weak_draw; auto.
  - destruct nw_ps; try congruence.
    + destruct nw_ops; try congruence.
      * elim (opp_no_fp p); congruence.
      * eapply eloise_weak_draw; eauto.
        rewrite opp_invol; auto.
    + destruct nw_ops; try congruence.
      * eapply eloise_weak_draw; eauto.
        rewrite opp_invol; auto.
      * elim (opp_no_fp (opp p)); congruence.
Defined.

Record NW_Trap {G} (P : GameState G -> Type) p := {
  NWT_no_loss : forall s, P s -> atomic_res s <> Some (Win (opp p));
  NWT_eloise : forall s, P s -> atomic_res s = None -> to_play s = p ->
    { m : Move s & P (exec_move s m) };
  NWT_abelard : forall s, P s -> atomic_res s = None -> to_play s = opp p ->
    forall m, P (exec_move s m)
  }.

CoFixpoint NW_Trap_nw {G} {P : GameState G -> Type} {p} : NW_Trap P p ->
  forall s, P s -> no_worse p s.
Proof.
  intros PT s p_s.
  destruct (atomic_res s) eqn:s_res.
  - destruct r.
    + apply atom_win_no_worse.
      rewrite s_res; repeat f_equal.
      destruct (player_id_or_opp_r_t p0 p); auto.
      rewrite e in s_res.
      elim (NWT_no_loss _ _ PT s); auto.
    + apply atom_draw_no_worse; auto.
  - destruct (player_id_or_opp_r_t (to_play s) p).
    + destruct (NWT_eloise _ _ PT s) as [m Hm]; auto.
      eapply eloise_no_worse; auto.
      eapply NW_Trap_nw; eauto.
    + apply abelard_no_worse; auto.
      intro m.
      eapply NW_Trap_nw; eauto.
      eapply NWT_abelard; eauto.
Defined.

Lemma no_worse_not_lost {G : Game} (p : Player) : forall (s : GameState G), no_worse p s ->
  win (opp p) s -> False.
Proof.
  intros s nw_s w_s.
  induction w_s.
  - destruct nw_s; try congruence.
    elim (opp_no_fp p); congruence.
  - apply IHw_s.
    destruct nw_s; try congruence.
    + elim (opp_no_fp p); congruence.
    + apply n.
  - destruct nw_s; try congruence.
    + apply (H m); exact nw_s.
    + elim (opp_no_fp (opp p)); congruence.
Qed.

Lemma win_no_worse {G : Game} (p : Player) : forall (s : GameState G), win p s ->
 no_worse p s.
Proof.
  intros s w_s.
  induction w_s.
  - apply atom_win_no_worse; auto.
  - eapply eloise_no_worse; eauto.
  - apply abelard_no_worse; auto.
Qed.

CoFixpoint draw_no_worse {G : Game} (p : Player) : forall (s : GameState G), draw s ->
  no_worse p s.
Proof.
  intros s s_draw.
  destruct s_draw.
  - apply atom_draw_no_worse; auto.
  - destruct (player_id_or_opp_r_t p0 p).
    + rewrite e1 in *.
      eapply eloise_no_worse; auto.
      apply draw_no_worse. exact s_draw.
    + rewrite e1 in *.
      apply abelard_no_worse; auto.
      intro m'.
      destruct (s0 m').
      * apply draw_no_worse. exact d.
      * apply win_no_worse.
        rewrite opp_invol in w.
        exact w.
Defined.
