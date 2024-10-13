
Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.
Require Import Games.Game.Draw.
Require Import Games.Game.NoWorse.

Require Import TBGen.Util.ListUtil.

(*
Definition inv_forward s m s' :
  bisim G G auto (exec_move s m) s' ->
  { s'' : GameState G & Move s'' }.
Proof.
  intro pf.

Admitted.

Lemma inv_forward_correct s m s' (b : bisim G G auto (exec_move s m) s') :
  exec_move (projT1 (inv_forward s m s' b)) (projT2 (inv_forward s m s' b)) = s'.
Admitted.

Lemma exec_inv_forward s m s' (b : bisim G G auto (exec_move s m) s') :
  bisim G G auto s (projT1 (inv_forward s m s' b)).
Admitted.
*)

Record InvertibleBisim (G H : Game) : Type := {
  bisim : GameState G -> GameState H -> Type;

  forward : forall {s s'}, bisim s s' ->
    Move s -> Move s';
  back : forall {s s'}, bisim s s' ->
    Move s' -> Move s;

  to_play_bisim : forall s s', bisim s s' ->
    to_play s = to_play s';

  atomic_bisim : forall s s', bisim s s' ->
    atomic_res s = atomic_res s';

  exec_forward : forall s s' m (b : bisim s s'),
    bisim
      (exec_move s m)
      (exec_move s' (forward b m));

  exec_back : forall s s' m (b : bisim s s'),
    bisim
      (exec_move s (back b m))
      (exec_move s' m);

  forward_back : forall s s' m (b : bisim s s'),
    forward b (back b m) = m;

  back_forward : forall s s' m (b : bisim s s'),
    back b (forward b m) = m;

  inv_forward s m s' :
    bisim (exec_move s m) s' ->
    { s'' : GameState H & Move s'' };

  inv_forward_correct s m s' (b : bisim (exec_move s m) s') :
    exec_move (projT1 (inv_forward s m s' b)) (projT2 (inv_forward s m s' b)) = s';

  exec_inv_forward s m s' (b : bisim (exec_move s m) s') :
    bisim s (projT1 (inv_forward s m s' b));

  inv_back s m s' :
    bisim s' (exec_move s m) ->
    { s'' : GameState G & Move s'' };

  inv_back_correct s m s' (b : bisim s' (exec_move s m)) :
    exec_move (projT1 (inv_back s m s' b)) (projT2 (inv_back s m s' b)) = s';

  exec_inv_back s m s' (b : bisim s' (exec_move s m)) :
    bisim (projT1 (inv_back s m s' b)) s;
  }.

Definition Bisim_sym {G H} (B : InvertibleBisim G H) : InvertibleBisim H G.
Proof.
  unshelve econstructor.
  - exact (fun s' s => bisim G H B s s').
  - simpl; intros s s'.
    apply (@back G H B).
  - simpl; intros s s'.
    apply (@forward G H B).
  - intros.
    eapply inv_back.
    exact X.
  - intros.
    eapply inv_forward.
    exact X.
  - intros; symmetry.
    apply (to_play_bisim G H B _ _ X).
  - intros; symmetry.
    apply (atomic_bisim G H B _ _ X).
  - simpl; intros. apply exec_back.
  - simpl; intros. apply exec_forward.
  - simpl; intros. apply back_forward.
  - simpl; intros. apply forward_back.
  - apply inv_back_correct.
  - apply exec_inv_back.
  - apply inv_forward_correct.
  - apply exec_inv_forward.
Defined.

Lemma bisim_sym {G H} (B : InvertibleBisim G H) s s' :
  bisim G H B s s' -> bisim H G (Bisim_sym B) s' s.
Proof.
  simpl; auto.
Qed.

Fixpoint bisim_win {G H} {p} (B : InvertibleBisim G H) s s'
  (b : bisim G H B s s') 
  (w : win p s) : win p s'.
Proof.
  destruct w.
  - apply atom_win.
    erewrite <- atomic_bisim; eauto.
  - apply eloise_win with
      (m := forward G H B b m).
    + erewrite <- atomic_bisim; eauto.
    + erewrite <- to_play_bisim; eauto.
    + eapply bisim_win; [|exact w].
      apply exec_forward.
  - apply abelard_win.
    + erewrite <- atomic_bisim; eauto.
    + erewrite <- to_play_bisim; eauto.
    + intro m.
      eapply bisim_win; [|exact (w (back G H B b m))].
      apply exec_back.
Defined.

Lemma list_max_ext (xs ys : list nat) :
  (forall x, List.In x xs <-> List.In x ys) ->
  List.list_max xs = List.list_max ys.
Proof.
  intro pf.
  apply PeanoNat.Nat.le_antisymm.
  - rewrite List.list_max_le.
    rewrite List.Forall_forall.
    intros.
    rewrite pf in H.
    apply list_max_is_max; auto.
  - rewrite List.list_max_le.
    rewrite List.Forall_forall.
    intros.
    rewrite <- pf in H.
    apply list_max_is_max; auto.
Qed.

Lemma bisim_win_depth {G H} {p} (B : InvertibleBisim G H)
  s (w : win p s) : forall s' (b : bisim G H B s s'),
  depth (bisim_win B s s' b w) = depth w.
Proof.
  induction w; intro.
  - reflexivity.
  - simpl; intro.
    rewrite IHw; auto.
  - intro; simpl.
    f_equal.
    apply list_max_ext.
    intro d; split; intro pf.
    + rewrite List.in_map_iff in *.
      destruct pf as [m [Hm1 Hm2]].
      exists (back G H B b0 m).
      split.
      * rewrite H0 in Hm1; auto.
      * apply G.
    + rewrite List.in_map_iff in *.
      destruct pf as [m [Hm1 Hm2]].
      exists (forward G H B b0 m).
      split.
      * rewrite H0.
        rewrite back_forward; auto.
      * apply H.
Qed.

Lemma bisim_mate {G H} {p} {n} (B : InvertibleBisim G H) s s' :
  bisim G H B s s' -> mate p s n -> mate p s' n.
Proof.
  intros b [w [w_depth w_min]].
  exists (bisim_win B s s' b w); split.
  - rewrite bisim_win_depth; auto.
  - intro w'.
    rewrite bisim_win_depth.
    apply bisim_sym in b.
    rewrite <- bisim_win_depth with
      (s' := s) (b := b).
    apply w_min.
Qed.

CoFixpoint bisim_no_worse {G H} {p} (B : InvertibleBisim G H) s s'
  (b : bisim G H B s s') (n : no_worse p s) : no_worse p s'.
Proof.
  destruct n.
  - apply atom_draw_no_worse.
    erewrite <- atomic_bisim; eauto.
  - apply atom_win_no_worse.
    erewrite <- atomic_bisim; eauto.
  - apply eloise_no_worse with (m := forward G H B b m).
    + erewrite <- to_play_bisim; eauto.
    + erewrite <- atomic_bisim; eauto.
    + apply bisim_no_worse with (B := B) (s := exec_move s m).
      * apply exec_forward.
      * exact n.
  - apply abelard_no_worse.
    + erewrite <- to_play_bisim; eauto.
    + erewrite <- atomic_bisim; eauto.
    + intro m'.
      pose (m'' := back G H B b m').
      apply bisim_no_worse with (B := B) (s := exec_move s m'').
      * apply exec_back.
      * apply n.
Defined.

CoFixpoint bisim_draw {G H} (B : InvertibleBisim G H) s s'
  (b : bisim G H B s s') 
  (d : draw s) : draw s'.
Proof.
  destruct d.
  - apply atom_draw.
    erewrite <- atomic_bisim; eauto.
  - apply play_draw with (m := forward G H B b m) (p := p).
    + erewrite <- to_play_bisim; eauto.
    + erewrite <- atomic_bisim; eauto.
    + intro m'.
      pose (m'' := back G H B b m').
      specialize (n m'').
      apply bisim_no_worse with (B := B) (s := exec_move s m'').
      -- apply exec_back.
      -- exact n.
    + apply bisim_draw with (B := B) (s :=
        exec_move s m).
      * apply exec_forward.
      * exact d.
Defined.
