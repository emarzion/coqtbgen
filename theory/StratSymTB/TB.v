Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Compare_dec.

Require Import Games.Util.ListUtil.
Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Draw.
Require Import Games.Game.Win.
Require Import Games.Game.NoWorse.
Require Import Games.Game.Strategy.

Require Import TBGen.Util.Bisim.
Require Import TBGen.Util.IntMap.
Require Import TBGen.Util.IntHash.
Require Import Games.Util.Dec.
Require Import TBGen.Util.Loop.
Require Import TBGen.Util.ListUtil.
Require Import TBGen.StratSymTB.Closed.

Class FinPred {G} (P : GameState G -> Prop) : Type := {
  enum_states : list (GameState G);
  enum_P_wins : Player -> list (GameState G);

  enum_states_correct : forall s, In s enum_states;
  enum_P_wins_correct1 : forall s pl,
    In s (enum_P_wins pl) -> atomic_res s = Some (Win pl);
  enum_wins_correct2 : forall s pl,
    atomic_res s = Some (Win pl) -> P s -> In s (enum_P_wins pl)
  }.

Class NiceGame (G : Game) : Prop := {
  atomic_win_opp : forall (s : GameState G) pl,
    atomic_res s = Some (Win pl) ->
    to_play s = opp pl
  }.

Class Reversible (G : Game) : Type := {
  enum_preds : GameState G -> list (GameState G);

  enum_preds_correct1 : forall s s' : GameState G,
    In s (enum_preds s') -> {m : Move s & exec_move s m = s'};
  enum_preds_correct2 : forall (s : GameState G)
    (m : Move s), In s (enum_preds (exec_move s m))
  }.

Class Symmetry (G : Game) : Type := {
  auto : InvertibleBisim G G;
  auto_refl : forall s, bisim G G auto s s;
  auto_sym : forall s s', bisim G G auto s s' -> bisim G G auto s' s;
  auto_trans : forall s1 s2 s3, bisim G G auto s1 s2 -> bisim G G auto s2 s3 -> bisim G G auto s1 s3;
  normalize : GameState G -> GameState G;
  normalize_bisim : forall s, bisim G G auto s (normalize s);
  normalize_functional : forall s s', bisim G G auto s s' -> normalize s = normalize s';
  }.

Section TB.

Context {G : Game}.
Context `{NiceGame G}.
Context `{Reversible G}.
Context `{IntHash (GameState G)}.
Context `{forall s : GameState G, Discrete (Move s)}.
Context `{Symmetry G}.

Context {M : Type -> Type}.
Context `{IntMap M}.

Context `{P : GameState G -> Prop}.
Context `{FinPred G P}.
Context `{Closed G P}.
Context `{Bisim_closed G auto P}.
Context `{Pd : Dec1 _ P}.

Lemma P_to_Pnorm : forall s, P s -> P (normalize s).
Proof.
  intros.
  apply bisim_closed with (s := s); auto.
  apply normalize_bisim.
Qed.

Lemma Pnorm_to_P : forall s, P (normalize s) -> P s.
Proof.
  intros.
  apply bisim_closed with (s := normalize s); auto.
  apply auto_sym.
  apply normalize_bisim.
Qed.

Definition enum_norm_wins pl : list (GameState G) :=
  nodup IntHash_dec (map normalize (enum_P_wins pl)).

Lemma enum_norm_wins_correct1 : forall s pl,
  In s (enum_norm_wins pl) -> exists s',
    normalize s' = s /\ atomic_res s' = Some (Win pl).
Proof.
  unfold enum_norm_wins.
  intros s pl pf.
  rewrite nodup_In in pf.
  rewrite in_map_iff in pf.
  destruct pf as [s' [Hs'1 Hs'2]].
  exists s'; split; auto.
  apply enum_P_wins_correct1; auto.
Qed.

Lemma enum_norm_wins_correct2 : forall s pl, P s ->
  atomic_res s = Some (Win pl) -> In (normalize s) (enum_norm_wins pl).
Proof.
  unfold enum_norm_wins.
  intros s pl pf1 pf2.
  rewrite nodup_In.
  rewrite in_map_iff.
  exists s; split; auto.
  apply enum_wins_correct2; auto.
Qed.

Definition win_to_normal_win : forall s pl,
  win pl s -> win pl (normalize s).
Proof.
  intros s pl w.
  apply bisim_win with (s := s) (B := auto).
  apply normalize_bisim.
  exact w.
Defined.

Definition win_of_normal_win : forall s pl,
  win pl (normalize s) -> win pl s.
Proof.
  intros s pl w.
  apply bisim_win with (s := normalize s) (B := Bisim_sym auto).
  apply normalize_bisim.
  exact w.
Defined.

Definition mate_of_normal_mate : forall s pl n,
  mate pl (normalize s) n -> mate pl s n.
Proof.
  intros s pl w.
  apply bisim_mate with (B := Bisim_sym auto).
  apply normalize_bisim.
Defined.

Definition mate_to_normal_mate : forall s pl n,
  mate pl s n -> mate pl (normalize s) n.
Proof.
  intros s pl w.
  apply bisim_mate with (B := auto).
  apply normalize_bisim.
Defined.

Lemma atomic_res_normalize s : atomic_res (normalize s) = atomic_res s.
Proof.
  symmetry.
  eapply atomic_bisim.
  apply normalize_bisim.
Qed.

Lemma to_play_normalize s : to_play (normalize s) = to_play s.
Proof.
  symmetry.
  eapply to_play_bisim.
  apply normalize_bisim.
Qed.

Lemma normalize_idem s :
  normalize (normalize s) = normalize s.
Proof.
  symmetry.
  apply normalize_functional.
  apply normalize_bisim.
Qed.

Variant Step :=
  | Eloise : Step
  | Abelard : Step.

Definition switch : Step -> Step :=
  fun s =>
    match s with
    | Eloise => Abelard
    | Abelard => Eloise
    end.

Definition step_player : Step -> Player -> Player :=
  fun s =>
    match s with
    | Eloise => fun pl => pl
    | Abelard => opp
    end.

Record TB : Type := {
  curr : nat;
  last_step : Step;

  white_positions : M (Player * nat);
  black_positions : M (Player * nat);

  last_white_positions : list (GameState G);
  last_black_positions : list (GameState G)
  }.

Definition tb_lookup (tb : TB) (s : GameState G) : option (Player * nat) :=
  match to_play s with
  | White => hash_lookup (normalize s) (white_positions tb)
  | Black => hash_lookup (normalize s) (black_positions tb)
  end.

Definition tag (winner : Player) (n : nat) (s : GameState G) :=
  (s, (winner, n)).

Definition add_positions (m : M (Player * nat)) (winner : Player) (n : nat)
  (ps : list (GameState G)) : M (Player * nat) :=
  hash_adds (map (tag winner n) ps) m.

Definition eloise_step (tb : TB) (pl : Player) : list (GameState G) :=
  let prev :=
    match pl with
    | White => last_black_positions tb
    | Black => last_white_positions tb
    end in
  let m :=
    match pl with
    | White =>
        add_positions
          (white_positions tb)
          (step_player (last_step tb) White)
          (curr tb)
          (last_white_positions tb)
    | Black =>
        add_positions
          (black_positions tb)
          (step_player (last_step tb) Black)
          (curr tb)
          (last_black_positions tb)
    end in
  let candidates := map normalize (concat (map enum_preds prev)) in
  let candidates' :=
    filter_dec P (filter_Nones (fun s => hash_lookup s m) candidates) in
  nodup IntHash_dec candidates'.

Definition abelard_step (tb : TB) (pl : Player) : list (GameState G) :=
  let prev :=
    match pl with
    | White => last_black_positions tb
    | Black => last_white_positions tb
    end in
  let m :=
    match pl with
    | White =>
        add_positions
          (white_positions tb)
          (step_player (last_step tb) White)
          (curr tb)
          (last_white_positions tb)
    | Black =>
        add_positions
          (black_positions tb)
          (step_player (last_step tb) Black)
          (curr tb)
          (last_black_positions tb)
    end in
  let m' :=
    match pl with
    | Black =>
        add_positions
          (white_positions tb)
          (step_player (last_step tb) White)
          (curr tb)
          (last_white_positions tb)
    | White =>
        add_positions
          (black_positions tb)
          (step_player (last_step tb) Black)
          (curr tb)
          (last_black_positions tb)
    end in
  let candidates := map normalize (concat (map enum_preds prev)) in
  let candidates' :=
    filter_dec P (filter_Nones (fun s => hash_lookup s m) candidates) in
  let candidates'' := filter
    (fun s => forallb (fun m =>
      match hash_lookup (normalize (exec_move s m)) m' with
      | Some (pl',_) => player_eqb (opp pl) pl'
      | None => false
      end) (enum_moves s)) candidates' in
  nodup IntHash_dec candidates''.

Definition TB_init : TB := {|
  curr := 0;
  last_step := Abelard;

  white_positions := empty;
  black_positions := empty;

  last_white_positions := nodup IntHash_dec (enum_norm_wins Black);
  last_black_positions := nodup IntHash_dec (enum_norm_wins White);
  |}.

Definition TB_step (tb : TB) : TB := {|
  curr := S (curr tb);
  last_step := switch (last_step tb);

  white_positions := add_positions
    (white_positions tb)
    (step_player (last_step tb) White)
    (curr tb)
    (last_white_positions tb);
  black_positions := add_positions
    (black_positions tb)
    (step_player (last_step tb) Black)
    (curr tb)
    (last_black_positions tb);

  last_white_positions :=
    match last_step tb with
    | Eloise => abelard_step tb White
    | Abelard => eloise_step tb White
    end;
  last_black_positions :=
    match last_step tb with
    | Eloise => abelard_step tb Black
    | Abelard => eloise_step tb Black
    end
  |}.

Definition num_left (tb : TB) : nat :=
  length enum_states -
  size (white_positions tb) -
  size (black_positions tb).

Definition num_left_decr : forall tb,
  num_left (TB_step tb) <= num_left tb.
Proof.
  unfold num_left.
  intros []; simpl.
  unfold add_positions.
  pose proof (hash_size_adds_le
    (map (tag (step_player last_step0 White) curr0) last_white_positions0)
    white_positions0).
  pose proof (hash_size_adds_le
    (map (tag (step_player last_step0 Black) curr0) last_black_positions0)
    black_positions0).
  lia.
Qed.

Definition TB_loop_data : loop_data TB := {|
  measure := num_left;
  step := TB_step;
  step_measure := num_left_decr
  |}.

Definition TB_final : TB :=
  loop TB_loop_data TB_init.

Record TB_valid (tb : TB) : Type := {

  white_good : good (white_positions tb);
  black_good : good (black_positions tb);

  mate_tb : forall {s pl n},
    P s -> n < curr tb -> mate pl s n ->
    tb_lookup tb s = Some (pl, n);

  tb_mate : forall {s pl n},
    tb_lookup tb s = Some (pl, n) ->
    mate pl s n;

  tb_small : forall {s pl n},
    tb_lookup tb s = Some (pl, n) ->
    n < curr tb;

  tb_white : forall {s pl n},
    hash_lookup s (white_positions tb) = Some (pl, n) ->
    to_play s = White;

  tb_black : forall {s pl n},
    hash_lookup s (black_positions tb) = Some (pl, n) ->
    to_play s = Black;

  tb_None : forall {s pl} (w : win pl s), P s ->
    tb_lookup tb s = None ->
    curr tb <= depth w;

  mate_lwp : forall {s pl}, P s ->
    to_play s = White ->
    mate pl s (curr tb) ->
    In (normalize s) (last_white_positions tb);

  lwp_mate : forall {s},
    In s (last_white_positions tb) ->
    mate (step_player (last_step tb) White) s (curr tb);

  mate_lbp : forall {s pl}, P s ->
    to_play s = Black ->
    mate pl s (curr tb) ->
    In (normalize s) (last_black_positions tb);

  lbp_mate : forall {s},
    In s (last_black_positions tb) ->
    mate (step_player (last_step tb) Black) s (curr tb);

  lwp_NoDup : NoDup (last_white_positions tb);

  lbp_NoDup : NoDup (last_black_positions tb);

  lwp_disj : forall s, In s (last_white_positions tb) -> hash_lookup s (white_positions tb) = None;

  lbp_disj : forall s, In s (last_black_positions tb) -> hash_lookup s (black_positions tb) = None;

  lwp_white : forall s, In s (last_white_positions tb) -> to_play s = White;

  lbp_black : forall s, In s (last_black_positions tb) -> to_play s = Black;

  }.

Lemma step_player_white (tb : TB) (v : TB_valid tb) :
  forall {s : GameState G} {pl},
  P s ->
  to_play s = White ->
  mate pl s (curr tb) ->
  pl = step_player (last_step tb) White.
Proof.
  intros s pl s_p s_play sm.
  pose proof (mate_lwp _ v s_p s_play sm) as HIn.
  pose (lwp_mate _ v HIn) as sm'.
  destruct sm as [w _].
  destruct sm' as [w' _].
  apply win_of_normal_win in w'.
  exact (unique_winner _ _ _ w w').
Qed.

Lemma step_player_black (tb : TB) (v : TB_valid tb) :
  forall {s : GameState G} {pl},
  P s ->
  to_play s = Black ->
  mate pl s (curr tb) ->
  pl = step_player (last_step tb) Black.
Proof.
  intros s pl s_p s_play sm.
  pose proof (mate_lbp _ v s_p s_play sm) as HIn.
  pose (lbp_mate _ v HIn) as sm'.
  destruct sm as [w _].
  destruct sm' as [w' _].
  apply win_of_normal_win in w'.
  exact (unique_winner _ _ _ w w').
Qed.

Lemma NoDup_app {X} : forall (xs ys : list X),
  NoDup xs -> NoDup ys -> disj xs ys -> NoDup (xs ++ ys).
Proof.
  induction xs as [|x xs']; intros ys nd_xs nd_ys d_xs_ys.
  - exact nd_ys.
  - simpl.
    constructor.
    + rewrite in_app_iff.
      intros [in_x_xs'|in_x_ys].
      * now inversion nd_xs.
      * apply (d_xs_ys x); [now left|auto].
    + apply IHxs'; auto.
      * now inversion nd_xs.
      * intros y in_y_xs' in_y_ys.
        apply (d_xs_ys y); [now right|auto].
Qed.

Lemma TB_init_valid : TB_valid TB_init.
Proof.
  constructor.
  - constructor.
  - constructor.
  - simpl.
    intros; lia.
  - intros s pl n Htb.
    unfold tb_lookup, TB_init in Htb; simpl in Htb.
    destruct (to_play s);
    now rewrite hash_lookup_empty in Htb.
  - intros s pl n Htb.
    unfold tb_lookup, TB_init in Htb; simpl in Htb.
    destruct (to_play s);
    now rewrite hash_lookup_empty in Htb.
  - intros s pl n Htb; simpl in Htb.
    now rewrite hash_lookup_empty in Htb.
  - intros s pl n Htb; simpl in Htb.
    now rewrite hash_lookup_empty in Htb.
  - intros; simpl; lia.
  - intros s pl s_p s_play [w [w_d _]].
    destruct w; simpl in *; try lia.
    rewrite (atomic_win_opp _ _ e) in s_play.
    assert (pl = Black) as s_pl by (now apply opp_inj).
    rewrite nodup_In.
    apply enum_norm_wins_correct2; congruence.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    assert (atomic_res s = Some (Win Black)) as s_res.
    { destruct (enum_norm_wins_correct1 _ _ HIn) as [s' [Hs'1 Hs'2]].
      rewrite <- Hs'1.
      rewrite atomic_res_normalize; auto.
    }
    exists (atom_win s_res); split; auto.
    intro w'; simpl; lia.
  - intros s pl s_p s_play [w [w_d _]].
    destruct w; simpl in *; try lia.
    rewrite (atomic_win_opp _ _ e) in s_play.
    assert (pl = White) as s_pl by (now apply opp_inj).
    rewrite nodup_In.
    apply enum_norm_wins_correct2; congruence.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    assert (atomic_res s = Some (Win White)) as s_res.
    { destruct (enum_norm_wins_correct1 _ _ HIn) as [s' [Hs'1 Hs'2]].
      rewrite <- Hs'1.
      rewrite atomic_res_normalize; auto.
    }
    exists (atom_win s_res); split; auto.
    intro w'; simpl; lia.
  - apply NoDup_nodup.
  - apply NoDup_nodup.
  - intros.
    now apply hash_lookup_empty.
  - intros.
    now apply hash_lookup_empty.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    destruct (enum_norm_wins_correct1 _ _ HIn) as [s' [Hss' s'_res]].
    rewrite <- Hss'.
    rewrite to_play_normalize.
    now rewrite (atomic_win_opp _ _ s'_res).
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    destruct (enum_norm_wins_correct1 _ _ HIn) as [s' [Hss' s'_res]].
    rewrite <- Hss'.
    rewrite to_play_normalize.
    now rewrite (atomic_win_opp _ _ s'_res).
Defined.

Lemma map_tag_functional : forall pl n ps,
  functional (map (tag pl n) ps).
Proof.
  intros pl n ps.
  intros s [q1 k] [q2 l] Hq1 Hq2.
  rewrite in_map_iff in Hq1, Hq2.
  destruct Hq1 as [t [Ht _]].
  destruct Hq2 as [u [Hu _]].
  unfold tag in Ht, Hu.
  congruence.
Qed.

Lemma mate_S_lemma (tb : TB) (v : TB_valid tb) :
  forall {s : GameState G} {pl}, P s ->
  mate pl s (S (curr tb)) ->
  { m : Move s & mate pl (exec_move s m) (curr tb) }.
Proof.
  intros s pl s_p [w [w_d w_m]].
  destruct w.
  - now simpl in w_d.
  - exists m, w; split.
    + simpl in w_d; lia.
    + intro w'.
      pose (w'' := eloise_win e e0 m w').
      pose (w_m w'').
      simpl in l; lia.
  - destruct (None_or_all_Some (fun m =>
      tb_lookup tb (exec_move b m)) (enum_moves b)) as [[m tb_sm]|[ys Hys]].
    + assert (depth (w m) = curr tb) as wm_d.
      { apply PeanoNat.Nat.le_antisymm.
        * simpl in w_d.
          inversion w_d.
          apply list_max_is_max.
          rewrite in_map_iff.
          exists m; split; auto.
          apply enum_all.
        * refine (tb_None _ v (w m) _ tb_sm).
          now apply closed.
      }
      clear w_d.
      exists m, (w m).
      split; [simpl; congruence|].
      intro w'.
      rewrite wm_d.
      refine (tb_None _ v w' _ tb_sm).
      now apply closed.
    + exfalso.
      assert (forall m, {k : nat & k < curr tb /\ tb_lookup tb (exec_move b m) = Some (pl, k)}).
      { intro m.
        destruct (tb_lookup tb (exec_move b m)) as [[pl' k]|] eqn:tb_sm.
        + exists k; split.
          exact (tb_small _ v tb_sm).
          do 2 f_equal.
          apply (unique_winner _ _ (exec_move b m)).
          * now destruct (tb_mate _ v tb_sm).
          * apply w.
        + exfalso.
          eapply (not_None_in_Somes).
          rewrite <- tb_sm.
          rewrite <- Hys.
          rewrite in_map_iff.
          exists m; split; auto.
          apply enum_all.
      }
      assert (forall m, {w : win pl (exec_move b m) & depth w < curr tb}) as ws.
      { intro m.
        destruct (X m) as [k [Hk_small tb_sm]].
        destruct (tb_mate _ v tb_sm) as [w' ?].
        exists w'; lia.
      }
      pose (w' := abelard_win e e0 (fun m => projT1 (ws m))).
      assert (depth w' <= curr tb) as w'_d.
      { simpl.
        destruct (curr tb).
        + destruct (enum_moves b) eqn:Hmoves.
          * destruct (nil_atomic_res Hmoves); congruence.
          * destruct (ws m); lia.
        + apply le_n_S.
          rewrite list_max_le.
          rewrite Forall_forall.
          intros x HIn.
          rewrite in_map_iff in HIn.
          destruct HIn as [m [Hm _]].
          destruct (ws m).
          simpl in Hm; lia.
      }
      pose (w_m w'); lia.
Defined.

Lemma mate_eq {s : GameState G} {pl pl'} {n n'} :
  mate pl s n ->
  mate pl' s n' ->
  n = n'.
Proof.
  intros sm sm'.
  assert (pl = pl') as Heq.
  { destruct sm as [w _].
    destruct sm' as [w' _].
    exact (unique_winner _ _ _ w w').
  }
  rewrite Heq in sm.
  destruct sm as [w [w_d w_m]].
  destruct sm' as [w' [w'_d w'_m]].
  rewrite <- w_d, <- w'_d.
  apply PeanoNat.Nat.le_antisymm.
  - apply w_m.
  - apply w'_m.
Qed.

Lemma in_concat_sig {X} `{Discrete X} (xss : list (list X)) (x : X) :
  In x (concat xss) -> { xs : list X & In xs xss /\ In x xs }.
Proof.
  induction xss as [|xs xss']; intro HIn.
  - destruct HIn.
  - simpl in HIn.
    rewrite in_app_iff in HIn.
    destruct (in_dec x xs).
    + exists xs; split; auto; now left.
    + destruct IHxss'.
      * tauto.
      * exists x0.
        split; [now right|tauto].
Defined.

Lemma TB_step_valid : forall tb, TB_valid tb
  -> TB_valid (TB_step tb).
Proof.
  intros tb v.
  constructor.
  (* white_good *)
  - simpl.
    apply good_as.
    + apply (white_good _ v).
    + rewrite map_map.
      simpl.
      rewrite map_id.
      exact (lwp_NoDup _ v).
    + intros s [pl n] HIn.
      apply (lwp_disj _ v).
      rewrite in_map_iff in HIn.
      destruct HIn as [s' [Hs' ?]].
      inversion Hs'; congruence.
  (* black_good *)
  - simpl.
    apply good_as.
    + apply (black_good _ v).
    + rewrite map_map.
      simpl.
      rewrite map_id.
      exact (lbp_NoDup _ v).
    + intros s [pl n] HIn.
      apply (lbp_disj _ v).
      rewrite in_map_iff in HIn.
      destruct HIn as [s' [Hs' ?]].
      inversion Hs'; congruence.
  (* mate_tb *)
  - simpl; intros s pl n s_p n_small sm.
    destruct (le_lt_eq_dec _ _ n_small) as [pf|pf].
    + pose proof (PeanoNat.lt_S_n _ _ pf) as pf'.
      pose proof (mate_tb _ v s_p pf' sm) as Htb.
      unfold tb_lookup in *.
      destruct (to_play s) eqn:s_play.
      * simpl.
        unfold add_positions.
        rewrite hash_lookup_adds_nIn; auto.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        intro HIn.
        rewrite lwp_disj in Htb; congruence.
      * simpl.
        unfold add_positions.
        rewrite hash_lookup_adds_nIn; auto.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        intro HIn.
        rewrite lbp_disj in Htb; congruence.
    + inversion pf as [pf'].
      unfold tb_lookup.
      destruct (to_play s) eqn:s_play.
      * simpl.
        unfold add_positions.
        erewrite hash_lookup_adds;
        [reflexivity| apply map_tag_functional|].
        rewrite in_map_iff.
        exists (normalize s).
        rewrite pf' in sm.
        pose proof (step_player_white _ v s_p s_play sm) as Hpl.
        pose (mate_lwp _ v s_p s_play sm) as Hpl'.
        split; auto.
        now rewrite Hpl.
      * simpl.
        unfold add_positions.
        erewrite hash_lookup_adds;
        [reflexivity| apply map_tag_functional|].
        rewrite in_map_iff.
        exists (normalize s).
        rewrite pf' in sm.
        pose proof (step_player_black _ v s_p s_play sm) as Hpl.
        pose (mate_lbp _ v s_p s_play sm) as Hpl'.
        split; auto.
        now rewrite Hpl.
  (* tb_mate *)
  - unfold tb_lookup.
    intros s pl n Htb.
    destruct (to_play s) eqn:s_play.
    + simpl in Htb.
      unfold add_positions in Htb.
      destruct (hash_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * destruct (in_map_sig pf) as [s' [Hs'1 Hs'2]].
        unfold tag in Hs'1.
        epose (lwp_mate _ v Hs'2).
        inversion Hs'1; subst.
        apply mate_of_normal_mate; auto.
      * apply (tb_mate _ v).
        unfold tb_lookup.
        now rewrite s_play.
    + simpl in Htb.
      unfold add_positions in Htb.
      destruct (hash_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * destruct (in_map_sig pf) as [s' [Hs'1 Hs'2]].
        unfold tag in Hs'1.
        epose (lbp_mate _ v Hs'2).
        inversion Hs'1; subst.
        apply mate_of_normal_mate; auto.
      * apply (tb_mate _ v).
        unfold tb_lookup.
        now rewrite s_play.
  (* tb_small *)
  - intros s pl n Htb.
    unfold tb_lookup in Htb.
    destruct (to_play s) eqn:s_play; simpl in *.
    + destruct (hash_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * rewrite in_map_iff in pf.
        destruct pf as [s' [Hs'1 Hs'2]].
        inversion Hs'1; lia.
      * cut (n < curr tb); [lia|].
        eapply (tb_small _ v).
        unfold tb_lookup; rewrite s_play; eauto.
    + destruct (hash_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * rewrite in_map_iff in pf.
        destruct pf as [s' [Hs'1 Hs'2]].
        inversion Hs'1; lia.
      * cut (n < curr tb); [lia|].
        eapply (tb_small _ v).
        unfold tb_lookup; rewrite s_play; eauto.
  (* tb_white *)
  - intros s pl n Htb.
    simpl in Htb.
    destruct (hash_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
    + rewrite in_map_iff in pf.
      destruct pf as [s' [Hs'1 Hs'2]].
      inversion Hs'1; subst.
      now apply (lwp_white _ v).
    + eapply (tb_white _ v); exact pf.
  (* tb_black *)
  - intros s pl n Htb.
    simpl in Htb.
    destruct (hash_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
    + rewrite in_map_iff in pf.
      destruct pf as [s' [Hs'1 Hs'2]].
      inversion Hs'1; subst.
      now apply (lbp_black _ v).
    + eapply (tb_black _ v); exact pf.
  (* tb_None *)
  - intros s pl w s_p tb_s.
    unfold tb_lookup in tb_s.
    simpl in *.
    destruct (to_play s) eqn:s_play.
    + destruct (hash_lookup_adds_None_invert tb_s) as [s_lwp tb'_s].
      epose proof (tb_None _ v w s_p) as Hs.
      unfold tb_lookup in Hs.
      rewrite s_play in Hs.
      specialize (Hs tb'_s).
      destruct (PeanoNat.Nat.eq_dec (depth w) (curr tb)); [|lia].
      cut (mate pl s (curr tb)).
      { intro sm.
        elim s_lwp.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        apply (mate_lwp _ v s_p s_play sm).
      }
      exists w; split; auto.
      intro w'.
      rewrite e.
      apply (tb_None _ v w'); auto.
      unfold tb_lookup; now rewrite s_play.
    + destruct (hash_lookup_adds_None_invert tb_s) as [s_lbp tb'_s].
      epose proof (tb_None _ v w) as Hs.
      unfold tb_lookup in Hs.
      rewrite s_play in Hs.
      specialize (Hs s_p tb'_s).
      destruct (PeanoNat.Nat.eq_dec (depth w) (curr tb)); [|lia].
      cut (mate pl s (curr tb)).
      { intro sm.
        elim s_lbp.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        apply (mate_lbp _ v s_p s_play sm).
      }
      exists w; split; auto.
      intro w'.
      rewrite e.
      apply (tb_None _ v w'); auto.
      unfold tb_lookup; now rewrite s_play.
  (* mate_lwp *)
  - intros s pl s_p s_play sm; simpl in *.
    destruct (last_step tb) eqn:tb_step.
    + unfold abelard_step.
      rewrite nodup_In.
      rewrite filter_In; split.
      * rewrite filter_dec_In; split; [|now apply P_to_Pnorm].
        rewrite In_filter_Nones_iff; split.
        -- rewrite tb_step; simpl.
           apply not_Some_None.
           intros [pl' n] tb_s.
           destruct (hash_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1; subst.
              pose (lwp_mate _ v Hs'2) as m.
              apply mate_of_normal_mate in m.
              pose (mate_eq sm m); lia.
           ++ epose (tb_small _ v).
              unfold tb_lookup in l.
              rewrite s_play in l.
              specialize (l pf).
              epose (tb_mate _ v).
              unfold tb_lookup in m.
              rewrite s_play in m.
              specialize (m pf).
              pose (mate_eq sm m); lia.
        -- destruct (mate_S_lemma _ v s_p sm) as [m smm].
           apply (mate_lbp _ v) in smm; [|now apply closed |now rewrite 
             to_play_exec_move, s_play].
           pose proof (inv_forward_correct G G _ s m _
             (normalize_bisim (exec_move s m))) as pf.
           pose proof (exec_inv_forward _ _ _ s m _
             (normalize_bisim (exec_move s m))) as pf'.
           destruct inv_forward; simpl in *.
           rewrite (normalize_functional _ _ pf').
           apply in_map.
           rewrite in_concat.
           exists (enum_preds (normalize (exec_move s m))).
           split.
           ++ apply in_map; auto.
           ++ rewrite <- pf; apply enum_preds_correct2.
      * rewrite forallb_forall.
        intros m _.
        destruct (mate_S_lemma _ v s_p sm) as [m' smm'].
        assert (to_play (exec_move s m') = Black) as sm'_play
          by now rewrite to_play_exec_move, s_play.
        pose proof (step_player_black _ v (closed s s_p m') sm'_play smm') as Hpl.
        rewrite tb_step in Hpl; simpl in Hpl.
        destruct hash_lookup as [[pl' n']|] eqn:tb_sm.
        -- destruct (hash_lookup_adds_invert _ _ _ _ tb_sm) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1.
              now rewrite tb_step.
           ++ destruct pl'; [|reflexivity].
              absurd (Black = White); [discriminate|].
              apply (unique_winner _ _ s).
              ** rewrite Hpl in sm.
                 now destruct sm.
              ** apply win_of_normal_win.
                 apply eloise_win with (m := m); auto.
                 { rewrite atomic_res_normalize.
                   destruct (atomic_res s) eqn:s_res; auto.
                   pose proof (enum_all m) as HIn.
                   rewrite <- atomic_res_normalize in s_res.
                   rewrite (atomic_res_nil s_res) in HIn; destruct HIn.
                 }
                 { rewrite to_play_normalize; auto. }
                 epose (@tb_mate _ v (exec_move (normalize s) m)).
                 unfold tb_lookup in m0.
                 rewrite to_play_exec_move in m0.
                 rewrite to_play_normalize in m0.
                 rewrite s_play in m0; simpl in m0.
                 destruct (m0 _ _ pf); eauto.
        -- subst.
           rewrite tb_step in tb_sm; simpl in *.
           destruct (hash_lookup_adds_None_invert tb_sm).
           destruct sm as [w [w_d wm]].
           destruct w; [simpl in w_d; lia|congruence|].
           pose (tb_None _ v (w (back G G auto (normalize_bisim b) m))).
           unfold tb_lookup in l.
           rewrite to_play_exec_move in l.
           rewrite s_play in l; simpl in l.
           assert (normalize (exec_move b (back G G auto (normalize_bisim b) m)) = normalize (exec_move (normalize b) m)).
           { apply normalize_functional;
             apply exec_back.
           }
           rewrite H10 in l.
           assert (P (exec_move b (back G G auto (normalize_bisim b) m))).
           { now apply closed. }
           specialize (l H11 H9).
           simpl in w_d.
           inversion w_d as [w_d']; clear w_d.
           assert (depth (w (back G G auto (normalize_bisim b) m)) <= curr tb).
           { rewrite <- w_d'.
             apply list_max_is_max.
             rewrite in_map_iff.
             eexists; split; auto.
             apply enum_all.
           }
           assert (mate Black (exec_move b (back G G auto (normalize_bisim b) m)) (curr tb)).
           { exists (w _).
             split; [lia|].
             intro w'.
             assert (depth (w (back G G auto (normalize_bisim b) m)) = curr tb) by lia.
             rewrite H12.
             apply (tb_None _ v w'); auto.
             unfold tb_lookup.
             rewrite to_play_exec_move. rewrite s_play. simpl; auto.
             rewrite H10; auto.
           }
           elim H8.
           rewrite in_map_iff.
           exists (normalize (exec_move (normalize b) m) , (Black, curr tb)).
           simpl; split; [reflexivity|].
           rewrite in_map_iff.
           exists (normalize (exec_move (normalize b) m)); split; [reflexivity|].
           eapply (mate_lbp _ v).
           ++ apply closed; now apply P_to_Pnorm.
           ++ rewrite to_play_exec_move.
           rewrite to_play_normalize.
           rewrite s_play; reflexivity.
           ++ apply bisim_mate with (B := auto) (s' := exec_move (normalize b) m) in X.
           exact X.
           apply exec_back.
    + unfold eloise_step.
      rewrite nodup_In.
      rewrite filter_dec_In; split; [|now apply P_to_Pnorm].
      rewrite In_filter_Nones_iff; split.
      * apply not_Some_None.
        intros [pl' n] tb_s.
        destruct (hash_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
        -- rewrite in_map_iff in pf.
           destruct pf as [s' [Hs'1 Hs'2]].
           inversion Hs'1; subst.
           pose (lwp_mate _ v Hs'2).
           apply mate_of_normal_mate in m.
           pose (mate_eq sm m); lia.
        -- epose (tb_small _ v).
           unfold tb_lookup in l.
           rewrite s_play in l.
           specialize (l pf).
           epose (tb_mate _ v).
           unfold tb_lookup in m.
           rewrite s_play in m.
           specialize (m pf).
           pose (mate_eq sm m); lia.
      * destruct (mate_S_lemma _ v s_p sm) as [m smm].
        pose proof (inv_forward_correct _ _ _ s m _ (normalize_bisim _)).
        pose proof (exec_inv_forward _ _ _ s m _ (normalize_bisim _)).
        destruct inv_forward; simpl in *.
        rewrite (normalize_functional _ _ X).
        apply in_map.
        rewrite in_concat.
        exists (enum_preds (exec_move x m0)).
        split.
        -- apply in_map.
           rewrite H8.
           eapply (mate_lbp _ v).
           ++ now apply closed.
           ++ rewrite to_play_exec_move, s_play; reflexivity.
           ++ exact smm.
        -- apply enum_preds_correct2.
  (* lwp_mate *)
  - intros s HIn; simpl in *.
    destruct (last_step tb) eqn:tb_step; simpl.
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' Hforall].
      rewrite filter_dec_In in HIn'; destruct HIn' as [pf1 pf2].
      rewrite In_filter_Nones_iff in pf1.
      destruct pf1 as [Hs1 Hs2].
      apply in_map_sig in Hs2.
      destruct Hs2 as [t [Ht1 Ht2]].
      destruct (in_concat_sig _ _ Ht2) as [xs [Hxs1 Hxs2]].
      destruct (in_map_sig Hxs1) as [s' [Hs'1 Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hxs2) as [m Hm]; subst.
      pose (lbp_mate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play t = White) as t_play.
      { apply opp_inj.
        rewrite <- (to_play_exec_move m).
        apply (lbp_black _ v); auto.
      }
      destruct sm as [w [w_d w_m]].
      destruct (atomic_res t) eqn:t_res.
      { exfalso.
        pose proof (enum_all m) as pf.
        rewrite (atomic_res_nil t_res) in pf.
        exact pf.
      }
      rewrite forallb_forall in Hforall.
      rewrite tb_step in *.
      simpl in *.
      assert (forall m, {w : win Black (exec_move t m) & depth w <= curr tb /\ minimal w}).
      { intro m'.
        specialize (Hforall (forward G G auto (normalize_bisim _) m') (enum_all _)).
        destruct (hash_lookup
              (normalize
                 (exec_move (normalize t)
                    (forward G G auto (normalize_bisim t) m')))
              (add_positions (black_positions tb) Black
                 (curr tb) (last_black_positions tb))) as [[[|] n]|] eqn:Hsm; try congruence.
        clear Hforall.
        destruct (hash_lookup_adds_invert _ _ _ _ Hsm) as [HIn|tb_sm].
        + destruct (in_map_sig HIn) as [s' [G1 G2]]; inversion G1; subst.
          pose (lbp_mate _ v G2) as sm.
          rewrite tb_step in sm; simpl in sm.
          apply mate_of_normal_mate in sm.
          apply bisim_mate with (B := auto) (s' := exec_move t m') in sm;
            [|apply auto_sym; apply exec_forward].
          destruct sm as [w' []].
          exists w'; split; [lia|auto].
        + pose (@tb_mate _ v (normalize (exec_move (normalize t) (forward G G auto (normalize_bisim t) m'))) Black n) as sm.
          unfold tb_lookup in sm.
          rewrite to_play_normalize in sm.
          rewrite to_play_exec_move in sm.
          rewrite to_play_normalize in sm.
          rewrite t_play in sm; simpl in sm.
          rewrite normalize_idem in sm.
          pose (sm tb_sm) as sm'.
          apply mate_of_normal_mate in sm'.
          apply bisim_mate with (B := auto) (s' := exec_move t m') in sm';
            [| apply auto_sym; apply exec_forward].
          destruct sm' as [w' [w'_d w'_m]].
          exists w'; split; auto.
          pose (@tb_small _ v (exec_move (normalize t) (forward G G auto (normalize_bisim t) m')) Black n).
          unfold tb_lookup in l.
          rewrite to_play_exec_move in l.
          rewrite to_play_normalize in l.
          rewrite t_play in l; specialize (l tb_sm); lia.
      }
      pose (w' := @abelard_win _ Black _ t_res t_play (fun m => projT1 (X m))).
      apply mate_to_normal_mate.
      exists w'; simpl; split.
      * f_equal.
        apply PeanoNat.Nat.le_antisymm.
        -- rewrite list_max_le.
           rewrite Forall_forall.
           intros.
           rewrite in_map_iff in H8.
           destruct H8 as [m' [Hm' _]].
           destruct (X m').
           simpl in *; lia.
        -- apply list_max_is_max.
           rewrite in_map_iff.
           exists m.
           destruct (X m); simpl; split; [|apply enum_all].
           destruct a.
           pose (w_m x); lia.
      * intro w''.
        destruct w''; try congruence.
        simpl; apply le_n_S.
        apply list_max_map.
        intro m'.
        destruct (X m'); simpl.
        apply a.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_dec_In in HIn.
      destruct HIn as [pf1 pf2].
      rewrite In_filter_Nones_iff in pf1.
      destruct pf1 as [Hs1 Hs2].
      apply in_map_sig in Hs2.
      destruct Hs2 as [t [Ht1 Ht2]].
      destruct (in_concat_sig _ _ Ht2) as [xs [Hxs1 Hxs2]].
      destruct (in_map_sig Hxs1) as [s' [Hs'1 Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hxs2) as [m Hm]; subst.
      pose (lbp_mate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play t = White) as s_play.
      { apply opp_inj.
        rewrite <- (to_play_exec_move m).
        apply (lbp_black _ v); auto.
      }
      destruct sm as [w [w_d w_m]].
      destruct (atomic_res t) eqn:s_res.
      { exfalso.
        pose proof (enum_all m) as pf.
        rewrite (atomic_res_nil s_res) in pf.
        exact pf.
      }
      apply mate_to_normal_mate.
      (* can this be cleaned up? *)
      exists (eloise_win s_res s_play m w).
      split; [simpl; congruence|].
      intro w'; simpl.
      destruct w'; simpl in *; try congruence.
      apply le_n_S.
      rewrite w_d.
      destruct (hash_lookup_adds_None_invert Hs1) as [tb_b lwp_b].
      pose (w'' := eloise_win s_res s_play m0 w').
      epose proof (tb_None _ v w'') as Hw'.
      unfold tb_lookup in Hw'.
      rewrite s_play in Hw'.
      assert (P b) as b_p by now apply Pnorm_to_P.
      specialize (Hw' b_p lwp_b).
      simpl in Hw'.
      rewrite map_map in tb_b; simpl in tb_b.
      rewrite map_id in tb_b.
      rewrite PeanoNat.Nat.le_ngt.
      intro pf.
      assert (S (depth w') = (curr tb)) by lia.
      apply tb_b.
      eapply (mate_lwp _ v b_p s_play).
      exists w''; split; auto.
      intro. simpl. rewrite H8.
      eapply (tb_None _ v); auto.
      unfold tb_lookup.
      now rewrite s_play.
  (* mate_lbp *)
  - intros s pl s_p s_play sm; simpl in *.
    destruct (last_step tb) eqn:tb_step.
    + unfold abelard_step.
      rewrite nodup_In.
      rewrite filter_In; split.
      * rewrite filter_dec_In; split; [|now apply P_to_Pnorm].
        rewrite In_filter_Nones_iff; split.
        -- rewrite tb_step; simpl.
           apply not_Some_None.
           intros [pl' n] tb_s.
           destruct (hash_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1; subst.
              pose (lbp_mate _ v Hs'2) as m.
              apply mate_of_normal_mate in m.
              pose (mate_eq sm m); lia.
           ++ epose (tb_small _ v).
              unfold tb_lookup in l.
              rewrite s_play in l.
              specialize (l pf).
              epose (tb_mate _ v).
              unfold tb_lookup in m.
              rewrite s_play in m.
              specialize (m pf).
              pose (mate_eq sm m); lia.
        -- destruct (mate_S_lemma _ v s_p sm) as [m smm].
           apply (mate_lwp _ v) in smm; [| now apply closed |now rewrite 
             to_play_exec_move, s_play].
           pose proof (inv_forward_correct _ _ _ s m _
             (normalize_bisim (exec_move s m))) as pf.
           pose proof (exec_inv_forward _ _ _ s m _
             (normalize_bisim (exec_move s m))) as pf'.
           destruct inv_forward; simpl in *.
           rewrite (normalize_functional _ _ pf').
           apply in_map.
           rewrite in_concat.
           exists (enum_preds (normalize (exec_move s m))).
           split.
           ++ apply in_map; auto.
           ++ rewrite <- pf; apply enum_preds_correct2.
      * rewrite forallb_forall.
        intros m _.
        destruct (mate_S_lemma _ v s_p sm) as [m' smm'].
        assert (to_play (exec_move s m') = White) as sm'_play
          by now rewrite to_play_exec_move, s_play.
        pose proof (step_player_white _ v (closed s s_p m') sm'_play smm') as Hpl.
        rewrite tb_step in Hpl; simpl in Hpl.
        destruct hash_lookup as [[pl' n']|] eqn:tb_sm.
        -- destruct (hash_lookup_adds_invert _ _ _ _ tb_sm) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1.
              now rewrite tb_step.
           ++ destruct pl'; [reflexivity|].
              absurd (White = Black); [discriminate|].
              apply (unique_winner _ _ s).
              ** rewrite Hpl in sm.
                 now destruct sm.
              ** apply win_of_normal_win.
                 apply eloise_win with (m := m); auto.
                 { rewrite atomic_res_normalize.
                   destruct (atomic_res s) eqn:s_res; auto.
                   pose proof (enum_all m) as HIn.
                   rewrite <- atomic_res_normalize in s_res.
                   rewrite (atomic_res_nil s_res) in HIn; destruct HIn.
                 }
                 { rewrite to_play_normalize; auto. }
                 epose (@tb_mate _ v (exec_move (normalize s) m)).
                 unfold tb_lookup in m0.
                 rewrite to_play_exec_move in m0.
                 rewrite to_play_normalize in m0.
                 rewrite s_play in m0; simpl in m0.
                 destruct (m0 _ _ pf); eauto.
        -- subst.
           rewrite tb_step in tb_sm; simpl in *.
           destruct (hash_lookup_adds_None_invert tb_sm).
           destruct sm as [w [w_d wm]].
           destruct w; [simpl in w_d; lia|congruence|].
           pose (tb_None _ v (w (back G G auto (normalize_bisim b) m))).
           unfold tb_lookup in l.
           rewrite to_play_exec_move in l.
           rewrite s_play in l; simpl in l.
           assert (normalize (exec_move b (back G G auto (normalize_bisim b) m)) = normalize (exec_move (normalize b) m)).
           { apply normalize_functional;
             apply exec_back.
           }
           rewrite H10 in l.
           specialize (l (closed _ s_p _) H9).
           simpl in w_d.
           inversion w_d as [w_d']; clear w_d.
           assert (depth (w (back G G auto (normalize_bisim b) m)) <= curr tb).
           { rewrite <- w_d'.
             apply list_max_is_max.
             rewrite in_map_iff.
             eexists; split; auto.
             apply enum_all.
           }
           assert (mate White (exec_move b (back G G auto (normalize_bisim b) m)) (curr tb)).
           { exists (w _).
             split; [lia|].
             intro w'.
             assert (depth (w (back G G auto (normalize_bisim b) m)) = curr tb) by lia.
             rewrite H12.
             apply (tb_None _ v w'); [now apply closed|].
             unfold tb_lookup.
             rewrite to_play_exec_move. rewrite s_play. simpl; auto.
             rewrite H10; auto.
           }
           elim H8.
           rewrite in_map_iff.
           exists (normalize (exec_move (normalize b) m) , (White, curr tb)).
           simpl; split; [reflexivity|].
           rewrite in_map_iff.
           exists (normalize (exec_move (normalize b) m)); split; [reflexivity|].
           eapply (mate_lwp _ v).
           ++ apply closed; now apply P_to_Pnorm.
           ++ rewrite to_play_exec_move.
              rewrite to_play_normalize.
              rewrite s_play; reflexivity.
           ++ apply bisim_mate with (B := auto) (s' := exec_move (normalize b) m) in X.
              exact X.
              apply exec_back.
    + unfold eloise_step.
      rewrite nodup_In.
      rewrite filter_dec_In; split; [|now apply P_to_Pnorm].
      rewrite In_filter_Nones_iff; split.
      * apply not_Some_None.
        intros [pl' n] tb_s.
        destruct (hash_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
        -- rewrite in_map_iff in pf.
           destruct pf as [s' [Hs'1 Hs'2]].
           inversion Hs'1; subst.
           pose (lbp_mate _ v Hs'2).
           apply mate_of_normal_mate in m.
           pose (mate_eq sm m); lia.
        -- epose (tb_small _ v).
           unfold tb_lookup in l.
           rewrite s_play in l.
           specialize (l pf).
           epose (tb_mate _ v).
           unfold tb_lookup in m.
           rewrite s_play in m.
           specialize (m pf).
           pose (mate_eq sm m); lia.
      * destruct (mate_S_lemma _ v s_p sm) as [m smm].
        pose proof (inv_forward_correct _ _ _ s m _ (normalize_bisim _)).
        pose proof (exec_inv_forward _ _ _ s m _ (normalize_bisim _)).
        destruct inv_forward; simpl in *.
        rewrite (normalize_functional _ _ X).
        apply in_map.
        rewrite in_concat.
        exists (enum_preds (exec_move x m0)).
        split.
        -- apply in_map.
           rewrite H8.
           eapply (mate_lwp _ v); eauto.
           ++ now apply closed.
           ++ rewrite to_play_exec_move, s_play; auto.
        -- apply enum_preds_correct2.
  (* lbp_mate *)
  - intros s HIn; simpl in *.
    destruct (last_step tb) eqn:tb_step; simpl.
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' Hforall].
      rewrite filter_dec_In in HIn'.
      destruct HIn' as [pf1 pf2].
      rewrite In_filter_Nones_iff in pf1.
      destruct pf1 as [Hs1 Hs2].
      apply in_map_sig in Hs2.
      destruct Hs2 as [t [Ht1 Ht2]].
      destruct (in_concat_sig _ _ Ht2) as [xs [Hxs1 Hxs2]].
      destruct (in_map_sig Hxs1) as [s' [Hs'1 Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hxs2) as [m Hm]; subst.
      pose (lwp_mate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play t = Black) as t_play.
      { apply opp_inj.
        rewrite <- (to_play_exec_move m).
        apply (lwp_white _ v); auto.
      }
      destruct sm as [w [w_d w_m]].
      destruct (atomic_res t) eqn:t_res.
      { exfalso.
        pose proof (enum_all m) as pf.
        rewrite (atomic_res_nil t_res) in pf.
        exact pf.
      }
      rewrite forallb_forall in Hforall.
      rewrite tb_step in *.
      simpl in *.
      assert (forall m, {w : win White (exec_move t m) & depth w <= curr tb /\ minimal w}).
      { intro m'.
        specialize (Hforall (forward G G auto (normalize_bisim _) m') (enum_all _)).
        destruct (hash_lookup
              (normalize
                 (exec_move (normalize t)
                    (forward G G auto (normalize_bisim t) m')))
              (add_positions (white_positions tb) White
                 (curr tb) (last_white_positions tb))) as [[[|] n]|] eqn:Hsm; try congruence.
        clear Hforall.
        destruct (hash_lookup_adds_invert _ _ _ _ Hsm) as [HIn|tb_sm].
        + destruct (in_map_sig HIn) as [s' [G1 G2]]; inversion G1; subst.
          pose (lwp_mate _ v G2) as sm.
          rewrite tb_step in sm; simpl in sm.
          apply mate_of_normal_mate in sm.
          apply bisim_mate with (B := auto) (s' := exec_move t m') in sm;
            [|apply auto_sym; apply exec_forward].
          destruct sm as [w' []].
          exists w'; split; [lia|auto].
        + pose (@tb_mate _ v (normalize (exec_move (normalize t) (forward G G auto (normalize_bisim t) m'))) White n) as sm.
          unfold tb_lookup in sm.
          rewrite to_play_normalize in sm.
          rewrite to_play_exec_move in sm.
          rewrite to_play_normalize in sm.
          rewrite t_play in sm; simpl in sm.
          rewrite normalize_idem in sm.
          pose (sm tb_sm) as sm'.
          apply mate_of_normal_mate in sm'.
          apply bisim_mate with (B := auto) (s' := exec_move t m') in sm';
            [| apply auto_sym; apply exec_forward].
          destruct sm' as [w' [w'_d w'_m]].
          exists w'; split; auto.
          pose (@tb_small _ v (exec_move (normalize t) (forward G G auto (normalize_bisim t) m')) White n).
          unfold tb_lookup in l.
          rewrite to_play_exec_move in l.
          rewrite to_play_normalize in l.
          rewrite t_play in l; specialize (l tb_sm); lia.
      }
      pose (w' := @abelard_win _ White _ t_res t_play (fun m => projT1 (X m))).
      apply mate_to_normal_mate.
      exists w'; simpl; split.
      * f_equal.
        apply PeanoNat.Nat.le_antisymm.
        -- rewrite list_max_le.
           rewrite Forall_forall.
           intros.
           rewrite in_map_iff in H8.
           destruct H8 as [m' [Hm' _]].
           destruct (X m').
           simpl in *; lia.
        -- apply list_max_is_max.
           rewrite in_map_iff.
           exists m.
           destruct (X m); simpl; split; [|apply enum_all].
           destruct a.
           pose (w_m x); lia.
      * intro w''.
        destruct w''; try congruence.
        simpl; apply le_n_S.
        apply list_max_map.
        intro m'.
        destruct (X m'); simpl.
        apply a.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_dec_In in HIn.
      destruct HIn as [pf1 pf2].
      rewrite In_filter_Nones_iff in pf1.
      destruct pf1 as [Hs1 Hs2].
      apply in_map_sig in Hs2.
      destruct Hs2 as [t [Ht1 Ht2]].
      destruct (in_concat_sig _ _ Ht2) as [xs [Hxs1 Hxs2]].
      destruct (in_map_sig Hxs1) as [s' [Hs'1 Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hxs2) as [m Hm]; subst.
      pose (lwp_mate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play t = Black) as s_play.
      { apply opp_inj.
        rewrite <- (to_play_exec_move m).
        apply (lwp_white _ v); auto.
      }
      destruct sm as [w [w_d w_m]].
      destruct (atomic_res t) eqn:s_res.
      { exfalso.
        pose proof (enum_all m) as pf.
        rewrite (atomic_res_nil s_res) in pf.
        exact pf.
      }
      apply mate_to_normal_mate.
      (* can this be cleaned up? *)
      exists (eloise_win s_res s_play m w).
      split; [simpl; congruence|].
      intro w'; simpl.
      destruct w'; simpl in *; try congruence.
      apply le_n_S.
      rewrite w_d.
      destruct (hash_lookup_adds_None_invert Hs1) as [tb_b lwp_b].
      pose (w'' := eloise_win s_res s_play m0 w').
      epose proof (tb_None _ v w'') as Hw'.
      unfold tb_lookup in Hw'.
      rewrite s_play in Hw'.
      assert (P b) as b_p by now apply Pnorm_to_P.
      specialize (Hw' b_p lwp_b).
      simpl in Hw'.
      rewrite map_map in tb_b; simpl in tb_b.
      rewrite map_id in tb_b.
      rewrite PeanoNat.Nat.le_ngt.
      intro pf.
      assert (S (depth w') = (curr tb)) by lia.
      apply tb_b.
      eapply (mate_lbp _ v b_p s_play).
      exists w''; split; auto.
      intro. simpl. rewrite H8.
      eapply (tb_None _ v); auto.
      unfold tb_lookup.
      now rewrite s_play.
  (* lwp_NoDup *)
  - simpl.
    destruct last_step.
    + unfold abelard_step.
      apply NoDup_nodup.
    + unfold eloise_step.
      apply NoDup_nodup.
  (* lbp_NoDup *)
  - simpl.
    destruct last_step.
    + unfold abelard_step.
      apply NoDup_nodup.
    + unfold eloise_step.
      apply NoDup_nodup.
  (* lwp_disj *)
  - simpl.
    intros s HIn.
    destruct (last_step tb) eqn:tb_step.
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' _].
      rewrite filter_dec_In in HIn'.
      rewrite In_filter_Nones_iff in HIn'.
      rewrite tb_step in HIn'.
      tauto.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_dec_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      rewrite tb_step in HIn.
      tauto.
  (* lbp_disj *)
  - simpl.
    intros s HIn.
    destruct (last_step tb) eqn:tb_step.
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' _].
      rewrite filter_dec_In in HIn'.
      rewrite In_filter_Nones_iff in HIn'.
      rewrite tb_step in HIn'.
      tauto.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_dec_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      rewrite tb_step in HIn.
      tauto.
  (* lwp_white *)
  - simpl; intros s HIn.
    destruct (last_step tb).
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' _].
      rewrite filter_dec_In in HIn'.
      rewrite In_filter_Nones_iff in HIn'.
      destruct HIn' as [[_ HIn] _].
      rewrite in_map_iff in HIn.
      destruct HIn as [t [Ht1 Ht2]].
      rewrite in_concat in Ht2.
      destruct Ht2 as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lbp_black _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      rewrite to_play_normalize.
      now apply opp_inj.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_dec_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      destruct HIn as [[_ HIn'] _].
      rewrite in_map_iff in HIn'.
      destruct HIn' as [t [Ht1 Ht2]].
      rewrite in_concat in Ht2.
      destruct Ht2 as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lbp_black _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      rewrite to_play_normalize.
      now apply opp_inj.
  (* lbp_black *)
  - simpl; intros s HIn.
    destruct (last_step tb).
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' _].
      rewrite filter_dec_In in HIn'.
      rewrite In_filter_Nones_iff in HIn'.
      destruct HIn' as [[_ HIn] _].
      rewrite in_map_iff in HIn.
      destruct HIn as [t [Ht1 Ht2]].
      rewrite in_concat in Ht2.
      destruct Ht2 as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lwp_white _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      rewrite to_play_normalize.
      now apply opp_inj.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_dec_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      destruct HIn as [[_ HIn'] _].
      rewrite in_map_iff in HIn'.
      destruct HIn' as [t [Ht1 Ht2]].
      rewrite in_concat in Ht2.
      destruct Ht2 as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lwp_white _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      rewrite to_play_normalize.
      now apply opp_inj.
Defined.

Definition TB_validity_data : validity_data TB_loop_data.
Proof.
  refine {|
  valid := TB_valid;
  step_valid := _
  |}.
  exact TB_step_valid.
Defined.

Lemma TB_final_valid : TB_valid TB_final.
Proof.
  exact (loop_valid _
    TB_validity_data _ TB_init_valid).
Defined.

Lemma iter_curr : forall k,
  curr (Nat.iter k TB_step TB_init) = k.
Proof.
  induction k.
  - reflexivity.
  - simpl; congruence.
Qed.

Lemma mate_drop : forall {s : GameState G} {pl n}, P s ->
  mate pl s (S n) ->
  { s' : GameState G & (P s' * mate pl s' n)%type }.
Proof.
  intros s pl n s_p sm.
  pose (TBn := Nat.iter n TB_step TB_init).
  assert (TB_valid TBn) as v_n by 
  exact (iter_step_valid _ TB_validity_data n TB_init TB_init_valid).
  epose (mate_S_lemma _ v_n) as sm'.
  unfold TBn in sm'.
  rewrite iter_curr in sm'.
  destruct (sm' s_p sm) as [m sm''].
  exists (exec_move s m); split.
  - now apply closed.
  - exact sm''.
Defined.

Lemma mate_lower : forall {n} {s : GameState G} {pl k}, k <= n ->
  P s ->
  mate pl s n ->
  {s' : GameState G & (P s' * mate pl s' k)%type }.
Proof.
  induction n; intros s pl k k_le s_p sm.
  - destruct k.
    + exists s; split; auto.
    + lia.
  - destruct (le_lt_eq_dec k (S n) k_le) as [pf|pf]; clear k_le.
    + pose proof (le_S_n _ _ pf) as k_le.
      destruct (mate_drop s_p sm) as [s' [s'_p sm']].
      exact (IHn s' pl k k_le s'_p sm').
    + rewrite pf.
      exists s; split; auto.
Defined.

Definition in_decb {X} `{Discrete X}
  (x : X) (xs : list X) : bool :=
  match in_dec x xs with
  | left _ => true
  | right _ => false
  end.

Fixpoint remove {X} `{Discrete X} (x : X) (xs : list X) : list X :=
  match xs with
  | [] => []
  | y :: xs' =>
    match eq_dec x y with
    | left _ => remove x xs'
    | right _ => y :: remove x xs'
    end
  end.

Lemma length_remove_le {X} `{Discrete X} (x : X) (xs : list X) :
  length (remove x xs) <= length xs.
Proof.
  induction xs as [|y xs'].
  - simpl; lia.
  - simpl.
    destruct (eq_dec x y); simpl; lia.
Qed.

Lemma length_remove_lt {X} `{Discrete X} (x : X) (xs : list X) :
  In x xs -> length (remove x xs) < length xs.
Proof.
  induction xs as [|y xs'].
  - intros [].
  - intros [He|HIn].
    + simpl.
      destruct (eq_dec x y); [|congruence].
      pose (length_remove_le x xs'); lia.
    + pose (IHxs' HIn).
      simpl.
      destruct (eq_dec x y); simpl; lia.
Qed.

Lemma In_remove_1 {X} `{Discrete X} (x : X) (xs : list X) :
  forall y, In y (remove x xs) -> y <> x /\ In y xs.
Proof.
  induction xs.
  - intros y [].
  - intros y HIn.
    simpl in HIn.
    destruct (eq_dec x a).
    + destruct (IHxs _ HIn).
      split; auto.
      now right.
    + destruct HIn as [|HIn].
      * split; [congruence|now left].
      * destruct (IHxs _ HIn).
        split; auto.
        now right.
Qed.

Lemma In_remove_2 {X} `{Discrete X} (x : X) (xs : list X) :
  forall y, y <> x /\ In y xs -> In y (remove x xs).
Proof.
  induction xs.
  - intros y [? []].
  - intros y [y_neq [y_eq|HIn]].
    + simpl.
      destruct (eq_dec x a); [congruence|].
      now left.
    + simpl.
      destruct (eq_dec x a).
      * apply IHxs; now split.
      * right; apply IHxs; now split.
Qed.

Lemma In_remove_iff {X} `{Discrete X} (x : X) (xs : list X) :
  forall y, In y (remove x xs) <-> y <> x /\ In y xs.
Proof.
  intro y; split.
  - apply In_remove_1.
  - apply In_remove_2.
Qed.

Lemma sublist_length_lemma {X} `{Discrete X} : forall (xs ys : list X),
  NoDup xs -> (forall x, In x xs -> In x ys) ->
  length xs <= length ys.
Proof.
  induction xs as [|x xs']; intros ys nd_xs xs_ys.
  - simpl; lia.
  - simpl.
    apply (PeanoNat.Nat.le_lt_trans _ (length (remove x ys))).
    + apply IHxs'.
      * now inversion nd_xs.
      * intros y Hy.
        rewrite In_remove_iff; split.
        -- intro Heq.
           inversion nd_xs.
           congruence.
        -- apply xs_ys; now right.
    + apply length_remove_lt.
      apply xs_ys.
      now left.
Qed.

Lemma filter_length {X} (xs : list X) (p : X -> bool) :
  length (filter p xs) +
  length (filter (fun x => negb (p x)) xs) =
  length xs.
Proof.
  induction xs as [|x' xs'].
  - reflexivity.
  - simpl.
    destruct (p x'); simpl; lia.
Qed.

Lemma filter_count_lemma {X} `{Discrete X} (xs ys : list X)
  (p : X -> bool) : NoDup xs ->
  (forall x, In x xs -> In x ys) ->
  (forall x, In x xs -> p x = false) ->
  length (filter p ys) <= length ys - length xs.
Proof.
  intros nd_xs xs_ys xs_np.
  pose (sublist_length_lemma _ _ nd_xs xs_ys).
  pose (filter_length ys p).
  assert (length xs <= length
  (filter (fun x => negb (p x)) ys)).
  { apply sublist_length_lemma; auto.
    intros x Hx.
    rewrite filter_In; split.
    - now apply xs_ys.
    - now rewrite (xs_np x Hx).
  }
  lia.
Qed.

Lemma num_left_lt : forall tb (s : GameState G) pl,
  P s ->
  mate pl s (curr tb) -> TB_valid tb ->
  num_left (step TB_loop_data tb) < num_left tb.
Proof.
  intros.
  unfold num_left.
  simpl.
  destruct (good_to_list _ (white_good _ X0)) as [ws Hws].
  destruct (good_to_list _ (black_good _ X0)) as [bs Hbs].
  unfold add_positions.
  repeat rewrite hash_size_adds; try
  (rewrite map_map;
    unfold tag;
    simpl;
    rewrite map_id).
  - repeat rewrite map_length.
    rewrite (to_list_size _ _ Hws).
    rewrite (to_list_size _ _ Hbs).
    assert (
      length (last_white_positions tb) +
      length (last_black_positions tb) > 0).
    { destruct (to_play s) eqn:s_play.
      + assert (In (normalize s) (last_white_positions tb)).
        { eapply (mate_lwp _ X0); eauto. }
        pose (In_length_pos _ _ H9); lia.
      + assert (In (normalize s) (last_black_positions tb)).
        { eapply (mate_lbp _ X0); eauto. }
        pose (In_length_pos _ _ H9); lia.
    }
    assert (
      length (last_white_positions tb) +
      length (last_black_positions tb) <=
      length enum_states - (
      length ws +
      length bs)).
    { repeat rewrite <- app_length.
      pose (xs := filter (fun s =>
        negb (in_decb s (map fst (ws ++ bs))))
        enum_states).
      apply (PeanoNat.Nat.le_trans _ (length xs)).
      + unfold xs.
        apply sublist_length_lemma.
        * apply NoDup_app; try apply X0.
          intros s' Hs'w Hs'b.
          pose (lwp_white _ X0 _ Hs'w).
          pose (lbp_black _ X0 _ Hs'b).
          congruence.
        * intro s'; rewrite in_app_iff.
          intros [Hw|Hb].
          -- rewrite filter_In.
             split; [apply enum_states_correct|].
             unfold in_decb.
             destruct in_dec as [pf|]; [|auto].
             rewrite map_app in pf.
             rewrite in_app_iff in pf.
             destruct pf as [pf|pf].
             ++ rewrite in_map_iff in pf.
                destruct pf as [[s'' [pl' n']] [? HInw]].
                simpl in *; subst.
                rewrite <- (lookup_in _ _ Hws) in HInw.
                pose (lwp_disj _ X0 _ Hw); congruence.
             ++ rewrite in_map_iff in pf.
                destruct pf as [[s'' [pl' n]] [? Hinb]].
                simpl in *; subst.
                rewrite <- (lookup_in _ _ Hbs) in Hinb.
                pose (tb_black _ X0 Hinb).
                pose (lwp_white _ X0 _ Hw).
                congruence.
          -- rewrite filter_In.
             split; [apply enum_states_correct|].
             unfold in_decb.
             destruct in_dec as [pf|]; [|auto].
             rewrite map_app in pf.
             rewrite in_app_iff in pf.
             destruct pf as [pf|pf].
             ++ rewrite in_map_iff in pf.
                destruct pf as [[s'' [pl' n]] [? Hinw]].
                simpl in *; subst.
                rewrite <- (lookup_in _ _ Hws) in Hinw.
                pose (tb_white _ X0 Hinw).
                pose (lbp_black _ X0 _ Hb).
                congruence.
             ++ rewrite in_map_iff in pf.
                destruct pf as [[s'' [pl' n']] [? HInb]].
                simpl in *; subst.
                rewrite <- (lookup_in _ _ Hbs) in HInb.
                pose (lbp_disj _ X0 _ Hb); congruence.
      + rewrite <- (map_length fst (ws ++ bs)).
        apply filter_count_lemma.
        * rewrite map_app.
          apply NoDup_app; [apply Hws|apply Hbs|].
          intros x Hxw Hxb.
          rewrite in_map_iff in Hxw, Hxb.
          destruct Hxw as [[x' [pl' n']] [? HInw]]; subst.
          destruct Hxb as [[x'' [pl'' n'']] [? HInb]]; simpl in *; subst.
          rewrite <- (lookup_in _ _ Hws) in HInw.
          rewrite <- (lookup_in _ _ Hbs) in HInb.
          pose (tb_white _ X0 HInw).
          pose (tb_black _ X0 HInb).
          congruence.
        * intros s' _.
          apply enum_states_correct.
        * intros y HIn.
          unfold in_decb.
          destruct in_dec; [auto|contradiction].
    }
    lia.
  - apply (lbp_NoDup _ X0).
  - apply (lbp_disj _ X0).
  - apply (lwp_NoDup _ X0).
  - apply (lwp_disj _ X0).
Qed.

Lemma no_final_curr_mate pl (s : GameState G) :
  P s ->
  mate pl s (curr TB_final) -> False.
Proof.
  intros s_p sm.
  pose proof (num_left_lt TB_final s pl s_p sm TB_final_valid).
  pose proof (loop_measure TB_loop_data TB_init).
  unfold TB_final in *.
  simpl in *; lia.
Qed.

Theorem TB_final_lookup_mate : forall s pl n,
  tb_lookup TB_final s = Some (pl, n) ->
  mate pl s n.
Proof.
  intros s pl n Htb.
  exact (tb_mate _ TB_final_valid Htb).
Defined.

Theorem mate_TB_final_lookup : forall s pl n,
  P s ->
  mate pl s n ->
  tb_lookup TB_final s = Some (pl, n).
Proof.
  intros s pl n s_p sm.
  destruct (le_lt_dec (curr TB_final) n) as [pf|].
  - destruct (mate_lower pf s_p sm) as [s' [s'_p sm']].
    elim (no_final_curr_mate _ _ s'_p sm').
  - now apply (mate_tb _ TB_final_valid).
Qed.

Lemma forallb_false {X} (p : X -> bool) (xs : list X) :
  forallb p xs = false -> {x : X & In x xs /\ p x = false}.
Proof.
  induction xs as [|x xs']; simpl; intros pf.
  - discriminate.
  - destruct (p x) eqn:px.
    + destruct (IHxs' pf) as [x' [Hx'1 Hx'2]].
      exists x'; tauto.
    + exists x; tauto.
Defined.

Definition respects_atomic_wins (tb : TB) : Prop :=
  forall s pl, P s -> atomic_res s = Some (Win pl) ->
  tb_lookup tb s = Some (pl, 0).

Lemma TB_final_respects_atomic_wins :
  respects_atomic_wins TB_final.
Proof.
  destruct (loop_iter TB_loop_data TB_init) as [k Hk].
  destruct k.
  - intros s pl s_p s_res.
    unfold TB_final; rewrite Hk.
    simpl.
    pose proof (loop_measure TB_loop_data TB_init) as Hmeasure.
    simpl in Hmeasure.
    rewrite Hk in Hmeasure.
    unfold num_left in Hmeasure.
    simpl in Hmeasure.
    rewrite size_empty in Hmeasure.
    unfold add_positions in Hmeasure.
    assert (length enum_states > 0).
    { apply (In_length_pos _ s).
      apply enum_states_correct.
    }
    destruct (to_play s) eqn:s_play.
    + assert (In (normalize s, (Black, 0)) (map (tag Black 0) (nodup IntHash_dec (enum_norm_wins Black)))) as Hs.
      { rewrite in_map_iff.
        exists (normalize s); split; [reflexivity|].
        rewrite nodup_In.
        erewrite atomic_win_opp in s_play; [|exact s_res].
        apply enum_norm_wins_correct2; auto. now destruct pl.
      }
      pose proof (hash_adds_ne_pos (map (tag Black 0) (nodup IntHash_dec (enum_norm_wins Black)))
        (normalize s) (Black, 0) Hs); lia.
    + assert (In (normalize s, (White, 0)) (map (tag White 0) (nodup IntHash_dec (enum_norm_wins White)))) as Hs.
      { rewrite in_map_iff.
        exists (normalize s); split; [reflexivity|].
        rewrite nodup_In.
        erewrite atomic_win_opp in s_play; [|exact s_res].
        apply enum_norm_wins_correct2; now destruct pl.
      }
      pose proof (hash_adds_ne_pos (map (tag White 0) (nodup IntHash_dec (enum_norm_wins White)))
        (normalize s) (White, 0) Hs); lia.
  - intros s pl s_p s_res.
    apply mate_TB_final_lookup; auto.
    exists (atom_win s_res).
    split; auto.
    intro; simpl; lia.
Qed.

(* todo *)
Lemma TB_lookup_None_eloise : forall p s,
  P s ->
  to_play s = p ->
  tb_lookup TB_final s = None ->
  (atomic_res s = Some Draw) +
  (atomic_res s = None) * { m : Move s & tb_lookup TB_final (exec_move s m) = None }.
Proof.
  intros p s s_p s_play tb_s.
  destruct atomic_res eqn:s_res.
  - destruct r.
    + erewrite TB_final_respects_atomic_wins in tb_s; auto;
        [congruence|eauto].
    + left; reflexivity.
  - right; split; [reflexivity|].
    destruct (None_or_all_Some
      (fun m => tb_lookup TB_final (exec_move s m))
      (enum_moves s)) as [[m Hm]|[ps Hps]].
    + now exists m.
    + exfalso.
      destruct (forallb
        (fun p => player_eqb (fst p) (opp (to_play s))) ps) eqn:Hps2.
      * apply (no_final_curr_mate (opp (to_play s)) s); auto.
        rewrite forallb_forall in Hps2.
        assert (forall m : Move s,
          {w : win (opp (to_play s)) (exec_move s m) & depth w < curr TB_final}).
        { intro m.
          pose proof (in_map
            (fun m' => tb_lookup TB_final (exec_move s m'))
            (enum_moves s) m (enum_all m)) as pf.
          rewrite Hps in pf.
          destruct (in_map_sig pf) as [[pl' k] [tb_sm HIn]].
          pose proof (player_eqb_true _ _ (Hps2 _ HIn)); simpl in *; subst.
          symmetry in tb_sm.
          destruct (TB_final_lookup_mate _ _ _ tb_sm) as [w [w_d _]].
          exists w.
          rewrite w_d.
          eapply (tb_small _ TB_final_valid); eauto.
        }
        rewrite s_play in X.
        rewrite <- opp_invol in s_play.
        pose (w' := abelard_win s_res s_play (fun m => projT1 (X m))).
        assert (depth w' <= curr TB_final).
        { simpl.
          apply list_max_lt.
          -- intro pf.
             pose (map_eq_nil _ _ pf) as pf'.
             destruct (nil_atomic_res pf'); congruence.
          -- rewrite Forall_forall.
             intros x HIn.
             rewrite in_map_iff in HIn.
             destruct HIn as [m [Hm _]].
             destruct (X m); simpl in Hm.
             congruence.
        }
        rewrite s_play.
        rewrite opp_invol.
        exists w'; split.
        -- apply PeanoNat.Nat.le_antisymm; auto.
           exact (tb_None _ TB_final_valid w' s_p tb_s).
        -- intro w''.
           pose (tb_None _ TB_final_valid w'' s_p tb_s).
           lia.
      * destruct (forallb_false _ _ Hps2)
          as [[pl n] [HIn Heq]].
        simpl in Heq.
        pose proof (player_eqb_false _ _ Heq).
        rewrite opp_invol in *; subst.
        pose proof (in_map Some _ _ HIn) as pf.
        rewrite <- Hps in pf.
        rewrite in_map_iff in pf.
        destruct pf as [m [tb_sm _]].
        destruct (TB_final_lookup_mate _ _ _ tb_sm) as [w [w_d _]].
        apply (no_final_curr_mate (to_play s) s); auto.
        pose (w' := eloise_win s_res eq_refl m w).
        pose proof (tb_None _ TB_final_valid w' s_p tb_s) as pf.
        simpl in pf.
        epose proof (tb_small _ TB_final_valid tb_sm).
        assert (curr TB_final = S n) as pf' by lia.
        rewrite pf'.
        exists w'; split; simpl; [lia|].
        intro w''.
        pose proof (tb_None _ TB_final_valid w'' s_p tb_s).
        simpl; lia.
Defined.

Lemma TB_lookup_None_abelard : forall p s,
  P s ->
  to_play s = opp p ->
  tb_lookup TB_final s = None ->
  (atomic_res s = Some Draw) +
  (atomic_res s = None) * (forall m,
    (tb_lookup TB_final (exec_move s m) = None) +
    { n : nat & tb_lookup TB_final (exec_move s m) = Some (p, n) }).
Proof.
  intros p s s_p s_play tb_s.
  destruct atomic_res as [[|]|] eqn:s_res.
  - erewrite TB_final_respects_atomic_wins in tb_s; auto.
    + congruence.
    + exact s_res.
  - now left.
  - right; split; auto.
    intro m.
    destruct (tb_lookup TB_final (exec_move s m)) as [[pl n]|] eqn:Hm.
    + right; exists n.
      repeat f_equal.
      destruct (player_id_or_opp pl p) as [|pf]; auto.
      exfalso.
      apply (no_final_curr_mate (to_play s) s); auto.
      pose proof (TB_final_lookup_mate _ pl n Hm) as mt.
      destruct mt as [w [w_depth w_min]].
      rewrite <- pf in s_play.
      rewrite opp_invol in s_play.
      rewrite s_play.
      pose (w' := eloise_win s_res s_play m w).
      pose proof (tb_None _ TB_final_valid w' s_p tb_s) as pf'.
      simpl in pf'.
      epose proof (tb_small _ TB_final_valid Hm).
      assert (curr TB_final = S n) as pf'' by lia.
      rewrite pf''.
      exists w'; split; simpl; [lia|].
      intro w''.
      pose proof (tb_None _ TB_final_valid w'' s_p tb_s).
      simpl; lia.
    + now left.
Defined.

CoFixpoint TB_final_lookup_no_worse p : forall s,
  P s ->
  tb_lookup TB_final s = None ->
  no_worse p s.
Proof.
  intros s s_p tb_s.
  destruct (player_id_or_opp_r_t (to_play s) p) as [s_play|s_play].
  - destruct (TB_lookup_None_eloise p s s_p s_play tb_s) as [s_res|[s_res [m Hm]]].
    + apply atom_draw_no_worse; exact s_res.
    + apply (eloise_no_worse p s s_play s_res m).
      apply TB_final_lookup_no_worse.
      * now apply closed.
      * exact Hm.
  - destruct (TB_lookup_None_abelard p s s_p s_play tb_s) as [s_res|[s_res pf]].
    + apply atom_draw_no_worse; exact s_res.
    + apply (abelard_no_worse p s s_play s_res).
      intro m.
      destruct (pf m) as [Hm|[n Hmn]].
      * apply TB_final_lookup_no_worse.
        -- now apply closed.
        -- exact Hm.
      * apply win_no_worse.
        apply TB_final_lookup_mate in Hmn.
        exact (projT1 Hmn).
Defined.

Theorem TB_final_lookup_draw : forall s,
  P s ->
  tb_lookup TB_final s = None ->
  draw s.
Proof.
  intros.
  apply both_no_worse_draw with (p := to_play s);
  apply TB_final_lookup_no_worse; auto.
Defined.

Theorem draw_TB_final_lookup : forall s,
  draw s ->
  tb_lookup TB_final s = None.
Proof.
  intros s d.
  destruct (tb_lookup TB_final s) eqn:tb_s; [|reflexivity].
  destruct p as [pl n].
  destruct (TB_final_lookup_mate _ _ _ tb_s).
  elim (win_not_draw _ _ x d).
Qed.

End TB.
