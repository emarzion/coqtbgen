Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Compare_dec.

Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Draw.
Require Import Games.Game.Win.

(*Require Import Games.Util.TBLoop.*)
Require Import Games.Util.StringMap.
Require Import Games.Util.Show.
Require Import Games.Util.Dec.
Require Import Games.Util.NewLoop.

Global Instance Show_disc {X} `{Show X} : Discrete X.
Proof.
  constructor.
  apply Show_dec.
Defined.

Global Instance List_disc {X} `{Discrete X} : Discrete (list X).
Proof.
  constructor.
  unfold decision.
  decide equality.
  apply eq_dec.
Defined.

Class FinGame (G : Game) : Type := {
  enum_states : list (GameState G);
  enum_wins : Player -> list (GameState G);

  enum_states_correct : forall s, In s enum_states;
  enum_wins_correct1 : forall s pl,
    In s (enum_wins pl) -> atomic_res s = Some (Win pl);
  enum_wins_correct2 : forall s pl,
    atomic_res s = Some (Win pl) -> In s (enum_wins pl)
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

Section TB.

Context {G : Game}.
Context `{FinGame G}.
Context `{NiceGame G}.
Context `{Reversible G}.
Context `{Show (GameState G)}.
Context `{forall s : GameState G, Discrete (Move s)}.

Context {M : Type -> Type}.
Context `{StringMap M}.

Inductive Step :=
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
  | White => str_lookup s (white_positions tb)
  | Black => str_lookup s (black_positions tb)
  end.

Definition tag (winner : Player) (n : nat) (s : GameState G) :=
  (s, (winner, n)).

Definition add_positions (m : M (Player * nat)) (winner : Player) (n : nat)
  (ps : list (GameState G)) : M (Player * nat) :=
  str_adds (map (tag winner n) ps) m.

Fixpoint filter_Nones {X Y} (f : X -> option Y) (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' =>
    match f x with
    | None => x :: filter_Nones f xs'
    | Some _ => filter_Nones f xs'
    end
  end.

Lemma In_filter_Nones_correct1 {X Y} (f : X -> option Y) (xs : list X) :
  forall x, In x (filter_Nones f xs) -> f x = None /\ In x xs.
Proof.
  induction xs as [|x' xs'].
  - intros x [].
  - intros x HIn; simpl in *.
    destruct (f x') eqn:fx'.
    + destruct (IHxs' _ HIn).
      split; auto.
    + destruct HIn as [Heq|HIn].
      * split; [congruence|tauto].
      * destruct (IHxs' _ HIn).
        split; auto.
Qed.

Lemma In_filter_Nones_correct2 {X Y} (f : X -> option Y) (xs : list X) :
  forall x, f x = None /\ In x xs -> In x (filter_Nones f xs).
Proof.
  induction xs as [|x' xs'].
  - intros x [_ []].
  - intros x [fx [Heq|HIn]]; simpl.
    + rewrite Heq, fx.
      left; reflexivity.
    + destruct (f x').
      * apply IHxs'; auto.
      * right; apply IHxs'; auto.
Qed.

Lemma In_filter_Nones_iff {X Y} (f : X -> option Y) (xs : list X) :
  forall x, In x (filter_Nones f xs) <-> f x = None /\ In x xs.
Proof.
  intro; split.
  - apply In_filter_Nones_correct1.
  - apply In_filter_Nones_correct2.
Qed.

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
  let candidates := concat (map enum_preds prev) in
  let candidates' :=
    filter_Nones (fun s => str_lookup s m) candidates in
  nodup Show_dec candidates'.

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
  let candidates := concat (map enum_preds prev) in
  let candidates' :=
    filter_Nones (fun s => str_lookup s m) candidates in
  let candidates'' := filter
    (fun s => forallb (fun m =>
      match str_lookup (exec_move s m) m' with
      | Some (pl',_) => player_eqb (opp pl) pl'
      | None => false
      end) (enum_moves s)) candidates' in
  nodup Show_dec candidates''.

Definition TB_init : TB := {|
  curr := 0;
  last_step := Abelard;

  white_positions := empty;
  black_positions := empty;

  last_white_positions := nodup Show_dec (enum_wins Black);
  last_black_positions := nodup Show_dec (enum_wins White);
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
  pose proof (str_size_adds_le
    (map (tag (step_player last_step0 White) curr0) last_white_positions0)
    white_positions0).
  pose proof (str_size_adds_le
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

Definition satMate pl (s : GameState G) (n : nat) : Type :=
  { w : win pl s & depth w = n /\ minimal w }.

Record TB_valid (tb : TB) : Type := {

  satMate_tb : forall {s pl n},
    n < curr tb -> satMate pl s n ->
    tb_lookup tb s = Some (pl, n);

  tb_satMate : forall {s pl n},
    tb_lookup tb s = Some (pl, n) ->
    satMate pl s n;

  tb_small : forall {s pl n},
    tb_lookup tb s = Some (pl, n) ->
    n < curr tb;

  tb_white : forall {s pl n},
    str_lookup s (white_positions tb) = Some (pl, n) ->
    to_play s = White;

  tb_black : forall {s pl n},
    str_lookup s (black_positions tb) = Some (pl, n) ->
    to_play s = Black;

  tb_None : forall {s pl} (w : win pl s),
    tb_lookup tb s = None ->
    curr tb <= depth w;

  satMate_lwp : forall {s pl},
    to_play s = White ->
    satMate pl s (curr tb) ->
    In s (last_white_positions tb);

  lwp_satMate : forall {s},
    In s (last_white_positions tb) ->
    satMate (step_player (last_step tb) White) s (curr tb);

  satMate_lbp : forall {s pl},
    to_play s = Black ->
    satMate pl s (curr tb) ->
    In s (last_black_positions tb);

  lbp_satMate : forall {s},
    In s (last_black_positions tb) ->
    satMate (step_player (last_step tb) Black) s (curr tb);

  lwp_NoDup : NoDup (last_white_positions tb);

  lbp_NoDup : NoDup (last_black_positions tb);

  lwp_disj : forall s, In s (last_white_positions tb) -> str_lookup s (white_positions tb) = None;

  lbp_disj : forall s, In s (last_black_positions tb) -> str_lookup s (black_positions tb) = None;

  lwp_white : forall s, In s (last_white_positions tb) -> to_play s = White;

  lbp_black : forall s, In s (last_black_positions tb) -> to_play s = Black;

  sizes_never_exceed :
    size (white_positions tb) +
    size (black_positions tb) +
    length (last_white_positions tb) +
    length (last_black_positions tb) <= length enum_states;

  }.

Lemma step_player_white (tb : TB) (v : TB_valid tb) : forall {s pl},
  to_play s = White ->
  satMate pl s (curr tb) ->
  pl = step_player (last_step tb) White.
Proof.
  intros s pl s_play sm.
  pose proof (satMate_lwp _ v s_play sm) as HIn.
  pose (lwp_satMate _ v HIn) as sm'.
  destruct sm as [w _].
  destruct sm' as [w' _].
  exact (unique_winner _ _ _ w w').
Qed.

Lemma step_player_black (tb : TB) (v : TB_valid tb) : forall {s pl},
  to_play s = Black ->
  satMate pl s (curr tb) ->
  pl = step_player (last_step tb) Black.
Proof.
  intros s pl s_play sm.
  pose proof (satMate_lbp _ v s_play sm) as HIn.
  pose (lbp_satMate _ v HIn) as sm'.
  destruct sm as [w _].
  destruct sm' as [w' _].
  exact (unique_winner _ _ _ w w').
Qed.

Definition disj {X} (xs ys : list X) : Prop :=
  forall x, In x xs -> ~ In x ys.

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
  - simpl.
    intros; lia.
  - intros s pl n Htb.
    unfold tb_lookup, TB_init in Htb; simpl in Htb.
    destruct (to_play s);
    now rewrite str_lookup_empty in Htb.
  - intros s pl n Htb.
    unfold tb_lookup, TB_init in Htb; simpl in Htb.
    destruct (to_play s);
    now rewrite str_lookup_empty in Htb.
  - intros s pl n Htb; simpl in Htb.
    now rewrite str_lookup_empty in Htb.
  - intros s pl n Htb; simpl in Htb.
    now rewrite str_lookup_empty in Htb.
  - intros; simpl; lia.
  - intros s pl s_play [w [w_d _]].
    destruct w; simpl in *; try lia.
    rewrite (atomic_win_opp _ _ e) in s_play.
    assert (pl = Black) as s_pl by (now apply opp_inj).
    rewrite nodup_In.
    apply enum_wins_correct2; congruence.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    pose proof (enum_wins_correct1 _ _ HIn) as s_res.
    exists (atom_win s_res); split; auto.
    intro w'; simpl; lia.
  - intros s pl s_play [w [w_d _]].
    destruct w; simpl in *; try lia.
    rewrite (atomic_win_opp _ _ e) in s_play.
    assert (pl = White) as s_pl by (now apply opp_inj).
    rewrite nodup_In.
    apply enum_wins_correct2; congruence.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    pose proof (enum_wins_correct1 _ _ HIn) as s_res.
    exists (atom_win s_res); split; auto.
    intro w'; simpl; lia.
  - apply NoDup_nodup.
  - apply NoDup_nodup.
  - intros.
    now apply str_lookup_empty.
  - intros.
    now apply str_lookup_empty.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    pose proof (enum_wins_correct1 _ _ HIn) as s_res.
    now rewrite (atomic_win_opp _ _ s_res).
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    pose proof (enum_wins_correct1 _ _ HIn) as s_res.
    now rewrite (atomic_win_opp _ _ s_res).
  - simpl; rewrite size_empty; simpl.
    rewrite <- app_length.
    apply NoDup_incl_length.
    + apply NoDup_app.
      * apply NoDup_nodup.
      * apply NoDup_nodup.
      * intros s s_b s_w.
        rewrite nodup_In in s_b, s_w.
        pose proof (enum_wins_correct1 _ _ s_b);
        pose proof (enum_wins_correct1 _ _ s_w);
        congruence.
    + intros s _.
      apply enum_states_correct.
Defined.

Lemma map_tag_functional : forall pl n ps,
  AL.functional (map (tag pl n) ps).
Proof.
  intros pl n ps.
  intros s [q1 k] [q2 l] Hq1 Hq2.
  rewrite in_map_iff in Hq1, Hq2.
  destruct Hq1 as [t [Ht _]].
  destruct Hq2 as [u [Hu _]].
  unfold tag in Ht, Hu.
  congruence.
Qed.

Lemma in_map_sig {X Y} `{Discrete Y} {f : X -> Y} {xs} {y}
  : In y (map f xs) -> {x : X & f x = y /\ In x xs}.
Proof.
  induction xs as [|x xs'].
  - intros [].
  - intro HIn.
    destruct (eq_dec (f x) y).
    + exists x; split; auto.
      now left.
    + destruct IHxs' as [x' [Hx'1 Hx'2]].
      * destruct HIn; [contradiction|auto].
      * exists x'; split; auto.
        now right.
Defined.

Lemma not_Some_None {X} (o : option X) :
  (forall x, ~ o = Some x) -> o = None.
Proof.
  intro nSome.
  destruct o; [|reflexivity].
  elim (nSome x); reflexivity.
Qed.

Lemma None_or_all_Some {X Y} (f : X -> option Y) (xs : list X) :
  { x : X & f x = None } +
  { ys : list Y & map f xs = map Some ys }.
Proof.
  induction xs as [|x xs'].
  - right.
    exists [].
    reflexivity.
  - destruct (f x) eqn:fx.
    + destruct IHxs' as [[x' Hx']| [ys Hys]].
      * left; now exists x'.
      * right; exists (y :: ys); simpl; congruence.
    + left; now exists x.
Defined.

Lemma list_max_is_max : forall xs x, In x xs -> x <= list_max xs.
Proof.
  intro xs.
  rewrite <- Forall_forall.
  rewrite <- list_max_le.
  lia.
Qed.

Lemma not_None_in_Somes {X} (xs : list X) :
  ~ In None (map Some xs).
Proof.
  induction xs.
  - intros [].
  - intros [|]; auto.
    congruence.
Qed.

Lemma satMate_S_lemma (tb : TB) (v : TB_valid tb) : forall {s pl},
  satMate pl s (S (curr tb)) ->
  { m : Move s & satMate pl (exec_move s m) (curr tb) }.
Proof.
  intros s pl [w [w_d w_m]].
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
        * exact (tb_None _ v (w m) tb_sm).
      }
      clear w_d.
      exists m, (w m).
      split; [simpl; congruence|].
      intro w'.
      rewrite wm_d.
      exact (tb_None _ v w' tb_sm).
    + exfalso.
      assert (forall m, {k : nat & k < curr tb /\ tb_lookup tb (exec_move b m) = Some (pl, k)}).
      { intro m.
        destruct (tb_lookup tb (exec_move b m)) as [[pl' k]|] eqn:tb_sm.
        + exists k; split.
          exact (tb_small _ v tb_sm).
          do 2 f_equal.
          apply (unique_winner _ _ (exec_move b m)).
          * now destruct (tb_satMate _ v tb_sm).
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
        destruct (tb_satMate _ v tb_sm) as [w' ?].
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


Lemma satMate_eq {s} {pl pl'} {n n'} :
  satMate pl s n ->
  satMate pl' s n' ->
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
Admitted.

Lemma TB_step_valid : forall tb, TB_valid tb
  -> TB_valid (TB_step tb).
Proof.
  intros tb v.
  constructor.
  (* satMate_tb *)
  - simpl; intros s pl n n_small sm.
    destruct (le_lt_eq_dec _ _ n_small) as [pf|pf].
    + pose proof (Arith_prebase.lt_S_n _ _ pf) as pf'.
      pose proof (satMate_tb _ v pf' sm) as Htb.
      unfold tb_lookup in *.
      destruct (to_play s) eqn:s_play.
      * simpl.
        unfold add_positions.
        rewrite str_lookup_adds_nIn; auto.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        intro HIn.
        rewrite lwp_disj in Htb; congruence.
      * simpl.
        unfold add_positions.
        rewrite str_lookup_adds_nIn; auto.
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
        erewrite str_lookup_adds;
        [reflexivity| apply map_tag_functional|].
        rewrite in_map_iff.
        exists s.
        rewrite pf' in sm.
        pose proof (step_player_white _ v s_play sm) as Hpl.
        pose (satMate_lwp _ v s_play sm) as Hpl'.
        split; auto.
        now rewrite Hpl.
      * simpl.
        unfold add_positions.
        erewrite str_lookup_adds;
        [reflexivity| apply map_tag_functional|].
        rewrite in_map_iff.
        exists s.
        rewrite pf' in sm.
        pose proof (step_player_black _ v s_play sm) as Hpl.
        pose (satMate_lbp _ v s_play sm) as Hpl'.
        split; auto.
        now rewrite Hpl.
  (* tb_satMate *)
  - unfold tb_lookup.
    intros s pl n Htb.
    destruct (to_play s) eqn:s_play.
    + simpl in Htb.
      unfold add_positions in Htb.
      destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * destruct (in_map_sig pf) as [s' [Hs'1 Hs'2]].
        unfold tag in Hs'1.
        epose (lwp_satMate _ v Hs'2).
        inversion Hs'1.
        subst; auto.
      * apply (tb_satMate _ v).
        unfold tb_lookup.
        now rewrite s_play.
    + simpl in Htb.
      unfold add_positions in Htb.
      destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * destruct (in_map_sig pf) as [s' [Hs'1 Hs'2]].
        unfold tag in Hs'1.
        epose (lbp_satMate _ v Hs'2).
        inversion Hs'1.
        subst; auto.
      * apply (tb_satMate _ v).
        unfold tb_lookup.
        now rewrite s_play.
  (* tb_small *)
  - intros s pl n Htb.
    unfold tb_lookup in Htb.
    destruct (to_play s) eqn:s_play; simpl in *.
    + destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * rewrite in_map_iff in pf.
        destruct pf as [s' [Hs'1 Hs'2]].
        inversion Hs'1; lia.
      * cut (n < curr tb); [lia|].
        eapply (tb_small _ v).
        unfold tb_lookup; rewrite s_play; eauto.
    + destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
      * rewrite in_map_iff in pf.
        destruct pf as [s' [Hs'1 Hs'2]].
        inversion Hs'1; lia.
      * cut (n < curr tb); [lia|].
        eapply (tb_small _ v).
        unfold tb_lookup; rewrite s_play; eauto.
  (* tb_white *)
  - intros s pl n Htb.
    simpl in Htb.
    destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
    + rewrite in_map_iff in pf.
      destruct pf as [s' [Hs'1 Hs'2]].
      inversion Hs'1; subst.
      now apply (lwp_white _ v).
    + eapply (tb_white _ v); exact pf.
  (* tb_black *)
  - intros s pl n Htb.
    simpl in Htb.
    destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
    + rewrite in_map_iff in pf.
      destruct pf as [s' [Hs'1 Hs'2]].
      inversion Hs'1; subst.
      now apply (lbp_black _ v).
    + eapply (tb_black _ v); exact pf.
  (* tb_None *)
  - intros s pl w tb_s.
    unfold tb_lookup in tb_s.
    simpl in *.
    destruct (to_play s) eqn:s_play.
    + destruct (str_lookup_adds_None_invert tb_s) as [s_lwp tb'_s].
      epose proof (tb_None _ v w) as Hs.
      unfold tb_lookup in Hs.
      rewrite s_play in Hs.
      specialize (Hs tb'_s).
      destruct (PeanoNat.Nat.eq_dec (depth w) (curr tb)); [|lia].
      cut (satMate pl s (curr tb)).
      { intro sm.
        elim s_lwp.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        apply (satMate_lwp _ v s_play sm).
      }
      exists w; split; auto.
      intro w'.
      rewrite e.
      apply (tb_None _ v w').
      unfold tb_lookup; now rewrite s_play.
    + destruct (str_lookup_adds_None_invert tb_s) as [s_lbp tb'_s].
      epose proof (tb_None _ v w) as Hs.
      unfold tb_lookup in Hs.
      rewrite s_play in Hs.
      specialize (Hs tb'_s).
      destruct (PeanoNat.Nat.eq_dec (depth w) (curr tb)); [|lia].
      cut (satMate pl s (curr tb)).
      { intro sm.
        elim s_lbp.
        rewrite map_map.
        unfold tag; simpl.
        rewrite map_id.
        apply (satMate_lbp _ v s_play sm).
      }
      exists w; split; auto.
      intro w'.
      rewrite e.
      apply (tb_None _ v w').
      unfold tb_lookup; now rewrite s_play.
  (* satMate_lwp *)
  - intros s pl s_play sm; simpl in *.
    destruct (last_step tb) eqn:tb_step.
    + unfold abelard_step.
      rewrite nodup_In.
      rewrite filter_In; split.
      * rewrite In_filter_Nones_iff; split.
        -- rewrite tb_step; simpl.
           apply not_Some_None.
           intros [pl' n] tb_s.
           destruct (str_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1; subst.
              pose (lwp_satMate _ v Hs'2).
              pose (satMate_eq sm s0); lia.
           ++ epose (tb_small _ v).
              unfold tb_lookup in l.
              rewrite s_play in l.
              specialize (l pf).
              epose (tb_satMate _ v).
              unfold tb_lookup in s0.
              rewrite s_play in s0.
              specialize (s0 pf).
              pose (satMate_eq sm s0); lia.
        -- rewrite in_concat.
           destruct (satMate_S_lemma _ v sm) as [m smm].
           exists (enum_preds (exec_move s m)).
           split.
           ++ apply in_map.
              eapply (satMate_lbp _ v).
              rewrite to_play_exec_move, s_play; reflexivity.
              exact smm.
           ++ apply enum_preds_correct2.
      * rewrite forallb_forall.
        intros m _.
        destruct (satMate_S_lemma _ v sm) as [m' smm'].
        assert (to_play (exec_move s m') = Black) as sm'_play
          by now rewrite to_play_exec_move, s_play.
        pose proof (step_player_black _ v sm'_play smm') as Hpl.
        rewrite tb_step in Hpl; simpl in Hpl.
        destruct str_lookup as [[pl' n']|] eqn:tb_sm.
        -- destruct (str_lookup_adds_invert _ _ _ _ tb_sm) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1.
              now rewrite tb_step.
           ++ destruct pl'; [|reflexivity].
              absurd (Black = White); [discriminate|].
              apply (unique_winner _ _ s).
              ** rewrite Hpl in sm.
                 now destruct sm.
              ** eapply eloise_win; auto.
                 { destruct (atomic_res s) eqn:s_res; auto.
                   pose proof (enum_all m) as HIn.
                   rewrite (atomic_res_nil s_res) in HIn; destruct HIn.
                 }
                 epose (@tb_satMate _ v (exec_move s m)).
                 unfold tb_lookup in s0.
                 rewrite to_play_exec_move in s0.
                 rewrite s_play in s0; simpl in s0.
                 destruct (s0 _ _ pf); eauto.
        -- subst.
           rewrite tb_step in tb_sm; simpl in *.
           destruct (str_lookup_adds_None_invert tb_sm).
           destruct sm as [w [w_d wm]].
           destruct w; [simpl in w_d; lia|congruence|].
           pose (tb_None _ v (w m)).
           unfold tb_lookup in l.
           rewrite to_play_exec_move in l.
           rewrite s_play in l; simpl in l.
           specialize (l H6).
           simpl in w_d.
           inversion w_d as [w_d']; clear w_d.
           assert (depth (w m) <= curr tb).
           { rewrite <- w_d'.
             apply list_max_is_max.
             rewrite in_map_iff.
             exists m; split; auto.
             apply enum_all.
           }
           assert (satMate Black (exec_move b m) (curr tb)).
           { exists (w m).
             split; [lia|].
             intro w'.
             assert (depth (w m) = curr tb) by lia.
             rewrite H8.
             apply (tb_None _ v w').
             unfold tb_lookup.
             rewrite to_play_exec_move, s_play; simpl; auto.
           }
           elim H5.
           rewrite in_map_iff.
           exists (exec_move b m, (Black, curr tb)).
           simpl; split; [reflexivity|].
           rewrite in_map_iff.
           exists (exec_move b m); split; [reflexivity|].
           eapply (satMate_lbp _ v).
           rewrite to_play_exec_move, s_play; reflexivity.
           exact X.
    + unfold eloise_step.
      rewrite nodup_In.
      rewrite In_filter_Nones_iff; split.
      * apply not_Some_None.
        intros [pl' n] tb_s.
        destruct (str_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
        -- rewrite in_map_iff in pf.
           destruct pf as [s' [Hs'1 Hs'2]].
           inversion Hs'1; subst.
           pose (lwp_satMate _ v Hs'2).
           pose (satMate_eq sm s0); lia.
        -- epose (tb_small _ v).
           unfold tb_lookup in l.
           rewrite s_play in l.
           specialize (l pf).
           epose (tb_satMate _ v).
           unfold tb_lookup in s0.
           rewrite s_play in s0.
           specialize (s0 pf).
           pose (satMate_eq sm s0); lia.
      * rewrite in_concat.
        destruct (satMate_S_lemma _ v sm) as [m smm].
        exists (enum_preds (exec_move s m)).
        split.
        -- apply in_map.
           eapply (satMate_lbp _ v).
           rewrite to_play_exec_move, s_play; reflexivity.
           exact smm.
        -- apply enum_preds_correct2.
  (* lwp_satMate *)
  - intros s HIn; simpl in *.
    destruct (last_step tb) eqn:tb_step; simpl.
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' Hforall].
      rewrite In_filter_Nones_iff in HIn'.
      destruct HIn' as [Hs1 Hs2].
      destruct (in_concat_sig _ _ Hs2) as [xs [Hxs1 Hxs2]].
      destruct (in_map_sig Hxs1) as [s' [Hs'1 Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hxs2) as [m Hm]; subst.
      pose (lbp_satMate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play s = White) as s_play.
      { apply opp_inj.
        rewrite <- (to_play_exec_move m).
        apply (lbp_black _ v); auto.
      }
      destruct sm as [w [w_d w_m]].
      destruct (atomic_res s) eqn:s_res.
      { exfalso.
        pose proof (enum_all m) as pf.
        rewrite (atomic_res_nil s_res) in pf.
        exact pf.
      }
      rewrite forallb_forall in Hforall.
      rewrite tb_step in *.
      simpl in *.
      assert (forall m, {w : win Black (exec_move s m) & depth w <= curr tb /\ minimal w}).
      { intro m'.
        specialize (Hforall m' (enum_all m')).
        destruct (str_lookup (exec_move s m')
          (add_positions (black_positions tb) Black (curr tb)
          (last_black_positions tb))) as [[[|] n]|] eqn:Hsm; try congruence.
        clear Hforall.
        destruct (str_lookup_adds_invert _ _ _ _ Hsm) as [HIn|tb_sm].
        + destruct (in_map_sig HIn) as [s' [G1 G2]]; inversion G1; subst.
          pose (lbp_satMate _ v G2) as sm.
          rewrite tb_step in sm; simpl in sm.
          destruct sm as [w' [w'_d w'_m]].
          exists w'; split; [lia|auto].
        + pose (@tb_satMate _ v (exec_move s m') Black n) as sm.
          unfold tb_lookup in sm.
          rewrite to_play_exec_move in sm.
          rewrite s_play in sm; simpl in sm.
          destruct (sm tb_sm) as [w' [w'_d w'_m]].
          exists w'; split; auto.
          pose (@tb_small _ v (exec_move s m') Black n).
          unfold tb_lookup in l.
          rewrite to_play_exec_move in l.
          rewrite s_play in l; specialize (l tb_sm); lia.
      }
      pose (w' := @abelard_win _ Black _ s_res s_play (fun m => projT1 (X m))).
      exists w'; simpl; split.
      * f_equal.
        apply PeanoNat.Nat.le_antisymm.
        -- rewrite list_max_le.
           rewrite Forall_forall.
           intros.
           rewrite in_map_iff in H5.
           destruct H5 as [m' [Hm' _]].
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
      rewrite In_filter_Nones_iff in HIn.
      destruct HIn as [Hs1 Hs2].
      destruct (in_concat_sig _ _ Hs2) as [xs [Hxs1 Hxs2]].
      destruct (in_map_sig Hxs1) as [s' [Hs'1 Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hxs2) as [m Hm]; subst.
      pose (lbp_satMate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play s = White) as s_play.
      { apply opp_inj.
        rewrite <- (to_play_exec_move m).
        apply (lbp_black _ v); auto.
      }
      destruct sm as [w [w_d w_m]].
      destruct (atomic_res s) eqn:s_res.
      { exfalso.
        pose proof (enum_all m) as pf.
        rewrite (atomic_res_nil s_res) in pf.
        exact pf.
      }
      (* can this be cleaned up? *)
      exists (eloise_win s_res s_play m w).
      split; [simpl; congruence|].
      intro w'; simpl.
      destruct w'; simpl in *; try congruence.
      apply le_n_S.
      rewrite w_d.
      destruct (str_lookup_adds_None_invert Hs1) as [tb_b lwp_b].
      pose (w'' := eloise_win s_res s_play m0 w').
      epose proof (tb_None _ v w'') as Hw'.
      unfold tb_lookup in Hw'.
      rewrite s_play in Hw'.
      specialize (Hw' lwp_b).
      simpl in Hw'.
      rewrite map_map in tb_b; simpl in tb_b.
      rewrite map_id in tb_b.
      rewrite PeanoNat.Nat.le_ngt.
      intro pf.
      assert (S (depth w') = (curr tb)) by lia.
      apply tb_b.
      eapply (satMate_lwp _ v s_play).
      exists w''; split; auto.
      intro. simpl. rewrite H5.
      eapply (tb_None _ v).
      unfold tb_lookup.
      now rewrite s_play.
  (* satMate_lbp *)
  - intros s pl s_play sm; simpl in *.
    destruct (last_step tb) eqn:tb_step.
    + unfold abelard_step.
      rewrite nodup_In.
      rewrite filter_In; split.
      * rewrite In_filter_Nones_iff; split.
        -- rewrite tb_step; simpl.
           apply not_Some_None.
           intros [pl' n] tb_s.
           destruct (str_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1; subst.
              pose (lbp_satMate _ v Hs'2).
              pose (satMate_eq sm s0); lia.
           ++ epose (tb_small _ v).
              unfold tb_lookup in l.
              rewrite s_play in l.
              specialize (l pf).
              epose (tb_satMate _ v).
              unfold tb_lookup in s0.
              rewrite s_play in s0.
              specialize (s0 pf).
              pose (satMate_eq sm s0); lia.
        -- rewrite in_concat.
           destruct (satMate_S_lemma _ v sm) as [m smm].
           exists (enum_preds (exec_move s m)).
           split.
           ++ apply in_map.
              eapply (satMate_lwp _ v).
              rewrite to_play_exec_move, s_play; reflexivity.
              exact smm.
           ++ apply enum_preds_correct2.
      * rewrite forallb_forall.
        intros m _.
        destruct (satMate_S_lemma _ v sm) as [m' smm'].
        assert (to_play (exec_move s m') = White) as sm'_play
          by now rewrite to_play_exec_move, s_play.
        pose proof (step_player_white _ v sm'_play smm') as Hpl.
        rewrite tb_step in Hpl; simpl in Hpl.
        destruct str_lookup as [[pl' n']|] eqn:tb_sm.
        -- destruct (str_lookup_adds_invert _ _ _ _ tb_sm) as [pf|pf].
           ++ rewrite in_map_iff in pf.
              destruct pf as [s' [Hs'1 Hs'2]].
              inversion Hs'1.
              now rewrite tb_step.
           ++ destruct pl'; [reflexivity|].
              absurd (White = Black); [discriminate|].
              apply (unique_winner _ _ s).
              ** rewrite Hpl in sm.
                 now destruct sm.
              ** eapply eloise_win; auto.
                 { destruct (atomic_res s) eqn:s_res; auto.
                   pose proof (enum_all m) as HIn.
                   rewrite (atomic_res_nil s_res) in HIn; destruct HIn.
                 }
                 epose (@tb_satMate _ v (exec_move s m)).
                 unfold tb_lookup in s0.
                 rewrite to_play_exec_move in s0.
                 rewrite s_play in s0; simpl in s0.
                 destruct (s0 _ _ pf); eauto.
        -- subst.
           rewrite tb_step in tb_sm; simpl in *.
           destruct (str_lookup_adds_None_invert tb_sm).
           destruct sm as [w [w_d wm]].
           destruct w; [simpl in w_d; lia|congruence|].
           pose (tb_None _ v (w m)).
           unfold tb_lookup in l.
           rewrite to_play_exec_move in l.
           rewrite s_play in l; simpl in l.
           specialize (l H6).
           simpl in w_d.
           inversion w_d as [w_d']; clear w_d.
           assert (depth (w m) <= curr tb).
           { rewrite <- w_d'.
             apply list_max_is_max.
             rewrite in_map_iff.
             exists m; split; auto.
             apply enum_all.
           }
           assert (satMate White (exec_move b m) (curr tb)).
           { exists (w m).
             split; [lia|].
             intro w'.
             assert (depth (w m) = curr tb) by lia.
             rewrite H8.
             apply (tb_None _ v w').
             unfold tb_lookup.
             rewrite to_play_exec_move, s_play; simpl; auto.
           }
           elim H5.
           rewrite in_map_iff.
           exists (exec_move b m, (White, curr tb)).
           simpl; split; [reflexivity|].
           rewrite in_map_iff.
           exists (exec_move b m); split; [reflexivity|].
           eapply (satMate_lwp _ v).
           rewrite to_play_exec_move, s_play; reflexivity.
           exact X.
    + unfold eloise_step.
      rewrite nodup_In.
      rewrite In_filter_Nones_iff; split.
      * apply not_Some_None.
        intros [pl' n] tb_s.
        destruct (str_lookup_adds_invert _ _ _ _ tb_s) as [pf|pf].
        -- rewrite in_map_iff in pf.
           destruct pf as [s' [Hs'1 Hs'2]].
           inversion Hs'1; subst.
           pose (lbp_satMate _ v Hs'2).
           pose (satMate_eq sm s0); lia.
        -- epose (tb_small _ v).
           unfold tb_lookup in l.
           rewrite s_play in l.
           specialize (l pf).
           epose (tb_satMate _ v).
           unfold tb_lookup in s0.
           rewrite s_play in s0.
           specialize (s0 pf).
           pose (satMate_eq sm s0); lia.
      * rewrite in_concat.
        destruct (satMate_S_lemma _ v sm) as [m smm].
        exists (enum_preds (exec_move s m)).
        split.
        -- apply in_map.
           eapply (satMate_lwp _ v).
           rewrite to_play_exec_move, s_play; reflexivity.
           exact smm.
        -- apply enum_preds_correct2.
  (* lbp_satMate *)
  - admit.
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
      rewrite In_filter_Nones_iff in HIn'.
      rewrite tb_step in HIn'.
      tauto.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
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
      rewrite In_filter_Nones_iff in HIn'.
      rewrite tb_step in HIn'.
      tauto.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
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
      rewrite In_filter_Nones_iff in HIn'.
      destruct HIn' as [_ HIn].
      rewrite in_concat in HIn.
      destruct HIn as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lbp_black _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      now apply opp_inj.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      destruct HIn as [_ HIn'].
      rewrite in_concat in HIn'.
      destruct HIn' as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lbp_black _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      now apply opp_inj.
  (* lbp_black *)
  - simpl; intros s HIn.
    destruct (last_step tb).
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' _].
      rewrite In_filter_Nones_iff in HIn'.
      destruct HIn' as [_ HIn].
      rewrite in_concat in HIn.
      destruct HIn as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lwp_white _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      now apply opp_inj.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      destruct HIn as [_ HIn'].
      rewrite in_concat in HIn'.
      destruct HIn' as [l [Hl1 Hl2]].
      rewrite in_map_iff in Hl1.
      destruct Hl1 as [s' [Hs' Hs'2]]; subst.
      destruct (enum_preds_correct1 _ _ Hl2) as [m]; subst.
      pose proof (lwp_white _ v _ Hs'2) as sm_play.
      rewrite to_play_exec_move in sm_play.
      now apply opp_inj.
  (* sizes_never_exceed *)
  - simpl.
    unfold add_positions.
    repeat rewrite str_size_adds.
    + repeat rewrite map_length.
      pose proof (sizes_never_exceed _ v) as pf.
      pose (E := length enum_states).
      pose (W := length (last_white_positions tb)).
      pose (SW := size (white_positions tb)).
      pose (B := length (last_black_positions tb)).
      pose (SB := size (black_positions tb)).
      fold E W SW B SB in pf.
      fold E W SW B SB.
      destruct (last_step tb); simpl.
      * pose (NW := length (abelard_step tb White)).
        pose (NB := length (abelard_step tb Black)).
        fold NW NB.
        assert (NW + NB <= E - (SW + SB + W + B)) by admit.
        lia.
      * pose (NW := length (eloise_step tb White)).
        pose (NB := length (eloise_step tb Black)).
        fold NW NB.
        assert (NW + NB <= E - (SW + SB + W + B)) by admit.
        lia.
    + unfold tag.
      rewrite map_map; simpl.
      rewrite map_id.
      now apply lbp_NoDup.
    + unfold tag.
      rewrite map_map; simpl.
      rewrite map_id.
      now apply lbp_disj.
    + unfold tag.
      rewrite map_map; simpl.
      rewrite map_id.
      now apply lwp_NoDup.
    + unfold tag.
      rewrite map_map; simpl.
      rewrite map_id.
      now apply lwp_disj.
Admitted.

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

Lemma In_length_pos {X} (xs : list X) : forall x, In x xs ->
  length xs > 0.
Proof.
  destruct xs; intros y HIn.
  - destruct HIn.
  - simpl; lia.
Qed.

Lemma num_left_lt : forall tb (s : GameState G) pl,
  satMate pl s (curr tb) -> TB_valid tb ->
  num_left (step TB_loop_data tb) < num_left tb.
Proof.
  intros.
  unfold num_left.
  simpl.
  unfold add_positions.
  rewrite str_size_adds.
  - rewrite str_size_adds.
    + repeat rewrite map_length.
      pose (E := length enum_states).
      pose (W := length (last_white_positions tb)).
      pose (SW := size (white_positions tb)).
      pose (B := length (last_black_positions tb)).
      pose (SB := size (black_positions tb)).
      fold E W SW B SB.
      assert (SW + SB + W + B <= E).
      { apply sizes_never_exceed; auto. }
      destruct (to_play s) eqn:s_play.
      * assert (W > 0).
        { unfold W.
          apply (In_length_pos _ s).
          eapply satMate_lwp; eauto.
        }
        lia.
      * assert (B > 0).
        { unfold W.
          apply (In_length_pos _ s).
          eapply satMate_lbp; eauto.
        }
        lia.
    + rewrite map_map.
      unfold tag.
      simpl.
      rewrite map_id.
      apply lbp_NoDup; auto.
    + rewrite map_map.
      unfold tag.
      simpl.
      rewrite map_id.
      apply lbp_disj; auto.
  - rewrite map_map.
    unfold tag.
    simpl.
    rewrite map_id.
    apply lwp_NoDup; auto.
  - rewrite map_map.
    unfold tag.
    simpl.
    rewrite map_id.
    apply lwp_disj; auto.
Qed.

Lemma TB_final_lookup_satMate : forall s pl n,
  tb_lookup TB_final s = Some (pl, n) ->
  satMate pl s n.
Proof.
  intros s pl n Htb.
  exact (tb_satMate _ TB_final_valid Htb).
Defined.

Lemma satMate_TB_final_lookup : forall s pl n,
  satMate pl s n ->
  tb_lookup TB_final s = Some (pl, n).
Proof.
  intros s pl n sm.
  destruct (tb_lookup TB_final s) as [[pl' k]|] eqn:tb_s.
  - pose (tb_satMate _ TB_final_valid tb_s).
    do 2 f_equal.
    + destruct sm as [w _].
      destruct s0 as [w' _].
      exact (unique_winner _ _ _ w' w).
    + eapply satMate_eq; eauto.
  - destruct sm as [w [w_d w_m]].
    pose (tb_None _ TB_final_valid w tb_s).
Admitted.

Lemma map_fg_lemma {X Y Z} `{Discrete Y} {f : X -> Z} {g : Y -> Z} :
  forall {xs ys}, map f xs = map g ys -> 
  forall y, In y ys -> {x : X & In x xs /\ f x = g y}.
Proof.
  induction xs as [|x xs']; intros ys pf y Hy.
  - destruct ys; [destruct Hy|inversion pf].
  - destruct ys; [inversion pf|].
    destruct (eq_dec y0 y).
    + exists x; split.
      * now left.
      * inversion pf; congruence.
    + inversion pf.
      destruct (IHxs' _ H8 y).
      * destruct Hy; [contradiction|auto].
      * exists x0; split; [now right| tauto].
Defined.

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

Lemma forallb_true {X} (p : X -> bool) (xs : list X) :
  forallb p xs = true -> forall x, In x xs -> p x = true.
Proof.
  induction xs as [|x' xs']; intros Hpxs x Hx.
  - destruct Hx.
  - destruct Hx; subst; simpl in *.
    + destruct (p x); [reflexivity|discriminate].
    + destruct (p x'); [simpl in *|discriminate].
      now apply IHxs'.
Qed.

Definition respects_atomic_wins (tb : TB) : Prop :=
  forall s pl, atomic_res s = Some (Win pl) ->
  tb_lookup tb s = Some (pl, 0).

Lemma TB_final_respects_atomic_wins :
  respects_atomic_wins TB_final.
Proof.
  destruct (loop_iter TB_loop_data TB_init) as [k Hk].
  destruct k.
  - intros s pl s_res.
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
    + assert (In (s, (Black, 0)) (map (tag Black 0) (nodup Show_dec (enum_wins Black)))) as Hs.
      { rewrite in_map_iff.
        exists s; split; [reflexivity|].
        rewrite nodup_In.
        erewrite atomic_win_opp in s_play; [|exact s_res].
        apply enum_wins_correct2; now destruct pl.
      }
      pose proof (str_adds_ne_pos (map (tag Black 0) (nodup Show_dec (enum_wins Black)))
        s (Black, 0) Hs); lia.
    + assert (In (s, (White, 0)) (map (tag White 0) (nodup Show_dec (enum_wins White)))) as Hs.
      { rewrite in_map_iff.
        exists s; split; [reflexivity|].
        rewrite nodup_In.
        erewrite atomic_win_opp in s_play; [|exact s_res].
        apply enum_wins_correct2; now destruct pl.
      }
      pose proof (str_adds_ne_pos (map (tag White 0) (nodup Show_dec (enum_wins White)))
        s (White, 0) Hs); lia.
  - intros s pl s_res.
    apply satMate_TB_final_lookup.
    exists (atom_win s_res).
    split; auto.
    intro; simpl; lia.
Qed.

Lemma TB_lookup_None : forall s,
  tb_lookup TB_final s = None ->
  (atomic_res s = Some Draw) +
  (atomic_res s = None) * { m : Move s & tb_lookup TB_final (exec_move s m) = None }.
Proof.
  intros.
  destruct atomic_res eqn:s_res.
  - destruct r.
    + erewrite TB_final_respects_atomic_wins in H5;
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
      * admit.
      * admit.
Admitted.

Theorem TB_final_lookup_draw : forall s,
  tb_lookup TB_final s = None ->
  draw s.
Proof.
  cofix d.
  intros s tb_s.
  destruct (TB_lookup_None s tb_s) as
    [|[s_res [m tb_sm]]].
  - now apply atom_draw.
  - eapply (play_draw s _ eq_refl s_res).
    + clear m tb_sm.
      intro m.
      destruct (tb_lookup TB_final (exec_move s m)) eqn:tb_sm.
      * destruct p as [pl n].
        destruct (player_id_or_opp_r_t (to_play s) pl) as [pf|pf].
        ** destruct (tb_satMate TB_final TB_final_valid tb_sm) as
           [w [w_d w_m]].
           erewrite satMate_TB_final_lookup in tb_s; [congruence|].
           exists (eloise_win s_res pf _ w); split; [reflexivity|].
           intro w'; simpl.
           pose (tb_None _ TB_final_valid w' tb_s).
           pose (tb_small _ TB_final_valid tb_sm); lia.
        ** right.
           rewrite pf.
           rewrite opp_invol.
           eapply tb_satMate; [|eauto].
           exact TB_final_valid.
      * left.
        apply d.
        exact tb_sm.
    + apply d.
      exact tb_sm.
Defined.

Theorem draw_TB_final_lookup : forall s,
  draw s ->
  tb_lookup TB_final s = None.
Proof.
  intros s d.
  destruct (tb_lookup TB_final s) eqn:tb_s; [|reflexivity].
  destruct p as [pl n].
  destruct (TB_final_lookup_satMate _ _ _ tb_s).
  elim (win_not_draw _ _ x d).
Qed.

Theorem TB_final_lookup_mate : forall s pl n,
  tb_lookup TB_final s = Some (pl, n) ->
  mate pl s n.
Proof.
  intros s pl n tb_s.
  destruct (TB_final_lookup_satMate _ _ _ tb_s) as [w [w_d w_s]].
  exists w; split; auto.
Defined.

Theorem mate_TB_final_lookup : forall s pl n,
  mate pl s n ->
  tb_lookup TB_final s = Some (pl, n).
Proof.
  intros.
  apply satMate_TB_final_lookup.
  exact X.
Defined.

End TB.

Record CorrectTablebase (M : Type -> Type) `{StringMap M}
  (G : Game) `{Show (GameState G)} := {

  tb : TB (G := G) (M := M);

  tb_lookup_mate : forall s pl n,
    tb_lookup tb s = Some (pl, n) ->
    mate pl s n;
  mate_tb_lookup : forall s pl n,
    mate pl s n ->
    tb_lookup tb s = Some (pl, n);

  tb_lookup_draw : forall s,
    tb_lookup tb s = None ->
    draw s;

  draw_tb_lookup : forall s,
    draw s ->
    tb_lookup tb s = None

  }.

Definition certified_TB {M} `{StringMap M}
  {G} `{Show (GameState G)} `{FinGame G} `{Reversible G}
  `{NiceGame G} `{forall s, Discrete (Move s)} :
  CorrectTablebase M G := {|
  tb := TB_final;
  tb_lookup_mate := TB_final_lookup_mate;
  mate_tb_lookup := mate_TB_final_lookup;
  tb_lookup_draw := TB_final_lookup_draw;
  draw_tb_lookup := draw_TB_final_lookup
  |}.
