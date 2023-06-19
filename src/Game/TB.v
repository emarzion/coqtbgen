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
  { w : win pl s & depth w = n /\ saturated w }.

Record TB_valid (tb : TB) : Type := {

  satMate_tb : forall {s pl n},
    n < curr tb -> satMate pl s n ->
    tb_lookup tb s = Some (pl, n);

  tb_satMate : forall {s pl n},
    tb_lookup tb s = Some (pl, n) ->
    satMate pl s n; (* TODO /\ n < curr tb *)

  satMate_lwp : forall {s pl},
    to_play s = White ->
    satMate pl s (curr tb) ->
    In s (last_white_positions tb) /\ pl = step_player (last_step tb) White;

  lwp_satMate : forall {s},
    In s (last_white_positions tb) ->
    satMate (step_player (last_step tb) White) s (curr tb);

  satMate_lbp : forall {s pl},
    to_play s = Black ->
    satMate pl s (curr tb) ->
    In s (last_black_positions tb) /\ pl = step_player (last_step tb) Black;

  lbp_satMate : forall {s},
    In s (last_black_positions tb) ->
    satMate (step_player (last_step tb) Black) s (curr tb);

(*
  tb_respects_atomic_wins : curr tb = 0 \/ respects_atomic_wins tb;
*)
  lwp_NoDup : NoDup (last_white_positions tb);

  lbp_NoDup : NoDup (last_black_positions tb);

  lwp_disj : forall s, In s (last_white_positions tb) -> str_lookup s (white_positions tb) = None;

  lbp_disj : forall s, In s (last_black_positions tb) -> str_lookup s (black_positions tb) = None;

  sizes_never_exceed :
    size (white_positions tb) +
    size (black_positions tb) +
    length (last_white_positions tb) +
    length (last_black_positions tb) <= length enum_states;

  }.

Lemma last_white_positions_win_TB_init : forall s,
  In s (last_white_positions TB_init) ->
  win (step_player (last_step TB_init) White) s.
Proof.
  intros.
  apply atom_win.
  simpl.
  apply enum_wins_correct1.
  simpl in H5.
  now rewrite nodup_In in H5.
Defined.

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
  - intros s pl s_play [w [w_d _]].
    destruct w; simpl in *; try lia.
    rewrite (atomic_win_opp _ _ e) in s_play.
    assert (pl = Black) as s_pl by (now apply opp_inj).
    split; auto.
    rewrite nodup_In.
    apply enum_wins_correct2; congruence.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    pose proof (enum_wins_correct1 _ _ HIn) as s_res.
    exists (atom_win s_res); now split.
  - intros s pl s_play [w [w_d _]].
    destruct w; simpl in *; try lia.
    rewrite (atomic_win_opp _ _ e) in s_play.
    assert (pl = White) as s_pl by (now apply opp_inj).
    split; auto.
    rewrite nodup_In.
    apply enum_wins_correct2; congruence.
  - intros s HIn; simpl in *.
    rewrite nodup_In in HIn.
    pose proof (enum_wins_correct1 _ _ HIn) as s_res.
    exists (atom_win s_res); now split.
  - apply NoDup_nodup.
  - apply NoDup_nodup.
  - intros.
    now apply str_lookup_empty.
  - intros.
    now apply str_lookup_empty.
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

Definition satMate_invert {s pl n} (sm : satMate pl s (S n)) :
  { m : Move s & satMate pl (exec_move s m) n }.
Proof.
  destruct sm as [w [w_d w_s]].
  destruct w.
  - now simpl in w_d.
  - exists m, w.
    simpl in *; split; auto.
    tauto.
  - simpl in *.
    pose proof (pf := PeanoNat.Nat.succ_inj _ _ w_d).
    destruct (list_max_ne_achieves
      (map (fun m => depth (w m)) (enum_moves b))).
    + exfalso.
      assert (enum_moves b = []) as ms_nil by (eapply map_eq_nil; eauto).
      destruct (nil_atomic_res ms_nil); congruence.
    + destruct (in_map_sig i) as [m Hm].
      exists m, (w m); split.
      * destruct Hm; congruence.
      * apply w_s.
Defined.
Check in_concat.

Lemma in_concat_sig {X} (xss : list (list X)) (x : X) :
  In x (concat xss) -> {xs : list X & In xs xss /\ In x xs}.
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
        destruct (satMate_lwp _ v s_play sm) as [? Hpl].
        split; auto.
        now rewrite Hpl.
      * simpl.
        unfold add_positions.
        erewrite str_lookup_adds;
        [reflexivity| apply map_tag_functional|].
        rewrite in_map_iff.
        exists s.
        rewrite pf' in sm.
        destruct (satMate_lbp _ v s_play sm) as [? Hpl].
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
  (* satMate_lwp *)
  - intros s pl s_play sm.
    simpl in *.
    destruct (satMate_invert sm) as [m sm'].
    assert (to_play (exec_move s m) = Black) as s'_play
      by (now rewrite to_play_exec_move, s_play).
    destruct (satMate_lbp _ v s'_play sm') as [_ Hstep].
    destruct (last_step tb) eqn:tb_step; simpl in *.
    + split; auto.
      unfold abelard_step.
      rewrite nodup_In.
      rewrite filter_In.
      rewrite In_filter_Nones_iff.
      repeat split.
      * admit.
      * rewrite in_concat.
        exists (enum_preds (exec_move s m)).
        split; [|apply enum_preds_correct2].
        apply in_map.
        eapply satMate_lbp; eauto.
      * rewrite forallb_forall.
        intros m' _.
        unfold add_positions.
        unfold tag.
        admit.
    + split; auto.
      unfold eloise_step.
      rewrite nodup_In.
      rewrite In_filter_Nones_iff.
      split.
      * apply not_Some_None.
        intros [pl' k] Htb.
        destruct (str_lookup_adds_invert _ _ _ _ Htb) as [pf|pf].
        ** unfold tag in pf.
           rewrite in_map_iff in pf.
           destruct pf as [s' [Hs'1 Hs'2]].
           pose (lwp_satMate _ v Hs'2) as sm''.
           admit. (* contra minimal *)
        ** epose (@tb_satMate _ v s pl' k) as sm''.
           unfold tb_lookup in sm''.
           rewrite s_play in sm''.
           specialize (sm'' pf).
           (* contra minimal *)
           admit.
      * rewrite in_concat.
        exists (enum_preds (exec_move s m)).
        split; [|apply enum_preds_correct2].
        apply in_map.
        eapply satMate_lbp; eauto.
  (* lwp_satMate *)
  - intros s HIn.
    simpl in *.
    destruct (last_step tb) eqn:tb_step; simpl in *.
    + unfold abelard_step in HIn.
      rewrite nodup_In in HIn.
      rewrite filter_In in HIn.
      destruct HIn as [HIn' Hmoves].
      rewrite In_filter_Nones_iff in HIn'.
      destruct HIn' as [tb_s HIn].
      rewrite forallb_forall in Hmoves.
      simpl in Hmoves.
      assert (forall m, {k : nat & satMate Black (exec_move s m) k}).
      { intro m.
        specialize (Hmoves m (enum_all m)).
        destruct (str_lookup (exec_move s m)
          (add_positions (black_positions tb)
          (step_player (last_step tb) Black)
          (curr tb) (last_black_positions tb))) as [[[|]]|] eqn:tb_sm; try discriminate.
        destruct (str_lookup_adds_invert _ _ _ _ tb_sm) as [pf|pf].
        * destruct (in_map_sig pf) as [s' [Hs'1 Hs'2]].
          unfold tag in Hs'1.
          pose (lbp_satMate _ v Hs'2).
          exists (curr tb); congruence.
        * admit.
      }
      admit.
    + unfold eloise_step in HIn.
      rewrite nodup_In in HIn.
      rewrite In_filter_Nones_iff in HIn.
      destruct HIn as [tb_s HIn'].
      unfold add_positions in tb_s.
      rewrite tb_step in *.
      destruct (in_concat_sig _ _ HIn') as [ss [Hss1 Hss2]].
      destruct (in_map_sig Hss1) as [s' [Hs'1 Hs'2]]; subst.
      Search enum_preds.
      destruct (enum_preds_correct1 _ _ Hss2) as [m Hm]; subst.
      epose (lbp_satMate _ v Hs'2) as sm.
      rewrite tb_step in sm; simpl in sm.
      assert (to_play s = White) as s_play by admit.
      assert (atomic_res s = None) as s_res by admit.
      destruct sm as [w [w_d w_s]].
      pose (w' := eloise_win s_res s_play m w).
      exists w'; split.
      * simpl; auto.
      * simpl; split; auto.
        intros.
        clear Hss2.
        
      simpl.
      admit. (* HERE *)
  (* satMate_lbp *)
  - admit.
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
      admit.
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
  apply (satMate_tb TB_final TB_final_valid); auto.
  destruct (loop_iter TB_loop_data TB_init) as [k Hk].
  unfold TB_final; rewrite Hk.
  rewrite iter_curr.
  destruct (Compare_dec.le_lt_dec k n); [|auto].
  destruct sm as [w [w_d w_s]].
  rewrite <- w_d in l.
  destruct (sat_lower _ _ w_s l) as [s' [w' [w'_depth w'_sat]]].
  pose proof (loop_measure TB_loop_data TB_init).
  rewrite Hk in H5.
  simpl in H5.
  assert (num_left (TB_step (Nat.iter k TB_step TB_init)) <
    num_left (Nat.iter k TB_step TB_init));
    [|lia].
  eapply num_left_lt; [|exact (iter_step_valid TB_loop_data TB_validity_data _ _ TB_init_valid)].
  exists w'; split; auto.
  rewrite iter_curr; exact w'_depth.
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
    now split.
Qed.

Fixpoint list_min (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
    match list_min xs' with
    | None => Some x
    | Some y => Some (Nat.min x y)
    end
  end.

Lemma list_min_cons : forall xs x,
  exists y, list_min (x :: xs) = Some y.
Proof.
  intros.
  simpl.
  destruct (list_min xs); eexists; reflexivity.
Qed.

Lemma list_min_achieves : forall xs x,
  list_min xs = Some x -> In x xs.
Proof.
  induction xs; intros x Hxs.
  - discriminate.
  - simpl in Hxs.
    destruct (list_min xs) eqn:lm.
    + inversion Hxs as [Hmin].
      destruct (PeanoNat.Nat.min_spec_le a n) as [[_ Hm]|[_ Hm]].
      * now left.
      * right; apply IHxs; congruence.
    + left; congruence.
Qed.

Lemma list_min_le : forall xs x,
  In x xs ->
  match list_min xs with
  | None => False
  | Some y => y <= x
  end.
Proof.
  induction xs; intros x HIn.
  - exact HIn.
  - simpl.
    destruct (list_min xs) eqn:Hxs.
    + destruct HIn.
      * rewrite H5.
        apply PeanoNat.Nat.le_min_l.
      * apply (PeanoNat.Nat.le_trans _ n).
        ** apply PeanoNat.Nat.le_min_r.
        ** now apply IHxs.
    + destruct HIn; [lia|].
      destruct (IHxs _ H5).
Qed.

Definition list_min_ne (xs : list nat) : nat :=
  match list_min xs with
  | None => 0
  | Some x => x
  end.

Lemma list_min_ne_achieves : forall xs,
  { xs = [] } + {In (list_min_ne xs) xs}.
Proof.
  destruct xs.
  - now left.
  - right.
    unfold list_min_ne.
    destruct (list_min_cons xs n) as [k Hk].
    rewrite Hk.
    now apply list_min_achieves.
Qed.

Lemma list_min_ne_le : forall xs x,
  In x xs -> list_min_ne xs <= x.
Proof.
  intros.
  pose proof (list_min_le _ _ H5).
  unfold list_min_ne.
  destruct (list_min xs); lia.
Qed.

Fixpoint map_filter_Somes {X Y} (f : X -> option Y) (xs : list X) : list Y :=
  match xs with
  | [] => []
  | x :: xs' =>
    match f x with
    | Some y => y :: map_filter_Somes f xs'
    | None => map_filter_Somes f xs'
    end
  end.

Lemma In_map_filter_Somes_sig {X Y} `{Discrete Y} {f : X -> option Y} {xs} : forall {y},
  In y (map_filter_Somes f xs) -> {x : X & In x xs /\ f x = Some y}.
Proof.
  induction xs as [|x xs'].
  - intros _ [].
  - simpl.
    intros y HIn; destruct (f x) eqn:fx.
    + destruct (eq_dec y0 y).
      * exists x; split; [tauto|congruence].
      * destruct (IHxs' y).
        ** destruct HIn; [contradiction|auto].
        ** exists x0; split; tauto.
    + destruct (IHxs' _ HIn).
      exists x0; split; tauto.
Defined.

Lemma In_map_filter_Somes_1 {X Y} (f : X -> option Y) (xs : list X) : forall y,
  In y (map_filter_Somes f xs) -> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x xs'].
  - intros _ [].
  - simpl.
    intros y HIn; destruct (f x) eqn:fx.
    + destruct HIn.
      * exists x; split; [tauto|congruence].
      * destruct (IHxs' _ H5).
        exists x0; split; tauto.
    + destruct (IHxs' _ HIn).
      exists x0; split; tauto.
Qed.

Lemma In_map_filter_Somes_2 {X Y} (f : X -> option Y) (xs : list X) : forall y,
  (exists x, In x xs /\ f x = Some y) -> In y (map_filter_Somes f xs).
Proof.
  induction xs as [|x xs'].
  - intros _ [? [[] _]].
  - intros y [x' [[Heq|HIn] Hf]].
    + simpl.
      rewrite Heq, Hf.
      now left.
    + simpl; destruct (f x);
      [right|idtac]; apply IHxs'; exists x'; tauto.
Qed.

Lemma In_map_filter_Somes_iff {X Y} (f : X -> option Y) (xs : list X) : forall y,
  In y (map_filter_Somes f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  intro y; split.
  - apply In_map_filter_Somes_1.
  - apply In_map_filter_Somes_2.
Qed.

Lemma player_eqb_refl : forall p, player_eqb p p = true.
Proof.
  now destruct p.
Qed.

Lemma list_max_ext {X} (f g : X -> nat)
  (fg : forall x, f x = g x) (xs : list X) :
  list_max (map f xs) = list_max (map g xs).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    now rewrite fg, IHxs.
Qed.

Definition win_satMate_aux : forall n s pl (w : win pl s),
  depth w = n -> { k : nat & satMate pl s k }.
Proof.
  intro n.
  induction (Wf_nat.lt_wf n) as [n _ IHn].
  intros s pl w w_d.
  destruct w as [ s s_res | s s_res s_play m w' | s s_res s_play ws ].
  - exists 0.
    exists (atom_win s_res); now split.
  - simpl in w_d.
    assert (depth w' < n) as w'_d by lia.
    destruct (IHn _ w'_d _ _ w' eq_refl) as [k sm].
    pose (non_drawn_pairs :=
      map_filter_Somes (fun m' => tb_lookup TB_final (exec_move s m')) (enum_moves s)).
    pose (won_pairs :=
      filter (fun p => player_eqb (fst p) pl) non_drawn_pairs).
    pose (won_ns := map snd won_pairs).
    exists (S (list_min_ne won_ns)).
    assert (In k won_ns) as pf.
    { unfold won_ns.
      rewrite in_map_iff.
      exists (pl, k); split; [reflexivity|].
      unfold won_pairs.
      rewrite filter_In.
      split; [|apply player_eqb_refl].
      unfold non_drawn_pairs.
      rewrite In_map_filter_Somes_iff.
      exists m; split; [apply enum_all| auto].
      exact (satMate_TB_final_lookup _ _ _ sm).
    }
    destruct (list_min_ne_achieves won_ns) as [pf_nil|HIn];
      [rewrite pf_nil in pf; destruct pf|].
    destruct (in_map_sig HIn) as [[pl' l] [Hl HIn']]; clear HIn.
    simpl in Hl; rewrite <- Hl.
    unfold won_pairs in HIn'.
    rewrite filter_In in HIn'; destruct HIn' as [HIn pl_eq].
    simpl in pl_eq.
    rewrite (player_eqb_true _ _ pl_eq) in HIn; clear pl_eq.
    unfold non_drawn_pairs in HIn.
    destruct (In_map_filter_Somes_sig HIn) as [m' [_ tb_sm']].
    clear w_d.
    destruct (TB_final_lookup_satMate _ _ _ tb_sm') as [w [w_d w_s]].
    pose (w'' := eloise_win s_res s_play m' w).
    exists w''; split; simpl; [rewrite w_d; congruence|].
    split; auto.
    intros.
    destruct (le_lt_dec n (depth w''0)).
    + apply (PeanoNat.Nat.le_trans _ n); auto.
      apply (PeanoNat.Nat.le_trans _ (depth w')); [|lia].
      destruct sm as [wk [wk_d wk_s]].
      apply (PeanoNat.Nat.le_trans _ (depth wk)); [|now apply saturated_minimal].
      rewrite w_d.
      rewrite Hl.
      apply list_min_ne_le.
      unfold won_ns.
      rewrite in_map_iff.
      exists (pl, depth wk); split; [reflexivity|].
      unfold won_pairs.
      rewrite filter_In.
      split; [|apply player_eqb_refl].
      unfold non_drawn_pairs.
      rewrite In_map_filter_Somes_iff.
      exists m.
      split; [apply enum_all|].
      apply satMate_TB_final_lookup.
      exists wk; now split.
    + destruct (IHn _ l0 _ _ w''0 eq_refl) as [p smp].
      apply (PeanoNat.Nat.le_trans _ p).
      * rewrite w_d, Hl.
        apply list_min_ne_le.
        unfold won_ns.
        rewrite in_map_iff.
        exists (pl, p).
        split; [reflexivity|].
        unfold won_pairs.
        rewrite filter_In.
        split; [|apply player_eqb_refl].
        unfold non_drawn_pairs.
        rewrite In_map_filter_Somes_iff.
        exists m'0.
        split; [apply enum_all|].
        apply satMate_TB_final_lookup; exact smp.
      * destruct smp.
        destruct a.
        rewrite <- H5.
        now apply saturated_minimal.
  - assert (forall m, depth (ws m) < n) as wm_d.
    { intro m.
      simpl in w_d.
      assert (list_max (map (fun m => depth (ws m)) (enum_moves s)) < n) as Hmax by lia.
      rewrite list_max_lt in Hmax.
      + Search Forall In.
        rewrite Forall_forall in Hmax.
        apply Hmax.
        rewrite in_map_iff.
        exists m; split; [reflexivity|].
        apply enum_all.
      + intro pf; pose proof (map_eq_nil _ _ pf) as moves_nil.
        assert (In m (enum_moves s)) as HIn by apply enum_all.
        rewrite moves_nil in HIn; exact HIn.
    }
    pose (fun m => IHn _ (wm_d m) _ _ (ws m) eq_refl) as sms.
    exists (S (list_max (map (fun m => projT1 (sms m)) (enum_moves s)))).
    pose (abelard_win s_res s_play (fun m =>
      projT1 (projT2 (sms m)))) as w'.
    exists w'.
    split.
    + unfold w'.
      simpl.
      f_equal.
      apply list_max_ext.
      intro m.
      simpl.
      destruct (sms m).
      destruct s0.
      simpl; tauto.
    + simpl; intro.
      destruct (sms m); simpl.
      destruct s0; simpl; tauto.
Defined.

Definition win_satMate : forall s pl,
  win pl s -> { k : nat & satMate pl s k } :=
  fun s pl w => win_satMate_aux (depth w) s pl w eq_refl.

Lemma win_tb : forall s pl,
  win pl s -> { k : nat & tb_lookup TB_final s = Some (pl, k) }.
Proof.
  intros s pl w.
  destruct (win_satMate s pl w) as [k sm].
  exists k.
  now apply satMate_TB_final_lookup.
Defined.

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
    + destruct (forallb
        (fun p => player_eqb (fst p) (opp (to_play s))) ps) eqn:Hps2.
      * cut (win (opp (to_play s)) s); [intro w;
           destruct (win_tb _ _ w); congruence|].
        apply abelard_win; [auto | now rewrite opp_invol|].
        intro m.
        pose proof (forallb_true _ _ Hps2).
        symmetry in Hps.
        destruct (map_fg_lemma Hps m (enum_all m)) as
          [[pl n] [HIn Htb]].
        symmetry in Htb.
        destruct (TB_final_lookup_satMate _ _ _ Htb) as [w _].
        eapply (tb_satMate TB_final TB_final_valid).
        rewrite <- (player_eqb_true _ _ (H6 _ HIn)); simpl.
        exact Htb.
      * destruct (forallb_false _ _ Hps2) as [[pl n] [HIn Heqb]].
        simpl in *.
        pose proof (player_eqb_false _ _ Heqb) as pf.
        rewrite opp_invol in pf.
        destruct (map_fg_lemma Hps _ HIn) as [m [_ tb_m]].
        pose (w := projT1 (tb_satMate TB_final TB_final_valid tb_m)).
        symmetry in pf.
        pose (w' := eloise_win s_res pf m w).
        destruct (win_tb _ _ w') as [k tb_s].
        congruence.
Defined.

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
           pose (eloise_win s_res pf _ w) as w'.
           destruct (win_satMate _ _ w').
           erewrite satMate_TB_final_lookup in tb_s; [congruence|eauto].
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
  now apply saturated_minimal.
Defined.

Theorem mate_TB_final_lookup : forall s pl n,
  mate pl s n ->
  tb_lookup TB_final s = Some (pl, n).
Proof.
  intros s pl n [w [w_d w_m]].
  destruct (win_satMate _ _ w) as [n' sm].
  rewrite (satMate_TB_final_lookup _ _ _ sm).
  repeat f_equal.
  destruct sm as [w' [w'_d w'_s]].
  rewrite <- w_d, <- w'_d.
  apply PeanoNat.Nat.le_antisymm.
  - now apply saturated_minimal.
  - apply w_m.
Qed.

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
