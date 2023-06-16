Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Draw.
Require Import Games.Game.Win.

Require Import Games.Util.TBLoop.
Require Import Games.Util.StringMap.
Require Import Games.Util.Show.
Require Import Games.Util.Dec.

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
    In s (enum_preds s') -> exists m, exec_move s m = s';
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

Definition respects_atomic_wins (tb : TB) : Prop := forall s pl,
  atomic_res s = Some (Win pl) ->
  tb_lookup tb s = Some (pl, 0).

Record TB_valid (tb : TB) : Type := {

  win_tb : forall {s pl} (w : win pl s),
    depth w < curr tb -> {n : nat & tb_lookup tb s = Some (pl, n)};

  tb_win : forall {s pl n},
    tb_lookup tb s = Some (pl, n) ->
    win pl s;

  tb_win_depth : forall {s pl n} (pf : tb_lookup tb s = Some (pl, n)),
    depth (tb_win pf) = n;

  tb_win_sat : forall {s pl n} (pf : tb_lookup tb s = Some (pl, n)),
    saturated (tb_win pf);

  win_last_white_positions : forall {s pl} (w : win pl s), to_play s = White ->
    depth w = curr tb -> In s (last_white_positions tb);

  last_white_positions_win : forall {s}, In s (last_white_positions tb) ->
    win (step_player (last_step tb) White) s;

  last_white_positions_win_depth : forall {s} (pf : In s (last_white_positions tb)),
    depth (last_white_positions_win pf) = curr tb;

  win_last_black_positions : forall {s pl} (w : win pl s), to_play s = Black ->
    depth w = curr tb -> In s (last_black_positions tb);

  tb_respects_atomic_wins : curr tb = 0 \/ respects_atomic_wins tb;

  last_white_positions_NoDup : NoDup (last_white_positions tb);

  last_black_positions_NoDup : NoDup (last_black_positions tb);

  last_white_positions_disj : forall s, In s (last_white_positions tb) -> str_lookup s (white_positions tb) = None;

  last_black_positions_disj : forall s, In s (last_black_positions tb) -> str_lookup s (black_positions tb) = None;

  sizes_never_exceed :
    size (white_positions tb) +
    size (black_positions tb) +
    length (last_white_positions tb) +
    length (last_black_positions tb) <= length enum_states;

  }.

(* Lemma win_tb_TB_init : forall s pl (w : win pl s),
    depth w < curr TB_init -> {n : nat & tb_lookup TB_init s = Some (pl, n)}.
Proof.
  unfold TB_init; simpl; lia.
Defined. *)

Lemma tb_win_TB_init :  forall s pl n,
  tb_lookup TB_init s = Some (pl, n) ->
  win pl s.
Proof.
  unfold TB_init, tb_lookup; simpl.
  intros s pl n Hs.
  destruct (to_play s);
  now rewrite str_lookup_empty in Hs.
Defined.

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
  refine {|
    win_tb := _;
    tb_win := tb_win_TB_init;
    tb_win_depth := _;
    tb_win_sat := _;
    win_last_white_positions := _;
    last_white_positions_win := last_white_positions_win_TB_init;
    last_white_positions_win_depth := _;
    win_last_black_positions := _;
    tb_respects_atomic_wins := _;
    last_white_positions_NoDup := _;
    last_black_positions_NoDup := _;
    last_white_positions_disj := _;
    last_black_positions_disj := _;
    sizes_never_exceed := _;
  |}.
Proof.
  (* win_tb *)
  - unfold TB_init; simpl; lia.
  (* tb_win_depth *)
  - intros.
    cut False; [tauto|].
    unfold tb_lookup in pf.
    destruct (to_play s) eqn:s_play; simpl in pf;
    now rewrite str_lookup_empty in pf.
  (* tb_win_sat *)
  - intros.
    cut False; [tauto|].
    unfold tb_lookup in pf.
    destruct (to_play s) eqn:s_play; simpl in pf;
    now rewrite str_lookup_empty in pf.
  (* win_last_white_positions *)
  - intros s pl w s_play w_depth.
    simpl in *.
    rewrite nodup_In.
    apply enum_wins_correct2.
    destruct w.
    + rewrite (atomic_win_opp _ _ e) in s_play.
      now destruct pl.
    + now simpl in w_depth.
    + now simpl in w_depth.
  (* last_white_positions_win_depth *)
  - now intros.
  (* win_last_black_positions *)
  - intros s pl w s_play w_depth.
    simpl in *.
    rewrite nodup_In.
    apply enum_wins_correct2.
    destruct w.
    + rewrite (atomic_win_opp _ _ e) in s_play.
      now destruct pl.
    + now simpl in w_depth.
    + now simpl in w_depth.
  (* tb_respects_atomic_wins *)
  - now left.
  (* last_white_positions_NoDup *)
  - apply NoDup_nodup.
  (* last_black_positions_NoDup *)
  - apply NoDup_nodup.
  (* last_white_positions_disj *)
  - intros; apply str_lookup_empty.
  (* last_black_positions_disj *)
  - intros; apply str_lookup_empty.
  (* sizes_never_exceed *)
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

Lemma TB_step_valid : forall tb, TB_valid tb
  -> TB_valid (TB_step tb).
Proof.
Admitted.

Definition TB_validity_data : validity_data TB_loop_data.
Proof.
  refine ( {|
  valid := TB_valid;
  step_valid := _
  |} ).
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

Lemma num_left_lt : forall tb (s : GameState G) pl
  (w : win pl s), TB_valid tb -> depth w = curr tb ->
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
          eapply win_last_white_positions; eauto.
        }
        lia.
      * assert (B > 0).
        { unfold W.
          apply (In_length_pos _ s).
          eapply win_last_black_positions; eauto.
        }
        lia.
    + rewrite map_map.
      unfold tag.
      simpl.
      rewrite map_id.
      apply last_black_positions_NoDup; auto.
    + rewrite map_map.
      unfold tag.
      simpl.
      rewrite map_id.
      apply last_black_positions_disj; auto.
  - rewrite map_map.
    unfold tag.
    simpl.
    rewrite map_id.
    apply last_white_positions_NoDup; auto.
  - rewrite map_map.
    unfold tag.
    simpl.
    rewrite map_id.
    apply last_white_positions_disj; auto.
Qed.

Lemma win_TB_final_lookup : forall s pl,
  win pl s -> {n : nat & tb_lookup TB_final s = Some (pl, n)}.
Proof.
  intros s pl w.
  destruct (win_tb TB_final TB_final_valid w).
  - destruct (loop_iter TB_loop_data TB_init) as [k Hk].
    unfold TB_final; rewrite Hk.
    rewrite iter_curr.
    destruct (Compare_dec.le_lt_dec k (depth w)); [|auto].
    destruct (depth_lower _ _ l) as [s' [w' w'_depth]].
    pose proof (loop_measure TB_loop_data TB_init).
    rewrite Hk in H5.
    simpl in H5.
    assert (num_left (TB_step (Nat.iter k TB_step TB_init)) <
      num_left (Nat.iter k TB_step TB_init));
      [|lia].
    eapply num_left_lt.
    + apply (iter_step_valid TB_loop_data TB_validity_data).
      exact TB_init_valid.
    + rewrite iter_curr. exact w'_depth.
  - exists x.
    exact e.
Defined.

Theorem TB_final_lookup_mate : forall s pl n,
  tb_lookup TB_final s = Some (pl, n) ->
  mate pl s n.
Proof.
  intros.
  destruct TB_final_valid.
  exists (tb_win0 _ _ _ H5).
  split.
  - apply tb_win_depth0.
  - apply saturated_minimal.
    apply tb_win_sat0.
Defined.

Theorem mate_TB_final_lookup : forall s pl n,
  mate pl s n ->
  tb_lookup TB_final s = Some (pl, n).
Proof.
  intros s pl n [w [w_d w_m]].
  destruct (win_TB_final_lookup _ _ w) as [m Hm].
  destruct (TB_final_lookup_mate _ _ _ Hm) as
    [w' [w'_d w'_m]].
  cut (m = n); [congruence|].
  pose (w_m w').
  pose (w'_m w).
  lia.
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

(* (* Definition respects_atomic_wins (tb : TB) : Prop :=
  forall s pl, atomic_res s = Some (Win pl) ->
  tb_lookup tb s = Some (pl, 0). *) *)

Lemma respects_atomic_wins_step_1 : respects_atomic_wins (TB_step TB_init).
Proof.
  intros s pl s_res.
  unfold TB_step, TB_init, tb_lookup; simpl.
  destruct (to_play s) eqn:s_play.
  - unfold add_positions.
    apply str_lookup_adds.
    + apply map_tag_functional.
    + rewrite in_map_iff.
      rewrite (atomic_win_opp s pl s_res) in s_play.
      destruct pl; [discriminate|].
      exists s; split; [reflexivity|].
      rewrite nodup_In.
      now apply enum_wins_correct2.
  - unfold add_positions.
    apply str_lookup_adds.
    + apply map_tag_functional.
    + rewrite in_map_iff.
      rewrite (atomic_win_opp s pl s_res) in s_play.
      destruct pl; [|discriminate].
      exists s; split; [reflexivity|].
      rewrite nodup_In.
      now apply enum_wins_correct2.
Qed.

(** TODO : use in step proof *)
(* Lemma respects_atomic_wins_step : forall tb, TB_valid tb -> respects_atomic_wins tb ->
  respects_atomic_wins (TB_step tb).
Proof.
  intros tb tb_v Htb s pl s_res.
  unfold TB_step, tb_lookup; simpl.
  destruct (to_play s) eqn:s_play; unfold add_positions.
  - rewrite str_lookup_adds_nIn.
    + pose proof (Htb s pl s_res) as Htb.
      unfold tb_lookup in Htb.
      now rewrite s_play in Htb.
    + rewrite in_map_iff.
      intros [[? [pl' n']] [? Hs]].
      simpl in *; subst.
      rewrite in_map_iff in Hs.
      destruct Hs as [s' [Hs'1 Hs'2]].
      unfold tag in Hs'1.
      inversion Hs'1; subst.
      pose (Htb s _ s_res).
Admitted. *)

Lemma TB_final_respects_atomic_wins :
  respects_atomic_wins TB_final.
Proof.
  destruct (tb_respects_atomic_wins TB_final).
  - apply TB_final_valid.
  - destruct (loop_iter TB_loop_data TB_init) as [k Hk].
    unfold TB_final in H5.
    rewrite Hk in H5.
    rewrite iter_curr in H5.
    subst; simpl in *.
    pose proof (loop_measure TB_loop_data TB_init) as Hmeasure.
    simpl in Hmeasure.
    rewrite Hk in Hmeasure.
    unfold num_left in Hmeasure.
    simpl in Hmeasure.
    rewrite size_empty in Hmeasure.
    unfold add_positions in Hmeasure.
    intros s pl s_res.
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
  - auto.
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
    + destruct (forallb
        (fun p => player_eqb (fst p) (opp (to_play s))) ps) eqn:Hps2.
      * cut (win (opp (to_play s)) s); [intro w;
           destruct (win_TB_final_lookup _ _ w); congruence|].
        apply abelard_win; [auto | now rewrite opp_invol|].
        intro m.
        pose proof (forallb_true _ _ Hps2).
        symmetry in Hps.
        destruct (map_fg_lemma Hps m (enum_all m)) as
          [[pl n] [HIn Htb]].
        symmetry in Htb.
        destruct (TB_final_lookup_mate _ _ _ Htb) as [w _].
        eapply (tb_win TB_final TB_final_valid).
        rewrite <- (player_eqb_true _ _ (H6 _ HIn)); simpl.
        exact Htb.
      * destruct (forallb_false _ _ Hps2) as [[pl n] [HIn Heqb]].
        simpl in *.
        pose proof (player_eqb_false _ _ Heqb) as pf.
        rewrite opp_invol in pf.
        destruct (map_fg_lemma Hps _ HIn) as [m [_ tb_m]].
        pose (w := tb_win TB_final TB_final_valid tb_m).
        symmetry in pf.
        pose (w' := eloise_win s_res pf m w).
        destruct (win_TB_final_lookup _ _ w') as [k tb_s].
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
        ** pose (w := tb_win TB_final TB_final_valid tb_sm).
           pose (eloise_win s_res pf _ w) as w'.
           destruct (win_TB_final_lookup _ _ w').
           congruence.
        ** right.
           rewrite pf.
           rewrite opp_invol.
           eapply tb_win; [|eauto].
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
  destruct (TB_final_lookup_mate s pl n tb_s) as
    [w _].
  elim (win_not_draw _ _ w d).
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
