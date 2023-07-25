Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Coq.Sorting.Sorting.

Require Import Games.Game.Game.
Require Import Games.Bear.Graph.
Require Import Games.Bear.Sort.
Require Import Games.Game.TB.
Require Import Games.Game.Player.
Require Import Games.Util.Show.
Require Import Games.Util.Dec.
Require Import Games.Util.AssocList.
Require Import Games.Util.StringMap.

Definition NoDup_dec {X} `{Discrete X} (xs : list X) :
  { NoDup xs } + { ~ NoDup xs }.
Proof.
  induction xs.
  - left; constructor.
  - destruct (in_dec a xs).
    + right; intro pf.
      now inversion pf.
    + destruct IHxs.
      * left; now constructor.
      * right; intro pf.
        now inversion pf.
Defined.

Record BG_State (G : Graph) : Type := {

  to_play : Player;

  (* black *)
  bear : Vert G;
  (* white *)
  hunters : list (Vert G);

  hunters_sort : sorted hunters;
  hunters_3 : List.length hunters = 3;
  hunters_distinct : NoDup hunters;
  bear_not_hunter : ~ In bear hunters

  }.

Arguments to_play {_} _.
Arguments bear {_} _.
Arguments hunters {_} _.
Arguments hunters_distinct {_} _.
Arguments bear_not_hunter {_} _.

Record BearMv {G} (s : BG_State G) : Type := {
  b_dest : Vert G;
  b_dest_reachable : In b_dest (successors (bear s));

    (* reflexive loops are permitted so the
       bear can make a null move if possible *)
  b_dest_empty : ~ In b_dest (hunters s);

  }.

Arguments b_dest {_} {_} _.
Arguments b_dest_reachable {_} {_}.
Arguments b_dest_empty {_} {_}.

Record HunterMv {G} (s : BG_State G) : Type := {
  h_orig : Vert G;
  h_dest : Vert G;
  h_orig_playable : In h_orig (hunters s);
  h_dest_reachable : In h_dest (successors h_orig);
  h_dest_not_bear : h_dest <> bear s;

    (* reflexive loops are permitted so the
       hunter can make a null move if possible *)
  h_dest_not_diff_hunter : In h_dest (hunters s) -> h_dest = h_orig;
  }.

Arguments h_orig {_} {_}.
Arguments h_dest {_} {_}.
Arguments h_orig_playable {_} {_}.
Arguments h_dest_reachable {_} {_}.
Arguments h_dest_not_bear {_} {_}.

Inductive BG_Move {G} (s : BG_State G) : Type :=
  | BearMove : to_play s = Black -> BearMv s -> BG_Move s
  | HunterMove : to_play s = White -> HunterMv s -> BG_Move s.
(* 
Lemma shuffle1 {X} {w x y z : X} :
  NoDup [x;w;y;z] -> NoDup [w;x;y;z].
Proof.
  intros pf.
  inversion pf.
  inversion H5.
  inversion H9.
  repeat constructor; simpl in *; firstorder.
Qed.

Lemma shuffle2 {X} {w x y z : X} :
  NoDup [y;x;w;z] -> NoDup [w;x;y;z].
Proof.
  intros pf.
  inversion pf.
  inversion H5.
  inversion H9.
  repeat constructor; simpl in *; firstorder.
Qed.

Lemma shuffle3 {X} {w x y z : X} :
  NoDup [z;x;y;w] -> NoDup [w;x;y;z].
Proof.
  intros pf.
  inversion pf.
  inversion H5.
  inversion H9.
  repeat constructor; simpl in *; firstorder.
Qed.
 *)

Lemma no_remove_id {X} `{Discrete X}
  (x : X) (xs : list X) :
  ~ In x xs -> remove x xs = xs.
Proof.
  induction xs as [|y ys]; intro nIn.
  - reflexivity.
  - simpl.
    destruct (eq_dec x y).
    + elim nIn; now left.
    + simpl; rewrite IHys; auto.
      intro pf; apply nIn; now right.
Qed.

Lemma NoDup_remove {X} `{Discrete X}
  (x : X) (xs : list X) : NoDup xs ->
  NoDup (remove x xs).
Proof.
  induction xs as [|y ys]; intro nd_xs.
  - exact nd_xs.
  - simpl.
    destruct (eq_dec x y).
    + apply IHys.
      now inversion nd_xs.
    + constructor.
      * rewrite In_remove_iff.
        intros [_ pf].
        now inversion nd_xs.
      * apply IHys.
        now inversion nd_xs.
Qed.

Lemma remove_length {X} `{Discrete X}
  (x : X) (xs : list X) : forall n,
  NoDup xs -> In x xs ->
  List.length xs = S n ->
  List.length (remove x xs) = n.
Proof.
  induction xs as [|y xs']; intros n xs_nd HIn Hlen.
  - destruct HIn.
  - simpl.
    destruct (eq_dec x y).
    + rewrite no_remove_id.
      * simpl in Hlen; congruence.
      * rewrite e.
        now inversion xs_nd.
    + simpl.
      destruct n as [|k].
      * simpl in Hlen.
        inversion Hlen.
        destruct xs'; [|now simpl in H1].
        destruct HIn; [congruence|].
        destruct H0.
      * rewrite (IHxs' k); auto.
        -- now inversion xs_nd.
        -- destruct HIn; [congruence|auto].
Qed.

Definition exec_move {G} {s : BG_State G} (m : BG_Move s) : BG_State G.
Proof.
  destruct m.
  (* bear move *)
  - refine {|
      to_play := White;
      bear := b_dest b;
      hunters := hunters s;
      hunters_sort := _;
      hunters_3 := _;
      hunters_distinct := _;
      bear_not_hunter := _;
    |}.
    + apply s.
    + apply s.
    + apply s.
    + apply (b_dest_empty b).
  - refine {|
      to_play := Black;
      bear := bear s;
      hunters := insertion_sort (h_dest h :: (remove (h_orig h) (hunters s)));
      hunters_sort := _;
      hunters_3 := _;
      hunters_distinct := _;
      bear_not_hunter := _;
    |}.
    + apply insertion_sort_sorts.
    + rewrite insertion_sort_length; simpl.
      rewrite (remove_length _ _ 2); auto.
      * apply s.
      * apply h.
      * apply s.
    + apply insertion_sort_NoDup.
      constructor.
      * rewrite In_remove_iff; intro HIn.
        pose (h_dest_not_diff_hunter _ h).
        tauto.
      * apply NoDup_remove.
        apply s.
    + rewrite insertion_sort_In.
      intros [Heq|HIn].
      * exact (h_dest_not_bear h Heq).
      * rewrite In_remove_iff in HIn.
        now apply (bear_not_hunter s).
Defined.

Fixpoint pf_map {X Y} (xs : list X) (f : forall x, In x xs -> Y) {struct xs} : list Y.
Proof.
  destruct xs.
  - exact [].
  - apply cons.
    + apply (f x).
      left; reflexivity.
    + apply (pf_map _ _ xs).
      intros x' HIn.
      apply (f x').
      now right.
Defined.

Lemma in_pf_map_1 {X Y} (xs : list X) (f : forall x, In x xs -> Y) :
  forall y, In y (pf_map xs f) -> exists x pf, f x pf = y /\ In x xs.
Proof.
  induction xs; intros y HIn.
  - destruct HIn.
  - destruct HIn.
    + exists a, (or_introl eq_refl).
      split; auto.
      now left.
    + destruct (IHxs _ _ H) as [x [pf [Hx1 Hx2]]].
      exists x, (or_intror pf).
      split; auto.
      now right.
Qed.

Lemma in_pf_map_2 {X Y} (xs : list X) (f : forall x, In x xs -> Y) :
  forall y, (exists x pf, f x pf = y /\ In x xs) -> In y (pf_map xs f).
Proof.
  induction xs; intros y [x [pf [Hx1 Hx2]]].
  - destruct pf.
  - destruct pf.
    + destruct e.
      now left.
    + right.
      apply IHxs.
      exists x, i.
      now split.
Qed.

Lemma in_pf_map_iff {X Y} (xs : list X) (f : forall x, In x xs -> Y) :
  forall y, In y (pf_map xs f) <-> exists x pf, f x pf = y /\ In x xs.
Proof.
  intro y; split.
  - apply in_pf_map_1.
  - apply in_pf_map_2.
Qed.

Definition eqb {X} `{Discrete X} (x x' : X) : bool :=
  match eq_dec x x' with
  | left _ => true
  | right _ => false
  end.

Definition enum_moves {G} (s : BG_State G) : list (BG_Move s).
Proof.
  destruct (to_play s) eqn:s_res.
  - refine (List.concat (pf_map (hunters s) (fun h => _))).
    intro Hh.
    refine (pf_map (filter (fun v => andb (negb (eqb v (bear s))) (orb
      (negb (in_decb v (hunters s)))
      (eqb v h))) (successors h)) _).
    intros v HIn.
    rewrite filter_In in HIn.
    apply HunterMove; auto.
    refine {|
      h_orig := h;
      h_dest := v;
      h_orig_playable := Hh;
      h_dest_reachable := _;
      h_dest_not_bear := _;
      h_dest_not_diff_hunter := _;
    |}.
    + apply HIn.
    + destruct HIn as [_ HIn].
      rewrite Bool.andb_true_iff in HIn.
      destruct HIn as [Hv _].
      unfold eqb in Hv.
      destruct (eq_dec v (bear s)).
      * discriminate.
      * auto.
    + intro pf.
      destruct HIn as [_ HIn].
      rewrite Bool.andb_true_iff in HIn.
      destruct HIn as [_ Hv].
      rewrite Bool.orb_true_iff in Hv.
      destruct Hv as [Hv|Hv].
      * unfold in_decb in Hv.
        destruct (in_dec v (hunters s)).
        -- discriminate.
        -- contradiction.
      * unfold eqb in Hv.
        destruct (eq_dec v h).
        -- auto.
        -- discriminate.
  - refine (pf_map (filter (fun v => negb (in_decb v (hunters s))) (successors (bear s))) _).
    intros v HIn.
    apply BearMove; auto.
    refine {|
      b_dest := v;
      b_dest_reachable := _;
      b_dest_empty := _
    |}.
    + rewrite filter_In in HIn.
      apply HIn.
    + rewrite filter_In in HIn.
      destruct HIn as [_ HIn].
      unfold in_decb in HIn.
      destruct (in_dec v (hunters s)).
      * discriminate.
      * auto.
Defined.

Definition atomic_res {G} (s : BG_State G) : option Result :=
  match enum_moves s with
  | [] =>
    match to_play s with
    | White => Some Draw
    | Black => Some (Win White)
    end
  | _ => None
  end.

Require Import Coq.Logic.ProofIrrelevance.

Lemma BearMv_ext {G} (s : BG_State G) :
  forall m m' : BearMv s, b_dest m = b_dest m' -> m = m'.
Proof.
  intros.
  destruct m, m'; simpl in *.
  destruct H.
  f_equal; apply proof_irrelevance.
Qed.

Lemma HunterMv_ext {G} (s : BG_State G) :
  forall m m' : HunterMv s,
    h_orig m = h_orig m' ->
    h_dest m = h_dest m' ->
    m = m'.
Proof.
  intros.
  destruct m, m'; simpl in *.
  destruct H, H0.
  f_equal; apply proof_irrelevance.
Qed.

Definition BearGame (G : Graph) : Game.
Proof.
  refine {|
    GameState := BG_State G;
    Move := BG_Move;
    Game.to_play := to_play;
    Game.exec_move := @exec_move G;
    Game.atomic_res := atomic_res;
    Game.enum_moves := enum_moves;
    enum_all := _;
    to_play_exec_move := _;
    atomic_res_nil := _;
    nil_atomic_res := _;
  |}.
  - intros s m.
    destruct m.
    + unfold enum_moves.
      destruct s; simpl in *.
      destruct to_play0; [discriminate|].
      simpl.
      rewrite in_pf_map_iff.
      exists (b_dest b).
      assert (In (b_dest b) (filter (fun v : Vert G => negb (in_decb v hunters0)) (successors bear0))) as pf.
      { rewrite filter_In; split.
        * apply b.
        * unfold in_decb.
          destruct in_dec; [|reflexivity].
          elim (b_dest_empty b i).
      }
      exists pf.
      simpl; split; auto.
      f_equal; [apply proof_irrelevance|].
      destruct b; simpl.
      apply BearMv_ext; reflexivity.
    + unfold enum_moves.
      destruct s; simpl in *.
      destruct to_play0; [|discriminate].
      simpl.
      rewrite in_concat.
      eexists.
      rewrite in_pf_map_iff.
      split.
      * exists (h_orig h), (h_orig_playable h).
        split; auto.
        apply h.
      * rewrite in_pf_map_iff.
        exists (h_dest h).
        assert (In (h_dest h)
         (filter
            (fun v : Vert G =>
             (negb (eqb v bear0) && (negb (in_decb v hunters0) || eqb v (h_orig h)))%bool)
            (successors (h_orig h)))) as pf.
        { rewrite filter_In; split.
          * apply h.
          * rewrite Bool.andb_true_iff; split.
            -- unfold eqb.
               destruct eq_dec; [|reflexivity].
               elim (h_dest_not_bear h e0).
            -- rewrite Bool.orb_true_iff.
               unfold in_decb.
               destruct in_dec.
               ++ right; unfold eqb.
                  destruct eq_dec; [reflexivity|].
                  elim n.
                  now apply h_dest_not_diff_hunter.
               ++ now left.
        }
        exists pf; split; auto.
        f_equal; [apply proof_irrelevance|].
        destruct h; simpl.
        apply HunterMv_ext; reflexivity.
  - intros.
    destruct m.
    + simpl.
      now rewrite e.
    + simpl.
      now rewrite e.
  - intros s res s_res.
    unfold atomic_res in s_res.
    destruct (enum_moves s); [reflexivity|discriminate].
  - intros s Hmoves.
    unfold atomic_res.
    rewrite Hmoves.
    destruct (to_play s).
    + now exists Draw.
    + now exists (Win White).
Defined.

Axiom cheat : forall {X},X.

Global Instance BearGameStateShow {G} `{sh : Show (Vert G)}
  `{@CommaFree _ sh, @Nonnil _ sh, @SemicolonFree _ sh} : Show (GameState (BearGame G)).
Proof.
  simpl.
  refine {|
    show := fun s => "(" ++ show (to_play s) ++ "," ++ show (bear s) ++ "," ++ show (hunters s) ++ ")";
    show_inj := _
  |}.
  intros s s' pf.
  inversion pf.
  apply cheat.
Defined.

Definition all_BG_States (pl : Player) {G} : list (BG_State G).
Proof.
  refine (List.concat (List.map _ (enum : list (Vert G)))).
  intro b.
  pose (hunter_lists := sublists 3 (filter (fun h => negb (eqb h b)) enum)).
  refine (pf_map hunter_lists _).
  intros hs HIn.
  refine {|
    to_play := pl;
    bear := b;
    hunters := hs;
    hunters_sort := _;
    hunters_3 := _;
    hunters_distinct := _;
    bear_not_hunter := _
  |}.
  - unfold hunter_lists in HIn.
    eapply sublist_sort; eauto.
    apply sorted_filter.
    apply enum_sorted.
    apply cheat.
  - unfold hunter_lists in HIn.
    eapply sublist_length; eauto.
  - apply cheat.
  - intro pf.
    pose proof (sublist_In_trans _ _ _ _ pf HIn) as pf'.
    rewrite filter_In in pf'.
    unfold eqb in pf'.
    destruct (eq_dec b b).
    + destruct pf'; discriminate.
    + apply n; reflexivity.
Defined.

Global Instance Fin_BearGame {G} : FinGame (BearGame G).
Proof.
  unshelve econstructor.
  - exact (all_BG_States White ++ all_BG_States Black)%list.
  - intro pl.
    destruct pl eqn:?.
    + refine (filter _ (all_BG_States Black)).
      exact (fun s =>
        match enum_moves s with
        | [] => true
        | _ => false
        end).
    + exact [].
  - apply cheat.
  - apply cheat.
  - apply cheat.
Defined.

Definition switch_player {G} (s : BG_State G) : BG_State G := {|
  to_play := opp (to_play s);
  bear := bear s;
  hunters := hunters s;
  hunters_sort := hunters_sort G s;
  hunters_3 := hunters_3 G s;
  hunters_distinct := hunters_distinct s;
  bear_not_hunter := bear_not_hunter s
  |}.

Global Instance Reversible_BearGame {G} : Reversible (BearGame G).
Proof.
  unshelve econstructor.
  - intro s.
    exact (List.map (fun m => switch_player (exec_move m)) (enum_moves (switch_player s))).
  - intros s s' HIn.
    unshelve eexists.
    constructor.
    apply cheat.
    unshelve econstructor.
    apply s.
    apply cheat.
    apply cheat.
    apply cheat.
  - intros.
 apply cheat.
Defined.

Global Instance Nice_BearGame {G} : NiceGame (BearGame G).
Proof.
  constructor.
  intros s pl pf.
  unfold Game.atomic_res in pf.
  simpl in pf.
  unfold atomic_res in pf.
  destruct enum_moves; [|discriminate].
  unfold Game.to_play; simpl.
  destruct to_play; [discriminate|].
  now inversion pf.
Defined.


Global Instance DiscMove_BearGame {G} (s : GameState (BearGame G))
  : Discrete (Move s).
Proof.
  constructor.
  intros m m'.
  destruct m, m'; try congruence.
  - destruct (eq_dec (b_dest b) (b_dest b0)).
    + left; f_equal; [apply proof_irrelevance|].
      now apply BearMv_ext.
    + right; intro.
      inversion H.
      congruence.
  - destruct (eq_dec (h_orig h) (h_orig h0)).
    + destruct (eq_dec (h_dest h) (h_dest h0)).
      * left; f_equal; [apply proof_irrelevance|].
        now apply HunterMv_ext.
      * right; intro.
        inversion H.
        congruence.
    + right; intro.
      inversion H.
      congruence.
Defined.

Require Import Games.Util.OMap.

Definition Bear_TB (G : Graph) `{sh : Show (Vert G)}
  `{@CommaFree _ sh, @Nonnil _ sh, @SemicolonFree _ sh}
  : CorrectTablebase OM
  (BearGame G) := certified_TB.







