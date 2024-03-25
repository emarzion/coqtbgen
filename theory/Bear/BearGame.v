Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Coq.Sorting.Sorting.
Require Import Games.Game.Game.

Require Import Games.Game.Game.
Require Import TBGen.Bear.Graph.
Require Import TBGen.Bear.Sort.
Require Import TBGen.TB.TB.
Require Import Games.Game.Player.
Require Import TBGen.Util.IntHash.
Require Import Games.Util.Dec.
Require Import TBGen.Util.AssocList.
Require Import TBGen.Util.IntMap.
Require Import TBGen.Util.OMap.
Require Import TBGen.TB.OCamlTB.

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

Definition create_Move {G} (s : BG_State G) (v v' : Vert G) : option (BG_Move s).
Proof.
  destruct (to_play s) eqn:s_play.
  - destruct (in_dec v (hunters s)); [|exact None].
    destruct (in_dec v' (successors v)); [|exact None].
    destruct (eq_dec v' (bear s)); [exact None|].
    destruct (in_dec v' (hunters s)).
    + destruct (eq_dec v' v); [|exact None].
      apply Some; apply HunterMove; auto.
      econstructor.
      * exact i.
      * exact i0.
      * exact n.
      * intro; exact e.
    + apply Some; apply HunterMove; auto.
      econstructor.
      * exact i.
      * exact i0.
      * exact n.
      * intro; contradiction.
  - destruct (eq_dec v (bear s)); [|exact None].
    destruct (in_dec v' (successors v)); [|exact None].
    destruct (in_dec v' (hunters s)); [exact None|].
    apply Some; apply BearMove; auto.
    econstructor.
    + destruct e.
      exact i.
    + exact n.
Defined.

Definition is_hunter {G} (s : BG_State G)
  (v : Vert G) : bool :=
  match in_dec v (hunters s) with
  | left _ => true
  | right _ => false
  end.

Definition is_bear {G} (s : BG_State G)
  (v : Vert G) : bool :=
  match eq_dec v (bear s) with
  | left _ => true
  | right _ => false
  end.

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

Inductive dep_data X (P : X -> Prop) (Q : forall x, P x -> Prop) : Type :=
 | mk_dep_data : forall x (pf : P x), Q x pf -> dep_data X P Q.

Lemma in_pf_map_sig {X Y} `{Discrete Y} {xs : list X} {f : forall x, In x xs -> Y} :
  forall {y}, In y (pf_map xs f) ->
  dep_data X (fun x => In x xs) (fun x pf => f x pf = y /\ In x xs).
Proof.
  induction xs; intros y HIn.
  - destruct HIn.
  - simpl in HIn.
    destruct (eq_dec (f a (or_introl eq_refl)) y).
    + unshelve econstructor; [exact a| now left |].
      split; auto.
      now left.
    + assert (In y (pf_map xs (fun x'
        HIn => f x' (or_intror HIn)))) as G by tauto.
      destruct (IHxs _ _ G) as [x pf [Hpf1 Hpf2]].
      unshelve econstructor; [exact x| right; exact pf |].
      split; auto.
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

Lemma app_l_cancel : forall pre suff suff',
  (pre ++ suff = pre ++ suff') -> suff = suff'.
Proof.
  induction pre; intros suff suff'.
  - simpl; auto.
  - simpl; intro pf.
    apply IHpre.
    now inversion pf.
Qed.

Lemma BG_State_ext {G} (s s' : BG_State G) :
  to_play s = to_play s' ->
  bear s = bear s' ->
  hunters s = hunters s' ->
  s = s'.
Proof.
  intros pf1 pf2 pf3.
  destruct s, s'; simpl in *.
  destruct pf1, pf2, pf3.
  f_equal; apply proof_irrelevance.
Qed.

Definition strLP : string := "(".
Definition strComma : string := ",".
Definition strRP : string := ")".

Lemma NoDup_sublists {X} : forall (xs : list X) n,
  NoDup xs -> forall ys, In ys (sublists n xs) -> NoDup ys.
Proof.
  intro xs.
  induction xs as [|x xs']; intros n pf.
  - intros ys Hys; simpl in Hys.
    destruct n.
    + destruct Hys as [[]|[]]; auto.
    + destruct Hys.
  - intros ys Hys; simpl in Hys.
    destruct n.
    + destruct Hys as [[]|[]]; constructor.
    + rewrite in_app_iff in Hys; destruct Hys as [Hys|].
      * rewrite in_map_iff in Hys.
        destruct Hys as [l [[] Hl]].
        constructor.
        -- intro Hx.
           pose proof (sublist_In_trans _ _ _ _ Hx Hl).
           now inversion pf.
        -- inversion pf.
           now apply (IHxs' n).
      * inversion pf.
        now apply (IHxs' (S n)).
Qed.

Definition all_BG_States (pl : Player) {G} : list (BG_State G).
Proof.
  refine (List.concat (List.map _ enum)).
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
    apply Vert_NoDup.
  - unfold hunter_lists in HIn.
    eapply sublist_length; eauto.
  - eapply NoDup_sublists; [|exact HIn].
    apply NoDup_filter.
    apply Vert_NoDup.
  - intro pf.
    pose proof (sublist_In_trans _ _ _ _ pf HIn) as pf'.
    rewrite filter_In in pf'.
    unfold eqb in pf'.
    destruct (eq_dec b b).
    + destruct pf'; discriminate.
    + apply n; reflexivity.
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

Global Instance BG_State_Disc {G}
  : Discrete (BG_State G).
Proof.
  constructor; intros s s'.
  destruct (eq_dec (to_play s) (to_play s'));
    [|right; congruence].
  destruct (eq_dec (bear s) (bear s'));
    [|right; congruence].
  destruct (eq_dec (hunters s) (hunters s'));
    [|right; congruence].
  left.
  destruct s, s'; simpl in *.
  destruct e,e0,e1.
  f_equal; apply proof_irrelevance.
Defined.

Lemma all_BG_States_correct {G} : forall pl (s : BG_State G),
  to_play s = pl -> In s (all_BG_States pl).
Proof.
  intros.
  unfold all_BG_States.
  rewrite in_concat.
  eexists.
  rewrite in_map_iff.
  split.
  - exists (bear s).
    split; [reflexivity|].
    apply enum_correct.
  - rewrite in_pf_map_iff.
    exists (hunters s).
    unshelve eexists.
    + apply in_sublists.
      * apply NoDup_filter.
        apply G.
      * apply sorted_filter.
        apply enum_sorted.
        apply G.
      * apply s.
      * apply s.
      * intros y Hy.
        rewrite filter_In.
        split; [apply enum_correct|].
        unfold eqb.
        destruct eq_dec as [pf|]; [|reflexivity].
        elim (bear_not_hunter s); congruence.
      * apply s.
    + split.
      * apply BG_State_ext; simpl.
        -- now symmetry.
        -- reflexivity.
        -- reflexivity.
      * apply in_sublists.
        -- apply NoDup_filter.
           apply G.
        -- apply sorted_filter.
           apply enum_sorted.
           apply G.
        -- apply s.
        -- apply s.
        -- intros y Hy.
           rewrite filter_In.
           split; [apply enum_correct|].
           unfold eqb.
           destruct eq_dec as [pf|]; [|reflexivity].
           elim (bear_not_hunter s); congruence.
        -- apply s.
Qed.

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
  - intro s.
    rewrite in_app_iff.
    destruct (to_play s) eqn:s_play.
    + left.
      now apply all_BG_States_correct.
    + right.
      now apply all_BG_States_correct.
  - intros s [] pf; simpl in pf.
    + simpl.
      unfold atomic_res.
      rewrite filter_In in pf.
      destruct (enum_moves s).
      * destruct pf as [pf _].
        unfold all_BG_States in pf.
        rewrite in_concat in pf.
        destruct pf as [l [Hl1 Hl2]].
        rewrite in_map_iff in Hl1.
        destruct Hl1 as [v [Hv _]].
        rewrite <- Hv in Hl2; clear Hv.
        rewrite in_pf_map_iff in Hl2.
        destruct Hl2 as [l' [pf [Hl' _]]].
        now rewrite <- Hl'.
      * now destruct pf.
    + destruct pf.
  - intros s pl s_res; simpl.
    destruct pl.
    + rewrite filter_In; split.
      * apply all_BG_States_correct.
        simpl in s_res.
        unfold atomic_res in s_res.
        destruct (enum_moves s); [|discriminate].
        destruct (to_play s); [discriminate|reflexivity].
      * simpl in s_res.
        unfold atomic_res in s_res.
        destruct (enum_moves s); [|discriminate].
        destruct (to_play s); auto.
    + simpl in *.
      unfold atomic_res in s_res.
      destruct (enum_moves s); [|discriminate].
      destruct (to_play s); discriminate.
Defined.

Lemma remove_insert {X} `{Ord X, Discrete X} xs (x : X) :
  (~ In x xs) ->
  remove x (insert x xs) = xs.
Proof.
  induction xs as [|y ys]; intro HnIn; simpl.
  - destruct eq_dec; [reflexivity|contradiction].
  - destruct (ord_le_dec x y).
    + simpl; destruct eq_dec; [|contradiction].
      destruct (eq_dec x y).
      * elim HnIn; now left.
      * rewrite no_remove_id; [reflexivity|].
        simpl in HnIn; tauto.
    + simpl; destruct eq_dec.
      * elim HnIn; now left.
      * rewrite IHys; [reflexivity|].
        simpl in HnIn; tauto.
Qed.

Lemma insert_cons {X} `{Ord X} : forall (x : X) xs,
  sorted (x :: xs) -> insert x xs = x :: xs.
Proof.
  intros x xs xs_sort.
  induction xs as [|y ys].
  - reflexivity.
  - simpl.
    inversion xs_sort as [|? ? _ xs_bound Heq].
    destruct ord_le_dec; [reflexivity|].
    assert (x = y) as pf.
    { apply ord_le_antisym; auto.
      rewrite Forall_forall in xs_bound.
      apply xs_bound; now left.
    }
    rewrite pf in *.
    rewrite IHys; auto.
    now inversion xs_sort.
Qed.

Lemma insert_remove {X} `{Ord X, Discrete X} xs (x : X) :
  sorted xs -> NoDup xs -> In x xs ->
  insert x (remove x xs) = xs.
Proof.
  induction xs as [|y ys]; intros xs_sort xs_nd HIn.
  - destruct HIn.
  - destruct HIn as [Heq|HIn].
    + simpl.
      destruct (eq_dec x y); [|congruence].
      rewrite no_remove_id.
      * rewrite e.
        now apply insert_cons.
      * rewrite e in *.
        now inversion xs_nd.
    + simpl.
      destruct (eq_dec x y).
      * rewrite e in *.
        now inversion xs_nd.
      * simpl.
        destruct ord_le_dec.
        -- elim n.
           apply ord_le_antisym; auto.
           inversion xs_sort as [|? ? ys_sort ys_bound].
           rewrite Forall_forall in ys_bound.
           now apply ys_bound.
        -- rewrite IHys; auto.
           ++ now inversion xs_sort.
           ++ now inversion xs_nd.
Qed.

Lemma insertion_sort_idem {X} `{Ord X} xs :
  sorted xs -> insertion_sort xs = xs.
Proof.
  induction xs; intros xs_sort.
  - reflexivity.
  - simpl.
    rewrite IHxs; [|now inversion xs_sort].
    now apply insert_cons.
Qed.

Lemma remove_sorted {X} `{Ord X, Discrete X} xs :
  sorted xs -> forall x, sorted (remove x xs).
Proof.
  induction xs as [|y ys]; intros xs_sort x.
  - constructor.
  - simpl.
    destruct (eq_dec x y).
    + apply IHys; now inversion xs_sort.
    + constructor.
      * apply IHys; now inversion xs_sort.
      * inversion xs_sort as [|? ? ys_sort ys_bound].
        rewrite Forall_forall in *.
        intros z Hz.
        apply ys_bound.
        now rewrite In_remove_iff in Hz.
Qed.

Global Instance Reversible_BearGame {G} : Reversible (BearGame G).
Proof.
  unshelve econstructor.
  - intro s.
    destruct (to_play s) eqn:s_play.
    + refine (pf_map
        (filter (fun b => negb (in_decb b (hunters s)))
          (predecessors (bear s)))
        (fun b pf => {|
          to_play := Black;
          bear := b;
          hunters := hunters s;
          hunters_sort := hunters_sort G s;
          hunters_3 := hunters_3 G s;
          hunters_distinct := hunters_distinct s;
          bear_not_hunter := _
        |})).
      rewrite filter_In in pf.
      destruct pf as [_ pf].
      unfold in_decb in pf.
      destruct in_dec; [discriminate|auto].
    + refine (List.concat (pf_map (hunters s) (fun h pf_h => _))).
      refine (pf_map
        (filter (fun h' => orb (negb (in_decb h' (bear s :: hunters s))) (eqb h' h))
          (predecessors h))
        (fun h' pf => {|
          to_play := White;
          bear := bear s;
          hunters := insertion_sort (h' :: (remove h (hunters s)));
          hunters_sort := _;
          hunters_3 := _;
          hunters_distinct := _;
          bear_not_hunter := _
        |})).
      * apply insertion_sort_sorts.
      * rewrite insertion_sort_length.
        simpl; f_equal.
        erewrite remove_length; [reflexivity | | |].
        -- apply s.
        -- exact pf_h.
        -- apply s.
      * apply insertion_sort_NoDup.
        constructor.
        -- rewrite In_remove_iff.
           intros [Hh'h Hh'].
           rewrite filter_In in pf.
           destruct pf as [_ pf].
           unfold in_decb in pf.
           destruct in_dec.
           ++ simpl in pf.
              unfold eqb in pf.
              destruct eq_dec; [contradiction|discriminate].
           ++ elim n; now right.
        -- apply NoDup_remove.
           apply s.
      * rewrite insertion_sort_In.
        rewrite filter_In in pf.
        destruct pf as [pf1 pf2].
        rewrite Bool.orb_true_iff in pf2.
        destruct pf2 as [pf2|pf2].
        -- rewrite Bool.negb_true_iff in pf2.
           unfold in_decb in pf2.
           destruct in_dec; [discriminate|].
           intros [pf|pf].
           ++ apply n; now left.
           ++ rewrite In_remove_iff in pf.
              now apply s.
        -- unfold eqb in pf2.
           destruct eq_dec; [|discriminate].
           destruct e.
           intros [Hbear|Hbear].
           ++ rewrite Hbear in pf_h.
              now apply s.
           ++ rewrite In_remove_iff in Hbear.
              now apply s.
  - intros s s' pf.
    simpl in pf.
    destruct (to_play s') eqn:s'_play.
    + destruct (in_pf_map_sig pf) as [v pf' [Hv1 Hv2]].
      unshelve eexists.
      * apply BearMove.
        -- now rewrite <- Hv1.
        -- unshelve eexists.
           ++ exact (bear s').
           ++ rewrite <- Hv1; simpl.
              rewrite filter_In in Hv2.
              destruct Hv2 as [Hv3 _].
              now rewrite <- predecessors_correct in Hv3.
           ++ rewrite <- Hv1; simpl.
              apply s'.
      * apply BG_State_ext; simpl.
        -- auto.
        -- reflexivity.
        -- now rewrite <- Hv1.
    + destruct (in_concat_sig _ _ pf)
        as [l [Hl1 Hl2]]; clear pf.
      destruct (in_pf_map_sig Hl1) as [v pf [Hv1 Hv2]]; clear Hl1.
      rewrite <- Hv1 in Hl2; clear Hv1.
      destruct (in_pf_map_sig Hl2) as [v' pf' [Hv'1 Hv'2]]; clear Hl2.
      unshelve eexists.
      * apply HunterMove.
        -- now rewrite <- Hv'1.
        -- unshelve eexists.
           ++ exact v'.
           ++ exact v.
           ++ rewrite <- Hv'1; simpl.
              rewrite insert_In; now left.
           ++ rewrite filter_In in Hv'2.
              destruct Hv'2 as [Hv'3 _].
              now rewrite predecessors_correct.
           ++ rewrite <- Hv'1; simpl.
              intro Heq.
              apply s'; congruence.
           ++ rewrite <- Hv'1; simpl.
              rewrite insert_In.
              intros [Hv'3|Hv'3]; [auto|].
              rewrite insertion_sort_In in Hv'3.
              now rewrite In_remove_iff in Hv'3.
      * apply BG_State_ext.
        -- simpl; congruence.
        -- simpl.
           now rewrite <- Hv'1.
        -- simpl.
           rewrite <- Hv'1; simpl; clear Hv'1.
           rewrite remove_insert.
           ++ rewrite insertion_sort_idem; [|apply insertion_sort_sorts].
              rewrite insertion_sort_idem.
              ** apply insert_remove; [apply s'|apply s'|auto].
              ** apply remove_sorted; apply s'.
           ++ rewrite insertion_sort_In.
              rewrite In_remove_iff.
              rewrite filter_In in Hv'2.
              destruct Hv'2 as [_ Hv'].
              unfold in_decb in Hv'.
              destruct in_dec as [HIn|HnIn].
              ** simpl in Hv'.
                 unfold eqb in Hv'.
                 destruct eq_dec; [tauto|discriminate].
              ** simpl in HnIn; tauto.
  - intros.
    simpl.
    destruct (to_play (exec_move m)) eqn:m_play.
    + rewrite in_pf_map_iff.
      exists (bear s).
      unfold exec_move in m_play.
      destruct m; [|discriminate].
      unshelve eexists.
      * rewrite filter_In; split.
        -- simpl; rewrite <- predecessors_correct.
           apply b.
        -- simpl; unfold in_decb.
           destruct in_dec; [|reflexivity].
           elim (bear_not_hunter s i).
      * split.
        -- apply BG_State_ext.
           ++ simpl; auto.
           ++ reflexivity.
           ++ reflexivity.
        -- rewrite filter_In.
           split.
           ++ simpl; rewrite <- predecessors_correct.
              apply b.
           ++ simpl; unfold in_decb.
              destruct in_dec; [|reflexivity].
              elim (bear_not_hunter s i).
    + simpl.
      unfold exec_move in m_play.
      destruct m; [discriminate|].
      clear m_play.
      rewrite in_concat.
      eexists.
      rewrite in_pf_map_iff; split.
      * exists (h_dest h).
        unshelve eexists.
        -- simpl; rewrite insert_In.
           now left.
        -- split; [reflexivity|].
           simpl; rewrite insert_In.
           now left.
      * rewrite in_pf_map_iff.
        exists (h_orig h).
        unshelve eexists.
        -- rewrite filter_In.
           split.
           ++ rewrite <- predecessors_correct.
              apply h.
           ++ rewrite Bool.orb_true_iff.
              unfold in_decb.
              destruct in_dec as [pf|pf]; [|now left].
              right.
              destruct pf as [pf|pf].
              ** simpl in pf.
                 elim (bear_not_hunter s).
                 rewrite pf; apply h.
              ** simpl in pf.
                 rewrite insert_In in pf.
                 unfold eqb.
                 destruct eq_dec as [|pf']; [reflexivity|].
                 destruct pf as [|pf]; [congruence|].
                 rewrite insertion_sort_In in pf.
                 rewrite In_remove_iff in pf.
                 destruct pf; contradiction.
        -- simpl; split.
           ++ apply BG_State_ext.
              ** simpl; auto.
              ** reflexivity.
              ** simpl.
                 rewrite remove_insert.
                 --- rewrite insertion_sort_idem; [|apply insertion_sort_sorts].
                     rewrite insertion_sort_idem.
                     +++ apply insert_remove; [apply s|apply s|apply h].
                     +++ apply remove_sorted; apply s.
                 --- rewrite insertion_sort_In.
                     rewrite In_remove_iff.
                     intros [pf1 pf2].
                     apply pf1.
                     now apply h_dest_not_diff_hunter.
           ++ rewrite filter_In.
              split.
              ** rewrite <- predecessors_correct.
                 apply h.
              ** rewrite Bool.orb_true_iff.
              unfold in_decb.
              destruct in_dec as [pf|pf]; [|now left].
              right.
              destruct pf as [pf|pf].
              --- simpl in pf.
                  elim (bear_not_hunter s).
                  rewrite pf; apply h.
              --- simpl in pf.
                  rewrite insert_In in pf.
                  unfold eqb.
                  destruct eq_dec as [|pf']; [reflexivity|].
                  destruct pf as [|pf]; [congruence|].
                  rewrite insertion_sort_In in pf.
                  rewrite In_remove_iff in pf.
                  destruct pf; contradiction.
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

Definition Bear_TB (G : Graph) `{hsh : IntHash (GameState (BearGame G))}
  : OCamlTablebase (BearGame G) := certified_TB.
