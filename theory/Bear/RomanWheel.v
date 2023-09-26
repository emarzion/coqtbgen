Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.

Require Import Games.Util.Show.
Require Import Games.Bear.Graph.
Require Import Games.Bear.BearGame.
Require Import Games.Game.TB.

Inductive Spoke :=
  S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8.

Definition clockwise (s : Spoke) : Spoke :=
  match s with
  | S1 => S2
  | S2 => S3
  | S3 => S4
  | S4 => S5
  | S5 => S6
  | S6 => S7
  | S7 => S8
  | S8 => S1
  end.

Definition c_clockwise (s : Spoke) : Spoke :=
  match s with
  | S1 => S8
  | S2 => S1
  | S3 => S2
  | S4 => S3
  | S5 => S4
  | S6 => S5
  | S7 => S6
  | S8 => S7
  end.

Definition list_spokes :=
  [S1;S2;S3;S4;S5;S6;S7;S8].

Definition show_spoke (s : Spoke) : string := (
  match s with
  | S1 => "1"
  | S2 => "2"
  | S3 => "3"
  | S4 => "4"
  | S5 => "5"
  | S6 => "6"
  | S7 => "7"
  | S8 => "8"
  end)%string.

Inductive SpokeLoc :=
  Mid | L | R.

Definition show_loc (l : SpokeLoc) : string := (
  match l with
  | Mid => "M"
  | L => "L"
  | R => "R"
  end)%string.

Definition list_locs :=
  [Mid;L;R].

Inductive RWVert :=
  | Center
  | SpokeVert (s : Spoke) (l : SpokeLoc).

Lemma show_loc_inj : forall l l',
  show_loc l = show_loc l' -> l = l'.
Proof.
  intros l l'.
  destruct l, l'; simpl;
  (discriminate || reflexivity).
Qed.

Lemma spoke_loc : forall s s' l l',
  show_spoke s ++ show_loc l =
  show_spoke s' ++ show_loc l' ->
  s = s' /\ l = l'.
Proof.
  intros s s' l l' pf.
  destruct s, s'; try inversion pf;
  (split; [reflexivity|now apply show_loc_inj]).
Qed.

Global Instance Show_RWVert : Show RWVert.
Proof.
  unshelve econstructor.
  - intro v.
    destruct v eqn:?.
    + exact "C"%string.
    + exact (show_spoke s ++ show_loc l)%string.
  - intros v v'.
    destruct v as [|s l];
    destruct v' as [|s' l'].
    + intro; reflexivity.
    + intro pf; destruct s'; now inversion pf.
    + intro pf; destruct s; now inversion pf.
    + cbv zeta match beta.
      intro pf.
      cut (s = s' /\ l = l').
      { intros []; congruence. }
      now apply spoke_loc.
Defined.

Global Instance RWVert_Nonnil : Nonnil RWVert.
Proof.
  constructor.
  destruct x; simpl.
  - discriminate.
  - destruct s; discriminate.
Qed.

Global Instance RWVert_CommaFree : CommaFree RWVert.
Proof.
  constructor.
  destruct x.
  - simpl; repeat split; discriminate.
  - unfold show.
    unfold Show_RWVert.
    repeat rewrite char_free_app.
    split.
    + destruct s; simpl; repeat split; discriminate.
    + destruct l; simpl; repeat split; discriminate.
Qed.

Global Instance RWVert_Semicolon : SemicolonFree RWVert.
Proof.
  constructor.
  destruct x.
  - simpl; repeat split; discriminate.
  - unfold show.
    unfold Show_RWVert.
    repeat rewrite char_free_app.
    split.
    + destruct s; simpl; repeat split; discriminate.
    + destruct l; simpl; repeat split; discriminate.
Qed.

Lemma NoDup_list_locs : NoDup list_locs.
Proof.
  unfold list_locs.
  constructor; simpl.
  - intros [|[|]]; auto; discriminate.
  - constructor; simpl.
    + intros [|]; auto; discriminate.
    + constructor; simpl.
      * tauto.
      * constructor.
Qed.

Lemma all_neq_not_In {X} (x : X) (xs : list X) :
  List.fold_right and True (List.map (fun y => x <> y) xs) ->
  ~ In x xs.
Proof.
  induction xs; simpl; firstorder.
Qed.

(* TODO: use tactics *)
Lemma NoDup_list_spokes : NoDup list_spokes.
Proof.
  unfold list_spokes.
  constructor.
  - apply all_neq_not_In; simpl.
    repeat split; discriminate.
  - constructor.
    + apply all_neq_not_In; simpl.
      repeat split; discriminate.
    + constructor.
      * apply all_neq_not_In; simpl.
        repeat split; discriminate.
      * constructor.
        -- apply all_neq_not_In; simpl.
           repeat split; discriminate.
        -- constructor.
           ++ apply all_neq_not_In; simpl.
              repeat split; discriminate.
           ++ constructor.
              ** apply all_neq_not_In; simpl.
                 repeat split; discriminate.
              ** constructor.
                 --- apply all_neq_not_In; simpl.
                     repeat split; discriminate.
                 --- constructor.
                     +++ apply all_neq_not_In; simpl.
                         repeat split.
                     +++ constructor.
Qed.

Lemma NoDup_concat {X} (xss : list (list X)) :
  NoDup xss ->
  (forall xs, In xs xss -> NoDup xs) ->
  (forall x xs xs', In xs xss -> In xs' xss ->
    In x xs -> In x xs' -> xs = xs') ->
  NoDup (List.concat xss).
Proof.
  induction xss; intros nd nds disj.
  - constructor.
  - simpl.
    apply NoDup_app.
    + apply nds; now left.
    + apply IHxss.
      * now inversion nd.
      * intros; apply nds.
        now right.
      * intros; eapply disj.
        -- now right.
        -- now right.
        -- eauto.
        -- auto.
    + intros x Hx1 Hx2.
      rewrite in_concat in Hx2.
      destruct Hx2 as [l [Hl1 Hl2]].
      rewrite <- (disj x a l) in Hl1; simpl; auto.
      now inversion nd.
Qed.

Definition RomanWheel : Graph.
Proof.
  unshelve refine {|
    Vert := RWVert;
    Vert_disc := _;
    Vert_enum := _;
    Vert_NoDup := _;
    successors := fun v =>
      match v with
      | Center => map (fun s => SpokeVert s Mid) list_spokes
      | SpokeVert s Mid => [Center; SpokeVert s L; SpokeVert s R]
      | SpokeVert s L => [SpokeVert s R; SpokeVert s Mid; SpokeVert (c_clockwise s) R]
      | SpokeVert s R => [SpokeVert s L; SpokeVert s Mid; SpokeVert (clockwise s) L]
      end
  |}.
  - refine {|
      enum := Center :: List.concat
        (List.map (fun s => List.map (SpokeVert s) list_locs) list_spokes);
      enum_correct := _
    |}.
    intros [|s l].
    + now left.
    + right.
      rewrite in_concat.
      exists (map (SpokeVert s) list_locs).
      split.
      * rewrite in_map_iff.
        exists s.
        split; [reflexivity|].
        unfold list_spokes.
        destruct s; simpl; tauto.
      * apply in_map.
        unfold list_locs.
        destruct l; simpl; tauto.
  - unfold enum.
    constructor.
    + rewrite in_concat.
      intros [vs pf].
      rewrite in_map_iff in pf.
      destruct pf as [[s [[] Hs]] pf].
      rewrite in_map_iff in pf.
      destruct pf as [l [Hl _]]; discriminate.
    + apply NoDup_concat.
      * apply FinFun.Injective_map_NoDup.
        -- intros s s' pf.
           now inversion pf.
        -- apply NoDup_list_spokes.
      * intros xs Hxs.
        rewrite in_map_iff in Hxs.
        destruct Hxs as [s [[] Hs]].
        apply FinFun.Injective_map_NoDup.
        -- intros l l' pf.
           now inversion pf.
        -- apply NoDup_list_locs.
      * intros v vs vs' Hvs Hvs' Hvvs Hvvs'.
        rewrite in_map_iff in Hvs.
        rewrite in_map_iff in Hvs'.
        destruct Hvs as [s [Heq Hs]].
        destruct Heq.
        destruct Hvs' as [s' [Heq Hs']].
        destruct Heq.
        rewrite in_map_iff in Hvvs.
        rewrite in_map_iff in Hvvs'.
        destruct Hvvs as [l [Heq _]].
        destruct Heq.
        destruct Hvvs' as [l' [Heq _]].
        now inversion Heq.
Defined.

Global Instance Show_RWV : Show (Vert RomanWheel) :=
  Show_RWVert.

Definition RW_TB := Bear_TB RomanWheel.
