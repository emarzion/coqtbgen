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

Definition str1 : string := "1".
Definition str2 : string := "2".
Definition str3 : string := "3".
Definition str4 : string := "4".
Definition str5 : string := "5".
Definition str6 : string := "6".
Definition str7 : string := "7".
Definition str8 : string := "8".

Definition show_spoke (s : Spoke) : string := (
  match s with
  | S1 => str1
  | S2 => str2
  | S3 => str3
  | S4 => str4
  | S5 => str5
  | S6 => str6
  | S7 => str7
  | S8 => str8
  end)%string.

Inductive SpokeLoc :=
  Mid | L | R.

Definition strM : string := "M".
Definition strL : string := "L".
Definition strR : string := "R".

Definition show_loc (l : SpokeLoc) : string := (
  match l with
  | Mid => strM
  | L => strL
  | R => strR
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

Definition strC : string := "C".
Definition str1L : string := "1L".
Definition str1M : string := "1M".
Definition str1R : string := "1R".
Definition str2L : string := "2L".
Definition str2M : string := "2M".
Definition str2R : string := "2R".
Definition str3L : string := "3L".
Definition str3M : string := "3M".
Definition str3R : string := "3R".
Definition str4L : string := "4L".
Definition str4M : string := "4M".
Definition str4R : string := "4R".
Definition str5L : string := "5L".
Definition str5M : string := "5M".
Definition str5R : string := "5R".
Definition str6L : string := "6L".
Definition str6M : string := "6M".
Definition str6R : string := "6R".
Definition str7L : string := "7L".
Definition str7M : string := "7M".
Definition str7R : string := "7R".
Definition str8L : string := "8L".
Definition str8M : string := "8M".
Definition str8R : string := "8R".

Definition show_RWVert (v : RWVert) : string :=
  match v with
  | Center => strC
  | SpokeVert S1 L => str1L
  | SpokeVert S1 Mid => str1M
  | SpokeVert S1 R => str1R
  | SpokeVert S2 L => str2L
  | SpokeVert S2 Mid => str2M
  | SpokeVert S2 R => str2R
  | SpokeVert S3 L => str3L
  | SpokeVert S3 Mid => str3M
  | SpokeVert S3 R => str3R
  | SpokeVert S4 L => str4L
  | SpokeVert S4 Mid => str4M
  | SpokeVert S4 R => str4R
  | SpokeVert S5 L => str5L
  | SpokeVert S5 Mid => str5M
  | SpokeVert S5 R => str5R
  | SpokeVert S6 L => str6L
  | SpokeVert S6 Mid => str6M
  | SpokeVert S6 R => str6R
  | SpokeVert S7 L => str7L
  | SpokeVert S7 Mid => str7M
  | SpokeVert S7 R => str7R
  | SpokeVert S8 L => str8L
  | SpokeVert S8 Mid => str8M
  | SpokeVert S8 R => str8R
  end.

Global Instance Show_RWVert : Show RWVert. refine {|
  show := show_RWVert;
  show_inj := _;
  |}.
Proof.
  - intros v v'.
    destruct v as [|[] []];
    destruct v' as [|[] []]; try reflexivity.
    all: discriminate.
Defined.

Global Instance RWVert_Nonnil : Nonnil RWVert.
Proof.
  constructor.
  destruct x; simpl.
  - discriminate.
  - destruct s; destruct l; discriminate.
Qed.

Global Instance RWVert_CommaFree : CommaFree RWVert.
Proof.
  constructor.
  destruct x.
  - simpl; repeat split; discriminate.
  - unfold show.
    unfold Show_RWVert.
    destruct s, l; simpl;
    repeat split; discriminate.
Qed.

Global Instance RWVert_Semicolon : SemicolonFree RWVert.
Proof.
  constructor.
  destruct x.
  - simpl; repeat split; discriminate.
  - unfold show.
    unfold Show_RWVert.
    destruct s, l; simpl;
    repeat split; discriminate.
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
