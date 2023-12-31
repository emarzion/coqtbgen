Require Import List.
Import ListNotations.

Require Import PrimInt63.
Require Import Uint63.

Require Import Games.Util.IntHash.
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

Inductive SpokeLoc :=
  Mid | L | R.

Definition list_locs :=
  [Mid;L;R].

Inductive RWVert :=
  | Center
  | SpokeVert (s : Spoke) (l : SpokeLoc).

Definition hash_RWVert (v : RWVert) : int :=
  match v with
  | Center => 0
  | SpokeVert S1 L => 1
  | SpokeVert S1 Mid => 2
  | SpokeVert S1 R => 3
  | SpokeVert S2 L => 4
  | SpokeVert S2 Mid => 5
  | SpokeVert S2 R => 6
  | SpokeVert S3 L => 7
  | SpokeVert S3 Mid => 8
  | SpokeVert S3 R => 9
  | SpokeVert S4 L => 10
  | SpokeVert S4 Mid => 11
  | SpokeVert S4 R => 12
  | SpokeVert S5 L => 13
  | SpokeVert S5 Mid => 14
  | SpokeVert S5 R => 15
  | SpokeVert S6 L => 16
  | SpokeVert S6 Mid => 17
  | SpokeVert S6 R => 18
  | SpokeVert S7 L => 19
  | SpokeVert S7 Mid => 20
  | SpokeVert S7 R => 21
  | SpokeVert S8 L => 22
  | SpokeVert S8 Mid => 23
  | SpokeVert S8 R => 24
  end.

Lemma hash_RWVert_inj : forall v v',
  hash_RWVert v = hash_RWVert v' -> v = v'.
Proof.
  intros [|[] []] [|[] []]; simpl; intro pf; try reflexivity; 
  discriminate (f_equal to_Z pf).
Qed.

Global Instance IntHash_RWVert : IntHash RWVert := {|
  hash := hash_RWVert;
  hash_inj := hash_RWVert_inj;
  |}.

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

Global Instance IntHash_RWV : IntHash (Vert RomanWheel) :=
  IntHash_RWVert.

Definition add_vert (v : Vert RomanWheel) (i : int) : int :=
  (hash v) lor (i << 5).

Definition add_player (p : Player.Player) (i : int) : int :=
  match p with
  | Player.White => i << 1
  | Player.Black => 1 lor (i << 1)
  end.

Definition get_player (i : int) : Player.Player * int :=
  match is_even i with
  | true => (Player.White, i >> 1)
  | false => (Player.Black, i >> 1)
  end%uint63.

Definition hash_RW_State (s : BG_State RomanWheel) : int :=
  match s with
  | Build_BG_State _ p b hs _ _ _ _ =>
      add_player p (add_vert b (fold_right add_vert 0%uint63 hs))
  end.

Lemma hash_RW_State_inj : forall s s',
  hash_RW_State s = hash_RW_State s' -> s = s'.
Proof.
Admitted.

Global Instance IntHash_RW : IntHash (Game.GameState (BearGame RomanWheel)) := {|
  hash := hash_RW_State;
  hash_inj := hash_RW_State_inj;
  |}.

Definition RW_TB := Bear_TB RomanWheel.
