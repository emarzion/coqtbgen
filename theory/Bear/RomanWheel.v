Require Import List.
Import ListNotations.

Require Import PrimInt63.
Require Import Uint63.
Require Import ZArith.
Require Import Lia.

Require Import TBGen.Util.IntHash.
Require Import TBGen.Bear.Graph.
Require Import TBGen.Bear.BearGame.
Require Import TBGen.TB.TB.

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

Definition unhash_RWVert (z : Z) : option RWVert := (
  match z with
  | 0 => Some Center
  | 1 => Some (SpokeVert S1 L)
  | 2 => Some (SpokeVert S1 Mid)
  | 3 => Some (SpokeVert S1 R)
  | 4 => Some (SpokeVert S2 L)
  | 5 => Some (SpokeVert S2 Mid)
  | 6 => Some (SpokeVert S2 R)
  | 7 => Some (SpokeVert S3 L)
  | 8 => Some (SpokeVert S3 Mid)
  | 9 => Some (SpokeVert S3 R)
  | 10 => Some (SpokeVert S4 L)
  | 11 => Some (SpokeVert S4 Mid)
  | 12 => Some (SpokeVert S4 R)
  | 13 => Some (SpokeVert S5 L)
  | 14 => Some (SpokeVert S5 Mid)
  | 15 => Some (SpokeVert S5 R)
  | 16 => Some (SpokeVert S6 L)
  | 17 => Some (SpokeVert S6 Mid)
  | 18 => Some (SpokeVert S6 R)
  | 19 => Some (SpokeVert S7 L)
  | 20 => Some (SpokeVert S7 Mid)
  | 21 => Some (SpokeVert S7 R)
  | 22 => Some (SpokeVert S8 L)
  | 23 => Some (SpokeVert S8 Mid)
  | 24 => Some (SpokeVert S8 R)
  | _ => None
  end)%Z.

Lemma unhash_hash : forall v,
  unhash_RWVert (to_Z (hash_RWVert v)) = Some v.
Proof.
  destruct v as [|[] []]; reflexivity.
Qed.

Lemma hash_RWVert_inj : forall v v',
  hash_RWVert v = hash_RWVert v' -> v = v'.
Proof.
  intros v v' pf1.
  pose proof (unhash_hash v) as pf2.
  rewrite pf1 in pf2.
  rewrite unhash_hash in pf2.
  congruence.
Qed.

Global Instance IntHash_RWVert : IntHash RWVert := {|
  hash := hash_RWVert;
  hash_inj := hash_RWVert_inj;
  |}.

Lemma hash_small : forall v,
  (to_Z (hash v) < 2 ^ 5)%Z.
Proof.
  intros [|[][ ]]; simpl; reflexivity.
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

Global Instance IntHash_RWV : IntHash (Vert RomanWheel) :=
  IntHash_RWVert.

Definition add_vert (v : Vert RomanWheel) (i : int) : int :=
  (hash v) lor (i << 5).

Definition lsb (i : Z) (n : Z) : Z :=
  i mod (2 ^ n).

Fixpoint pow2 n : positive :=
  match n with
  | 0 => xH
  | S m => xO (pow2 m)
  end.

Lemma pow2_correct : forall n,
  2 ^ n = Pos.to_nat (pow2 n).
Proof.
  induction n.
  - reflexivity.
  - rewrite Nat.pow_succ_r'.
    simpl pow2.
    rewrite Pos2Nat.inj_xO.
    lia.
Qed.

Lemma pow_pow2 : forall p,
  (2 ^ p)%positive = pow2 (Pos.to_nat p).
Proof.
  intro p.
  apply Pos2Nat.inj.
  rewrite Pos2Nat.inj_pow.
  apply pow2_correct.
Qed.

Lemma Pos_lor_add : forall n x y, (
  x < pow2 n ->
  Pos.lor x (pow2 n * y) = x + (pow2 n * y))%positive.
Proof.
  induction n.
  - simpl; lia.
  - simpl; intros x y x_small.
    destruct x; simpl in *.
    + f_equal.
      apply IHn.
      unfold Pos.lt in x_small.
      unfold Pos.compare in x_small.
      simpl in x_small.
      rewrite Pos.compare_cont_Gt_Lt in x_small.
      assumption.
    + f_equal.
      apply IHn.
      assumption.
    + f_equal.
Qed.

Lemma lor_add : forall n x y, (
  0 <= n ->
  0 <= x ->
  0 <= y ->
  x < 2 ^ n ->
  Z.lor x (y * 2 ^ n) = x + (y * 2 ^ n))%Z.
Proof.
  intros.
  rewrite Z.mul_comm.
  destruct x.
  - rewrite Z.lor_0_l.
    lia.
  - destruct y; try lia.
    + rewrite Z.mul_0_r.
      rewrite Z.lor_0_r; lia.
    + destruct n; try lia.
      rewrite <- Pos2Z.inj_pow in *.
      rewrite <- Pos2Z.inj_mul.
      simpl; f_equal.
      rewrite pow_pow2 in *.
      apply Pos_lor_add; assumption.
  - lia.
Qed.

Lemma Pos_lor_small : forall n x y, (
  x < pow2 n ->
  y < pow2 n ->
  Pos.lor x y < pow2 n)%positive.
Proof.
  induction n; intros; simpl in *.
  - lia.
  - unfold Pos.lt in *.
    unfold Pos.compare in *.
    destruct x, y; simpl in *.
    + rewrite Pos.compare_cont_Gt_Lt in *.
      apply IHn; assumption.
    + rewrite Pos.compare_cont_Gt_Lt in *.
      apply IHn; assumption.
    + assumption.
    + rewrite Pos.compare_cont_Gt_Lt in *.
      apply IHn; assumption.
    + apply IHn; assumption.
    + now rewrite Pos.compare_cont_Gt_Lt.
    + assumption.
    + now rewrite Pos.compare_cont_Gt_Lt.
    + reflexivity.
Qed.

Lemma lor_small : forall x y d, (
  0 <= d ->
  0 <= x ->
  0 <= y ->
  x < 2 ^ d ->
  y < 2 ^ d ->
  Z.lor x y < 2 ^ d)%Z.
Proof.
  intros x y d d_nn x_nn y_nn Hx Hy.
  destruct x; try lia.
  - now rewrite Z.lor_0_l.
  - destruct y; try lia.
    + now rewrite Z.lor_0_r.
    + simpl.
      destruct d; try lia.
      rewrite <- Pos2Z.inj_pow in *.
      apply Pos2Z.pos_lt_pos.
      rewrite pow_pow2 in *.
      apply Pos_lor_small; assumption.
Qed.

Definition get_vert (i : int) : option (Vert RomanWheel * int) :=
  match unhash_RWVert (lsb (to_Z i) 5) with
  | Some v => Some (v, i >> 5)%uint63
  | None => None
  end.

Lemma get_vert_add_vert : forall v i d,
  (to_Z i < 2^d)%Z ->
  (0 <= d)%Z ->
  (d + 5 <= 63)%Z ->
  get_vert (add_vert v i) = Some (v, i).
Proof.
  intros.
  unfold get_vert, add_vert.
  rewrite lor_spec'.
  rewrite lsl_spec.
  unfold lsb.
  rewrite (Z.mod_small _ wB).
  - rewrite lor_add; try apply to_Z_bounded; try apply hash_small.
    rewrite Z_mod_plus_full.
    rewrite Z.mod_small.
    + rewrite unhash_hash.
      simpl Vert; do 2 f_equal.
      apply to_Z_inj.
      rewrite lsr_spec.
      rewrite lor_spec'.
      rewrite lsl_spec.
      rewrite Z.mod_small.
      * rewrite <- Z.shiftr_div_pow2; [|apply to_Z_bounded].
        rewrite Z.shiftr_lor.
        rewrite (Z.shiftr_div_pow2 (to_Z i * _)); [|apply to_Z_bounded].
        rewrite Z.div_mul; [|vm_compute; lia].
        rewrite Z.shiftr_eq_0; try apply to_Z_bounded.
        -- apply Z.lor_0_l.
        -- destruct (Z.eq_dec 0 (to_Z (hash v))).
           ++ simpl Vert in *; rewrite <- e; reflexivity.
           ++ rewrite <- Z.log2_lt_pow2.
              ** apply hash_small.
              ** destruct (to_Z_bounded (hash v)).
                 simpl Vert in *; lia.
      * split.
        -- apply Z.mul_nonneg_nonneg; [|lia].
           apply to_Z_bounded.
        -- unfold wB.
            simpl Z.of_nat.
            apply (Z.lt_le_trans _ (2^(d+5))).
            ++ rewrite Z.pow_add_r; simpl; lia.
            ++ apply Z.pow_le_mono_r; lia.
    + split.
      * apply to_Z_bounded.
      * apply hash_small.
  - split.
    + apply Z.mul_nonneg_nonneg; [|lia].
      apply to_Z_bounded.
    + unfold wB.
      simpl Z.of_nat.
      apply (Z.lt_le_trans _ (2^(d+5))).
      * rewrite Z.pow_add_r; simpl; lia.
      * apply Z.pow_le_mono_r; lia.
Qed.

Lemma add_vert_small v i d :
  (0 <= d)%Z ->
  (d + 5 <= 63)%Z ->
  (to_Z i < 2^d)%Z ->
  (to_Z (add_vert v i) < 2^(d+5))%Z.
Proof.
  intros d_nonneg d_small i_small.
  unfold add_vert.
  rewrite lor_spec'.
  rewrite lsl_spec.
  rewrite Z.mod_small.
  - apply lor_small; try lia.
    + apply to_Z_bounded.
    + apply Z.mul_nonneg_nonneg; [|lia].
      apply to_Z_bounded.
    + apply (Z.lt_le_trans _ (2^5)).
      * apply hash_small.
      * apply Z.pow_le_mono_r; lia.
    + rewrite Z.pow_add_r; try lia.
      apply Zmult_gt_0_lt_compat_r; auto; lia.
  - split.
    + apply Z.mul_nonneg_nonneg; [|lia].
      apply to_Z_bounded.
    + apply (Z.lt_le_trans _ (2^(d+5))).
      * rewrite Z.pow_add_r; try lia.
        apply Zmult_gt_0_lt_compat_r; auto; lia.
      * unfold wB, size.
        apply Z.pow_le_mono_r; lia.
Qed.

Definition add_verts (vs : list (Vert RomanWheel)) (i : int) : int :=
  fold_right add_vert i vs.

Fixpoint get_verts n (i : int) : option (list (Vert RomanWheel)) :=
  match n with
  | 0 => Some []
  | S m =>
    match get_vert i with
    | Some (v, j) =>
      match get_verts m j with
      | Some vs => Some (v :: vs)
      | None => None
      end
    | None => None
    end
  end.

Lemma add_verts_small vs i d :
  (0 <= d)%Z ->
  (d + 5 * Z.of_nat (length vs) <= 63)%Z ->
  (to_Z i < 2^d)%Z ->
  (to_Z (add_verts vs i) < 2^(d + 5 * Z.of_nat (length vs)))%Z.
Proof.
  intro d_nonneg.
  unfold add_verts.
  induction vs.
  - simpl.
    rewrite Z.add_0_r.
    lia.
  - simpl length.
    rewrite Nat2Z.inj_succ.
    rewrite <- Z.add_1_r.
    simpl fold_right.
    intro.
    assert (d + 5 * (Z.of_nat (length vs) + 1) =
      (d + 5 * (Z.of_nat (length vs))) + 5)%Z as pf by lia.
    simpl Vert in pf.
    rewrite pf.
    intro Hi.
    apply add_vert_small; simpl Vert; try lia.
    apply IHvs; auto.
    simpl Vert; lia.
Qed.

Lemma get_verts_add_verts : forall vs i d,
  (to_Z i < 2^d)%Z ->
  (0 <= d)%Z ->
  (d + 5 * (Z.of_nat (length vs)) <= 63)%Z ->
  get_verts (length vs) (add_verts vs i) = Some vs.
Proof.
  induction vs.
  - intros; reflexivity.
  - intros; simpl.
    erewrite get_vert_add_vert.
    + erewrite IHvs.
      * reflexivity.
      * exact H.
      * auto.
      * simpl length in H1.
        simpl Vert. lia.
    + apply add_verts_small; eauto.
      simpl length in H1.
      rewrite Nat2Z.inj_succ in H1.
      rewrite <- Z.add_1_r in H1.
      simpl Vert; lia.
    + simpl length in H1.
      rewrite Nat2Z.inj_succ in H1.
      rewrite <- Z.add_1_r in H1.
      simpl Vert; lia.
    + simpl length in H1.
      rewrite Nat2Z.inj_succ in H1.
      rewrite <- Z.add_1_r in H1.
      simpl Vert; lia.
Qed.

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

Lemma lor_1_even : forall x : Z,
  (0 <= x -> Z.even x = true -> Z.lor 1 x = x + 1)%Z.
Proof.
  intros x x_nonneg x_even.
  unfold Z.lor.
  destruct x; try lia.
  rewrite Pos2Z.add_pos_pos.
  destruct p; try discriminate.
  reflexivity.
Qed.

Lemma get_player_add_player : forall p i,
  (to_Z i < 2^62)%Z ->
  get_player (add_player p i) = (p,i).
Proof.
  intros.
  unfold get_player, add_player.
  destruct p.
  - rewrite is_even_lsl_1.
    f_equal.
    apply to_Z_inj.
    rewrite lsr_spec.
    rewrite lsl_spec.
    rewrite Z.mod_small.
    + simpl; unfold Z.pow_pos; simpl.
      apply Z.div_mul; lia.
    + split.
      * apply Z.mul_nonneg_nonneg; [|lia].
        apply to_Z_bounded.
      * simpl; unfold Z.pow_pos; simpl.
        unfold wB; simpl Z.of_nat.
        lia.
  - rewrite is_even_bit.
    rewrite lor_spec; simpl.
    f_equal.
    apply to_Z_inj.
    rewrite lsr_spec.
    rewrite lor_spec'.
    rewrite lsl_spec.
    simpl Z.pow.
    unfold Z.pow_pos; simpl Pos.iter.
    rewrite Z.mod_small.
    + rewrite lor_1_even.
      * rewrite Z.div_add_l; [|lia].
        unfold Z.div; simpl; lia.
      * apply Z.mul_nonneg_nonneg; [|lia].
        apply to_Z_bounded.
      * rewrite Z.even_mul.
        apply Bool.orb_true_r.
    + split.
      * apply Z.mul_nonneg_nonneg; [|lia].
        apply to_Z_bounded.
      * simpl; unfold Z.pow_pos; simpl.
        unfold wB; simpl Z.of_nat.
        lia.
Qed.

Definition hash_RW_State (s : BG_State RomanWheel) : int :=
  match s with
  | Build_BG_State _ p b hs _ _ _ _ =>
      add_player p (add_vert b (add_verts hs 0))
  end.

Lemma hash_RW_State_inj : forall s s',
  hash_RW_State s = hash_RW_State s' -> s = s'.
Proof.
  intros s s' Hss'.
  unfold hash_RW_State in Hss'.
  destruct s, s'; simpl in *.
  pose proof (f_equal get_player Hss') as pf1.
  rewrite get_player_add_player in pf1.
  rewrite get_player_add_player in pf1.
  - inversion pf1.
    pose proof (f_equal get_vert H1) as pf2.
    rewrite (get_vert_add_vert _ _ 15) in pf2; try lia.
    rewrite (get_vert_add_vert _ _ 15) in pf2; try lia.
    + inversion pf2.
      pose proof (f_equal (get_verts (length hunters)) H3) as pf3.
      rewrite (get_verts_add_verts _ 0 0) in pf3; try (lia||reflexivity).
      rewrite hunters_3 in pf3.
      rewrite <- hunters_0 in pf3.
      rewrite (get_verts_add_verts _ 0 0) in pf3; try (lia||reflexivity).
      * apply BG_State_ext; simpl; congruence.
      * simpl Vert; rewrite hunters_0; lia.
      * simpl Vert; rewrite hunters_3; lia.
    + pose proof (add_verts_small hunters0 0 0).
      simpl Vert in *.
      rewrite hunters_0 in H.
      apply H; simpl; [lia|lia |reflexivity].
    + pose proof (add_verts_small hunters 0 0).
      simpl Vert in *.
      rewrite hunters_3 in H.
      apply H; simpl; [lia|lia|reflexivity].
  - apply (Z.lt_trans _ (2^20)); [|lia].
    apply (add_vert_small _ _ 15); simpl; [lia|lia|].
    pose (add_verts_small hunters0) as pf'.
    simpl Vert in *.
    rewrite hunters_0 in pf'.
    apply (pf' _ 0)%Z; unfold to_Z; simpl; try lia.
  - apply (Z.lt_trans _ (2^20)); [|lia].
    apply (add_vert_small _ _ 15); simpl; [lia|lia|].
    pose (add_verts_small hunters) as pf'.
    simpl Vert in *.
    rewrite hunters_3 in pf'.
    apply (pf' _ 0)%Z; unfold to_Z; simpl; try lia.
Qed.

Global Instance IntHash_RW : IntHash (Game.GameState (BearGame RomanWheel)) := {|
  hash := hash_RW_State;
  hash_inj := hash_RW_State_inj;
  |}.

Definition RW_TB := Bear_TB RomanWheel.
