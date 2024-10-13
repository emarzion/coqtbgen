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
Require Import TBGen.Bear.RomanWheel.

Require Import TBGen.Bear.GroupAction.

Definition Fin n : Type :=
  { i : nat & i < n }.

Definition val {n} (i : Fin n) : nat :=
  projT1 i.

(* technically doesn't need proof irrel. *)
Lemma val_inj {n} (i j : Fin n) :
  val i = val j -> i = j.
Proof.
  destruct i as [x x_pf].
  destruct j as [y y_pf]; simpl.
  intro pf; subst.
  assert (x_pf = y_pf) by
    apply ProofIrrelevance.proof_irrelevance.
  subst; reflexivity.
Qed.

Definition Fin_zero {n} : Fin (S n).
Proof.
  exists 0; lia.
Defined.

Definition Fin_plus {n} : Fin n -> Fin n -> Fin n.
Proof.
  intros [x x_pf] [y y_pf].
  exists ((x + y) mod n).
  apply Nat.mod_upper_bound; lia.
Defined.

Lemma val_plus {n} (i j : Fin n) :
  val (Fin_plus i j) = (val i + val j) mod n.
Proof.
  destruct i,j; simpl.
  reflexivity.
Qed.

Definition Fin_inv {n} : Fin n -> Fin n.
Proof.
  intros [x x_pf].
  exists (
    match x with
    | 0 => 0
    | _ => n - x
    end).
  destruct x; lia.
Defined.

Lemma val_inv {n} (i : Fin n) :
  val (Fin_inv i) =
  match val i with
  | 0 => 0
  | _ => n - val i
  end.
Proof.
  destruct i; reflexivity.
Qed.

Definition Z_8 : Group.
Proof.
  refine {|
    carrier := Fin 8;
    id := Fin_zero;
    mult := Fin_plus;
    inv := Fin_inv;
    assoc := _;
    id_left := _;
    id_right := _;
    inv_left := _;
    inv_right := _;
  |}.
  - intros.
    apply val_inj.
    repeat rewrite val_plus.
    rewrite Nat.Div0.add_mod_idemp_r.
    rewrite Nat.Div0.add_mod_idemp_l.
    now rewrite Nat.add_assoc.
  - intros [x x_small].
    apply val_inj.
    rewrite val_plus.
    simpl val.
    rewrite Nat.mod_small; auto.
  - intros [x x_small].
    apply val_inj.
    rewrite val_plus.
    simpl val.
    rewrite Nat.mod_small; auto; lia.
  - intros [x x_small].
    apply val_inj.
    rewrite val_plus.
    rewrite val_inv.
    simpl val.
    destruct x.
    + reflexivity.
    + assert (8 - S x + S x = 8) by lia.
      rewrite H; reflexivity.
  - intros [x x_small].
    apply val_inj.
    rewrite val_plus.
    rewrite val_inv.
    simpl val.
    destruct x.
    + reflexivity.
    + assert (S x + (8 - S x) = 8) by lia.
      rewrite H; reflexivity.
Defined.

Fixpoint rotate_spoke (n : nat) (s : Spoke) : Spoke :=
  match n with
  | 0 => s
  | S m => clockwise (rotate_spoke m s)
  end.

Lemma rotate_spoke_plus (m n : nat) : forall (s : Spoke),
  rotate_spoke (m + n) s =
  rotate_spoke m (rotate_spoke n s).
Proof.
  induction m; intro.
  - reflexivity.
  - simpl.
    now rewrite IHm.
Qed.

Lemma rotate_8 : forall s,
  rotate_spoke 8 s = s.
Proof.
  intros []; reflexivity.
Qed.

Lemma rotate_mult_8 (n : nat) : forall (s : Spoke),
  rotate_spoke (8 * n) s = s.
Proof.
  induction n; intro.
  - reflexivity.
  - rewrite <- mult_n_Sm.
    rewrite rotate_spoke_plus.
    rewrite rotate_8.
    apply IHn.
Qed.

Lemma rotate_mod_8 (n : nat) : forall (s : Spoke),
  rotate_spoke n s = rotate_spoke (n mod 8) s.
Proof.
  intro s.
  rewrite (Nat.Div0.div_mod n 8) at 1.
  rewrite rotate_spoke_plus.
  now rewrite rotate_mult_8.
Qed.

Definition rotate_vert (n : nat) (v : RWVert) : RWVert :=
  match v with
  | Center => Center
  | SpokeVert s l => SpokeVert (rotate_spoke n s) l
  end.

Global Instance RW_Z_8 : GroupAction RomanWheel Z_8.
Proof.
  refine {|
    act := fun (x : carrier Z_8) (v : Vert RomanWheel) =>
      rotate_vert (val x) v;
    act_id := _;
    act_comp := _;
    act_edge := _;
  |}.
  - intros []; reflexivity.
  - intros [] x y.
    + reflexivity.
    + simpl; f_equal.
      rewrite val_plus.
      rewrite <- rotate_mod_8.
      now rewrite rotate_spoke_plus.
  - intros x v v' pf.
    destruct v.
    + simpl rotate_vert.
      apply cheat.
    + apply cheat.
Defined.

Definition spoke_nat (s : Spoke) : nat :=
  match s with
  | S1 => 0
  | S2 => 7
  | S3 => 6
  | S4 => 5
  | S5 => 4
  | S6 => 3
  | S7 => 2
  | S8 => 1
  end.

Lemma spoke_nat_small s : spoke_nat s < 8.
Proof.
  destruct s; simpl; lia.
Qed.

Definition spoke_Fin (s : Spoke) : Fin 8 :=
  existT _ (spoke_nat s) (spoke_nat_small s).

Definition compute_rotation (s : BG_State RomanWheel) : Fin 8.
Proof.
  destruct (bear s) eqn:?.
  - destruct s; simpl in *.
    destruct hunters.
    + discriminate.
    + destruct r.
      * elim bear_not_hunter; now left.
      * exact (spoke_Fin s).
  - exact (spoke_Fin s0).
Defined.

Global Instance RW_OrbitSelector : OrbitSelector RomanWheel Z_8.
Proof.
  refine {|
    select := fun s => BG_State_act (compute_rotation s) s
  |}.
  - intro s.
    exists (compute_rotation s).
    reflexivity.
  - apply cheat.
Defined.

Definition RW_TB :=
  Bear_TB RomanWheel Z_8.

