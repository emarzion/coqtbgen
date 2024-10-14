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
  { i : nat | i < n }.

Definition val {n} (i : Fin n) : nat :=
  proj1_sig i.

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

Lemma Fin_plus_comm {n} (i j : Fin n) :
  Fin_plus i j = Fin_plus j i.
Proof.
  apply val_inj.
  repeat rewrite val_plus.
  rewrite Nat.add_comm.
  auto.
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

Lemma successors_Center : forall v,
  In v (@successors RomanWheel Center) <->
  exists s, v = SpokeVert s Mid.
Proof.
  intro v; split; intro pf.
  - simpl in pf.
    firstorder; subst; eexists; eauto.
  - destruct pf as [s Hs]; subst.
    simpl; destruct s; tauto.
Qed.

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
      rewrite successors_Center in *.
      destruct pf as [s Hs]; subst.
      exists (rotate_spoke (val x) s).
      reflexivity.
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
  exist _ (spoke_nat s) (spoke_nat_small s).

Fixpoint mult {n} (k : nat) (i : Fin (S n)) : Fin (S n) :=
  match k with
  | 0 => Fin_zero
  | S m => Fin_plus i (mult m i)
  end.

Fixpoint spoke_total (vs : list RWVert) : carrier Z_8 :=
  match vs with
  | [] => Fin_zero
  | Center :: vs' => spoke_total vs'
  | SpokeVert s _ :: vs' => Fin_plus (spoke_Fin s) (spoke_total vs')
  end.

Definition compute_rotation (s : BG_State RomanWheel) : carrier Z_8 :=
  match bear s with
  | Center => mult 3 (spoke_total (hunters s))
  | SpokeVert s' l => spoke_Fin s'
  end.

Lemma spoke_Fin_rotate_spoke : forall (x : carrier Z_8) s,
  spoke_Fin (rotate_spoke (val x) s) =
  (inv x) ** (spoke_Fin s).
Proof.
Admitted.

Lemma compute_rotation_BG_State_act : forall (x : carrier Z_8) s,
  compute_rotation (BG_State_act x s) =
  compute_rotation s ** (inv x).
Proof.
  intros.
  destruct (bear s) eqn:?.
  -
  unfold compute_rotation.
  simpl.
  rewrite Heqv.
  simpl.
  admit.
  -
  unfold compute_rotation.
  simpl.
  rewrite Heqv.
  simpl rotate_vert.
  cbv iota.
  rewrite spoke_Fin_rotate_spoke.
  rewrite Fin_plus_comm.
  reflexivity.
Admitted.

Global Instance RW_OrbitSelector : OrbitSelector RomanWheel Z_8.
Proof.
  refine {|
    select := fun s => BG_State_act (compute_rotation s) s
  |}.
  - intro s.
    exists (compute_rotation s).
    reflexivity.
  - intros s x.
    rewrite compute_rotation_BG_State_act.
    rewrite BG_State_act_comp.
    rewrite <- (BG_State_act_comp (inv x)).
    rewrite inv_left.
    now rewrite BG_State_act_id.
Defined.

Definition RW_TB :=
  Bear_TB RomanWheel Z_8.
