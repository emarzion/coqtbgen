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

Lemma Fin_plus_assoc {n} (i j k : Fin n) :
  Fin_plus i (Fin_plus j k) = Fin_plus (Fin_plus i j) k.
Proof.
  intros.
  apply val_inj.
  repeat rewrite val_plus.
  rewrite Nat.Div0.add_mod_idemp_r.
  rewrite Nat.Div0.add_mod_idemp_l.
  now rewrite Nat.add_assoc.
Qed.

Lemma Fin_inv_left {n} (x : Fin (S n)) :
  Fin_plus (Fin_inv x) x = Fin_zero.
Proof.
  destruct x as [x x_small].
  apply val_inj.
  rewrite val_plus.
  rewrite val_inv.
  simpl val.
  destruct x.
  - simpl; lia.
  - assert (S n - S x + S x = S n) by lia.
    rewrite H.
    now rewrite Nat.Div0.mod_same.
Qed.

Lemma Fin_inv_right {n} (x : Fin (S n)) :
  Fin_plus x (Fin_inv x) = Fin_zero.
Proof.
  - destruct x as [x x_small].
    apply val_inj.
    rewrite val_plus.
    rewrite val_inv.
    simpl val.
    destruct x.
    + simpl; lia.
    + assert (S x + (S n - S x) = S n) by lia.
      rewrite H.
      now rewrite Nat.Div0.mod_same.
Qed.

Lemma Fin_zero_l {n} (x : Fin (S n)) :
  Fin_plus Fin_zero x = x.
Proof.
  destruct x as [x x_small].
  apply val_inj.
  rewrite val_plus.
  simpl val.
  rewrite Nat.mod_small; auto.
Qed.

Lemma Fin_zero_r {n} (x : Fin (S n)) :
  Fin_plus x Fin_zero = x.
Proof.
  destruct x as [x x_small].
  apply val_inj.
  rewrite val_plus.
  simpl val.
  rewrite Nat.mod_small; auto; lia.
Qed.

Definition Z_8 : Group := {|
    carrier := Fin 8;
    id := Fin_zero;
    mult := Fin_plus;
    inv := Fin_inv;
    assoc := Fin_plus_assoc;
    id_left := Fin_zero_l;
    id_right := Fin_zero_r;
    inv_left := Fin_inv_left;
    inv_right := Fin_inv_right;
  |}.

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

Lemma cw_ccw s :
  clockwise (c_clockwise s) = s.
Proof.
  destruct s; auto.
Qed.

Lemma ccw_cw s :
  c_clockwise (clockwise s) = s.
Proof.
  destruct s; auto.
Qed.

Lemma rotate_spoke_c_clockwise n s :
  rotate_spoke n (c_clockwise s) =
  c_clockwise (rotate_spoke n s).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite cw_ccw.
    now rewrite ccw_cw.
Qed.

Lemma rotate_spoke_clockwise n s :
  rotate_spoke n (clockwise s) = 
  clockwise (rotate_spoke n s).
Proof.
  induction n.
  - reflexivity.
  - simpl; now rewrite IHn.
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
    + simpl successors in *.
      destruct l.
      * destruct pf as [pf1|[pf2|[pf3|[]]]]; subst.
        -- now left.
        -- right; now left.
        -- right; right; now left.
      * destruct pf as [pf1|[pf2|[pf3|[]]]]; subst.
        -- now left.
        -- right; now left.
        -- right; right; left; simpl.
           now rewrite rotate_spoke_c_clockwise.
      * destruct pf as [pf1|[pf2|[pf3|[]]]]; subst.
        -- now left.
        -- right; now left.
        -- right; right; left; simpl.
           simpl.
           now rewrite rotate_spoke_clockwise.
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

Definition one : carrier Z_8.
Proof.
  exists 1; lia.
Defined.

Definition compute_rotation (s : BG_State RomanWheel) : carrier Z_8 :=
  match bear s with
  | Center => mult 3 (spoke_total (hunters s))
  | SpokeVert s' l => spoke_Fin s'
  end.

Lemma spoke_Fin_clockwise : forall s,
  spoke_Fin (clockwise s) =
  Fin_plus (inv one) (spoke_Fin s).
Proof.
  intro s.
  apply val_inj.
  destruct s; reflexivity.
Qed.

Lemma spoke_Fin_rotate_spoke_nat : forall n s,
  spoke_Fin (rotate_spoke n s) =
  Fin_plus (mult n (inv one)) (spoke_Fin s).
Proof.
  induction n; intro s.
  - simpl rotate_spoke.
    simpl mult.
    symmetry; apply (@id_left Z_8).
  - simpl rotate_spoke.
    rewrite spoke_Fin_clockwise.
    unfold mult; fold @mult.
    rewrite IHn.
    apply (@assoc Z_8).
Qed.

Lemma val_mult n (x : carrier Z_8) :
  val (mult n x) = (n * val x) mod 8.
Proof.
  induction n.
  - reflexivity.
  - simpl mult.
    rewrite val_plus.
    simpl Nat.mul.
    rewrite IHn.
    now rewrite Nat.Div0.add_mod_idemp_r.
Qed.

Lemma val_one : val one = 1.
Proof.
  reflexivity.
Qed.

Lemma spoke_Fin_rotate_spoke : forall (x : carrier Z_8) s,
  spoke_Fin (rotate_spoke (val x) s) =
  (inv x) ** (spoke_Fin s).
Proof.
  intros x s; simpl.
  rewrite spoke_Fin_rotate_spoke_nat.
  f_equal.
  apply val_inj.
  rewrite val_inv.
  rewrite val_mult.
  unfold inv.
  unfold Z_8.
  rewrite val_inv.
  rewrite val_one.
  destruct x as [x x_pf].
  simpl val.
  destruct x.
  - reflexivity.
  - destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    lia.
Defined.

Lemma spoke_total_insert_Center
  (xs : list (Vert RomanWheel)) :
  spoke_total (Sort.insert (Center : Vert RomanWheel) xs) =
  spoke_total xs.
Proof.
  induction xs.
  - reflexivity.
  - unfold Sort.insert; fold @Sort.insert.
    destruct Sort.ord_le_dec.
    + reflexivity.
    + unfold spoke_total; fold @spoke_total.
      rewrite IHxs; reflexivity.
Qed.

Lemma spoke_total_insert_spoke
  (xs : list (Vert RomanWheel)) s l :
  spoke_total (Sort.insert (SpokeVert s l : Vert RomanWheel) xs) =
  Fin_plus (spoke_Fin s) (spoke_total xs).
Proof.
  induction xs.
  - reflexivity.
  - unfold Sort.insert; fold @Sort.insert.
    destruct Sort.ord_le_dec.
    + reflexivity.
    + unfold spoke_total; fold @spoke_total.
      rewrite IHxs.
      destruct a; auto.
      rewrite Fin_plus_assoc.
      rewrite (Fin_plus_comm (spoke_Fin s0)).
      now rewrite <- Fin_plus_assoc.
Qed.

Lemma spoke_total_insertion_sort (xs : list (Vert RomanWheel)) :
  spoke_total (Sort.insertion_sort xs) = spoke_total xs.
Proof.
  induction xs.
  - reflexivity.
  - simpl Sort.insertion_sort.
    destruct a.
    + simpl spoke_total.
      now rewrite spoke_total_insert_Center.
    + unfold spoke_total at 2.
      fold @spoke_total.
      rewrite <- IHxs.
      now rewrite spoke_total_insert_spoke.
Qed.

Lemma spoke_total_map_rotate_vert n (xs : list (Vert RomanWheel)) :
  (~ In Center xs) ->
  spoke_total (map (rotate_vert n) xs) =
  Fin_plus (mult (length xs) (mult n (inv one))) (spoke_total xs).
Proof.
  intro pf.
  induction xs.
  - apply val_inj; reflexivity.
  - simpl map.
    unfold spoke_total; fold spoke_total.
    destruct a.
    + elim pf; now left.
    + simpl rotate_vert.
      rewrite IHxs.
      * simpl length.
        rewrite spoke_Fin_rotate_spoke_nat.
        pose (a := spoke_total xs); fold a.
        pose (b := mult n (inv one)); fold b.
        simpl mult.
        pose (c := spoke_Fin s); fold c.
        pose (d := mult (length xs) b); simpl Vert in d.
        fold d.
        rewrite <- Fin_plus_assoc.
        rewrite (Fin_plus_assoc c d a).
        rewrite (Fin_plus_comm c d).
        rewrite <- (Fin_plus_assoc d c a).
        now rewrite Fin_plus_assoc.
      * intro; apply pf; now right.
Qed.

Lemma mult_Fin_plus k (x y : carrier Z_8) :
  mult k (Fin_plus x y) =
  Fin_plus (mult k x) (mult k y).
Proof.
  apply val_inj.
  rewrite val_plus.
  rewrite val_mult.
  rewrite val_plus.
  repeat rewrite val_mult.
  do 2 rewrite Nat.Div0.add_mod.
  destruct x as [x ?].
  destruct y as [y ?].
  simpl val.
  repeat rewrite (Nat.mod_small x); auto.
  repeat rewrite (Nat.mod_small y); auto.
  rewrite Nat.Div0.mul_mod_idemp_r.
  rewrite Nat.mul_add_distr_l.
  now rewrite Nat.Div0.add_mod.
Qed.

Lemma Fin_plus_l_cancel {n} (x y z : Fin (S n)) :
  Fin_plus x y = Fin_plus x z ->
  y = z.
Proof.
  intro pf.
  rewrite <- (Fin_zero_l y).
  rewrite <- (Fin_inv_left x).
  rewrite <- Fin_plus_assoc.
  rewrite pf.
  rewrite Fin_plus_assoc.
  rewrite Fin_inv_left.
  apply Fin_zero_l.
Qed.

Lemma Fin_inv_plus (x y : carrier Z_8) :
  Fin_inv (Fin_plus x y) =
  Fin_plus (Fin_inv y) (Fin_inv x).
Proof.
  apply (Fin_plus_l_cancel (Fin_plus x y)).
  rewrite Fin_inv_right.
  rewrite Fin_plus_assoc.
  rewrite <- (Fin_plus_assoc x).
  rewrite Fin_inv_right.
  rewrite Fin_zero_r.
  now rewrite Fin_inv_right.
Qed.

Lemma mult_add k l (x : carrier Z_8) :
  mult (k + l) x =
  Fin_plus (mult k x) (mult l x).
Proof.
  induction k.
  - simpl mult.
    symmetry; apply (@id_left Z_8).
  - simpl.
    rewrite IHk.
    apply (@assoc Z_8).
Qed.

Lemma mult_comp k l (x : carrier Z_8) :
  mult k (mult l x) = mult (k * l) x.
Proof.
  induction k.
  - reflexivity.
  - simpl.
    rewrite IHk.
    now rewrite mult_add.
Qed.

Lemma mult_inv k (x : carrier Z_8) :
  mult k (Fin_inv x) = Fin_inv (mult k x).
Proof.
  induction k.
  - simpl mult.
    now apply val_inj.
  - simpl mult.
    rewrite IHk.
    rewrite Fin_plus_comm.
    now rewrite Fin_inv_plus.
Qed.

Lemma compute_rotation_BG_State_act : forall (x : carrier Z_8) s,
  compute_rotation (BG_State_act x s) =
  compute_rotation s ** (inv x).
Proof.
  intros.
  destruct (bear s) eqn:?.
  - unfold compute_rotation.
    simpl bear.
    rewrite Heqv.
    simpl rotate_vert.
    cbv iota.
    simpl hunters.
    rewrite spoke_total_insertion_sort.
    rewrite spoke_total_map_rotate_vert.
    + rewrite hunters_3.
      pose (y := spoke_total (hunters s)).
      fold y.
      rewrite mult_Fin_plus.
      rewrite Fin_plus_comm.
      unfold GroupAction.mult.
      unfold Z_8.
      f_equal.
      repeat rewrite mult_comp.
      unfold inv.
      rewrite mult_inv.
      f_equal.
      apply val_inj.
      rewrite val_mult.
      rewrite Nat.Div0.mul_mod.
      rewrite val_one.
      rewrite (Nat.Div0.mul_mod (3 * 3)).
      simpl ((3 * 3) mod 8).
      simpl (1 mod 8).
      rewrite Nat.mul_1_l.
      rewrite Nat.mul_1_r.
      repeat rewrite Nat.Div0.mod_mod.
      apply Nat.mod_small.
      destruct x; simpl; auto.
    + rewrite <- Heqv.
      apply s.
  - unfold compute_rotation.
    simpl.
    rewrite Heqv.
    simpl rotate_vert.
    cbv iota.
    rewrite spoke_Fin_rotate_spoke.
    rewrite Fin_plus_comm.
    reflexivity.
Qed.

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
