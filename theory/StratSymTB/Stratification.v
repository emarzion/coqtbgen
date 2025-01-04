Require Import Init.Wf.
Require Import List.

Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Draw.
Require Import Games.Game.Win.
Require Import Games.Game.NoWorse.
Require Import Games.Game.Strategy.

Inductive star {X} (R : X -> X -> Prop) : X -> X -> Prop :=
  | star_nil : forall x, star R x x
  | star_snoc : forall x y z, star R x y -> R y z -> star R x z.

Record FinBranchWFOrd : Type := {
  carrier :> Type;
  eq_dec : forall i i' : carrier, { i = i' } + { i <> i' };
  lt : carrier -> carrier -> Prop;
  lt_wf : well_founded lt;
  ancestors : carrier -> list carrier;
  lt_ancestor : forall i j,
    lt i j -> In i (ancestors j);
  ancestor_lt : forall i j,
    In i (ancestors j) -> lt i j
  }.

Record Stratification (I : FinBranchWFOrd) (G : Game) : Type := {
  index : GameState G -> I;
  index_decr : forall s (m : Move s),
    { index (exec_move s m) = index s } +
    { lt I (index (exec_move s m)) (index s) }
  }.

Require Import List.
Import ListNotations.
Require Import Lia.

Fixpoint in_specific_map {A B} (xs : list A) :
  (forall x, In x xs -> B) -> list B :=
  match xs with
  | [] => fun _ => []
  | x :: ys => fun f =>
    f x (or_introl eq_refl) ::
    in_specific_map ys (fun y pf => f y (or_intror pf))
  end.

Lemma In_in_specific_map {A B} (xs : list A) (x : A)
  (pf : In x xs) (f : forall x, In x xs -> B) :
  In (f x pf) (in_specific_map xs f).
Proof.
  induction xs.
  - destruct pf.
  - simpl.
    destruct pf.
    + destruct e; left; reflexivity.
    + right.
      apply (IHxs i (fun x pf => f x (or_intror pf))).
Qed.

Lemma in_specific_map_In {A B} (xs : list A) (y : B)
  (f : forall x, In x xs -> B) :
  In y (in_specific_map xs f) ->
  exists (x : A) (pf : In x xs),
  f x pf = y.
Proof.
  induction xs; intro pf.
  - destruct pf.
  - simpl in pf.
    destruct pf.
    + exists a.
      eexists; exact H.
    + destruct (IHxs _ H) as [x [pf Hxpf]].
      exists x.
      eexists; exact Hxpf.
Qed.

Lemma in_specific_map_iff {A B} (xs : list A) (y : B)
  (f : forall x, In x xs -> B) :
  In y (in_specific_map xs f) <->
  exists (x : A) (pf : In x xs),
  f x pf = y.
Proof.
  split.
  - apply in_specific_map_In.
  - intros [x [pf Hpf]].
    rewrite <- Hpf.
    apply In_in_specific_map.
Qed.

Fixpoint compute_all_ancestors_aux {I : FinBranchWFOrd} (i : I)
  (a : Acc (lt I) i) {struct a} : list I.
Proof.
  destruct a.
  apply (cons i).
  apply (nodup (eq_dec I)).
  refine (concat _).
  unshelve eapply in_specific_map;
    [| exact (ancestors I i) |].
  intros x' pf.
  apply (compute_all_ancestors_aux I x').
  apply H.
  apply ancestor_lt.
  exact pf.
Defined.

Definition compute_all_ancestors {I : FinBranchWFOrd} (i : I) : list I :=
  compute_all_ancestors_aux i
  (lt_wf I i).

Fixpoint compute_all_ancestors_aux_star {I : FinBranchWFOrd} (i j : I) a {struct a} :
  In j (compute_all_ancestors_aux i a) -> star (lt I) j i.
Proof.
  intro pf.
  destruct a; simpl in pf.
  destruct pf.
  - subst. apply star_nil.
  - rewrite nodup_In in H.
    rewrite in_concat in H.
    destruct H as [xs [Hxs1 Hxs2]].
    rewrite in_specific_map_iff in Hxs1.
    destruct Hxs1 as [i' [pf Hi'pf]].
    rewrite <- Hi'pf in Hxs2; clear Hi'pf.
    apply compute_all_ancestors_aux_star in Hxs2.
    apply ancestor_lt in pf.
    apply star_snoc with (y := i'); auto.
Qed.

Fixpoint star_compute_all_ancestors_aux {I : FinBranchWFOrd} (i j : I) a
  (pf : star (lt I) j i) {struct pf} :
  In j (compute_all_ancestors_aux i a).
Proof.
  destruct pf.
  - destruct a; left.
    reflexivity.
  - destruct a; right.
    rewrite nodup_In.
    rewrite in_concat.
    apply lt_ancestor in H.
    exists (compute_all_ancestors_aux y
      (a y (ancestor_lt I y z H))); split.
    + rewrite in_specific_map_iff.
      exists y, H.
      reflexivity.
    + apply star_compute_all_ancestors_aux; auto.
Qed.

Lemma compute_all_ancestors_correct {I : FinBranchWFOrd} (i j : I) :
  In j (compute_all_ancestors i) <-> star (lt I) j i.
Proof.
  split.
  - apply compute_all_ancestors_aux_star.
  - apply star_compute_all_ancestors_aux.
Qed.


