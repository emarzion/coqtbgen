Require Import List.
Import ListNotations.
Require Import Sorting.

Class Ord (X : Type) := {
  ord_le : X -> X -> Prop;
  ord_le_trans : forall x y z, ord_le x y -> ord_le y z -> ord_le x z;
  ord_le_dec : forall x y, { ord_le x y } + { ord_le y x }
  }.

Definition sorted {X} `{Ord X} : list X -> Prop :=
  StronglySorted ord_le.

Fixpoint insert {X} `{Ord X} (x : X) (xs : list X) : list X :=
  match xs with
  | [] => [x]
  | y :: ys =>
    match ord_le_dec x y with
    | left _ => x :: xs
    | right _ => y :: insert x ys
    end
  end.

Lemma In_insert_invert {X} `{Ord X} {x y : X} {xs : list X} :
  In x (insert y xs) -> x = y \/ In x xs.
Proof.
  induction xs; intros HIn.
  - destruct HIn as [Heq|[]].
    now left.
  - simpl in *.
    destruct (ord_le_dec y a).
    + repeat destruct HIn; auto.
    + destruct HIn; auto.
      destruct (IHxs H0); auto.
Qed.

Lemma insert_sorted {X} `{Ord X} (x : X) (xs : list X) :
  sorted xs -> sorted (insert x xs).
Proof.
  induction xs; intros pf.
  - do 2 constructor.
  - simpl.
    destruct (ord_le_dec x a).
    + constructor; auto.
      rewrite Forall_forall.
      intros y HIn.
      destruct HIn.
      * congruence.
      * apply (ord_le_trans _ a).
        -- auto.
        -- inversion pf.
           rewrite Forall_forall in H4.
           now apply H4.
    + constructor.
      * apply IHxs.
        inversion pf; auto.
      * rewrite Forall_forall.
        intros y HIn.
        destruct (In_insert_invert HIn).
        -- now congruence.
        -- inversion pf.
           rewrite Forall_forall in H4.
           now apply H4.
Qed.

Fixpoint insertion_sort {X} `{Ord X} (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: ys => insert x (insertion_sort ys)
  end.

Lemma insertion_sort_sorts {X} `{Ord X} (xs : list X) :
  sorted (insertion_sort xs).
Proof.
  induction xs.
  - constructor.
  - now apply insert_sorted.
Qed.

Lemma insertion_sort_length {X} `{Ord X} (xs : list X) :
  length (insertion_sort xs) = length xs.
Proof.
Admitted.

Lemma insertion_sort_NoDup {X} `{Ord X} (xs : list X) :
  NoDup xs -> NoDup (insertion_sort xs).
Proof.
Admitted.

Lemma insertion_sort_In {X} `{Ord X} (xs : list X) :
  forall x, In x (insertion_sort xs) <-> In x xs.
Proof.
Admitted.

Fixpoint sublists {X} n (xs : list X) {struct xs} : list (list X) :=
  match n with
  | 0 => [[]]
  | S m =>
    match xs with
    | [] => []
    | x :: ys => map (cons x) (sublists m ys) ++ sublists n ys
    end
  end.

