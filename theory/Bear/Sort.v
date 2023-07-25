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

Lemma sublist_length {X} (xs : list X) : forall n ys,
  In ys (sublists n xs) -> length ys = n.
Proof.
  induction xs; intros n ys Hys.
  - destruct ys; simpl in Hys.
    + destruct n; [reflexivity|destruct Hys].
    + destruct n; now inversion Hys.
  - simpl in Hys.
    destruct n.
    + inversion Hys as [H|H];
      now destruct H.
    + rewrite in_app_iff in Hys.
      destruct Hys as [H|H].
      * rewrite in_map_iff in H.
        destruct H as [l [Hl1 Hl2]].
        rewrite <- Hl1; simpl.
        now rewrite (IHxs _ _ Hl2).
      * now apply IHxs.
Qed.

Lemma sublist_In_trans {X} (xs : list X)
  : forall n x ys, In x ys -> In ys (sublists n xs) -> In x xs.
Proof.
  induction xs; intros n x ys Hx Hys.
  - simpl in Hys.
    destruct n.
    + destruct Hys as [H|H].
      * congruence.
      * destruct H.
    + destruct Hys.
  - simpl in Hys.
    destruct n.
    + destruct Hys as [H|H].
      * rewrite <- H in Hx; destruct Hx.
      * destruct H.
    + rewrite in_app_iff in Hys.
      destruct Hys.
      * rewrite in_map_iff in H.
        destruct H as [l [Hl1 Hl2]].
        rewrite <- Hl1 in Hx.
        destruct Hx.
        -- now left.
        -- right; eapply IHxs; eauto.
      * right; eapply IHxs; eauto.
Qed.

Lemma sublist_Forall {X} (xs : list X) (P : X -> Prop)
  : Forall P xs -> forall n ys, In ys (sublists n xs) ->
    Forall P ys.
Proof.
  induction xs; intros Hxs n ys Hys.
  - destruct n; simpl in Hys.
    + destruct Hys as [[]|[]].
      constructor.
    + destruct Hys.
  - destruct n; simpl in Hys.
    + destruct Hys as [[]|[]].
      constructor.
    + rewrite in_app_iff in Hys.
      destruct Hys as [pf|pf].
      * rewrite in_map_iff in pf.
        destruct pf as [l [[] Hl2]].
        inversion Hxs; constructor; auto.
        eapply IHxs; eauto.
      * eapply IHxs; eauto.
        now inversion Hxs.
Qed.

Lemma sublist_sort {X} `{Ord X} (xs : list X) :
  forall n ys, In ys (sublists n xs) ->
  sorted xs -> sorted ys.
Proof.
  unfold sorted.
  induction xs; intros n ys Hys xs_sort.
  - destruct n; simpl in Hys.
    + destruct Hys as [pf|[]].
      rewrite <- pf.
      constructor.
    + destruct Hys.
  - destruct n; simpl in Hys.
    + destruct Hys as [pf|[]].
      rewrite <- pf.
      constructor.
    + rewrite in_app_iff in Hys.
      destruct Hys as [pf|pf].
      * rewrite in_map_iff in pf.
        destruct pf as [l [Hl1 Hl2]].
        rewrite <- Hl1.
        inversion xs_sort.
        constructor.
        -- eapply IHxs; eauto.
        -- eapply sublist_Forall; eauto.
      * inversion xs_sort.
        eapply IHxs; eauto.
Qed.

Lemma filter_Forall {X} (xs : list X)
  (P : X -> Prop) (p : X -> bool) :
  Forall P xs -> Forall P (filter p xs).
Proof.
  induction xs; intros Hxs.
  - constructor.
  - inversion Hxs.
    simpl; destruct (p a).
    + constructor; auto.
    + now apply IHxs.
Qed.

Lemma sorted_filter {X} `{Ord X} (p : X -> bool) (xs : list X) :
  sorted xs -> sorted (filter p xs).
Proof.
  induction xs; intros xs_sort.
  - constructor.
  - simpl.
    inversion xs_sort.
    destruct (p a).
    + constructor.
      * now apply IHxs.
      * now apply filter_Forall.
    + now apply IHxs.
Qed.
