Require Import List.
Import ListNotations.
Require Import Sorting.

Class Ord (X : Type) := {
  ord_le : X -> X -> Prop;
  ord_le_trans : forall x y z, ord_le x y -> ord_le y z -> ord_le x z;
  ord_le_dec : forall x y, { ord_le x y } + { ord_le y x };
  ord_le_antisym : forall x y, ord_le x y -> ord_le y x -> x = y
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

Lemma insert_length {X} `{Ord X} (x : X) (xs : list X) :
  length (insert x xs) = S (length xs).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct (ord_le_dec x a).
    + reflexivity.
    + simpl; congruence.
Qed.

Lemma insertion_sort_length {X} `{Ord X} (xs : list X) :
  length (insertion_sort xs) = length xs.
Proof.
  induction xs; intros.
  - reflexivity.
  - simpl.
    rewrite insert_length; congruence.
Qed.

Lemma insert_In_1 {X} `{Ord X} (x : X) (xs : list X) :
  forall y, In y (insert x xs) -> (x = y \/ In y xs).
Proof.
  induction xs; intros y Hy.
  - left; now destruct Hy.
  - simpl in Hy.
    destruct (ord_le_dec x a).
    + destruct Hy; auto.
    + simpl in *; firstorder.
Qed.

Lemma insert_In_2 {X} `{Ord X} (x : X) (xs : list X) :
  forall y, (x = y \/ In y xs) -> In y (insert x xs).
Proof.
  induction xs; intros y Hy.
  - simpl in *; tauto.
  - simpl.
    destruct (ord_le_dec x a); simpl in *; firstorder.
Qed.

Lemma insert_In {X} `{Ord X} (x : X) (xs : list X) :
  forall y, In y (insert x xs) <-> (x = y \/ In y xs).
Proof.
  intro; split.
  - apply insert_In_1.
  - apply insert_In_2.
Qed.

Lemma insertion_sort_In_1 {X} `{Ord X} (xs : list X) :
  forall x, In x (insertion_sort xs) -> In x xs.
Proof.
  induction xs; intros x Hx.
  - destruct Hx.
  - simpl in Hx.
    rewrite insert_In in Hx.
    simpl; firstorder.
Qed.

Lemma insertion_sort_In_2 {X} `{Ord X} (xs : list X) :
  forall x, In x xs -> In x (insertion_sort xs).
Proof.
  induction xs; intros x Hx.
  - destruct Hx.
  - simpl.
    rewrite insert_In.
    simpl in Hx; firstorder.
Qed.

Lemma insertion_sort_In {X} `{Ord X} (xs : list X) :
  forall x, In x (insertion_sort xs) <-> In x xs.
Proof.
  intro; split.
  - apply insertion_sort_In_1.
  - apply insertion_sort_In_2.
Qed.

Lemma insert_NoDup {X} `{Ord X} (x : X) xs :
  NoDup xs -> ~ In x xs -> NoDup (insert x xs).
Proof.
  induction xs; intros nd nIn.
  - constructor; auto.
  - simpl.
    destruct (ord_le_dec x a).
    + now constructor.
    + constructor.
      * rewrite insert_In.
        intros [pf|pf].
        -- simpl in nIn; auto.
        -- now inversion nd.
      * apply IHxs.
        -- now inversion nd.
        -- simpl in nIn; auto.
Qed.

Lemma insertion_sort_NoDup {X} `{Ord X} (xs : list X) :
  NoDup xs -> NoDup (insertion_sort xs).
Proof.
  induction xs; intro pf.
  - constructor.
  - simpl.
    inversion pf.
    apply insert_NoDup; auto.
    now rewrite insertion_sort_In.
Qed.

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

Lemma in_sublists {X} `{Ord X} :
  forall xs, NoDup xs -> sorted xs ->
  forall ys, NoDup ys -> sorted ys ->
  (forall y, In y ys -> In y xs) ->
  forall n, length ys = n ->
  In ys (sublists n xs).
Proof.
  induction xs; intros nd_xs sort_xs ys nd_ys sort_ys ys_sublist n ys_len.
  - simpl; destruct n.
    + destruct ys; [now left|].
      discriminate.
    + destruct ys; [discriminate|].
      elim (ys_sublist x).
      now left.
  - simpl; destruct n.
    + destruct ys; [now left|].
      discriminate.
    + rewrite in_app_iff.
      destruct ys as [|y zs]; [discriminate|].
      destruct (ys_sublist y) as [pf|pf]; [now left| |].
      * left.
        rewrite <- pf.
        apply in_map.
        apply IHxs.
        -- now inversion nd_xs.
        -- now inversion sort_xs.
        -- now inversion nd_ys.
        -- now inversion sort_ys.
        -- intros z Hz.
           destruct (ys_sublist z); [now right| |auto].
           inversion nd_ys; congruence.
        -- simpl in ys_len; congruence.
      * right.
        apply IHxs.
        -- now inversion nd_xs.
        -- now inversion sort_xs.
        -- now inversion nd_ys.
        -- now inversion sort_ys.
        -- intros z [Heq|HIn]; [now rewrite <- Heq|].
           destruct (ys_sublist z) as [pf'|]; [now right| |auto].
           absurd (y = z).
           ++ inversion nd_ys; congruence.
           ++ apply ord_le_antisym.
              ** inversion sort_ys as [|? ? ? Hy].
                 rewrite Forall_forall in Hy.
                 now apply Hy.
              ** rewrite pf' in *.
                 inversion sort_xs as [|? ? ? Hz].
                 rewrite Forall_forall in Hz.
                 now apply Hz.
        -- auto.
Qed.
