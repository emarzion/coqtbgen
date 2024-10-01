Require Import List.
Import ListNotations.
Require Import Games.Util.Dec.

Fixpoint filter_Nones_aux {X Y} (acc : list X) (f : X -> option Y) (xs : list X) : list X :=
  match xs with
  | [] => acc
  | x :: xs' =>
    match f x with
    | None => filter_Nones_aux (x :: acc) f xs'
    | Some _ => filter_Nones_aux acc f xs'
    end
  end.

Lemma In_filter_Nones_aux_correct1 {X Y} (f : X -> option Y) (xs : list X) :
  forall acc x, In x (filter_Nones_aux acc f xs) -> (f x = None /\ In x xs) \/ In x acc.
Proof.
  induction xs as [|x' xs']; intros acc x HIn; simpl in *.
  - now right.
  - destruct (f x') eqn:fx'.
    + destruct (IHxs' _ _ HIn).
      * left; split; tauto.
      * now right.
    + destruct (IHxs' _ _ HIn) as [Heq|HIn'].
      * left; split; tauto.
      * destruct HIn'.
        -- left; split; auto; congruence.
        -- now right.
Qed.

Lemma In_filter_Nones_aux_correct2 {X Y} (f : X -> option Y) (xs : list X) :
  forall acc x, (f x = None /\ In x xs) \/ In x acc -> In x (filter_Nones_aux acc f xs).
Proof.
  induction xs as [|x' xs'].
  - intros acc x [[_ []]|]; auto.
  - intros acc x [[fx [Heq|HIn]]|Q]; simpl.
    + rewrite Heq, fx. simpl.
      apply IHxs'; right; now left.
    + destruct (f x'); apply IHxs'; left; now split.
    + destruct (f x'); apply IHxs'.
      -- now right.
      -- right; now right.
Qed.

Lemma In_filter_Nones_aux_iff {X Y} (f : X -> option Y) (xs : list X) :
  forall acc x, In x (filter_Nones_aux acc f xs) <-> (f x = None /\ In x xs) \/ In x acc.
Proof.
  intros; split.
  - apply In_filter_Nones_aux_correct1.
  - apply In_filter_Nones_aux_correct2.
Qed.

Definition filter_Nones {X Y} (f : X -> option Y) (xs : list X) : list X :=
  filter_Nones_aux [] f xs.

Lemma In_filter_Nones_iff {X Y} (f : X -> option Y) (xs : list X) :
  forall x, In x (filter_Nones f xs) <-> f x = None /\ In x xs.
Proof.
  intro.
  unfold filter_Nones.
  rewrite In_filter_Nones_aux_iff; simpl; tauto.
Qed.

Definition disj {X} (xs ys : list X) : Prop :=
  forall x, In x xs -> ~ In x ys.

Definition functional {K V} (ps : list (K * V)) : Prop :=
  forall x y y', In (x,y) ps -> In (x,y') ps -> y = y'.

Lemma functional_tail {K V} {p : K * V} {qs} :
  functional (p :: qs) -> functional qs.
Proof.
  intros Hfunc k v v' Hin Hin'.
  eapply Hfunc; right; eauto.
Qed.

Lemma in_map_sig {X Y} `{Discrete Y} {f : X -> Y} {xs} {y}
  : In y (map f xs) -> {x : X & f x = y /\ In x xs}.
Proof.
  induction xs as [|x xs'].
  - intros [].
  - intro HIn.
    destruct (eq_dec (f x) y).
    + exists x; split; auto.
      now left.
    + destruct IHxs' as [x' [Hx'1 Hx'2]].
      * destruct HIn; [contradiction|auto].
      * exists x'; split; auto.
        now right.
Defined.

Lemma not_Some_None {X} (o : option X) :
  (forall x, ~ o = Some x) -> o = None.
Proof.
  intro nSome.
  destruct o; [|reflexivity].
  elim (nSome x); reflexivity.
Qed.

Lemma None_or_all_Some {X Y} (f : X -> option Y) (xs : list X) :
  { x : X & f x = None } +
  { ys : list Y & map f xs = map Some ys }.
Proof.
  induction xs as [|x xs'].
  - right.
    exists [].
    reflexivity.
  - destruct (f x) eqn:fx.
    + destruct IHxs' as [[x' Hx']| [ys Hys]].
      * left; now exists x'.
      * right; exists (y :: ys); simpl; congruence.
    + left; now exists x.
Defined.

Lemma list_max_is_max : forall xs x, In x xs -> x <= list_max xs.
Proof.
  intro xs.
  rewrite <- Forall_forall.
  rewrite <- list_max_le.
  constructor.
Qed.

Lemma not_None_in_Somes {X} (xs : list X) :
  ~ In None (map Some xs).
Proof.
  induction xs.
  - intros [].
  - intros [|]; auto.
    congruence.
Qed.

Lemma In_length_pos {X} (xs : list X) : forall x, In x xs ->
  length xs > 0.
Proof.
  destruct xs; intros y HIn.
  - destruct HIn.
  - simpl. apply PeanoNat.Nat.lt_0_succ.
Qed.

Global Instance List_disc {X} `{Discrete X} :
  Discrete (list X).
Proof.
  constructor.
  intro xs; induction xs as [|x xs]; intro ys.
  - destruct ys as [|y ys].
    + now left.
    + now right.
  - destruct ys as [|y ys].
    + now right.
    + destruct (eq_dec x y).
      * destruct (IHxs ys).
        -- left; congruence.
        -- right; intro pf.
           inversion pf; auto.
      * right; intro pf.
        inversion pf; auto.
Defined.

Lemma in_dec {X} `{Discrete X} (x : X) (xs : list X) :
  { In x xs } + { ~ In x xs }.
Proof.
  induction xs as [|x' xs']; simpl.
  - now right.
  - destruct (eq_dec x' x).
    + left; now left.
    + destruct IHxs'.
      * left; now right.
      * right; intros [|]; contradiction.
Defined.

Definition in_decb {X} `{Discrete X} (x : X) (xs : list X) : bool :=
  match in_dec x xs with
  | left _ => true
  | right _ => false
  end.


