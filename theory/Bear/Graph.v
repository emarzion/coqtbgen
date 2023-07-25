
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Games.Bear.Sort.

Require Import Games.Util.Dec.

Class Enum (X : Type) : Type := {
  enum : list X;
  enum_correct : forall x : X, In x enum
  }.

Record Graph : Type := {
  Vert : Type;

  Vert_disc : Discrete Vert;
  Vert_enum : Enum Vert;

  successors : Vert -> list Vert;
  }.

Arguments successors {_} _.

Global Instance Graph_Vert_disc (G : Graph) : Discrete (Vert G) :=
  Vert_disc G.

Global Instance Graph_Vert_enum (G : Graph) : Enum (Vert G) :=
  Vert_enum G.

Fixpoint first_index_aux {X} `{Discrete X} n xs (x : X) : option nat :=
  match xs with
  | [] => None
  | y :: ys =>
    match eq_dec x y with
    | left _ => Some n
    | right _ => first_index_aux (S n) ys x
    end
  end.

Definition opt_le (o1 o2 : option nat) : Prop :=
  match o1, o2 with
  | None, _ => True
  | Some x, None => False
  | Some x, Some y => x <= y
  end.

(*
Global Instance Ord_nat : Ord nat.
Proof.
  refine {|
    ord_le := le
  |}.
  - apply PeanoNat.Nat.le_trans.
  - intros x y; destruct (Compare_dec.le_dec x y).
    + now left.
    + right; lia.
Defined.
*)

Lemma first_index_aux_bound {X} `{Discrete X} {xs} : forall {n x k},
  first_index_aux n xs x = Some k -> n <= k.
Proof.
  induction xs; intros n x k Hx.
  - now discriminate.
  - simpl in Hx.
    destruct (eq_dec x a).
    + inversion Hx; lia.
    + pose (IHxs _ _ _ Hx); lia.
Defined.

Lemma first_index_aux_inj {X} `{Discrete X} xs : forall n (x x' : X) k k',
  first_index_aux n xs x = Some k ->
  first_index_aux n xs x' = Some k' ->
  k = k' -> x = x'.
Proof.
  induction xs; intros n x x' k k' Hx Hx' Hkk'.
  - now discriminate.
  - simpl in *.
    destruct (eq_dec x a), (eq_dec x' a).
    + congruence.
    + inversion Hx; subst.
      pose (first_index_aux_bound Hx'); lia.
    + inversion Hx'; subst.
      pose (first_index_aux_bound Hx); lia.
    + eapply IHxs; eauto.
Qed.

Lemma first_index_aux_In {X} `{Discrete X} {xs} : forall n {x},
  In x xs -> { k : nat & first_index_aux n xs x = Some k }.
Proof.
  induction xs; intros n x HIn.
  - destruct HIn.
  - simpl.
    destruct (eq_dec x a).
    + exists n; reflexivity.
    + apply IHxs.
      destruct HIn; [congruence|auto].
Defined.

(*
Definition inj_nat {X} `{Discrete X} `{Enum X} : X -> nat :=
  fun x => projT1 (first_index_aux_In 0 (enum_correct x)).
*)

(*
Lemma inj_nat_correct {X} `{Discrete X} `{Enum X} :
  forall (x x' : X), inj_nat x = inj_nat x' -> x = x'.
Proof.
  intros x x' Hxx'.
  unfold inj_nat in Hxx'.
  destruct (first_index_aux_In 0 (enum_correct x)) as [n Hn].
  destruct (first_index_aux_In 0 (enum_correct x')) as [m Hm].
  simpl in Hxx'; subst.
  eapply first_index_aux_inj; eauto.
Qed.
*)

Global Instance subcount_Ord {X} `{Discrete X, Enum X} : Ord X.
Proof.
  refine {|
    ord_le := fun x y => opt_le (first_index_aux 0 enum x) (first_index_aux 0 enum y);
    ord_le_trans := _;
    ord_le_dec := _
  |}.
  - intros x y z Hxy Hyz.
    unfold opt_le in *.
    destruct (first_index_aux_In 0 (enum_correct x)) as [a Ha].
    destruct (first_index_aux_In 0 (enum_correct y)) as [b Hb].
    destruct (first_index_aux_In 0 (enum_correct z)) as [c Hc].
    rewrite Ha, Hb, Hc in *.
    now apply (PeanoNat.Nat.le_trans _ b).
  - intros x y.
    unfold opt_le.
    destruct (first_index_aux_In 0 (enum_correct x)) as [a Ha].
    destruct (first_index_aux_In 0 (enum_correct y)) as [b Hb].
    rewrite Ha, Hb.
    destruct (Compare_dec.le_le_S_dec a b).
    + now left.
    + right; lia.
Defined.

(*
H2 : Forall (R (f a)) (map f xs)
H : a0 = f a
H0 : l = map f xs
______________________________________(1/1)
Forall (fun y : X => R (f a) (f y)) xs
*)

Lemma Forall_map_lemma {X Y} (f : X -> Y) (P : Y -> Prop) : forall xs,
  Forall P (map f xs) -> Forall (fun x => P (f x)) xs.
Proof.
  induction xs as [|x xs']; intro HP.
  - constructor.
  - inversion HP; constructor; auto.
Qed.

Lemma sort_map_lemma {X Y} (f : X -> Y) (R : Y -> Y -> Prop) :
  forall xs, Sorted.StronglySorted R (map f xs) ->
  Sorted.StronglySorted (fun x y => R (f x) (f y)) xs.
Proof.
  induction xs; intros HR.
  - constructor.
  - inversion HR.
    constructor.
    + now apply IHxs.
    + now apply Forall_map_lemma.
Qed.

Lemma map_ext_lemma {X Y} (f g : X -> Y) :
  forall xs, (forall x, In x xs -> f x = g x) ->
  map f xs = map g xs.
Proof.
  induction xs; intro Hfg.
  - reflexivity.
  - simpl.
    rewrite Hfg; [|now left].
    rewrite IHxs; [reflexivity|].
    intros x Hx.
    apply Hfg; now right.
Qed.

Lemma first_index_aux_NoDup_bound {X} `{Discrete X} : forall (xs : list X),
  NoDup xs -> forall m n, m <= n ->
  Forall (opt_le (Some m)) (map (first_index_aux n xs) xs).
Proof.
  induction xs as [|x xs']; intros pf m n Hmn.
  - constructor.
  - simpl; constructor.
    + simpl; destruct (eq_dec x x); [lia|contradiction].
    + simpl.
      assert (
        map (fun y =>
          if eq_dec y x then Some n else first_index_aux (S n) xs' y) xs' =
        map (first_index_aux (S n) xs') xs') as eq_pf.
      { apply map_ext_lemma.
        intros y Hy.
        destruct (eq_dec y x); [|reflexivity].
        inversion pf; congruence.
      }
      rewrite eq_pf.
      apply IHxs'; [|lia].
      now inversion pf.
Qed.

Lemma first_index_aux_NoDup_sorted {X} `{Discrete X}
  : forall (xs : list X), NoDup xs -> forall n,
  Sorted.StronglySorted opt_le (map (first_index_aux n xs) xs).
Proof.
  induction xs; intros.
  - constructor.
  - simpl.
    destruct (eq_dec a a); [|contradiction].
    assert (
      map (fun x =>
        if eq_dec x a then Some n else first_index_aux (S n) xs x) xs =
      map (first_index_aux (S n) xs) xs) as pf.
    { apply map_ext_lemma.
      intros x Hx.
      destruct (eq_dec x a); [|reflexivity].
      inversion H0.
      congruence.
    }
    rewrite pf.
    constructor.
    + apply IHxs.
      now inversion H0.
    + apply first_index_aux_NoDup_bound; [|lia].
      now inversion H0.
Qed.

Lemma enum_sorted {X} `{Discrete X, Enum X} :
  NoDup enum -> sorted (enum : list X).
Proof.
  unfold sorted.
  unfold ord_le.
  unfold subcount_Ord.
  intro.
  apply sort_map_lemma.
  now apply first_index_aux_NoDup_sorted.
Qed.
