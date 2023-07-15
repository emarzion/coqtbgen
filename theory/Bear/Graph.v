
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

Fixpoint first_index_aux {X} `{Discrete X} n (x : X) xs : option nat :=
  match xs with
  | [] => None
  | y :: ys =>
    match eq_dec x y with
    | left _ => Some n
    | right _ => first_index_aux (S n) x ys
    end
  end.

Lemma first_index_aux_bound {X} `{Discrete X} {xs} : forall {n x k},
  first_index_aux n x xs = Some k -> n <= k.
Proof.
  induction xs; intros n x k Hx.
  - now discriminate.
  - simpl in Hx.
    destruct (eq_dec x a).
    + inversion Hx; lia.
    + pose (IHxs _ _ _ Hx); lia.
Defined.

Lemma first_index_aux_inj {X} `{Discrete X} xs : forall n (x x' : X) k k',
  first_index_aux n x xs = Some k ->
  first_index_aux n x' xs = Some k' ->
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
  In x xs -> {k : nat & first_index_aux n x xs = Some k}.
Proof.
  induction xs; intros n x HIn.
  - destruct HIn.
  - simpl.
    destruct (eq_dec x a).
    + exists n; reflexivity.
    + apply IHxs.
      destruct HIn; [congruence|auto].
Defined.

Definition inj_nat {X} `{Discrete X} `{Enum X} : X -> nat :=
  fun x => projT1 (first_index_aux_In 0 (enum_correct x)).

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

Global Instance subcount_Ord {X} `{Discrete X, Enum X} : Ord X.
Proof.
  refine {|
    ord_le := fun x y => inj_nat x <= inj_nat y;
    ord_le_trans := _;
    ord_le_dec := _
  |}.
  - intros; eapply PeanoNat.Nat.le_trans; eauto.
  - intros.
    destruct (Compare_dec.le_le_S_dec (inj_nat x) (inj_nat y)).
    + now left.
    + right; lia.
Defined.
