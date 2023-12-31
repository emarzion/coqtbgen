Require Import Lia.
Require Import List.
Import ListNotations.
Require Import PrimInt63.
Require Import Uint63.

Require Import Games.Util.Dec.
Require Import Games.Util.IntHash.
Require Games.Util.AssocList.

Module AL := AssocList.

Class IntMap (M : Type -> Type) : Type := {
  empty {X} : M X;
  add {X} : int -> X -> M X -> M X;
  lookup {X} : int -> M X -> option X;
  size {X} : M X -> nat;

  lookup_empty {X} : forall k, lookup k (empty : M X) = None;
  lookup_add {X} : forall k (x : X) m, lookup k (add k x m) = Some x;
  lookup_add_neq {X} : forall k k' (x : X) m, k <> k' ->
    lookup k (add k' x m) = lookup k m;
  size_empty {X} : size (empty : M X) = 0;
  size_add {X} : forall k (x : X) m,
    size (add k x m) =
      match lookup k m with
      | Some _ => size m
      | None => S (size m)
      end
  }.

Definition hash_add {M} {X Y} `{IntMap M} `{IntHash X} :
  X -> Y -> M Y -> M Y :=
  fun x => add (hash x).

Definition hash_lookup {M} {X Y} `{IntMap M} `{IntHash X} :
  X -> M Y -> option Y :=
  fun x => lookup (hash x).

Lemma hash_lookup_empty {M} {X Y} `{IntMap M} `{IntHash X} :
  forall x, hash_lookup x (empty : M Y) = None.
Proof.
  intro.
  apply lookup_empty.
Qed.

Lemma hash_lookup_add {M} {X Y} `{IntMap M} `{IntHash X} :
  forall (x : X) (y : Y) m, hash_lookup x (hash_add x y m) = Some y.
Proof.
  intros.
  apply lookup_add.
Qed.

Lemma hash_lookup_add_neq {M} {X Y} `{IntMap M} `{IntHash X} :
  forall (x x' : X) (y : Y) m, x <> x' ->
    hash_lookup x (hash_add x' y m) = hash_lookup x m.
Proof.
  intros x x' y m Hxx'.
  apply lookup_add_neq.
  intro Hhash.
  apply Hxx'.
  now apply hash_inj.
Qed.

Lemma hash_size_add {M} {X Y} `{IntMap M} `{IntHash X} :
  forall (x : X) (y : Y) m,
    size (hash_add x y m) =
      match hash_lookup x m with
      | Some _ => size m
      | None => S (size m)
      end.
Proof.
  intros.
  apply size_add.
Qed.

Fixpoint hash_adds {M} {X Y} `{IntMap M} `{IntHash X}
  (ps : list (X * Y)) (m : M Y) {struct ps} : M Y :=
  match ps with
  | [] => m
  | (x,y) :: qs => hash_adds qs (hash_add x y m)
  end.

Inductive good {M} {X Y} `{IntMap M} `{IntHash X} : M Y -> Prop :=
  | good_e : good empty
  | good_a {x y m} : good m -> hash_lookup x m = None -> good (hash_add x y m).

Fixpoint good_as {M} {X Y} `{IntMap M} `{IntHash X} {ps : list (X * Y)}
  {m : M Y} (pf : good m) (nd : NoDup (map fst ps))
  (disj : forall x y, In (x,y) ps -> hash_lookup x m = None) {struct ps}
  : good (hash_adds ps m).
Proof.
  induction ps as [|[x y] qs].
  - exact pf.
  - simpl.
    apply good_as.
    + apply good_a; auto.
      apply (disj x y); now left.
    + now inversion nd.
    + intros x' y' HIn.
      rewrite hash_lookup_add_neq.
      * apply (disj x' y'); now right.
      * simpl in nd; inversion nd.
        intro Heq.
        apply H3.
        rewrite <- Heq.
        rewrite in_map_iff.
        exists (x', y'); split; auto.
Qed.

Record map_list_equiv {M} {X Y} `{IntMap M} `{IntHash X}
  (m : M Y) (ps : list (X * Y)) : Prop := {
  to_list_size : size m = List.length ps;
  keys_unique : NoDup (map fst ps);
  lookup_in {x y} : hash_lookup x m = Some y <-> In (x,y) ps;
  }.

Lemma hash_adds_add {M} {X Y} `{IntMap M} `{IntHash X}
  {ps : list (X * Y)} : forall x y m,
  hash_add x y (hash_adds ps m) = hash_adds (ps ++ [(x,y)]) m.
Proof.
  induction ps; intros.
  - reflexivity. 
  - simpl.
    destruct a.
    now rewrite IHps.
Qed.

Lemma hash_adds_app {M} {X Y} `{IntMap M} `{IntHash X}
  {ps : list (X * Y)} : forall qs m,
  hash_adds ps (hash_adds qs m) = hash_adds (qs ++ ps) m.
Proof.
  induction ps; intros.
  - simpl; now rewrite app_nil_r.
  - simpl.
    destruct a.
    assert (qs ++ (x,y) :: ps = (qs ++ [(x,y)]) ++ ps)%list.
    { now rewrite <- app_assoc. }
    rewrite H1.
    rewrite <- IHps.
    now rewrite hash_adds_add.
Qed.

Lemma hash_size_add_le {M} {X Y} `{IntMap M} `{IntHash X}
  (x : X) (y : Y) : forall m : M Y,
  size m <= size (hash_add x y m).
Proof.
  intro.
  rewrite hash_size_add.
  destruct hash_lookup; lia.
Qed.

Lemma hash_size_add_lt {M} {X Y} `{IntMap M} `{IntHash X}
  : forall (m : M Y) (x : X) (y : Y),
  hash_lookup x m = None ->
  size m < size (hash_add x y m).
Proof.
  intros m x y Hlookup.
  rewrite hash_size_add.
  rewrite Hlookup.
  lia.
Qed.

Lemma hash_size_adds_le {M} {X Y} `{IntMap M} `{IntHash X}
  (ps : list (X * Y)) : forall m : M Y,
  size m <= size (hash_adds ps m).
Proof.
  induction ps as [|[x y] qs].
  - intro; simpl. lia.
  - intros; simpl.
    simpl.
    apply (PeanoNat.Nat.le_trans _ (size (hash_add x y m))).
    + apply hash_size_add_le.
    + apply IHqs.
Qed.

Lemma hash_adds_ne_pos {M} {X Y} `{IntMap M} `{IntHash X}
  (ps : list (X * Y)) : forall (x : X) (y : Y),
  In (x,y) ps -> size (hash_adds ps empty) > 0.
Proof.
  destruct ps as [|[x' y'] qs]; intros.
  - destruct H1.
  - simpl.
    pose proof (hash_size_adds_le qs (hash_add x' y' empty)).
    rewrite hash_size_add in H2.
    rewrite hash_lookup_empty in H2.
    lia.
Qed.

Lemma hash_size_adds {M} {X Y} `{IntMap M} `{IntHash X}
  (ps : list (X * Y)) : forall m : M Y,
  NoDup (map fst ps) ->
  (forall x, In x (map fst ps) -> hash_lookup x m = None) ->
  size (hash_adds ps m) = List.length ps + size m.
Proof.
  induction ps as [|[x y] qs]; intros m ndps Hpsm.
  - reflexivity.
  - simpl.
    rewrite IHqs.
    + rewrite hash_size_add.
      rewrite Hpsm.
      * apply PeanoNat.Nat.add_succ_r.
      * left; reflexivity.
    + now inversion ndps.
    + intros.
      rewrite hash_lookup_add_neq.
      * apply Hpsm.
        right; auto.
      * intro Hx0x.
        rewrite Hx0x in H1.
        now inversion ndps.
Qed.

Global Instance int_Discrete : Discrete int.
Proof.
  constructor.
  intros x y.
  destruct (eqb x y) eqn:Heq.
  - left.
    rewrite eqb_spec in Heq.
    exact Heq.
  - right.
    rewrite eqb_false_spec in Heq.
    exact Heq.
Defined.

Lemma hash_lookup_adds_invert {M} {X Y} `{IntMap M} `{IntHash X}
  (ps : list (X * Y)) : forall (m : M Y) (x : X) (y : Y),
  hash_lookup x (hash_adds ps m) = Some y ->
  {In (x,y) ps} + {hash_lookup x m = Some y}.
Proof.
  induction ps as [|[x y] qs]; intros m x' y' Hx'.
  - right. exact Hx'.
  - simpl in Hx'.
    destruct (IHqs _ _ _ Hx').
    + left; now right.
    + destruct (eq_dec (hash x') (hash x)).
      * assert (x' = x) as Hx'x by now apply hash_inj.
        rewrite Hx'x in e.
        rewrite hash_lookup_add in e.
        left; left; congruence.
      * rewrite hash_lookup_add_neq in e.
        ** now right.
        ** intro Hx'x.
           now rewrite Hx'x in n.
Defined.

Lemma good_to_list {M} {X Y} `{IntHash X} `{IntMap M}
  (m : M Y) (g : good m) : exists (ps : list (X * Y)), map_list_equiv m ps.
Proof.
  induction g.
  - exists nil; constructor.
    + now rewrite size_empty.
    + constructor.
    + intros x y.
      unfold hash_lookup.
      now rewrite lookup_empty.
  - destruct IHg as [ps [tl_sz key_un l_in]].
    exists ((x,y) :: ps); constructor.
    + unfold hash_add.
      unfold hash_lookup in H1.
      rewrite size_add.
      rewrite H1.
      simpl; congruence.
    + simpl; constructor; auto.
      intro HIn.
      rewrite in_map_iff in HIn.
      destruct HIn as [[str x'] [Hx1 Hx2]].
      simpl in *.
      rewrite Hx1 in Hx2.
      rewrite <- l_in in Hx2; congruence.
    + intros.
      unfold hash_lookup, hash_add.
      destruct (eq_dec (hash x0) (hash x)).
      * rewrite e.
        rewrite lookup_add.
        split; intro.
        -- pose (hash_inj _ _ e).
           left; congruence.
        -- destruct H2; [congruence|].
           rewrite <- l_in in H2.
           pose (hash_inj _ _ e); congruence.
      * rewrite lookup_add_neq; auto.
        unfold hash_lookup in l_in.
        rewrite l_in.
        split; intro; [now right|].
        destruct H2; [congruence|auto].
Qed.

Lemma hash_lookup_adds_None_invert {M} {X Y} `{IntMap M} `{IntHash X}
  {ps} : forall {m : M Y} {x : X},
  hash_lookup x (hash_adds ps m) = None ->
  (~ In x (List.map fst ps)) /\
  hash_lookup x m = None.
Proof.
  induction ps as [|[x y] qs]; intros m x' Hx'.
  - split.
    + intros [].
    + exact Hx'.
  - simpl in *.
    destruct (IHqs _ _ Hx').
    split.
    + intros [|].
      * rewrite H3 in H2.
        now rewrite hash_lookup_add in H2.
      * contradiction.
    + destruct (eq_dec (hash x') (hash x)).
      * rewrite (hash_inj _ _ e) in H2.
        now rewrite hash_lookup_add in H2.
      * rewrite hash_lookup_add_neq in H2; auto.
        congruence.
Qed.

Lemma hash_lookup_adds_nIn {M} {X Y} `{IntMap M} `{IntHash X} :
  forall (ps : list (X * Y)) (x : X) m,
    ~ In x (List.map fst ps) ->
    hash_lookup x (hash_adds ps m) = hash_lookup x m.
Proof.
  intro ps.
  induction ps as [|[x y] qs]; intros x' m nIn.
  - reflexivity.
  - simpl.
    rewrite IHqs.
    + rewrite hash_lookup_add_neq.
      * reflexivity.
      * intro Hxx'; apply nIn.
        left; symmetry; exact Hxx'.
    + intro HIn; apply nIn.
      right; auto.
Qed.

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

Definition in_decb {X} `{Discrete X} (x : X) (xs : list X) :=
  match in_dec x xs with
  | left _ => true
  | right _ => false
  end.

Global Instance Hash_disc {X} `{IntHash X} : Discrete X.
Proof.
  constructor.
  intros x y.
  destruct (eq_dec (hash x) (hash y)).
  - left.
    now apply hash_inj.
  - right; congruence.
Defined.

Lemma hash_lookup_adds {M} {X Y} `{IntMap M} `{IntHash X}
  (ps : list (X * Y)) : forall m : M Y, AL.functional ps ->
  forall (x : X) (y : Y), In (x,y) ps ->
  hash_lookup x (hash_adds ps m) = Some y.
Proof.
  induction ps as [|[x y] qs]; intros m ndkeys x' y' HIn.
  - destruct HIn.
  - simpl in *.
    destruct HIn.
    + inversion H1; subst.
      destruct (in_dec x' (map fst qs)).
      * apply (IHqs (hash_add x' y' m));
          [exact (AL.functional_tail ndkeys)|].
        unfold AL.functional in ndkeys.
        rewrite in_map_iff in i.
        destruct i as [[u v] [Heq HIn]].
        simpl in Heq; subst.
        rewrite (ndkeys x' y' v); auto.
        ** now left.
        ** now right.
      * rewrite hash_lookup_adds_nIn; auto.
        apply hash_lookup_add.
    + apply IHqs; auto.
      exact (AL.functional_tail ndkeys).
Qed.

Global Instance AssocList_SM : IntMap (AL.t int) := {|
  empty X := AL.empty;
  add X := AL.add;
  lookup X := AL.lookup;
  size X := AL.size;

  lookup_empty X := AL.lookup_empty;
  lookup_add X := AL.lookup_add;
  lookup_add_neq X := AL.lookup_add_neq;
  size_empty X := AL.size_empty;
  size_add X := AL.size_add;
  |}.
