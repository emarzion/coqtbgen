Require Import Lia.
Require Import List.
Import ListNotations.
Require Import String.

Require Import Games.Util.Dec.
Require Import Games.Util.Show.
Require Games.Util.AssocList.

Module AL := AssocList.

Class StringMap (M : Type -> Type) : Type := {
  empty {X} : M X;
  add {X} : string -> X -> M X -> M X;
  lookup {X} : string -> M X -> option X;
  size {X} : M X -> nat;

  lookup_empty {X} : forall str, lookup str (empty : M X) = None;
  lookup_add {X} : forall str (x : X) m, lookup str (add str x m) = Some x;
  lookup_add_neq {X} : forall str str' (x : X) m, str <> str' ->
    lookup str (add str' x m) = lookup str m;
  size_empty {X} : size (empty : M X) = 0;
  size_add {X} : forall str (x : X) m,
    size (add str x m) =
      match lookup str m with
      | Some _ => size m
      | None => S (size m)
      end
  }.

Definition str_add {M} {X Y} `{StringMap M} `{Show X} :
  X -> Y -> M Y -> M Y :=
  fun x => add (show x).

Definition str_lookup {M} {X Y} `{StringMap M} `{Show X} :
  X -> M Y -> option Y :=
  fun x => lookup (show x).

Lemma str_lookup_empty {M} {X Y} `{StringMap M} `{Show X} :
  forall x, str_lookup x (empty : M Y) = None.
Proof.
  intro.
  apply lookup_empty.
Qed.

Lemma str_lookup_add {M} {X Y} `{StringMap M} `{Show X} :
  forall (x : X) (y : Y) m, str_lookup x (str_add x y m) = Some y.
Proof.
  intros.
  apply lookup_add.
Qed.

Lemma str_lookup_add_neq {M} {X Y} `{StringMap M} `{Show X} :
  forall (x x' : X) (y : Y) m, x <> x' ->
    str_lookup x (str_add x' y m) = str_lookup x m.
Proof.
  intros x x' y m Hxx'.
  apply lookup_add_neq.
  intro Hshow.
  apply Hxx'.
  now apply show_inj.
Qed.

Lemma str_size_add {M} {X Y} `{StringMap M} `{Show X} :
  forall (x : X) (y : Y) m,
    size (str_add x y m) =
      match str_lookup x m with
      | Some _ => size m
      | None => S (size m)
      end.
Proof.
  intros.
  apply size_add.
Qed.

Fixpoint str_adds {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) (m : M Y) {struct ps} : M Y :=
  match ps with
  | [] => m
  | (x,y) :: qs => str_adds qs (str_add x y m)
  end.

Inductive good {M} {X Y} `{StringMap M} `{Show X} : M Y -> Prop :=
  | good_e : good empty
  | good_a {x y m} : good m -> str_lookup x m = None -> good (str_add x y m).

Fixpoint good_as {M} {X Y} `{StringMap M} `{Show X} {ps : list (X * Y)}
  {m : M Y} (pf : good m) (nd : NoDup (map fst ps))
  (disj : forall x y, In (x,y) ps -> str_lookup x m = None) {struct ps}
  : good (str_adds ps m).
Proof.
  induction ps as [|[x y] qs].
  - exact pf.
  - simpl.
    apply good_as.
    + apply good_a; auto.
      apply (disj x y); now left.
    + now inversion nd.
    + intros x' y' HIn.
      rewrite str_lookup_add_neq.
      * apply (disj x' y'); now right.
      * simpl in nd; inversion nd.
        intro Heq.
        apply H3.
        rewrite <- Heq.
        rewrite in_map_iff.
        exists (x', y'); split; auto.
Qed.

Record map_list_equiv {M} {X Y} `{Show X} `{StringMap M}
  (m : M Y) (ps : list (X * Y)) : Prop := {
  to_list_size : size m = List.length ps;
  keys_unique : NoDup (map fst ps);
  lookup_in {x y} : str_lookup x m = Some y <-> In (x,y) ps;
  }.

Lemma str_adds_add {M} {X Y} `{StringMap M} `{Show X}
  {ps : list (X * Y)} : forall x y m,
  str_add x y (str_adds ps m) = str_adds (ps ++ [(x,y)]) m.
Proof.
  induction ps; intros.
  - reflexivity. 
  - simpl.
    destruct a.
    now rewrite IHps.
Qed.

Lemma str_adds_app {M} {X Y} `{StringMap M} `{Show X}
  {ps : list (X * Y)} : forall qs m,
  str_adds ps (str_adds qs m) = str_adds (qs ++ ps) m.
Proof.
  induction ps; intros.
  - simpl; now rewrite app_nil_r.
  - simpl.
    destruct a.
    assert (qs ++ (x,y) :: ps = (qs ++ [(x,y)]) ++ ps)%list.
    { now rewrite <- app_assoc. }
    rewrite H1.
    rewrite <- IHps.
    now rewrite str_adds_add.
Qed.

Lemma str_size_add_le {M} {X Y} `{StringMap M} `{Show X}
  (x : X) (y : Y) : forall m : M Y,
  size m <= size (str_add x y m).
Proof.
  intro.
  rewrite str_size_add.
  destruct str_lookup; lia.
Qed.

Lemma str_size_add_lt {M} {X Y} `{StringMap M} `{Show X}
  : forall (m : M Y) (x : X) (y : Y),
  str_lookup x m = None ->
  size m < size (str_add x y m).
Proof.
  intros.
  rewrite str_size_add.
  rewrite H1.
  lia.
Qed.

Lemma str_size_adds_le {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall m : M Y,
  size m <= size (str_adds ps m).
Proof.
  induction ps as [|[x y] qs].
  - intro; simpl. lia.
  - intros; simpl.
    simpl.
    apply (PeanoNat.Nat.le_trans _ (size (str_add x y m))).
    + apply str_size_add_le.
    + apply IHqs.
Qed.

Lemma str_adds_ne_pos {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall (x : X) (y : Y),
  In (x,y) ps -> size (str_adds ps empty) > 0.
Proof.
  destruct ps as [|[x' y'] qs]; intros.
  - destruct H1.
  - simpl.
    pose proof (str_size_adds_le qs (str_add x' y' empty)).
    rewrite str_size_add in H2.
    rewrite str_lookup_empty in H2.
    lia.
Qed.

Lemma str_size_adds {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall m : M Y,
  NoDup (map fst ps) ->
  (forall x, In x (map fst ps) -> str_lookup x m = None) ->
  size (str_adds ps m) = List.length ps + size m.
Proof.
  induction ps as [|[x y] qs]; intros m ndps Hpsm.
  - reflexivity.
  - simpl.
    rewrite IHqs.
    + rewrite str_size_add.
      rewrite Hpsm.
      * apply PeanoNat.Nat.add_succ_r.
      * left; reflexivity.
    + now inversion ndps.
    + intros.
      rewrite str_lookup_add_neq.
      * apply Hpsm.
        right; auto.
      * intro Hx0x.
        rewrite Hx0x in H1.
        now inversion ndps.
Qed.

Global Instance string_Discrete : Discrete string := {|
  eq_dec := string_dec
  |}.

Lemma str_lookup_adds_invert {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall (m : M Y) (x : X) (y : Y),
  str_lookup x (str_adds ps m) = Some y ->
  {In (x,y) ps} + {str_lookup x m = Some y}.
Proof.
  induction ps as [|[x y] qs]; intros m x' y' Hx'.
  - right. exact Hx'.
  - simpl in Hx'.
    destruct (IHqs _ _ _ Hx').
    + left; now right.
    + destruct (eq_dec (show x') (show x)).
      * assert (x' = x) as Hx'x by now apply show_inj.
        rewrite Hx'x in e.
        rewrite str_lookup_add in e.
        left; left; congruence.
      * rewrite str_lookup_add_neq in e.
        ** now right.
        ** intro Hx'x.
           now rewrite Hx'x in n.
Defined.

Lemma good_to_list {M} {X Y} `{Show X} `{StringMap M}
  (m : M Y) (g : good m) : exists (ps : list (X * Y)), map_list_equiv m ps.
Proof.
  induction g.
  - exists nil; constructor.
    + now rewrite size_empty.
    + constructor.
    + intros x y.
      unfold str_lookup.
      now rewrite lookup_empty.
  - destruct IHg as [ps [tl_sz key_un l_in]].
    exists ((x,y) :: ps); constructor.
    + unfold str_add.
      unfold str_lookup in H1.
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
      unfold str_lookup, str_add.
      destruct (string_dec (show x0) (show x)).
      * rewrite e.
        rewrite lookup_add.
        split; intro.
        -- pose (show_inj _ _ e).
           left; congruence.
        -- destruct H2; [congruence|].
           rewrite <- l_in in H2.
           pose (show_inj _ _ e); congruence.
      * rewrite lookup_add_neq; auto.
        unfold str_lookup in l_in.
        rewrite l_in.
        split; intro; [now right|].
        destruct H2; [congruence|auto].
Qed.

Lemma str_lookup_adds_None_invert {M} {X Y} `{StringMap M} `{Show X}
  {ps} : forall {m : M Y} {x : X},
  str_lookup x (str_adds ps m) = None ->
  (~ In x (List.map fst ps)) /\
  str_lookup x m = None.
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
        now rewrite str_lookup_add in H2.
      * contradiction.
    + destruct (eq_dec (show x') (show x)).
      * rewrite (show_inj _ _ e) in H2.
        now rewrite str_lookup_add in H2.
      * rewrite str_lookup_add_neq in H2; auto.
        congruence.
Qed.

Lemma str_lookup_adds_nIn {M} {X Y} `{StringMap M} `{Show X} :
  forall (ps : list (X * Y)) (x : X) m,
    ~ In x (List.map fst ps) ->
    str_lookup x (str_adds ps m) = str_lookup x m.
Proof.
  intro ps.
  induction ps as [|[x y] qs]; intros x' m nIn.
  - reflexivity.
  - simpl.
    rewrite IHqs.
    + rewrite str_lookup_add_neq.
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

Global Instance Show_disc {X} `{Show X} : Discrete X.
Proof.
  constructor.
  apply Show_dec.
Defined.

Lemma str_lookup_adds {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall m : M Y, AL.functional ps ->
  forall (x : X) (y : Y), In (x,y) ps ->
  str_lookup x (str_adds ps m) = Some y.
Proof.
  induction ps as [|[x y] qs]; intros m ndkeys x' y' HIn.
  - destruct HIn.
  - simpl in *.
    destruct HIn.
    + inversion H1; subst.
      destruct (in_dec x' (map fst qs)).
      * apply (IHqs (str_add x' y' m));
          [exact (AL.functional_tail ndkeys)|].
        unfold AL.functional in ndkeys.
        rewrite in_map_iff in i.
        destruct i as [[u v] [Heq HIn]].
        simpl in Heq; subst.
        rewrite (ndkeys x' y' v); auto.
        ** now left.
        ** now right.
      * rewrite str_lookup_adds_nIn; auto.
        apply str_lookup_add.
    + apply IHqs; auto.
      exact (AL.functional_tail ndkeys).
Qed.

Global Instance AssocList_SM : StringMap (AL.t string) := {|
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
