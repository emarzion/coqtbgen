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

Lemma str_lookup_adds {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall m : M Y, AL.functional ps ->
  forall (x : X) (y : Y), In (x,y) ps ->
  str_lookup x (str_adds ps m) = Some y.
Proof.
  induction ps as [|[x y] qs]; intros m ndkeys x' y' HIn.
  - destruct HIn.
  - simpl in *.
    destruct HIn.
    + inversion H1.
      rewrite str_lookup_adds_nIn.
      * admit.
      * admit.
Admitted.


(*
Lemma str_lookup_adds {M} {X Y} `{StringMap M} `{Show X}
  (ps : list (X * Y)) : forall m : M Y, NoDup (List.map fst ps) ->
  forall (x : X) (y : Y), In (x,y) ps ->
  str_lookup x (str_adds ps m) = Some y.
Proof.
  induction ps as [|[x y] qs]; intros m ndkeys x' y' HIn.
  - destruct HIn.
  - simpl in *.
    inversion ndkeys.
    destruct HIn.
    + inversion H5.
      rewrite str_lookup_adds_nIn.
      * apply str_lookup_add.
      * congruence.
    + now apply IHqs.
Qed.
*)

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
