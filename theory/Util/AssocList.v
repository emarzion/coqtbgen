Require Import List.
Import ListNotations.

Require Import Games.Util.Dec.

Definition t (K V : Type) : Type :=
  list (K * V).

Definition empty {K V} : t K V := [].

Fixpoint add {K V} `{Discrete K}
  (k : K) (v : V) (ps : t K V) : t K V :=
  match ps with
  | [] => [(k,v)]
  | (k',v') :: qs =>
    match eq_dec k k' with
    | left _ => (k,v) :: qs
    | right _ => (k',v') :: add k v qs
    end
  end.

Fixpoint lookup {K V} `{Discrete K}
  (k : K) (ps : t K V) : option V :=
  match ps with
  | [] => None
  | (k',v) :: qs =>
    match eq_dec k k' with
    | left _ => Some v
    | right _ => lookup k qs
    end
  end.

Definition size {K V} (ps : t K V) : nat :=
  length ps.

Lemma lookup_empty {K V} `{Discrete K} : forall k,
  lookup k (empty : t K V) = None.
Proof.
  auto.
Qed.

Lemma lookup_add {K V} `{Discrete K} : forall (k : K) (v : V) m,
  lookup k (add k v m) = Some v.
Proof.
  intros k v m.
  induction m as [|[k' v'] m'].
  - simpl; now destruct (eq_dec k k).
  - simpl; destruct (eq_dec k k').
    + simpl; now destruct (eq_dec k k).
    + simpl; now destruct (eq_dec k k').
Qed.

Lemma lookup_add_neq {K V} `{Discrete K} : forall (k k' : K) (v : V) m,
  k <> k' -> lookup k (add k' v m) = lookup k m.
Proof.
  intros k k' v m Hkk'.
  induction m as [|[k'' v''] m'].
  - simpl; now destruct (eq_dec k k').
  - simpl; destruct (eq_dec k' k'').
    + simpl; destruct (eq_dec k k'').
      * congruence.
      * now destruct (eq_dec k k').
    + simpl; now rewrite IHm'.
Qed.

Lemma size_empty {K V} : size (empty : t K V) = 0.
Proof.
  reflexivity.
Qed.

Lemma size_add {K V} `{Discrete K} : forall (k : K) (v : V) m,
  size (add k v m) =
    match lookup k m with
    | Some _ => size m
    | None => S (size m)
    end.
Proof.
  intros k v m.
  induction m as [|[k' v'] m'].
  - reflexivity.
  - simpl.
    destruct (eq_dec k k').
    + reflexivity.
    + simpl; destruct (lookup k m'); auto.
Qed.

Definition functional {K V} (ps : list (K * V)) : Prop :=
  forall x y y', In (x,y) ps -> In (x,y') ps -> y = y'.

Lemma functional_tail {K V} {p : K * V} {qs} :
  functional (p :: qs) -> functional qs.
Proof.
  intros Hfunc k v v' Hin Hin'.
  eapply Hfunc; right; eauto.
Qed.
