Require Import List.
Import ListNotations.

Require Import Games.Util.Dec.

Record t (K V : Type) : Type := {
  assoc_list : list (K * V);
  nd_keys : NoDup (map fst assoc_list);
  }.

Arguments assoc_list {_} {_} _.
Arguments nd_keys {_} {_} _.

Definition empty {K V} : t K V := {|
  assoc_list := [];
  nd_keys := NoDup_nil _;
  |}.

Fixpoint al_add {K V} `{Discrete K}
  (k : K) (v : V) (ps : list (K * V)) : list (K * V) :=
  match ps with
  | [] => [(k,v)]
  | (k',v') :: qs =>
    match eq_dec k k' with
    | left _ => (k,v) :: qs
    | right _ => (k',v') :: al_add k v qs
    end
  end.

Lemma In_al_add_inv {K V} `{Discrete K} (k : K) (v : V) p m :
  In p (al_add k v m) -> p = (k, v) \/ In p m.
Proof.
  induction m as [|[k' v'] l]; intro pf.
  - left; destruct pf as [|[]].
    congruence.
  - simpl in pf.
    destruct eq_dec.
    + subst.
      destruct pf.
      * left; congruence.
      * right; right; auto.
    + destruct pf as [pf|pf].
      * right; left; congruence.
      * apply IHl in pf.
        destruct pf.
        -- now left.
        -- right; now right.
Qed.

Lemma al_add_NoDup {K V} `{Discrete K} {k} {v} {ps : list (K * V)} :
  NoDup (map fst ps) ->
  NoDup (map fst (al_add k v ps)).
Proof.
  induction ps as [|[k' v'] l']; intro pf.
  - constructor; [|constructor].
    intros [].
  - simpl in *.
    destruct eq_dec; simpl.
    + congruence.
    + constructor.
      * intro Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as [[k'' v''] [pf1 pf2]].
        simpl in *; subst.
        apply In_al_add_inv in pf2.
        destruct pf2 as [pf2|pf2].
        -- congruence.
        -- rewrite NoDup_cons_iff in pf.
           destruct pf as [pf _].
           apply pf.
           apply in_map with (f := fst) in pf2; auto.
      * apply IHl'.
        inversion pf; auto.
Qed.

Definition add {K V} `{Discrete K} (k : K) (v : V) (m : t K V) : t K V := {|
  assoc_list := al_add k v (assoc_list m);
  nd_keys := al_add_NoDup (nd_keys m);
  |}.

Fixpoint al_lookup {K V} `{Discrete K}
  (k : K) (ps : list (K * V)) : option V :=
  match ps with
  | [] => None
  | (k',v) :: qs =>
    match eq_dec k k' with
    | left _ => Some v
    | right _ => al_lookup k qs
    end
  end.

Definition lookup {K V} `{Discrete K} (k : K) (m : t K V) : option V :=
  al_lookup k (assoc_list m).

Lemma lookup_empty {K V} `{Discrete K} : forall k,
  lookup k (empty : t K V) = None.
Proof.
  auto.
Qed.

Lemma lookup_add {K V} `{Discrete K} : forall (k : K) (v : V) m,
  lookup k (add k v m) = Some v.
Proof.
  unfold lookup.
  intros k v [m nd]; simpl; clear nd.
  induction m as [|[k' v'] m'].
  - simpl; now destruct (eq_dec k k).
  - simpl; destruct (eq_dec k k').
    + simpl; now destruct (eq_dec k k).
    + simpl; now destruct (eq_dec k k').
Qed.

Lemma lookup_add_neq {K V} `{Discrete K} : forall (k k' : K) (v : V) m,
  k <> k' -> lookup k (add k' v m) = lookup k m.
Proof.
  unfold lookup.
  intros k k' v [m nd] Hkk'; simpl; clear nd.
  induction m as [|[k'' v''] m'].
  - simpl; now destruct (eq_dec k k').
  - simpl; destruct (eq_dec k' k'').
    + simpl; destruct (eq_dec k k'').
      * congruence.
      * now destruct (eq_dec k k').
    + simpl; now rewrite IHm'.
Qed.

Definition to_list {K V} (m : t K V) : list (K * V) :=
  assoc_list m.

Lemma to_list_lookup {K V} `{Discrete K} (m : t K V) k v :
  In (k, v) (to_list m) -> lookup k m = Some v.
Proof.
  unfold to_list, lookup.
  destruct m as [l nd]; simpl.
  induction l as [|[k' v'] l']; intro pf.
  - destruct pf.
  - destruct pf as [pf|pf]; simpl in *.
    + inversion pf.
      destruct eq_dec; auto.
      contradiction.
    + rewrite NoDup_cons_iff in nd.
      destruct nd as [nIn nd].
      destruct eq_dec.
      * subst; simpl in *.
        elim nIn.
        apply in_map with (f := fst) in pf; auto.
      * apply IHl'; auto.
Qed.

Lemma lookup_to_list {K V} `{Discrete K} (m : t K V) k v :
  lookup k m = Some v -> In (k, v) (to_list m).
Proof.
  unfold to_list, lookup.
  destruct m as [l nd]; simpl; clear nd.
  induction l as [|[k' v'] l']; intro pf.
  - discriminate.
  - simpl in pf.
    destruct eq_dec.
    + left; congruence.
    + right; apply IHl'; auto.
Qed.

Lemma to_list_NoDup_keys {K V} `{Discrete K} (m : t K V) :
  NoDup (map fst (to_list m)).
Proof.
  apply m.
Qed.

Definition size {K V} (m : t K V) : nat :=
  length (assoc_list m).

Lemma size_to_list {K V} (m : t K V) :
  size m = length (to_list m).
Proof.
  reflexivity.
Qed.
