
Fixpoint dist (m n : nat) : nat :=
  match m with
  | 0 => n
  | S m' =>
    match n with
    | 0 => m
    | S n' => dist m' n'
    end
  end.

Lemma dist_n_0 : forall n,
  dist n 0 = n.
Proof.
  destruct n; reflexivity.
Qed.

Lemma dist_sym : forall m n,
  dist m n = dist n m.
Proof.
  induction m; intro n.
  - simpl.
    symmetry; apply dist_n_0.
  - simpl.
    destruct n.
    + reflexivity.
    + apply IHm.
Qed.

