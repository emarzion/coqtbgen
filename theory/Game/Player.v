Require Import Games.Util.Dec.

Inductive Player :=
  | White : Player
  | Black : Player.

#[export]
Instance Player_Discrete : Discrete Player.
Proof.
  constructor; unfold decision; decide equality.
Defined.

Definition opp : Player -> Player :=
  fun p =>
    match p with
    | White => Black
    | Black => White
    end.

Lemma opp_invol : forall p, opp (opp p) = p.
Proof.
  intro p; destruct p; reflexivity.
Qed.

Lemma opp_inj : forall p p',
  opp p = opp p' -> p = p'.
Proof.
  intros p p' Hpp'.
  destruct p, p'; auto.
Qed.

Lemma player_id_or_opp : forall p p',
  p = p' \/ opp p = p'.
Proof.
  destruct p, p'; auto.
Qed.

Lemma player_id_or_opp_r_t : forall p p',
  { p = p' } + { p = opp p' }.
Proof.
  intros.
  destruct p, p'; auto.
Defined.

Lemma opp_no_fp : forall p, opp p <> p.
Proof.
  destruct p; discriminate.
Qed.

Definition player_eqb (p1 p2 : Player) : bool :=
  match p1, p2 with
  | White, White => true
  | Black, Black => true
  | _, _ => false
  end.

Lemma player_eqb_true : forall p1 p2,
  player_eqb p1 p2 = true -> p1 = p2.
Proof.
  intros [] [] pf; (reflexivity || discriminate).
Qed.

Lemma player_eqb_false : forall p1 p2,
  player_eqb p1 p2 = false -> p1 = opp p2.
Proof.
  intros [] [] pf; (reflexivity || discriminate).
Qed.
