Require Import List.
Import ListNotations.

Require Import Games.Game.Game.
Require Import TBGen.Util.Bisim.

Class Closed {G} (P : GameState G -> Prop) : Prop := {
  closed : forall s, P s -> forall m, P (exec_move s m)
  }.

Class Bisim_closed {G} (B : InvertibleBisim G G)
  (P : GameState G -> Prop) : Prop := {
  bisim_closed : forall s s', P s -> bisim G G B s s' -> P s'
  }.

Class Dec1 {X} (P : X -> Prop) := {
  dec1 : forall x, {P x} + {~ P x}
  }.

Fixpoint filter_dec {X} (P : X -> Prop) `{Dec1 X P} (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' =>
    match dec1 x with
    | left _ => x :: filter_dec P xs'
    | right _ => filter_dec P xs'
    end
  end.

Lemma filter_dec_In {X} (P : X -> Prop) `{Dec1 X P} (xs : list X) :
  forall x, In x (filter_dec P xs) <-> In x xs /\ P x.
Proof.
  induction xs.
  - intro x; split; intro pf.
    + destruct pf.
    + destruct pf as [[]].
  - intro x; split; intro pf.
    + simpl in pf.
      destruct (dec1 a).
      * destruct pf.
        -- subst; split; auto.
           now left.
        -- apply IHxs in H0; destruct H0.
           split; auto.
           now right.
      * apply IHxs in pf.
        destruct pf.
        split; auto.
        now right.
    + simpl; destruct (dec1 a).
      * destruct pf.
        destruct H0.
        -- now left.
        -- right; apply IHxs; split; auto.
      * destruct pf. apply IHxs; split; auto.
        destruct H0; auto.
        subst; contradiction.
Qed.
