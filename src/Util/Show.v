Require Import Ascii.
Open Scope char.

Require Import String.
Require List.
Open Scope string_scope.

Class Show (X : Type) : Type := {
  show : X -> string;
  show_inj : forall x x', show x = show x' -> x = x'
  }.

Definition Show_dec {X} `{Show X} : forall x x' : X,
  {x = x'} + {x <> x'}.
Proof.
  intros.
  destruct (string_dec (show x) (show x')).
  - left; now apply show_inj.
  - right; intro.
    apply n; congruence.
Defined.

Fixpoint char_free (c : ascii) (str : string) : Prop :=
  match str with
  | EmptyString => True
  | String c' str' => c <> c' /\ char_free c str'
  end.

Lemma char_free_split : forall {c s t u v},
  char_free c s ->
  char_free c t ->
  char_free c u ->
  char_free c v ->
  s ++ (String c t) = u ++ (String c v) ->
  s = u /\ t = v.
Proof.
  intros c s.
  induction s; intros.
  - destruct u.
    + inversion H3; now split.
    + simpl in *.
      now inversion H3.
  - destruct u.
    + simpl in *.
      inversion H3.
      now rewrite H5 in H.
    + simpl in *.
      inversion H3.
      destruct H, H1.
      destruct (IHs _ _ _ H4 H0 H7 H2 H6).
      split; [congruence|auto].
Qed.

Class CommaFree (X : Type) `{Show X} := {
  comma_free : forall x, char_free (",")%char (show x)
  }.

Global Instance Show_Prod {X Y} `{CommaFree X, CommaFree Y} : Show (X * Y).
Proof.
  apply (Build_Show _
    (fun '(x,y) => show x ++ "," ++ show y)).
  intros [x y] [x' y'] pair_eq.
  inversion pair_eq.
  destruct (char_free_split
    (comma_free x)
    (comma_free y)
    (comma_free x')
    (comma_free y') H4).
  rewrite (show_inj _ _ H3).
  now rewrite (show_inj _ _ H5).
Defined.
