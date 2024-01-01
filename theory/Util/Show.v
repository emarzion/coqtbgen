Require Import Ascii.
Open Scope char.

Require Import String.
Require Import Lia.
Require List.
Import List.ListNotations.
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

Lemma char_free_app (c : ascii) (str str' : string) :
  char_free c (str ++ str') <-> char_free c str /\ char_free c str'.
Proof.
  split; induction str; simpl; tauto.
Qed.

Lemma char_free_split : forall {c s t u v},
  s ++ (String c t) = u ++ (String c v) ->
  char_free c s ->
  char_free c u ->
  s = u /\ t = v.
Proof.
  intros c s.
  induction s; intros t u v Heq Hs Hu.
  - destruct u.
    + inversion Heq; now split.
    + simpl in *.
      now inversion Heq.
  - destruct u.
    + simpl in *.
      inversion Heq.
      now rewrite H0 in Hs.
    + simpl in *.
      inversion Heq.
      destruct Hs, Hu.
      destruct (IHs _ _ _ H1); auto.
      split; [congruence|auto].
Qed.

Class CommaFree (X : Type) `{Show X} := {
  comma_free : forall x, char_free (",")%char (show x)
  }.

Class SemicolonFree (X : Type) `{Show X} := {
  semicolon_free : forall x, char_free (";")%char (show x)
  }.

Class Nonnil (X : Type) `{Show X} := {
  nonnil : forall x, show x <> ""
  }.

Definition str_comma : string := ",".

Global Instance Show_Prod {X Y} `{CommaFree X, CommaFree Y} : Show (X * Y).
Proof.
  apply (Build_Show _
    (fun '(x,y) => show x ++ str_comma ++ show y)).
  intros [x y] [x' y'] pair_eq.
  inversion pair_eq.
  destruct (char_free_split H4); try apply comma_free.
  rewrite (show_inj _ _ H3).
  now rewrite (show_inj _ _ H5).
Defined.

Lemma string_app_length : forall {pre suff},
  String.length (pre ++ suff) =
  String.length pre + String.length suff.
Proof.
  induction pre; intros suff.
  - reflexivity.
  - simpl.
    now rewrite IHpre.
Qed.

Lemma string_app_lemma : forall (pre pre' suff : string),
  pre ++ suff = pre' ++ suff -> pre = pre'.
Proof.
  induction pre; intros pre' suff.
  - destruct pre'; intro pf.
    + reflexivity.
    + symmetry in pf.
      simpl append at 2 in pf.
      absurd (String.length (String a pre' ++ suff) =
        String.length suff); [|congruence].
      rewrite (string_app_length); simpl.
      lia.
  - destruct pre'; intro pf.
    + simpl append at 2 in pf.
      absurd (String.length (String a pre ++ suff) =
        String.length suff); [|congruence].
      rewrite (string_app_length); simpl.
      lia.
    + inversion pf.
      apply f_equal.
      eapply IHpre; eauto.
Qed.

Definition str_LB : string := "[".
Definition str_RB : string := "]".
Definition str_SC : string := ";".


Global Instance Show_list {X} `{sh : Show X}
  `{@SemicolonFree X sh, @Nonnil X sh} : Show (list X).
Proof.
  refine {|
    show xs := str_LB ++ String.concat str_SC (List.map show xs) ++ str_RB;
    show_inj := _
  |}.
  intro xs; induction xs; intro ys.
  - destruct ys; intro Heq; [reflexivity|].
    simpl in Heq.
    destruct ys; simpl in *.
    + destruct (show x) eqn:Hx.
      * elim (nonnil x Hx).
      * destruct s; discriminate.
    + destruct (show x); [discriminate|].
      destruct s; discriminate.
  - destruct ys; intro Heq; simpl in *.
    + destruct xs.
      * simpl in Heq.
        destruct (show a) eqn:Ha.
        -- elim (nonnil a Ha).
        -- destruct s; discriminate.
      * simpl in Heq.
        destruct (show a); [discriminate|].
        destruct s; discriminate.
    + destruct xs, ys; simpl in Heq.
      * f_equal.
        apply show_inj.
        apply (string_app_lemma _ _ "]").
        now inversion Heq.
      * absurd (char_free ";" (String "[" (show a ++ "]"))).
        -- unfold str_RB in Heq.
           rewrite Heq; simpl.
           repeat rewrite char_free_app; simpl.
           firstorder.
        -- simpl; split; [discriminate|].
           rewrite char_free_app; split.
           ++ apply semicolon_free.
           ++ simpl; now split.
      * absurd (char_free ";" (String "[" (show x ++ "]"))).
        -- unfold str_RB in Heq.
           rewrite <- Heq; simpl.
           repeat rewrite char_free_app; simpl.
           firstorder.
        -- simpl; split; [discriminate|].
           rewrite char_free_app; split.
           ++ apply semicolon_free.
           ++ simpl; now split.
      * rewrite (IHxs (x1 :: ys)%list).
        -- f_equal.
           inversion Heq.
           pose proof (string_app_lemma _ _ _ H2).
           destruct (char_free_split H1); simpl in *; try apply semicolon_free.
           now apply show_inj.
        -- destruct xs; simpl in *.
           ++ repeat f_equal.
              inversion Heq.
              pose proof (string_app_lemma _ _ _ H2).
              edestruct (char_free_split H1); simpl in *; try apply semicolon_free; auto.
           ++ inversion Heq.
              pose proof (string_app_lemma _ _ _ H2).
              destruct (char_free_split H1); simpl in *; try apply semicolon_free.
              congruence.
Defined.

Global Instance CommaFree_list {X} `{sh : Show X}
  `{@SemicolonFree X sh, @Nonnil X sh, @CommaFree X sh} : CommaFree (list X).
Proof.
  constructor.
  intro xs; induction xs.
  - simpl; repeat split; discriminate.
  - simpl; split; [discriminate|].
    destruct xs; simpl.
    + rewrite char_free_app; split.
      * apply comma_free.
      * simpl; repeat split.
        discriminate.
    + rewrite char_free_app; repeat split; [|discriminate].
      rewrite char_free_app; repeat split; try discriminate.
      * apply comma_free.
      * destruct xs; simpl in *;
        rewrite char_free_app in IHxs; tauto.
Defined.