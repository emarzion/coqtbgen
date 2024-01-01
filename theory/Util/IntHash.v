Require Import Ascii.
Open Scope char.

Require Import PrimInt63.
Require Import Uint63.
Require Import Lia.
Require List.
Import List.ListNotations.

Class IntHash (X : Type) : Type := {
  hash : X -> int;
  hash_inj : forall x x', hash x = hash x' -> x = x'
  }.

Definition IntHash_dec {X} `{IntHash X} : forall x x' : X,
  {x = x'} + {x <> x'}.
Proof.
  intros.
  destruct (eqb (hash x) (hash x')) eqn:Heq.
  - rewrite eqb_spec in Heq.
    left; now apply hash_inj.
  - right; intro.
    rewrite eqb_false_spec in Heq.
    apply Heq; congruence.
Defined.
