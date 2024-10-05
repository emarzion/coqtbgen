Require Import Ascii.
Open Scope char.

Require Import String.
Require Import Lia.
Require List.
Import List.ListNotations.
Open Scope string_scope.

Class Show (X : Type) : Type := {
  show : X -> string;
  }.
