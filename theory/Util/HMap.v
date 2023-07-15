Require Import String.
Require Games.Util.StringMap.

Parameter HM : Type -> Type.

Parameter empty : forall {X}, HM X.
Parameter add : forall {X}, string -> X -> HM X -> HM X.
Parameter lookup : forall {X}, string -> HM X -> option X.
Parameter size : forall {X}, HM X -> nat.

Axiom lookup_empty : forall {X} str,
  lookup str (empty : HM X) = None.
Axiom lookup_add : forall {X} str (x : X) m,
  lookup str (add str x m) = Some x.
Axiom lookup_add_neq : forall {X} str str' (x : X) m, str <> str' ->
  lookup str (add str' x m) = lookup str m.
Axiom size_empty : forall {X}, size (empty : HM X) = 0.
Axiom size_add : forall {X} str (x : X) m,
  size (add str x m) =
    match lookup str m with
    | Some _ => size m
    | None => S (size m)
    end.

Global Instance HMap : StringMap.StringMap HM := {|
  StringMap.empty := @empty;
  StringMap.add := @add;
  StringMap.lookup := @lookup;
  StringMap.size := @size;
  StringMap.lookup_empty := @lookup_empty;
  StringMap.lookup_add := @lookup_add;
  StringMap.lookup_add_neq := @lookup_add_neq;
  StringMap.size_empty := @size_empty;
  StringMap.size_add := @size_add
  |}.

Require Import Extraction.
Extraction Language Haskell.

Extract Constant empty => "M.empty".
Extract Constant add => "M.insert".
Extract Constant lookup => "M.lookup".
Extract Constant size => "M.size".
Extract Constant HM "v" => "M.Map Prelude.String v".









