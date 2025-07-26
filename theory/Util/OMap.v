Require Import PrimInt63.
Require TBGen.Util.IntMap.

Parameter OM : Type -> Type.

Parameter empty : forall {X}, OM X.
Parameter add : forall {X}, int -> X -> OM X -> OM X.
Parameter lookup : forall {X}, int -> OM X -> option X.
Parameter to_list : forall {X}, OM X -> list (int * X).
Parameter size : forall {X}, OM X -> nat.

Axiom lookup_empty : forall {X} str,
  lookup str (empty : OM X) = None.
Axiom lookup_add : forall {X} str (x : X) m,
  lookup str (add str x m) = Some x.
Axiom lookup_add_neq : forall {X} str str' (x : X) m, str <> str' ->
  lookup str (add str' x m) = lookup str m.

Axiom to_list_lookup : forall {X} (m : OM X) k v,
  List.In (k, v) (to_list m) -> lookup k m = Some v.
Axiom lookup_to_list : forall {X} (m : OM X) k v,
  lookup k m = Some v -> List.In (k, v) (to_list m).
Axiom to_list_NoDup_keys : forall {X} (m : OM X),
  List.NoDup (List.map fst (to_list m)).
Axiom size_to_list : forall {X} (m : OM X),
  size m = length (to_list m).

Global Instance OMap : IntMap.IntMap OM := {|
  IntMap.empty := @empty;
  IntMap.add := @add;
  IntMap.lookup := @lookup;
  IntMap.to_list := @to_list;
  IntMap.size := @size;
  IntMap.lookup_empty := @lookup_empty;
  IntMap.lookup_add := @lookup_add;
  IntMap.lookup_add_neq := @lookup_add_neq;
  IntMap.to_list_lookup := @to_list_lookup;
  IntMap.lookup_to_list := @lookup_to_list;
  IntMap.to_list_NoDup_keys := @to_list_NoDup_keys;
  IntMap.size_to_list := @size_to_list;
  |}.

Require Import Extraction.
Extraction Language OCaml.

Extract Constant empty => "M.empty".
Extract Constant add => "M.insert".
Extract Constant lookup => "M.lookup".
Extract Constant to_list => "M.to_list".
Extract Constant size => "M.size".

Extract Constant OM "'v" => "'v M.t".
