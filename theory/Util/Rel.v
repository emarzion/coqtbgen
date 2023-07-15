
Fixpoint Rel (n : nat) (X : Type) : Type :=
  match n with
  | 0 => Prop
  | S m => X -> Rel m X
  end.
