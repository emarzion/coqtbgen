Require Import TBGen.Bear.Graph.

Record Group : Type := {
  carrier : Type;

  id : carrier;
  mult : carrier -> carrier -> carrier;
  inv : carrier -> carrier;

  assoc : forall x y z, mult x (mult y z) = mult (mult x y) z;
  id_left : forall x, mult id x = x;
  id_right : forall x, mult x id = x;

  inv_left : forall x, mult (inv x) x = id;
  inv_right : forall x, mult x (inv x) = id;
  }.

Arguments id {_}.
Arguments mult {_} _ _.
Arguments inv {_} _.

Infix "**" := mult (at level 10).

Class GroupAction (G : Graph) (H : Group) : Type := {
  act : carrier H -> Vert G -> Vert G;
  act_id : forall v, act id v = v;
  act_comp : forall v x y, act (x ** y) v = act x (act y v);
  act_edge : forall (x : carrier H) (v v' : Vert G),
    List.In v' (successors v) ->
    List.In (act x v') (successors (act x v));
  }.

Arguments act {_} {_} {_} _ _.

Infix "#" := act (at level 5).

Lemma act_inj {G} {H} `{GroupAction G H} :
  forall x v v', x # v = x # v' -> v = v'.
Proof.
  intros x v v' pf.
  apply f_equal with (f := act (inv x)) in pf.
  repeat rewrite <- act_comp in pf.
  rewrite inv_left in pf.
  repeat rewrite act_id in pf.
  auto.
Qed.
