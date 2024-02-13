Require Import Games.Game.Player.
Require Import Games.Game.Game.

CoInductive strategy {G : Game} (p : Player) : GameState G -> Type :=
  | atom_strategy : forall b res,
      atomic_res b = Some res ->
      strategy p b
  | eloise_strategy : forall b,
      atomic_res b = None ->
      to_play b = p -> forall m,
      strategy p (exec_move b m) -> strategy p b
  | abelard_strategy : forall b,
      atomic_res b = None ->
      to_play b = opp p ->
      (forall m, strategy p (exec_move b m)) ->
      strategy p b.

Arguments atom_strategy {_} {_} {_} {_} _.
Arguments eloise_strategy {_} {_} {_} _ _ _.
Arguments abelard_strategy {_} {_} {_} _ _ _.

Definition strat_id {G} {p} {s : GameState G} (str : strategy p s) : strategy p s :=
  match str with
  | atom_strategy res_pf => atom_strategy res_pf
  | eloise_strategy res_pf play_pf m str => eloise_strategy res_pf play_pf m str
  | abelard_strategy res_pf play_pf strs => abelard_strategy res_pf play_pf strs
  end.

Lemma strat_id_eq {G : Game} {p} {s : GameState G} (str : strategy p s) :
  str = strat_id str.
Proof.
  destruct str; reflexivity.
Qed.

Inductive winning_strategy {G : Game} (p : Player) : forall {s : GameState G},
  strategy p s -> Prop :=
  | atom_strat_win : forall s (res_pf : atomic_res s = Some (Win p)),
      winning_strategy p (atom_strategy res_pf)
  | eloise_strat_win : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = p) (m : Move s)
      (str : strategy p (exec_move s m)), winning_strategy p str ->
      winning_strategy p (eloise_strategy res_pf play_pf m str)
  | abelard_strat_win : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = opp p)
      (strs : forall m, strategy p (exec_move s m)),
      (forall m, winning_strategy p (strs m)) ->
      winning_strategy p (abelard_strategy res_pf play_pf strs).

CoInductive drawing_strategy {G : Game} (p : Player) : forall {s : GameState G},
  strategy p s -> Prop :=
  | atom_strat_draw : forall s (res_pf : atomic_res s = Some Draw),
      drawing_strategy p (atom_strategy res_pf)
  | eloise_strat_draw : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = p) (m : Move s)
      (str : strategy p (exec_move s m)), drawing_strategy p str ->
      drawing_strategy p (eloise_strategy res_pf play_pf m str)
  | abelard_strat_draw : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = opp p)
      (strs : forall m, strategy p (exec_move s m)),
      (forall m, drawing_strategy p (strs m) \/ winning_strategy p (strs m)) ->
      drawing_strategy p (abelard_strategy res_pf play_pf strs).
