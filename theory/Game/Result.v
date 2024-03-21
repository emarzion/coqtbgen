Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.

CoInductive Res :=
  | Win_res (pl : Player) : Res
  | Step_res : Res -> Res.

Definition Res_id (r : Res) : Res :=
  match r with
  | Win_res pl => Win_res pl
  | Step_res r' => Step_res r'
  end.

Lemma Res_id_eq (r : Res) : r = Res_id r.
Proof.
  destruct r; reflexivity.
Qed.

CoInductive bisim : Res -> Res -> Prop :=
  | Win_refl {pl} : bisim (Win_res pl) (Win_res pl)
  | Step_bisim {r1 r2} : bisim r1 r2 -> bisim (Step_res r1) (Step_res r2).

CoFixpoint draw : Res := Step_res draw.

Definition Res_of_Result (r : Result) : Res :=
  match r with
  | Win pl => Win_res pl
  | Draw => draw
  end.

Fixpoint Res_of_n pl (n : nat) : Res :=
  match n with
  | 0 => Win_res pl
  | S m => Step_res (Res_of_n pl m)
  end.

Definition Res_of_tb_res (o : option (Player * nat)) : Res :=
  match o with
  | Some (pl, n) => Res_of_n pl n
  | None => draw
  end.

CoInductive res_le (pl : Player) : Res -> Res -> Prop :=
  | Win_is_best : forall r, res_le pl r (Win_res pl)
  | Loss_is_worst : forall r, res_le pl (Win_res (opp pl)) r
  | Step_mon : forall r1 r2, res_le pl r1 r2 -> res_le pl (Step_res r1) (Step_res r2).

Notation "r1 <<= p r2" := (res_le p r1 r2)
  (at level 10, r2 at next level, p at next level).

CoFixpoint res_flip pl : forall r1 r2,
  r1 <<= pl r2 -> r2 <<= (opp pl) r1.
Proof.
  intros r1 r2 H.
  destruct H.
  - rewrite <- (opp_invol pl) at 2.
    apply Loss_is_worst.
  - apply Win_is_best.
  - apply Step_mon.
    now apply res_flip.
Defined.

Axiom cheat : forall {X}, X.

CoFixpoint res_le_trans_pf pl : forall r1 r2 r3,
  r1 <<= pl r2 -> r2 <<= pl r3 -> r1 <<= pl r3.
Proof.
  intros r1 r2 r3 H1 H2.
  destruct H1.
  - apply cheat.

  - apply Loss_is_worst.
  - destruct r3.
    + apply cheat.
    + apply Step_mon.
      eapply (res_le_trans_pf).
      * exact H1.
      * apply cheat.
Defined.

Print res_le_trans_pf.

Definition res_le_trans pl :=

let cofix res_le_trans_pf
  (r1 r2 r3 : Res) (H1 : r1 <<= pl r2) (H2 : r2 <<= pl r3) :
    r1 <<= pl r3 :=
  match H1 in (r <<= _ r0) return (r0 <<= pl r3 -> r <<= pl r3) with
  | Win_is_best _ r => (fun (r0 : Res) (_ : (Win_res pl) <<= pl r3) => cheat) r
  | Loss_is_worst _ r =>
      (fun (r0 : Res) (_ : r0 <<= pl r3) => Loss_is_worst pl r3) r
  | Step_mon _ r4 r5 x =>
      (fun (r6 r7 : Res) (H3 : r6 <<= pl r7) (H4 : (Step_res r7) <<= pl r3) =>
       match
         r3 as r return ((Step_res r7) <<= pl r -> (Step_res r6) <<= pl r)
       with
       | Win_res pl0 =>
           (fun (pl1 : Player) (_ : (Step_res r7) <<= pl (Win_res pl1)) => cheat)
             pl0
       | Step_res r =>
           (fun (r8 : Res) (_ : (Step_res r7) <<= pl (Step_res r8)) =>
            Step_mon pl r6 r8 (res_le_trans_pf r6 r7 r8 H3 cheat)) r
       end H4) r4 r5 x
  end H2 in
  res_le_trans_pf.


(*
CoFixpoint res_le_trans pl : forall r1 r2 r3,
  r1 <<= pl r2 -> r2 <<= pl r3 -> r1 <<= pl r3.
Proof.
  intros r1 r2 r3 H1 H2.
  destruct H2 eqn:?.
  - apply Win_is_best.
  - inversion H1.
    + elim (opp_no_fp pl); congruence.
    + apply Loss_is_worst.
  - destruct r1.
    + inversion H1.
      apply Loss_is_worst.
    + apply Step_mon.
      apply (res_le_trans pl _ r0); auto.
      now inversion H1.
Defined.


Axiom cheat : forall {X},X.

Goal res_le_trans = cheat.
*)

CoFixpoint res_le_antisym pl : forall r1 r2,
  r1 <<= pl r2 -> r2 <<= pl r1 ->
  bisim r1 r2.
Proof.
  intros.
  destruct H.
  - inversion H0.
    + apply Win_refl.
    + elim (opp_no_fp pl); congruence.
  - inversion H0.
    + elim (opp_no_fp pl); congruence.
    + apply Win_refl.
  - inversion H0.
    apply Step_bisim.
    apply (res_le_antisym _ _ _ H H3).
Qed.

Lemma atomic_res_inf {G} (s : GameState G) :
  { r : Result & atomic_res s = Some r } +
  (atomic_res s = None) .
Proof.
  destruct atomic_res as [r|].
  - left; exists r; reflexivity.
  - right; reflexivity.
Defined.

CoFixpoint trace {G} {pl} {s : GameState G}
  (s1 : strategy pl s) (s2 : strategy (opp pl) s) : Res.
Proof.
  destruct (atomic_res_inf s) as [[r s_res]|s_res].
  - exact (Res_of_Result r).
  - apply Step_res.
    destruct s1; try congruence.
    + destruct s2; try congruence; try (elim (opp_no_fp pl); congruence).
      exact (trace _ _ _ s1 (s m)).
    + destruct s2; try congruence; try (elim (opp_no_fp (opp pl)); congruence).
      exact (trace _ _ _ (s m) s2).
Defined.

CoFixpoint opp_opp_str {G} {pl} {s : GameState G} (st : strategy pl s) : strategy (opp (opp pl)) s.
Proof.
  destruct st.
  - eapply atom_strategy; eauto.
  - eapply eloise_strategy; auto.
    + now rewrite opp_invol.
    + apply opp_opp_str.
      exact st.
  - apply abelard_strategy; auto.
    now rewrite opp_invol.
Defined.

CoFixpoint bisim_refl : forall r, bisim r r.
Proof.
  intro r.
  destruct r; constructor.
  apply bisim_refl.
Defined.

CoFixpoint trace_comm {G} {pl} {s : GameState G}
  (s1 : strategy pl s) (s2 : strategy (opp pl) s) :
  bisim (trace s1 s2) (trace s2 (opp_opp_str s1)).
Proof.
  rewrite (Res_id_eq (trace s1 s2)).
  rewrite (Res_id_eq (trace s2 (opp_opp_str s1))).
  unfold Res_id.
  unfold trace.
  destruct (atomic_res_inf s) as [[r s_res]|s_res].
  - apply bisim_refl.
  - constructor.
    destruct s1; try (elim (opp_no_fp pl); congruence).
    + destruct s2; try (elim (opp_no_fp (opp pl)); congruence).
      fold @trace.
      unfold opp_opp_str.
      fold @opp_opp_str.
      apply trace_comm.
    + destruct s2; try (elim (opp_no_fp (opp pl)); congruence).
      fold @trace.
      unfold opp_opp_str.
      fold @opp_opp_str.
      apply trace_comm.
Defined.

Definition str_le {G} {st : GameState G} {pl} (s s' : strategy pl st) : Prop :=
  forall opp, exists opp', (trace s opp') <<= pl (trace s' opp).

Notation "s <<= s'" := (str_le s s')
  (at level 10).

Definition optimal {G} {pl} {s : GameState G} (str : strategy pl s) : Prop :=
  forall str', str' <<= str.








