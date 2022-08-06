Require Import CoqChess.Game.Player.
Require Import CoqChess.Game.Game.
Require Import CoqChess.Util.All.
Require Import Lia.
Require Import List.
Import ListNotations.

Inductive Piece :=
  | King : Piece
  | Queen : Piece
  | Rook : Piece
  | Bishop : Piece
  | Knight : Piece
  .

#[export]
Instance Piece_Discrete : Discrete Piece.
Proof.
  constructor.
  unfold decision.
  decide equality.
Defined.

#[export]
Instance Piece_Exhaustible : Exhaustible Piece.
Proof.
  constructor.
  intros P Pd.
  destruct (Pd King); [firstorder|].
  destruct (Pd Queen); [firstorder|].
  destruct (Pd Rook); [firstorder|].
  destruct (Pd Bishop); [firstorder|].
  destruct (Pd Knight); [firstorder|].
  right; intros [[] Hp]; tauto.
Defined.

Definition Board : Type :=
  Mat (option (Player * Piece)) 8 8.


Inductive Rank : Type :=
  | MkRank : Fin 8 -> Rank.

Definition fin_of_rank : Rank -> Fin 8 :=
  fun '(MkRank i) => i.

#[export]
Instance Rank_Discrete : Discrete Rank.
Proof.
  constructor.
  unfold decision; decide equality; apply dec.
Defined.

#[export]
Instance Rank_Exhaustible : Exhaustible Rank.
Proof.
  constructor.
  intros P Pd.
  destruct (sig_dec (fun i => P (MkRank i))).
  - intro; apply Pd.
  - left; destruct e as [i Hi].
    exists (MkRank i); exact Hi.
  - right; intros [[i] Hi].
    apply n; exists i; exact Hi.
Defined.

Inductive File : Type :=
  | MkFile : Fin 8 -> File.

Definition fin_of_file : File -> Fin 8 :=
  fun '(MkFile i) => i.

#[export]
Instance File_Discrete : Discrete File.
Proof.
  constructor.
  unfold decision; decide equality; apply dec.
Defined.

#[export]
Instance File_Exhaustible : Exhaustible File.
Proof.
  constructor.
  intros P Pd.
  destruct (sig_dec (fun i => P (MkFile i))).
  - intro; apply Pd.
  - left; destruct e as [i Hi].
    exists (MkFile i); exact Hi.
  - right; intros [[i] Hi].
    apply n; exists i; exact Hi.
Defined.

Definition Pos : Type :=
  File * Rank.

Definition file : Pos -> File :=
  fst.

Definition rank : Pos -> Rank :=
  snd.

Definition lookup_piece : Pos -> Board -> option (Player * Piece) :=
  fun '(MkFile i, MkRank j) b =>
    fin_maccess i j b.

Definition place_piece : Player -> Piece -> Pos
  -> Board -> Board :=
  fun pl pc '(MkFile i, MkRank j) b =>
    fin_mupdate i j (Some (pl, pc)) b.

Definition clear : Pos -> Board -> Board :=
  fun '(MkFile i, MkRank j) b =>
    fin_mupdate i j None b.

Lemma lookup_clear_eq : forall pos b,
  lookup_piece pos (clear pos b) = None.
Proof.
  intros.
  unfold lookup_piece, clear.
  destruct pos as [[r] [f]].
  apply fin_maccess_fin_mupdate_eq.
Qed.

Lemma lookup_clear_neq : forall pos1 pos2 b, pos1 <> pos2 ->
  lookup_piece pos1 (clear pos2 b) =
  lookup_piece pos1 b.
Proof.
  intros.
  unfold lookup_piece, clear.
  destruct pos1 as [[r1] [f1]].
  destruct pos2 as [[r2] [f2]].
  rewrite fin_maccess_fin_mupdate_neq;
    [auto | congruence].
Qed.

Lemma lookup_place_eq : forall player pos b piece,
  lookup_piece pos (place_piece player piece pos b) =
  Some (player, piece).
Proof.
  intros.
  unfold lookup_piece, place_piece.
  destruct pos as [[r] [f]].
  apply fin_maccess_fin_mupdate_eq.
Qed.

Lemma lookup_place_neq : forall player pos1 pos2 b piece,
  pos1 <> pos2 ->
  lookup_piece pos1 (place_piece player piece pos2 b) =
  lookup_piece pos1 b.
Proof.
  intros.
  unfold lookup_piece, place_piece.
  destruct pos1 as [[r1] [f1]].
  destruct pos2 as [[r2] [f2]].
  rewrite fin_maccess_fin_mupdate_neq;
    [auto | congruence].
Qed.

(** Rank/File Operations *)
Section RF_ops.

Definition white_home_rank : Rank.
Proof.
  apply MkRank.
  exists 1.
  lia.
Defined.

Definition black_home_rank : Rank.
Proof.
  apply MkRank.
  exists 6.
  lia.
Defined.

Definition home_rank : Player -> Rank :=
  fun p =>
    match p with
    | White => white_home_rank
    | Black => black_home_rank
    end.

Definition white_back_rank : Rank.
Proof.
  apply MkRank.
  exists 7.
  lia.
Defined.

Definition black_back_rank : Rank.
Proof.
  apply MkRank.
  exists 0.
  lia.
Defined.

Definition back_rank : Player -> Rank :=
  fun p =>
    match p with
    | White => white_back_rank
    | Black => black_home_rank
    end.

Definition one_up : Rank -> Rank -> Prop :=
  fun '(MkRank i) '(MkRank j) =>
    val j = S (val i).

Definition one_down : Rank -> Rank -> Prop :=
  fun '(MkRank i) '(MkRank j) =>
    val i = S (val j).

Definition one_move : Player -> Rank -> Rank -> Prop :=
  fun p =>
    match p with
    | White => one_up
    | Black => one_down
    end.

Definition two_up : Rank -> Rank -> Prop :=
  fun '(MkRank i) '(MkRank j) =>
    val j = S (S (val i)).

Definition two_down : Rank -> Rank -> Prop :=
  fun '(MkRank i) '(MkRank j) =>
    val i = S (S (val i)).

Definition two_move : Player -> Rank -> Rank -> Prop :=
  fun p =>
    match p with
    | White => two_up
    | Black => two_down
    end.

Definition rank_dist : Rank -> Rank -> nat :=
  fun '(MkRank i) '(MkRank j) =>
    fin_dist i j.

Lemma rank_dist_sym : forall r1 r2 : Rank,
  rank_dist r1 r2 = rank_dist r2 r1.
Proof.
  intros [i] [j].
  apply fin_dist_sym.
Qed.

Definition rank_sbetween : Rel 3 Rank :=
  fun r1 r2 r3 =>
    fin_sbetween
      (fin_of_rank r1)
      (fin_of_rank r2)
      (fin_of_rank r3).

Lemma rank_sbetween_sym : forall r1 r2 r3 : Rank,
  rank_sbetween r1 r2 r3 -> rank_sbetween r3 r2 r1.
Proof.
  intros [i] [j] [k]; unfold rank_sbetween;
  apply fin_sbetween_sym.
Qed.

Definition file_dist : File -> File -> nat :=
  fun '(MkFile i) '(MkFile j) =>
    fin_dist i j.

Lemma file_dist_sym : forall f1 f2 : File,
  file_dist f1 f2 = file_dist f2 f1.
Proof.
  intros [i] [j].
  apply fin_dist_sym.
Qed.

Definition file_sbetween : Rel 3 File :=
  fun f1 f2 f3 =>
    fin_sbetween
      (fin_of_file f1)
      (fin_of_file f2)
      (fin_of_file f3).

Lemma file_sbetween_sym : forall f1 f2 f3 : File,
  file_sbetween f1 f2 f3 -> file_sbetween f3 f2 f1.
Proof.
  intros [i] [j] [k]; unfold file_sbetween;
  apply fin_sbetween_sym.
Qed.

End RF_ops.

(** movement of pieces before obstacles *)
Section PreAdjacencies.

Definition diag_preadj : Rel 2 Pos :=
  fun p1 p2 =>
    rank_dist (rank p1) (rank p2) =
    file_dist (file p1) (file p2).

Definition L_preadj : Rel 2 Pos :=
  fun p1 p2 =>
       (    file_dist (file p1) (file p2) = 1
         /\ rank_dist (rank p1) (rank p2) = 2
       )
    \/ (    file_dist (file p1) (file p2) = 2
         /\ rank_dist (rank p1) (rank p2) = 1
       ).

Definition horiz_preadj : Rel 2 Pos :=
  fun p1 p2 => rank p1 = rank p2.

Definition vert_preadj : Rel 2 Pos :=
  fun p1 p2 => file p1 = file p2.

Definition neighbor_preadj : Rel 2 Pos :=
  fun p1 p2 =>
    rank_dist (rank p1) (rank p2) <= 1 /\
    file_dist (file p1) (file p2) <= 1.

End PreAdjacencies.

(** Movement of pieces accounting for obstacles. *)
Section Adjacencies.

Definition diag_adj : Board -> Rel 2 Pos :=
  fun b p1 p2 =>
       diag_preadj p1 p2
    /\ forall p3, diag_preadj p1 p3 ->
       file_sbetween (file p1) (file p3) (file p2) ->
       rank_sbetween (rank p1) (rank p3) (rank p2) ->
       lookup_piece p3 b = None.

Definition horiz_adj : Board -> Rel 2 Pos :=
  fun b p1 p2 =>
       horiz_preadj p1 p2
    /\ forall p3, horiz_preadj p1 p3 ->
       file_sbetween (file p1) (file p3) (file p2) ->
       lookup_piece p3 b = None.

Definition vert_adj : Board -> Rel 2 Pos :=
  fun b p1 p2 =>
       vert_preadj p1 p2
    /\ forall p3, vert_preadj p1 p3 ->
       rank_sbetween (rank p1) (rank p3) (rank p2) ->
       lookup_piece p3 b = None.

Definition orthog_adj : Board -> Rel 2 Pos :=
  fun b p1 p2 => horiz_adj b p1 p2 \/ vert_adj b p1 p2.

Definition diag_orthog_adj : Board -> Rel 2 Pos :=
  fun b p1 p2 => diag_adj b p1 p2 \/ orthog_adj b p1 p2.

Definition L_adj : Board -> Rel 2 Pos :=
  fun _ => L_preadj.

Definition neighbor_adj : Board -> Rel 2 Pos :=
  fun _ => neighbor_preadj.

Definition non_pawn_piece_adj : Piece -> Board -> Rel 2 Pos :=
  fun p =>
    match p with
    | King => neighbor_adj
    | Queen => diag_orthog_adj
    | Rook => orthog_adj
    | Bishop => diag_adj
    | Knight => L_adj
    end.

#[export]
Instance Dec_non_pawn_piece_adj : forall p b pos1 pos2,
  Dec (non_pawn_piece_adj p b pos1 pos2).
Proof.
  intros p b pos1 pos2.
  constructor.
  destruct p; apply dec.
Defined.

End Adjacencies.

Definition open : Player -> Board -> Rel 1 Pos :=
  fun player b pos =>
    match lookup_piece pos b with
    | None => True
    | Some (p, _) => p = opp player
    end.

Definition adj : Player -> Board -> Piece -> Rel 2 Pos :=
  fun player b piece pos1 pos2 =>
       lookup_piece pos1 b = Some (player, piece)
    /\ open player b pos2
    /\ non_pawn_piece_adj piece b pos1 pos2.

Definition is_threatened_by : Board -> Pos -> Player -> Prop :=
  fun b pos player =>
    exists pos' piece,
         lookup_piece pos' b = Some (player, piece)
      /\ non_pawn_piece_adj piece b pos' pos.

Record ChessState : Type := {
  chess_to_play : Player;
  board : Board;

  kings_found : forall player, exists pos,
    lookup_piece pos board = Some (player, King);
  kings_unique : forall player pos1 pos2,
    lookup_piece pos1 board = Some (player, King) ->
    lookup_piece pos2 board = Some (player, King) ->
    pos1 = pos2;

  opp_to_play_not_in_check : forall pos,
    lookup_piece pos board = Some (opp chess_to_play, King) ->
    ~ is_threatened_by board pos chess_to_play

  }.

Definition make_move : Player -> Piece -> Pos -> Pos -> Board -> Board :=
  fun player piece pos1 pos2 b =>
    clear pos1 (place_piece player piece pos2 b).

Inductive ChessMove (st : ChessState) : Type :=
  | mkMove : forall (pos1 pos2 : Pos) (piece : Piece),
      adj (chess_to_play st) (board st) piece pos1 pos2 ->
      (forall pos, lookup_piece pos
        (make_move (chess_to_play st) piece pos1 pos2 (board st)) = (Some (chess_to_play st, King)) ->
         ~ is_threatened_by (make_move (chess_to_play st) piece pos1 pos2 (board st)) pos (opp (chess_to_play st))) ->
      ChessMove st.

Definition exec_ChessMove : forall {st}, ChessMove st -> ChessState. refine (
  fun st '(mkMove _ pos1 pos2 piece adj_pf not_in_check_pf) =>
    {|
      chess_to_play := opp (chess_to_play st);
      board := make_move (chess_to_play st) piece pos1 pos2 (board st);
      kings_found := _;
      kings_unique := _;
      opp_to_play_not_in_check := _
    |} ).
Proof.
  (* kings_found *)
  { intro player.
    destruct (player_id_or_opp player (chess_to_play st)) as [pf|pf].
    - rewrite <- pf in *.
      destruct (kings_found st player) as [king Hking].
      destruct (dec (P := king = pos1)) as [king_eq|king_neq].
      + exists pos2.
        unfold make_move.
        rewrite lookup_clear_neq.
        * rewrite lookup_place_eq.
          rewrite <- king_eq in adj_pf.
          destruct adj_pf as [Hlookup [Hopen Hadj]]; congruence.
        * intro pf2; rewrite pf2 in *.
          destruct adj_pf as [Hlookup [Hopen Hadj]].
          unfold open in Hopen.
          rewrite Hlookup in Hopen.
          apply (opp_no_fp player); congruence.
      + exists king.
        unfold make_move.
        rewrite lookup_clear_neq; auto.
        rewrite lookup_place_neq; auto.
        intro pf2.
        rewrite <- pf2 in *.
        destruct adj_pf as [Hlookup [Hopen Hadj]].
        unfold open in Hopen.
        rewrite Hking in Hopen.
        apply (opp_no_fp player); congruence.
    - destruct (kings_found st player) as [king Hking].
      exists king.
      rewrite <- pf.
      unfold make_move.
      rewrite lookup_clear_neq.
      + rewrite lookup_place_neq; auto.
        intro Hkp; rewrite <- Hkp in *; clear Hkp.
        apply (opp_to_play_not_in_check st king).
        * rewrite Hking.
          rewrite <- pf.
          rewrite opp_invol; reflexivity.
        * exists pos1, piece; split; apply adj_pf.
      + unfold adj in adj_pf.
        intro Hkp; rewrite <- Hkp in *; clear Hkp.
        destruct adj_pf as [Hlookup _].
        rewrite Hlookup in Hking.
        apply (opp_no_fp player); congruence.
  }
  (* kings_unique *)
  { intros player pos3 pos4 Hpos3 Hpos4.
    destruct (dec (P := pos3 = pos2)) as [pf|pf].
    - rewrite <- pf in *; clear pf.
      unfold make_move in Hpos3.
      rewrite lookup_clear_neq in Hpos3.
      + rewrite lookup_place_eq in Hpos3.
        inversion Hpos3 as [[Hplayer Hpiece]].
        rewrite Hplayer, Hpiece in *; clear Hplayer Hpiece.
        unfold make_move in Hpos4.
        destruct (dec (P := pos4 = pos1)) as [pf|pf].
        * rewrite <- pf in Hpos4.
          rewrite lookup_clear_eq in Hpos4; discriminate.
        * rewrite lookup_clear_neq in Hpos4; auto.
          destruct (dec (P := pos4 = pos3)); [congruence|].
          rewrite lookup_place_neq in Hpos4; auto.
          destruct adj_pf as [Hlookup [Hopen Hadj]].
          elim pf.
          apply (kings_unique st player); auto.
      + intro pf; rewrite pf in *; clear pf.
        destruct adj_pf as [Hlookup [Hopen Hadj]].
        unfold open in Hopen.
        rewrite Hlookup in Hopen.
        apply (opp_no_fp (chess_to_play st)); congruence.
    - unfold make_move in Hpos3, Hpos4.
      assert (pos3 <> pos1) as neq_pf.
      { intro pf2.
        rewrite pf2 in *.
        rewrite lookup_clear_eq in Hpos3; discriminate.
      }
      rewrite lookup_clear_neq in Hpos3; auto.
      rewrite lookup_place_neq in Hpos3; auto.
      rewrite lookup_clear_neq in Hpos4.
      + destruct (dec (P := pos4 = pos2)) as [pf2|pf2].
        * rewrite <- pf2 in *; clear pf2.
          rewrite lookup_place_eq in Hpos4.
          inversion Hpos4 as [[Hplayer Hpiece]].
          rewrite Hplayer, Hpiece in *; clear Hplayer Hpiece.
          elim neq_pf.
          eapply kings_unique; eauto.
          apply adj_pf.
        * rewrite lookup_place_neq in Hpos4; auto.
          eapply kings_unique; eauto.
      + intro pf2; rewrite pf2 in *; clear pf2.
        rewrite lookup_clear_eq in Hpos4; discriminate.
  }
  (* opp_to_play_not_in_check *)
  { intros pos Hpos.
    eapply (not_in_check_pf).
    rewrite opp_invol in Hpos.
    exact Hpos.
  }
Defined.

Definition all_piece : list Piece :=
  [King; Queen; Rook; Bishop; Knight].

Lemma all_piece_In : forall p : Piece,
  In p all_piece.
Proof.
  unfold all_piece.
  intros []; simpl; tauto.
Qed.

Definition all_rank : list Rank :=
  List.map MkRank (all_fin 8).

Lemma all_rank_In : forall r : Rank,
  List.In r all_rank.
Proof.
  intros [i].
  apply List.in_map.
  apply all_fin_In.
Qed.

Definition all_file : list File :=
  List.map MkFile (all_fin 8).

Lemma all_file_In : forall f : File,
  List.In f all_file.
Proof.
  intros [i].
  apply List.in_map.
  apply all_fin_In.
Qed.

Definition all_pos : list Pos :=
  List.concat
    (List.map (fun f : File =>
      List.map (pair f) all_rank) all_file).

Lemma all_pos_In : forall p : Pos,
  List.In p all_pos.
Proof.
  intros [f r].
  unfold all_pos.
  rewrite List.in_concat.
  eexists.
  split.
  - apply List.in_map.
    apply all_file_In.
  - apply List.in_map.
    apply all_rank_In.
Qed.

Fixpoint filter_dec {X} (P : X -> Prop) `{forall x, Dec (P x)}
  (xs : list X) : list {x : X & P x} :=
  match xs with
  | [] => []
  | x :: ys =>
    match dec with
    | left pf => existT P x pf :: filter_dec P ys
    | right _ => filter_dec P ys
    end
  end.

Lemma In_filter_dec {X} (P : X -> Prop) `{forall x, Dec (P x)} :
  forall xs x (pf : P x), In x xs -> In (existT P x pf) (filter_dec P xs).
Proof.
  induction xs; intros.
  - destruct H0.
  - destruct H0.
    + simpl.
      destruct dec.
      * left.
        destruct H0.
        f_equal; apply UIP.
      * congruence.
    + simpl.
      destruct dec; [right|idtac]; apply IHxs; auto.
Qed.

#[export]
Instance Dec_open : forall player b pos, Dec (open player b pos).
Proof.
  intros.
  constructor.
  unfold open.
  destruct (lookup_piece pos b).
  - destruct p.
    apply dec.
  - apply dec.
Defined.

#[export]
Instance Dec_not {P}`{Dec P} : Dec (~ P).
Proof.
  apply impl_Dec.
Defined.

Definition enum_chess_moves (st : ChessState) : list (ChessMove st).
Proof.
  pose (Tup := (Piece * Pos * Pos)%type).
  pose (tups := (list_prod (list_prod all_piece all_pos) all_pos) : list Tup).
  pose (piece := fun (tup : Tup) => fst (fst tup)).
  pose (pos1 := fun (tup : Tup) => snd (fst tup)).
  pose (pos2 := fun (tup : Tup) => snd tup).
  pose (good_tup := fun tup =>
    adj (chess_to_play st) (board st) (piece tup) (pos1 tup) (pos2 tup) /\
    (forall pos, lookup_piece pos (make_move (chess_to_play st) (piece tup)
      (pos1 tup) (pos2 tup) (board st)) = Some (chess_to_play st, King) ->
      ~ is_threatened_by
        (make_move (chess_to_play st) (piece tup) (pos1 tup) (pos2 tup) (board st)) pos
        (opp (chess_to_play st)))).
  pose (good_tups := filter_dec
    good_tup tups).
  assert ({x : Tup & good_tup x} -> ChessMove st) as f.
  { intros [tup good_pf].
    unfold good_tup in good_pf.
    apply (mkMove st (pos1 tup) (pos2 tup) (piece tup)); tauto.
  }
  exact (List.map f good_tups).
Defined.

Definition in_check (s : ChessState) : Prop := forall pos,
  lookup_piece pos (board s) = Some (chess_to_play s, King) ->
  is_threatened_by (board s) pos (opp (chess_to_play s)).

Definition atomic_chess_res : ChessState -> option Result :=
  fun s =>
    match enum_chess_moves s with
    | nil =>
      match dec (P := in_check s) with
      | left _ => Some (Win (opp (chess_to_play s)))
      | right _ => Some Draw
      end
    | _ => None
    end.

Lemma in_map_2 {A B : Type} (f : A -> B)
  (xs : list A) (x : A) (y : B) (pf : f x = y) :
  In x xs -> In y (map f xs).
Proof.
  rewrite <- pf; apply in_map.
Qed.

Definition ChessGame : Game. refine ( {|
  GameState := ChessState;
  Move := ChessMove;

  to_play := chess_to_play;
  exec_move := @exec_ChessMove;

  atomic_res := atomic_chess_res;
  enum_moves := enum_chess_moves;

  enum_all := _;
  to_play_exec_move := _;
  atomic_res_nil := _;
  nil_atomic_res := _
  |} ).
  { intros.
    destruct m as [pos1 pos2 piece Hm1 Hm2].
    unfold enum_chess_moves.
    pose (Tup := (Piece * Pos * Pos)%type).
    pose (tups := (list_prod (list_prod all_piece all_pos) all_pos) : list Tup).
    pose (piece_of := fun (tup : Tup) => fst (fst tup)).
    pose (pos1_of := fun (tup : Tup) => snd (fst tup)).
    pose (pos2_of := fun (tup : Tup) => snd tup).
    pose (good_tup := fun tup =>
      adj (chess_to_play b) (board b) (piece_of tup) (pos1_of tup) (pos2_of tup) /\
      (forall pos, lookup_piece pos (make_move (chess_to_play b) (piece_of tup)
        (pos1_of tup) (pos2_of tup) (board b)) = Some (chess_to_play b, King) ->
        ~ is_threatened_by
          (make_move (chess_to_play b) (piece_of tup) (pos1_of tup) (pos2_of tup) (board b)) pos
          (opp (chess_to_play b)))).
    pose (good_tups := filter_dec
    good_tup tups).
    pose (foo := (existT good_tup (piece, pos1, pos2) (conj Hm1 Hm2))).
    apply (in_map_2 _ _ foo).
    { reflexivity. }
    { unfold foo.
      apply In_filter_dec.
      apply in_prod.
      { apply in_prod.
        { apply all_piece_In. }
        { apply all_pos_In. }
      }
      { apply all_pos_In. }
    }
  }
  { intros.
    destruct m.
    reflexivity.
  }
  { unfold atomic_chess_res; intros.
    destruct (enum_chess_moves b); [auto|discriminate].
  }
  { intros.
    unfold atomic_chess_res.
    rewrite H.
    destruct dec; eexists; auto.
  }
Defined.
