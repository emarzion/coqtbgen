Require Import List.
Import ListNotations.
Require Import PrimInt63.
Require Import Uint63.

Require Import Games.Game.Player.
Require Import Games.Game.Game.
Require Import Games.Game.Draw.
Require Import Games.Game.Win.
Require Import Games.Game.TB.
Require Import Games.Util.AssocList.
Require Import Games.Util.IntHash.
Require Import Games.Util.Dec.

Require Import Games.Util.OMap.
Require Import Games.Game.OCamlTB.

Inductive Pos :=
  A | B | C | D | E | F.

Definition St : Type :=
  Player * Pos.

Inductive LRS :=
  | LRS_L (* left *)
  | LRS_R (* right *)
  | LRS_S (* still *).

Definition enum_LRS : list LRS :=
  [ LRS_L; LRS_R; LRS_S ].

Definition LRS_all : forall x,
  In x enum_LRS.
Proof.
  intros []; simpl; auto.
Qed.

Inductive LS :=
  | LS_L
  | LS_S.

Definition enum_LS : list LS :=
  [ LS_L; LS_S ].

Definition LS_all : forall x,
  In x enum_LS.
Proof.
  intros []; simpl; auto.
Qed.

Inductive RS :=
  | RS_R
  | RS_S.

Definition enum_RS : list RS :=
  [ RS_R; RS_S ].

Definition RS_all : forall x,
  In x enum_RS.
Proof.
  intros []; simpl; auto.
Qed.

Global Instance Empty_set_disc : Discrete Empty_set.
Proof.
  constructor; unfold decision; decide equality.
Defined.

Global Instance LRS_disc : Discrete LRS.
Proof.
  constructor; unfold decision; decide equality.
Defined.

Global Instance LS_disc : Discrete LS.
Proof.
  constructor; unfold decision; decide equality.
Defined.

Global Instance RS_disc : Discrete RS.
Proof.
  constructor; unfold decision; decide equality.
Defined.

Definition Mv : St -> Type :=
  fun '(pl, pos) =>
    match pl with
    | White =>
      match pos with
      | A => RS
      | B | C | D => LRS
      | E => RS
      | F => Empty_set
      end
    | Black =>
      match pos with
      | A => Empty_set
      | B => LS
      | C | D | E => LRS
      | F => LS
      end
    end.

Global Instance Mv_disc : forall {s}, Discrete (Mv s).
Proof.
  intros [pl pos]; destruct pl; destruct pos; (
  exact LRS_disc ||
  exact RS_disc  ||
  exact LS_disc  ||
  exact Empty_set_disc
  ).
Defined.

Definition winning_state : St -> option Result :=
  fun '(pl, pos) =>
    match pl, pos with
    | White, F => Some (Win Black)
    | Black, A => Some (Win White)
    | _, _ => None
    end.

Definition exec {s} : Mv s -> St :=
  match s with
  | (White, A) => fun m =>
    match m with
    | RS_R => (Black, B)
    | RS_S => (Black, A)
    end
  | (White, B) => fun m =>
    match m with
    | LRS_L => (Black, A)
    | LRS_R => (Black, C)
    | LRS_S => (Black, B)
    end
  | (White, C) => fun m =>
    match m with
    | LRS_L => (Black, B)
    | LRS_R => (Black, D)
    | LRS_S => (Black, C)
    end
  | (White, D) => fun m =>
    match m with
    | LRS_L => (Black, C)
    | LRS_R => (Black, E)
    | LRS_S => (Black, D)
    end
  | (White, E) => fun m =>
    match m with
    | RS_R => (Black, F)
    | RS_S => (Black, E)
    end
  | (White, F) => fun m =>
    match m with
    end
  | (Black, A) => fun m =>
    match m with
    end
  | (Black, B) => fun m =>
    match m with
    | LS_L => (White, A)
    | LS_S => (White, B)
    end
  | (Black, C) => fun m =>
    match m with
    | LRS_L => (White, B)
    | LRS_R => (White, D)
    | LRS_S => (White, C)
    end
  | (Black, D) => fun m =>
    match m with
    | LRS_L => (White, C)
    | LRS_R => (White, E)
    | LRS_S => (White, D)
    end
  | (Black, E) => fun m =>
    match m with
    | LRS_L => (White, D)
    | LRS_R => (White, F)
    | LRS_S => (White, E)
    end
  | (Black, F) => fun m =>
    match m with
    | LS_L => (White, E)
    | LS_S => (White, F)
    end
  end.

Definition enum_Mv : forall {s}, list (Mv s) :=
  fun '(pl, pos) =>
    match pl with
    | White =>
      match pos with
      | A => enum_RS
      | B | C | D => enum_LRS
      | E => enum_RS
      | F => []
      end
    | Black =>
      match pos with
      | A => []
      | B => enum_LS
      | C | D | E => enum_LRS
      | F => enum_LS
      end
    end.

Definition SampleGame : Game. refine ( {|
  GameState := St;
  Move := Mv;

  to_play := fst;
  exec_move := @exec;
  atomic_res := winning_state;
  enum_moves := @enum_Mv;

  enum_all := _;
  to_play_exec_move := _;
  atomic_res_nil := _;
  nil_atomic_res := _;
  |}).
Proof.
  - intros [[][]];
      (apply RS_all ||
       apply LRS_all ||
       apply LS_all ||
       intros []
      ).
  - intros [[][]] []; reflexivity.
  - intros [[][]] res pf;
      simpl in *; (discriminate||auto).
  - intros [[][]] pf; simpl in *;
      (discriminate || eexists; eauto).
Defined.

Lemma conditional_white_D_draw :
  @draw SampleGame (Black, C) ->
  @draw SampleGame (White, D).
Proof.
  intro d.
  refine (@play_draw SampleGame (White, D) White _ _ _ LRS_L d).
  - reflexivity.
  - reflexivity.
  - intros []; simpl.
    + left; exact d.
    + right.
      apply (@eloise_win SampleGame Black (Black, E) eq_refl eq_refl LRS_R).
      simpl.
      apply atom_win.
      reflexivity.
    + right.
      apply (@eloise_win SampleGame Black (Black, D) eq_refl eq_refl LRS_R).
      simpl.
      apply abelard_win; try reflexivity.
      intros [].
      * simpl.
        apply (@eloise_win SampleGame Black (Black, F) eq_refl eq_refl LS_S).
        apply atom_win. reflexivity.
      * simpl.
        apply (@eloise_win SampleGame Black (Black, E) eq_refl eq_refl LRS_R).
        apply atom_win. reflexivity.
Defined.

CoFixpoint black_C_draw :
  @draw SampleGame (Black, C).
  refine (@play_draw SampleGame (Black, C) Black _ _ _ LRS_R _).
Proof.
  - reflexivity.
  - reflexivity.
  - intros []; simpl.
    + right.
      apply (@eloise_win SampleGame White (White, B) eq_refl eq_refl LRS_L).
      apply atom_win.
      reflexivity.
    + left.
      apply conditional_white_D_draw.
      auto.
    + right.
      apply (@eloise_win SampleGame White (White, C) eq_refl eq_refl LRS_L).
      apply abelard_win; try reflexivity.
      intros [].
      * simpl.
        apply (@eloise_win SampleGame White (White, A) eq_refl eq_refl RS_S).
        apply atom_win.
        reflexivity.
      * simpl.
        apply (@eloise_win SampleGame White (White, B) eq_refl eq_refl LRS_L).
        apply atom_win.
        reflexivity.
  - simpl.
    apply conditional_white_D_draw.
    auto.
Defined.

Global Instance Fin_SampleGame : FinGame SampleGame.
Proof.
  refine ( {|
    enum_states := [
      (White, A) : GameState SampleGame;
      (White, B);
      (White, C);
      (White, D);
      (White, E);
      (White, F);
      (Black, A);
      (Black, B);
      (Black, C);
      (Black, D);
      (Black, E);
      (Black, F)
    ];

    enum_wins p :=
      match p with
      | White => [(Black, A)]
      | Black => [(White, F)]
      end;
    enum_states_correct := _;
    enum_wins_correct1 := _;
    enum_wins_correct2 := _;
  |} ).
  - intros [[] []]; simpl; tauto.
  - intros [[] []] [] []; simpl in *;
      (tauto || discriminate).
  - intros [[] []] [] pf; simpl in *;
      (tauto || discriminate).
Defined.

Global Instance Nice_SampleGame : NiceGame SampleGame.
Proof.
  constructor.
  intros [[] []] [] pf; simpl in *;
    (reflexivity || discriminate).
Qed.

Definition enum_preds_SampleGame (s : GameState SampleGame) : list St :=
  match s with
  | (White, A) => [(Black, B)]
  | (White, B) => [(Black, B); (Black, C)]
  | (White, C) => [(Black, C); (Black, D)]
  | (White, D) => [(Black, C); (Black, D); (Black, E)]
  | (White, E) => [(Black, D); (Black, E); (Black, F)]
  | (White, F) => [(Black, E); (Black, F)]
  | (Black, A) => [(White, A); (White, B)]
  | (Black, B) => [(White, A); (White, B); (White, C)]
  | (Black, C) => [(White, B); (White, C); (White, D)]
  | (Black, D) => [(White, C); (White, D)]
  | (Black, E) => [(White, D); (White, E)]
  | (Black, F) => [(White, E)]
  end.

Global Instance Reverse_SampleGame : Reversible SampleGame.
Proof.
  refine ( {|
    enum_preds := enum_preds_SampleGame;
    enum_preds_correct1 := _;
    enum_preds_correct2 := _
  |} ).
  - intros [[] []] [[] []] pf; simpl in *;
    try (exfalso; intuition; discriminate).
    + now exists RS_S.
    + now exists RS_R.
    + now exists LRS_L.
    + now exists LRS_S.
    + now exists LRS_R.
    + now exists LRS_L.
    + now exists LRS_S.
    + now exists LRS_R.
    + now exists LRS_L.
    + now exists LRS_S.
    + now exists LRS_R.
    + now exists RS_S.
    + now exists RS_R.
    + now exists LS_L.
    + now exists LS_S.
    + now exists LRS_L.
    + now exists LRS_S.
    + now exists LRS_R.
    + now exists LRS_L.
    + now exists LRS_S.
    + now exists LRS_R.
    + now exists LRS_L.
    + now exists LRS_S.
    + now exists LRS_R.
    + now exists LS_L.
    + now exists LS_S.
  - intros [[] []] []; simpl; tauto.
Defined.

Definition hash_St (st : St) : int :=
  match st with
  | (White,A) => 0
  | (White,B) => 1
  | (White,C) => 2
  | (White,D) => 3
  | (White,E) => 4
  | (White,F) => 5
  | (Black,A) => 6
  | (Black,B) => 7
  | (Black,C) => 8
  | (Black,D) => 9
  | (Black,E) => 10
  | (Black,F) => 11
  end.

Global Instance foo : IntHash St. refine {|
  hash := hash_St;
  hash_inj := _;
  |}.
Proof.
  intros [[][]] [[][]]; simpl; intro pf; try reflexivity;
  discriminate ((f_equal to_Z pf)).
Defined.

Definition TB_Sample : OCamlTablebase SampleGame :=
  certified_TB.
