
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a



(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun n0 -> f (iter n0 f x))
    n

module Nat =
 struct
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x :: xs -> if in_dec decA x xs then nodup decA xs else x :: (nodup decA xs)

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)

(** val le_le_S_dec : int -> int -> bool **)

let le_le_S_dec =
  (<=)

(** val le_lt_eq_dec : int -> int -> bool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Some a -> a
   | None -> assert false (* absurd case *))

type 'x show =
  'x -> string
  (* singleton inductive, whose constructor was Build_Show *)

(** val show0 : 'a1 show -> 'a1 -> string **)

let show0 show1 =
  show1

(** val show_dec : 'a1 show -> 'a1 -> 'a1 -> bool **)

let show_dec h x x' =
  (=) (show0 h x) (show0 h x')

(** val show_list : 'a1 show -> 'a1 list show **)

let show_list sh xs =
  (^) "[" ((^) (String.concat ";" (map (show0 sh) xs)) "]")

type 'x ord =
  'x -> 'x -> bool
  (* singleton inductive, whose constructor was Build_Ord *)

(** val ord_le_dec : 'a1 ord -> 'a1 -> 'a1 -> bool **)

let ord_le_dec ord0 =
  ord0

(** val insert : 'a1 ord -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insert h x xs = match xs with
| [] -> x :: []
| y :: ys -> if ord_le_dec h x y then x :: xs else y :: (insert h x ys)

(** val insertion_sort : 'a1 ord -> 'a1 list -> 'a1 list **)

let rec insertion_sort h = function
| [] -> []
| x :: ys -> insert h x (insertion_sort h ys)

(** val sublists : int -> 'a1 list -> 'a1 list list **)

let rec sublists n xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [] :: [])
    (fun m ->
    match xs with
    | [] -> []
    | x :: ys -> app (map (fun x0 -> x :: x0) (sublists m ys)) (sublists n ys))
    n

type decision = bool

type 'x discrete =
  'x -> 'x -> decision
  (* singleton inductive, whose constructor was Build_Discrete *)

(** val eq_dec : 'a1 discrete -> 'a1 -> 'a1 -> decision **)

let eq_dec discrete0 =
  discrete0

type 'x enum =
  'x list
  (* singleton inductive, whose constructor was Build_Enum *)

(** val enum0 : 'a1 enum -> 'a1 list **)

let enum0 enum1 =
  enum1

type graph = { vert_disc : __ discrete; vert_enum : __ enum;
               successors : (__ -> __ list) }

type vert = __

(** val graph_Vert_disc : graph -> vert discrete **)

let graph_Vert_disc g =
  g.vert_disc

(** val graph_Vert_enum : graph -> vert enum **)

let graph_Vert_enum g =
  g.vert_enum

(** val first_index_aux_In :
    'a1 discrete -> 'a1 list -> int -> 'a1 -> (int, __) sigT **)

let rec first_index_aux_In h xs n x =
  match xs with
  | [] -> assert false (* absurd case *)
  | y :: l ->
    let d = eq_dec h x y in
    if d then ExistT (n, __) else first_index_aux_In h l (Stdlib.Int.succ n) x

(** val inj_nat : 'a1 discrete -> 'a1 enum -> 'a1 -> int **)

let inj_nat h h0 x =
  projT1 (first_index_aux_In h (enum0 h0) 0 x)

(** val subcount_Ord : 'a1 discrete -> 'a1 enum -> 'a1 ord **)

let subcount_Ord h h0 x y =
  le_le_S_dec (inj_nat h h0 x) (inj_nat h h0 y)

type player =
| White
| Black

(** val show_player : player -> string **)

let show_player = function
| White -> "White"
| Black -> "Black"

(** val show_Player : player show **)

let show_Player =
  show_player

(** val opp : player -> player **)

let opp = function
| White -> Black
| Black -> White

(** val player_id_or_opp_r_t : player -> player -> bool **)

let player_id_or_opp_r_t p p' =
  match p with
  | White -> (match p' with
              | White -> true
              | Black -> false)
  | Black -> (match p' with
              | White -> false
              | Black -> true)

(** val player_eqb : player -> player -> bool **)

let player_eqb p1 p2 =
  match p1 with
  | White -> (match p2 with
              | White -> true
              | Black -> false)
  | Black -> (match p2 with
              | White -> false
              | Black -> true)

type result =
| Win of player
| Draw

type game = { to_play : (__ -> player); exec_move : (__ -> __ -> __);
              atomic_res : (__ -> result option); enum_moves : (__ -> __ list) }

type gameState = __

type move = __

type win =
| Atom_win of gameState
| Eloise_win of gameState * move * win
| Abelard_win of gameState * (move -> win)

type mate = (win, __) sigT

type draw = __draw Lazy.t
and __draw =
| Atom_draw of gameState
| Play_draw of gameState * player * (move -> (draw, win) sum) * move * draw

type 'm stringMap = { empty : (__ -> 'm);
                      add : (__ -> string -> __ -> 'm -> 'm);
                      lookup : (__ -> string -> 'm -> __ option);
                      size : (__ -> 'm -> int) }

(** val empty : 'a1 stringMap -> 'a1 **)

let empty stringMap0 =
  stringMap0.empty __

(** val add : 'a1 stringMap -> string -> 'a2 -> 'a1 -> 'a1 **)

let add stringMap0 x x0 x1 =
  Obj.magic stringMap0.add __ x x0 x1

(** val lookup : 'a1 stringMap -> string -> 'a1 -> 'a2 option **)

let lookup stringMap0 x x0 =
  Obj.magic stringMap0.lookup __ x x0

(** val size : 'a1 stringMap -> 'a1 -> int **)

let size stringMap0 x =
  stringMap0.size __ x

(** val str_add : 'a1 stringMap -> 'a2 show -> 'a2 -> 'a3 -> 'a1 -> 'a1 **)

let str_add h h0 x =
  add h (show0 h0 x)

(** val str_lookup : 'a1 stringMap -> 'a2 show -> 'a2 -> 'a1 -> 'a3 option **)

let str_lookup h h0 x =
  lookup h (show0 h0 x)

(** val str_adds :
    'a1 stringMap -> 'a2 show -> ('a2 * 'a3) list -> 'a1 -> 'a1 **)

let rec str_adds h h0 ps m =
  match ps with
  | [] -> m
  | p :: qs -> let (x, y) = p in str_adds h h0 qs (str_add h h0 x y m)

(** val string_Discrete : string discrete **)

let string_Discrete =
  (=)

(** val str_lookup_adds_invert :
    'a1 stringMap -> 'a2 show -> ('a2 * 'a3) list -> 'a1 -> 'a2 -> 'a3 -> bool **)

let str_lookup_adds_invert h h0 ps m x y =
  let rec f = function
  | [] -> (fun _ _ _ _ -> false)
  | y0 :: l0 ->
    let iHqs = f l0 in
    (fun m0 x' y' _ ->
    let (a, b) = y0 in
    let s = iHqs (str_add h h0 a b m0) x' y' __ in
    if s then true else eq_dec string_Discrete (show0 h0 x') (show0 h0 a))
  in f ps m x y __

(** val in_dec0 : 'a1 discrete -> 'a1 -> 'a1 list -> bool **)

let rec in_dec0 h x = function
| [] -> false
| y :: l -> let d = eq_dec h y x in if d then true else in_dec0 h x l

(** val in_decb : 'a1 discrete -> 'a1 -> 'a1 list -> bool **)

let in_decb h x xs =
  if in_dec0 h x xs then true else false

(** val show_disc : 'a1 show -> 'a1 discrete **)

let show_disc =
  show_dec

type 'x loop_data = { measure : ('x -> int); step : ('x -> 'x) }

(** val loop_aux : 'a1 loop_data -> 'a1 -> 'a1 **)

let rec loop_aux l x =
  let s = le_lt_eq_dec (l.measure (l.step x)) (l.measure x) in
  if s then loop_aux l (l.step x) else x

(** val loop : 'a1 loop_data -> 'a1 -> 'a1 **)

let loop =
  loop_aux

(** val loop_iter_aux : 'a1 loop_data -> int -> 'a1 -> (int, __) sigT **)

let rec loop_iter_aux l _ x =
  let s = le_lt_eq_dec (l.measure (l.step x)) (l.measure x) in
  if s
  then let s0 = let y = l.measure (l.step x) in loop_iter_aux l y (l.step x)
       in
       let ExistT (x0, _) = s0 in ExistT ((Stdlib.Int.succ x0), __)
  else ExistT (0, __)

(** val loop_iter : 'a1 loop_data -> 'a1 -> (int, __) sigT **)

let loop_iter l x =
  loop_iter_aux l (l.measure x) x

type 'x validity_data =
  'x -> __ -> __
  (* singleton inductive, whose constructor was Build_validity_data *)

type 'x valid = __

(** val step_valid :
    'a1 loop_data -> 'a1 validity_data -> 'a1 -> 'a1 valid -> 'a1 valid **)

let step_valid _ v =
  v

(** val iter_step_valid :
    'a1 loop_data -> 'a1 validity_data -> int -> 'a1 -> 'a1 valid -> 'a1 valid **)

let rec iter_step_valid l v n x x_v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x_v)
    (fun n0 ->
    step_valid l v (iter n0 l.step x) (iter_step_valid l v n0 x x_v))
    n

(** val loop_valid :
    'a1 loop_data -> 'a1 validity_data -> 'a1 -> 'a1 valid -> 'a1 valid **)

let loop_valid l v x x0 =
  let s = loop_iter l x in
  let ExistT (x1, _) = s in iter_step_valid l v x1 x x0

(** val list_disc : 'a1 discrete -> 'a1 list discrete **)

let rec list_disc h x x' =
  match x with
  | [] -> (match x' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l ->
    (match x' with
     | [] -> false
     | a :: l0 -> if eq_dec h y a then list_disc h l l0 else false)

type finGame = { enum_states : gameState list;
                 enum_wins : (player -> gameState list) }

type reversible = { enum_preds : (gameState -> gameState list);
                    enum_preds_correct1 : (gameState -> gameState -> __ ->
                                          (move, __) sigT) }

(** val enum_preds_correct1 :
    game -> reversible -> gameState -> gameState -> (move, __) sigT **)

let enum_preds_correct1 _ reversible0 s s' =
  reversible0.enum_preds_correct1 s s' __

type step0 =
| Eloise
| Abelard

(** val switch : step0 -> step0 **)

let switch = function
| Eloise -> Abelard
| Abelard -> Eloise

(** val step_player : step0 -> player -> player **)

let step_player = function
| Eloise -> (fun pl -> pl)
| Abelard -> opp

type 'm tB = { curr : int; last_step : step0; white_positions : 'm;
               black_positions : 'm; last_white_positions : gameState list;
               last_black_positions : gameState list }

(** val tb_lookup :
    game -> gameState show -> 'a1 stringMap -> 'a1 tB -> gameState ->
    (player * int) option **)

let tb_lookup g h2 h4 tb0 s =
  match g.to_play s with
  | White -> str_lookup h4 h2 s tb0.white_positions
  | Black -> str_lookup h4 h2 s tb0.black_positions

(** val tag :
    game -> player -> int -> gameState -> gameState * (player * int) **)

let tag _ winner n s =
  (s, (winner, n))

(** val add_positions :
    game -> gameState show -> 'a1 stringMap -> 'a1 -> player -> int ->
    gameState list -> 'a1 **)

let add_positions g h2 h4 m winner n ps =
  str_adds h4 h2 (map (tag g winner n) ps) m

(** val filter_Nones : ('a1 -> 'a2 option) -> 'a1 list -> 'a1 list **)

let rec filter_Nones f = function
| [] -> []
| x :: xs' ->
  (match f x with
   | Some _ -> filter_Nones f xs'
   | None -> x :: (filter_Nones f xs'))

(** val eloise_step :
    game -> reversible -> gameState show -> 'a1 stringMap -> 'a1 tB -> player
    -> gameState list **)

let eloise_step g h1 h2 h4 tb0 pl =
  let prev =
    match pl with
    | White -> tb0.last_black_positions
    | Black -> tb0.last_white_positions
  in
  let m =
    match pl with
    | White ->
      add_positions g h2 h4 tb0.white_positions
        (step_player tb0.last_step White) tb0.curr tb0.last_white_positions
    | Black ->
      add_positions g h2 h4 tb0.black_positions
        (step_player tb0.last_step Black) tb0.curr tb0.last_black_positions
  in
  let candidates = concat (map h1.enum_preds prev) in
  let candidates' = filter_Nones (fun s -> str_lookup h4 h2 s m) candidates in
  nodup (show_dec h2) candidates'

(** val abelard_step :
    game -> reversible -> gameState show -> 'a1 stringMap -> 'a1 tB -> player
    -> gameState list **)

let abelard_step g h1 h2 h4 tb0 pl =
  let prev =
    match pl with
    | White -> tb0.last_black_positions
    | Black -> tb0.last_white_positions
  in
  let m =
    match pl with
    | White ->
      add_positions g h2 h4 tb0.white_positions
        (step_player tb0.last_step White) tb0.curr tb0.last_white_positions
    | Black ->
      add_positions g h2 h4 tb0.black_positions
        (step_player tb0.last_step Black) tb0.curr tb0.last_black_positions
  in
  let m' =
    match pl with
    | White ->
      add_positions g h2 h4 tb0.black_positions
        (step_player tb0.last_step Black) tb0.curr tb0.last_black_positions
    | Black ->
      add_positions g h2 h4 tb0.white_positions
        (step_player tb0.last_step White) tb0.curr tb0.last_white_positions
  in
  let candidates = concat (map h1.enum_preds prev) in
  let candidates' = filter_Nones (fun s -> str_lookup h4 h2 s m) candidates in
  let candidates'' =
    filter (fun s ->
      forallb (fun m0 ->
        match str_lookup h4 h2 (g.exec_move s m0) m' with
        | Some y -> let (pl', _) = y in player_eqb (opp pl) pl'
        | None -> false) (g.enum_moves s)) candidates'
  in
  nodup (show_dec h2) candidates''

(** val tB_init :
    game -> finGame -> gameState show -> 'a1 stringMap -> 'a1 tB **)

let tB_init _ h h2 h4 =
  { curr = 0; last_step = Abelard; white_positions = (empty h4);
    black_positions = (empty h4); last_white_positions =
    (nodup (show_dec h2) (h.enum_wins Black)); last_black_positions =
    (nodup (show_dec h2) (h.enum_wins White)) }

(** val tB_step :
    game -> reversible -> gameState show -> 'a1 stringMap -> 'a1 tB -> 'a1 tB **)

let tB_step g h1 h2 h4 tb0 =
  { curr = (Stdlib.Int.succ tb0.curr); last_step = (switch tb0.last_step);
    white_positions =
    (add_positions g h2 h4 tb0.white_positions
      (step_player tb0.last_step White) tb0.curr tb0.last_white_positions);
    black_positions =
    (add_positions g h2 h4 tb0.black_positions
      (step_player tb0.last_step Black) tb0.curr tb0.last_black_positions);
    last_white_positions =
    (match tb0.last_step with
     | Eloise -> abelard_step g h1 h2 h4 tb0 White
     | Abelard -> eloise_step g h1 h2 h4 tb0 White); last_black_positions =
    (match tb0.last_step with
     | Eloise -> abelard_step g h1 h2 h4 tb0 Black
     | Abelard -> eloise_step g h1 h2 h4 tb0 Black) }

(** val num_left : game -> finGame -> 'a1 stringMap -> 'a1 tB -> int **)

let num_left _ h h4 tb0 =
  sub (sub (length h.enum_states) (size h4 tb0.white_positions))
    (size h4 tb0.black_positions)

(** val tB_loop_data :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap -> 'a1
    tB loop_data **)

let tB_loop_data g h h1 h2 h4 =
  { measure = (num_left g h h4); step = (tB_step g h1 h2 h4) }

(** val tB_final :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap -> 'a1 tB **)

let tB_final g h h1 h2 h4 =
  loop (tB_loop_data g h h1 h2 h4) (tB_init g h h2 h4)

type satMate = (win, __) sigT

type 'm tB_valid = { tb_satMate : (gameState -> player -> int -> __ ->
                                  satMate);
                     lwp_satMate : (gameState -> __ -> satMate);
                     lbp_satMate : (gameState -> __ -> satMate) }

(** val tb_satMate :
    game -> gameState show -> 'a1 stringMap -> 'a1 tB -> 'a1 tB_valid ->
    gameState -> player -> int -> satMate **)

let tb_satMate _ _ _ _ t s pl n =
  t.tb_satMate s pl n __

(** val lwp_satMate :
    game -> gameState show -> 'a1 stringMap -> 'a1 tB -> 'a1 tB_valid ->
    gameState -> satMate **)

let lwp_satMate _ _ _ _ t s =
  t.lwp_satMate s __

(** val lbp_satMate :
    game -> gameState show -> 'a1 stringMap -> 'a1 tB -> 'a1 tB_valid ->
    gameState -> satMate **)

let lbp_satMate _ _ _ _ t s =
  t.lbp_satMate s __

(** val tB_init_valid :
    game -> finGame -> gameState show -> 'a1 stringMap -> 'a1 tB_valid **)

let tB_init_valid _ _ _ _ =
  { tb_satMate = (fun _ _ _ _ -> assert false (* absurd case *));
    lwp_satMate = (fun s _ -> ExistT ((Atom_win s), __)); lbp_satMate =
    (fun s _ -> ExistT ((Atom_win s), __)) }

(** val in_map_sig :
    'a2 discrete -> ('a1 -> 'a2) -> 'a1 list -> 'a2 -> ('a1, __) sigT **)

let rec in_map_sig h5 f xs y =
  match xs with
  | [] -> assert false (* absurd case *)
  | y0 :: l ->
    let d = eq_dec h5 (f y0) y in
    if d
    then ExistT (y0, __)
    else let s = in_map_sig h5 f l y in
         let ExistT (x, _) = s in ExistT (x, __)

(** val none_or_all_Some :
    ('a1 -> 'a2 option) -> 'a1 list -> (('a1, __) sigT, ('a2 list, __) sigT)
    sum **)

let rec none_or_all_Some f = function
| [] -> Inr (ExistT ([], __))
| y :: l ->
  let o = f y in
  (match o with
   | Some a ->
     (match none_or_all_Some f l with
      | Inl a0 -> let ExistT (x, _) = a0 in Inl (ExistT (x, __))
      | Inr b -> let ExistT (x, _) = b in Inr (ExistT ((a :: x), __)))
   | None -> Inl (ExistT (y, __)))

(** val in_concat_sig :
    'a1 discrete -> 'a1 list list -> 'a1 -> ('a1 list, __) sigT **)

let rec in_concat_sig h5 xss x =
  match xss with
  | [] -> assert false (* absurd case *)
  | y :: l ->
    let s = in_dec0 h5 x y in
    if s
    then ExistT (y, __)
    else let s0 = in_concat_sig h5 l x in
         let ExistT (x0, _) = s0 in ExistT (x0, __)

(** val tB_step_valid :
    game -> reversible -> gameState show -> 'a1 stringMap -> 'a1 tB -> 'a1
    tB_valid -> 'a1 tB_valid **)

let tB_step_valid g h1 h2 h4 tb0 v =
  { tb_satMate = (fun s pl n _ ->
    let p = g.to_play s in
    (match p with
     | White ->
       let s0 =
         str_lookup_adds_invert h4 h2
           (map (tag g (step_player tb0.last_step White) tb0.curr)
             tb0.last_white_positions) tb0.white_positions s (pl, n)
       in
       if s0
       then lwp_satMate g h2 h4 tb0 v s
       else tb_satMate g h2 h4 tb0 v s pl n
     | Black ->
       let s0 =
         str_lookup_adds_invert h4 h2
           (map (tag g (step_player tb0.last_step Black) tb0.curr)
             tb0.last_black_positions) tb0.black_positions s (pl, n)
       in
       if s0
       then lbp_satMate g h2 h4 tb0 v s
       else tb_satMate g h2 h4 tb0 v s pl n)); lwp_satMate = (fun s _ ->
    let s0 = tb0.last_step in
    (match s0 with
     | Eloise ->
       let o = g.atomic_res s in
       (match o with
        | Some _ -> assert false (* absurd case *)
        | None ->
          let x = fun m' ->
            let o0 =
              str_lookup h4 h2 (g.exec_move s m')
                (add_positions g h2 h4 tb0.black_positions Black tb0.curr
                  tb0.last_black_positions)
            in
            (match o0 with
             | Some a ->
               let (a0, b) = a in
               (match a0 with
                | White -> assert false (* absurd case *)
                | Black ->
                  let s1 =
                    str_lookup_adds_invert h4 h2
                      (map (tag g Black tb0.curr) tb0.last_black_positions)
                      tb0.black_positions (g.exec_move s m') (Black, b)
                  in
                  if s1
                  then let sm = lbp_satMate g h2 h4 tb0 v (g.exec_move s m')
                       in
                       let ExistT (x, _) = sm in ExistT (x, __)
                  else let sm = fun _ ->
                         tb_satMate g h2 h4 tb0 v (g.exec_move s m') Black b
                       in
                       let s2 = sm __ in
                       let ExistT (x, _) = s2 in ExistT (x, __))
             | None -> assert false (* absurd case *))
          in
          let w' = Abelard_win (s, (fun m -> projT1 (x m))) in ExistT (w', __))
     | Abelard ->
       let s1 =
         in_concat_sig (show_disc h2)
           (map h1.enum_preds tb0.last_black_positions) s
       in
       let ExistT (x, _) = s1 in
       let s2 =
         in_map_sig (list_disc (show_disc h2)) h1.enum_preds
           tb0.last_black_positions x
       in
       let ExistT (x0, _) = s2 in
       let s3 = enum_preds_correct1 g h1 s x0 in
       let ExistT (x1, _) = s3 in
       let sm = lbp_satMate g h2 h4 tb0 v (g.exec_move s x1) in
       let ExistT (x2, _) = sm in
       let o = g.atomic_res s in
       (match o with
        | Some _ -> assert false (* absurd case *)
        | None -> ExistT ((Eloise_win (s, x1, x2)), __)))); lbp_satMate =
    (fun s _ ->
    let s0 = tb0.last_step in
    (match s0 with
     | Eloise ->
       let o = g.atomic_res s in
       (match o with
        | Some _ -> assert false (* absurd case *)
        | None ->
          let x = fun m' ->
            let o0 =
              str_lookup h4 h2 (g.exec_move s m')
                (add_positions g h2 h4 tb0.white_positions White tb0.curr
                  tb0.last_white_positions)
            in
            (match o0 with
             | Some a ->
               let (a0, b) = a in
               (match a0 with
                | White ->
                  let s1 =
                    str_lookup_adds_invert h4 h2
                      (map (tag g White tb0.curr) tb0.last_white_positions)
                      tb0.white_positions (g.exec_move s m') (White, b)
                  in
                  if s1
                  then let sm = lwp_satMate g h2 h4 tb0 v (g.exec_move s m')
                       in
                       let ExistT (x, _) = sm in ExistT (x, __)
                  else let sm = fun _ ->
                         tb_satMate g h2 h4 tb0 v (g.exec_move s m') White b
                       in
                       let s2 = sm __ in
                       let ExistT (x, _) = s2 in ExistT (x, __)
                | Black -> assert false (* absurd case *))
             | None -> assert false (* absurd case *))
          in
          let w' = Abelard_win (s, (fun m -> projT1 (x m))) in ExistT (w', __))
     | Abelard ->
       let s1 =
         in_concat_sig (show_disc h2)
           (map h1.enum_preds tb0.last_white_positions) s
       in
       let ExistT (x, _) = s1 in
       let s2 =
         in_map_sig (list_disc (show_disc h2)) h1.enum_preds
           tb0.last_white_positions x
       in
       let ExistT (x0, _) = s2 in
       let s3 = enum_preds_correct1 g h1 s x0 in
       let ExistT (x1, _) = s3 in
       let sm = lwp_satMate g h2 h4 tb0 v (g.exec_move s x1) in
       let ExistT (x2, _) = sm in
       let o = g.atomic_res s in
       (match o with
        | Some _ -> assert false (* absurd case *)
        | None -> ExistT ((Eloise_win (s, x1, x2)), __)))) }

(** val tB_validity_data :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap -> 'a1
    tB validity_data **)

let tB_validity_data g _ h1 h2 h4 =
  Obj.magic tB_step_valid g h1 h2 h4

(** val tB_final_valid :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap -> 'a1
    tB_valid **)

let tB_final_valid g h h1 h2 h4 =
  Obj.magic loop_valid (tB_loop_data g h h1 h2 h4)
    (tB_validity_data g h h1 h2 h4) (tB_init g h h2 h4)
    (tB_init_valid g h h2 h4)

(** val remove : 'a1 discrete -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove h5 x = function
| [] -> []
| y :: xs' ->
  if eq_dec h5 x y then remove h5 x xs' else y :: (remove h5 x xs')

(** val tB_final_lookup_satMate :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap ->
    gameState -> player -> int -> satMate **)

let tB_final_lookup_satMate g h h1 h2 h4 s pl n =
  tb_satMate g h2 h4 (tB_final g h h1 h2 h4) (tB_final_valid g h h1 h2 h4) s
    pl n

(** val tB_lookup_None :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap ->
    gameState -> (__, __ * (move, __) sigT) sum **)

let tB_lookup_None g h h1 h2 h4 s =
  let o = g.atomic_res s in
  (match o with
   | Some a ->
     (match a with
      | Win _ -> assert false (* absurd case *)
      | Draw -> Inl __)
   | None ->
     Inr (__,
       (let s0 =
          none_or_all_Some (fun m ->
            tb_lookup g h2 h4 (tB_final g h h1 h2 h4) (g.exec_move s m))
            (g.enum_moves s)
        in
        match s0 with
        | Inl a -> let ExistT (x, _) = a in ExistT (x, __)
        | Inr _ -> assert false (* absurd case *))))

(** val tB_final_lookup_draw :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap ->
    gameState -> draw **)

let rec tB_final_lookup_draw g h h1 h2 h4 s =
  let s0 = tB_lookup_None g h h1 h2 h4 s in
  (match s0 with
   | Inl _ -> lazy (Atom_draw s)
   | Inr b ->
     let (_, b0) = b in
     let ExistT (x, _) = b0 in
     lazy (Play_draw (s, (g.to_play s), (fun m ->
     let o = tb_lookup g h2 h4 (tB_final g h h1 h2 h4) (g.exec_move s m) in
     (match o with
      | Some a ->
        let (a0, b1) = a in
        let s1 = player_id_or_opp_r_t (g.to_play s) a0 in
        if s1
        then assert false (* absurd case *)
        else Inr
               (let tb0 = tB_final g h h1 h2 h4 in
                let t = tB_final_valid g h h1 h2 h4 in
                let s2 = g.exec_move s m in
                let ExistT (x0, _) = tb_satMate g h2 h4 tb0 t s2 a0 b1 in x0)
      | None -> Inl (tB_final_lookup_draw g h h1 h2 h4 (g.exec_move s m)))),
     x, (tB_final_lookup_draw g h h1 h2 h4 (g.exec_move s x)))))

(** val tB_final_lookup_mate :
    game -> finGame -> reversible -> gameState show -> 'a1 stringMap ->
    gameState -> player -> int -> mate **)

let tB_final_lookup_mate g h h1 h2 h4 s pl n =
  let s0 = tB_final_lookup_satMate g h h1 h2 h4 s pl n in
  let ExistT (x, _) = s0 in ExistT (x, __)

type 'm correctTablebase = { tb : 'm tB;
                             tb_lookup_mate : (gameState -> player -> int ->
                                              __ -> mate);
                             tb_lookup_draw : (gameState -> __ -> draw) }

(** val certified_TB :
    'a1 stringMap -> game -> gameState show -> finGame -> reversible ->
    (gameState -> move discrete) -> 'a1 correctTablebase **)

let certified_TB h g h0 h1 h2 _ =
  { tb = (tB_final g h1 h2 h0 h); tb_lookup_mate = (fun x x0 x1 _ ->
    tB_final_lookup_mate g h1 h2 h0 h x x0 x1); tb_lookup_draw = (fun x _ ->
    tB_final_lookup_draw g h1 h2 h0 h x) }

type 'v oM = 'v M.t

(** val empty0 : 'a1 oM **)

let empty0 = M.empty

(** val add0 : string -> 'a1 -> 'a1 oM -> 'a1 oM **)

let add0 = M.insert

(** val lookup0 : string -> 'a1 oM -> 'a1 option **)

let lookup0 = M.lookup

(** val size0 : 'a1 oM -> int **)

let size0 = M.size

(** val oMap : __ oM stringMap **)

let oMap =
  { empty = (fun _ -> empty0); add = (fun _ -> add0); lookup = (fun _ ->
    lookup0); size = (fun _ -> size0) }

type bG_State = { to_play0 : player; bear : vert; hunters : vert list }

type bearMv =
  vert
  (* singleton inductive, whose constructor was Build_BearMv *)

(** val b_dest : graph -> bG_State -> bearMv -> vert **)

let b_dest _ _ b =
  b

type hunterMv = { h_orig : vert; h_dest : vert }

type bG_Move =
| BearMove of bearMv
| HunterMove of hunterMv

(** val exec_move0 : graph -> bG_State -> bG_Move -> bG_State **)

let exec_move0 g s = function
| BearMove b ->
  { to_play0 = White; bear = (b_dest g s b); hunters = s.hunters }
| HunterMove h ->
  { to_play0 = Black; bear = s.bear; hunters =
    (insertion_sort (subcount_Ord (graph_Vert_disc g) (graph_Vert_enum g))
      (h.h_dest :: (remove (graph_Vert_disc g) h.h_orig s.hunters))) }

(** val pf_map : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec pf_map xs f =
  match xs with
  | [] -> []
  | a :: l -> (f a __) :: (pf_map l (fun x' _ -> f x' __))

(** val eqb : 'a1 discrete -> 'a1 -> 'a1 -> bool **)

let eqb h x x' =
  if eq_dec h x x' then true else false

(** val enum_moves0 : graph -> bG_State -> bG_Move list **)

let enum_moves0 g s =
  let p = s.to_play0 in
  (match p with
   | White ->
     concat
       (pf_map s.hunters (fun h _ ->
         pf_map
           (filter (fun v ->
             (&&) (negb (eqb (graph_Vert_disc g) v s.bear))
               ((||) (negb (in_decb (graph_Vert_disc g) v s.hunters))
                 (eqb (graph_Vert_disc g) v h))) (g.successors h))
           (fun v _ -> HunterMove { h_orig = h; h_dest = v })))
   | Black ->
     pf_map
       (filter (fun v -> negb (in_decb (graph_Vert_disc g) v s.hunters))
         (g.successors s.bear)) (fun v _ -> BearMove v))

(** val atomic_res0 : graph -> bG_State -> result option **)

let atomic_res0 g s =
  match enum_moves0 g s with
  | [] ->
    (match s.to_play0 with
     | White -> Some Draw
     | Black -> Some (Win White))
  | _ :: _ -> None

(** val bearGame : graph -> game **)

let bearGame g =
  { to_play = (Obj.magic (fun b -> b.to_play0)); exec_move =
    (Obj.magic exec_move0 g); atomic_res = (Obj.magic atomic_res0 g);
    enum_moves = (Obj.magic enum_moves0 g) }

(** val bearGameStateShow : graph -> vert show -> gameState show **)

let bearGameStateShow _ sh s =
  (^) "("
    ((^) (show0 show_Player (Obj.magic s).to_play0)
      ((^) ","
        ((^) (show0 sh (Obj.magic s).bear)
          ((^) "," ((^) (show0 (show_list sh) (Obj.magic s).hunters) ")")))))

(** val all_BG_States : player -> graph -> bG_State list **)

let all_BG_States pl g =
  concat
    (map (fun b ->
      let hunter_lists =
        sublists (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
          (filter (fun h -> negb (eqb (graph_Vert_disc g) h b))
            (enum0 (graph_Vert_enum g)))
      in
      pf_map hunter_lists (fun hs _ -> { to_play0 = pl; bear = b; hunters =
        hs })) (enum0 (graph_Vert_enum g)))

(** val fin_BearGame : graph -> finGame **)

let fin_BearGame g =
  { enum_states =
    (app (Obj.magic all_BG_States White g) (Obj.magic all_BG_States Black g));
    enum_wins = (fun pl ->
    match pl with
    | White ->
      filter (fun s ->
        match enum_moves0 g (Obj.magic s) with
        | [] -> true
        | _ :: _ -> false) (Obj.magic all_BG_States Black g)
    | Black -> []) }

(** val switch_player : graph -> bG_State -> bG_State **)

let switch_player _ s =
  { to_play0 = (opp s.to_play0); bear = s.bear; hunters = s.hunters }

(** val reversible_BearGame : graph -> reversible **)

let reversible_BearGame g =
  { enum_preds = (fun s ->
    map (fun m ->
      Obj.magic switch_player g
        (exec_move0 g (switch_player g (Obj.magic s)) m))
      (enum_moves0 g (switch_player g (Obj.magic s)))); enum_preds_correct1 =
    (fun s _ _ -> ExistT ((Obj.magic (BearMove (Obj.magic s).bear)), __)) }

(** val discMove_BearGame : graph -> gameState -> move discrete **)

let discMove_BearGame g s m m' =
  match Obj.magic m with
  | BearMove b ->
    (match Obj.magic m' with
     | BearMove b0 ->
       eq_dec (graph_Vert_disc g) (b_dest g (Obj.magic s) b)
         (b_dest g (Obj.magic s) b0)
     | HunterMove _ -> assert false (* absurd case *))
  | HunterMove h ->
    (match Obj.magic m' with
     | BearMove _ -> assert false (* absurd case *)
     | HunterMove h0 ->
       let d = eq_dec (graph_Vert_disc g) h.h_orig h0.h_orig in
       if d then eq_dec (graph_Vert_disc g) h.h_dest h0.h_dest else false)

(** val bear_TB : graph -> vert show -> __ oM correctTablebase **)

let bear_TB g sh =
  certified_TB oMap (bearGame g) (bearGameStateShow g sh) (fin_BearGame g)
    (reversible_BearGame g) (discMove_BearGame g)

type spoke =
| S1
| S2
| S3
| S4
| S5
| S6
| S7
| S8

(** val clockwise : spoke -> spoke **)

let clockwise = function
| S1 -> S2
| S2 -> S3
| S3 -> S4
| S4 -> S5
| S5 -> S6
| S6 -> S7
| S7 -> S8
| S8 -> S1

(** val c_clockwise : spoke -> spoke **)

let c_clockwise = function
| S1 -> S8
| S2 -> S1
| S3 -> S2
| S4 -> S3
| S5 -> S4
| S6 -> S5
| S7 -> S6
| S8 -> S7

(** val list_spokes : spoke list **)

let list_spokes =
  S1 :: (S2 :: (S3 :: (S4 :: (S5 :: (S6 :: (S7 :: (S8 :: [])))))))

(** val show_spoke : spoke -> string **)

let show_spoke = function
| S1 -> "1"
| S2 -> "2"
| S3 -> "3"
| S4 -> "4"
| S5 -> "5"
| S6 -> "6"
| S7 -> "7"
| S8 -> "8"

type spokeLoc =
| Mid
| L
| R

(** val show_loc : spokeLoc -> string **)

let show_loc = function
| Mid -> "M"
| L -> "L"
| R -> "R"

(** val list_locs : spokeLoc list **)

let list_locs =
  Mid :: (L :: (R :: []))

type rWVert =
| Center
| SpokeVert of spoke * spokeLoc

(** val show_RWVert : rWVert show **)

let show_RWVert = function
| Center -> "Center"
| SpokeVert (s, l) -> (^) "Spoke" ((^) (show_spoke s) (show_loc l))

(** val romanWheel : graph **)

let romanWheel =
  { vert_disc = (show_disc (Obj.magic show_RWVert)); vert_enum =
    ((Obj.magic Center) :: (concat
                             (map (fun s ->
                               map (Obj.magic (fun x -> SpokeVert (s, x)))
                                 list_locs) list_spokes))); successors =
    (fun v ->
    match Obj.magic v with
    | Center -> map (fun s -> Obj.magic (SpokeVert (s, Mid))) list_spokes
    | SpokeVert (s, l) ->
      (match l with
       | Mid ->
         (Obj.magic Center) :: ((Obj.magic (SpokeVert (s, L))) :: ((Obj.magic
                                                                    (SpokeVert
                                                                    (s, R))) :: []))
       | L ->
         (Obj.magic (SpokeVert (s, R))) :: ((Obj.magic (SpokeVert (s, Mid))) :: (
           (Obj.magic (SpokeVert ((c_clockwise s), R))) :: []))
       | R ->
         (Obj.magic (SpokeVert (s, L))) :: ((Obj.magic (SpokeVert (s, Mid))) :: (
           (Obj.magic (SpokeVert ((clockwise s), L))) :: [])))) }

(** val show_RWV : vert show **)

let show_RWV =
  Obj.magic show_RWVert

(** val rW_TB : __ oM correctTablebase **)

let rW_TB =
  bear_TB romanWheel show_RWV

(** val wps : (player * int) oM **)

let wps =
  (Obj.magic rW_TB).tb.white_positions

(** val bps : (player * int) oM **)

let bps =
  (Obj.magic rW_TB).tb.black_positions
