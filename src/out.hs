{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Out where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Empty_set = () -- empty inductive

empty_set_rect :: Empty_set -> a1
empty_set_rect _ =
  Prelude.error "absurd case"

empty_set_rec :: Empty_set -> a1
empty_set_rec =
  empty_set_rect

data Bool =
   True
 | False

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True -> Left;
                   False -> Right}) (\x ->
    case x of {
     True -> Right;
     False -> Left}) b1 b2

flip :: (a1 -> a2 -> a3) -> a2 -> a1 -> a3
flip f x y =
  f y x

eq_dec :: Nat -> Nat -> Sumbool
eq_dec n =
  nat_rec (\m -> case m of {
                  O -> Left;
                  S _ -> Right}) (\_ iHn m ->
    case m of {
     O -> Right;
     S n0 -> iHn n0}) n

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 _ iHl ->
    let {s = h a0 a} in case s of {
                         Left -> Left;
                         Right -> iHl}) l

concat :: (List (List a1)) -> List a1
concat l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f l =
  case l of {
   Nil -> True;
   Cons a l0 -> andb (f a) (forallb f l0)}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

nodup :: (a1 -> a1 -> Sumbool) -> (List a1) -> List a1
nodup decA l =
  case l of {
   Nil -> Nil;
   Cons x xs ->
    case in_dec decA x xs of {
     Left -> nodup decA xs;
     Right -> Cons x (nodup decA xs)}}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii b b0 b1 b2 b3 b4 b5 b6 -> f b b0 b1 b2 b3 b4 b5 b6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15))
                    (\_ -> Right) (bool_dec b6 b14)) (\_ -> Right)
                  (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10))
          (\_ -> Right) (bool_dec b1 b9)) (\_ -> Right) (bool_dec b0 b8)}) a
    b

data String =
   EmptyString
 | String0 Ascii0 String

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ h x ->
    case x of {
     EmptyString -> Right;
     String0 a0 s ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (h s)) (\_ ->
        Right) (ascii_dec a a0)}) s1 s2

append :: String -> String -> String
append s1 s2 =
  case s1 of {
   EmptyString -> s2;
   String0 c s1' -> String0 c (append s1' s2)}

type Decision = Sumbool

type Discrete x =
  x -> x -> Decision
  -- singleton inductive, whose constructor was Build_Discrete
  
eq_dec0 :: (Discrete a1) -> a1 -> a1 -> Decision
eq_dec0 discrete =
  discrete

data Player =
   White
 | Black

opp :: Player -> Player
opp p =
  case p of {
   White -> Black;
   Black -> White}

player_eqb :: Player -> Player -> Bool
player_eqb p1 p2 =
  case p1 of {
   White -> case p2 of {
             White -> True;
             Black -> False};
   Black -> case p2 of {
             White -> False;
             Black -> True}}

data Result =
   Win Player
 | Draw

data Game =
   Build_Game (Any -> Player) (Any -> Any -> Any) (Any -> Option Result) 
 (Any -> List Any)

type GameState = Any

type Move = Any

exec_move :: Game -> GameState -> Move -> GameState
exec_move game =
  case game of {
   Build_Game _ exec_move0 _ _ -> exec_move0}

enum_moves :: Game -> GameState -> List Move
enum_moves game =
  case game of {
   Build_Game _ _ _ enum_moves0 -> enum_moves0}

type Show x =
  x -> String
  -- singleton inductive, whose constructor was Build_Show
  
show :: (Show a1) -> a1 -> String
show show0 =
  show0

show_dec :: (Show a1) -> a1 -> a1 -> Sumbool
show_dec h x x' =
  string_dec (show h x) (show h x')

show_Prod :: (Show a1) -> (Show a2) -> Show (Prod a1 a2)
show_Prod h h1 pat =
  case pat of {
   Pair x y ->
    append (show h x)
      (append (String0 (Ascii False False True True False True False False)
        EmptyString) (show h1 y))}

type T k v = List (Prod k v)

empty :: T a1 a2
empty =
  Nil

add :: (Discrete a1) -> a1 -> a2 -> (T a1 a2) -> T a1 a2
add h k v ps =
  case ps of {
   Nil -> Cons (Pair k v) Nil;
   Cons p qs ->
    case p of {
     Pair k' v' ->
      case eq_dec0 h k k' of {
       Left -> Cons (Pair k v) qs;
       Right -> Cons (Pair k' v') (add h k v qs)}}}

lookup :: (Discrete a1) -> a1 -> (T a1 a2) -> Option a2
lookup h k ps =
  case ps of {
   Nil -> None;
   Cons p qs ->
    case p of {
     Pair k' v ->
      case eq_dec0 h k k' of {
       Left -> Some v;
       Right -> lookup h k qs}}}

size :: (T a1 a2) -> Nat
size =
  length

data StringMap m =
   Build_StringMap (() -> m) (() -> String -> Any -> m -> m) (() -> String ->
                                                             m -> Option 
                                                             Any) (() -> m ->
                                                                  Nat)

empty0 :: (StringMap a1) -> a1
empty0 stringMap =
  case stringMap of {
   Build_StringMap empty1 _ _ _ -> empty1 __}

add0 :: (StringMap a1) -> String -> a2 -> a1 -> a1
add0 stringMap x x0 x1 =
  case stringMap of {
   Build_StringMap _ add1 _ _ -> unsafeCoerce add1 __ x x0 x1}

lookup0 :: (StringMap a1) -> String -> a1 -> Option a2
lookup0 stringMap x x0 =
  case stringMap of {
   Build_StringMap _ _ lookup1 _ -> unsafeCoerce lookup1 __ x x0}

size0 :: (StringMap a1) -> a1 -> Nat
size0 stringMap x =
  case stringMap of {
   Build_StringMap _ _ _ size1 -> size1 __ x}

str_add :: (StringMap a1) -> (Show a2) -> a2 -> a3 -> a1 -> a1
str_add h h0 x =
  add0 h (show h0 x)

str_lookup :: (StringMap a1) -> (Show a2) -> a2 -> a1 -> Option a3
str_lookup h h0 x =
  lookup0 h (show h0 x)

str_adds :: (StringMap a1) -> (Show a2) -> (List (Prod a2 a3)) -> a1 -> a1
str_adds h h0 ps m =
  case ps of {
   Nil -> m;
   Cons p qs ->
    case p of {
     Pair x y -> str_adds h h0 qs (str_add h h0 x y m)}}

string_Discrete :: Discrete String
string_Discrete =
  string_dec

assocList_SM :: StringMap (T String Any)
assocList_SM =
  Build_StringMap (\_ -> empty) (\_ -> add string_Discrete) (\_ ->
    lookup string_Discrete) (\_ -> size)

loop :: (a1 -> Nat) -> (a1 -> a1) -> a1 -> a1
loop m f x =
  case eq_dec (m x) (m (f x)) of {
   Left -> x;
   Right -> let {y = f x} in loop m f y}

data FinGame =
   Build_FinGame (List GameState) (Player -> List GameState)

enum_states :: Game -> FinGame -> List GameState
enum_states _ finGame =
  case finGame of {
   Build_FinGame enum_states0 _ -> enum_states0}

enum_wins :: Game -> FinGame -> Player -> List GameState
enum_wins _ finGame =
  case finGame of {
   Build_FinGame _ enum_wins0 -> enum_wins0}

type Reversible =
  GameState -> List GameState
  -- singleton inductive, whose constructor was Build_Reversible
  
enum_preds :: Game -> Reversible -> GameState -> List GameState
enum_preds _ reversible =
  reversible

data Step =
   Eloise
 | Abelard

switch :: Step -> Step
switch s =
  case s of {
   Eloise -> Abelard;
   Abelard -> Eloise}

step_player :: Step -> Player -> Player
step_player s =
  case s of {
   Eloise -> (\pl -> pl);
   Abelard -> opp}

data TB m =
   Build_TB Nat Step m m (List GameState) (List GameState)

curr_nat :: Game -> (TB a1) -> Nat
curr_nat _ t =
  case t of {
   Build_TB curr_nat0 _ _ _ _ _ -> curr_nat0}

last_step :: Game -> (TB a1) -> Step
last_step _ t =
  case t of {
   Build_TB _ last_step0 _ _ _ _ -> last_step0}

white_positions :: Game -> (TB a1) -> a1
white_positions _ t =
  case t of {
   Build_TB _ _ white_positions0 _ _ _ -> white_positions0}

black_positions :: Game -> (TB a1) -> a1
black_positions _ t =
  case t of {
   Build_TB _ _ _ black_positions0 _ _ -> black_positions0}

last_white_positions :: Game -> (TB a1) -> List GameState
last_white_positions _ t =
  case t of {
   Build_TB _ _ _ _ last_white_positions0 _ -> last_white_positions0}

last_black_positions :: Game -> (TB a1) -> List GameState
last_black_positions _ t =
  case t of {
   Build_TB _ _ _ _ _ last_black_positions0 -> last_black_positions0}

filter_Nones :: (a1 -> Option a2) -> (List a1) -> List a1
filter_Nones f xs =
  case xs of {
   Nil -> Nil;
   Cons x xs' ->
    case f x of {
     Some _ -> filter_Nones f xs';
     None -> Cons x (filter_Nones f xs')}}

eloise_step :: (StringMap a1) -> Game -> (Show GameState) -> Reversible ->
               (TB a1) -> Player -> List GameState
eloise_step m_SM g g_string g_rev tb pl =
  let {
   prev = case pl of {
           White -> last_black_positions g tb;
           Black -> last_white_positions g tb}}
  in
  let {
   b = case pl of {
        White ->
         str_adds m_SM g_string
           (map
             (flip (\x x0 -> Pair x x0) (Pair
               (step_player (last_step g tb) White) (curr_nat g tb)))
             (last_white_positions g tb)) (white_positions g tb);
        Black ->
         str_adds m_SM g_string
           (map
             (flip (\x x0 -> Pair x x0) (Pair
               (step_player (last_step g tb) Black) (curr_nat g tb)))
             (last_black_positions g tb)) (black_positions g tb)}}
  in
  let {candidates = concat (map (enum_preds g g_rev) prev)} in
  let {
   candidates' = filter_Nones (\s -> str_lookup m_SM g_string s b) candidates}
  in
  nodup (show_dec g_string) candidates'

abelard_step :: (StringMap a1) -> Game -> (Show GameState) -> Reversible ->
                (TB a1) -> Player -> List GameState
abelard_step m_SM g g_string g_rev tb pl =
  let {
   prev = case pl of {
           White -> last_black_positions g tb;
           Black -> last_white_positions g tb}}
  in
  let {
   b = case pl of {
        White ->
         str_adds m_SM g_string
           (map
             (flip (\x x0 -> Pair x x0) (Pair
               (step_player (last_step g tb) White) (curr_nat g tb)))
             (last_white_positions g tb)) (white_positions g tb);
        Black ->
         str_adds m_SM g_string
           (map
             (flip (\x x0 -> Pair x x0) (Pair
               (step_player (last_step g tb) Black) (curr_nat g tb)))
             (last_black_positions g tb)) (black_positions g tb)}}
  in
  let {
   b' = case pl of {
         White ->
          str_adds m_SM g_string
            (map
              (flip (\x x0 -> Pair x x0) (Pair
                (step_player (last_step g tb) Black) (curr_nat g tb)))
              (last_black_positions g tb)) (black_positions g tb);
         Black ->
          str_adds m_SM g_string
            (map
              (flip (\x x0 -> Pair x x0) (Pair
                (step_player (last_step g tb) White) (curr_nat g tb)))
              (last_white_positions g tb)) (white_positions g tb)}}
  in
  let {candidates = concat (map (enum_preds g g_rev) prev)} in
  let {
   candidates' = filter_Nones (\s -> str_lookup m_SM g_string s b) candidates}
  in
  let {
   candidates'' = filter (\s ->
                    forallb (\m ->
                      case str_lookup m_SM g_string (exec_move g s m) b' of {
                       Some p ->
                        case p of {
                         Pair pl' _ -> player_eqb (opp pl) pl'};
                       None -> False}) (enum_moves g s)) candidates'}
  in
  nodup (show_dec g_string) candidates''

add_positions :: (StringMap a1) -> Game -> (Show GameState) -> a1 -> Player
                 -> Nat -> (List GameState) -> a1
add_positions m_SM _ g_string m winner n ps =
  str_adds m_SM g_string (map (flip (\x x0 -> Pair x x0) (Pair winner n)) ps)
    m

init_TB :: (StringMap a1) -> Game -> (Show GameState) -> FinGame -> TB a1
init_TB m_SM g g_string g_fin =
  Build_TB O Abelard
    (add_positions m_SM g g_string (empty0 m_SM) Black O
      (enum_wins g g_fin Black))
    (add_positions m_SM g g_string (empty0 m_SM) White O
      (enum_wins g g_fin White)) (enum_wins g g_fin Black)
    (enum_wins g g_fin White)

tB_step :: (StringMap a1) -> Game -> (Show GameState) -> Reversible -> (TB
           a1) -> TB a1
tB_step m_SM g g_string g_rev tb =
  let {
   next_white = case last_step g tb of {
                 Eloise -> abelard_step m_SM g g_string g_rev tb White;
                 Abelard -> eloise_step m_SM g g_string g_rev tb White}}
  in
  let {
   next_black = case last_step g tb of {
                 Eloise -> abelard_step m_SM g g_string g_rev tb Black;
                 Abelard -> eloise_step m_SM g g_string g_rev tb Black}}
  in
  Build_TB (S (curr_nat g tb)) (switch (last_step g tb))
  (add_positions m_SM g g_string (white_positions g tb)
    (step_player (last_step g tb) White) (S (curr_nat g tb)) next_white)
  (add_positions m_SM g g_string (black_positions g tb)
    (step_player (last_step g tb) Black) (S (curr_nat g tb)) next_black)
  next_white next_black

num_left :: (StringMap a1) -> Game -> FinGame -> (TB a1) -> Nat
num_left m_SM g g_fin tb =
  sub
    (sub (length (enum_states g g_fin)) (size0 m_SM (white_positions g tb)))
    (size0 m_SM (black_positions g tb))

final_TB :: (StringMap a1) -> Game -> (Show GameState) -> FinGame ->
            Reversible -> (GameState -> Discrete Move) -> TB a1
final_TB m_SM g g_string g_fin g_rev _ =
  loop (num_left m_SM g g_fin) (tB_step m_SM g g_string g_rev)
    (init_TB m_SM g g_string g_fin)

type TableBase m = TB m

empty_disc :: Discrete Empty_set
empty_disc =
  empty_set_rec

data Pos =
   A
 | B
 | C
 | D
 | E
 | F

type St = Prod Player Pos

show_Player :: Show Player
show_Player p =
  case p of {
   White -> String0 (Ascii True True True False True False True False)
    (String0 (Ascii False False False True False True True False) (String0
    (Ascii True False False True False True True False) (String0 (Ascii False
    False True False True True True False) (String0 (Ascii True False True
    False False True True False) EmptyString))));
   Black -> String0 (Ascii False True False False False False True False)
    (String0 (Ascii False False True True False True True False) (String0
    (Ascii True False False False False True True False) (String0 (Ascii True
    True False False False True True False) (String0 (Ascii True True False
    True False True True False) EmptyString))))}

show_Pos :: Show Pos
show_Pos p =
  case p of {
   A -> String0 (Ascii True False False False False False True False)
    EmptyString;
   B -> String0 (Ascii False True False False False False True False)
    EmptyString;
   C -> String0 (Ascii True True False False False False True False)
    EmptyString;
   D -> String0 (Ascii False False True False False False True False)
    EmptyString;
   E -> String0 (Ascii True False True False False False True False)
    EmptyString;
   F -> String0 (Ascii False True True False False False True False)
    EmptyString}

data LRS =
   LRS_L
 | LRS_R
 | LRS_S

lRS_rect :: a1 -> a1 -> a1 -> LRS -> a1
lRS_rect f f0 f1 l =
  case l of {
   LRS_L -> f;
   LRS_R -> f0;
   LRS_S -> f1}

lRS_rec :: a1 -> a1 -> a1 -> LRS -> a1
lRS_rec =
  lRS_rect

lRS_disc :: Discrete LRS
lRS_disc x x' =
  lRS_rec (\x0 -> case x0 of {
                   LRS_L -> Left;
                   _ -> Right}) (\x0 ->
    case x0 of {
     LRS_R -> Left;
     _ -> Right}) (\x0 -> case x0 of {
                           LRS_S -> Left;
                           _ -> Right}) x x'

enum_LRS :: List LRS
enum_LRS =
  Cons LRS_L (Cons LRS_R (Cons LRS_S Nil))

data LS =
   LS_L
 | LS_S

lS_rect :: a1 -> a1 -> LS -> a1
lS_rect f f0 l =
  case l of {
   LS_L -> f;
   LS_S -> f0}

lS_rec :: a1 -> a1 -> LS -> a1
lS_rec =
  lS_rect

lS_disc :: Discrete LS
lS_disc x x' =
  lS_rec (\x0 -> case x0 of {
                  LS_L -> Left;
                  LS_S -> Right}) (\x0 ->
    case x0 of {
     LS_L -> Right;
     LS_S -> Left}) x x'

enum_LS :: List LS
enum_LS =
  Cons LS_L (Cons LS_S Nil)

data RS =
   RS_R
 | RS_S

rS_rect :: a1 -> a1 -> RS -> a1
rS_rect f f0 r =
  case r of {
   RS_R -> f;
   RS_S -> f0}

rS_rec :: a1 -> a1 -> RS -> a1
rS_rec =
  rS_rect

rS_disc :: Discrete RS
rS_disc x x' =
  rS_rec (\x0 -> case x0 of {
                  RS_R -> Left;
                  RS_S -> Right}) (\x0 ->
    case x0 of {
     RS_R -> Right;
     RS_S -> Left}) x x'

enum_RS :: List RS
enum_RS =
  Cons RS_R (Cons RS_S Nil)

type Mv = Any

winning_state :: St -> Option Result
winning_state pat =
  case pat of {
   Pair pl pos ->
    case pl of {
     White -> case pos of {
               F -> Some (Win Black);
               _ -> None};
     Black -> case pos of {
               A -> Some (Win White);
               _ -> None}}}

exec :: St -> Mv -> St
exec s m =
  case s of {
   Pair p p0 ->
    case p of {
     White ->
      case p0 of {
       A ->
        case unsafeCoerce m of {
         RS_R -> Pair Black B;
         RS_S -> Pair Black A};
       B ->
        case unsafeCoerce m of {
         LRS_L -> Pair Black A;
         LRS_R -> Pair Black C;
         LRS_S -> Pair Black B};
       C ->
        case unsafeCoerce m of {
         LRS_L -> Pair Black B;
         LRS_R -> Pair Black D;
         LRS_S -> Pair Black C};
       D ->
        case unsafeCoerce m of {
         LRS_L -> Pair Black C;
         LRS_R -> Pair Black E;
         LRS_S -> Pair Black D};
       E ->
        case unsafeCoerce m of {
         RS_R -> Pair Black F;
         RS_S -> Pair Black E};
       F -> Prelude.error "absurd case"};
     Black ->
      case p0 of {
       A -> Prelude.error "absurd case";
       B ->
        case unsafeCoerce m of {
         LS_L -> Pair White A;
         LS_S -> Pair White B};
       C ->
        case unsafeCoerce m of {
         LRS_L -> Pair White B;
         LRS_R -> Pair White D;
         LRS_S -> Pair White C};
       D ->
        case unsafeCoerce m of {
         LRS_L -> Pair White C;
         LRS_R -> Pair White E;
         LRS_S -> Pair White D};
       E ->
        case unsafeCoerce m of {
         LRS_L -> Pair White D;
         LRS_R -> Pair White F;
         LRS_S -> Pair White E};
       F ->
        case unsafeCoerce m of {
         LS_L -> Pair White E;
         LS_S -> Pair White F}}}}

enum_Mv :: St -> List Mv
enum_Mv pat =
  case pat of {
   Pair pl pos ->
    case pl of {
     White ->
      case pos of {
       A -> unsafeCoerce enum_RS;
       E -> unsafeCoerce enum_RS;
       F -> Nil;
       _ -> unsafeCoerce enum_LRS};
     Black ->
      case pos of {
       A -> Nil;
       B -> unsafeCoerce enum_LS;
       F -> unsafeCoerce enum_LS;
       _ -> unsafeCoerce enum_LRS}}}

sampleGame :: Game
sampleGame =
  Build_Game (unsafeCoerce fst) (unsafeCoerce exec)
    (unsafeCoerce winning_state) (unsafeCoerce enum_Mv)

sample_fin :: FinGame
sample_fin =
  Build_FinGame (Cons (unsafeCoerce (Pair White A)) (Cons
    (unsafeCoerce (Pair White B)) (Cons (unsafeCoerce (Pair White C)) (Cons
    (unsafeCoerce (Pair White D)) (Cons (unsafeCoerce (Pair White E)) (Cons
    (unsafeCoerce (Pair White F)) (Cons (unsafeCoerce (Pair Black A)) (Cons
    (unsafeCoerce (Pair Black B)) (Cons (unsafeCoerce (Pair Black C)) (Cons
    (unsafeCoerce (Pair Black D)) (Cons (unsafeCoerce (Pair Black E)) (Cons
    (unsafeCoerce (Pair Black F)) Nil)))))))))))) (\p ->
    case p of {
     White -> Cons (unsafeCoerce (Pair Black A)) Nil;
     Black -> Cons (unsafeCoerce (Pair White F)) Nil})

sample_rev :: Reversible
sample_rev s =
  case unsafeCoerce s of {
   Pair p p0 ->
    case p of {
     White ->
      case p0 of {
       A -> Cons (unsafeCoerce (Pair Black B)) Nil;
       B -> Cons (unsafeCoerce (Pair Black B)) (Cons
        (unsafeCoerce (Pair Black C)) Nil);
       C -> Cons (unsafeCoerce (Pair Black C)) (Cons
        (unsafeCoerce (Pair Black D)) Nil);
       D -> Cons (unsafeCoerce (Pair Black C)) (Cons
        (unsafeCoerce (Pair Black D)) (Cons (unsafeCoerce (Pair Black E))
        Nil));
       E -> Cons (unsafeCoerce (Pair Black D)) (Cons
        (unsafeCoerce (Pair Black E)) (Cons (unsafeCoerce (Pair Black F))
        Nil));
       F -> Cons (unsafeCoerce (Pair Black E)) (Cons
        (unsafeCoerce (Pair Black F)) Nil)};
     Black ->
      case p0 of {
       A -> Cons (unsafeCoerce (Pair White B)) (Cons
        (unsafeCoerce (Pair White A)) Nil);
       B -> Cons (unsafeCoerce (Pair White C)) (Cons
        (unsafeCoerce (Pair White B)) (Cons (unsafeCoerce (Pair White A))
        Nil));
       C -> Cons (unsafeCoerce (Pair White D)) (Cons
        (unsafeCoerce (Pair White C)) (Cons (unsafeCoerce (Pair White B))
        Nil));
       D -> Cons (unsafeCoerce (Pair White D)) (Cons
        (unsafeCoerce (Pair White C)) Nil);
       E -> Cons (unsafeCoerce (Pair White E)) (Cons
        (unsafeCoerce (Pair White D)) Nil);
       F -> Cons (unsafeCoerce (Pair White E)) Nil}}}

move_disc :: GameState -> Discrete Move
move_disc s =
  case unsafeCoerce s of {
   Pair a b ->
    case a of {
     White ->
      case b of {
       A -> unsafeCoerce rS_disc;
       E -> unsafeCoerce rS_disc;
       F -> unsafeCoerce empty_disc;
       _ -> unsafeCoerce lRS_disc};
     Black ->
      case b of {
       A -> unsafeCoerce empty_disc;
       B -> unsafeCoerce lS_disc;
       F -> unsafeCoerce lS_disc;
       _ -> unsafeCoerce lRS_disc}}}

sampleTB :: TableBase (T String Any)
sampleTB =
  final_TB assocList_SM sampleGame
    (unsafeCoerce show_Prod show_Player show_Pos) sample_fin sample_rev
    move_disc

