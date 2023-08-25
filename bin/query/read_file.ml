open Yojson.Safe

open Extracted_code
open TBGen

let json_to_tup = function
  | (str, `Tuple [`String "White"; `Int n]) -> (str, (White, n))
  | (str, `Tuple [`String "Black"; `Int n]) -> (str, (Black, n))
  | _ -> failwith "Error converting json to tuple."

let json_to_tups = function
  | `Assoc pairs -> List.rev_map json_to_tup pairs
  | _ -> failwith "Error converting json to tuples."

let make_tb =
  let inc = open_in "tb.txt" in
  let js = from_channel inc in
  let tups = json_to_tups js in
  List.fold_left (fun m (str, pr) -> M.insert str pr m) M.empty tups
