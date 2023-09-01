open Yojson.Safe

open Extracted
open Player
open OCamlTB

let json_to_tup = function
  | (str, `Tuple [`String "White"; `Int n]) -> (str, (White, n))
  | (str, `Tuple [`String "Black"; `Int n]) -> (str, (Black, n))
  | _ -> failwith "Error converting json to tuple."

let json_to_tups = function
  | `Assoc pairs -> List.rev_map json_to_tup pairs
  | _ -> failwith "Error converting json to tuples."

let make_tb =
  let inc_w = open_in "tb_w.json" in
  let inc_b = open_in "tb_b.json" in
  let js_w = from_channel inc_w in
  let js_b = from_channel inc_b in
  let tups_w = json_to_tups js_w in
  let tups_b = json_to_tups js_b in
  let m_w = List.fold_left (fun m (str, pr) -> M.insert str pr m) M.empty tups_w in
  let m_b = List.fold_left (fun m (str, pr) -> M.insert str pr m) M.empty tups_b in
  { tb_whites = m_w; tb_blacks = m_b }