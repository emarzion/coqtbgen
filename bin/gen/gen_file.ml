open Yojson.Safe

open Extracted_code
open TBGen

let print_player pl =
  match pl with
  | White -> "White"
  | Black -> "Black"

let tup_to_json tup : string * t =
  let (i, (pl, n)) = tup in
  let pl_t = `String (print_player pl) in
  let n_t = `Int n in
  let pair_t = `Tuple [pl_t; n_t] in
  (string_of_int i, pair_t)

let tups_to_json tups =
  `Assoc (List.map tup_to_json tups)

let () =
  let {tb_whites; tb_blacks} = rW_TB in
  let oc_w = open_out "tb_w.json" in
  let oc_b = open_out "tb_b.json" in
  let tups_w = M.bindings tb_whites in
  let tups_b = M.bindings tb_blacks in
  let json_tups_w = tups_to_json tups_w in
  let json_tups_b = tups_to_json tups_b in
  let () = to_channel oc_w json_tups_w in
  let () = to_channel oc_b json_tups_b in
  let () = close_out oc_w in
  let () = close_out oc_b in
  ()
