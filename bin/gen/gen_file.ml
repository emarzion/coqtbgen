open Yojson.Safe

open Extracted_code
open TBGen

let print_player pl =
  match pl with
  | White -> "White"
  | Black -> "Black"

let tup_to_json tup : string * t =
  let (str, (pl, n)) = tup in
  let pl_t = `String (print_player pl) in
  let n_t = `Int n in
  let pair_t = `Tuple [pl_t; n_t] in
  (str, pair_t)

let tups_to_json tups =
  `Assoc (List.map tup_to_json tups)

let () =
  let oc = open_out "tb.txt" in
  let tups = M.bindings wps @ M.bindings bps in
  let json_tups = tups_to_json tups in
  let () = to_channel oc json_tups in
  ()
