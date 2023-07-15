open Extracted_code
open TBGen

let print_player pl =
  match pl with
  | White -> "White"
  | Black -> "Black"

let  print_tup oc (str, (pl, n)) =
  let () = output_string oc str in
  let () = Printf.fprintf oc ":" in
  let () = output_string oc (print_player pl ^ " ") in
  let () = Printf.fprintf oc "%d\n" n in
  ()

let () =
  let oc = open_out "tb.txt" in
  let tups = M.bindings wps @ M.bindings bps in
  let () = List.iter (print_tup oc) tups in
  let () = close_out oc in
  ()
