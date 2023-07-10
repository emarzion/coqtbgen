(*
let print_player pl =
  match pl with
  | RW.White -> "White"
  | RW.Black -> "Black"

let print_tup oc (str, (pl, n)) =
  let () = output_string oc str in
  let () = Printf.fprintf oc ": " in
  let () = output_string oc (print_player pl ^ " ") in
  let () = Printf.fprintf oc "%d\n" n in
  ()
*)

let rec scan_tb strk ch : string option =
  let line = try input_line ch with End_of_file -> "none" in
  match String.split_on_char ':' line with
  | [str1;str2] -> if str1 = strk then Some str2 else scan_tb strk ch
  | _ -> Some "error."

let () =
  let inc = open_in "filename.txt" in
  match scan_tb "(Black,Spoke8R,[Spoke6R;Spoke7M;Spoke8L])" inc with
  | None -> print_string "not found."
  | Some str -> print_string str


(*
let () =
  let oc = open_out "filename.txt" in
  let tups = M.bindings RW.wps @ M.bindings RW.bps in
  let () = List.iter (print_tup oc) tups in
  let () = close_out oc in
  ()
  *)