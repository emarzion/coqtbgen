
let rec scan_tb strk ch : string option =
  let oline = try Some (input_line ch) with End_of_file -> None in
  match oline with
  | None -> None
  | Some line ->
    match String.split_on_char ':' line with
    | [str1;str2] -> if str1 = strk then Some str2 else scan_tb strk ch
    | _ -> failwith "error."

let query_tb strk =
  let inc = open_in "tb.txt" in
  scan_tb strk inc
