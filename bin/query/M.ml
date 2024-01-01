
module SM = Map.Make(Uint63)

type 'a t = 'a SM.t

let empty = SM.empty
let insert = SM.add
let lookup = SM.find_opt
let size = SM.cardinal
let bindings = SM.bindings
(* 
let printMap m =
  SM.iter (fun key value -> Printf.printf "%s -> %d\n" key value) m
 *)

(* let tr_concat xss =
  let rec aux acc ls =
    match ls with
    | [] -> acc
    | xs :: xss' -> aux (List.rev_append xs acc) xss'
  in aux [] xss
 *)