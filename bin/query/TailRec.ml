
let app xs ys = List.rev_append (List.rev xs) ys

let length = List.length

let map f xs = List.rev (List.rev_map f xs)

let concat xss =
  let rec aux acc ls =
    match ls with
    | [] -> acc
    | xs :: xss' -> aux (List.rev_append xs acc) xss'
  in aux [] xss

let filter =
  List.filter

let nodup eqb xs =
  let rec aux acc l =
    match l with
    | [] -> acc
    | x :: xs' -> if List.exists (eqb x) xs' then aux acc xs' else aux (x::acc) xs'
  in aux [] xs