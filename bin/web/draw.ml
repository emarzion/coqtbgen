(*
open Lwt.Infix
open Js_of_ocaml
open Js_of_ocaml_tyxml
*)
open Query
(*
open BearGame
open ExtractQuery
open Read_file
*)

let coords x = RomanWheel.(
  match x with
  | Center -> (100.0, 100.0)

  | SpokeVert(S1, Mid) -> (100.0, 45.0)
  | SpokeVert(S2, Mid) -> (138.88, 61.109)
  | SpokeVert(S3, Mid) -> (155.0, 100.0)
  | SpokeVert(S4, Mid) -> (138.89, 138.89)
  | SpokeVert(S5, Mid) -> (100.0, 155.0)
  | SpokeVert(S6, Mid) -> (61.109, 138.88)
  | SpokeVert(S7, Mid) -> (45.0, 100.0)
  | SpokeVert(S8, Mid) -> (61.109, 61.109)

  | SpokeVert(S1,L) -> (80.213, 27.742)
  | SpokeVert(S2,L) -> (137.09, 34.922)
  | SpokeVert(S3,L) -> (172.258, 80.213)
  | SpokeVert(S4,L) -> (165.078, 137.09)
  | SpokeVert(S5,L) -> (119.787, 172.258)
  | SpokeVert(S6,L) -> (62.91, 165.078)
  | SpokeVert(S7,L) -> (27.742, 119.787)
  | SpokeVert(S8,L) -> (34.922, 62.91)

  | SpokeVert(S1,R) -> (119.787, 27.742)
  | SpokeVert(S2,R) -> (165.078, 62.91)
  | SpokeVert(S3,R) -> (172.258, 119.787)
  | SpokeVert(S4,R) -> (137.09, 165.078)
  | SpokeVert(S5,R) -> (80.213, 172.258)
  | SpokeVert(S6,R) -> (34.922, 137.09)
  | SpokeVert(S7,R) -> (27.742, 80.213)
  | SpokeVert(S8,R) -> (62.91, 34.922)
  )

  let arcs = List.map (fun p ->
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      path ~a:[a_stroke_width (1., Some `Px); a_fill `None;
      a_stroke (`Color ("black", None)); a_d p] []
    ))
    [ "m46.967 133.03a20 20 0 0 0-12.045 4.0566 75 75 0 0 0 27.959 28.016 20 20 0 0 0 4.0859-12.072 20 20 0 0 0-20-20z"
    ; "m100 155a20 20 0 0 0-19.787 17.258 75 75 0 0 0 19.787 2.7422 75 75 0 0 0 19.797-2.6719 20 20 0 0 0-19.797-17.328z"
    ; "m153.03 133.03a20 20 0 0 0-20 20 20 20 0 0 0 4.0586 12.047 75 75 0 0 0 28.014-27.961 20 20 0 0 0-12.072-4.0859z"
    ; "m172.33 80.203a20 20 0 0 0-17.328 19.797 20 20 0 0 0 17.258 19.787 75 75 0 0 0 2.7422-19.787 75 75 0 0 0-2.6719-19.797z"
    ; "m137.12 34.895a20 20 0 0 0-4.0859 12.072 20 20 0 0 0 20 20 20 20 0 0 0 12.045-4.0566 75 75 0 0 0-27.959-28.016z"
    ; "m100 25a75 75 0 0 0-19.797 2.6719 20 20 0 0 0 19.797 17.328 20 20 0 0 0 19.787-17.258 75 75 0 0 0-19.787-2.7422z"
    ; "m62.91 34.922a75 75 0 0 0-28.016 27.959 20 20 0 0 0 12.072 4.0859 20 20 0 0 0 20-20 20 20 0 0 0-4.0566-11.845z"
    ; "m27.742 80.213a75 75 0 0 0-2.7422 19.787 75 75 0 0 0 2.6719 19.797 20 20 0 0 0 17.328-19.797 20 20 0 0 0-17.258-19.787z"
    ]

  let lines = List.map (fun p ->
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      path ~a:[a_stroke_width (1., Some `Px); a_fill `None;
      a_stroke (`Color ("black", None)); a_d p] []
    ))
    [ "m45 100h110"
    ; "m61.109 138.88 77.782-77.782"
    ; "m100 155-2.1e-5 -110"
    ; "m138.89 138.89-77.782-77.782"
    ]
