(* based on https://commons.wikimedia.org/wiki/File:Bear_game_05.svg *)

open Lwt.Infix
open Js_of_ocaml
open Js_of_ocaml_tyxml

open Query
open BearGame
open ExtractQuery
open Read_file

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

module Model = struct

  type t = coq_BG_State

  let rotate x = RomanWheel.(
    match x with
    | Center -> SpokeVert(S1,L)
    | SpokeVert(s,l) -> SpokeVert(clockwise s, l)
    )

  let flip x = { x with bear = Obj.magic (rotate (Obj.magic x.bear)) }

  let init = init_RW_State

end

type rs = Model.t React.signal
type rf = ?step:React.step -> Model.t -> unit
type rp = rs * rf

module Action = struct
  type t =
    | ClickButton
    | ClickMove of coq_BG_Move
end

module Controller = struct
  open Action

  let update (a : Action.t) ((rs,rf) : rp) =
    let curr = React.S.value rs in
    let m =
      match a with
      | ClickButton -> Model.flip curr
      | ClickMove m -> exec_move RomanWheel.coq_RomanWheel curr m
    in
    rf m
end

module View = struct
  
  let circ =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      circle ~a:[a_stroke (`Color ("black", None)); a_fill `None; a_cx (100., Some `Px); (a_cy (100.0, Some `Px)); (a_r (75., Some `Px))] []
    )

  let pure_bear x =
    let pos = coords (Obj.magic (x.BearGame.bear)) in
    [Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      circle ~a:[a_stroke (`Color ("black", None)); a_fill (`Color ("black", None)); a_cx (fst pos, Some `Px); (a_cy (snd pos, Some `Px)); (a_r (5., Some `Px))] []
    )]

(*
  let bear (rs,_) =
    let foo = ReactiveData.RList.from_signal (React.S.map pure_bear rs) in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g foo]
    )
*)

  let pure_hunters x =
    let hs = List.map (fun x -> coords (Obj.magic x)) x.BearGame.hunters in
    List.map (fun pos ->
      Js_of_ocaml_tyxml.Tyxml_js.Svg.(
        circle ~a:[a_stroke (`Color ("black", None)); a_fill (`Color ("white", None)); a_cx (fst pos, Some `Px); (a_cy (snd pos, Some `Px)); (a_r (5., Some `Px))] []
      )) hs

  let pieces (rs,_) =
    let sig_bear = ReactiveData.RList.from_signal (React.S.map pure_bear rs) in
    let sig_hunters = ReactiveData.RList.from_signal (React.S.map pure_hunters rs) in
    let pieces = ReactiveData.RList.concat sig_bear sig_hunters in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g pieces]
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

  let one_more_button (rs,rf) =
    let onclick _ =
      Controller.update ClickButton (rs,rf); true in
    let curr = List.hd (ReactiveData.RList.value (ReactiveData.RList.from_signal (React.S.map (fun x -> [x]) rs))) in
    let curr_bear = curr.BearGame.bear in
    let str = RomanWheel.coq_Show_RWVert (Obj.magic curr_bear) in
    Tyxml_js.Html.(button ~a:[a_onclick onclick] [txt ("Bear: " ^ str)])

  let another_button (rs,rf) x =
    let onclick _ =
      Controller.update ClickButton (rs,rf); true in
    let curr_bear = x.BearGame.bear in
    let str = RomanWheel.coq_Show_RWVert (Obj.magic curr_bear) in
    [Tyxml_js.Html.(button ~a:[a_onclick onclick] [txt ("Bear: " ^ str)])]

  let mbutton (rs, rf) =
    let sig_button = ReactiveData.RList.from_signal (React.S.map (another_button (rs,rf)) rs) in
       [Js_of_ocaml_tyxml.Tyxml_js.R.Html.a sig_button]

(*
  let another_button2 (rs,rf) x =
    let onclick _ =
      Controller.update ClickButton (rs,rf); true in
    let curr_bear = x.BearGame.bear in
    let str = RomanWheel.coq_Show_RWVert (Obj.magic curr_bear) in
    Tyxml_js.Html.(button ~a:[a_onclick onclick] [txt ("Bear2: " ^ str)])


  let mbutton2 (rs,rf) =
    let sig_button = React.S.value (React.S.map (another_button2 (rs,rf)) rs) in
    sig_button
*)

(*
  let bear (rs,_) =
    let foo = ReactiveData.RList.from_signal (React.S.map pure_bear rs) in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g foo]
    )
*)

(*
  let pure_button (rs,rf) curr = 
    let onclick _ =
      Controller.update ClickButton (rs, rf); true in
    let foo = curr.BearGame.bear in
    let str = RomanWheel.coq_Show_RWVert (Obj.magic foo) in
    [Tyxml_js.Html.(button ~a:[a_onclick onclick] [txt ("Bear: " ^ str)])]

  let mbutton (rs, rf) =
    let sig_button = ReactiveData.RList.from_signal (React.S.map (pure_button (rs, rf)) rs) in
    ReactiveData.RList.value sig_button
*)


  let pure_move_links (rs,rf) x =
    let moves = enum_moves RomanWheel.coq_RomanWheel x in
    let onclick m _ =
      Controller.update (ClickMove m) (rs, rf); true in
    List.map (fun m ->
      let s' = coq_RW_exec_move x m in
      let st = show_RW_State s' in
      print_endline st;
      let str =
        (match query_tb st with
         | Some str -> str
         | None -> "None"
        ) in
      let text = print_RW_move x m ^ "==" ^ str ^ ";;" in
      Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick (onclick m)] [txt text])) moves

  let links (rs, rf) =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_move_links (rs, rf)) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

(*
  let pieces (rs,_) =
    let sig_bear = ReactiveData.RList.from_signal (React.S.map pure_bear rs) in
    let sig_hunters = ReactiveData.RList.from_signal (React.S.map pure_hunters rs) in
    let pieces = ReactiveData.RList.concat sig_bear sig_hunters in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g pieces]
    )
*)

  let board (rs,rf) =
    Tyxml_js.Html.svg (circ :: lines @ arcs @ [pieces (rs,rf)])

  let bar (rs,rf) =
    Tyxml_js.Html.(div ~a:[a_class ["bar"]] (one_more_button (rs,rf) :: (mbutton (rs,rf)) @ [board (rs,rf); links (rs,rf)]))


  let draw_stuff rp node =
    Dom.appendChild node (Tyxml_js.To_dom.of_node (bar rp));

end
   
let start rp node =
  View.draw_stuff rp node;
  Lwt.return ()
   
let main _ =
  let doc = Dom_html.document in
  let str =
    match query_tb "(White,Center,[Spoke3M;Spoke4L;Spoke7R])" with
    | None -> "none"
    | Some str -> str in
  print_endline str;
  let parent =
    Js.Opt.get (doc##getElementById(Js.string "beargame"))
      (fun () -> assert false)
    in
  let rp = React.S.create Model.init in
    start rp parent

let _ = Js_of_ocaml_lwt.Lwt_js_events.onload () >>= main
