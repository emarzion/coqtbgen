(* based on https://commons.wikimedia.org/wiki/File:Bear_game_05.svg *)

open Lwt.Infix
open Js_of_ocaml
open Js_of_ocaml_tyxml

open Query
open BearGame
open ExtractQuery
open Read_file
open Draw

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

  let pure_move_links (rs,rf) x =
    let moves = enum_moves RomanWheel.coq_RomanWheel x in
    let onclick m _ =
      Controller.update (ClickMove m) (rs, rf); true in
    List.concat_map (fun m ->
      let s' = coq_RW_exec_move x m in
      let st = show_RW_State s' in
      print_endline st;
      let str =
        (match query_tb st with
         | Some str -> str
         | None -> "Draw"
        ) in
      let text = print_RW_move x m ^ "==" ^ str ^ ";;" in
      [Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick (onclick m); a_class ["whitewin"]] [txt text]);
       Tyxml_js.Html.br ()
      ]
      ) moves

(*
<ul>
  <li>Item 1</li>
  <li>Item 2</li>
  <li>Item 3</li>
</ul>
*)

  let links (rs, rf) =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_move_links (rs, rf)) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

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
