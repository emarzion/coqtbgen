open Lwt.Infix
open Js_of_ocaml
open Js_of_ocaml_tyxml

open Query
open BearGame
open ExtractQuery
open Read_file
open Draw
open Strategy

module Model = struct

  type t = 
    { curr_state : coq_BG_State;
      curr_tb_strategy : strategy;
    }

  let init tb =
    { curr_state = init_RW_State;
      curr_tb_strategy = rw_tb_strat Player.White (Obj.magic init_RW_State) tb;
    }

end

type rs = Model.t React.signal
type rf = ?step:React.step -> Model.t -> unit
type rp = rs * rf

module Action = struct
  type t =
    | ClickMove of coq_BG_Move
    | ClickStep
end

module Controller = struct
  open Action

  let update (a : Action.t) ((rs,rf) : rp) =
    let Model.{ curr_state; curr_tb_strategy }  = React.S.value rs in
    let t =
      match a with
      | ClickMove m ->
        let strat = Lazy.force curr_tb_strategy in (
          match strat with
          | Coq_abelard_strategy(_,strats) ->
            let s = exec_move RomanWheel.coq_RomanWheel curr_state m in
            let str' = strats (Obj.magic m) in Model.{ curr_state = s; curr_tb_strategy = str' }
          | _ -> failwith "mismatch."
          )
      | ClickStep ->
        let strat = Lazy.force curr_tb_strategy in (
          match strat with
          | Coq_eloise_strategy(_,m,str) ->
            let s = exec_move RomanWheel.coq_RomanWheel curr_state (Obj.magic m) in
            Model.{ curr_state = s; curr_tb_strategy = str }
          | _ -> failwith "mismatch."
        )
    in
    rf t
end

module View = struct
  
  let circ =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      circle ~a:[a_stroke (`Color ("black", None)); a_fill `None; a_cx (100., Some `Px); (a_cy (100.0, Some `Px)); (a_r (75., Some `Px))] []
    )

  let pure_bear x =
    let Model.{ curr_state; _ } = x in
    let pos = coords (Obj.magic (curr_state.BearGame.bear)) in
    [Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      circle ~a:[a_stroke (`Color ("black", None)); a_fill (`Color ("black", None)); a_cx (fst pos, Some `Px); (a_cy (snd pos, Some `Px)); (a_r (7.5, Some `Px))] []
    )]

  let pure_hunters x =
    let Model.{ curr_state; _ } = x in
    let hs = List.map (fun x -> coords (Obj.magic x)) curr_state.BearGame.hunters in
    List.map (fun pos ->
      Js_of_ocaml_tyxml.Tyxml_js.Svg.(
        circle ~a:[a_stroke (`Color ("black", None)); a_fill (`Color ("white", None)); a_cx (fst pos, Some `Px); (a_cy (snd pos, Some `Px)); (a_r (7.5, Some `Px))] []
      )) hs

  let pieces (rs,_) =
    let sig_bear = ReactiveData.RList.from_signal (React.S.map pure_bear rs) in
    let sig_hunters = ReactiveData.RList.from_signal (React.S.map pure_hunters rs) in
    let pieces = ReactiveData.RList.concat sig_bear sig_hunters in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g pieces]
    )

  let pure_curr_res mp x =
    let Model.{ curr_state; _ } = x in
    let text = (
      match ExtractQuery.query_RW_TB mp curr_state with
      | Some (pl, n) -> (
        match pl with
        | Player.White -> "White wins in " ^ string_of_int n
        | Player.Black -> "Black wins in " ^ string_of_int n
        )
      | None -> "Drawn"
      ) in
    [Tyxml_js.Html.(a ~a:[a_class ["currtext"]] [txt text])]

  let curr_res mp (rs,_) =
    let sig_curr = ReactiveData.RList.from_signal (React.S.map (pure_curr_res mp) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p sig_curr

  let pure_move_links (rs,rf) x =
    let Model.{ curr_state; curr_tb_strategy } = x in
    let moves = enum_moves RomanWheel.coq_RomanWheel curr_state in
    let clickmove m _ =
      Controller.update (ClickMove m) (rs, rf); true in
    let clickstep _ =
      Controller.update ClickStep (rs, rf); true in
    let strat = Lazy.force curr_tb_strategy in
    match strat with
    | Coq_eloise_strategy(_,_,_) -> [Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickstep; a_class ["whitewin"]; a_style "text-decoration: none"] [txt "step"])]
    | _ ->
      List.concat_map (fun m ->
        let text = print_RW_move curr_state m in
        [Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick (clickmove m); a_class ["whitewin"]; a_style "text-decoration: none"] [txt text]);
        Tyxml_js.Html.br ()
        ]
        ) moves

  let links (rs, rf) =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_move_links (rs, rf)) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let board (rs,rf) =
    Tyxml_js.Html.svg (circ :: lines @ arcs @ [pieces (rs,rf)])

  let tablebase mp (rs,rf) =
    Tyxml_js.Html.(div ~a:[a_class ["tablebase"]] [curr_res mp (rs, rf); board (rs,rf); links (rs,rf)])

  let draw_stuff mp rp node =
    Dom.appendChild node (Tyxml_js.To_dom.of_node (tablebase mp rp));

end
   
let start mp rp node =
  View.draw_stuff mp rp node;
  Lwt.return ()
   
let main mp _ =
  let doc = Dom_html.document in
  let parent =
    Js.Opt.get (doc##getElementById(Js.string "beargame"))
      (fun () -> assert false)
    in
  let rp = React.S.create (Model.init mp) in
    start mp rp parent

let _ =
  let mp = make_tb in
  Js_of_ocaml_lwt.Lwt_js_events.onload () >>= (main (Obj.magic mp))
