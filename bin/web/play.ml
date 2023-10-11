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

  type play_state = 
    { curr_state : coq_BG_State;
      curr_tb_strategy : strategy;
      tb_player : Player.coq_Player;
      curr_selected : Graph.coq_Vert option;
    }

  type piece = H1 | H2 | H3 | B

  type edit_state =
    { bear : Graph.coq_Vert;
      hunter1 : Graph.coq_Vert;
      hunter2 : Graph.coq_Vert;
      hunter3 : Graph.coq_Vert;
      to_play : Player.coq_Player;
      tb_player : Player.coq_Player;
      curr_selected : piece option;
    }

  let piece_of_edit_state st v =
    if v = st.bear
    then Some B
    else if v = st.hunter1
    then Some H1
    else if v = st.hunter2
    then Some H2
    else if v = st.hunter3
    then Some H3
    else None

  let update_piece st p v =
    match p with
    | H1 -> { st with hunter1 = v; curr_selected = None }
    | H2 -> { st with hunter2 = v; curr_selected = None }
    | H3 -> { st with hunter3 = v; curr_selected = None }
    | B -> { st with bear = v; curr_selected = None }

  type t =
    | Play of play_state
    | Edit of edit_state

  let init tb = Play
    { curr_state = init_RW_State;
      curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic init_RW_State) tb;
      tb_player = Player.Black;
      curr_selected = None;
    }

end

type rs = Model.t React.signal
type rf = ?step:React.step -> Model.t -> unit
type rp = rs * rf

module Action = struct
  type t =
    | ClickMove of coq_BG_Move
    | ClickStep
    | ClickBlack
    | ClickWhite
    | ClickPiece of Graph.coq_Vert
    | ClickEdit
    | ClickPlay
end

module Controller = struct
  open Action

  let tb_step (m : Model.play_state) : Model.play_state =
    let Model.{ curr_state; curr_tb_strategy; tb_player; _ } = m in
    let strat = Lazy.force curr_tb_strategy in
    match strat with
    | Coq_eloise_strategy(_,m,str) ->
      let s = exec_move RomanWheel.coq_RomanWheel curr_state (Obj.magic m) in
      Model.
        { curr_state = s;
          curr_tb_strategy = str;
          tb_player = tb_player;
          curr_selected = None;
        }
    | Coq_atom_strategy(s,res) ->
      Model.
        { curr_state = curr_state;
          curr_tb_strategy = lazy (Coq_atom_strategy(s,res));
          tb_player = tb_player;
          curr_selected = None;
        }
    | _ -> failwith "Error: tb_step called with Abelard strategy."

  let click_move mv = function
    | Model.Play { curr_state; curr_tb_strategy; tb_player; _ } ->
      let strat = Lazy.force curr_tb_strategy in
        begin match strat with
        | Coq_abelard_strategy(_,strats) ->
          let s = exec_move RomanWheel.coq_RomanWheel curr_state mv in
          let str' = strats (Obj.magic mv) in
          let model = Model.
            { curr_state = s;
              curr_tb_strategy = str';
              tb_player = tb_player;
              curr_selected = None;
            } in Model.Play (tb_step model)
        | _ -> failwith "Error: Abelard strategy expected when clicking move."
        end
    | Model.Edit _ -> failwith "Error: click_move should not be triggerable in edit state."

  let step m =
    let strat = Lazy.force m.Model.curr_tb_strategy in
    match strat with
    | Coq_eloise_strategy(_,mv,str) ->
      let s = exec_move RomanWheel.coq_RomanWheel m.curr_state (Obj.magic mv) in
      Model.
        { curr_state = s;
          curr_tb_strategy = str;
          tb_player = m.tb_player;
          curr_selected = None;
        }
    | Coq_atom_strategy(s,res) ->
      Model.
        { curr_state = m.curr_state;
          curr_tb_strategy = lazy (Coq_atom_strategy(s,res));
          tb_player = m.tb_player;
          curr_selected = None;
        }
    | _ -> failwith "Error: Cannot step with Abelard strategy."

  let click_step = function
    | Model.Play m -> Model.Play (step m)
    | Model.Edit _ -> failwith "Error: click_step should not be triggerable in edit mode."

  let click_black tb = function
    | Model.Play { curr_state; _ } ->
      Model.Play
        { curr_state = curr_state;
          curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb;
          tb_player = White;
          curr_selected = None;
        }
    | Model.Edit { bear; hunter1; hunter2; hunter3; to_play; curr_selected; _ } ->
      Model.Edit
        { bear = bear;
          hunter1 = hunter1;
          hunter2 = hunter2;
          hunter3 = hunter3;
          to_play = to_play;
          tb_player = White;
          curr_selected = curr_selected
        }
  let click_white tb = function
    | Model.Play { curr_state; _ } ->
      Model.Play
        { curr_state = curr_state;
          curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb;
          tb_player = Black;
          curr_selected = None;
        }
    | Model.Edit { bear; hunter1; hunter2; hunter3; to_play; curr_selected; _ } ->
      Model.Edit
        { bear = bear;
          hunter1 = hunter1;
          hunter2 = hunter2;
          hunter3 = hunter3;
          to_play = to_play;
          tb_player = Black;
          curr_selected = curr_selected
        }

  let click_piece tb v = function
    | Model.Play { curr_state; curr_tb_strategy; tb_player; curr_selected } ->
      begin match curr_selected with
      | None ->
        begin match tb_player with
        | Player.White ->
          if BearGame.is_bear RomanWheel.coq_RomanWheel curr_state v
            then Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb;
                tb_player = tb_player;
                curr_selected = Some v;
              }
            else Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb;
                tb_player = tb_player;
                curr_selected = None;
              }
        | Player.Black ->
          if BearGame.is_hunter RomanWheel.coq_RomanWheel curr_state v
            then Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb;
                tb_player = tb_player;
                curr_selected = Some v;
              }
            else Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb;
                tb_player = tb_player;
                curr_selected = None;
              }
        end
      | Some v' ->
        let omv = BearGame.create_Move RomanWheel.coq_RomanWheel curr_state v' v in
        begin match omv with
        | Some mv ->
          let strat = Lazy.force curr_tb_strategy in
            begin match strat with
            | Coq_abelard_strategy(_,strats) ->
              let s = exec_move RomanWheel.coq_RomanWheel curr_state mv in
              let str' = strats (Obj.magic mv) in Model.Play (tb_step (
                { curr_state = s;
                  curr_tb_strategy = str';
                  tb_player = tb_player;
                  curr_selected = None;
                }))
            | _ -> failwith "Error: Abelard strategy expected when clicking piece."
            end
        | None -> Model.Play
            { curr_state = curr_state;
              curr_tb_strategy = rw_tb_strat tb_player (Obj.magic curr_state) tb;
              tb_player = tb_player;
              curr_selected = None;
            }
        end
      end
    | Model.Edit st ->
      begin match st.curr_selected with
      | None ->
        begin match Model.piece_of_edit_state st v with
        | Some p -> Model.Edit
          { st with curr_selected = Some p }
        | _ -> Model.Edit
          { st with curr_selected = None }
        end
      | Some p ->
        begin match Model.piece_of_edit_state st v with
        | None -> Model.Edit (Model.update_piece st p v)
        | _ -> Model.Edit
          { st with curr_selected = None }
        end
      end

  let click_edit = function
    | Model.Play st ->
      let (h1,h2,h3) =
        begin match st.curr_state.hunters with
        | [h1;h2;h3] -> (h1,h2,h3)
        | _ -> failwith "Error: there should be exactly three hunters."
        end in
      Model.Edit {
        bear = st.curr_state.bear;
        hunter1 = h1;
        hunter2 = h2;
        hunter3 = h3;
        to_play = st.curr_state.to_play;
        tb_player = st.tb_player;
        curr_selected = None;
      }
    | Model.Edit st -> Model.Edit st

  let click_play tb = function
    | Model.Play st -> Model.Play st
    | Model.Edit st ->
      begin match make_RW_State st.to_play (Obj.magic st.bear) (Obj.magic st.hunter1) (Obj.magic st.hunter2) (Obj.magic st.hunter3) with
      | Some s ->
        let m = Model.
        { curr_state = s;
          curr_tb_strategy = rw_tb_strat st.tb_player (Obj.magic s) tb;
          tb_player = st.tb_player;
          curr_selected = None;
        } in
        Model.Play (if st.tb_player = s.to_play then step m else m)
      | None -> failwith "Error: failed to construct state."
      end

  let update_func tb = function
    | ClickMove m -> click_move m
    | ClickStep -> click_step
    | ClickBlack -> click_black tb
    | ClickWhite -> click_white tb
    | ClickPiece v -> click_piece tb v
    | ClickEdit -> click_edit
    | ClickPlay -> click_play tb

  let update (a : Action.t) ((rs,rf) : rp) tb =
    let m = React.S.value rs in
    let t = update_func tb a m in
      rf t

end

module View = struct
  
  let circ =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      circle ~a:[a_stroke (`Color ("black", None)); a_fill `None; a_cx (100., Some `Px); (a_cy (100.0, Some `Px)); (a_r (75., Some `Px))] []
    )

  let black_style =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("black", None)); a_fill (`Color ("black", None)) ]

  let white_style =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("black", None)); a_fill (`Color ("white", None)) ]

  let transparent_style =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("transparent", None)); a_fill (`Color ("transparent", None)) ]

  let pos_style (x,y)  =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.[ a_cx (x, Some `Px); a_cy (y, Some `Px) ]

  let pure_pieces (rs,rf) tb x =
    match x with
    | Model.Play { curr_state; _ } ->
      List.map (fun v ->
        let pos = coords (Obj.magic v) in
        let click_piece _ = Controller.update (ClickPiece v) (rs, rf) tb; true in
        let (click, circ_style) =
          if v = curr_state.BearGame.bear
            then (click_piece,black_style) else 
            if List.mem v (curr_state.BearGame.hunters)
              then (click_piece,white_style)
              else (click_piece,transparent_style) in
        Js_of_ocaml_tyxml.Tyxml_js.Svg.(
          circle ~a:(a_onclick click :: circ_style @ pos_style pos) [])
        ) (Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel)
    | Model.Edit { bear; hunter1; hunter2; hunter3; _ } ->
      List.map (fun v ->
        let pos = coords (Obj.magic v) in
        let click_piece _ = Controller.update (ClickPiece v) (rs, rf) tb; true in
        let (click, circ_style) =
          if v = bear
            then (click_piece,black_style) else 
            if List.mem v [hunter1; hunter2; hunter3]
              then (click_piece,white_style)
              else (click_piece,transparent_style) in
        Js_of_ocaml_tyxml.Tyxml_js.Svg.(
          circle ~a:(a_onclick click :: circ_style @ pos_style pos) [])
        ) (Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel)

  let pieces tb (rs,rf) =
    let sig_pieces = ReactiveData.RList.from_signal (React.S.map (pure_pieces (rs,rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g sig_pieces]
    )

  let pure_curr_res x =
    match x with
    | Model.Play { curr_state; _ } -> (
      let text = (
        match BearGame.atomic_res RomanWheel.coq_RomanWheel curr_state with
        | Some res -> (
          match res with
          | Game.Win pl -> Player.show_player pl ^ " wins!"
          | Game.Draw -> "Drawn."
          )
        | None -> " "
        ) in
      [Tyxml_js.Html.(a ~a:[a_class ["currtext"]] [txt text])]
      )
    | Model.Edit _ -> []

  let curr_res (rs,_) =
    let sig_curr = ReactiveData.RList.from_signal (React.S.map pure_curr_res rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p sig_curr

  let pure_move_links (rs,rf) tb x =
    match x with
    | Model.Play { curr_state; curr_tb_strategy; _ } -> (
      let moves = enum_moves RomanWheel.coq_RomanWheel curr_state in
      let clickmove m _ =
        Controller.update (ClickMove m) (rs, rf) tb; true in
      let clickstep _ =
        Controller.update ClickStep (rs, rf) tb; true in
      let strat = Lazy.force curr_tb_strategy in
      match strat with
      | Coq_eloise_strategy(_,_,_) -> [Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickstep; a_class ["whitewin"]] [txt "step"])]
      | _ ->
        List.concat_map (fun m ->
          let text = print_RW_move curr_state m in
          [Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick (clickmove m); a_class ["whitewin"]] [txt text]);
          Tyxml_js.Html.br ()
          ]
          ) moves
      )
    | Model.Edit _ -> []

  let links (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_move_links (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let normal_style = Tyxml_js.Html.a_class ["normal"]
  let deselected = Tyxml_js.Html.a_class ["deselected"]
  let selected = Tyxml_js.Html.a_class ["selected"]

  let space () = Tyxml_js.Html.(a ~a:[] [txt " "])

  let pure_mode_toggles (rs,rf) tb x =
    let (style_e, style_p) =
      begin match x with
      | Model.Play _ -> (deselected, selected)
      | Model.Edit _ -> (selected, deselected)
      end in
    let clickedit _ =
      Controller.update ClickEdit (rs, rf) tb; true in
    let clickplay _ =
      Controller.update ClickPlay (rs, rf) tb; true in
    let edit = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickedit; style_e] [txt "Edit"]) in
    let play = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickplay; style_p] [txt "Play"]) in
    let mode_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Mode: "]) in
    [mode_text; space (); edit; space (); play]

  let mode_toggles (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_mode_toggles (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let pure_player_toggles (rs,rf) tb x =
    match x with
    | Model.Play x ->
      let pl = Model.(x.tb_player) in
      let clickblack _ =
        Controller.update ClickBlack (rs, rf) tb;
        Controller.update ClickStep (rs, rf) tb; true in
      let clickwhite _ =
        Controller.update ClickWhite (rs, rf) tb;
        Controller.update ClickStep (rs, rf) tb; true in
      let (style_w, style_b) =
        match pl with
        | Player.White -> (deselected, selected)
        | Player.Black -> (selected, deselected) in
      let black = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickblack; style_b] [txt "black"]) in
      let white = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickwhite; style_w] [txt "white"]) in
      let select_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Play as: "]) in
      [select_text; black; space (); white]
    | Model.Edit x ->
      let pl = Model.(x.tb_player) in
      let clickblack _ =
        Controller.update ClickBlack (rs, rf) tb; true in
      let clickwhite _ =
        Controller.update ClickWhite (rs, rf) tb; true in
      let (style_w, style_b) =
        match pl with
        | Player.White -> (deselected, selected)
        | Player.Black -> (selected, deselected) in
      let black = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickblack; style_b] [txt "black"]) in
      let white = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickwhite; style_w] [txt "white"]) in
      let select_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Play as: "]) in
      [select_text; black; space (); white]

  let player_toggles (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_player_toggles (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let board tb (rs,rf) =
    Tyxml_js.Html.svg (circ :: lines @ arcs @ [pieces tb (rs,rf)])

  let tablebase (rs,rf) tb =
    Tyxml_js.Html.(div ~a:[a_class ["tablebase"]] [
      mode_toggles (rs, rf) tb;
      player_toggles (rs, rf) tb;
      board tb (rs,rf);
      links (rs,rf) tb;
      curr_res (rs, rf)
    ])

  let draw_stuff tb rp node =
    Dom.appendChild node (Tyxml_js.To_dom.of_node (tablebase rp tb));

end

let start tb rp node =
  View.draw_stuff tb rp node;
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
