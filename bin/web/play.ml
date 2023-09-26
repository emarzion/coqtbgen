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
      tb_player : Player.coq_Player;
      curr_selected : Graph.coq_Vert option;
    }

  let init tb =
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
end

module Controller = struct
  open Action

  let tb_step (m : Model.t) : Model.t =
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
    | _ -> failwith "mismatch."

  let update (a : Action.t) ((rs,rf) : rp) tb =
    let Model.{ curr_state; curr_tb_strategy; tb_player; curr_selected }  = React.S.value rs in
    let t =
      match a with
      | ClickMove m ->
        let strat = Lazy.force curr_tb_strategy in (
          match strat with
          | Coq_abelard_strategy(_,strats) ->
            let s = exec_move RomanWheel.coq_RomanWheel curr_state m in
            let str' = strats (Obj.magic m) in
            let model = Model.
              { curr_state = s;
                curr_tb_strategy = str';
                tb_player = tb_player;
                curr_selected = None;
              } in tb_step model
          | _ -> failwith "mismatch."
          )
      | ClickStep ->
        let strat = Lazy.force curr_tb_strategy in (
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
              { curr_state = curr_state;
                curr_tb_strategy = lazy (Coq_atom_strategy(s,res));
                tb_player = tb_player;
                curr_selected = None;
              }
          | _ -> failwith "mismatch."
          )
      | ClickBlack -> Model.
          { curr_state = curr_state;
            curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb;
            tb_player = White;
            curr_selected = None;
          }
      | ClickWhite -> Model.
          { curr_state = curr_state;
            curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb;
            tb_player = Black;
            curr_selected = None;
          }
      | ClickPiece v ->
          match curr_selected with
          | None -> print_endline "none"; (
            match tb_player with
            | Player.White ->
              if BearGame.is_bear RomanWheel.coq_RomanWheel curr_state v
                then Model.
                  { curr_state = curr_state;
                    curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb; (*here*)
                    tb_player = tb_player;
                    curr_selected = Some v;
                  }
                else Model.
                  { curr_state = curr_state;
                    curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb; (*here*)
                    tb_player = tb_player;
                    curr_selected = None;
                  }
            | Player.Black ->
              if BearGame.is_hunter RomanWheel.coq_RomanWheel curr_state v
                then Model.
                  { curr_state = curr_state;
                    curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb; (*here*)
                    tb_player = tb_player;
                    curr_selected = Some v;
                  }
                else Model.
                  { curr_state = curr_state;
                    curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb; (*here*)
                    tb_player = tb_player;
                    curr_selected = None;
                  }
            )
          | Some v' -> print_endline "some";
            let omv = BearGame.create_Move RomanWheel.coq_RomanWheel curr_state v' v in
            match omv with
            | Some mv ->
                let strat = Lazy.force curr_tb_strategy in (
                  match strat with
                  | Coq_abelard_strategy(_,strats) ->
                    let s = exec_move RomanWheel.coq_RomanWheel curr_state mv in
                    let str' = strats (Obj.magic mv) in tb_step Model.
                      { curr_state = s;
                        curr_tb_strategy = str';
                        tb_player = tb_player;
                        curr_selected = None;
                      }
                  | _ -> failwith "mismatch."
                  )
            | None -> Model.
                { curr_state = curr_state;
                  curr_tb_strategy = rw_tb_strat tb_player (Obj.magic curr_state) tb; (*here*)
                  tb_player = tb_player;
                  curr_selected = None;
                }
    in
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
    let Model.{ curr_state; _ } = x in
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

  (*
  let pure_bear x =
    let Model.{ curr_state; _ } = x in
    let pos = coords (Obj.magic (curr_state.BearGame.bear)) in
    [Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      circle ~a:[a_onclick (fun _ -> print_endline "hi"; true); a_stroke (`Color ("black", None)); a_fill (`Color ("black", None)); a_cx (fst pos, Some `Px); (a_cy (snd pos, Some `Px)); (a_r (7.5, Some `Px))] []
    )]

  let foo = Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel

  let pure_hunters x =
    let Model.{ curr_state; _ } = x in
    let hs = List.map (fun x -> coords (Obj.magic x)) curr_state.BearGame.hunters in
    List.map (fun pos ->
      Js_of_ocaml_tyxml.Tyxml_js.Svg.(
        circle ~a:[a_stroke (`Color ("black", None)); a_fill (`Color ("white", None)); a_cx (fst pos, Some `Px); (a_cy (snd pos, Some `Px)); (a_r (7.5, Some `Px))] []
      )) hs
  *)

  let pieces tb (rs,rf) =
    let sig_pieces = ReactiveData.RList.from_signal (React.S.map (pure_pieces (rs,rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g sig_pieces]
    )

  let pure_curr_res x =
    let Model.{ curr_state; _ } = x in
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

  let curr_res (rs,_) =
    let sig_curr = ReactiveData.RList.from_signal (React.S.map pure_curr_res rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p sig_curr

  let pure_move_links (rs,rf) tb x =
    let Model.{ curr_state; curr_tb_strategy; _ } = x in
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

  let links (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_move_links (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let pure_player_toggles (rs,rf) tb x =
    let pl = Model.(x.tb_player) in
    let clickblack _ =
      Controller.update ClickBlack (rs, rf) tb;
      Controller.update ClickStep (rs, rf) tb; true in
    let clickwhite _ =
      Controller.update ClickWhite (rs, rf) tb;
      Controller.update ClickStep (rs, rf) tb; true in
    let deselected = Tyxml_js.Html.a_class ["deselected"] in
    let selected = Tyxml_js.Html.a_class ["selected"] in
    let (style_w, style_b) =
      match pl with
      | Player.White -> (deselected, selected)
      | Player.Black -> (selected, deselected) in
    let black = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickblack; style_b] [txt "black"]) in
    let white = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickwhite; style_w] [txt "white"]) in
    let space = Tyxml_js.Html.(a ~a:[] [txt " "]) in
    let normal_style = Tyxml_js.Html.a_class ["normal"] in
    let select_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Play as: "]) in
    [select_text; black; space; white]

  let player_toggles (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_player_toggles (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let board tb (rs,rf) =
    Tyxml_js.Html.svg (circ :: lines @ arcs @ [pieces tb (rs,rf)])

  let tablebase (rs,rf) tb =
    Tyxml_js.Html.(div ~a:[a_class ["tablebase"]] [player_toggles (rs, rf) tb; board tb (rs,rf); links (rs,rf) tb; curr_res (rs, rf)])

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
