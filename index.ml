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

  type pre_play_state =
    { curr_state : coq_BG_State;
    }

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
      curr_selected : piece option;
    }

  type query_state = 
    { curr_state : coq_BG_State;
      curr_selected : Graph.coq_Vert option;
    }

  let piece_of_vertex st v =
    if v = st.bear
    then Some B
    else if v = st.hunter1
    then Some H1
    else if v = st.hunter2
    then Some H2
    else if v = st.hunter3
    then Some H3
    else None

  let vertex_of_piece st = function
    | H1 -> st.hunter1
    | H2 -> st.hunter2
    | H3 -> st.hunter3
    | B -> st.bear

  let update_piece st p v =
    match p with
    | H1 -> { st with hunter1 = v; curr_selected = None }
    | H2 -> { st with hunter2 = v; curr_selected = None }
    | H3 -> { st with hunter3 = v; curr_selected = None }
    | B -> { st with bear = v; curr_selected = None }

  type t =
    | PrePlay of pre_play_state
    | Play of play_state
    | Edit of edit_state
    | Query of query_state

  let init = Edit RomanWheel.
    { bear = Obj.magic Center;
      hunter1 = Obj.magic (SpokeVert(S1,L));
      hunter2 = Obj.magic (SpokeVert(S1,Mid));
      hunter3 = Obj.magic (SpokeVert(S1,R));
      to_play = Obj.magic Player.White;
      curr_selected = None;
    }

end

type rs = Model.t React.signal
type rf = ?step:React.step -> Model.t -> unit
type rp = rs * rf

module Action = struct
  type t =
    | ClickMove of coq_BG_Move
    | ClickPlayAsBlack
    | ClickPlayAsWhite
    | ClickToPlayBlack
    | ClickToPlayWhite
    | ClickPiece of Graph.coq_Vert
    | ClickEdit
    | ClickPlay
    | ClickQuery 
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
    | Model.Query { curr_state; _ } ->
      let s = exec_move RomanWheel.coq_RomanWheel curr_state mv in
      Model.Query
        { curr_state = s;
          curr_selected = None;
        }
    | _ -> failwith "Error: click_move only triggerable in query mode."

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
          curr_selected = curr_selected
        }
    | Model.Query _ -> failwith "Error: click_black should not be triggerable in query mode."
    | Model.PrePlay { curr_state } ->
      let m =
        Model.{
          curr_state = curr_state;
          curr_tb_strategy = rw_tb_strat Player.White (Obj.magic curr_state) tb;
          tb_player = White;
          curr_selected = None
        } in
      Model.Play (if curr_state.to_play = White then step m else m)

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
          curr_selected = curr_selected
        }
    | Model.Query _ -> failwith "Error: click_white should not be triggerable in query mode."
    | Model.PrePlay { curr_state } ->
      let m =
        Model.{
          curr_state = curr_state;
          curr_tb_strategy = rw_tb_strat Player.Black (Obj.magic curr_state) tb;
          tb_player = Black;
          curr_selected = None
        } in
      Model.Play (if curr_state.to_play = Black then step m else m)

  (* a fake update to satisfy the react signal stuff *)
  let strat_id strat =
    let str = Lazy.force strat in
    match str with
    | Coq_eloise_strategy(s,m,str) -> lazy (Coq_eloise_strategy(s,m,str))
    | Coq_abelard_strategy(s,strs) -> lazy (Coq_abelard_strategy(s,strs))
    | Coq_atom_strategy(s,r) -> lazy (Coq_atom_strategy(s,r))

  let click_piece v = function
    | Model.Play { curr_state; curr_tb_strategy; tb_player; curr_selected } ->
      begin match curr_selected with
      | None ->
        begin match tb_player with
        | Player.White ->
          if BearGame.is_bear RomanWheel.coq_RomanWheel curr_state v
            then Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = strat_id curr_tb_strategy;
                tb_player = tb_player;
                curr_selected = Some v;
              }
            else Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = strat_id curr_tb_strategy;
                tb_player = tb_player;
                curr_selected = None;
              }
        | Player.Black ->
          if BearGame.is_hunter RomanWheel.coq_RomanWheel curr_state v
            then Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = strat_id curr_tb_strategy;
                tb_player = tb_player;
                curr_selected = Some v;
              }
            else Model.Play
              { curr_state = curr_state;
                curr_tb_strategy = strat_id curr_tb_strategy;
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
              curr_tb_strategy = strat_id curr_tb_strategy;
              tb_player = tb_player;
              curr_selected = None;
            }
        end
      end
    | Model.Edit st ->
      begin match st.curr_selected with
      | None ->
        begin match Model.piece_of_vertex st v with
        | Some p -> Model.Edit
          { st with curr_selected = Some p }
        | _ -> Model.Edit
          { st with curr_selected = None }
        end
      | Some p ->
        begin match Model.piece_of_vertex st v with
        | None -> Model.Edit (Model.update_piece st p v)
        | _ -> Model.Edit
          { st with curr_selected = None }
        end
      end
    | Model.Query { curr_state; curr_selected } ->
      begin match curr_selected with
      | None ->
        begin match curr_state.to_play with
        | Player.White ->
          if List.mem v curr_state.hunters
          then Model.Query
            { curr_state = curr_state;
              curr_selected = Some v;
            }
          else Model.Query
            { curr_state = curr_state;
              curr_selected = None;
            }
        | Player.Black ->
          if v = curr_state.bear
          then Model.Query
            { curr_state = curr_state;
              curr_selected = Some v;
            }
          else Model.Query
            { curr_state = curr_state;
              curr_selected = None;
            }
        end
      | Some v' ->
        let omv = BearGame.create_Move RomanWheel.coq_RomanWheel curr_state v' v in
        begin match omv with
        | Some mv ->
          let s = exec_move RomanWheel.coq_RomanWheel curr_state mv in
          Model.Query
          { curr_state = s;
            curr_selected = None;
          }
        | None -> Model.Query
          { curr_state = curr_state;
            curr_selected = None;
          }
        end
      end
  | Model.PrePlay st -> Model.PrePlay st

  let click_edit = function
    | Model.PrePlay st ->
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
        curr_selected = None;
      }
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
        curr_selected = None;
      }
    | Model.Edit st -> Model.Edit st
    | Model.Query st ->
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
        curr_selected = None;
      }

  let click_play _tb = function
    | Model.Play st -> Model.PrePlay
      { curr_state = st.curr_state
      }
    | Model.Edit st ->
      begin match make_RW_State st.to_play (Obj.magic st.bear) (Obj.magic st.hunter1) (Obj.magic st.hunter2) (Obj.magic st.hunter3) with
      | Some s ->
        Model.PrePlay
        { curr_state = s;
        }
      | None -> failwith "Error: failed to construct state."
      end
    | Model.Query st -> Model.PrePlay
      { curr_state = st.curr_state
      }
    | Model.PrePlay st -> Model.PrePlay st

  let click_query = function
    | Model.PrePlay st -> Model.Query
      { curr_state = st.curr_state;
        curr_selected = None      
      }
    | Model.Play st -> Model.Query
      { curr_state = st.curr_state;
        curr_selected = None
      }
    | Model.Edit st ->
      begin match make_RW_State st.to_play (Obj.magic st.bear) (Obj.magic st.hunter1) (Obj.magic st.hunter2) (Obj.magic st.hunter3) with
      | Some s ->
        Model.Query
        { curr_state = s;
          curr_selected = None;
        }
      | None -> failwith "Error: failed to construct state."
      end
    | Model.Query st -> Model.Query st

  let click_to_play_black = function
    | Model.Edit st -> Model.Edit { st with to_play = Player.Black }
    | _ -> failwith "Error: click_to_play_black should not be triggerable outside of Edit mode."

  let click_to_play_white = function
    | Model.Edit st -> Model.Edit { st with to_play = Player.White }
    | _ -> failwith "Error: click_to_play_white should not be triggerable outside of Edit mode."

  let update_func tb = function
    | ClickMove m -> click_move m
    | ClickPlayAsBlack -> click_black tb
    | ClickPlayAsWhite -> click_white tb
    | ClickPiece v -> click_piece v
    | ClickEdit -> click_edit
    | ClickPlay -> click_play tb
    | ClickQuery -> click_query
    | ClickToPlayBlack -> click_to_play_black
    | ClickToPlayWhite -> click_to_play_white

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

  let black_style is_selected =
    if is_selected
    then Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("gray", None)); a_stroke_width (4.,None); a_fill (`Color ("black", None)) ]
    else Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("black", None)); a_fill (`Color ("black", None)) ]

  let white_style is_selected =
    if is_selected
    then Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("gray", None)); a_stroke_width (4.,None); a_fill (`Color ("white", None)) ]
    else Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("black", None)) ; a_fill (`Color ("white", None)) ]

  let transparent_style =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.[a_r (7.5, Some `Px); a_stroke (`Color ("transparent", None)); a_fill (`Color ("transparent", None)) ]

  let pos_style (x,y)  =
    Js_of_ocaml_tyxml.Tyxml_js.Svg.[ a_cx (x, Some `Px); a_cy (y, Some `Px) ]

  let pure_pieces (rs,rf) tb x =
    match x with
    | Model.Play { curr_state; curr_selected; _ } ->
      List.map (fun v ->
        let pos = coords (Obj.magic v) in
        let is_selected = Some v = curr_selected in
        let click_piece _ = Controller.update (ClickPiece v) (rs, rf) tb; true in
        let (click, circ_style) =
          if v = curr_state.BearGame.bear
            then (click_piece,black_style is_selected) else 
            if List.mem v (curr_state.BearGame.hunters)
              then (click_piece,white_style is_selected)
              else (click_piece,transparent_style) in
        Js_of_ocaml_tyxml.Tyxml_js.Svg.(
          circle ~a:(a_onclick click :: circ_style @ pos_style pos) [])
        ) (Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel)
    | Model.Edit st ->
      List.map (fun v ->
        let pos = coords (Obj.magic v) in
        let is_selected = Some v = Option.map (Model.vertex_of_piece st) st.curr_selected in
        let click_piece _ = Controller.update (ClickPiece v) (rs, rf) tb; true in
        let (click, circ_style) =
          if v = st.bear
            then (click_piece,black_style is_selected) else 
            if List.mem v [st.hunter1; st.hunter2; st.hunter3]
              then (click_piece,white_style is_selected)
              else (click_piece,transparent_style) in
        Js_of_ocaml_tyxml.Tyxml_js.Svg.(
          circle ~a:(a_onclick click :: circ_style @ pos_style pos) [])
        ) (Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel)
    | Model.Query { curr_state; curr_selected } ->
      List.map (fun v ->
        let pos = coords (Obj.magic v) in
        let is_selected = Some v = curr_selected in
        let click_piece _ = Controller.update (ClickPiece v) (rs, rf) tb; true in
        let (click, circ_style) =
          if v = curr_state.BearGame.bear
            then (click_piece,black_style is_selected) else 
            if List.mem v (curr_state.BearGame.hunters)
              then (click_piece,white_style is_selected)
              else (click_piece,transparent_style) in
        Js_of_ocaml_tyxml.Tyxml_js.Svg.(
          circle ~a:(a_onclick click :: circ_style @ pos_style pos) [])
        ) (Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel)
    | Model.PrePlay { curr_state } ->
      List.map (fun v ->
        let pos = coords (Obj.magic v) in
        let circ_style =
          if v = curr_state.BearGame.bear
            then black_style false else 
            if List.mem v (curr_state.BearGame.hunters)
              then white_style false
              else transparent_style in
        Js_of_ocaml_tyxml.Tyxml_js.Svg.(
          circle ~a:(circ_style @ pos_style pos) [])
        ) (Graph.coq_Graph_Vert_enum RomanWheel.coq_RomanWheel)

  let pieces tb (rs,rf) =
    let sig_pieces = ReactiveData.RList.from_signal (React.S.map (pure_pieces (rs,rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.Svg.(
      svg [Js_of_ocaml_tyxml.Tyxml_js.R.Svg.g sig_pieces]
    )

  let pure_curr_res tb x =
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
    | Model.Query s ->
      let text = (
        match ExtractQuery.query_RW_TB tb s.curr_state with
        | Some (pl, n) -> (
          match pl with
          | Player.White -> "White wins in " ^ string_of_int n
          | Player.Black -> "Black wins in " ^ string_of_int n
          )
        | None -> "Drawn"
        ) in
      [Tyxml_js.Html.(a ~a:[a_class ["currtext"]] [txt text])]
    | _ -> []

  let curr_res tb (rs,_) =
    let sig_curr = ReactiveData.RList.from_signal (React.S.map (pure_curr_res tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p sig_curr

  let pure_move_links (rs,rf) tb x =
    match x with
    | Model.Query { curr_state; _ } ->
      let moves = enum_moves RomanWheel.coq_RomanWheel curr_state in
      let move_tups = List.map (fun m ->
        let s' = coq_RW_exec_move curr_state m in
        (m, ExtractQuery.query_RW_TB tb s')
      ) moves in
      let move_tups_sorted = List.sort (fun (_,o1) (_,o2) ->
        if OCamlTB.p_leb curr_state.to_play o1 o2 then 1 else -1
        ) move_tups in
      let clickmove m _ =
        Controller.update (ClickMove m) (rs, rf) tb; true in
      List.concat_map (fun (m,o) ->
        let str =
          begin match o with
          | Some (pl, n) -> (
            match pl with
            | Player.White -> "White wins in " ^ string_of_int n
            | Player.Black -> "Black wins in " ^ string_of_int n
            )
          | None -> "Drawn"
          end in
        let text = print_RW_move curr_state m ^ ": " ^ str in
        [Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick (clickmove m); a_class ["whitewin"]; a_style "text-decoration: none"] [txt text]);
        Tyxml_js.Html.br ()
        ]
        ) move_tups_sorted
    | _ -> []

  let links (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_move_links (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let normal_style = Tyxml_js.Html.a_class ["normal"]
  let deselected = Tyxml_js.Html.a_class ["deselected"]
  let selected = Tyxml_js.Html.a_class ["selected"]

  let space () = Tyxml_js.Html.(a ~a:[] [txt " "])

  let pure_mode_toggles (rs,rf) tb x =
    let (style_e, style_p, style_q) =
      begin match x with
      | Model.PrePlay _ -> (deselected, selected, deselected)
      | Model.Play _ -> (deselected, selected, deselected)
      | Model.Edit _ -> (selected, deselected, deselected)
      | Model.Query _ -> (deselected, deselected, selected)
      end in
    let clickedit _ =
      Controller.update ClickEdit (rs, rf) tb; true in
    let clickplay _ =
      Controller.update ClickPlay (rs, rf) tb; true in
    let clickquery _ =
      Controller.update ClickQuery (rs, rf) tb; true in
    let edit = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickedit; style_e] [txt "Edit"]) in
    let play = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickplay; style_p] [txt "Play"]) in
    let query = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick clickquery; style_q] [txt "Query"]) in
    let mode_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Mode: "]) in
    [mode_text; space (); query; space (); edit; space (); play]

  let mode_toggles (rs, rf) tb =
    let vals = ReactiveData.RList.from_signal (React.S.map (pure_mode_toggles (rs, rf) tb) rs) in
    Js_of_ocaml_tyxml.Tyxml_js.R.Html.p vals

  let pure_player_toggles (rs,rf) tb x =
    match x with
    | Model.Play x ->
      let tb_pl = Model.(x.tb_player) in
      let pl_txt =
        match tb_pl with
        | Player.White -> "Black"
        | Player.Black -> "White" in
      let player_txt = Tyxml_js.Html.(a ~a:[normal_style] [txt pl_txt]) in
      let playing_as_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Playing as: "]) in
      [playing_as_text; player_txt]
    | Model.Edit x ->
      let curr_pl = Model.(x.to_play) in
      let click_to_play_black _ =
        Controller.update ClickToPlayBlack (rs, rf) tb; true in
      let click_to_play_white _ =
        Controller.update ClickToPlayWhite (rs, rf) tb; true in
      let (curr_style_w, curr_style_b) =
        match curr_pl with
        | Player.White -> (selected, deselected)
        | Player.Black -> (deselected, selected) in

      let to_play_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "To play: "]) in  
      let to_play_black = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick click_to_play_black; curr_style_b] [txt "black"]) in
      let to_play_white = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick click_to_play_white; curr_style_w] [txt "white"]) in

      [ to_play_text; space (); to_play_black; space (); to_play_white ]
    | Model.Query x ->
      let pl = Model.((x.curr_state).to_play) in
      let pl_txt =
        match pl with
        | Player.White -> "White"
        | Player.Black -> "Black" in
      let player_txt = Tyxml_js.Html.(a ~a:[normal_style] [txt pl_txt]) in
      let to_play_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "To play: "]) in
      [to_play_text; player_txt]
    | Model.PrePlay _ ->
      let deselected = Tyxml_js.Html.a_class ["deselected"] in
      let click_play_as_black _ =
        Controller.update ClickPlayAsBlack (rs, rf) tb; true in
      let click_play_as_white _ =
        Controller.update ClickPlayAsWhite (rs, rf) tb; true in
      let play_as_black = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick click_play_as_black; deselected] [txt "black"]) in
      let play_as_white = Tyxml_js.Html.(a ~a:[a_href "#"; a_onclick click_play_as_white; deselected] [txt "white"]) in
      let play_as_text = Tyxml_js.Html.(a ~a:[normal_style] [txt "Play as: "]) in
      [ play_as_text; play_as_black; space (); play_as_white ]

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
      curr_res tb (rs, rf);
      links (rs,rf) tb;
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
  let rp = React.S.create Model.init in
    start mp rp parent

let _ =
  let mp = make_tb in
  Js_of_ocaml_lwt.Lwt_js_events.onload () >>= (main (Obj.magic mp))
