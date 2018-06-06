let fname = ref "test.sparkling"

open Prog

let () =
  if Array.length Sys.argv > 1 then
    fname := Sys.argv.(1);
  let lexbuf =
    let fi = open_in !fname in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
      really_input fi buf 0 flen;
      close_in fi;
      Lexing.from_string (Bytes.to_string buf)
  in
  let decls =
    try
      Parser.main Lexer.token lexbuf
    with
      | Failure "lexing: empty token" ->
          let pos = (Lexing.lexeme_end_p lexbuf) in
          let err =
            Printf.sprintf "Lexing error at line %d, character %d."
              pos.Lexing.pos_lnum
              (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
          in
            failwith err
      | Parsing.Parse_error ->
          let pos = (Lexing.lexeme_end_p lexbuf) in
          let err =
            Printf.sprintf "Parse error at word \"%s\", line %d, character %d."
              (Lexing.lexeme lexbuf)
              pos.Lexing.pos_lnum
              (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
          in
            failwith err
  in
  let main =
    let ans = ref None in
      List.iter
        (fun (_, name, _, prog) ->
           if name = "main" then
             ans := Some prog
        ) decls;
      !ans
  in
  let prog =
    match main with
      | Some main -> main
      | None ->
          failwith "No main function."
  in
  let prog = Lang.inline decls prog in
  let b = Lang.brackets prog in
  (* let region_f, comp = Lang.components prog in *)
    Printf.printf "* Program:\n  %s\n\n%!" (Prog.to_string prog);
    Printf.printf "* Brackets:\n%!";
    List.iter
      (fun (m,i) ->
         Printf.printf "  %s: %s\n%!" m (Int.to_string prog i)
      ) b;
    Printf.printf "\n%!";
    let forbidden = Lang.forbidden prog in
    Printf.printf "* Forbidden:\n%s\n%!" (Area.to_string prog forbidden);
    let fundamental = Area.compl prog forbidden in
    Printf.printf "* Fundamental:\n%s\n%!" (Area.to_string prog fundamental);
    Printf.printf "* Forbidden (normalized):\n%s\n%!" (Area.to_string prog (Area.compl prog fundamental));
    Printf.printf "* Fundamental (normalized):\n%s\n%!" (Area.to_string prog (Area.normalize prog fundamental));
    let deadlocks = "  " ^ String.concat ", " (List.map (Pos.to_string prog) (Area.deadlocks prog fundamental)) ^ "\n" in
    Printf.printf "* Deadlocks:\n%s\n%!" deadlocks;
    let deadlocks =
      let print t =
        (* List.fold_left (fun s e -> Printf.sprintf "%s  %s\n" s (Lang.string_of_action e)) "" (Pos.realize prog t) *)
        "" (* TODO *) (* Printf.sprintf "  %s\n" (Prog.to_string (Pos.realize prog t)) *)
      in
        String.concat "\n" (List.map print (Area.deadlocks prog fundamental))
    in
    Printf.printf "* Deadlock realizers:\n%s\n%!" deadlocks;
    (*
    Printf.printf "* Components:\n%s\n%!" (Area.to_string prog (Area.components fundamental));
    Printf.printf "* Components:\n%s\n%!" (Area.to_string prog (Area.normalize (Area.components fundamental)));
    (* Printf.printf "* Components:\n%s\n%!" (Area.to_string prog (Area.normalize (Area.normalize (Area.components fundamental)))); *)
    Printf.printf "* All:\n%s\n%!" (Area.to_string prog (Area.normalize (Area.join fundamental forbidden)));
    Printf.printf "* Components:\n%s\n%!" (CArea.to_string prog comp);
    (*
      let fo = open_out_bin "components.dot" in
        output_string fo (GArea.to_dot prog region);
        close_out fo
    );*)
    *)
    Printf.printf "* Ginsu:\n%s\n%!" (Area.to_string prog (Area.ginsu fundamental));
    let fg = Flow_graph.of_area (* ~no_squares:true *) ~diagonals:true prog fundamental in
    let fo = open_out_bin "ginsu.dot" in
      (* output_string fo (Area.to_dot prog (Area.ginsu fundamental)); *)
      output_string fo (Flow_graph.to_dot prog fg);
      close_out fo;
    Printf.printf "* Flowing graph\n\n%!";

    (* AI.flow prog fg *)
