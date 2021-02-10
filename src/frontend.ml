(** Parse a program. *)
let parse prog =
  let lexbuf = Lexing.from_string prog in
  let decls =
    try
      Parser.main Lexer.token lexbuf
    with
    | Failure _ ->
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
  Lang.inline decls prog

let parse_file fname =
  let prog =
    let fi = open_in fname in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    Bytes.to_string buf
  in
  parse prog
