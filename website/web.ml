open Js_of_ocaml
module Html = Dom_html

open Helper

let doc = Html.document

let debug s = Firebug.console##debug (Js.string s)

let jsget x = Js.Opt.get x (fun () -> assert false)

(** Replace [c] by [t] in [s]. *)
let replace_char c t s =
  String.concat t (String.split_on_char c s)

(** Replace [o] by [n] in [s]. *)
let replace o n s =
  String.concat n (String.split_on_string o s)

open Prog

let examples () =
  let prog = jsget (Html.CoerceTo.textarea (jsget (doc##getElementById(Js.string "prog")))) in
  let select = jsget (doc##getElementById(Js.string "ex-prog")) in
  let select = jsget (Html.CoerceTo.select select) in
  let () =
    let options = ref "" in
    List.iter
      (fun (fname, _) ->
         options := !options ^ "<option>" ^ fname ^ "</option>"
      ) Examples.list;
    select##.innerHTML := Js.string !options;
  in
  select##.onchange := Html.handler (fun _ -> prog##.innerHTML := Js.string (List.assoc (Js.to_string select##.value) Examples.list); Js._true)

let run _ =
  let prog = jsget (Html.CoerceTo.textarea (jsget (doc##getElementById(Js.string "prog")))) in
  let go = jsget (doc##getElementById (Js.string "go")) in
  let status = jsget (doc##getElementById (Js.string "status")) in
  let status s = status##.innerHTML := Js.string s in
  let error s = status ("<em style=\"color:red\">" ^ s ^ "</em>") in
  let set id s =
    let p = jsget (doc##getElementById(Js.string id)) in
    let s = replace_char '\n' "<br/>" s in
    p##.innerHTML := Js.string s
  in
  let set_region id r =
    let r = String.split_on_char '\n' r in
    let r = List.map
        (fun tr ->
           let tr = String.split_on_string "—" tr |> List.map (fun td -> "<td>"^td^"</td>") |> String.concat "<td>—</td>" in
           "<tr>"^tr^"</tr>"
        ) r
    in
    let r = String.concat "" r in
    let r = "<table>"^r^"</table>" in
    set id r
  in

  let handler _ =
    try
      status "Parsing program...";
      let prog = Js.to_string prog##.value in
      let prog = Frontend.parse prog in
      ignore prog;
      (jsget (doc##getElementById(Js.string "parsed")))##.innerHTML := Js.string (Prog.to_string prog);
      status "Computing brackets...";
      let b = Lang.brackets prog in
      let bs = ref "" in
      List.iter
        (fun (m,i) ->
           bs := Printf.sprintf "%s  %s: %s\n%!" !bs m (Int.to_string prog i)
        ) b;
      set "brackets" !bs;
      status "Computing forbidden region...";
      let forbidden = Lang.forbidden prog in
      set "forbidden" (Region.to_string prog forbidden);
      status "Computing fundamental region...";
      let fundamental = Region.compl prog forbidden in
      set_region "fundamental" (Region.to_string prog fundamental);
      status "Computing normalized regions...";
      set_region "forbidden-normalized" (Region.to_string prog (Region.normalize prog forbidden));
      set_region "fundamental-normalized" (Region.to_string prog (Region.normalize prog fundamental));
      status "Computing deadlocks...";
      let deadlocks = String.concat "<br/>" (List.map (BPos.to_string prog) (Region.deadlocks prog fundamental)) ^ "\n" in
      set "deadlocks" deadlocks;
      status "Finished.";
      Js._true
    with
    | Exit ->
      Js._false
    | Failure s ->
      error ("Error: " ^ s);
      Js._false
    | e ->
      error (Printexc.to_string e);
      Js._false
  in
  examples ();
  go##.onclick := Html.handler handler;
  (* ignore (handler ()); *)
  Js._true

let () =
  Html.window##.onload := Html.handler run
