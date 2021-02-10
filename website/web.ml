open Js_of_ocaml
module Html = Dom_html

let doc = Html.document
let button txt action =
  let button_type = Js.string "button" in
  let b = Html.createInput ~_type:button_type doc in
  b##.value := Js.string txt;
  b##.onclick := Dom_html.handler (fun _ -> action (); Js._true);
  b

let debug s = Firebug.console##debug (Js.string s)

let jsget x = Js.Opt.get x (fun () -> assert false)

(** Replace [c] by [t] in [s]. *)
let rec replace c t s =
  try
    let n = String.index s c in
    replace c t (String.sub s 0 n ^ t ^ String.sub s (n+1) (String.length s-(n+1)))
  with
  | Not_found -> s

open Prog

let run _ =
  let prog = jsget (Html.CoerceTo.textarea (jsget (doc##getElementById(Js.string "prog")))) in
  let go = jsget (doc##getElementById(Js.string "go")) in
  let status = jsget (doc##getElementById(Js.string "status")) in
  let status s = status##.innerHTML := Js.string s in
  let error s = status ("<em style=\"color:red\">" ^ s ^ "</em>") in
  let set id s =
    let p = jsget (doc##getElementById(Js.string id)) in
    let s = replace '\n' "<br/>" s in
    p##.innerHTML := Js.string s
  in

  go##.onclick :=
    Html.handler
      (fun _ ->
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
           set "fundamental" (Region.to_string prog fundamental);
           status "Computing normalized regions...";
           set "forbidden-normalized" (Region.to_string prog (Region.normalize prog forbidden));
           set "fundamental-normalized" (Region.to_string prog (Region.normalize prog fundamental));
           status "Computing deadlocks...";
           let deadlocks = "  " ^ String.concat ", " (List.map (Pos.to_string prog) (Region.deadlocks prog fundamental)) ^ "\n" in
           set "deadlocks" deadlocks;
           (*
  Printf.printf "* Deadlocks:\n%s\n%!" deadlocks;
  let deadlocks =
    let print _ =
      (* List.fold_left (fun s e -> Printf.sprintf "%s  %s\n" s (Lang.string_of_action e)) "" (Pos.realize prog t) *)
      "" (* TODO *) (* Printf.sprintf "  %s\n" (Prog.to_string (Pos.realize prog t)) *)
    in
    String.concat "\n" (List.map print (Region.deadlocks prog fundamental))
  in
  Printf.printf "* Deadlock realizers:\n%s\n%!" deadlocks;
  *)
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
      );

  Js._true

let () =
  Html.window##.onload := Html.handler run
