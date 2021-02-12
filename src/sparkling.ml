let fname = ref "swiss-flag.sparkling"

open Prog

let () =
  if Array.length Sys.argv > 1 then fname := Sys.argv.(1);
  let prog = Frontend.parse_file !fname in
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
  Printf.printf "* Forbidden:\n%s\n%!" (Region.to_string prog forbidden);
  let fundamental = Region.compl prog forbidden in
  Printf.printf "* Fundamental:\n%s\n%!" (Region.to_string prog fundamental);
  Printf.printf "* Forbidden (normalized):\n%s\n%!" (Region.to_string prog (Region.compl prog fundamental));
  Printf.printf "* Fundamental (normalized):\n%s\n%!" (Region.to_string prog (Region.normalize prog fundamental));
  let deadlocks = "  " ^ String.concat ", " (List.map (Pos.to_string prog) (Region.deadlocks prog fundamental)) ^ "\n" in
  Printf.printf "* Deadlocks:\n%s\n%!" deadlocks;
  let deadlocks =
    let print _ =
      (* List.fold_left (fun s e -> Printf.sprintf "%s  %s\n" s (Lang.string_of_action e)) "" (Pos.realize prog t) *)
      "" (* TODO *) (* Printf.sprintf "  %s\n" (Prog.to_string (Pos.realize prog t)) *)
    in
    String.concat "\n" (List.map print (Region.deadlocks prog fundamental))
  in
  Printf.printf "* Deadlock realizers:\n%s\n%!" deadlocks;
    (*
    Printf.printf "* Components:\n%s\n%!" (Region.to_string prog (Region.components fundamental));
    Printf.printf "* Components:\n%s\n%!" (Region.to_string prog (Region.normalize (Region.components fundamental)));
    (* Printf.printf "* Components:\n%s\n%!" (Region.to_string prog (Region.normalize (Region.normalize (Region.components fundamental)))); *)
    Printf.printf "* All:\n%s\n%!" (Region.to_string prog (Region.normalize (Region.join fundamental forbidden)));
    Printf.printf "* Components:\n%s\n%!" (CRegion.to_string prog comp);
    (*
      let fo = open_out_bin "components.dot" in
        output_string fo (GRegion.to_dot prog region);
        close_out fo
    );*)
    *)
  (* Printf.printf "* Ginsu:\n%s\n%!" (Region.to_string prog (Region.ginsu fundamental)); *)
  (* let fg = Flow_graph.of_region (\* ~no_squares:true *\) ~diagonals:true prog fundamental in *)
  (* let fo = open_out_bin "ginsu.dot" in *)
  (* output_string fo (Region.to_dot prog (Region.ginsu fundamental)); *)
  (* output_string fo (Flow_graph.to_dot prog fg); *)
  (* close_out fo; *)
  (* Printf.printf "* Flowing graph\n\n%!"; *)

  (* AI.flow prog fg *)
