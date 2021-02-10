open Prog

(* Test for the square *)
let () =
  let p = Seq [Action (P "a"); Action (V "a")] in
  let p = Seq [Action (Cmd (Lang.ENew_var (Lang.TMutex, "a"))); Par [p; p]] in
  let f = Lang.forbidden p in
  Printf.printf "forbidden:\n%s\n%!" (Region.to_string p f);
  Printf.printf "forbidden normalized:\n%s\n%!" (Region.to_string p (Region.normalize p f));
  let f = Region.compl p f in
  Printf.printf "fundamental:\n%s\n%!" (Region.to_string p f);
  Printf.printf "fundamental normalized:\n%s\n%!" (Region.to_string p f);
  let f = Region.compl p f in
  Printf.printf "forbidden:\n%s\n%!" (Region.to_string p f);
  Printf.printf "forbidden normalized:\n%s\n%!" (Region.to_string p (Region.normalize p f));
