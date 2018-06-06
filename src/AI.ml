open Apron
open Lang
open Common

let debug_transition = ref false

let man = Box.manager_alloc ()

let path p =
  let env = ref (Environment.make [||] [||]) in
  let env_map = ref [] in
  let abs = ref (Abstract1.top man !env) in
    List.iter
      (function
         | ENew_var (TInt, v) ->
             let var = Var.of_string v in
               env_map := (v, (TInt,var)) :: !env_map;
               env := Environment.add !env [|var|] [||];
               abs := Abstract1.change_environment man !abs !env false
         | EAssign (v,e) ->
             let var = snd (List.assoc v !env_map) in
               abs := Abstract1.assign_linexpr man !abs var (Apron.Parser.linexpr1_of_string !env (string_of_expr e)) None
         | _ -> assert false
      ) p;
    !abs

module Apron =
struct
  type 'a t =
      {
        env : Environment.t;
        env_map : (string * (Lang.type_expr * Var.t)) list;
        abs : 'a Abstract1.t;
      }

  let create () =
    let env = Environment.make [||] [||] in
      {
        env = env;
        env_map = [];
        abs = Abstract1.top man env;
      }

  let add_var e v =
    let var = Var.of_string v in
    let env_map = (v, (TInt,var)) :: e.env_map in
    let env = Environment.add e.env [|var|] [||] in
    let abs = Abstract1.change_environment man e.abs env false in
      {
        env = env;
        env_map = env_map;
        abs = abs;
      }

  let assign e v expr =
    let var = snd (List.assoc v e.env_map) in
    let abs = Abstract1.assign_linexpr man e.abs var (Apron.Parser.linexpr1_of_string e.env (string_of_expr expr)) None in
      {e with abs = abs}

  let meet_cons e cons =
    let cons = List.map string_of_constr cons in
    let abs = Abstract1.meet_lincons_array man e.abs (Parser.lincons1_of_lstring e.env cons) in
      {e with abs = abs}

  let to_string e =
    let buf = Buffer.create 10 in
      Format.bprintf buf "%a" Abstract1.print e.abs;
      Buffer.contents buf

  (* Both environments are assumed to have the same declared variables. *)
  let join e1 e2 =
    {e1 with abs = Abstract1.join man e1.abs e2.abs}

  let meet e1 e2 =
    {e1 with abs = Abstract1.meet man e1.abs e2.abs}

  let widening e1 e2 =
    {e2 with abs = Abstract1.join (*widening*) man e1.abs e2.abs}

  let is_eq e1 e2 =
    Abstract1.is_eq man e1.abs e2.abs
end

module Interval =
struct
  module Num =
  struct
    type t = int

    let bot = min_int

    let top = max_int

    let is_extr n =
      n = min_int || n = max_int

    (* TODO: assert that the addition is defined ie no infty-infty *)
    let add m n =
      if is_extr m then m
      else if is_extr n then n
      else m + n

    let sup (m:t) (n:t) = max m n

    let inf (m:t) (n:t) = min m n

    let to_string n =
      if n = bot then "-∞"
      else if n = top then " ∞"
      else Printf.sprintf "%02s" (string_of_int n)
  end

  (** Domain of intervals. *)
  module Int =
  struct
    type t = (Num.t * Num.t) option

    let make (m, n) =
      assert (m <= n);
      Some (m, n)

    let may_make (m, n) =
      if m <= n then
        Some (m, n)
      else
        None

    let bot = None

    let top = make (Num.bot, Num.top)

    let to_string i =
      match i with
        | None -> "⊥       "
        | i when i = top -> "⊤       "
        | Some (i1, i2) -> Printf.sprintf "[%s, %s]" (Num.to_string i1) (Num.to_string i2)

    let join i j =
      match i, j with
        | None, _ -> j
        | _, None -> i
        | Some i, Some j ->
            let i1, i2 = i in
            let j1, j2 = j in
              may_make (Num.inf i1 j1, Num.sup i2 j2)

    let meet i j =
      match i, j with
        | None, _ -> j
        | _, None -> i
        | Some i, Some j ->
            let i1, i2 = i in
            let j1, j2 = j in
              may_make (Num.sup i1 j1, Num.inf i2 j2)

    let add i j =
      match i, j with
        | None, _ -> None
        | _, None -> None
        | Some (i1, i2), Some (j1, j2) ->
            make (Num.add i1 j1, Num.add i2 j2)

    let closure_down i =
      match i with
        | None -> None
        | Some (n, _) -> Some (Num.bot, n)

    let closure_up i =
      match i with
        | None -> None
        | Some (n, _) -> Some (n, Num.top)

    (** Simulate an interval open in the first bound. *)
    let open_down i =
      match i with
        | None -> None
        | Some (i1, i2) -> Some (Num.add i1 1, i2)

    let open_up i =
      match i with
        | None -> None
        | Some (i1, i2) -> Some (i1, Num.add i2 1)

    let rec of_expr var = function
      | EInt n -> make (n, n)
      | EVar v -> var v
      | EAdd (e1, e2) -> add (of_expr var e1) (of_expr var e2)
      | _ -> assert false

    let widening i j =
      match i with
        | None ->
            (
              match j with
                | None -> None
                | _ -> top
            )
        | Some (i1, i2) ->
            let j1, j2 = get_some j in
              assert (j1 <= i1);
              assert (i2 <= j2);
              make
                ((if i1 = j1 then i1 else Num.bot),
                 (if i2 = j2 then i2 else Num.top))
  end

  type t = (string * Int.t) list

  let create () = []

  let add_var e v = (v, Int.top)::e

  let rm_var e v = List.filter (fun (w, _) -> w <> v) e

  let val_var e v = List.assoc v e

  let assign_int e v i = (v, i)::(rm_var e v)

  let assign e v expr = assign_int e v (Int.of_expr (val_var e) expr)

  let meet_int e v i =
    assign_int e v (Int.meet i (val_var e v))

  let rec meet_cons e cons =
    match cons with
      | EIs_eq (EVar v, e2) ->
          let i = Int.of_expr (val_var e) e2 in
            meet_int e v i
      | ELe (EVar v, e2) ->
          let i = Int.of_expr (val_var e) e2 in
            meet_int e v (Int.closure_down i)
      | ELe (e1, EVar v) ->
          let i = Int.of_expr (val_var e) e1 in
            meet_int e v (Int.closure_up i)
      | ELt (EVar v, e2) ->
          let i = Int.of_expr (val_var e) e2 in
            meet_int e v (Int.open_up (Int.closure_down i))
      | ELt (e1, EVar v) ->
          let i = Int.of_expr (val_var e) e1 in
            meet_int e v (Int.open_down (Int.closure_up i))
      | _ -> assert false

  let meet_cons e cons =
    List.fold_left meet_cons e cons

  let iter2 f e1 e2 =
    List.iter (fun (v, i) -> f v i (val_var e2 v)) e1

  let fold2 f x e1 e2 =
    let x = ref x in
      iter2 (fun v i j -> x:= f !x v i j) e1 e2;
      !x

  let join e1 e2 =
    fold2 (fun e v i j -> assign_int e v (Int.join i j)) (create ()) e1 e2

  let widening e1 e2 =
    fold2 (fun e v i j -> assign_int e v (Int.widening i j)) (create ()) e1 e2

  let is_eq e1 e2 =
    List.for_all (fun (v, i) -> val_var e2 v = i) e1

  let to_string e =
    List.fold_left
      (fun s (v, i) ->
         Printf.sprintf "%s  %s∊%s" s v (Int.to_string i)
      ) "" (List.sort (fun (v1,_) (v2,_) -> compare v1 v2) e)
end

module A = Interval (* Apron *)

module Environment =
struct
  let create () = A.create ()

  let transition e p =
    (* Printf.printf "  %s\n%!" (Lang.string_of_expr p); *)
    match p with
      | ENew_var (TMutex,v) -> e
      | ENew_var (TInt,v) -> A.add_var e v
      | EAssign (v,expr) -> A.assign e v expr
      | _ ->
          (* Printf.eprintf "expr: %s\n%!" (string_of_expr p); *)
          assert false

  let transition_action e = function
    | Prog.Cmd a -> transition e a
    | _ -> e

  let rec transition e p =
    let transition e p =
      let e' = transition e p in
        if !debug_transition then
          Printf.printf "** transition:\n--%s\n%s\n--%s\n\n%!" (A.to_string e) (Lang.to_string p) (A.to_string e');
        e'
    in
    match p with
      | Prog.Seq l
      | Prog.Par l -> List.fold_left transition e l
      | Prog.If (expr, p1, p2) ->
          let cons1 = disjunctive_normal_form expr in
          let e1 = List.map (fun cons -> transition (A.meet_cons e cons) p1) cons1 in
          let cons2 = disjunctive_normal_form (ENot expr) in
          let e2 = List.map (fun cons -> transition (A.meet_cons e cons) p2) cons2 in
          let e = e1@e2 in
            List.fold_left A.join (List.hd e) (List.tl e)
      | Prog.While (expr, p) ->
          (* TODO: widening, narrowing, etc. *)
          let cons = disjunctive_normal_form expr in
          let e' = List.map (fun cons -> transition (A.meet_cons e cons) p) cons in
          let e' = List.map (fun e' -> A.widening e (A.join e e')) e' in
          let e' = List.fold_left A.join (List.hd e') (List.tl e') in
            (* Printf.printf "WHILE %s\n%!" (A.to_string e'); *)
            if A.is_eq e e' then
              let e' = List.map (fun cons -> A.meet_cons e' cons) (disjunctive_normal_form (ENot expr)) in
              let e' = List.fold_left A.join (List.hd e') (List.tl e') in
                e'
                else
                  transition e' (Prog.While (expr, p))
      | Prog.Action a -> transition_action e a
      | Prog.Call _ -> assert false

  let join = A.join

  let to_string = A.to_string
end

module Env = Environment

let flow p g =
  (* Data attached to a node. *)
  let local = ref [Prog.Pos.bot p, Env.create ()] in
    Prog.Flow_graph.iter_breadth
      (fun t1 p t2 ->
         let e1 =
           try
             List.assoc t1 !local
           with
             | Not_found -> assert false
         in
         (* Printf.printf "* transition %s to %s\n%!" (Prog.Pos.to_string_simple
          * t1) (Prog.Pos.to_string_simple t2); *)
         let e2 = Env.transition e1 p in
         let e2 =
           try
             let e2' = List.assoc t2 !local in
               Env.join e2 e2'
           with
             | Not_found -> e2
         in
           local := (t2, e2) :: !local
      ) g;
    List.iter
      (fun (t,e) ->
         Format.printf "%32s : %s\n%!" (Prog.Pos.to_string_simple t) (Env.to_string e)
      ) !local

let print_path p =
    Format.printf "Abstract interpretation: %a\n\n%!" Abstract1.print (path p)
