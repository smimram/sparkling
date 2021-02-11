open Common

type type_expr =
  | TVoid
  | TBool
  | TInt
  | TMutex

type expr =
  | EAssign of string * expr
  | ENew_var of type_expr * string
  | EAssert of expr
  | EReturn of expr
  | EVar of string
  | EInt of int
  | EBool of bool
  | EAdd of expr * expr
  | ESub of expr * expr
  | ENot of expr
  | EMult of expr * expr
  | EDiv of expr * expr
  | EIs_eq of expr * expr
  | ELe of expr * expr
  | ELt of expr * expr
  | EAnd of expr * expr
  | EOr of expr * expr

let string_of_type_expr = function
  | TVoid -> "void"
  | TInt -> "int"
  | TBool -> "bool"
  | TMutex -> "mutex"

let rec string_of_expr e =
  let string_of_expr e =
    match e with
    | EVar _ | EInt _ -> string_of_expr e
    | _ -> "(" ^ string_of_expr e ^ ")"
  in
  match e with
  | EAssign (s,e) -> Printf.sprintf "%s = %s" s (string_of_expr e)
  | ENew_var (t,v) -> Printf.sprintf "%s %s" (string_of_type_expr t) v
  | EVar v -> v
  | EInt n -> string_of_int n
  | EBool b -> if b then "true" else "false"
  | EAdd (e1, e2) -> Printf.sprintf "%s+%s" (string_of_expr e1) (string_of_expr e2)
  | ESub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_expr e1) (string_of_expr e2)
  | EMult (e1, e2) -> Printf.sprintf "%s*%s" (string_of_expr e1) (string_of_expr e2)
  | EDiv (e1, e2) -> Printf.sprintf "%s/%s" (string_of_expr e1) (string_of_expr e2)
  | ELe (e1, e2) -> Printf.sprintf "%s <= %s" (string_of_expr e1) (string_of_expr e2)
  | ELt (e1, e2) -> Printf.sprintf "%s < %s" (string_of_expr e1) (string_of_expr e2)
  | EIs_eq (e1, e2) -> Printf.sprintf "%s == %s" (string_of_expr e1) (string_of_expr e2)
  | ENot e -> Printf.sprintf "!%s" (string_of_expr e)
  | EAnd (e1, e2) -> Printf.sprintf "%s && %s" (string_of_expr e1) (string_of_expr e2)
  | EOr (e1, e2) -> Printf.sprintf "%s || %s" (string_of_expr e1) (string_of_expr e2)
  | EReturn e -> Printf.sprintf "return %s" (string_of_expr e)
  | EAssert e -> Printf.sprintf "assert(%s)" (string_of_expr e)

type t = expr Prog.t

let string_of_action = function
  | Prog.P m ->
    Printf.sprintf "lock(%s);" m
  | Prog.V m ->
    Printf.sprintf "unlock(%s);" m
  | Prog.Cmd e ->
    Printf.sprintf "%s;" (string_of_expr e)

let rec normalize_constr = function
  | ENot (ENot (e)) -> normalize_constr e
  | ENot (EAnd (e1, e2)) -> normalize_constr (EOr (ENot e1, ENot e2))
  | ENot (EOr (e1, e2)) -> normalize_constr (EAnd (ENot e1, ENot e2))
  | ENot (EIs_eq (e1, e2)) -> EOr (ELt (e1, e2), ELt (e2, e1))
  | ENot (ELe (e1, e2)) -> ELt (e2, e1)
  | ENot (ELt (e1, e2)) -> ELe (e2, e1)
  | EAnd (EOr (e1, e2), e3) -> normalize_constr (EOr (EAnd (e1, e3), EAnd (e2, e3)))
  | EAnd (e1, EOr (e2, e3)) -> normalize_constr (EOr (EAnd (e1, e2), EAnd (e1, e3)))
  | EAnd (e1, e2) -> EAnd (normalize_constr e1, normalize_constr e2)
  | EOr (e1, e2) -> EOr (normalize_constr e1, normalize_constr e2)
  | EIs_eq (_, _)
  | ELe (_, _)
  | ELt (_, _) as e -> e
  | _ -> assert false

(*
let normalize_constr e =
  Printf.printf "normalize: %s\n%!" (string_of_expr e);
  normalize_constr e
*)

let string_of_constr = function
  | EIs_eq (e1, e2) -> Printf.sprintf "%s = %s" (string_of_expr e1) (string_of_expr e2)
  | ELe (e1, e2) -> Printf.sprintf "%s <= %s" (string_of_expr e1) (string_of_expr e2)
  | ELt (e1, e2) -> Printf.sprintf "%s < %s" (string_of_expr e1) (string_of_expr e2)
  | _ -> assert false

let disjunctive_normal_form e =
  let rec disj = function
    | EOr (e1, e2) -> (disj e1)@(disj e2)
    | e -> [e]
  in
  let rec conj = function
    | EAnd (e1, e2) -> (conj e1)@(conj e2)
    | e -> [e]
  in
  let e = normalize_constr e in
  List.map conj (disj e)

let rec to_string ?(indent=0) p =
  let to_string ?(indent=indent+1) p = to_string ~indent p in
  let i = String.make (2*indent) ' ' in
  match p with
  | Prog.Seq l ->
    String.concat "\n" (List.map (to_string ~indent) l)
  | Prog.Par l ->
    i ^ "{\n" ^ String.concat "\n}|{\n" (List.map to_string l) ^ "\n};"
  | Prog.If (e,p1,p2) ->
    Printf.sprintf "%sif (%s) {\n%s\n}\nelse\n{\n%s\n}" i (string_of_expr e) (to_string p1) (to_string p2)
  | Prog.While (e,p) ->
    Printf.sprintf "%swhile (%s) {\n%s\n%s}" i (string_of_expr e) (to_string p) i
  | Prog.Action a ->
    i ^ string_of_action a
  | Prog.Call _ ->
    (* TODO *)
    assert false

let to_string p = to_string p

type declaration =
  type_expr (* type *)
  * string (* name *)
  * ((type_expr * string) list) option (* arguments, none means variable *)
  * expr Prog.t (* the program *)

open Prog

let rec inline decls p =
  let resolve f a =
    (* TODO: replace arguments *)
    ignore a;
    let ans = ref None in
    List.iter
      (fun (_, name, _, prog) ->
         if name = f then
           ans := Some prog
      ) decls;
    match !ans with
    | Some ans -> ans
    | None ->
      failwith (Printf.sprintf "Reference to undefined function \"%s\"." f)
  in
  (* TODO: generic iterator... *)
  let rec return x p =
    let return = return x in
    match p with
    | Action (Cmd (EReturn e)) -> Action (Cmd (EAssign (x,e)))
    | Action _ | Call _ -> p
    | Seq l -> Seq (List.map return l)
    | Par l -> Par (List.map return l)
    | If (b,p1,p2) -> If (b, return p1, return p2)
    | While (e,p) -> While(e, return p)
  in
  let inline = inline decls in
  match p with
  | Action _ -> p
  | Seq l -> Seq (List.map inline l)
  | Par l -> Par (List.map inline l)
  | If (b, p1, p2) -> If (b, inline p1, inline p2)
  | While (e, p) -> While (e, inline p)
  | Call (f,a,x) ->
    (
      match x with
      | Some x ->
        return x (inline (resolve f a))
      | None ->
        inline (resolve f a)
    )

type 'a bracket_state =
  {
    bs_defined_m : string list; (* Defined mutexes. *)
    bs_opened_m : (string * (Pos.t * Pos.t)) list; (* Opened mutexes. *)
    bs_taken_m : (string * (Pos.t * Pos.t * Pos.t * Pos.t)) list; (* Intervals where mutexes are taken (the two faces of the forbidden interval). *)
    bs_context : bool -> Pos.t -> Pos.t; (* The current context for positions. The boolean indicate wheter we want the maximal context (used for parallels). *)
  }

(* TODO: also check for definition of variables and access conflicts of
 * variables *)
let rec brackets s = function
  | Action (Cmd (ENew_var (TMutex, m))) ->
    (* TODO: cleanly handle name clashes *)
    assert (not (List.mem m s.bs_defined_m));
    {s with bs_defined_m = m::s.bs_defined_m}
  | Action (P m) ->
    if not (List.mem m s.bs_defined_m) then
      failwith (Printf.sprintf "Mutex %s was not declared." m);
    (* Not really necessary but cannot hurt. *)
    if List.mem_assoc m s.bs_opened_m then
      failwith (Printf.sprintf "Mutex %s taken twice in a row." m);
    {s with bs_opened_m = (m, (s.bs_context false Pos.PTop, s.bs_context true Pos.PTop))::s.bs_opened_m}
  | Action (V m) ->
    if not (List.mem m s.bs_defined_m) then
      failwith (Printf.sprintf "Mutex %s was not declared." m);
    (
      try
        let t1, t2 = List.assoc m s.bs_opened_m in
        {s with
         bs_opened_m = List.remove_assoc m s.bs_opened_m;
         bs_taken_m = (m, (t1, s.bs_context false Pos.PBot, t2, s.bs_context true Pos.PBot))::s.bs_taken_m
        }
      with
      | Not_found ->
        failwith (Printf.sprintf "Mutex %s released without having been taken." m)
    )
  | Action _ -> s
  | Seq l ->
    let n = ref (-1) in
    let context = s.bs_context in
    List.fold_left
      (fun s p ->
         incr n;
         brackets {s with bs_context = (fun max p -> context max (Pos.PSeq (!n,p)))} p
      ) s l
  | Par l ->
    let l = Array.of_list l in
    let ss =
      Array.mapi
        (fun n p ->
           brackets
             {
               s with
               bs_taken_m = [];
               bs_context =
                 (fun max pp ->
                    s.bs_context max
                      (
                        Pos.PPar
                          (List.init
                             (Array.length l)
                             (fun i ->
                                if i = n then
                                  pp
                                else if max then
                                  Pos.top l.(i)
                                else
                                  Pos.bot l.(i))
                          )
                      )
                 )
             } p
        ) l
    in
    (* TODO: consistency checks *)
    {
      bs_defined_m = s.bs_defined_m;
      bs_opened_m = s.bs_opened_m; (* TODO: we might want to open mutexes in pars *)
      bs_taken_m = Array.fold_left (fun tk s -> s.bs_taken_m@tk) s.bs_taken_m ss;
      bs_context = s.bs_context; (* TODO: is it ok? *)
    }
  | If (_,p1,p2) ->
    let s1 =
      brackets
        {s with
         bs_taken_m = [];
         bs_context = (fun max p -> s.bs_context max (Pos.PIf (true,p)))
        } p1
    in
    let s2 =
      brackets
        {s with
         bs_taken_m = [];
         bs_context = (fun max p -> s.bs_context max (Pos.PIf (false,p)))
        } p2
    in
    (* TODO: remove this restriction. *)
    assert (s1.bs_opened_m = s.bs_opened_m);
    assert (s2.bs_opened_m = s.bs_opened_m);
    {
      bs_defined_m = s.bs_defined_m;
      bs_opened_m = s.bs_opened_m;
      bs_taken_m = s1.bs_taken_m@s2.bs_taken_m;
      bs_context = s.bs_context; (*TODO: is it ok? *)
    }
  | While (_, p) ->
    let s' =
      brackets
        {s with
         bs_context = (fun max p -> s.bs_context max (Pos.PWhile p))
        } p
    in
    assert (s'.bs_opened_m = s.bs_opened_m);
    {
      bs_defined_m = s.bs_defined_m;
      bs_opened_m = s.bs_opened_m;
      bs_taken_m = s'.bs_taken_m;
      bs_context = s.bs_context; (*TODO: is it ok? *)
    }
  | Call _ ->
    assert false

let brackets p =
  let s =
    brackets
      {
        bs_defined_m = [];
        bs_opened_m = [];
        bs_taken_m = [];
        bs_context = (fun _ -> id);
      } p
  in
  if List.length s.bs_opened_m <> 0 then
    failwith (Printf.sprintf "The following mutexes are not released: %s." (String.concat ", " (List.map fst s.bs_opened_m)));
  s.bs_taken_m

let brackets p =
  List.map
    (fun (m, (t, _, _, u)) ->
       (m, Int.make (t, u))
    ) (brackets p)

let forbidden p =
  let brackets = brackets p in
  let mutexes =
    let ans = ref [] in
    List.iter (fun (m, _) -> ans := List.add_uniq m !ans) brackets;
    !ans
  in
  let ans = ref (Region.create ()) in
  let push i = ans := Region.add p i !ans in
  let push = List.iter push in
  List.iter
    (fun m ->
       List.iter_tail
         (fun x t ->
            List.iter (fun y -> push (Int.meet p x y)) t
         ) (List.assoc_all m brackets)
    ) mutexes;
  !ans

let allowed p = Region.compl p (forbidden p)
