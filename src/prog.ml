open Common

let debug s = Printf.printf "[DD] %s\n%!" s
(* let error s = Printf.printf "[EE] %s\n%!" s *)
(* let debug_le = false *)
(* let debug_int = true *)
(* let debug_meet = ref false *)
let debug_meet_full = ref false
(* let debug_belongs = ref false *)
(* let debug_inf = ref false *)
(* let debug_supinf = ref false *)
let debug_compl = ref false
(* let debug_compl_full = ref false *)
let debug_difference = ref false
(* let debug_components = ref false *)
(* let debug_realize = ref false *)

(* For now, we assume that there is no par in while. *)
type 'a t =
  | Action of 'a action
  | Seq of 'a t list
  | Par of 'a t list
  | If of 'a * 'a t * 'a t
  | While of 'a * 'a t
  | Call of string * 'a list * (string option)
and 'a action =
  | P of string
  | V of string
  | Cmd of 'a

type 'a prog = 'a t

let rec to_string p =
  let to_string = function
    | Action _
    | While _
    | Seq _ as p -> to_string p
    | p -> "(" ^ to_string p ^ ")"
  in
  match p with
  | Seq l -> String.concat ";" (List.map to_string l)
  | Par l -> String.concat "|" (List.map to_string l)
  | Action (P m) -> "P(" ^ m ^ ")"
  | Action (V m) -> "V(" ^ m ^ ")"
  | Action (Cmd _) -> "?"
  | If (_,p1,p2) -> Printf.sprintf "(%s)+(%s)" (to_string p1) (to_string p2)
  | While (_,p) -> "W(" ^ to_string p ^ ")"
  | Call _ -> "C"

module Pos = struct
  exception Incompatible

  type t =
    | PBot
    | PTop
    | PSeq of int * t
    | PPar of t list (* TODO: use an array instead? *)
    | PIf of bool * t
    | PWhile of t

  let rec to_string p t =
    let to_string p = function
      | PBot | PTop | PIf _ as t -> to_string p t
      | t -> "(" ^ to_string p t ^ ")"
    in
    match (p, t) with
    | _, PBot -> "⊥"
    | _, PTop -> "⊤"
    | Seq l, PSeq (n, t) ->
      (* TODO: enhance this *)
      let ans = ref "" in
      for _ = 0 to n - 1 do ans := !ans ^ "□;" done;
      ans := !ans ^ to_string (List.ith l n) t;
      for _ = 0 to (List.length l) - (n+1) - 1 do ans := !ans ^ ";_" done;
      !ans
    | _, PSeq _ -> assert false
    | Par ll, PPar l ->
      String.concat "|" (List.map2 to_string ll l)
    | _, PPar _ -> assert false
    | If (_, p, _), PIf (b,t) ->
      if b then to_string p t ^ "+_"
      else "_+" ^ to_string p t
    | _, PIf _ -> assert false
    | While (_, p), PWhile t -> (to_string p t) ^ "*"
    | _, PWhile _ -> assert false

  let rec to_string_simple t =
    let to_string = function
      | PBot | PTop | PIf _ as t -> to_string_simple t
      | t -> "(" ^ to_string_simple t ^ ")"
    in
    match t with
    | PBot -> "⊥"
    | PTop -> "⊤"
    | PSeq (n, t) ->
      if n = max_int then "...;" ^ (to_string t) else
        let ans = ref "" in
        for _ = 0 to n - 1 do ans := !ans ^ "□;" done;
        ans := !ans ^ to_string t;
        !ans ^ ";"
    | PPar l ->
      String.concat "|" (List.map to_string l)
    | PIf (b,t) ->
      if b then to_string t ^ "+_"
      else "_+" ^ to_string t
    | PWhile t -> "(" ^ to_string_simple t ^ ")*"

  let bot (_ : 'a prog) = PBot

  let top (_ : 'a prog) = PTop

  (* TODO: we should check for imbricated loops! (in which case it is always le) *)
  let rec le t1 t2 =
    match (t1, t2) with
    | PBot, _ -> true
    | _, PBot -> false
    | _, PTop -> true
    | PTop, _ -> false
    | PSeq (n1, t1), PSeq (n2, t2) ->
      n1 < n2 || (n1 = n2 && le t1 t2)
    | PPar l1, PPar l2 ->
      List.for_all2 le l1 l2
    | PIf (b1,t1), PIf (b2,t2) ->
      if b1 <> b2 then raise Incompatible;
      le t1 t2
    | PWhile t1, PWhile t2 ->
      (* Check for incompatibility. *)
      ignore (le t1 t2 || le t2 t1);
      true
    | _ ->
      debug (Printf.sprintf "le: cannot compare %s with %s." (to_string_simple t1) (to_string_simple t2));
      assert false

  let ge t1 t2 = le t2 t1
end

module BPos = struct
  (* exception Incompatible *)

  open Pos

  type t =
    | BPBot
    | BPTop
    | BPSeq of int * t * int
    | BPPar of t list (* TODO: use an array instead? *)
    | BPIf of bool * t
    | BPWhile of int * t

  let rec to_string p t =
    let to_string p = function
      | BPBot | BPTop | BPIf _ as t -> to_string p t
      | t -> "(" ^ to_string p t ^ ")"
    in
    match (p, t) with
    | _, BPBot -> "⊥"
    | _, BPTop -> "⊤"
    | Seq l, BPSeq (n, t, _) ->
      (* TODO: enhance this *)
      let ans = ref "" in
      for _ = 0 to n - 1 do ans := !ans ^ "□;" done;
      ans := !ans ^ to_string (List.ith l n) t;
      for _ = 0 to (List.length l) - (n+1) - 1 do ans := !ans ^ ";_" done;
      !ans
    | _, BPSeq _ -> assert false
    | Par ll, BPPar l ->
      String.concat "|" (List.map2 to_string ll l)
    | _, BPPar _ -> assert false
    | If (_, p, _), BPIf (b,t) ->
      if b then to_string p t ^ "+_"
      else "_+" ^ to_string p t
    | _, BPIf _ -> assert false
    | While (_, p), BPWhile(_,t) -> (to_string p t) ^ "*"
    | _, BPWhile _ -> assert false

  let rec to_string_simple t =
    let to_string = function
      | BPBot | BPTop | BPIf _ as t -> to_string_simple t
      | t -> "(" ^ to_string_simple t ^ ")"
    in
    match t with
    | BPBot -> "⊥"
    | BPTop -> "⊤"
    | BPSeq (n, t, _) ->
      if n = max_int then "...;" ^ (to_string t) else
        let ans = ref "" in
        for _ = 0 to n - 1 do ans := !ans ^ "□;" done;
        ans := !ans ^ to_string t;
        !ans ^ ";"
    | BPPar l ->
      String.concat "|" (List.map to_string l)
    | BPIf (b,t) ->
      if b then to_string t ^ "+_"
      else "_+" ^ to_string t
    | BPWhile(n,t) -> "(" ^ to_string_simple t ^ ")" ^ (string_of_int n)

  let bot (_ : 'a prog) = BPBot

  let top (_ : 'a prog) = BPTop
  
  let rec conversion p t =
    match p,t with
    | _, PBot -> [BPBot]
    | _, PTop -> [BPTop]
    | Seq p1 , PSeq(n1,t1) -> List.map (fun x -> BPSeq(n1, x, List.length p1)) (conversion (List.nth p1 n1) t1) 
    | Par p1 , PPar t1 -> 
      List.map (fun l -> BPPar (List.rev l)) 
          (List.fold_left (fun acc l -> 
              List.flatten (List.map (fun y -> 
                  List.map (fun x -> y::x) acc) l)
              ) 
              [[]] (List.map2 (conversion) p1 t1))
    | If(_, p1, _), PIf(true, t1) -> List.map (fun x -> BPIf(true, x)) (conversion p1 t1) 
    | If(_, _, p2), PIf(false, t2) -> List.map (fun x -> BPIf(false, x)) (conversion p2 t2) 
    | While (_, p1), PWhile t1 -> let sub = conversion p1 t1 in 
      (List.map (fun x -> BPWhile(0, x)) sub)@(List.map (fun x -> BPWhile(1, x)) sub)
    | _,_ -> debug (Printf.sprintf "BPos.conversion: Unmatched case %s." (Pos.to_string_simple t));
    assert false
    ;;

  (*Return the position t1 v t2 *)
  let rec meet t1 t2 =
    match (t1,t2) with 
    | BPBot, _ -> BPBot
    | _, BPBot -> BPBot
    | _, BPTop -> t1
    | BPTop, _ -> t2
    | BPSeq (n1, t1, m), BPSeq (n2, t2,_) when n1=n2-> BPSeq(n1,meet t1 t2,m)
    | BPSeq (n1, t1,m), BPSeq (n2, _,_) when n1<n2-> BPSeq(n1,t1,m)
    | BPSeq (n1, _,_), BPSeq (n2, t2,m) when n1>n2-> BPSeq(n2,t2,m)
    | BPPar l1, BPPar l2 -> BPPar (List.map2 meet l1 l2)
    | BPIf (b1,_), BPIf (b2,_) when b1 <> b2-> BPBot
    | BPIf (b1,t1), BPIf (b2,t2) when b1 == b2-> BPIf (b1, meet t1 t2)
    | BPWhile(n1,t1), BPWhile(n2,t2) when n1 = n2 -> BPWhile(n1, meet t1 t2)
    | BPWhile(n1,t1), BPWhile(n2,_) when n1 < n2 -> BPWhile(n1, t1)
    | BPWhile(n1,_), BPWhile(n2,t2) when n1 > n2 -> BPWhile(n2, t2)
    | _ -> debug (Printf.sprintf "meet: cannot compare %s with %s." (to_string_simple t1) (to_string_simple t2));
           assert false
  ;;

  (*Return the position t1 ∧ t2 *)
  let rec up_meet t1 t2 =
    match (t1,t2) with 
    | BPBot, _ -> t2
    | _, BPBot -> t1
    | _, BPTop -> BPTop
    | BPTop, _ -> BPTop
    | BPSeq (n1, t1, m), BPSeq (n2, t2, _) when n1=n2-> BPSeq(n1, up_meet t1 t2, m)
    | BPSeq (n1, t1, m), BPSeq (n2, _, _) when n1 > n2-> BPSeq(n1, t1, m)
    | BPSeq (n1, _, _), BPSeq (n2, t2, m) when n1 < n2-> BPSeq(n2, t2, m)
    | BPPar l1, BPPar l2 -> BPPar (List.map2 up_meet l1 l2)
    | BPIf (b1,_), BPIf (b2,_) when b1 <> b2-> BPTop
    | BPIf (b1,t1), BPIf (b2,t2) when b1 == b2-> BPIf (b1, up_meet t1 t2)
    | BPWhile(n1,t1), BPWhile(n2,t2) when n1 = n2 -> BPWhile(n1, up_meet t1 t2)
    | BPWhile(n1,t1), BPWhile(n2,_) when n1 > n2 -> BPWhile(n1, t1)
    | BPWhile(n1,_), BPWhile(n2,t2) when n1 < n2 -> BPWhile(n2, t2)
    | _ -> debug (Printf.sprintf "up_meet: cannot compare %s with %s." (to_string_simple t1) (to_string_simple t2));
           assert false
  ;;
  
  let le t1 t2 = 
  (meet t1 t2 = t1)

  let ge t1 t2 = le t2 t1

  (*Returns the maximal elements not greater than t*)
  let rec not_sup p t = 
    match t, p with
    | BPBot, _ -> []
    (* | BPTop -> debug (Printf.sprintf "BPos.not_sup: Should not encouter lower-bound %s." (to_string_simple t));
      assert false  *)
    | BPTop, _ ->  let p_list = match p with
        | Action _ -> [BPBot] (*Enorme problème ici!!!!!!!!!!!!!! TODO : faut retourner le précédent, a voir en fonction du programme associé!*)
        | Seq lp -> [BPSeq((List.length lp)-1, BPTop, (List.length lp))]
        | Par lp -> [BPPar(List.map (fun _ -> BPTop) (lp))]
        | While _ -> debug (Printf.sprintf "BPos.not_sup: Should not encouter lower-bound %s." (to_string_simple t));
        assert false
        | If _ -> [BPIf(true, BPTop); BPIf(false, BPTop)]
        | _ -> []
      in p_list
    | BPSeq(n,t, _), _ when (n,t) = (0,BPBot) -> [BPBot]
    | BPSeq(n,t, m), _ when t = BPBot -> [BPSeq(n-1, BPTop, m)]
    | BPSeq(n, t, m), Seq lp -> List.map (fun x -> BPSeq(n, x, m)) (not_sup (List.nth lp n) t)
    | BPPar l, Par lp -> let rec aux head l l_pg acc =
      match l, l_pg with
      (*| [],_ -> acc*)
      | h::tail, h_pg::t_pg -> aux (h::head) tail t_pg 
              (List.map (fun x -> BPPar ((List.map (fun _ -> BPTop) head)@[x]@(List.map (fun _ -> BPTop) tail))) (not_sup h_pg h))@acc
      | _,_ -> acc
      in aux [] l lp [] 
    | BPIf (b,t), _ when t = BPBot -> [BPIf(not b, BPTop)]
    | BPIf (b,t), If(_,p1,p2) -> BPIf(not b, BPTop)::(List.map (fun (x) -> BPIf(b,x)) (not_sup (if b then p1 else p2) t))
    | BPWhile(n,t), _ when (n,t) = (0,BPBot) -> [BPBot]
    | BPWhile(n,t), _ when t = BPBot -> [BPWhile(n-1,BPTop)]
    | BPWhile(n,t), While (_, p) -> List.map (fun (x) -> BPWhile(n,x)) (not_sup p t)
    | _,_ -> debug (Printf.sprintf "not_sup : Position %s not valid for its program" (to_string_simple t));
    assert false
  ;;
  
  (*Returns the minimal elements not smaller than t*)
  let rec not_inf p t = 
    match t, p with
    (* | BPBot -> debug (Printf.sprintf "BPos.not_inf: Should not encouter upper-bound %s." (to_string_simple t));
    assert false  *)
    | BPTop, _ -> []
    | BPSeq(n, t, m), _ when (n,t) = (m,BPTop) -> [BPTop]
    | BPSeq(n, t, m), _ when t = BPTop -> [BPSeq(n+1, BPBot, m)]
    | BPSeq(n, t, m), Seq lp -> List.map (fun x -> BPSeq(n, x, m)) (not_inf (List.nth lp n) t)
    | BPPar l, Par lp -> let rec aux head l l_pg acc =
      match l, l_pg with
      (*| [],_ -> acc*)
      | h::tail, h_pg::t_pg -> aux (h::head) tail t_pg 
              (List.map (fun x -> BPPar ((List.map (fun _ -> BPBot) head)@[x]@(List.map (fun _ -> BPBot) tail))) (not_inf h_pg h))@acc
      | _,_ -> acc
      in aux [] l lp [] 
    | BPIf (b,t), _ when t = BPBot -> [BPIf(not b, BPBot)]    
    | BPIf(b,t), If(_,p1,p2) -> BPIf(not b, BPBot)::(List.map (fun (x) -> BPIf(b,x)) (not_inf (if b then p1 else p2) t ))  
    | BPWhile(n,t), _ when (n,t) = (1,BPTop) -> [BPTop]
    | BPWhile(n,t), _ when t = BPTop -> [BPWhile(n+1,BPBot)]
    | BPWhile(n,t), While (_, p1) -> List.map (fun (x) -> BPWhile(n,x)) (not_inf p1 t)
    | BPBot, _ -> let p_list = match p with
        | Action _ -> [BPTop] (*Enorme problème ici!!!!!!!!!!!!!! TODO : faut retourner le précédent, a voir en fonction du programme associé!*)
        | Seq lp -> [BPSeq(0, BPBot, (List.length lp))]
        | Par lp -> [BPPar(List.map (fun _ -> BPBot) (lp))]
        | While _ -> [BPWhile(0, BPBot)]
        | If _ -> [BPIf(true, BPBot); BPIf(false, BPBot)]
        | _ -> []
      in p_list
    | _,_ ->  debug (Printf.sprintf "not_inf : Position %s not valid for its program" (to_string_simple t));
    assert false
    ;;


  (*Checks if 2 positions correspond to the same position after forgetfullness*)
  let rec redundancy t1 t2 =
    match t1,t2 with
    | t1, t2 when t1 = t2 -> true
    | BPIf(b1,t1), BPIf(b2,t2) -> (b1 = b2) && (redundancy t1 t2)
    | BPWhile(_,t1), BPWhile(_,t2) -> (redundancy t1 t2)
    | BPSeq(n1,t1,_), BPSeq(n2,t2,_) -> (n1 = n2) && (redundancy t1 t2)
    | BPPar l1, BPPar l2 -> List.fold_right2 (fun t1 t2 b -> (redundancy t1 t2) && b) l1 l2 true
    | _ -> false

end

module Int = struct
  open BPos

  type t = BPos.t * BPos.t

  let everything p = bot p, top p

  let to_string p (t1,t2) = BPos.to_string p t1 ^ " — " ^ BPos.to_string p t2

  let to_string_simple (t1,t2) = BPos.to_string_simple t1 ^ " — " ^ BPos.to_string_simple t2

  let valid (t1,t2) = le t1 t2

  let make i =
    let valid = valid i in
    if not valid then debug (Printf.sprintf "Int.make: invalid interval %s." (to_string_simple i));
    assert valid;
    i

  let bounds = id

  let meet p i j =
    let (x1,y1),(x2,y2) = i,j in
    let m = (up_meet x1 x2, meet y1 y2) in
    if !debug_meet_full then
    (
      debug ( Printf.sprintf "Int.meet: %s ∨ %s = %s." (to_string p i) (to_string p j) (to_string p m));
      assert (valid m);
    );
    m

  let included p i j = (meet p i j = i)
      (* let included _ _ _ = false  *)

  let belongs p x i = included p (x,x) i

  let compl p i =
    let x,y = i in
    let ans = (List.map (fun t -> (BPBot, t)) (not_sup  p x))@(List.map (fun t -> (t, BPTop)) (not_inf p y))
     in
    if !debug_compl then
      debug (Printf.sprintf "Int.compl: %s is %s." (to_string p i) (String.concat " , " (List.map (to_string p) ans)));
    ans

  let realize (_:'a prog) (_:t) = assert false
  
  let redundancy (x1,y1) (x2,y2) = (BPos.redundancy x1 x2) && (BPos.redundancy y1 y2)

end

module Region =
struct
  type t = Int.t list

  let create () = []

  let everything p = [Int.everything p]

  (** Add an interval in a region. *)
  let add p i a =
    let i_redundant = ref false in
    let a =
      List.filter
        (fun j ->
           let ninc_ji = not (Int.included p j i) in
           if (Int.included p i j && ninc_ji) then i_redundant := true;
           ninc_ji
        ) a
    in
    if !i_redundant then a else (i::a)

  let forget i a =
    let i_redundant = ref false in
    let a =
      List.filter
        (fun j ->
           if Int.redundancy i j then i_redundant := true;
           true
        ) a
    in
    if !i_redundant then a else (i::a)
  

  let join p a b = List.fold_left (fun ans i -> add p i ans) b a

  let forget a = List.fold_left (fun ans i -> forget i ans) [] a

  (* let make a = join a (create ()) *)

  let to_string p a =
    List.fold_left
      (fun s i ->
         Printf.sprintf "%s  %s\n" s (Int.to_string p i)
      ) "" (forget a)

  let to_string_simple a =
    List.fold_left
      (fun s i ->
         Printf.sprintf "%s%s\n" s (Int.to_string_simple i)
      ) "" a

  (* BPositions are intervals and [a,b]->[c,d] means c in [a,b]. *)
  let to_dot p a =
    let ans = ref [] in
    List.iter_ctxt
      (fun h ((t1,_) as j) t ->
         let src = List.filter (fun i -> Int.belongs p t1 i && t1 <> (fst i)) (h@t) in
         ans := (List.map (fun i -> i,j) src) @ !ans
      ) a;
    let ans =
      List.fold_left
        (fun s (i,j) ->
           Printf.sprintf "%s\n    \"%s\" -> \"%s\";" s (Int.to_string p i) (Int.to_string p j)
        ) "" !ans
    in
    Printf.sprintf "digraph region {%s\n}\n" ans

  let meet p a b =
    List.fold_left
      (fun c i ->
         join p (List.map (Int.meet p i) b) c
      ) (create ()) a

  let compl p a =
    let a = List.map (Int.compl p) a in
    List.fold_left (fun ans a -> meet p a ans) (everything p) a

  let normalize p a = compl p (compl p a)

  let difference p a b = meet p a (compl p b)

  let nondegenerated a = a

  let difference p a b =
    let ans = difference p a b in
    if !debug_difference then
      debug (Printf.sprintf "Region.difference:\n%sminus\n%sis\n%s" (to_string_simple a) (to_string_simple b) (to_string_simple ans));
    ans

  let deadlocks p a =
    let ans = ref [] in
    List.iter_ctxt
      (fun b (_,x) c ->
         if not (List.exists (Int.belongs p x) (b@c)) then
           ans := x :: !ans
      ) a;
    !ans

  let ginsu (_:t) = assert false
end

module Flow_graph =
struct
  type 'a edge =
    {
      mutable source : 'a vertex;
      target : 'a vertex;
      path : 'a prog;
    }
  and 'a vertex =
    {
      pos : BPos.t;
      succ : 'a edge list;
      mutable pred : 'a edge list;
    }

  type 'a t = 'a vertex

  (* TODO: we suppose that we don't have intricated loops. *)
  let of_region prog ?(no_squares=false) ?(diagonals=false) a =
    (*
      let a = (Region.while_regions prog)@a in
      Printf.printf "* while regions:\n%s\n\n%!" (Region.to_string prog (Region.while_regions prog));
    *)
    let g = Region.ginsu a in
    (* Printf.printf "* gigiginsu:\n%s\n\n%!" (Region.to_string prog g); *)
    let leq i (t, _) = Int.belongs prog t i && t <> fst i in
    (* Transitions removed thanks to homotopy. *)
    let removed = ref [] in
    (* Terminal states are added separately. *)
    let terminal = ref [] in
    (* Compute successor intervals. *)
    let succ =
      List.map_ctxt
        (fun g1 i g2 ->
           let isucc = List.filter (leq i) (g1@g2) in
           (* Remove transitive edges. *)
           let isucc =
             List.filter_ctxt
               (fun s1 j s2 ->
                  let dominated = List.filter (fun k -> leq k j) (s1@s2) in
                  let n = List.length dominated in
                  (* There is a commutative square so we remove one transition. *)
                  if n >= 2 then
                    removed := (List.hd dominated, j) :: !removed;
                  (* Was not marked for deletion. *)
                  (not no_squares || not (List.mem (i, j) !removed))
                  &&
                  (* Isn't a transitive edge. *)
                  (diagonals || n = 0)
               ) isucc
           in
           if isucc = [] then
             (* Add terminal positions. *)
             let t = snd i in
             terminal := ((t,t),[]) :: !terminal;
             i, [t,t]
           else
             i, isucc
        ) g
    in
    let succ = !terminal @ succ in
    (* Printf.printf "* ginsuted:\n%s\n\n%!" (Region.to_string prog (List.map fst succ)); *)
    (* Find the initial position. *)
    let init = List.may_map (fun (t1,t2) -> if t1 = BPos.bot prog then Some t2 else None) g in
    let init = List.fold_left (fun m t -> if BPos.le t m then t else m) (List.hd init) (List.tl init) in
    let init = BPos.bot prog, init in
    (* let init = List.find (fun (t,_) -> t = BPos.bot) g in *)
    let vertices = ref [] in
    let rec vertex i =
      (* Printf.printf "V: %s\n%!" (Int.to_string prog i); *)
      try
        List.assoc i !vertices
      with
      | Not_found ->
        let v =
          {
            pos = fst i;
            succ = List.map (edge i) (List.assoc i succ);
            pred = []; (* Fake pred *)
          }
        in
        vertices := (i,v) :: !vertices;
        v
    and edge i j =
      (* Printf.printf "E: %s        %s\n%!" (Int.to_string prog i) (Int.to_string prog j); *)
      {
        source = vertex j; (* Fake source *)
        target = vertex j;
        path = Int.realize prog (Int.make (fst i, fst j));
      }
    in
    let ans = vertex init in
    (* Fill in pred and source *)
    (
      let visited = ref [] in
      let rec aux v =
        if not (List.mem v !visited) then
          (
            visited := v :: !visited;
            List.iter
              (fun e ->
                 e.source <- v;
                 e.target.pred <- e :: e.target.pred;
                 aux e.target
              ) v.succ
          )
      in
      aux ans
    );
    ans


  let iter_breadth f g =
    let visited = ref [] in
    let todo = ref g.succ in
    while !todo <> [] do
      (* Find a transition such that all the predecessors of the source have
       * been visited. *)
      let e, td =
        List.find_and_remove
          (fun e ->
             List.for_all (fun e -> List.mem e !visited) e.source.pred
          ) !todo
      in
      todo := td;
      visited := e :: !visited;
      List.iter (fun e -> if not (List.mem e !visited || List.mem e !todo) then todo := e :: !todo) e.target.succ;
      f e.source.pos e.path e.target.pos
    done

  let to_dot p g =
    let ans = ref "" in
    iter_breadth (*iter_depth*) (fun t1 _ t2 -> ans := Printf.sprintf "%s\n    \"%s\" -> \"%s\";" !ans (BPos.to_string p t1) (BPos.to_string p t2)) g;
    Printf.sprintf "digraph region {%s\n}\n" !ans
end
