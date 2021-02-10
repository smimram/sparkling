open Common

let debug s = Printf.printf "[DD] %s\n%!" s
(* let error s = Printf.printf "[EE] %s\n%!" s *)
(* let debug_le = false *)
(* let debug_int = true *)
let debug_meet = ref false
let debug_meet_full = ref false
(* let debug_belongs = ref false *)
(* let debug_inf = ref false *)
(* let debug_supinf = ref false *)
let debug_compl = ref false
let debug_compl_full = ref false
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
    | _, PBot -> "."
    | _, PTop -> "!"
    | Seq l, PSeq (n, t) ->
      (* TODO: enhance this *)
      let ans = ref "" in
      for _ = 0 to n - 1 do ans := !ans ^ "X;" done;
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
    | While (_, p), PWhile t -> "W" ^ to_string p t
    | _, PWhile _ -> assert false

  let rec to_string_simple t =
    let to_string = function
      | PBot | PTop | PIf _ as t -> to_string_simple t
      | t -> "(" ^ to_string_simple t ^ ")"
    in
    match t with
    | PBot -> "."
    | PTop -> "!"
    | PSeq (n, t) ->
      if n = max_int then "...;" ^ (to_string t) else
        let ans = ref "" in
        for _ = 0 to n - 1 do ans := !ans ^ "X;" done;
        ans := !ans ^ to_string t;
        !ans ^ ";"
    | PPar l ->
      String.concat "|" (List.map to_string l)
    | PIf (b,t) ->
      if b then to_string t ^ "+_"
      else "_+" ^ to_string t
    | PWhile t -> "W(" ^ to_string_simple t ^ ")"

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

module Int = struct
  open Pos

  type t = Pos.t * Pos.t

  let everything p = bot p, top p

  let to_string p (t1,t2) = Pos.to_string p t1 ^ " -- " ^ Pos.to_string p t2

  let to_string_simple (t1,t2) = Pos.to_string_simple t1 ^ " -- " ^ Pos.to_string_simple t2

  let valid (t1,t2) = le t1 t2

  let make i =
    let valid = valid i in
    if not valid then debug (Printf.sprintf "Int.make: invalid interval %s." (to_string_simple i));
    assert valid;
    i

  let bounds = id

  let rec meet p ((t1,t2) as i) ((t1',t2') as i') =
    let meet p i j = meet p i j in
    if !debug_meet_full then
      debug (Printf.sprintf "Int.meet: %s /\\ %s." (to_string p i) (to_string p i'));
    let meet p i j =
      let m = meet p i j in
      if !debug_meet_full then
        (
          debug (Printf.sprintf "Int.meet: %s /\\ %s = %s." (to_string p i) (to_string p j) (String.concat " , " (List.map (to_string p) m)));
          List.iter (fun i -> assert (valid i)) m
        );
      m
    in
    match p,t1,t2,t1',t2' with
    (* bot and top *)
    | _,PBot,PBot,PBot,_ -> [t1,t2]
    | _,PBot,PBot,_,_ -> []
    | _,PTop,PTop,_,PTop -> [t1,t2]
    | _,PTop,PTop,_,_ -> []
    | _,PBot,_,PBot,PBot -> [t1',t2']
    | _,_,_,PBot,PBot -> []
    |_, _,PTop,PTop,PTop -> [t1',t2']
    | _,_,_,PTop,PTop -> []
    | _,PTop,PBot,_,_ -> []
    | _,t1,t2,PBot,PTop -> [t1,t2]
    | _,PBot,PTop,t1,t2 -> [t1,t2]
    (* sequences *)
    | Seq l,PBot,PSeq(n2,t2),PBot,PSeq(n2',t2') ->
      if n2 < n2' then
        [PBot,PSeq(n2,t2)]
      else if n2 > n2' then
        [PBot,PSeq(n2',t2')]
      else
        let p = List.nth l n2 in
        List.map (fun (_,t) -> PBot,PSeq(n2,t)) (meet p (PBot,t2) (PBot,t2'))
    | Seq l,PSeq(n1,t1),PTop,PSeq(n1',t1'),PTop ->
      if n1 < n1' then
        [PSeq(n1',t1'),PTop]
      else if n1 > n1' then
        [PSeq(n1,t1),PTop]
      else
        let p = List.nth l n1 in
        List.map (fun (t,_) -> PSeq(n1,t),PTop) (meet p (t1,PTop) (t1',PTop))
    | p,PBot,_,PSeq (n,_),_ ->
      meet p (PSeq (n,PBot),t2) (t1',t2')
    | p,PSeq (n,_),_,PBot,_ ->
      meet p (t1,t2) (PSeq (n,PBot),t2')
    | Seq _,_,PTop,_,PSeq (n,_) ->
      meet p (t1,PSeq (n,PTop)) (t1',t2')
    | Seq _,_,PSeq (n,_),_,PTop ->
      meet p (t1,t2) (t1',PSeq (n,PTop))
    | Seq l,PSeq(n1,t1),PSeq(n2,t2),PSeq(n1',t1'),PSeq(n2',t2') ->
      if n2 < n1' || n1 > n2' then
        []
      else if n1 = n1' && n2 = n2' then
        if n1 = n2 then
          let p = List.nth l n1 in
          let m = meet p (t1,t2) (t1',t2') in
          List.map (fun (t1,t2) -> PSeq (n1,t1), PSeq (n1,t2)) m
        else
          let m1 = meet (List.nth l n1) (t1,PTop) (t1',PTop) in
          let m2 = meet (List.nth l n2) (PBot,t2) (PBot,t2') in
          List.map_pairs2 (fun (t1,t1') (t2',t2) -> assert (t1' = PTop && t2' = PBot); PSeq (n1,t1), PSeq (n2,t2)) m1 m2
      else
        let t1,t1' =
          if n1 < n1' then
            PBot, PSeq(n1',t1')
          else if n1 > n1' then
            PSeq(n1,t1), PBot
          else
            PSeq(n1,t1), PSeq(n1',t1')
        in
        let t2,t2' =
          if n2 < n2' then
            PSeq(n2,t2), PTop
          else if n2 > n2' then
            PTop, PSeq(n2',t2')
          else
            PSeq(n2,t2), PSeq(n2',t2')
        in
        meet p (t1,t2) (t1',t2')
    (* parallels *)
    | Par l,PBot,_,PBot,_ ->
      let bot = PPar (List.map (fun _ -> PBot) l) in
      let m = meet p (bot,t2) (bot,t2') in
      List.map (fun (t1,t2) -> assert (t1 = bot); PBot, t2) m
    | Par l,_,PTop,_,PTop ->
      let top = PPar (List.map (fun _ -> PTop) l) in
      let m = meet p (t1,top) (t1',top) in
      List.map (fun (t1,t2) -> assert (t2 = top); t1, PTop) m
    | Par _,PBot,_,PPar tt1',_ ->
      let bot = PPar (List.map (fun _ -> PBot) tt1') in
      meet p (bot,t2) (t1',t2')
    | Par _,PPar tt1,_,PBot,_ ->
      let bot = PPar (List.map (fun _ -> PBot) tt1) in
      meet p (t1,t2) (bot,t2')
    | Par _,_,PPar tt2,_,PTop ->
      let top = PPar (List.map (fun _ -> PTop) tt2) in
      meet p (t1,t2) (t1',top)
    | Par _,_,PTop,_,PPar tt2' ->
      let top = PPar (List.map (fun _ -> PTop) tt2') in
      meet p (t1,top) (t1',t2')
    | Par l,PPar tt1,PPar tt2,PPar tt1',PPar tt2' ->
      let ans = List.map5 (fun p t1 t2 t1' t2' -> meet p (t1,t2) (t1',t2')) l tt1 tt2 tt1' tt2' in
      let ans = List.unsum ans in
      List.map (fun tt -> PPar (List.map fst tt), PPar (List.map snd tt)) ans
    (* if *)
    | If _, PBot, PIf (b1,_), PBot, PIf (b2, _) ->
      if b1 <> b2 then
        [PBot,PBot]
      else
        let m = meet p (PIf(b1,PBot),t2) (PIf(b2,PBot),t2') in
        List.map (fun (t1,t2) -> assert (t1 = PIf(b1,PBot)); PBot,t2) m
    | If _, PBot, PIf (b, _), _, _ ->
      meet p (PIf(b,PBot),t2) (t1',t2')
    | If _, _, _, PBot, PIf (b, _) ->
      meet p (t1,t2) (PIf(b,PBot),t2')
    | If _, PIf (b1,_), PTop, PIf (b2,_), PTop ->
      if b1 <> b2 then
        [PTop,PTop]
      else
        let m = meet p (t1,PIf(b1,PTop)) (t1',PIf(b2,PTop)) in
        List.map (fun (t1,t2) -> assert (t2 = PIf(b1,PTop)); t1,PTop) m
    | If _, PIf (b,_), PTop, _, _ ->
      meet p (t1,PIf(b,PTop)) (t1',t2')
    | If _, _, _, PIf (b,_), PTop ->
      meet p (t1,t2) (t1',PIf(b,PTop))
    | If (_,p1,p2), PIf (b1,t1), PIf (b2,t2), PIf (b1',t1'), PIf (b2', t2') ->
      assert (b1 = b2 && b1' = b2');
      if b1 <> b2 then
        []
      else
        let p = if b1 then p1 else p2 in
        let k t = PIf (b1, t) in
        let m = meet p (t1,t2) (t1',t2') in
        List.map (diag k) m
    (* while and bot *)
    | While _, PBot, _, PBot, _ ->
      let m = meet p (PWhile PBot, t2) (PWhile PBot, t2') in
      List.map (fun (t1,t2) -> assert (t1 = PWhile PBot); PBot, t2) m
    | While _, PBot, _, _, _ ->
      meet p (PWhile PBot, t2) (t1', t2')
    | While _, _, _, PBot, _ ->
      meet p (t1,t2) (PWhile PBot, t2')
    (* while and top *)
    | While _, PWhile _, PTop, PWhile _, PTop ->
      let m = meet p (t1, PWhile PTop) (t1', PWhile PTop) in
      List.map (fun (t1,t2) -> assert (t2 = PWhile PTop); t1, PTop) m
    | While _, PWhile _, PTop, PWhile _, PWhile _ ->
      meet p (t1,PWhile PTop) (t1',t2')
    | While _, PWhile _, PWhile _, PWhile _, PTop ->
      meet p (t1,t2) (t1',PWhile PTop)
    (* while and while *)
    | While (_,p), PWhile t1, PWhile t2, PWhile t1', PWhile t2' ->
      let le' = le t1' t2' in
      let le = le t1 t2 in
      let k t = PWhile t in
      let k = diag k in
      (
        match le,le' with
        | true, true ->
          let m = meet p (t1,t2) (t1',t2') in
          List.map k m
        | true, false ->
          let m1 = meet p (t1,t2) (t2',PTop) in
          let m2 = meet p (t1,t2) (PBot,t1') in
          List.map k (m1@m2)
        | false, true ->
          let m1 = meet p (t2,PTop) (t1',t2') in
          let m2 = meet p (PBot,t1) (t1',t2') in
          List.map k (m1@m2)
        | false, false ->
          let m1 = meet p (t1,PTop) (t1',PTop) in
          let m2 = meet p (PBot,t2) (PBot,t2') in
          List.map_pairs2 (fun (t1,t2) (t1',t2') -> assert (t2 = PTop && t1' = PBot); k (t1, t2')) m1 m2
      )
    | _ -> assert false

  let meet p i j =
    let m = meet p i j in
    if !debug_meet then debug (Printf.sprintf "Int.meet: %s /\\ %s = %s." (to_string p i) (to_string p j) (String.concat " , " (List.map (to_string p) m)));
    m

  let included p i j = meet p i j = [i]

  let belongs p x i = included p (x,x) i

  let rec compl p i =
    let t1,t2 = i in
    let compl p i =
      if !debug_compl_full then Printf.printf "C: %s\n%!" (to_string p i);
      let (b,m,e) as ans = compl p i in
      (* TODO: show b and e too *)
      if !debug_compl_full then
        (
          let b = List.map (fun t -> PBot, t) b in
          let e = List.map (fun t -> t, PTop) e in
          Printf.printf "C: %s is %s\n%!" (to_string p i) (String.concat " , " (List.map (to_string p) (b@m@e)));
        );
      ans
    in
    let bme_map k (b,m,e) =
      let b = List.map k b in
      let m = List.map (diag k) m in
      let e = List.map k e in
      b,m,e
    in
    match p,t1,t2 with
    | _,PBot,PTop -> [PBot],[],[PTop]
    | _,PBot,PBot -> [PBot],[],[PBot]
    | _,PTop,PTop -> [PTop],[],[PTop]
    | Seq _,PBot,PSeq (n2,t2) ->
      let b,m,e = compl p (PSeq (n2,PBot),PSeq (n2,t2)) in
      let b = List.map (fun t -> if t = PSeq (0,PBot) then PBot else t) b in
      b,m,e
    | Seq l,PSeq (n1,t1),PTop ->
      let b,m,e = compl p (PSeq (n1,t1),PSeq (n1,PTop)) in
      let e = List.map (fun t -> if t = PSeq (List.length l - 1,PTop) then PTop else t) e in
      b,m,e
    | Seq l,PSeq (n1,t1),PSeq (n2,t2) ->
      if n1 = n2 then
        let p = List.nth l n1 in
        let k t = PSeq (n1,t) in
        bme_map k (compl p (t1,t2))
      else
        (
          assert (n1 < n2);
          (* [PSeq (n1,t1)],[],[PSeq (n2,t2)] *)
          let b,_,_ = compl p (PSeq (n1,t1),PSeq (n1,PTop)) in
          let _,_,e = compl p (PSeq (n2,PBot),PSeq (n2,t2)) in
          b,[],e
        )
    (* par *)
    | Par _,PBot,PPar tt2 ->
      let bot = PPar (List.map (fun _ -> PBot) tt2) in
      let b,m,e = compl p (bot, PPar tt2) in
      let b = List.map (fun t -> if t = bot then PBot else t) b in
      b,m,e
    | Par _,PPar tt1,PTop ->
      let top = PPar (List.map (fun _ -> PTop) tt1) in
      let b,m,e = compl p (PPar tt1, top) in
      let e = List.map (fun t -> if t = top then PTop else t) e in
      b,m,e
    | Par l,PPar tt1,PPar tt2 ->
      let bme = List.map3 (fun p t1 t2 -> compl p (t1,t2)) l tt1 tt2 in
      let b = List.map fst3 bme in
      let m = List.map snd3 bme in
      let e = List.map thd3 bme in
      let choose_one def l =
        let ans = ref [] in
        let l = Array.of_list l in
        let n = Array.length l in
        for i = 0 to n - 1 do
          List.iter
            (fun t ->
               let c = List.init n (fun j -> if j = i then t else def) in
               ans := c :: !ans
            ) l.(i)
        done;
        !ans
      in
      let b = choose_one PTop b in
      let e = choose_one PBot e in
      let m = choose_one (PBot,PTop) m in
      let k tt = PPar tt in
      let b = List.map k b in
      let e = List.map k e in
      let m =
        List.map
          (fun tt ->
             let tt1, tt2 = List.split tt in
             k tt1, k tt2) m
      in
      b,m,e
    (* conditional branching *)
    | If _, PBot, PIf (bool,_) ->
      let b,m,e = compl p (PIf(bool,PBot),t2) in
      let b = List.map (fun t -> if t = PIf(bool,PBot) then PBot else t) b in
      b,m,e
    | If _, PIf (bool,_), PTop ->
      let b,m,e = compl p (t1,PIf(bool,PTop)) in
      let e = List.map (fun t -> if t = PIf(bool,PTop) then PTop else t) e in
      b,m,e
    | If (_,p1,p2), PIf (b1,t1), PIf (b2,t2) ->
      assert (b1 = b2);
      let p = if b1 then p1 else p2 in
      let k t = PIf (b1, t) in
      let b,m,e = bme_map k (compl p (t1,t2)) in
      (PIf(not b1,PTop))::b,m,(PIf(not b1,PBot))::e
    (* while *)
    | While _, PBot, PWhile _ ->
      let b,m,e = compl p (PWhile PBot, t2) in
      let b = List.map (fun t -> if t = PWhile PBot then PBot else t) b in
      b,m,e
    | While _, PWhile _, PTop ->
      let b,m,e = compl p (t1,PWhile PTop) in
      let e = List.map (fun t -> if t = PWhile PTop then PTop else t) e in
      b,m,e
    | While (_, pp), PWhile t1, PWhile t2 ->
      let k t = PWhile t in
      if le t1 t2 then
        let b,m,e = compl pp (t1,t2) in
        let b = List.map k b in
        let e = List.map k e in
        let m = List.map (diag k) m in
        let eb = List.map_pairs2 pair e b in
        b,eb@m,e
      else
        let b,m,_ = compl pp (t1,PTop) in
        let _,m',e' = compl pp (PBot,t2) in
        let b = List.map k b in
        let e' = List.map k e' in
        let eb = List.map_pairs2 pair e' b in
        [PWhile PBot],eb@m@m',[PWhile PBot]
    | _ -> assert false

  let compl p (i:t) =
    let b,m,e = compl p i in
    let b = List.map (fun t -> PBot, t) b in
    let e = List.map (fun t -> t, PTop) e in
    b@m@e

  let compl p i =
    if !debug_compl_full then
      debug (Printf.sprintf "Int.compl: %s." (to_string p i));
    let ans = compl p i in
    if !debug_compl then
      debug (Printf.sprintf "Int.compl: %s is %s." (to_string p i) (String.concat " , " (List.map (to_string p) ans)));
    ans

  let realize (_:'a prog) (_:t) = assert false

(*
  (** Checks whether an interval is degenerated, which means that it is thin or
    * that the interior of its geometrical realization is empty. *)
  let rec degenerated = function
    | PBot, t -> t = PBot
    | t, PTop -> t = PTop
    | PSeq (n1, t1), PSeq (n2, t2) -> n1 = n2 && degenerated (t1, t2)
    | PPar tt1, PPar tt2 -> List.exists2 (fun t1 t2 -> degenerated (t1, t2)) tt1 tt2
    | PIf (_, t1), PIf (_, t2) -> degenerated (t1, t2)
    | PWhile t1, PWhile t2 -> degenerated (t1, t2)

  (** Checks whether an interval is standard, ie not an interval looping around
    * a while. *)
  (* Notice that in the case of the par of two intervals both are either both
   * stnadard or non-standard (otherwise things don't really make sense), which
   * is implied by the fact that programs should be well-bracketed. *)
  let rec standard = function
    | PBot, _
    | _, PTop -> true
    | PSeq (n1,t1), PSeq (n2,t2) ->
        (n1 < n2) || (n1 = n2 && standard (t1,t2))
    | PPar tt1, PPar tt2 ->
        List.for_all2 (fun t1 t2 -> standard (t1,t2)) tt1 tt2
    | PIf (_,t1), PIf (_,t2) ->
        standard (t1,t2)
    | PWhile _, PWhile _ -> true

  let included p i j =
    meet p i j = [i]

  (* TODO *)
  let realize _ _ = Seq []
*)

  (*
  let compl (t1,t2) =
    if !debug_compl then
      debug (Printf.sprintf "Int.compl: %s." (to_string_simple (t1,t2)));
    let below =
      list_may_map
        (fun t ->
           if t <> bot then
             Some (make (bot, t))
           else
             None
        ) (supinf t1)
    in
    let above =
      list_may_map
        (fun t ->
           if t <> top then
             Some (make (t, top))
           else
             None
        ) (infsup t2)
    in
      below@above

  let compl i =
    let ans = compl i in
      (
        if !debug_compl then
          let ans = String.concat " , " (List.map to_string_simple ans) in
            debug (Printf.sprintf "Int.compl: %s  =  %s." (to_string_simple i) ans)
      );
      ans

  let realize p (t1,t2) = Pos.realize (Pos.prog_residual p t1) (Pos.residual t1 t2)

  let realize p i =
    if !debug_realize then
      debug (Printf.sprintf "Int.realize %s in %s." (to_string_simple i) (prog_to_string p));
    realize p i
  *)

  (*
  (** [difference i j] computes the points in [i] but not in [j]. *)
  let difference ((t1,t2) as i) ((t1',t2') as i') =
    if le t2' t1 || le t2 t1' then [i]
    else if le t1' t1 && le t2 t2' then []
    else if le t1' t1 && le t2' t2 then [make (t2',t2)]
    else if le t1 t1' && le t2 t2' then [make (t1,t1')]
    else if le t1 t1' && le t2' t2 then [make (t1,t1'); make (t2',t2)]
    else assert false
  *)
end

module Region =
struct
  type t = Int.t list

  let create () = []

  let everything p = [Int.everything p]

  (** Add an interval in a region. *)
  let add p i a =
    let i_included = ref false in
    let a =
      List.filter
        (fun j ->
           let ninc_ji = not (Int.included p j i) in
           if Int.included p i j && ninc_ji then i_included := true;
           ninc_ji
        ) a
    in
    if !i_included then a else (i::a)

  let join p a b = List.fold_left (fun ans i -> add p i ans) b a

  (* let make a = join a (create ()) *)

  let to_string p a =
    List.fold_left
      (fun s i ->
         Printf.sprintf "%s  %s\n" s (Int.to_string p i)
      ) "" a

  let to_string_simple a =
    List.fold_left
      (fun s i ->
         Printf.sprintf "%s%s\n" s (Int.to_string_simple i)
      ) "" a

  (* Positions are positions and arrows are intervals. *)
  (*
  let to_dot p a =
    let ans =
      List.fold_left
        (fun s (t1,t2) ->
           Printf.sprintf "%s\n    \"%s\" -> \"%s\";" s (Pos.to_string p t1) (Pos.to_string p t2)
        ) "" a
    in
    Printf.sprintf "digraph region {%s\n}\n" ans
  *)

  (* Positions are intervals and [a,b]->[c,d] means c in [a,b]. *)
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
         join p (List.flatten (List.map (Int.meet p i) b)) c
      ) (create ()) a

  let compl p a =
    let a = List.map (Int.compl p) a in
    List.fold_left (fun ans a -> meet p a ans) (everything p) a

  let normalize p a = compl p (compl p a)

  (* let boundary p a = meet p a (compl p a) *)

  (* let contains p a i = List.exists (Int.included p i) a *)

  let difference p a b = meet p a (compl p b)

  let nondegenerated a = a
(*
  let nondegenerated a =
    List.filter (fun i -> not (Int.degenerated i)) a
*)

  let difference p a b =
    let ans = difference p a b in
    if !debug_difference then
      debug (Printf.sprintf "Region.difference:\n%sminus\n%sis\n%s" (to_string_simple a) (to_string_simple b) (to_string_simple ans));
    ans

  (* TODO: normalize a? *)
  (* TODO: correct ?? *)
  (* let belongs p i a = List.exists (Int.included p i) a *)

  (* let included p a b = List.for_all (fun i -> belongs p i b) a *)

  (* TODO: better complexity?... *)
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
      pos : Pos.t;
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
                  (* There is a commutative square so we remove one
                   * transition. *)
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
    let init = List.may_map (fun (t1,t2) -> if t1 = Pos.bot prog then Some t2 else None) g in
    let init = List.fold_left (fun m t -> if Pos.le t m then t else m) (List.hd init) (List.tl init) in
    let init = Pos.bot prog, init in
    (* let init = List.find (fun (t,_) -> t = Pos.bot) g in *)
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

  (*
  let iter_depth f v =
    let visited = ref [] in
    let rec aux v =
      if not (List.mem v !visited) then
        (
          visited := v :: !visited;
          List.iter
            (fun e ->
               f v.pos e.path e.target.pos;
               aux e.target
            ) v.succ
        )
    in
    aux v
  *)

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
    iter_breadth (*iter_depth*) (fun t1 _ t2 -> ans := Printf.sprintf "%s\n    \"%s\" -> \"%s\";" !ans (Pos.to_string p t1) (Pos.to_string p t2)) g;
    Printf.sprintf "digraph region {%s\n}\n" !ans
end
