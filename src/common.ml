(** General-purpose utility functions. *)

(** The identity function .*)
let id x = x

let pair x y = x, y

let diag f (x,y) = (f x, f y)

let get_some = function
  | Some x -> x
  | None -> assert false

let fst3 (x,_,_) = x
let snd3 (_,y,_) = y
let thd3 (_,_,z) = z

(** Composition for the option monad. *)
let option_comp f v =
  match v with
  | Some v -> Some (f v)
  | None -> None

(** {2 Operations on lists.} *)
module List =
struct
  include List

  (** Last element of a list. *)
  let rec last = function
    | [x] -> x
    | _::t -> last t
    | [] -> raise Not_found

  (** Make a list with [n] elements. *)
  let rec make n x =
    if n = 0 then
      []
    else
      x::(make (n-1) x)

  (** Similar to [Array.init] but for lists. *)
  let init n f =
    let rec aux i =
      if i = n then [] else (f i)::(aux (i+1))
    in
    aux 0

  (** Map a function to a list and keep all elements which are not [None]. *)
  let rec may_map f = function
    | x::t ->
      (
        match f x with
        | Some y -> y::(may_map f t)
        | None -> may_map f t
      )
    | [] -> []

  (** Map a function to a list, keeping track of the index of the current element. *)
  let mapi f l =
    let rec aux n = function
      | h::t -> (f n h)::(aux (n+1) t)
      | [] -> []
    in
    aux 0 l

  let mapi2 f l1 l2 =
    let rec aux n = function
      | h1::t1, h2::t2 -> (f n h1 h2)::(aux (n+1) (t1, t2))
      | [], [] -> []
      | _ -> assert false
    in
    aux 0 (l1, l2)

  (** Add an element to a list if it is not already present. *)
  let add_uniq x l =
    if mem x l then l else x::l

  (** Remove duplicate elements from a list. *)
  let uniq l =
    List.fold_left (fun l x -> add_uniq x l) [] l

  (** Same as [List.flatten] but removes duplicate elements. *)
  let rec flatten_uniq = function
    | h::t ->
      let t = flatten_uniq t in
      fold_left (fun t x -> add_uniq x t) t h
    | [] -> []

  (** Map a function on a list. For each element the function is given as argument
    * the prefix of the list before the element, the element, and the suffix of
    * the list after the element. *)
  let map_ctxt f l =
    let rec aux b = function
      | [] -> []
      | h::t -> (f b h t)::(aux (b@[h]) t)
    in
    aux [] l

  let iter_ctxt f l =
    let rec aux b = function
      | [] -> ()
      | h::t -> f b h t; aux (b@[h]) t
    in
    aux [] l

  let filter_ctxt f l =
    let rec aux b = function
      | [] -> []
      | h::t ->
        if f b h t then
          h::(aux (b@[h]) t)
        else
          aux (b@[h]) t
    in
    aux [] l

  let find_and_remove f l =
    let ans = ref None in
    iter_ctxt
      (fun b h t ->
         if !ans = None && f h then
           ans := Some (h, b@t);
      ) l;
    match !ans with
    | None -> raise Not_found
    | Some ans -> ans

  let rec iter_tail f l =
    match l with
    | [] -> ()
    | h::t -> f h t; iter_tail f t

  let iteri f l =
    let rec aux n = function
      | [] -> ()
      | h::t -> (f n h); aux (n+1) t
    in
    aux 0 l

  let iteri2 f l1 l2 =
    let rec aux n = function
      | [], [] -> ()
      | h1::t1, h2::t2 -> (f n h1 h2); aux (n+1) (t1,t2)
      | _ -> assert false
    in
    aux 0 (l1,l2)

  let iter_pairs2 f l1 l2 =
    iter
      (fun x ->
         iter
           (fun y ->
              f x y
           ) l2
      ) l1

  let map_pairs2 f l1 l2 =
    concat
      (
        map
          (fun x ->
             map
               (fun y ->
                  f x y
               ) l2
          ) l1
      )

  let may_map_pairs2 f l1 l2 =
    concat
      (
        map
          (fun x ->
             may_map
               (fun y ->
                  f x y
               ) l2
          ) l1
      )

      (*
  (** Split a list in two parts, given the length of the first part. *)
  let rec split n l =
    if n = 0 then [], l else
      match l with
        | h::t ->
            let l1, l2 = split (n-1) t in
              h::l1, l2
        | [] -> assert false
      *)

  (** Drop [n] elements in a list. *)
  let rec drop n l =
    if n = 0 then l else
      match l with
      | _::t -> drop (n-1) t
      | [] -> assert false

  (** Finds the longest common suffix of two lists (wrt physical equality). *)
  let common_suffix l1 l2 =
    (* TODO: compute lengths only once *)
    let l1, l2 =
      if length l1 >= length l2 then
        l1, l2
      else
        l2, l1
    in
    let l1 = drop (length l1 - length l2) l1 in
    let rec aux l1 l2 =
      if l1 == l2 then
        l1
      else
        aux (tl l1) (tl l2)
    in
    aux l1 l2

  let rec ith l n =
    match l with
    | h::t -> if n = 0 then h else ith t (n-1)
    | [] -> raise Not_found

  let nth = ith

  (** Convert a list of pairs into a pair of lists. *)
  let rec unpair = function
    | (x,y)::t ->
      let t1,t2 = unpair t in
      x::t1, y::t2
    | [] -> [], []

  (** Same as [List.for_all2] but works on the longuest prefix of the two lists.
    * It does not necessarily looks at every element. *)
  let rec for_all2_prefix f = function
    | [], _ -> ()
    | _, [] -> ()
    | x1::t1, x2::t2 ->
      if f x1 x2 then
        for_all2_prefix f (t1,t2)
      else
        raise Exit

  let for_all2_prefix f l1 l2 =
    try
      for_all2_prefix f (l1,l2);
      true
    with
    | Exit -> false

  let rec for_all3 f l1 l2 l3 =
    match l1,l2,l3 with
    | x1::t1, x2::t2, x3::t3 ->
      (f x1 x2 x3) && (for_all3 f t1 t2 t3)
    | [], [], [] -> true
    | _ -> assert false

  let rec map3 f l1 l2 l3 =
    match l1,l2,l3 with
    | x1::t1,x2::t2,x3::t3 ->
      (f x1 x2 x3)::(map3 f t1 t2 t3)
    | [],[],[] ->
      []
    | _ -> assert false

  let rec map4 f l1 l2 l3 l4 =
    match l1,l2,l3,l4 with
    | x1::t1,x2::t2,x3::t3,x4::t4 ->
      (f x1 x2 x3 x4)::(map4 f t1 t2 t3 t4)
    | [],[],[],[] ->
      []
    | _ -> assert false

  let rec map5 f l1 l2 l3 l4 l5 =
    match l1,l2,l3,l4,l5 with
    | x1::t1,x2::t2,x3::t3,x4::t4,x5::t5 ->
      (f x1 x2 x3 x4 x5)::(map5 f t1 t2 t3 t4 t5)
    | [],[],[],[],[] ->
      []
    | _ -> assert false

  let assoc_all x l =
    let ans = ref [] in
    iter
      (fun (y,v) ->
         if y = x then ans := v :: !ans
      ) l;
    rev !ans

  (** Maps a function on the elements of a list. If on of the results in [None]
    * then the global result is [None]. *)
  let rec for_all_map f = function
    | x::t ->
      (
        match f x with
        | Some y ->
          (
            match for_all_map f t with
            | Some l -> Some (y::l)
            | None -> None
          )
        | None -> None
      )
    | [] -> Some []

  (** Convert a list of sums to a sum of lists, ie [[a;b];[c;d]] becomes
    * [[a;c];[a;d];[b;c];[b;d]]. *)
  let rec unsum = function
    | [] -> [[]]
    | h::t ->
      let t = unsum t in
      let l = map (fun x -> (map (fun l -> x::l) t)) h in
      flatten l

  (** Given a list, returns the list of lists where all element are the default
    * value excepting one which is the corresponding value in the original list.
    **)
  let rec one_in d = function
    | x::t ->
      (x::(make (length t) d))::(map (fun l -> d::l) (one_in d t))
    | [] -> []
end

(** {2 Operations on arrays.} *)
module Array =
struct
  include Array

  (** Find an element in an array. *)
  let find f a =
    let ans = ref None in
    try
      for i = 0 to Array.length a - 1 do
        if f a.(i) then
          (
            ans := Some i;
            raise Exit
          )
      done;
      raise Not_found
    with
    | Exit ->
      match !ans with
      | Some i -> i
      | None -> raise Not_found
end
