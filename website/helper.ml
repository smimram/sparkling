module String = struct
  include String

  let rfind_from str pos sub =
    let sublen = length sub
    and len = length str in
    if pos + 1 < 0 || pos + 1 > len then invalid_arg "String.rfind_from";
    (* 0 <= pos + 1 <= length str *)
    if sublen = 0 then pos + 1 else
      (* length sub > 0 *)
      (* (pos + 1 - sublen) <= length str - length sub < length str *)
      let rec find ~str ~sub i =
        if i < 0 then raise Not_found
        else
          (* 0 <= i <= length str - length sub < length str *)
          let rec loop ~str ~sub i j =
            if j = sublen then i
            else
              (* 0 <= j < length sub *)
              (* ==> 0 <= i + j < length str *)
            if unsafe_get str (i + j) <> unsafe_get sub j
            then find ~str ~sub (i - 1)
            else loop ~str ~sub i (j + 1)
          in loop ~str ~sub i 0
      in find ~str ~sub (pos - sublen + 1)

  let split_on_string_comp sep str =
    if str = "" then [""]
    else if sep = "" then invalid_arg "String.split_on_string: empty sep not allowed"
    else
      (* str is non empty *)
      let seplen = String.length sep in
      let rec aux acc ofs =
        if ofs >= 0 then (
          match
            try Some (rfind_from str ofs sep)
            with Not_found -> None
          with
          | Some idx -> (* sep found *)
            let end_of_sep = idx + seplen - 1 in
            if end_of_sep = ofs (* sep at end of str *)
            then aux (""::acc) (idx - 1)
            else
              let token = sub str (end_of_sep + 1) (ofs - end_of_sep) in
              aux (token::acc) (idx - 1)
          | None -> (* sep NOT found *)
            (sub str 0 (ofs + 1))::acc
        )
        else
          (* Negative ofs: the last sep started at the beginning of str *)
          ""::acc
      in
      aux [] (length str - 1 )

  let split_on_string sep str = split_on_string_comp sep str
end
