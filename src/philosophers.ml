let oplate = ref false
let philo = ref 0

let () =
  Arg.parse
    [
      "-oplate", Arg.Set oplate, "Generate in hydroml format."
    ]
    (fun s -> philo := int_of_string s)
    "RTFM";
  let philo = !philo in
    if !oplate then
      (
        Printf.printf "#mtx";
        for i = 0 to philo - 1 do
          Printf.printf " a%d" i
        done;
        Printf.printf "\n%!";
        for i = 0 to philo - 1 do
          Printf.printf "p%d = P(a%d).P(a%d).V(a%d).V(a%d)\n%!" i i ((i+1) mod philo) i ((i+1) mod philo)
        done;
        Printf.printf "init:\n";
        for i = 0 to philo - 1 do
          Printf.printf "p%d " i
        done;
        Printf.printf "\n%!"
      )
    else
      (
        Printf.printf "void main()\n{\n";
        for i = 0 to philo - 1 do
          Printf.printf "mutex m%d;\n" i
        done;
        Printf.printf "\n";
        for i = 0 to philo - 1 do
          if i <> 0 then Printf.printf "|";
          Printf.printf "{\nlock(m%d);\nlock(m%d);\nunlock(m%d);\nunlock(m%d);\n}" i ((i+1) mod philo) i ((i+1) mod philo);
          if i = philo - 1 then Printf.printf ";";
          Printf.printf "\n"
        done;
        Printf.printf "}\n";
      )
