open S_exp

exception Stuck of s_exp

let () =
  Printexc.register_printer (function
    | Stuck e ->
        Some (Printf.sprintf "Stuck[%s]" (string_of_s_exp e))
    | _ ->
        None)
