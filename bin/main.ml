open Base
open Sexplib.Std
open Mini_dialyzer
open Mini_dialyzer.Types

let print_sexp sexp =
  Caml.Printf.printf "%s\n" (Sexplib.Sexp.to_string_hum sexp)

let run e ini =
  let (t, c) = type_judge ini e in
  let () = print_sexp (sexp_of_type_expr t) in
  let () = print_sexp (sexp_of_type_constraint c) in
  let sol = solve c in
  let () = print_sexp (Solution.sexp_of_t sol) in
  match Solution.subst sol t with
  | Some e' -> print_sexp (sexp_of_type_expr e')
  | None -> Caml.Printf.printf "bottom\n"

let () =
  (* let const = fun (x, y) -> x end in const(a, b) *)
  let e1 =
    Let ("const",
         Abs (FFunc (["x"; "y"], (Var "x"))),
         App (Var "const",
              [Var "a"; Var "b"])) in
  let ini1 = Map.of_alist_reduce
               ~f:(fun _ r -> r)
               (module String)
               [ "a", TyVar "tyvar_a"
               ; "b", TyVar "tyvar_b"
               ]
  in
  let () = run e1 ini1 in

  let e2 =
    Abs (FFunc (["x"; "y"],
                App (Var "plus",
                     [Var "x"; Var "y"]))) in
  let ini2 = Map.of_alist_reduce
               ~f:(fun _ r -> r)
               (module String)
               [ "plus", TyFunc ([ TyConcrete CTInteger
                                 ; TyConcrete CTInteger
                                 ], (TyConcrete CTInteger))
               ] in
  let () = run e2 ini2 in
  ()
