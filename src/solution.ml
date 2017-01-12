open Base
open Types

module Printf = Caml.Printf
module Pervasives = Caml.Pervasives (* to suppress ppx_compare warnings *)

type t =
  | Bottom
  | Mapping of type_expr Map.M(String).t
[@@deriving sexp, compare]

let equal sol1 sol2 = match sol1, sol2 with
  | Bottom, Bottom -> true
  | Mapping map1, Mapping map2 ->
     Map.equal [%compare.equal: type_expr] map1 map2
  | _, _ -> false

let empty = Map.empty (module String)
let is_bottom = function
  | Bottom -> true
  | _ -> false

let merge_all maps =
  let f ~key = function
    | `Left t -> Some t
    | `Right t -> Some t
    | `Both (_, t) -> Some t
  in
  List.fold_left maps ~init:empty ~f:(Map.merge ~f:f)

let rec init = function
  | Empty -> empty
  | Conj cs -> List.map cs ~f:init |> merge_all
  | Disj cs -> List.map cs ~f:init |> merge_all
  | Subset (e1, e2) ->
     let rec ee = function
       | TyVar var -> Map.singleton (module String) var (TyConcrete CTAny)
       | TyStruct es -> List.map es ~f:ee |> merge_all
       | TyFunc (es, e) -> List.map (e::es) ~f:ee |> merge_all
       | TyUnion (e1, e2) -> merge_all [ee e1; ee e2]
       | TyConstraint (e, c) -> merge_all [ee e; init c]
       | TyConcrete _ -> empty
     in
     merge_all [ee e1; ee e2]

(* TODO: simplify using lattice structure *)
let rec glb_conc ct1 ct2 = match ct1, ct2 with
  | CTAny, _ -> ct2
  | _, CTAny -> ct1
  (* integer *)
  | CTInteger, CTInteger -> CTInteger
  | CTInteger, CTVal (VInt n) -> CTVal (VInt n)
  | CTVal (VInt n), CTInteger -> CTVal (VInt n)
  | CTVal (VInt n1), CTVal (VInt n2) when n1 = n2 -> CTVal (VInt n1)
  (* atom *)
  | CTAtom, CTAtom -> CTAtom
  | CTAtom, CTVal (VAtom a) -> CTVal (VAtom a)
  | CTVal (VAtom a), CTAtom -> CTVal (VAtom a)
  | CTVal (VAtom a1), CTVal (VAtom a2) when String.equal a1 a2 -> CTVal (VAtom a1)
  | _, _ -> CTNone

(* greatest lower bound of types (as sets, intersection of sets) *)
let rec glb t1 t2 = match t1, t2 with
  | TyConcrete CTAny, _ -> t2
  | _, TyConcrete CTAny -> t1
  | TyUnion (l, r), _ ->
     TyUnion (glb l t2, glb r t2)
  | _, TyUnion (l, r) ->
     TyUnion (glb t1 l, glb t1 r)
  | TyConstraint (e, c), _ ->
     TyConstraint (glb e t2, c)
  | _, TyConstraint (e, c) ->
     TyConstraint (glb t1 e, c)
  | TyStruct ts1, TyStruct ts2
       when List.length ts1 = List.length ts2 ->
     TyStruct (List.map2_exn ts1 ts2 ~f:glb)
  | TyFunc (args1, body1), TyFunc (args2, body2)
       when List.length args1 = List.length args2 ->
     TyFunc (List.map2_exn args1 args2 ~f:glb, glb body1 body2) (* TODO: glb? *)
  | TyConcrete ct1, TyConcrete ct2 -> TyConcrete (glb_conc ct1 ct2)
  | _, _ -> TyConcrete CTNone

(* least upper bound of types (as sets, union of sets) *)
(* TODO *)
(* let lub t1 t2 = match t1, t2 with *)
(* let lub_sol = *)

(* TODO *)
let rec is_subset t1 t2 = match t1, t2 with
  | TyStruct ts1, TyStruct ts2 when List.length ts1 = List.length ts2 ->
     List.for_all2_exn ts1 ts2 ~f:is_subset
  | TyFunc (ts1, t1), TyFunc (ts2, t2) ->
     (* function arguments are contravariant *)
     List.for_all2_exn ts2 ts1 ~f:is_subset && is_subset t1 t2
  | TyConcrete CTNone, _ -> true
  | _, TyConcrete CTAny -> true
  | TyConcrete CTAny, _ -> false
  | TyConcrete (CTVal (VInt _)), TyConcrete CTInteger -> true
  | TyUnion _, _ ->
     Printf.printf "is_subset(union) is not implemented\n";
     true
  | _, TyUnion _ ->
     Printf.printf "is_subset(union) is not implemented\n";
     true
  | _, _ when [%compare.equal: type_expr] t1 t2 ->
     true
  | _, _ ->
     Printf.printf "t1: %s, t2: %s\n"
                   (sexp_of_type_expr t1 |> Sexplib.Sexp.to_string_hum)
                   (sexp_of_type_expr t2 |> Sexplib.Sexp.to_string_hum);
     false

let rec update map t1 t2 = match t1, t2 with
  | TyVar var, _ -> Map.update map var ~f:(Fn.const t2)
  | TyStruct ts1, TyStruct ts2 when List.length ts1 = List.length ts2 ->
     let zipped = List.zip_exn ts1 ts2 in
     List.fold_left zipped ~init:map ~f:(fun m (t1, t2) -> update m t1 t2)
  | TyFunc (ts1, t1), TyFunc (ts2, t2) when List.length ts1 = List.length ts2 ->
     let zipped = List.zip_exn (t1::ts1) (t2::ts2) in
     List.fold_left zipped ~init:map ~f:(fun m (t1, t2) -> update m t1 t2)
  | TyUnion (t1l, t1r), TyUnion (t2l, t2r) -> (* TODO: ? *)
     update (update map t1l t2l) t1r t2r
  | TyConstraint (t1, _c1), TyConstraint (t2, _c2) -> (* TODO: ? *)
     update map t1 t2
  | TyConcrete _, _ -> map
  | _, _ -> raise (Invalid_argument "update: not match constructor")

let print_t t =
  Printf.printf "[debug] %s\n" (sexp_of_type_expr t |> Sexplib.Sexp.to_string_hum)

let rec solve_impl sol con =
  Printf.printf "[sol] %s\n" (sexp_of_t sol |> Sexplib.Sexp.to_string_hum);
  Printf.printf "[con] %s\n" (sexp_of_type_constraint con |> Sexplib.Sexp.to_string_hum);
  match sol with
  | Bottom -> Bottom
  | Mapping map ->
     match con with
     | Empty -> sol
     | Subset (t1, t2) -> (* TODO *)
        let ct1 = subst_impl map t1 in
        print_t ct1;
        let ct2 = subst_impl map t2 in
        print_t ct2;
        if is_subset ct1 ct2 then
          sol
        else
          begin
            match glb ct1 ct2 with
            | TyConcrete CTNone -> Bottom
            | ct ->
               Printf.printf "[update]\n";
               Mapping (update map t1 ct)
          end
     | Conj cons ->
        let sol' = solve_conj sol cons in
        if equal sol' sol then
          sol
        else
          solve_impl sol' (Conj cons)
     | Disj _cons ->          (* TODO: not implemented *)
        Printf.printf "disjunction not implemented yet\n";
        sol
        (* lub_all *)
        (* Map.equal (fun t1 t2 -> true) *)
and solve_conj sol cons = match sol with
  | Bottom -> Bottom
  | Mapping map ->
     match cons with
     | [] -> sol
     | (con::cons) -> solve_conj (solve_impl sol con) cons
and subst_impl map = function
  | TyVar var -> Map.find_exn map var
  | TyStruct ts -> TyStruct (List.map ts ~f:(subst_impl map))
  | TyFunc (ts, t) -> TyFunc (List.map ts ~f:(subst_impl map), subst_impl map t)
  | TyUnion (t1, t2) -> TyUnion (subst_impl map t1, subst_impl map t2)
  | TyConstraint (t, c) -> begin
      match solve_impl (Mapping map) c with
      | Bottom -> TyConcrete CTNone (* TODO *)
      | Mapping map -> subst_impl map t
    end
  | TyConcrete c -> TyConcrete c

let solve con = solve_impl (Mapping (init con)) con
let subst sol t = match sol with
  | Bottom -> None
  | Mapping map -> Some (subst_impl map t)
