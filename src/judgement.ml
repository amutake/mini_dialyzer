open Base
open Types

module Printf = Caml.Printf

let var_ref = ref 0
let new_tyvar mark =
  let n = !var_ref in
  Caml.incr var_ref;
  TyVar ("tyvar" ^ Int.to_string n ^ "_" ^ mark)

let ty_eq t1 t2 = Conj [Subset (t1, t2); Subset (t2, t1)]
let pattern_vars = function
  | PVar (var, _) -> [var]
  | PStruct (vars, _) -> vars

exception Duplicate_key

let extend_env env pairs =
  let extra =
    match Map.of_alist (module String) pairs with
    | `Duplicate_key key ->
       Printf.printf "duplicate key '%s'\n" key;
       raise Duplicate_key
    | `Ok extra -> extra
  in
  let f ~key = function
    | `Left t -> Some t
    | `Right t -> Some t
    | `Both (_, t) -> Some t (* overwrite by right *)
  in
  Map.merge env extra ~f:f

let rec type_judge env = function
  | Val v ->
     (TyConcrete (CTVal v), Empty)
  | Var var ->
     begin
       match Map.find env var with
       | Some typ -> (typ, Empty)
       | None -> Printf.printf "var '%s' is not bound\n" var;
                 raise Not_found
     end
  | Struct exprs ->
     let (typs, cons) = collect_type_judgement env exprs in
     (TyStruct typs, Conj cons)
  | App (expr, exprs) ->
     let (typ, con) = type_judge env expr in
     let (typs, cons) = collect_type_judgement env exprs in
     let alpha = new_tyvar "app_alpha" in
     let beta = new_tyvar "app_beta" in
     let gen_alpha i = new_tyvar ("app_alpha" ^ Int.to_string i) in
     let alphas = List.map (List.range 0 (List.length exprs)) ~f:gen_alpha in
     let eq = ty_eq typ (TyFunc (alphas, alpha)) in
     let subset = Subset (beta, alpha) in
     let subsets = List.map2_exn typs alphas ~f:(fun t a -> Subset (t, a)) in
     (beta, Conj ((eq::subset::subsets) @ (con::cons)))
  | Abs (FFunc (args, body)) ->
     let gen_tyvar var = new_tyvar ("arg_" ^ var) in
     let arg_types = List.map args ~f:gen_tyvar in
     let extended = extend_env env (List.zip_exn args arg_types) in
     let (typb, conb) = type_judge extended body in
     let typ = new_tyvar "abs" in
     (typ, ty_eq typ (TyConstraint (TyFunc (arg_types, typb), conb)))
  | Let (var, e1, e2) ->
     let (typ1, con1) = type_judge env e1 in
     let (typ2, con2) = type_judge (extend_env env [(var, typ1)]) e2 in
     (typ2, Conj [con1; con2])
  | Letrec (binds, expr) ->
     let (vars, funcs) = List.unzip binds in
     let gen_tyvar var = new_tyvar ("letrec_" ^ var) in
     let tyvars = List.map vars ~f:gen_tyvar in
     let extended = extend_env env (List.zip_exn vars tyvars) in
     let (typs, cons) =
       collect_type_judgement extended (List.map funcs ~f:(fun f -> Abs f)) in
     let (typ, con) = type_judge extended expr in
     let eq_cons = List.map2_exn tyvars typs ~f:ty_eq in
     (typ, Conj (cons @ eq_cons))
  | Case (expr, branches) ->
     let beta = new_tyvar "case_beta" in
     let (typ, con) = type_judge env expr in
     let gen_tyvar i var = new_tyvar ("pat" ^ Int.to_string i ^ "_" ^ var) in
     let pattern_judge env =
       let go pat_expr guard =
         let (typp, conp) = type_judge env pat_expr in
         let (typg, cong) = type_judge env guard in
         let typg_true = ty_eq typg (TyConcrete (CTVal (VAtom "true"))) in
         (typp, Conj [conp; cong; typg_true])
       in
       function
       | PVar (var, guard) ->
          go (Var var) guard
       | PStruct (vars, guard) ->
          go (Struct (List.map vars ~f:(fun var -> Var var))) guard
     in
     let branch_constraint i (pat, body) =
       let vars = pattern_vars pat in
       let tyvars = List.map vars ~f:(gen_tyvar i) in
       let extended = extend_env env (List.zip_exn vars tyvars) in
       let (alphap, conp) = pattern_judge extended pat in
       let (betab, conb) = type_judge extended body in
       Conj [ty_eq beta betab; ty_eq typ alphap; conp; conb]
     in
     (beta, Conj [con; Disj (List.mapi branches ~f:branch_constraint)])
and collect_type_judgement env exprs =
  let judgements = List.map exprs ~f:(type_judge env) in
  List.fold_right judgements
                  ~f:(fun (t, c) (ts, cs) -> (t::ts, c::cs))
                  ~init:([], [])
