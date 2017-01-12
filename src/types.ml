open Base
module Pervasives = Caml.Pervasives (* to suppress ppx_compare warnings *)

type value =
  | VInt of Int.t
  | VAtom of String.t
[@@deriving sexp, compare]

type expr =
  | Val of value
  | Var of String.t
  | Struct of expr List.t
  | App of expr * expr List.t
  | Abs of func
  | Let of String.t * expr * expr
  | Letrec of (String.t * func) List.t * expr
  | Case of expr * (pattern * expr) List.t
and func =
  | FFunc of String.t List.t * expr
and pattern =
  | PVar of String.t * expr
  | PStruct of String.t List.t * expr
[@@deriving sexp, compare]

type concrete =
  | CTNone
  | CTAny
  | CTInteger
  | CTAtom
  | CTVal of value
[@@deriving sexp, compare]

type type_expr =
  | TyVar of String.t
  | TyStruct of type_expr List.t
  | TyFunc of type_expr List.t * type_expr
  | TyUnion of type_expr * type_expr
  | TyConstraint of type_expr * type_constraint
  | TyConcrete of concrete
and type_constraint =
  | Subset of type_expr * type_expr
  | Conj of type_constraint List.t
  | Disj of type_constraint List.t
  | Empty
[@@deriving sexp, compare]
