open ReM
open Parser_plaf.Ast

(* === Static Semantics: type expressions === *)
(* Original plus new constructors for HW5 and record/pair types *)
type texpr =
  | IntType                               (* int *)
  | BoolType                              (* bool *)
  | FuncType   of texpr * texpr          (* τ1 -> τ2 *)
  | PairType   of texpr * texpr          (* pair<τ1,τ2> *)
  | RecordType of (string * texpr) list  (* record<{id:τ;…}> *)
  | UnitType                              (* unit *)
  | RefType   of texpr   (* was TRef *)
  | ListType  of texpr   (* was TList *)
  | TreeType  of texpr   (* was TTree *)

(* Pretty-printer for types *)
let rec string_of_texpr = function
  | IntType         -> "int"
  | BoolType        -> "bool"
  | FuncType(t1,t2) -> "(" ^ string_of_texpr t1 ^ " -> " ^ string_of_texpr t2 ^ ")"
  | PairType(t1,t2) -> "(" ^ string_of_texpr t1 ^ "," ^ string_of_texpr t2 ^ ")"
  | RecordType fs   ->
      "{" ^ String.concat ";"
        (List.map (fun (id,t) -> id ^ ":" ^ string_of_texpr t) fs)
      ^ "}"
  | UnitType        -> "unit"
  | RefType t    -> "ref("  ^ string_of_texpr t ^ ")"
  | ListType t   -> "list(" ^ string_of_texpr t ^ ")"
  | TreeType t   -> "tree(" ^ string_of_texpr t ^ ")"


(* === Type Environments (unchanged) === *)
type tenv =
  | EmptyTEnv
  | ExtendTEnv of string * texpr * tenv

(* Expressed Result *)
type 'a tea_result = ('a,tenv) a_result

let run_teac (c:'a tea_result) : 'a result =
  c EmptyTEnv

let empty_tenv : unit -> tenv tea_result =
  fun () -> return EmptyTEnv

let extend_tenv : string -> texpr -> tenv tea_result =
  fun id v env -> Ok (ExtendTEnv(id,v,env))

let rec apply_tenv (id:string): texpr tea_result =
  fun tenv ->
    match tenv with
    | EmptyTEnv -> Error (id ^ " not found")
    | ExtendTEnv(id2,t,tenv2) ->
        if id = id2 then Ok t else apply_tenv id tenv2

let list_of_recordtype s = function
  | RecordType fs -> return fs
  | _ -> error @@ s ^ "Record type expected!"

let pair_of_funcType s = function
  | FuncType(t1,t2) -> return (t1,t2)
  | _ -> error @@ s ^ "Expected a function type"

let pair_of_pairType s = function
  | PairType(t1,t2) -> return (t1,t2)
  | _ -> error @@ s ^ "Expected a pair type"

let rec string_of_tenv' = function
  | EmptyTEnv -> ""
  | ExtendTEnv(id,v,env) ->
      "(" ^ id ^ "," ^ string_of_texpr v ^ ")" ^ string_of_tenv' env

let string_of_tenv =
  fun tenv -> Ok (string_of_tenv' tenv)
