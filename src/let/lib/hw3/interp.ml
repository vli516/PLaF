(*
Author: Vinci Li
Pledge: I pledge my honor that I have abided by the Stevens Honor System.
*)
open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds

(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | Record fields ->
    let field_names = List.map fst fields in
    let unique_field_names = List.sort_uniq String.compare field_names in
    if List.length field_names <> List.length unique_field_names then
      error "Record: duplicate fields"
    else
      let rec eval_fields acc = function
        | [] -> return (RecordVal (List.rev acc))
        | (key, (_mutable_flag, value)) :: rest ->
            eval_expr value >>= fun v ->
            eval_fields ((key, TupleVal [BoolVal false; v]) :: acc) rest
      in
      eval_fields [] fields

  | Proj(e, field) ->
      eval_expr e >>= record_of_recordVal >>= fun fields ->
      match List.assoc_opt field fields with
      | Some (TupleVal [_; v]) -> return v
      | Some v -> return v
      | None -> error "Proj: field does not exist"
    
  
(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c

(*looks up field*)
let lookup_field : string -> (string * exp_val) list -> exp_val ea_result = fun id fields ->
  match List.assoc_opt id fields with
  | Some (TupleVal [_; v]) -> return v
  | Some v -> return v
  | None -> error "Field does not exist!"
