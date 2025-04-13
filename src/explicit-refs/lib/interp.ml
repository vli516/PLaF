open Ds
open Parser_plaf.Ast

let g_store = Store.empty_store ()

let rec eval_expr : expr -> exp_val ea_result = fun e ->
  match e with
  | Num n -> return (NumVal n)
  | Var x -> apply_env x
  | Add (e1, e2) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    int_of_numVal v1 >>= fun n1 ->
    int_of_numVal v2 >>= fun n2 ->
    return (NumVal (n1 + n2))
  | Sub (e1, e2) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    int_of_numVal v1 >>= fun n1 ->
    int_of_numVal v2 >>= fun n2 ->
    return (NumVal (n1 - n2))
  | Mul (e1, e2) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    int_of_numVal v1 >>= fun n1 ->
    int_of_numVal v2 >>= fun n2 ->
    return (NumVal (n1 * n2))
  | Div (e1, e2) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    int_of_numVal v1 >>= fun n1 ->
    int_of_numVal v2 >>= fun n2 ->
    if n2 = 0 then error "Division by zero"
    else return (NumVal (n1 / n2))
  | Let (x, e1, e2) ->
    eval_expr e1 >>= fun v ->
    extend_env x v >>+ eval_expr e2
  | ITE (e1, e2, e3) ->
    eval_expr e1 >>= fun v ->
    bool_of_boolVal v >>= fun b ->
    if b then eval_expr e2 else eval_expr e3
  | IsZero e ->
    eval_expr e >>= fun v ->
    int_of_numVal v >>= fun n ->
    return (BoolVal (n = 0))
  | Pair (e1, e2) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    return (PairVal (v1, v2))
  | Fst e ->
    eval_expr e >>= fun v ->
    pair_of_pairVal v >>= fun (v1, _) ->
    return v1
  | Snd e ->
    eval_expr e >>= fun v ->
    pair_of_pairVal v >>= fun (_, v2) ->
    return v2
  | Debug -> fun env ->
    print_endline (string_of_env' [] env);
    print_endline (Store.string_of_store !g_store);
    error "Reached breakpoint"
  | Proc (x, body) ->
    lookup_env >>= fun env ->
    return (ProcVal (x, body, env))
  | App (e1, e2) ->
    eval_expr e1 >>= fun funval ->
    eval_expr e2 >>= fun argval ->
    clos_of_procVal funval >>= fun (id, body, env') ->
    extend_env id argval env' >>+ eval_expr body
  | Letrec (id, param, body, target) ->
    extend_env_rec id param body >>+ eval_expr target
  | BeginEnd es ->
    sequence (List.map eval_expr es) >>= fun vs ->
    match List.rev vs with
    | [] -> error "Empty begin-end block"
    | v::_ -> return v
  | NewRef e ->
    eval_expr e >>= fun v ->
    return (RefVal (Store.new_ref g_store v))
  | DeRef e ->
    eval_expr e >>= fun v ->
    int_of_refVal v >>= fun l ->
    return (Store.deref g_store l)
  | SetRef (e1, e2) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    int_of_refVal v1 >>= fun l ->
    return (Store.set_ref g_store l v2)
  | Tuple es ->
    mapM eval_expr es >>= fun vs ->
    return (TupleVal vs)
  | Untuple (ids, e1, e2) ->
    eval_expr e1 >>= fun v ->
    tupleVal_to_list_of_evs v >>= fun vs ->
    if List.length ids <> List.length vs then
      error "Tuple lengths do not match"
    else
      let new_env = List.combine ids vs in
      List.fold_right (fun (id, v) acc -> acc >>= extend_env id v) new_env (eval_expr e2)
  | Record fs ->
    let process_field (id, (is_mutable, e)) =
      eval_expr e >>= fun ev ->
      if is_mutable then return (RefVal (Store.new_ref g_store ev)) else return ev
    in
    sequence (List.map process_field fs) >>= fun evs ->
    return (RecordVal (addIds fs evs))
  | Proj(e, id) ->
    eval_expr e >>= fun ev ->
    fields_of_recordVal ev >>= fun fields ->
    (match List.assoc_opt id fields with
     | None -> error ("Field "^id^" not found!")
     | Some (true, RefVal l) -> return (Store.deref g_store l)
     | Some (false, v) -> return v
     | Some (true, _) -> error "Malformed reference in mutable field")
  | SetField(e1, id, e2) ->
    eval_expr e1 >>= fun v1 ->
    fields_of_recordVal v1 >>= fun fields ->
    (match List.assoc_opt id fields with
     | None -> error ("Field " ^ id ^ " not found!")
     | Some (false, _) -> error "Field not mutable"
     | Some (true, RefVal l) ->
         eval_expr e2 >>= fun v2 ->
         Store.set_ref g_store l v2
     | Some (true, _) -> error "Malformed reference in mutable field")
  | IsNumber(e) ->
    eval_expr e >>= fun v ->
    match v with
    | NumVal _ -> return (BoolVal true)
    | _ -> return (BoolVal false)
  | _ -> failwith ("Not implemented: "^string_of_expr e)

let interp (e : expr) : exp_val result =
  run (eval_expr e)

let interpf (s:string) : exp_val result =
  let s = String.trim s in
  let file_name = match String.index_opt s '.' with
    | None -> s ^ ".exr"
    | _ -> s
  in interp @@ Parser_plaf.Parser.parse_file file_name
