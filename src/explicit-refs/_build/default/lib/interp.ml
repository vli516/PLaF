(* Vinci Li CS496
I pledge my honor that I have abided by the Stevens Honor System.*)
open Ds
open Parser_plaf.Ast
open Parser_plaf.Parser

(* Assume you have a global store defined in a Store module *)
let g_store = Store.empty_store 20 (NumVal 0)

(* Helper function: associate each field identifier with its evaluated value.
   This is used for record creation.
*)
let rec addIds fs evs =
  match fs, evs with
  | [], [] -> []
  | (id, (is_mutable, _)) :: rest, v :: vs -> (id, (is_mutable, v)) :: addIds rest vs
  | _ -> failwith "Error: mismatched lengths in record fields"

(* Process one field of a record.
   If the field is mutable (declared with "<="), we allocate a new reference.
*)
let rec process_field (id, (is_mutable, e)) =
  eval_expr e >>= fun ev ->
  if is_mutable then return (RefVal (Store.new_ref g_store ev))
  else return ev

(* The main evaluator for expressions *)
and eval_expr (e : expr) : exp_val ea_result =
  match e with
  | Int n ->
      return (NumVal n)
  | Unit ->
      return UnitVal
  | Var id ->
      apply_env id
  | Add (e1, e2) ->
      eval_expr e1 >>= int_of_numVal >>= fun n1 ->
      eval_expr e2 >>= int_of_numVal >>= fun n2 ->
      return (NumVal (n1 + n2))
  | Sub (e1, e2) ->
      eval_expr e1 >>= int_of_numVal >>= fun n1 ->
      eval_expr e2 >>= int_of_numVal >>= fun n2 ->
      return (NumVal (n1 - n2))
  | Mul (e1, e2) ->
      eval_expr e1 >>= int_of_numVal >>= fun n1 ->
      eval_expr e2 >>= int_of_numVal >>= fun n2 ->
      return (NumVal (n1 * n2))
  | Div (e1, e2) ->
      eval_expr e1 >>= int_of_numVal >>= fun n1 ->
      eval_expr e2 >>= int_of_numVal >>= fun n2 ->
      if n2 = 0 then error "Division by zero"
      else return (NumVal (n1 / n2))
  | Let (id, def, body) ->
      eval_expr def >>= extend_env id >>+ eval_expr body
  | ITE (e1, e2, e3) ->
      eval_expr e1 >>= bool_of_boolVal >>= fun b ->
      if b then eval_expr e2 else eval_expr e3
  | BeginEnd es ->
      (* Evaluate a sequence and return the value of the last expression *)
      sequence (List.map eval_expr es) >>= fun vs ->
      return (List.hd (List.rev vs))
  | IsZero e ->
      eval_expr e >>= int_of_numVal >>= fun n ->
      return (BoolVal (n = 0))
  | Pair (e1, e2) ->
      eval_expr e1 >>= fun v1 ->
      eval_expr e2 >>= fun v2 ->
      return (PairVal (v1, v2))
  | Fst e ->
      eval_expr e >>= pair_of_pairVal >>= fun (v1, _) ->
      return v1
  | Snd e ->
      eval_expr e >>= pair_of_pairVal >>= fun (_, v2) ->
      return v2
  | Proc (id, _, body) ->
      lookup_env >>= fun en ->
      return (ProcVal (id, body, en))
  | App (e1, e2) ->
      eval_expr e1 >>= clos_of_procVal >>= fun (id, body, en) ->
      eval_expr e2 >>= fun ev ->
      return en >>+ extend_env id ev >>+ eval_expr body
  | Letrec ([(id, par, _, _, e)], target) ->
      extend_env_rec id par e >>+ eval_expr target

  (* --- Record operations (Part I) --- *)
  | Record fs ->
      sequence (List.map process_field fs) >>= fun evs ->
      return (RecordVal (addIds fs evs))
  | Proj (e, field) ->
      eval_expr e >>= fun ev ->
      fields_of_recordVal ev >>= fun fs ->
      (try 
         let (is_mutable, field_val) = List.assoc field fs in
         if is_mutable then 
           (match field_val with
            | RefVal r -> Store.deref g_store r
            | _ -> error "Expected a mutable field represented by a reference")
         else
           return field_val
       with Not_found -> error ("Field " ^ field ^ " not found"))
  | SetField (e1, field, e2) ->
      eval_expr e1 >>= fun ev ->
      fields_of_recordVal ev >>= fun fs ->
      (try
         let (is_mutable, field_val) = List.assoc field fs in
         if not is_mutable then error "Field not mutable"
         else eval_expr e2 >>= fun new_val ->
              (match field_val with
               | RefVal r ->
                   Store.set_ref g_store r new_val >>= fun _ ->
                   return UnitVal
               | _ -> error "Expected a mutable field represented by a reference")
       with Not_found -> error ("Field " ^ field ^ " not found"))
       
  (* --- Number predicate --- *)
  | IsNumber e ->
      eval_expr e >>= fun ev ->
      (match ev with
       | NumVal _ -> return (BoolVal true)
       | _ -> return (BoolVal false))
       
  (* --- Debug: print the current environment and store --- *)
  | Debug _e ->
      string_of_env >>= fun str_env ->
      let str_store = Store.string_of_store string_of_expval g_store in
      (print_endline (str_env ^ "\n" ^ str_store);
       error "Reached breakpoint")
       
  | _ -> failwith ("Not implemented: " ^ string_of_expr e)

and string_of_expr (e: expr) : string =
  "<expr>"

let eval_prog (AProg (_, e)) =
  eval_expr e

let interp (s:string) : exp_val result =
  let c = s |> parse |> eval_prog in
  run c

(* Preprocess file contents to remove extraneous newlines/whitespace *)
let preprocess (s:string) : string =
  let lines = String.split_on_char '\n' s in
  let trimmed = List.map String.trim lines in
  String.concat " " trimmed

(* Interpret an expression read from a file with optional extension .sool *)
let interpf (s:string) : exp_val result = 
    let s = String.trim s      (* remove leading and trailing spaces *)
    in let file_name =    (* allow rec to be optional *)
         match String.index_opt s '.' with None -> s^".exr" | _ -> s
    in
    interp @@ read_file file_name
