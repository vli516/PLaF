open ReM
open Parser_plaf.Ast
open Parser_plaf.Parser
open Dst  (* static-semantics texpr & helpers *)

(* === Convert AST types to semantic texprs === *)
let rec ast_type_to_texpr = function
  | Parser_plaf.Ast.IntType          -> IntType
  | Parser_plaf.Ast.BoolType         -> BoolType
  | Parser_plaf.Ast.FuncType(t1,t2)  -> FuncType(ast_type_to_texpr t1, ast_type_to_texpr t2)
  | Parser_plaf.Ast.PairType(t1,t2)  -> PairType(ast_type_to_texpr t1, ast_type_to_texpr t2)
  | Parser_plaf.Ast.RecordType fs    -> RecordType(List.map (fun (id,t) -> (id, ast_type_to_texpr t)) fs)
  | _ -> failwith "Unsupported type annotation"

(* === Type-Checker for the "CHECKED" Language === *)
let rec chk_expr : expr -> texpr tea_result = function
  (* Original cases unchanged *)
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
      chk_expr e >>= fun t ->
      if t = IntType then return BoolType
      else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2) | Div(e1,e2) ->
      chk_expr e1 >>= fun t1 -> chk_expr e2 >>= fun t2 ->
      if t1 = IntType && t2 = IntType then return IntType
      else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
      chk_expr e1 >>= fun t1 ->
      if t1 <> BoolType then error "ITE: condition must be boolean"
      else chk_expr e2 >>= fun t2 -> chk_expr e3 >>= fun t3 ->
           if t2 = t3 then return t2
           else error "ITE: branches must have same type"
  | Let(id,e,body) ->
      chk_expr e >>= fun t -> extend_tenv id t >>+ chk_expr body
  | Proc(var, Some tau, e) ->  (* proc(var:τ) e *)
      let t1 = ast_type_to_texpr tau in
      extend_tenv var t1 >>+ chk_expr e >>= fun t2 ->
      return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) -> error "proc: type declaration missing"
  | App(e1,e2) ->
      chk_expr e1 >>= pair_of_funcType "app: " >>= fun (t1,t2) ->
      chk_expr e2 >>= fun t3 -> if t1 = t3 then return t2
                                 else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target)
  | Letrec([(_id,_param,_,None,_body)],_target) ->
      error "letrec: type declaration missing"
  | Letrec([(id,param,Some tauParam,Some tauRes,body)],target) ->
      let p = ast_type_to_texpr tauParam in
      let r = ast_type_to_texpr tauRes in
      extend_tenv id (FuncType(p,r)) >>+
      (extend_tenv param p >>+ chk_expr body >>= fun t ->
       if t = r then chk_expr target
       else error "LetRec: Type of recursive function does not match declaration")
  | Debug(_e) -> string_of_tenv >>= fun str -> print_endline str; error "Debug: reached breakpoint"

  (* === ADDITIONS FOR PART 1: REFERENCES === *)
  | NewRef e -> chk_expr e >>= fun t -> return (RefType t)
  | DeRef e  -> chk_expr e >>= fun t -> (match t with | RefType t' -> return t' | _ -> error "deref: expected a reference")
  | SetRef(e1,e2) -> chk_expr e1 >>= fun t1 ->
      (match t1 with
       | RefType inner -> chk_expr e2 >>= fun t2 -> if t2 = inner then return UnitType else error "setref: type mismatch"
       | _ -> error "setref: expected a reference")
  | BeginEnd [] -> return UnitType
  | BeginEnd es ->
      let rec go = function
        | [] -> return UnitType
        | [e] -> chk_expr e
        | h::t -> chk_expr h >>= fun _ -> go t
      in go es

  (* === ADDITIONS FOR PART 2: LISTS === *)
  | EmptyList tau_opt ->
      (match tau_opt with
       | Some tau -> let dt = ast_type_to_texpr tau in return (ListType dt)
       | None     -> error "emptylist: missing type annotation")
  | Cons(hd,tl) -> chk_expr hd >>= fun th -> chk_expr tl >>= fun tt ->
      (match tt with
       | ListType te when te = th -> return (ListType te)
       | ListType _     -> error "cons: head and tail types do not match"
       | _           -> error "cons: second argument must be a list")
  | IsEmpty e -> chk_expr e >>= fun te -> (match te with | ListType _ -> return BoolType | _ -> error "empty?: expected a list")
  | Hd e      -> chk_expr e >>= fun te -> (match te with | ListType te' -> return te' | _ -> error "hd: expected a list")
  | Tl e      -> chk_expr e >>= fun te -> (match te with | ListType te' -> return (ListType te') | _ -> error "tl: expected a list")

  (* === ADDITIONS FOR PART 3: TREES === *)
  | EmptyTree tau_opt ->
      (match tau_opt with
       | Some tau -> let dt = ast_type_to_texpr tau in return (TreeType dt)
       | None     -> error "emptytree: missing type annotation")
  | Node(d,lt,rt) -> chk_expr d >>= fun td -> chk_expr lt >>= fun tlt -> chk_expr rt >>= fun trt ->
      (match tlt, trt with
       | TreeType te1, TreeType te2 when te1 = te2 && td = te1 -> return (TreeType te1)
       | TreeType _, TreeType _ -> error "node: argument types do not match or data mismatch"
       | _               -> error "node: expected two trees and matching data type")
  | CaseT(target, empty_case, id_d, id_lt, id_rt, node_case) -> chk_expr target >>= fun tt ->
      (match tt with
       | TreeType te -> chk_expr empty_case >>= fun t_empty ->
           extend_tenv id_d te >>+ extend_tenv id_lt (TreeType te) >>+ extend_tenv id_rt (TreeType te) >>+
           chk_expr node_case >>= fun t_node -> if t_empty = t_node then return t_empty else error "caseT: branches must return same type"
       | _ -> error "caseT: expected a tree")

  | _ -> failwith "chk_expr: implement"

and chk_prog (AProg(_,e)) = chk_expr e

let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog in run_teac (c >>= fun t -> return @@ string_of_texpr t)
