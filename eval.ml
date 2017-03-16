(*
#load "dynlink.cma";;
#load "camlp4o.cma";;
*)

(*
#use "topfind";;
#camlp4o;;
*)

open Genlex;;
open Printf;;
open List;;

type expr =
  (* Constants *)
  | EInt of int

  (* Variable *)
  | EVar of string

  (* Built-in primitve operations *)
  | EBin of string * expr * expr
  | EIsZero of expr

  (* Usual lambda operations *)
  | EApply of expr * expr
  | ELambda of string * expr
  | ECond of expr * expr * expr
  | ELetRec of string * expr * expr
and ptr =
  | Ptr of string * value
and env = (string * string) list
and value =
  | VInt of int
  | VClousure of expr * env
;;

let empty_storage: (ptr list) = [];;
let empty_env: (string * string) list = [];;
let new_ptr x v = Ptr(x, v);;

let rec lookup_storage st x = match st with
    | h :: t ->
      let name = match h with | Ptr(a, _) -> a in
      if name = x then
         h
      else
         lookup_storage t x
    | [] -> failwith ("storage lookup error")

let rec lookup_env env x = match env with
    | (var, pname) :: t ->
      if var = x then
          pname
      else
          lookup_env t x
    | [] -> failwith (sprintf "environment lookup error for name %s" x)
;;

let extend_env env s pname = (s, pname) :: env;;
let extend_storage st s v = Ptr(s, v) :: st;;


let rec print_ptr p = match p with
    | Ptr(x, v) -> printf "%s |-> " x; print_value v

and print_env e = match e with
    | (s, pname) :: t ->
            printf "%s |-> %s" s pname;
            printf ", ";
            print_env t
    | [] -> printf "_"

and print_storage s = match s with
    | Ptr(p, v) :: t ->
            printf "%s |-> " p;
            print_value v;
            printf ", ";
            print_storage t
    | [] -> printf "_"

and print_value v = match v with
    | VInt n -> printf "VInt %d" n
    | VClousure(e, env) ->
            printf "[";
            (match e with
             | ELambda(_, _) -> print_expr e
             | _ -> failwith ("invalid closure"));
            printf ", ";
            print_env env;
            printf "]"

and print_expr e = match e with
    | EVar x -> printf "Var %s" x
    | EInt n -> printf "Int %d" n
    | EBin(op, x, y) ->
            printf "(";
            print_expr x;
            printf ") %s (" op;
            print_expr y;
            printf ")"
    | EIsZero(e) ->
            printf "IsZero(";
            print_expr e;
            printf ")"
    | EApply(e1, e2) ->
            printf "App (";
            print_expr e1;
            printf ", ";
            print_expr e2;
            printf ")"
    | ELambda(x, e1) ->
            printf "Lambda (%s, " x;
            print_expr e1;
            printf ")"
    | ECond(e_pred, e_true, e_false) ->
            printf "Cond(";
            print_expr e_pred;
            printf ", ";
            print_expr e_true;
            printf ", ";
            print_expr e_false;
            printf ")"
    | ELetRec(x, e1, e2) ->
            printf "LetRec (%s, " x;
            print_expr e1;
            printf ", ";
            print_expr e2;
            printf ")"
    | _ -> failwith ("attempt to print unknown AST node")
;;



let test () =
    let s1 = extend_storage empty_storage "p1" (VInt 1) in
    print_ptr (lookup_storage s1 "p1"); printf "\n";
    let s2 = extend_storage s1 "p2" (VClousure(ELambda("x", EVar "x"), empty_env)) in
    print_ptr (lookup_storage s2 "p2"); printf "\n"
;;

(* test ();; *)

let rec update_storage st pname v = match st with
    | Ptr(pname', v') :: t ->
            if pname' = pname then
                Ptr(pname', v) :: (update_storage t pname v)
            else
                Ptr(pname', v') :: (update_storage t pname v)
    | [] -> []
;;


let keywords =
  ["("; ")"; "+"; "-"; "=";
   "if"; "then"; "else"; "iszero";
   "\\"; ".";
   "letrec"; "in"]
;;

(* This is needed to parse - as a seapate sign in case it stands before the number *)
let lex stream =
    let rec aux = parser
      | [< 'Int n when n<0; t=aux >] -> [< 'Kwd "-"; 'Int(-n); t >]
      | [< 'h; t=aux >] -> [< 'h; t >]
      | [< >] -> [< >] in
    aux(make_lexer keywords stream);;


let left_assoc_apply vec =
    let rec left_assoc_apply' vec res = match vec with
        | h :: t ->
            left_assoc_apply' t (EApply(res, h))
        | [] -> res
    in left_assoc_apply' (tl vec) (hd vec)
;;

let rec parse_atom = parser
    | [< 'Int n >] -> EInt n
    | [< 'Ident v >] -> EVar v
    | [< 'Kwd "("; e=parse_expr; 'Kwd ")" >] -> e

and parse_apply = parser
    | [< e1=parse_atom; stream >] ->
      (parser
         | [< e2 = parse_apply >] -> e1 :: e2
         | [< >] -> [e1]) stream


and parse_arith = parser
    | [< e1=parse_apply; stream >] ->
      (parser
         | [< 'Kwd "+"; e2=parse_arith >] -> EBin("+", left_assoc_apply e1, e2)
         | [< 'Kwd "-"; e2=parse_arith >] -> EBin("-", left_assoc_apply e1, e2)
         | [< >] -> left_assoc_apply e1) stream

and parse_expr : 'a Stream.t -> expr = parser
    | [< e1=parse_arith >] -> e1
    | [< 'Kwd "iszero"; e=parse_expr >] ->
        EIsZero(e)
    (*| [< e1=parse_arith; stream >] ->
        (parser
         | [< 'Kwd "="; e2=parse_expr >] -> EEqual(e1, e2)
         | [< >] -> e1) stream*)
    | [< 'Kwd "if"; p=parse_expr; 'Kwd "then"; t=parse_expr;
         'Kwd "else"; f=parse_expr >] ->
        ECond(p, t, f)
    | [< 'Kwd "\\"; 'Ident x; 'Kwd "."; body=parse_expr >] ->
        ELambda(x, body)
    | [< 'Kwd "letrec"; 'Ident x; 'Kwd "="; e1=parse_expr; 'Kwd "in"; e2=parse_expr >] ->
        ELetRec(x, e1, e2)
;;


let ptr_count = ref 0;;

let fresh_ptrname p =
    p := !p + 1;
    sprintf "p%d" !p
;;

(* In the storage `st', for all the enclosed environments,
   substitute the value <x> |-> p1 to <x> |-> p2.  *)
let rec update_letrec_pointer st p1 p2 =
    let rec update_enclosed_env env p1 p2 = match env with
        | (x, p) :: t ->
                if p = p1 then
                    (x, p2) :: update_enclosed_env t p1 p2
                else
                    (x, p) :: update_enclosed_env t p1 p2
        | [] -> []
    in
    match st with
    | Ptr(p, v) :: t ->
            Ptr(p, match v with
                   | VClousure(e, env) -> VClousure (e, update_enclosed_env env p1 p2)
                   | _ -> v) :: update_letrec_pointer t p1 p2
    | [] -> []
;;



let rec eval st env exp = match exp with
    | EInt n ->
            let newp = fresh_ptrname ptr_count in
            let st' = extend_storage st newp (VInt n) in
            (st', newp)
    | EVar x ->
            let p = lookup_env env x in
            (st, p)
    | EBin(op, e1, e2) ->
            let (st1, p1) = eval st env e1 in
            let (st2, p2) = eval st1 env e2 in
            let Ptr(_,v1) = lookup_storage st2 p1 in
            let n1 = match v1 with
                     | VInt n -> n
                     | _ -> failwith ("lhs of addition is not an integer") in
            let Ptr(_,v2) = lookup_storage st2 p2 in
            let n2 = match v2 with
                     | VInt n -> n
                     | _ -> failwith ("rhs of addition is not an integer") in
            let pname = fresh_ptrname ptr_count in
            let v = match op with
                    | "+" -> VInt (n1 + n2)
                    | "-" -> VInt (n1 - n2)
                    | _ -> failwith (sprintf "unsupported binary operation %s" op) in
            (extend_storage st2 pname v, pname)
    | EIsZero(e) ->
            let (st1, p) = eval st env e in
            let Ptr(_,v) = lookup_storage st1 p in
            let n = match v with
                    | VInt n -> n
                    | _ -> failwith ("iszero has non-integer argument") in
            let pname = fresh_ptrname ptr_count in
            if n = 0 then
                (extend_storage st1 pname (VInt 1), pname)
            else
                (extend_storage st1 pname (VInt 0), pname)
    | ELambda(x, e1) ->
            let newp = fresh_ptrname ptr_count in
            (* XXX do we need to copy env? *)
            let st' = extend_storage st newp (VClousure(ELambda(x, e1), env)) in
            (st', newp)
    | ECond(e1, e2, e3) ->
            let (st1, p1) = eval st env e1 in
            let Ptr(_,v) = lookup_storage st1 p1 in
            let n = match v with
                    | VInt n -> n
                    | _ -> failwith ("non-integer result in the condition predicate") in
            if n = 0 then
                eval st1 env e3
            else
                eval st1 env e2
    | EApply(e1, e2) ->
            let (st1, p1) = eval st env e1 in
            let (st2, p2) = eval st1 env e2 in
            let Ptr(_,v1) = lookup_storage st2 p1 in
            let (e', env') = match v1 with
                             | VClousure(e', env') -> (e', env')
                             | _ -> failwith ("lhs of apply is not a lambda abstraction") in
            let (x, ebody) = match e' with
                             | ELambda(x, ebody) -> (x, ebody)
                             | _ -> failwith ("closure does not contain lambda abstraction") in
            eval st2 (extend_env env' x p2) ebody
    | ELetRec(x, e1, e2) ->
            let pname = fresh_ptrname ptr_count in
            let env' = extend_env env x pname in
            let (st1, p1) = eval st env' e1 in
            let st2 = update_letrec_pointer st1 pname p1 in
            eval st2 (extend_env env x p1) e2

    | _ -> failwith ("attempt to evaluate unknown AST node")
;;


let prog01 = "2 + 3"
let prog02 = "\\x.x"
let prog03 = "(\\x.x) 2"
let prog04 = "(\\x.\\y.x) 2"
let prog05 = "(\\f.(f 1) + (f 1)) ((\\x.\\y.x) 2)"
let prog06 = "(\\f.(\\x.f (\\v.((x x) v))) (\\x.f (\\v.((x x) v)))) "
           ^ "(\\f.\\x.if (iszero x) then 0 else x + f (x-1)) 2"
let prog07 = "letrec f = 1 in f"
let prog08 = "letrec f = \\x.if iszero x then x else f (x-1) in f 1"

let prog = prog08

let v = parse_expr (lex (Stream.of_string prog));;
print_expr v;;
printf "\n"

let t = eval empty_storage empty_env v;;
match t with | (st, pname) ->
    print_storage st;
    printf "; %s\n" pname ;;

