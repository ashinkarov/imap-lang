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
  | Ptr of string * int * value
and env = (string * string) list
and value =
  | VInt of int
  | VClousure of expr * env
;;

let empty_storage: (ptr list) = [];;
let empty_env: (string * string) list = [];;

let rec lookup_storage ?(warn=true) st x  = match st with
    | h :: t ->
      let Ptr(name, rc, _) = h in
      if name = x then
          (if rc = 0 && warn then
              (printf "\t!!lookup of the pointer %s with RC=0!\n" name; h)
          else
              h)
      else
          lookup_storage t x ~warn:warn
    | [] -> failwith (sprintf "storage lookup error for name %s" x)

let rec lookup_env env x = match env with
    | (var, pname) :: t ->
      if var = x then
          pname
      else
          lookup_env t x
    | [] -> failwith (sprintf "environment lookup error for name %s" x)
;;

let extend_env env s pname = (s, pname) :: env;;
let extend_storage st s rc v = Ptr(s, rc, v) :: st;;


let rec print_ptr p = match p with
    | Ptr(x, rc, v) -> printf "%s |(%d)-> " x rc; print_value v

and print_env e = match e with
    | (s, pname) :: t ->
            printf "%s |-> %s" s pname;
            printf ", ";
            print_env t
    | [] -> printf "_"

and print_storage s = match s with
    | p :: t ->
            print_ptr p;
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
    let s1 = extend_storage empty_storage "p1" 1 (VInt 1) in
    print_ptr (lookup_storage s1 "p1"); printf "\n";
    let s2 = extend_storage s1 "p2" 1 (VClousure(ELambda("x", EVar "x"), empty_env)) in
    print_ptr (lookup_storage s2 "p2"); printf "\n"
;;

(* test ();; *)

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
    | Ptr(p, rc, v) :: t ->
            Ptr(p, rc, match v with
                       | VClousure(e, env) -> VClousure (e, update_enclosed_env env p1 p2)
                       | _ -> v)
            :: update_letrec_pointer t p1 p2
    | [] -> []
;;

let rec imm_use e r = match e with
    | EInt _ -> r
    | EVar x -> x :: r
    | EBin(_, e1, e2) -> imm_use e2 (imm_use e1 r)
    | EIsZero(e) -> imm_use e r
    | ELambda(x, e) -> r
    | EApply(e1, e2) -> imm_use e2 (imm_use e1 r)
    | ECond(e1,_,_) -> imm_use e1 r
    | ELetRec(_,_,_) -> r (* FIXME what do we do here? *)
;;

let rec unique l = match l with
    | h :: t -> h :: (unique (filter (fun x -> x <> h) t))
    | [] -> []
;;

let rec capture e r = match e with
    | EInt _ -> r
    | EVar x -> x :: r
    | EBin(_, e1, e2) -> capture e2 (capture e1 r)
    | EIsZero e -> capture e r
    | ELambda(x, e) ->
            let fv = filter (fun x' -> x' <> x) (capture e []) in
            append r (unique fv)
    | EApply(e1, e2) -> capture e2 (capture e1 r)
    | ECond(e1,e2,e3) ->
            let r1 = capture e1 r in
            let fv1 = capture e2 [] in
            let fv2 = capture e3 [] in
            append r1 (unique (append fv1 fv2))
    | ELetRec(x,e1,e2) ->
            let fv1 = filter (fun x' -> x' <> x) (capture e1 []) in
            let fv2 = filter (fun x' -> x' <> x) (capture e2 []) in
            append r (unique (append fv1 fv2))
;;

let rec prtlst l = match l with
    | h :: t -> printf "%s, " h; prtlst t
    | [] -> printf "_\n"
;;

let test_imm_use () =
    let e = parse_expr (lex (Stream.of_string "(f 1) + (f 1)")) in
    prtlst (imm_use e []);
    prtlst (capture e [])
;;

(* test_imm_use ();;  *)


let rec rc_inc st pname = match st with
    | Ptr(s, rc', v) as p :: t ->
            if s = pname then
                Ptr(s, rc'+1, v) :: t
            else
                p :: rc_inc t pname
    | [] -> failwith (sprintf "rc_inc failed to find pointer %s" pname)
;;


let rec rc_dec' st pname ptrs =
    printf "\t--- rc_dec' %s, st={" pname; print_storage st; printf "}, ptrs={"; prtlst ptrs; printf "}\n";
    if mem pname ptrs then
        st
    else
    let st1 = map (fun p -> let Ptr(s,rc,v) = p in
                            if s = pname then
                                Ptr(s, rc-1, v)
                            else
                                p)
                  st in
    let Ptr(s, rc, v) = lookup_storage st1 pname ~warn:false in
    if rc = 0 then
        match v with
        | VInt _ -> st1
        | VClousure(e, env) ->
                let vars = capture e [] in
                let rec upd st vars = match vars with
                    | v :: t ->
                            let pname = lookup_env env v in
                            rc_dec' (upd st t) pname (s::ptrs)
                    | [] -> st
                in
                upd st1 vars
    else
        st1
;;

let rc_dec st pname = rc_dec' st pname []
;;

(*let rec rc_dec_fun st pname = match st with
    | Ptr(s, rc', v) as p :: t ->
            if s = pname then
                Ptr(s, rc'-1, v) :: t
            else
                p :: rc_dec_fun t pname
    | [] -> failwith (sprintf "rc_dec_fun failed to find pointer %s" pname)
;;*)

(*let bump_fv st env e =
    let rec bump_helper st env fvlist = match fvlist with
    | [] -> st
    | h :: t ->
            let count = length (filter (fun x -> x = h) t) + 1 in
            (*printf "\t--> #fv %s = %d\n" h count; *)
            let pname = lookup_env env h in
            bump_helper (rc_add st pname count) env (filter (fun x -> x <> h) t)
    in
    let st' = bump_helper st env (fv e []) in
    printf "  --> "; print_storage st'; printf "\n";
    st'
;;*)

let inc_func_arg_rc st pname x ebody =
    let vars = capture ebody [] in
    printf "  -- capture %s (ptr = %s) -> " x pname; print_expr ebody; printf " = ";
    prtlst (filter (fun x' -> x' = x) vars);
    let count = fold_left (fun v x' -> v + if x' = x then 1 else 0) 0 vars in
    if count = 0 then
        rc_dec st pname
    else
        let rec upd n = if n = 0 then st else rc_inc (upd (n-1)) pname in
        upd (count - 1)
;;


let inc_func_fv_rc st env x ebody =
    let vars = filter (fun x' -> x' <> x) (capture ebody []) in
    printf "  -- func fv use %s in -> " x ; print_expr ebody; printf " = "; prtlst vars;
    let rec upd l = match l with
                    | h :: t -> rc_inc (upd t) (lookup_env env h)
                    | [] -> st
    in upd vars
;;

let inc_branch_fv_rc st env e =
    let vars = capture e [] in
    printf "  -- branch fv -> "; print_expr e; printf " = "; prtlst vars;
    let rec upd l = match l with
                    | h :: t -> rc_inc (upd t) (lookup_env env h)
                    | [] -> st
    in upd vars
;;

let dec_cond_fv_rc st env e =
    let (e1, e2) = match e with
        | ECond(e1, e2, e3) -> (e2, e3)
        | _ -> failwith ("dec_cond_fv got non-conditional") in
    let vars = unique (append (capture e1 []) (capture e2 [])) in
    printf "  -- cond fv dec -> "; print_expr e; printf " = "; prtlst vars;
    let rec upd l = match l with
                    | h :: t -> rc_dec (upd t) (lookup_env env h)
                    | [] -> st
    in upd vars
;;


let rec eval st env exp = match exp with
    | EInt n ->
            let newp = fresh_ptrname ptr_count in
            let st' = extend_storage st newp 1 (VInt n) in
            (st', newp)
    | EVar x ->
            let p = lookup_env env x in
            (st, p)
    | EBin(op, e1, e2) ->
            let (st1, p1) = eval st env e1 in
            let (st2, p2) = eval st1 env e2 in
            let Ptr(_,_,v1) = lookup_storage st2 p1 in
            let n1 = match v1 with
                     | VInt n -> n
                     | _ -> failwith ("lhs of addition is not an integer") in
            let Ptr(_,_,v2) = lookup_storage st2 p2 in
            let n2 = match v2 with
                     | VInt n -> n
                     | _ -> failwith ("rhs of addition is not an integer") in
            let pname = fresh_ptrname ptr_count in
            let v = match op with
                    | "+" -> VInt (n1 + n2)
                    | "-" -> VInt (n1 - n2)
                    | _ -> failwith (sprintf "unsupported binary operation %s" op) in
            let st3 = rc_dec st2 p1 in
            let st4 = rc_dec st3 p2 in
            (extend_storage st4 pname 1 v, pname)
    | EIsZero(e) ->
            let (st1, p) = eval st env e in
            let Ptr(_,rc,v) = lookup_storage st1 p in
            let n = match v with
                    | VInt n -> n
                    | _ -> failwith ("iszero has non-integer argument") in
            printf "\t---IsZero: RC ("; print_expr e; printf ") = %d\n" rc;
            let pname = fresh_ptrname ptr_count in
            let st2 = rc_dec st1 p in
            if n = 0 then
                (extend_storage st2 pname 1 (VInt 1), pname)
            else
                (extend_storage st2 pname 1 (VInt 0), pname)
    | ELambda(x, e1) ->
            let newp = fresh_ptrname ptr_count in
            (* XXX do we need to copy env? *)
            let st' = extend_storage st newp 1 (VClousure(ELambda(x, e1), env)) in
            (st', newp)
    | ECond(e1, e2, e3) ->
            let (st1, p1) = eval st env e1 in
            let Ptr(_,_,v) = lookup_storage st1 p1 in
            let n = match v with
                    | VInt n -> n
                    | _ -> failwith ("non-integer result in the condition predicate") in
            let st2 = rc_dec st1 p1 in
            if n = 0 then
                let st3 = inc_branch_fv_rc st2 env e3 in
                let (st4, p) = eval st3 env e3 in
                let st5 = dec_cond_fv_rc st4 env exp in
                (st5, p)
            else
                let st3 = inc_branch_fv_rc st2 env e2 in
                let (st4, p) = eval st3 env e2 in
                let st5 = dec_cond_fv_rc st4 env exp in
                (st5, p)
    | EApply(e1, e2) ->
            printf "  App --> "; print_expr exp; printf "\n";
            let (st1, p1) = eval st env e1 in
            let (st2, p2) = eval st1 env e2 in
            printf "  -0-> "; print_storage st2; printf "\n";
            let Ptr(_,_,v1) = lookup_storage st2 p1 in
            let (e', env') = match v1 with
                             | VClousure(e', env') -> (e', env')
                             | _ -> failwith ("lhs of apply is not a lambda abstraction") in
            let (x, ebody) = match e' with
                             | ELambda(x, ebody) -> (x, ebody)
                             | _ -> failwith ("closure does not contain lambda abstraction") in
            let env'' = extend_env env' x p2 in
            (* immediate uses and captures (function is called capture, but computes both) *)
            let st3 = inc_func_arg_rc st2 p2 x ebody in
            (* update free variables that will be used immediately in the body *)
            let st4 = inc_func_fv_rc st3 env' x ebody in
            printf "  -1-> "; print_storage st4; printf "\n";
            let st5 = rc_dec st4 p1 in
            let (st6, p3) = eval st5 env'' ebody in
            printf "  -2-> "; print_storage st6; printf "\n\n";
            (st6, p3)
    | ELetRec(x, e1, e2) ->
            let pname = fresh_ptrname ptr_count in
            let env' = extend_env env x pname in
            let (st1, p1) = eval st env' e1 in
            let st2 = update_letrec_pointer st1 pname p1 in
            let st3 = inc_func_arg_rc st2 p1 x e2 in
            let (st4, p3) = eval st3 (extend_env env x p1) e2 in
            printf "  -LR-> "; print_storage st3; printf "\n\n";
            (st4, p3)

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
let prog08 = "letrec f = \\x.if iszero x then x else f (x-1) in f 4"
let prog09 = "(\\x.\\y.\\z.\\w.x + x + x) 2 3 4"
let prog10 = "(\\x.\\y.x + (\\z.1) (\\w.x+x+x)) 2 3"
let prog11 = "(\\f.\\x.f 1) ((\\f.\\x.f 1) ((\\x.\\y.x) 2))"
let prog12 = "(\\x.\\y. if iszero (x+x+x) then x + x + x else x) 1 2"
let prog13 = "(\\x.\\y. if iszero (x) then (\\z.y) (x + x + x) else x) 0 2"
let prog14 = "(\\x.\\y. if iszero (x) then if x then x + x + x else 0 else x) 0 2"
let prog15 = "(letrec f = \\x.if iszero x then 5 else f (x-1) in \\x.f x) 0"
let prog16 = "letrec f = \\x.f x in (\\x.1) f "
let prog17 = "(\\z.letrec f = \\x.f x in (\\x.1) f) 3"
let prog18 = "letrec f = \\x.x+1 in f  3"
let prog19 = "(\\g.\\x.g x) (letrec f = \\x.x+1 in f)  3"
let prog20 = "(\\g.\\x.g x) (letrec f = \\x.if iszero x then x else x + (f (x-1)) in f)  3"
let prog21 = "letrec f = \\x.f x in 5"
let prog22 = "letrec f = \\x.if iszero x then x else f (x-1) in f 1 + f 1"
let prog23 = "(\\f.(f 1)) ((\\x.\\y.iszero x) 2)"

let prog = prog20

let v = parse_expr (lex (Stream.of_string prog));;
print_expr v;;
printf "\n"

let t = eval empty_storage empty_env v;;
match t with | (st, pname) ->
    print_storage st;
    printf "; %s\n" pname ;;
