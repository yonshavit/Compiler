(*
TODO:
quasiquote
mit - add dot support
*)

(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Yonatan Shavit and Mirabelle Herscu, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

  let rec expr_eq e1 e2 =
    match e1, e2 with
    | Const Void, Const Void -> true
    | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
    | Var(v1), Var(v2) -> String.equal v1 v2
    | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                              (expr_eq th1 th2) &&
                                                (expr_eq el1 el2)
    | (Seq(l1), Seq(l2)
      | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
    | (Set(var1, val1), Set(var2, val2)
      | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                               (expr_eq val1 val2)
    | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
    | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
       (String.equal var1 var2) &&
         (List.for_all2 String.equal vars1 vars2) &&
           (expr_eq body1 body2)
    | Applic(e1, args1), Applic(e2, args2) ->
       (expr_eq e1 e2) &&
         (List.for_all2 expr_eq args1 args2)
    | _ -> false;;
	
let expr_eq_int e1 e2 = if expr_eq e1 e2
                        then 0
                        else 1;;

exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let rec _make_list_loop_ sexprlist = match sexprlist with
                | Nil -> []
                | Pair(car, cdr) -> car :: _make_list_loop_ cdr
                | _ -> raise X_syntax_error;;

let rec list_to_pair l = match l with
                        | [] -> Nil
                        | _ -> Pair((List.hd l), (list_to_pair (List.tl l)))

let pair_to_ocaml_pair p =
  match p with
  | Pair(car, cdr) -> (car, cdr)
  | Nil -> (Nil, Nil)
  | _ -> raise X_this_should_not_happen;;

let rec separate_args_values listoflists =
  match listoflists with
  | Nil -> (Nil, Nil)
  | Pair(Pair(arg_sexpr, Pair(value_sexpr, Nil)), cdr) -> let (separated_args, separated_values) = separate_args_values cdr in
                                                             (Pair(arg_sexpr, separated_args), Pair(value_sexpr, separated_values))
  | _ -> raise X_syntax_error;;

let rec makey_argy_funcy (args, values, body) =
  match args with
    | Nil-> body
    | Pair(car_args, cdr_args) -> let (car_values, cdr_values) = pair_to_ocaml_pair values in
                                    Pair(Pair(Symbol("set!"),Pair(car_args,Pair(car_values,Nil))),makey_argy_funcy (cdr_args, cdr_values, body))
    | _-> raise X_syntax_error;;

let rec whatever_generator args =
  match args with
  | Nil-> Nil
  | Pair(car_args, cdr_args) -> Pair(Pair(car_args, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), (whatever_generator cdr_args))
  | _-> raise X_syntax_error;;

let expand_let args body =
  let (separated_args, separated_values) = separate_args_values args in
  Pair(Pair(Symbol("lambda"), Pair(separated_args, body)), separated_values);;


let expand_let_star args body =
  let (separated_args, separated_values) = separate_args_values args in
  let (first_arg, args_cdr) = pair_to_ocaml_pair separated_args in
  let (first_val, vals_cdr) = pair_to_ocaml_pair separated_values in
  match args with
  | Nil -> Pair(Symbol("let"), Pair(Nil, body)) (*base case*)
  | Pair(car_args, Nil) -> Pair(Symbol("let"),(*This is our recursive case*)
                                        Pair
                                        (Pair (Pair (first_arg, Pair(first_val,Nil)),
                                        Nil),
                                        body))
  | Pair(car_args, cdr_args) -> Pair(Symbol("let"),(*This is our recursive case*)
                                            Pair
                                            (Pair (Pair (first_arg, Pair(first_val,Nil)),
                                            Nil),
                                            Pair(Pair(Symbol("let*"), Pair(cdr_args, body)),Nil)))
  | _ -> raise X_syntax_error;;

let expand_letrec args body =
  let (separated_args, separated_values) = separate_args_values args in
  Pair(Symbol("let"), Pair((whatever_generator separated_args), makey_argy_funcy (separated_args, separated_values, body)));;
 
let expand_and sexpr =
  match sexpr with
  | Nil -> Bool(true)
  | Pair(car, Nil) -> car
  | Pair(car, cdr) -> Pair(Symbol("if"), Pair(car, Pair(Pair(Symbol("and"), cdr), Pair (Bool(false), Nil))))
  | _ -> raise X_syntax_error;;

let rec expand_quasiquote sexpr = match sexpr with
 | Symbol(x) -> Pair(Symbol "quote", Pair(Symbol(x), Nil))
 | Pair(Symbol("quote"), Pair(x, Nil)) -> Pair(Symbol("cons"), Pair(Pair(Symbol("quote"), Pair(Symbol("quote"), Nil)), Pair(Pair(Symbol("cons"), Pair(Pair(Symbol("quote"), Pair(x, Nil)), Pair(Pair(Symbol("quote"), Pair(Nil, Nil)), Nil))), Nil)))
 (* Pair(Symbol("cons"), Pair(Pair(Pair (Symbol "quote", Pair (Symbol "quote", Nil)), Pair(Symbol("cons"), Nil)), Pair(Pair(x, Pair(Pair(Symbol("quote"), Pair(Nil, Nil)), Nil)), Nil))) *)
 | Pair(Symbol "unquote", Pair(x, Nil))-> x
 | Pair(Symbol "unquote-splicing", Pair(x, Nil))-> raise X_syntax_error
 | Vector(l) -> Pair(Symbol("vector"), (list_to_pair(List.map expand_quasiquote l)))

 | Pair(car, cdr) -> quasiquote_list_func sexpr
 | _ -> sexpr

and quasiquote_list_func sexpr = match sexpr with
  | Nil -> Pair (Symbol "quote", Pair (Nil, Nil))
  | Pair(car,cdr)-> (match (car,cdr) with
                        | (Pair(Symbol("unquote-splicing"), Pair (carsex, Nil)),_)-> Pair(Symbol("append"), Pair(carsex, (expand_quasiquote cdr)))
                        | (_, Pair(Symbol("unquote-splicing"), Pair (cdrsex, Nil)))-> Pair((expand_quasiquote car), Pair(Symbol("append"), cdrsex))
                        | _ -> (Pair(Symbol("cons"), Pair((expand_quasiquote car), Pair((expand_quasiquote cdr), Nil)))))
  | _ -> raise X_syntax_error;;
  
let rec expand_cond ribs_list =
  match ribs_list with
  | Pair(Pair(test, Pair(Symbol("=>"), body)), Nil) -> let if_expr = Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))) in
                                                        let lambda_expr = Pair(Symbol("lambda"), Pair(Nil, body)) in
                                                        let args = Pair(Pair(Symbol("value"), Pair(test, Nil)),
                                                                    Pair(Pair(Symbol("f"), Pair(lambda_expr, Nil)), Nil)) in
                                                        Pair(Symbol("let"), Pair(args, Pair(if_expr, Nil)))
  | Pair(Pair(test, Pair(Symbol("=>"), body)), rest_ribs) ->  let res = expand_cond rest_ribs in
                                                              let ribs = (match res with
                                                                        | Nil -> Nil
                                                                        | _ -> Pair(res, Nil) )in
                                                              let rest = Pair(Symbol("lambda"), Pair(Nil, ribs)) in
                                                              let if_expr = Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))) in
                                                              let lambda_expr = Pair(Symbol("lambda"), Pair(Nil, body)) in
                                                              let args = Pair(Pair(Symbol("value"), Pair(test, Nil)),
                                                                          Pair(Pair(Symbol("f"), Pair(lambda_expr, Nil)),
                                                                          Pair(Pair(Symbol("rest"), Pair(rest, Nil)), Nil))) in
                                                              Pair(Symbol("let"), Pair(args, Pair(if_expr, Nil)))
  | Pair(Pair(Symbol("else"), body), Nil) -> Pair(Symbol("begin"), body)
  | Pair(Pair(test, body), rest_ribs) -> let res = expand_cond rest_ribs in
                                          let ribs = match res with
                                                    | Nil -> Nil
                                                    | _ -> Pair(res, Nil) in
                                                    Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), body), ribs)))
  | Nil -> Nil
  | _ -> raise X_syntax_error;;

let expand_mitdefine var args body =
  let exp = Pair(Symbol("lambda"), Pair(args, body)) in
  Pair(Symbol("define"), Pair(var, Pair(exp,Nil)));;

let rec _expr_ sexp = match sexp with
                      (* 3.2.1.1 CONST *)
                      | Pair(Symbol("quote"),Pair(x,Nil)) -> Const(Sexpr(x))
                      | Bool(x) -> Const(Sexpr(Bool(x)))
                      | Number(x) -> Const(Sexpr(Number(x)))
                      | Char(x) -> Const(Sexpr(Char(x)))
                      | String(x) -> Const(Sexpr(String(x)))
                      | Nil -> Const(Sexpr(Nil))
                      | Vector(l) -> Const(Sexpr(Vector(l)))
                      (* 3.2.1.2 VARIABLE *)
                      | Symbol(x) -> if (List.mem x reserved_word_list)
                                      then raise X_syntax_error
                                      else Var(x)
                      (* 3.2.1.3 CONDITIONALS *)
                      (* if-else *)
                      | Pair(Symbol("if"), Pair(pred, Pair(caseT,Pair (caseF,Nil)))) -> If((_expr_ pred) , (_expr_ caseT), (_expr_ caseF))
                      (* if *)
                      | Pair(Symbol("if"), Pair(pred, Pair(caseT,Nil))) -> If((_expr_ pred), (_expr_ caseT), (Const(Void)))
                      (* 3.2.1.4 LAMBDA *)
                      | Pair(Symbol("lambda"), Pair(args, body)) -> if (sexpr_eq body Nil)
                                                                    then raise X_syntax_error
                                                                    else (if (_check_unique2 args)
                                                                          then _make_lambda_ args body
                                                                          else raise X_syntax_error)
                      (* 3.2.1.6 DISJUNCTION *)
                      | Pair(Symbol("or"), Nil) -> _expr_ (Bool(false))
                      | Pair(Symbol("or"), Pair(x, Nil)) -> _expr_ x
                      | Pair(Symbol("or"), sexprs) -> Or(List.map _expr_ (_make_list_loop_ sexprs))
                      (* 3.2.1.8 ASSIGNMENT *)
                      | Pair(Symbol("set!"), Pair(Symbol(x), Pair(y, Nil))) -> Set(_expr_ (Symbol(x)), _expr_ y)
                      (* 3.2.1.9 SEQUENCE *)
                      (* empty explicit sequence *)
                      | Pair(Symbol("begin"), Nil) -> Const(Void)
                      (* explicit sequence *)
                      (* one element should be returned as Var *)
                      | Pair(Symbol("begin"), Pair(x, Nil)) -> _expr_ x
                      | Pair(Symbol("begin"), rest) -> if (verify_nil_terminated rest)
                                                        then _make_sequence_ rest
                                                        else raise X_syntax_error
                      (* 3.2.1.7 DEFINITION *)
                      | Pair(Symbol("define"), Pair(Symbol(name), Pair(exp, Nil))) -> Def(_expr_ (Symbol(name)), _expr_ exp)
                      | Pair(Symbol("define"), Pair(Pair(Symbol(var), args), body)) -> _expr_ (expand_mitdefine (Symbol(var)) args body)
                      | Pair(Symbol("quasiquote"), Pair (Nil, Nil)) -> _expr_ (Pair(Symbol("quote"), Pair(Nil, Nil)))
                      | Pair(Symbol("quasiquote"), Pair(sexpr, Nil)) -> _expr_ (expand_quasiquote sexpr)
                      | Pair(Symbol("and"), sexpr) -> _expr_ (expand_and sexpr)
                      | Pair(Symbol("let"), Pair(args,body))-> _expr_ (expand_let args body)
                      | Pair(Symbol("let*"),Pair(args, body))-> _expr_ (expand_let_star args body)
                      | Pair(Symbol("letrec"), Pair(args,body))-> _expr_ (expand_letrec args body)
                      | Pair(Symbol("cond"), ribs_list) -> _expr_ (expand_cond ribs_list)
                      (* 3.2.1.5 APPLICATION
                      Parses the applicator as a symbol and then uses make_argslist_ which returns a list of parsed exprs.*)
                      | Pair(x, args) -> if(verify_nil_terminated args)
                                            then (Applic(_expr_ x, _make_argslist_ args))
                                            else raise X_syntax_error
                      (* | _ -> raise X_syntax_error *)
and verify_nil_terminated args =
  match args with
  | Nil -> true
  | Pair(car,cdr) -> (verify_nil_terminated cdr)
  | _ -> false

and _check_unique_ args =
  let _list_ = _make_argslist_ args in
  if (List.compare_lengths (List.sort_uniq expr_eq_int _list_ ) _list_) = 0
  then true
  else false

and _check_unique2 args =
    let _list_ = _make_argslist_ args in
    _check_unique_3 _list_

and _check_unique_3 _list_ =
match _list_ with
| [] -> true
| hd::tl -> if (List.mem hd tl)
            then false
            else _check_unique_3 tl

(* we distinguish between simple lambda and optional and variadic by the end,
if it ends with Nil it will be simple
if it ends with a symbol and the list is empty it's variadic
else its opt - notice that the last argument will be the first*)
and _make_lambda_ args body =
  let (s, last) = _find_end_ args in
  match (s, last) with
  | (_, Nil) -> LambdaSimple(s, _make_sequence_ body)
  | ([], Symbol(opt)) -> LambdaOpt(s, opt, _make_sequence_ body)
  | (_, Symbol(x)) -> LambdaOpt(s, x, _make_sequence_ body)
  | _ -> raise X_syntax_error

(*  *)
and _find_end_ somelist =
  match somelist with
  | Nil -> ([], Nil)
  | Symbol(x) -> ([], Symbol(x))
  | Pair(Symbol(car), Symbol(cdr)) -> ([car], Symbol(cdr))
  | Pair(Symbol(car), cdr) -> let (s, newcdr) = _find_end_ cdr in (car :: s, newcdr)
  | _ -> ([], somelist)

  (* takes an sexpr list in the form of nested pairs,
  turns it to a list of sexpr and with map applys _expr_ on each element
  we get an expr list and create Seq with it *)
and _make_sequence_ sexprlist = match sexprlist with
                              | Pair(x, Nil) -> _expr_ x
                              | _ -> Seq(_make_argslist_ sexprlist)

(*takes a list of sexrp args and returns a list of exprs after applying _expr_ to each element.*)
and _make_argslist_ args = match args with
                         | Nil -> []
                         | Symbol(x) -> [_expr_ (Symbol(x))]
                         | Pair(car, cdr) -> _expr_ car :: _make_argslist_ cdr
                         | _ -> raise X_syntax_error;;

let tag_parse_expression sexpr = _expr_ sexpr;;

let tag_parse_expressions sexpr = List.map _expr_ sexpr;;

end;; (* struct Tag_Parser *)