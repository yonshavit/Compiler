(*
 * A compiler from Scheme to CISC
 *
 * Programmer: Yonatan Shavit and Mirabelle Herscu, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec annotate_lexical e scope params =
  match e with
  | Const(c) -> Const'(c)
  | Var(s) -> annotate_lexical_var e scope params s
  | If(test, caseT, caseF) -> If'(annotate_lexical test scope params, annotate_lexical caseT scope params, annotate_lexical caseF scope params)
  | Seq(s) -> Seq'(annotate_lexical_list s scope params)
  | Set(e_var, e_val) -> Set'(annotate_lexical e_var scope params, annotate_lexical e_val scope params)
  | Def(e_var, e_val) -> Def'(annotate_lexical e_var scope params, annotate_lexical e_val scope params)
  | Or(s) -> Or'(annotate_lexical_list s scope params)
  | LambdaSimple(lambda_params, body) -> LambdaSimple'(lambda_params, annotate_lexical body (params::scope) lambda_params)
  | LambdaOpt(lambda_params, opt, body) -> LambdaOpt'(lambda_params, opt, annotate_lexical body ((params@[opt])::scope) (lambda_params@[opt]))
  | Applic(proc, args) -> Applic'(annotate_lexical proc scope params, annotate_lexical_list args scope params)

and annotate_lexical_var e scope params s =
  if (is_param s params)
  then Var'(VarParam(s, get_index s params 0))
  else (let major = get_major s scope 0 in
        let minor = get_minor s scope in
        if (major < 0 || minor < 0)
        then Var'(VarFree(s))
        else Var'(VarBound(s, major, minor)))
and is_param s params =
  match params with
  | [] -> false
  | _ -> List.exists (fun x -> x = s) params

and get_index s params index =
  match params with
  | [] ->  -1
  | l -> if (List.hd l = s)
          then index
          else get_index s (List.tl l) index+1

and get_major s scope index =
  match scope with
  | [] ->  -1
  | l -> if (is_param s (List.hd l))
          then index
          else get_major s (List.tl l) index+1

and get_minor s scope =
  match scope with
  | [] -> -1
  | l -> if (is_param s (List.hd l))
          then get_index s (List.hd l) 0
          else get_minor s (List.tl l)

and annotate_lexical_list s scope params =
  List.map (fun e -> annotate_lexical e scope params) s;;

let rec annotate_tail e tail =
  match e with
  | Const'(s) -> e
  | Var'(s) -> e
  | If'(test, caseT, caseF) -> If'(annotate_tail test false, annotate_tail caseT tail, annotate_tail caseF tail)
  | Seq'(s) -> Seq'(annotate_tail_list s tail)
  | Set'(e_var, e_val) -> Set'(e_var, annotate_tail e_val false)
  | Def'(e_var, e_val) -> Def'(e_var, annotate_tail e_val false)
  | Or'(s) -> Or'(annotate_tail_list s tail)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, annotate_tail body true)
  | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, annotate_tail body true)
  | Applic'(proc, args) -> if tail
                            then ApplicTP'(annotate_tail proc false, List.map (fun x -> annotate_tail x false) args)
                            else Applic'(annotate_tail proc false, List.map (fun x -> annotate_tail x false) args)
  | _ -> raise X_syntax_error

  and annotate_tail_list e tail =
  match e with
  | [] -> []
  | l -> if ((List.tl l) = [])
          then [annotate_tail (List.hd l) true]
          else (annotate_tail (List.hd l) false) :: (annotate_tail_list (List.tl l) tail);;

let get_name_of_var v =
  match v with
  | Var'(VarFree(s)) -> s
  | Var'(VarParam(s, i)) -> s
  | Var'(VarBound(s, i1, i2)) -> s
  | _ -> raise X_syntax_error;;

let get_minor v =
  match v with
  | Var'(VarParam(s, i)) -> i
  | Var'(VarBound(s, i1, i2)) -> i2
  | _ -> raise X_syntax_error;;

let rec no_read l id =
  if (l = [])
  then []
  else ( let good_list = (List.filter (fun x -> if (x = []) then false else true) l) in
    List.map (fun x -> id::x) good_list);;

let rec checky_boxy_gety e v id =
  match e with
  | Var'(s) -> if((get_name_of_var v) = (get_name_of_var e))
                then [[id]]
                else []
  | Box'(s) -> checky_boxy_gety (Var'(s)) v id
  | BoxSet'(s, exp) -> checky_boxy_gety exp v id
  | If'(test, caseT, caseF) -> let catenated = [test]@[caseT]@[caseF] in
                                List.concat (handle_seq catenated 0 v)
  (* ((checky_boxy_gety test v id)@(checky_boxy_gety caseT v id)@(checky_boxy_gety caseF v id))  *)
  | Seq'(l) -> (List.concat (handle_seq l 0 v))
  | Set'(e_var, e_val) -> (checky_boxy_gety e_val v id)
  | Def'(e_var, e_val) -> (checky_boxy_gety e_val v id)
  | Or'(l) -> List.concat (List.map (fun x -> (checky_boxy_gety x v id) ) l)
  | LambdaSimple'(params, body) -> if (is_param (get_name_of_var v) params)
                                    then []
                                    else no_read (checky_boxy_gety body v 0) id
  | LambdaOpt'(params, opt, body) -> if (is_param (get_name_of_var v) (opt::params) )
                                      then []
                                      else no_read (checky_boxy_gety body v 0) id
  | Applic'(proc, args) -> let catenated = proc::args in
                            List.concat (handle_seq catenated 0 v)
   (* (List.append (checky_boxy_gety proc v id) (List.concat (List.map (fun x -> checky_boxy_gety x v id) args )))  *)
  | ApplicTP'(proc, args) -> let catenated = proc::args in
                              List.concat (handle_seq catenated 0 v)
   (* (List.append (checky_boxy_gety proc v id) (List.concat (List.map (fun x -> checky_boxy_gety x v id) args )))  *)
  | _ -> []

and is_param s params =
    match params with
    | [] -> false
    | _ -> List.exists (fun x -> x = s) params

and handle_seq l i v =
  match l with
  | [] -> []
  | hd::tl -> match hd with
              | LambdaSimple'(params, body) -> (checky_boxy_gety (List.hd l) v i)::(handle_seq (List.tl l) (i+1) v)
              | LambdaOpt'(params, opt, body) -> (checky_boxy_gety (List.hd l) v i)::(handle_seq (List.tl l) (i+1) v)
              | _ -> (checky_boxy_gety (List.hd l) v 0)::(handle_seq (List.tl l) i v);;

let rec checky_boxy_sety e v id =
  match e with
  | BoxSet'(s, exp) -> checky_boxy_sety exp v id
  | If'(test, caseT, caseF) -> let catenated = [test]@[caseT]@[caseF] in
                                List.concat (handle_seq catenated 0 v)
  (* ((checky_boxy_sety test v id)@(checky_boxy_sety caseT v id)@(checky_boxy_sety caseF v id))  *)
  | Seq'(l) -> (List.concat (handle_seq l 0 v))
  | Set'(e_var, e_val) -> let res = checky_boxy_sety e_val v id in
                          if((get_name_of_var v) = (get_name_of_var e_var))
                          then res@[[id]]
                          else res
  | Def'(e_var, e_val) -> (checky_boxy_sety e_val v id)
  | Or'(l) -> List.concat (List.map (fun x -> (checky_boxy_sety x v id) ) l)
  | LambdaSimple'(params, body) -> if (is_param (get_name_of_var v) params)
                                    then []
                                    else no_read (checky_boxy_sety body v 0) id
  | LambdaOpt'(params, opt, body) -> if (is_param (get_name_of_var v) (opt::params) )
                                      then []
                                      else no_read (checky_boxy_sety body v 0) id
  | Applic'(proc, args) ->  let catenated = proc::args in
                            List.concat (handle_seq catenated 0 v)
  (* (List.append (checky_boxy_sety proc v id) (List.concat (List.map (fun x -> checky_boxy_sety x v id) args )))  *)
  | ApplicTP'(proc, args) -> let catenated = proc::args in
                              List.concat (handle_seq catenated 0 v)
  (* (List.append (checky_boxy_sety proc v id) (List.concat (List.map (fun x -> checky_boxy_sety x v id) args )))  *)
  | _ -> []

and is_param s params =
    match params with
    | [] -> false
    | _ -> List.exists (fun x -> x = s) params

and handle_seq l i v =
  match l with
  | [] -> []
  | hd::tl -> match hd with
              | LambdaSimple'(params, body) -> (checky_boxy_sety (List.hd l) v i)::(handle_seq (List.tl l) (i+1) v)
              | LambdaOpt'(params, opt, body) -> (checky_boxy_sety (List.hd l) v i)::(handle_seq (List.tl l) (i+1) v)
              | _ -> (checky_boxy_sety (List.hd l) v i)::(handle_seq (List.tl l) i v);;

let wrapper_get e v =
  match e with
    | LambdaSimple'(params, body) -> no_read (checky_boxy_gety body v 0) (-1)
    | LambdaOpt'(params, opt, body)->  no_read (checky_boxy_gety body v 0) (-1)
    | _ -> raise X_syntax_error;;

let wrapper_set e v =
  match e with
    | LambdaSimple'(params, body) -> no_read (checky_boxy_sety body v 0) (-1)
    | LambdaOpt'(params, opt, body)->  no_read (checky_boxy_sety body v 0) (-1)
    | _ -> raise X_syntax_error;;

let rec make_get_set e v scope =
  match e with
  | Var'(s) -> (match_var_get e s v scope)
  | BoxSet'(e_var, exp) -> BoxSet'(e_var, (make_get_set exp v scope))
  | If'(test, caseT, caseF) -> If'((make_get_set test v scope), (make_get_set caseT v scope), (make_get_set caseF v scope))
  | Seq'(l) -> Seq'((List.map (fun x -> make_get_set x v scope) l))
  | Set'(e_var, e_val) -> match_var_set e e_var e_val v scope
  | Def'(e_var, e_val) -> Def'(e_var, make_get_set e_val v scope)
  | Or'(l) -> Or'((List.map (fun x -> make_get_set x v scope) l))
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (make_get_set body v (scope + 1)))
  | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, (make_get_set body v (scope + 1)))
  | Applic'(proc, args) -> Applic'((make_get_set proc v scope), (List.map (fun x -> make_get_set x v scope) args))
  | ApplicTP'(proc, args) -> ApplicTP'((make_get_set proc v scope), (List.map (fun x -> make_get_set x v scope) args))
  | _ -> e

and match_var_get e s v scope =
    match s with
      | VarParam(str, i) -> if ((expr'_eq e v) && (scope=(-1)))
                            then BoxGet'(s)
                            else e
      | VarBound(str, i1, i2) -> if ((i1 = scope) && (str = (get_name_of_var v)) && (i2 = (get_minor v)))
                                  then BoxGet'(s)
                                  else e
      | _ -> e

and match_var_set e e_var e_val v scope =
    match e_var with
    | Var'(VarParam(str, i)) -> if ((expr'_eq e_var v) && (scope=(-1)))
          then BoxSet'(VarParam(str, i), (make_get_set e_val v scope))
          else Set'(e_var, (make_get_set e_val v scope))
    | Var'(VarBound(str, i1, i2)) -> if ((i1 = scope) && (str = (get_name_of_var v)) && (i2 = (get_minor v)))
          then BoxSet'(VarBound(str, i1, i2), (make_get_set e_val v scope))
          else Set'(e_var, (make_get_set e_val v scope))
    | _ -> Set'(e_var, (make_get_set e_val v scope));;

let folding_has_ancestor l1 l2 = List.fold_left (fun acc curr -> if ((acc = false) && ((List.hd l1) = (List.hd curr)) && ((List.length l1) > 1) && ((List.length curr) > 1))
                                                                  then true
                                                                  else acc) false l2;;

let has_no_ancestor l1 l2 =
  let tail_l1 = List.map (fun l -> List.tl l) l1 in
  let tail_l2 = List.map (fun l -> List.tl l) l2 in
  let res = List.fold_left (fun acc curr -> if((folding_has_ancestor curr tail_l2) && (acc = false))
                                  then false
                                  else true) true tail_l1 in
  res;;

let rec true_if_common_ancester_pair cart_pair =
  let (l1,l2) = cart_pair in
  if (l1 = [] || l2 = [])
    then false
    else (if ((List.hd l1 = List.hd l2) && (List.length l1 >1) && (List.length l2 > 1))
                    then true
                    else false);;

let rec new_has_ancestor cart =
  match cart with
  | [] -> true
  | _ -> let l1 = List.tl (fst(List.hd cart)) in
          let l2 = List.tl (snd(List.hd cart)) in
          let res = true_if_common_ancester_pair (l1, l2) in
          res && new_has_ancestor (List.tl cart);;

let should_box e v =
  let get_list = wrapper_get e v in
  let set_list = wrapper_set e v in
  if ((get_list = []) || (set_list = []))
  then false
  else let curated_get = (List.fold_left (fun acc curr -> if (List.mem curr set_list)
                                        then acc
                                        else curr::acc) [] get_list) in
        let curated_set = (List.fold_left (fun acc curr -> if (List.mem curr get_list)
                                                            then acc
                                                            else curr::acc) [] set_list) in
        if ((curated_get = []) || (curated_set = []))
        then false
        else if ((has_no_ancestor curated_get curated_set) && (has_no_ancestor curated_set curated_get))
              then true
              else false;;

let rec loop_primitives l1 l2 = if (l1 = [] && l2 = [])
                                then true
                                else (if (l1 = [] || l2 = [])
                                then false
                                else (if ((List.hd l1) = (List.hd l2))
                                then loop_primitives (List.tl l1) (List. tl l2)
                                else false));;

let rec loop l1 l2 = if (loop_primitives (List.hd l1) (List.hd l2))
                then (if (l1 = [] && l2 = [])
                      then true
                      else loop (List.tl l1) (List. tl l2))
                else false;;

let route_eq (list1,list2) = loop_primitives list1 list2;;

let check_couples_true_if_should_boxed cart =
  List.fold_left (fun acc curr -> if (route_eq curr)
                                    then (acc || false)
                                     else true) false cart;;

let negative_couples cart = List.fold_left (fun acc curr -> if (route_eq curr)
                                                            then acc
                                                            else curr::acc) [] cart;;

let should_box_ver_2 e v =
  let get_list = wrapper_get e v in
  let set_list = wrapper_set e v in
  if ((get_list = []) || (set_list = []))
  then false
  else (let cart = List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) set_list) get_list) in (*Swapped the list removal into cartsian product.*)
        let neg = negative_couples cart in
        if (neg = [])
        then false
        else  (let bla = new_has_ancestor neg in
                if (bla)
                        (* if ((has_no_ancestor curated_get curated_set) && (has_no_ancestor curated_set curated_get)) *)
                then false
                else true));;


let rec create_vars params index =
  match params with
  | [] -> []
  | _ -> (Var'(VarParam((List.hd params), index))::(create_vars (List.tl params) (index+1)));;

let rec change_getset_body e vlist =
  match vlist with
  | [] -> e
  | _ -> if ((snd (List.hd vlist)) = true)
          then change_getset_body (make_get_set e (fst (List.hd vlist)) (-1)) (List.tl vlist)
          else change_getset_body e (List.tl vlist);;

let get_var e =
  match e with
  | Var'(v) -> v
  | _ -> raise X_syntax_error;;

let is_false l =
  List.fold_left (fun acc curr -> acc || (snd curr)) false l;;

let autobox_lambda e =
  match e with
  | LambdaSimple'(params, body) -> let var_params = create_vars params 0 in
                                    let should_boxed_list = List.map (fun v -> (v, should_box_ver_2 e v)) var_params in
                                    if (is_false should_boxed_list)
                                    then
                                    (let boxing_seq = List.fold_left (fun acc curr -> if(snd curr)
                                                                                      then acc@[Set'((fst curr), Box'(get_var (fst curr)))]
                                                                                      else acc) [] should_boxed_list in
                                    let changed_body = change_getset_body body should_boxed_list in
                                    let real_seq = Seq'((boxing_seq)@[changed_body]) in
                                    LambdaSimple'(params, real_seq))
                                    else e
  | LambdaOpt'(params, opt, body) -> let var_params = (create_vars (params@[opt]) 0) in
                                      let should_boxed_list = List.map (fun v -> (v, should_box_ver_2 e v)) var_params in
                                      if (is_false should_boxed_list)
                                      then (let boxing_seq = List.fold_left (fun acc curr -> if(snd curr)
                                                                                        then acc@[Set'((fst curr), Box'(get_var(fst curr)))]
                                                                                        else acc) [] should_boxed_list in
                                      let changed_body = change_getset_body body should_boxed_list in
                                      let real_seq = Seq'((boxing_seq)@[changed_body]) in
                                      LambdaOpt'(params, opt, real_seq))
                                      else e
  | _ -> e;;

let lambda_to_pair e =
  match e with
  | LambdaSimple'(params, body) -> (params, body)
  | _ -> raise X_syntax_error;;

let lambda_to_tuple e =
  match e with
  | LambdaOpt'(params, opt, body) -> (params, opt, body)
  | _ -> raise X_syntax_error;;

let rec wrapper_box e =
  match e with
  | BoxSet'(v, exp) -> BoxSet'(v, wrapper_box exp)
  | If'(test, caseT, caseF) -> If'(wrapper_box test, wrapper_box caseT, wrapper_box caseF)
  | Seq'(l) -> Seq'(handle_seq l)
  | Set'(e_var, e_val) -> Set'(e_var, wrapper_box e_val)
  | Def'(e_var, e_val) -> Def'(e_var, wrapper_box e_val)
  | Or'(l) -> Or'(handle_seq l)
  | LambdaSimple'(params, body) -> let (new_params, new_body) = lambda_to_pair(autobox_lambda e) in
                                    LambdaSimple'(new_params, wrapper_box new_body)
  | LambdaOpt'(params, opt, body) -> let (new_params, new_opt, new_body) = lambda_to_tuple(autobox_lambda e) in
                                      LambdaOpt'(new_params, new_opt, wrapper_box new_body)
  | Applic'(proc, args) -> Applic'(wrapper_box proc, handle_seq args)
  | ApplicTP'(proc, args) -> ApplicTP'(wrapper_box proc, handle_seq args)
  | _ -> e

and handle_seq l =
  List.map (fun e -> wrapper_box e) l;;

let annotate_lexical_addresses e = annotate_lexical e [] [];;

let annotate_tail_calls e = annotate_tail e false;;

let box_set e = wrapper_box e;;

let run_semantics expr =
  box_set
    ( annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)