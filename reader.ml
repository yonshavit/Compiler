(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Yonatan Shavit and Mirabelle Herscu, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  (*3.2.1*)
(*type: (char list -> 'a * char list) -> char list -> 'a * char list = <fun> *)
(*ignores the spaces the returns only whats between them*)
let _delete_spaces_ parser =
  let _whitespaces_ = PC.star (PC.range (char_of_int 0) (char_of_int 32)) in
  PC.pack (PC.caten (PC.caten _whitespaces_ parser) _whitespaces_) (fun ((l, s), r) -> s);;

  let _space_ = 
    PC.pack (PC.nt_whitespace)
    (fun x -> Nil);;
  
(*3.3.3*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns a char that a symbol can contain. sensitive*)
let _symbol_char_ =
  PC.disj_list [PC.range (char_of_int 48) (char_of_int 57); (*0-9*)
                              PC.range (char_of_int 97) (char_of_int 122); (*a-z*)
                              PC.pack (PC.range (char_of_int 65) (char_of_int 90)) (fun (l) -> lowercase_ascii l);(*A-Z*)
                              PC.char '!';
                              PC.char '$';
                              PC.char '^';
                              PC.char '*';
                              PC.char '-';
                              PC.char '_';
                              PC.char '=';
                              PC.char '+';
                              PC.char '<';
                              PC.char '>';
                              PC.char '/';
                              PC.char ':';
                              PC.char '?'];;





(*3.3.3*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns Symbol that is constructed from a lisr of chars. can't be empty*)
let _symbol_ = PC.pack (_delete_spaces_ (PC.plus _symbol_char_)) (fun (s) -> Symbol(list_to_string(s)));;


(*3.3.1*)
(*type: char list -> sexpr * char list = <fun> *)
(*a parser that retruns true for #t and false for #f and constructs Bool *)
let _bool_ =
  let _true_ =  (PC.caten (_delete_spaces_ (PC.char '#')) (_delete_spaces_ (PC.char_ci 't'))) in
  let _false_ = (PC.caten (_delete_spaces_ (PC.char '#')) (_delete_spaces_ (PC.char_ci 'f'))) in
  PC.pack (PC.disj _true_ _false_)  (fun (l,r) -> match r with
                                                |'t' -> Bool(true)
                                                |'T' -> Bool(true)
                                                |'f' -> Bool(false)
                                                |'F' -> Bool(false)
                                                |_-> raise PC.X_no_match);;

(*3.3.5*)
(*type: char list -> (char * char) * char list = <fun> *)
(*a parser that retruns #\ for char prefix *)
let _char_prefix_ =
  PC.caten (PC.char '#') (PC.char '\\');;

(*3.3.2.1*)
(*type: char list -> (char * char) * char list = <fun> *)
(*a parser that retruns #x for hex prefix *)
let _hex_prefix_ =
  PC.caten (PC.char '#') (PC.char_ci 'x');;

(*3.3.5.2*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns char that is a char after space*)
let _visible_simple_char_ = (PC.range (char_of_int 33) (char_of_int 127));;

(*3.3.5.1*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns char that is a special chars*)
let _named_char_ =
  let _nul_ = PC.pack (PC.word_ci "nul")  (fun r -> char_of_int 0) in
  let _newline_ = PC.pack (PC.word_ci "newline") (fun r -> char_of_int 10) in
  let _return_ = PC.pack (PC.word_ci "return") (fun r -> char_of_int 13) in
  let _tab_ = PC.pack (PC.word_ci "tab") (fun r -> char_of_int 9) in
  let _page_ = PC.pack (PC.word_ci "page") (fun r -> char_of_int 12) in
  let _space_ = PC.pack (PC.word_ci "space") (fun r -> char_of_int 32) in
  (PC.disj_list [_nul_; _newline_; _return_; _tab_; _page_; _space_]);;

(*3.3.5.3*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns char list of hex digits*)
let _hex_digit_ = PC.disj_list [PC.range (char_of_int 48) (char_of_int 57); (*0-9*)
                                PC.range (char_of_int 97) (char_of_int 102); (*a-f*)
                                PC.range (char_of_int 65) (char_of_int 70)];; (*A-F*)
(*3.3.5.3*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns a hex char*)
let _hex_char_ =
  let _plus_hex_digit_ = PC.plus (_hex_digit_) in
    PC.pack (PC.caten (PC.char_ci 'x') _plus_hex_digit_) (fun (l,r) -> char_of_int(int_of_string("0x" ^ (list_to_string(r)))));;

(*3.3.5*)
(*type: char list -> sexpr * char list = <fun> *)
(*a parser that retruns Char constructed by a prefix and special char || hex char || visible char*)
let _char_ =
  let _cataneted_char_ = PC.caten (_delete_spaces_ _char_prefix_) (PC.disj_list [_named_char_; _hex_char_; _visible_simple_char_;]) in
  PC.pack (_cataneted_char_) (fun (l,r)-> Char(r));;

(*3.3.2*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns a digit*)
let _digit_ = PC.range (char_of_int 48) (char_of_int 57);;

(*3.3.2*)
(*type: char list -> char list * char list = <fun> *)
(*a parser that retruns a natural number*)
let _natural_ = PC.plus _digit_;;

(*3.3.2.1*)
(*type: char list -> char list * char list = <fun> *)
(*a parser that retruns a decimal integer*)
let _integer_ =
  let _plus_ = PC.char '+' in
  let _minus_ = PC.char '-' in
  PC.pack  (PC.caten (PC.maybe (PC.disj _minus_ _plus_)) _natural_) (fun (l,r) -> match l with
                                                                    | Some '-'-> '-' :: r
                                                                    | Some '+' -> '+' :: r
                                                                    | None -> r
                                                                    | _ -> raise PC.X_no_match);;



(*3.3.2.2*)
(*type: char list -> char list * char list = <fun> *)
(*a parser that retruns a decimal float*)
let _float_ =
  let _dot_ = PC.word "." in
  PC.pack (PC.caten_list [_integer_; _dot_; _natural_]) (fun (l) -> (List.concat l));;

(*3.3.2*)
(*type: char list -> char list * char list = <fun> *)
(*a parser that retruns a natural number in hex*)
let _hex_natural_ = PC.plus _hex_digit_;;

(*3.3.2.1*)
(*type: char list -> char list * char list = <fun> *)
(*a parser that retruns an integer in hex*)
let _hex_integer_ =
  let _plus_ = PC.char '+' in
  let _minus_ = PC.char '-' in
  let _hex_int_no_pre_ = PC.caten (PC.maybe (PC.disj _minus_ _plus_)) _hex_natural_ in
  PC.pack (PC.caten _hex_prefix_ _hex_int_no_pre_) (fun ((p,x),(l,r)) -> match l with
                                                                  | Some '-' -> '-' :: '0' :: x :: r
                                                                  | Some '+' -> '+' :: '0' :: x :: r
                                                                  | None -> '0' :: x :: r
                                                                  | _ -> raise PC.X_no_match);;

(*3.3.2.2*)
(*type: char list -> char list * char list = <fun> *)
(*a parser that retruns float in hex*)
let _hex_float_ =
  let _dot_ = PC.word "." in
  PC.pack (PC.caten_list [_hex_integer_; _dot_; _hex_natural_]) (fun (l) -> (List.concat l));;

(*4.4.1.*)
(*type: char list -> number * char list = <fun> *)
(*a parser that retruns a scientificly notated float*)
let _scientific_ =
  let _integer_or_float_ = PC.disj _float_ _integer_  in
  let _e_ = PC.word_ci "e" in
  PC.pack (PC.pack (PC.caten_list [_integer_or_float_; _e_; _integer_]) (fun (l) -> (List.concat l))) (fun (n) -> Float(float_of_string(list_to_string n)));;

(*3.3.2.1*)
let _some_integer_ = PC.pack (PC.disj _hex_integer_ _integer_) (fun (n) -> Int(int_of_string(list_to_string n)));;

(*3.3.2.2*)
let _some_float_ = PC.pack (PC.disj _hex_float_ _float_ ) (fun (n) -> Float(float_of_string(list_to_string n)));;

(*3.3.2*)
(*type: char list -> sexpr * char list = <fun> *)
(*a parser that retruns Number that can be either float or integer*)
let _number_ =
  PC.pack (_delete_spaces_ (PC.not_followed_by (PC.disj_list [_scientific_; _some_float_; _some_integer_])_symbol_char_)) (fun (n)-> Number(n));;

(*3.3.4.1*)
(*type: char list -> char * char list = <fun> *)
(*a parser that returns unseen chars *)
let _string_meta_char_ =
  let _backslash_ = PC.pack (PC.word_ci "\\\\")  (fun r -> char_of_int 92) in
  let _double_quote_ = PC.pack (PC.word_ci "\\\"") (fun r -> char_of_int 34) in
  let _tab_ = PC.pack (PC.word_ci "\\t") (fun r -> char_of_int 9) in
  let _page_ = PC.pack (PC.word_ci "\\f") (fun r -> char_of_int 12) in
  let _newline_ = PC.pack (PC.word_ci "\\n") (fun r -> char_of_int 10) in
  let _return_ = PC.pack (PC.word_ci "\\r") (fun r -> char_of_int 13) in
  (PC.disj_list [_double_quote_; _tab_; _page_; _newline_; _return_; _backslash_; ]);;

(*3.3.4*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns tany char other then backslash or quote*)
let _string_literal_char_ = PC.disj_list [PC.range (char_of_int 0) (char_of_int 33);
                            PC.range (char_of_int 35) (char_of_int 91);
                            PC.range (char_of_int 93) (char_of_int 127)];;

(*3.3.4.2*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns chars represented as hex ASCII*)
let _string_hex_char_ =
  let _hex_digit_plus_ = PC.plus _hex_digit_ in
  let _backslash_x_prefix_ = PC.word_ci "\\x" in
  let _suffix_ = PC.word ";" in
  PC.pack (PC.caten (PC.caten _backslash_x_prefix_ _hex_digit_plus_) _suffix_) (fun ((l,r), rr) -> (char_of_int (int_of_string (list_to_string ('0' :: 'x' :: r))))) ;;

(*3.3.4*)
(*type: char list -> char * char list = <fun> *)
(*a parser that retruns either literal, hex or meta char*)
let _string_char_ =
  PC.disj_list [_string_literal_char_;  _string_hex_char_; _string_meta_char_];;

(*3.3.4*)
(*type: char list -> sexpr * char list = <fun> *)
(*a parser that retruns String constructed by a list of chars*)
let _string_ =
  let _quote_ = (PC.word "\"") in 
  PC.pack (PC.caten (PC.caten _quote_ ( (PC.star _string_char_))) _quote_) (fun ((l, r), rr) -> String(list_to_string(r)));;


let _left_paren_ = _delete_spaces_ (PC.char '(');;

let _right_paren_ = _delete_spaces_ (PC.char ')');;

let _left_square_paren_ = _delete_spaces_ (PC.char '[');;

let _right_square_paren_ = _delete_spaces_ (PC.char ']');;

let _dot_char_ = _delete_spaces_ (PC.char '.');;

let _hashtag_ = _delete_spaces_ (PC.char '#');;

let _quote_ = _delete_spaces_ (PC.word "\'");;

let _quasi_quote_ = _delete_spaces_ (PC.word "`");;

let _unquote_ = _delete_spaces_ (PC.word ",");;

let _splice_ = _delete_spaces_ (PC.word ",@");;

let _closeall_ =  PC.word "...";;


(*3.3*)
(*type: char list -> sexpr * char list = <fun> *)
let rec _sexpr_ s = let _disjointed_sexprs_ = PC.disj_list [_bool_; _char_; _number_; _string_; _symbol_;  _list_; _dotted_list_; _vector_; _quoted_; _quasi_quoted_; _unquoted_; _unquoted_and_spliced_; _S_ ] in
  let _star_comment_ = PC.pack (PC.star _comment_) (fun (c) -> Nil) in
  let _shem_ = PC.pack (PC.caten (PC.caten _star_comment_ _disjointed_sexprs_) _star_comment_) (fun ((ll, lr), r) -> lr) in
  PC.pack (PC.caten _final_comment_ (PC.caten  _disjointed_sexprs_ _final_comment_)) (fun (l, (rl, rr)) -> rl) s

 (* PC.pack (PC.caten final_comment (PC.caten 
(PC.disj [_bool_; _char_; _number_; _string_; _symbol_;  _list_; _dotted_list_; _vector_; _quoted_; _quasi_quoted_; _unquoted_; _unquoted_and_spliced_; _S_ ]) final_comment)) (fun (_, (a,_ )) -> a) s *)

(*freaking ...*)

and _S_ s =
  (PC.pack (PC.caten (PC.disj_list [_packed_D_disjoint_; _packed_L_disjoint_; _packed_V_disjoint_]) (_delete_spaces_ _closeall_)) (fun (l,r) -> l)) s

and _D_ s =
  (PC.caten (PC.caten (PC.caten (PC.caten _left_paren_ (PC.plus _A_)) _dot_char_) _A_) (PC.maybe _right_paren_)) s

and _packed_D_ s =
  (PC.pack _D_ (fun (((((l, sexps), d), sexp), r)) -> List.fold_right (fun a b -> Pair(a, b)) sexps sexp)) s

and _D_square_ s =
  (PC.caten (PC.caten (PC.caten (PC.caten _left_square_paren_ (PC.plus _A_)) _dot_char_) _A_) (PC.maybe _right_square_paren_)) s

and _packed_D_square_ s =
  (PC.pack _D_square_ (fun (((((l, sexps), d), sexp), r)) -> List.fold_right (fun a b -> Pair(a, b)) sexps sexp)) s

and _packed_D_disjoint_ s =
 (PC.disj _packed_D_ _packed_D_square_) s

and _L_ s =
 (PC.caten (PC.caten _left_paren_ (PC.star _A_)) (PC.maybe _right_paren_)) s

and _packed_L_ s =
 (PC.pack _L_ (fun ((l, s), r) -> List.fold_right (fun a b -> Pair(a, b)) s Nil)) s

and _L_square_ s =
 (PC.caten (PC.caten _left_square_paren_ (PC.star _A_)) (PC.maybe _right_square_paren_)) s

and _packed_L_square_ s =
 (PC.pack _L_square_ (fun ((l, s), r) -> List.fold_right (fun a b -> Pair(a, b)) s Nil)) s

and _packed_L_disjoint_ s =
 (PC.disj _packed_L_ _packed_L_square_) s

and _V_ s =
 (PC.caten (PC.caten (PC.caten _hashtag_ _left_paren_) (PC.star _A_)) (PC.maybe _right_paren_)) s

and _packed_V_ s =
(PC.pack _V_ (fun ((((h, l), sexp), r)) -> Vector(sexp))) s

and _V_square_ s =
 (PC.caten (PC.caten (PC.caten _hashtag_ _left_square_paren_) (PC.star _A_)) (PC.maybe _right_square_paren_)) s

and _packed_V_square_ s =
 (PC.pack _V_square_ (fun ((((h, l), sexp), r)) -> Vector(sexp))) s

and _packed_V_disjoint_ s =
 (PC.disj _packed_V_ _packed_V_square_) s

and _A_ s =
 (PC.disj_list [(PC.diff _sexpr_ _S_); _packed_D_disjoint_; _packed_L_disjoint_; _packed_V_disjoint_]) s

(*3.3.6*)
(*type: char list -> sexpr * char list = <fun> *)
(*a parser that returns Nil*)
  and _nil_ s =
    let _star_comment_ = PC.pack (PC.star _comment_) (fun (c) -> Nil) in
    let _packed_nil_ = PC.pack (PC.caten (PC.caten _left_paren_ _star_comment_) _right_paren_) (fun ((l, c), r) -> Nil) in
    _packed_nil_ s

(*3.3.7*)
(*type: char list -> char * char list = <fun> *)
(*a parser that returns proper list constructed by pairs of sexpes*)
  and _list_ s =
    let _the_list_circle_ = PC.caten (PC.caten _left_paren_ (PC.star (_delete_spaces_ _sexpr_))) _right_paren_ in
    let _packed_list_circle_ = PC.pack _the_list_circle_ (fun ((l, s), r) -> List.fold_right (fun a b -> Pair(a, b)) s Nil) in
    let _the_list_square_ = PC.caten (PC.caten _left_square_paren_ (PC.star (_delete_spaces_ _sexpr_))) _right_square_paren_ in
    let _packed_list_square_ = PC.pack _the_list_square_ (fun ((l, s), r) -> List.fold_right (fun a b -> Pair(a, b)) s Nil) in
    let _packed_list_ = PC.disj _packed_list_square_ _packed_list_circle_ in
    _packed_list_ s

(*type: char list -> char * char list = <fun> *)
(*a parser that returns improper list constructed by pairs of sexpes*)
  and _dotted_list_ s =
    let _the_dot_list_ = PC.caten (PC.caten (PC.caten (PC.caten _left_paren_ (PC.plus (_delete_spaces_ _sexpr_))) _dot_char_) (_delete_spaces_ _sexpr_)) _right_paren_ in
    let _packed_dot_list_circle_ = PC.pack _the_dot_list_ (fun (((((l, sexps), d), sexp), r)) -> List.fold_right (fun a b -> Pair(a, b)) sexps sexp) in
    let _the_dot_list_square_ = PC.caten (PC.caten (PC.caten (PC.caten _left_square_paren_ (PC.plus (_delete_spaces_ _sexpr_))) _dot_char_) (_delete_spaces_ _sexpr_)) _right_square_paren_ in
    let _packed_dot_list_square_ = PC.pack _the_dot_list_square_ (fun (((((l, sexps), d), sexp), r)) -> List.fold_right (fun a b -> Pair(a, b)) sexps sexp) in
    let _packed_dot_list_ = PC.disj _packed_dot_list_circle_ _packed_dot_list_square_ in
    _packed_dot_list_ s


(*3.3.8*)
(*type: char list -> sexpr * char list = <fun> *)
(*a parser that returns Vector*)
  and _vector_ s =
    let _the_vector_ = PC.caten (PC.caten (PC.caten _hashtag_ _left_paren_) (PC.star (_delete_spaces_ _sexpr_))) _right_paren_ in
    let _packed_vector_ = PC.pack _the_vector_ (fun ((((h, l), sexp), r)) -> Vector(sexp)) in
    _packed_vector_ s

(*3.3.9*)
(*type: char list -> sexpr * char list = <fun> *)
  and _quoted_ s = PC.pack (PC.caten _quote_ _sexpr_) (fun (name, s) -> Pair(Symbol("quote"), Pair(s, Nil))) s

(*type: char list -> sexpr * char list = <fun> *)
  and _quasi_quoted_ s = PC.pack (PC.caten _quasi_quote_ _sexpr_) (fun (name, s) -> Pair(Symbol("quasiquote"), Pair(s, Nil))) s

(*type: char list -> sexpr * char list = <fun> *)
  and _unquoted_ s = PC.pack (PC.caten _unquote_ _sexpr_) (fun (name, s) -> Pair(Symbol("unquote"), Pair(s, Nil))) s

(*type: char list -> sexpr * char list = <fun> *)
  and _unquoted_and_spliced_ s = PC.pack (PC.caten _splice_ _sexpr_) (fun (name, s) -> Pair(Symbol("unquote-splicing"), Pair(s, Nil))) s

(*3.2.2 + 3.2.3*)
(*a parser that ignores comments*)
  and _one_line_comment_ s = 
 PC.pack (PC.disj (PC.range (char_of_int (0)) (char_of_int (9)))
 (PC.range (char_of_int (11)) (char_of_int (127))))
 (fun x -> PC.char x) s

and _line_comment_ s = 
        PC.pack (PC.caten (PC.word ";") (PC.caten (PC.star _one_line_comment_)
        (PC.disj (PC.word "\n") PC.nt_end_of_input)))
        (fun (l, (rl, rr)) -> Nil) 
        s

and _sexpr_comment_ s =
        PC.pack (PC.caten (PC.word "#;") _sexpr_)
        (fun (l, r) -> Nil)
        s

and _comment_ s = (PC.disj _line_comment_ _sexpr_comment_) s

and _final_comment_ s = (PC.star (PC.disj _comment_ _space_)) s;;

let read_sexpr string =
    let (sexpression,charlist) = _sexpr_ (string_to_list string) in
    sexpression;;

let read_sexprs string =
  let rec _recursive_read_ st =
    if st = "" then []
    else let (s, cl) = (_sexpr_ (string_to_list st)) in
      s :: (_recursive_read_ (list_to_string cl))
    in _recursive_read_ string;;

    end;; (*struct Reader *)