#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * (int * string)) list
  val generate : (constant * (int * string)) list -> (string * (int * string)) list -> expr' -> string
  val get_const_address: constant -> (constant * (int * 'a)) list -> string
  val get_free_var_index: string -> (string * (int * string)) list -> int
end;;

module Code_Gen : CODE_GEN = struct

  let label_counter = ref 0;;

  let primitives = ["boolean?"; "float?"; "integer?"; "pair?"; "null?"; "char?"; "vector?"; "string?"; "procedure?"; "symbol?"; "string-length"; "string-ref";
  "string-set!"; "make-string"; "vector-length"; "vector-ref"; "vector-set!"; "make-vector"; "symbol->string"; "char->integer"; "integer->char"; "eq?"; "+"; "*"; "-"; "/"; "<"; "=";
  "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply"]

  let magic = "push 0xffffffffffffffff\n"

  let int_of_bool b =
    match b with
    | false -> 0
    | true -> 1;;

  (* Compare constants - can be Void os sexpr *)
  let const_eq c1 c2 =
    match c1 with
    | Void -> if (c2 = Void)
              then true
              else false
    | Sexpr(x) -> (match c2 with
                    | Void -> false
                    | Sexpr(y) -> sexpr_eq x y);;

(* Chapter 6 page 32.1 *)
(* Build the first const table, consists of constants and had duplicates *)
let rec naive_const_table lin lout =
  match lin with
  | [] -> lout
  | hd::tl -> (let res = match hd with
              | Const'(c) -> lout@[c]
              | BoxSet'(v, e) -> naive_const_table [e] lout
              | If'(test, caseT, caseF) -> naive_const_table [test; caseT; caseF] lout
              | Seq'(l) -> naive_const_table l lout
              | Set'(e_var, e_val) -> naive_const_table [e_var; e_val] lout
              | Def'(e_var, e_val) -> naive_const_table [e_var; e_val] lout
              | Or'(l) -> naive_const_table l lout
              | LambdaSimple'(params, body) -> naive_const_table [body] lout
              | LambdaOpt'(params, opt, body) -> naive_const_table [body] lout
              | Applic'(proc, args) -> (naive_const_table ([proc]@args) lout)
              | ApplicTP'(proc, args) -> (naive_const_table ([proc]@args) lout)
              | _ -> lout
              in naive_const_table tl res);;

(* Chapter 6 page 32.3 *)
(* Handle compound constants *)
let rec open_complex l =
  match l with
  | [] -> []
  | hd::tl -> (match hd with
                | Sexpr(Symbol(s)) -> [Sexpr(String(s))]@[hd]@(open_complex tl)
                | Sexpr(Pair(car, cdr)) -> (open_complex [Sexpr(car); Sexpr(cdr)])@[hd]@(open_complex tl)
                | Sexpr(Vector(v)) -> (open_complex (List.map (fun s -> Sexpr(s)) v))@[hd]@(open_complex tl)
                | _ -> [hd]@(open_complex tl))

let rec sexpr_mem member l =
  match l with
      | [] -> false
      | hd::tl ->  if (const_eq member hd)
                    then true
                    else sexpr_mem member tl;;

let rec remove_dups l ans =
  match l with
      | [] -> ans
      | hd::tl ->  if (sexpr_mem hd ans)
                                  then remove_dups tl ans
                                  else remove_dups tl (ans@[hd]) ;;

  let rec find_offset c table =
    match table with
    | [] -> raise X_this_should_not_happen
    | hd::tl -> let (const, (offset, str)) = hd in
                if (const_eq const c)
                then offset
                else find_offset c tl;;

  let get_const_address c table = "const_tbl+" ^ (string_of_int (find_offset c table));;

  let rec make_const_table constants_list (position : int) table =
    match constants_list with
    | [] -> table
    | hd::tl -> (match hd with
                | Void -> make_const_table tl (position + 1) (table@[(Void, (position, "MAKE_VOID"))])
                | Sexpr(Bool(b)) -> make_const_table tl (position + 2) (table@[(Sexpr(Bool(b)), (position, "MAKE_BOOL(" ^ (string_of_int (int_of_bool b)) ^ ")"))])
                | Sexpr(Nil) -> make_const_table tl (position + 1) (table@[(Sexpr(Nil), (position, "MAKE_NIL"))])
                | Sexpr(Number(Int(i))) -> make_const_table tl (position + 9) (table@[(Sexpr(Number(Int(i))), (position, "MAKE_LITERAL_INT(" ^ (string_of_int i) ^ ")"))])
                | Sexpr(Number(Float(f))) -> make_const_table tl (position + 9) (table@[(Sexpr(Number(Float(f))), (position, "MAKE_LITERAL_FLOAT(" ^ (string_of_float f) ^ ")"))])
                | Sexpr(Char(ch)) -> make_const_table tl (position + 2) (table@[(Sexpr(Char(ch)), (position, "MAKE_LITERAL_CHAR(" ^ string_of_int (int_of_char ch) ^ ")" ))])
                | Sexpr(String(s)) -> make_const_table tl (position + 9 + (String.length s)) (table@[(Sexpr(String(s)), (position, "MAKE_LITERAL_STRING \"" ^ s ^ "\""))])
                | Sexpr(Symbol(s)) -> make_const_table tl (position + 9) (table@[(Sexpr(Symbol(s)), (position, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (find_offset (Sexpr(String(s))) table)) ^ ")"))])
                | Sexpr(Pair(s1, s2)) -> make_const_table tl (position + 17) (table@[(Sexpr(Pair(s1, s2)), (position, "MAKE_LITERAL_PAIR (const_tbl+" ^ (string_of_int (find_offset (Sexpr(s1)) table)) ^ ", const_tbl+" ^ (string_of_int (find_offset (Sexpr(s2)) table)) ^ ")"))])
                | Sexpr(Vector(l)) -> let (vectorstring, vectoroffset) = make_vector_string l table in
                                      make_const_table tl (position+vectoroffset) (table@[(Sexpr(Vector(l)), (position, vectorstring))]))
  and make_vector_string v table =
  let length_v = List.length v in
  if (length_v = 0)
  then ("MAKE_LITERAL_VECTOR", 1)
  else(
  let hd = "const_tbl+" ^ (string_of_int (find_offset (Sexpr(List.hd v)) table)) ^ " " in
  let tl = List.tl v in
    let offset_list = List.fold_left (fun acc curr -> acc ^ ", const_tbl+" ^ (string_of_int (find_offset (Sexpr(curr)) table))) "" tl in
    ("MAKE_LITERAL_VECTOR " ^ hd ^ offset_list ^ "", (9+8*length_v)));;

let wrapper_make_const_table t = make_const_table t 0 [];;

  (* Chapter 6 page 32.2 + 32.4 *)
let final_table l = remove_dups (open_complex (remove_dups (naive_const_table l []) [])) [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))];;

  let rec naive_free_var_table lin lout =
    match lin with
    | [] -> lout
    | hd::tl -> (let res = match hd with
                  | Var'(VarFree(fv)) -> lout@[fv]
                  | Box'(v) -> naive_free_var_table [Var'(v)] lout
                  | BoxGet'(v) -> naive_free_var_table [Var'(v)] lout
                  | BoxSet'(v, e) -> naive_free_var_table [Var'(v); e] lout
                  | If'(test, caseT, caseF) -> naive_free_var_table [test; caseT; caseF] lout
                  | Seq'(l) -> naive_free_var_table l lout
                  | Set'(e_var, e_val) -> naive_free_var_table [e_var; e_val] lout
                  | Def'(e_var, e_val) -> naive_free_var_table [e_var; e_val] lout
                  | Or'(l) -> naive_free_var_table l lout
                  | LambdaSimple'(params, body) -> naive_free_var_table [body] lout
                  | LambdaOpt'(params, opt, body) -> naive_free_var_table [body] lout
                  | Applic'(proc, args) -> naive_free_var_table ([proc]@args) lout
                  | ApplicTP'(proc, args) -> naive_free_var_table ([proc]@args) lout
                  | _ -> lout in
                  naive_free_var_table tl res)

  let rec remove_dups_strings l ans =
    match l with
        | [] -> ans
        | hd::tl ->  if (List.mem hd ans)
                                    then remove_dups_strings tl ans
                                    else remove_dups_strings tl (ans@[hd]) ;;

  let rec make_free_val_table freeValList index table =
    match freeValList with
    | [] -> table
    | hd::tl -> (make_free_val_table tl (index+1) (table@[(hd, (index, "MAKE_UNDEF"))]));;

let rec get_free_var_index v_name table =
  match table with
  | [] -> raise X_this_should_not_happen
  | hd::tl -> let (name, ((index: int), something)) = hd in
              if (name = v_name)
              then index
              else get_free_var_index v_name tl;;

let rec semi_generate const_table fv_table e index =
  match e with
  | Const'(c) -> make_const const_table c
  | Var'(v) -> make_get_var const_table fv_table v index
  | Box'(v) -> make_box const_table fv_table v index
  | BoxGet'(v) -> make_box_get const_table fv_table v index
  | BoxSet'(v, exp) -> make_box_set const_table fv_table v exp index
  | If'(test, caseT, caseF) -> make_if const_table fv_table test caseT caseF index
  | Seq'(l) -> make_seq const_table fv_table l index
  | Set'(e_var, e_val) -> make_set const_table fv_table e_var e_val index
  | Def'(e_var, e_val) -> make_def const_table fv_table e_var e_val index
  | Or'(l) -> make_or const_table fv_table l index
  | LambdaSimple'(params, body) -> make_simple_lambda const_table fv_table params body (index+1)
  | LambdaOpt'(params, opt, body) -> make_opt_lambda const_table fv_table params opt body (index+1)
  | Applic'(proc, args) -> make_applic const_table fv_table proc args index
  | ApplicTP'(proc, args) -> make_applicTP const_table fv_table proc args index

  and make_const const_table c =
    ";MAKE_CONST \n" ^" mov rax, " ^ (get_const_address c const_table) ^ "\n"

  and make_get_var const_table fv_table v index =(*let comment = ";MAKE_GET_VAR\n" in*)
    match v with
    | VarFree(name) -> "mov rax, qword FVAR(" ^ (string_of_int (get_free_var_index name fv_table)) ^ ")\n " 
    | VarParam(name, minor) -> "mov rax, qword [rbp +  " ^ (string_of_int (8*(4+minor))) ^ "]\n"
    (* Return here and check it's correct *)
    | VarBound(name, major, minor) ->
    "mov rax, qword [rbp + 16]
  mov rax, qword [rax + " ^ (string_of_int (8*major)) ^ "]
  mov rax, qword [rax + " ^ (string_of_int (8*minor)) ^ "]\n"

  and make_box const_table fv_table v index =
   let generated_var = semi_generate const_table fv_table (Var'(v)) index in
    "MALLOC r15, 8 \n" ^ generated_var ^
    "mov qword [r15], rax \n
    mov rax, r15 \n"
  
  and make_box_get const_table fv_table v index =
   let generated_var = semi_generate const_table fv_table (Var'(v)) index in
   generated_var ^ "mov rax, qword [rax] \n"

  and make_box_set const_table fv_table v exp index =
    let generated_exp = semi_generate const_table fv_table exp index in
    let generated_var = semi_generate const_table fv_table (Var'(v)) index in
    generated_exp ^ "push rax \n" ^ generated_var ^ "pop qword [rax] \n
    mov rax, SOB_VOID_ADDRESS \n"

  and make_if const_table fv_table test caseT caseF index =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    ";MAKE_IF\n" ^ (semi_generate const_table fv_table test index) ^ "cmp rax, SOB_FALSE_ADDRESS \n je Lelse" ^ (string_of_int current_label_counter) ^ " \n" ^ (semi_generate const_table fv_table caseT index) ^ "jmp Lexit" ^ (string_of_int current_label_counter) ^ " \n Lelse" ^ (string_of_int current_label_counter) ^ ":" ^ (semi_generate const_table fv_table caseF index) ^ "Lexit" ^ (string_of_int current_label_counter) ^ ":\n"

  and make_seq const_table fv_table l index = ";MAKE_SEQ\n" ^  (List.fold_left (fun acc curr -> acc ^ (semi_generate const_table fv_table curr index)) "" l)

  and make_set const_table fv_table e_var e_val index = (*let comment = ";MAKE_SET\n" in*)
    match e_var with
    | Var'(VarFree(name)) ->   (semi_generate const_table fv_table e_val index ) ^ "mov qword FVAR(" ^ (string_of_int (get_free_var_index name fv_table)) ^ "), rax \n mov rax, SOB_VOID_ADDRESS \n"
    | Var'(VarParam(name, minor)) ->   (semi_generate const_table fv_table e_val index ) ^ "mov qword [rbp + " ^ (string_of_int (8*(4+minor))) ^ "], rax \n mov rax, SOB_VOID_ADDRESS \n"
    | Var'(VarBound(name, major, minor)) -> (semi_generate const_table fv_table e_val index ) ^ 
    "mov rbx, qword [rbp + 16]
  mov rbx, qword [rbx + " ^ (string_of_int (8*major)) ^ "]
  mov qword [rbx + " ^ (string_of_int (8*minor)) ^ "], rax
  mov rax, SOB_VOID_ADDRESS \n"
    | _ -> raise X_syntax_error

  and make_def const_table fv_table e_var e_val index = let comment = ";MAKE_DEF \n" in
    comment ^ (make_set const_table fv_table e_var e_val index)

  and make_or const_table fv_table l index =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    ";MAKE_OR\n" ^ (List.fold_left (fun acc curr -> acc ^ (semi_generate const_table fv_table curr index) ^ " cmp rax, SOB_FALSE_ADDRESS \n jne Lexit" ^ (string_of_int current_label_counter) ^ " \n") "" l) ^ "Lexit" ^ (string_of_int current_label_counter) ^ ":\n"

    and make_simple_lambda const_table fv_table params body index =
      if (index = 1)
      then make_simple_lambda_base const_table fv_table params body index
      else make_simple_lambda_not_base const_table fv_table params body index

    (* Create an empty env *)
    and make_simple_lambda_base const_table fv_table params body index =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let comment = Printf.sprintf ";MAKE_LAMBDA_SIMPLE_BASE%i \n" index in
    let code = Printf.sprintf
    "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, CLOSURELABEL%i)
    jmp ENDOFMAKECLOSURE%i

    CLOSURELABEL%i:
    push rbp
    mov rbp,rsp
    %s
    leave
    ret

    ENDOFMAKECLOSURE%i:
    "current_label_counter current_label_counter  current_label_counter (semi_generate const_table fv_table body index) current_label_counter in
     comment ^ code

  (* We extend at least one env *)
  and make_simple_lambda_not_base const_table fv_table params body index =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let comment = Printf.sprintf ";MAKE_LAMBDA_SIMPLE_NOT_BASE%i \n" index in
    let allocating_commands = "MALLOC rax, "^(string_of_int (8*(index-1))) ^ "; We allocate a pointer to the extended env of size |env+1| \n" in
    let code = Printf.sprintf " mov rcx, %i
    mov r10, rax ; r10 now holds the pointer to the start of the env
    add rax, 8   ; we increment the poitner from malloc to skip env[0]
    mov r8, qword [rbp+16] ;r8 contains the start of the last env
    cmp rcx, 1
    je skip_env_loop%i
  start_of_env_loop%i:
    mov r9, qword [r8]   ;we use r9 to dereference.
    mov qword [rax], r9
    add rax, 8    ;we increment the pointer to env[i]
    add r8, 8     ; we increment the pointer to env[j]

  loop start_of_env_loop%i

  skip_env_loop%i:
  push r10

  mov r15, qword [rbp+8*3]
  CHECK_MAGIC rdx
  JNE .case_no_magic1
  inc r15
  .case_no_magic1:
  shl r15, 3
  MALLOC rax, r15 ; we allocate a pointer to env0
  shr r15, 3
  pop r10           ; we take back the pointer to where the pointer to env0 is stored in memory
  mov qword [r10], rax    ;we hang our pointer to env0 in place.

  ;this loop assigns each parameter to it's place in the env0
  mov qword [rax], SOB_NIL_ADDRESS
  mov rcx, qword [rbp+8*3]
  CHECK_MAGIC rdx
  JNE .case_no_magic2
  inc rcx
  .case_no_magic2:
  cmp rcx, 0              ;we make sure there's some parameters otherwise we skip the assignment
  je end_of_params_loop%i
  mov r11, rbp
  add r11, 8*4           ; now r11 points to the first argument.
  start_of_env0_loop%i:  ;start of assignement loop
  mov r12, qword [r11]
  mov qword [rax], r12;
  add rax, 8 ; we increment i in extenv[0][i]
  add r11, 8  ; we increment the parameters pointer.

  loop start_of_env0_loop%i
  end_of_params_loop%i:

  push r10
  ;MALLOC rax, 17  ; allocate memory for closure.
  pop r10
  MAKE_CLOSURE(rax, r10, CLOSURELABEL%i)
  jmp ENDOFMAKECLOSURE%i

  CLOSURELABEL%i:
  push rbp
  mov rbp,rsp
  %s
  leave
  ret

  ENDOFMAKECLOSURE%i:
  " (index-1) current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter (semi_generate const_table fv_table body index) current_label_counter in
  comment ^ allocating_commands ^ code

  and make_opt_lambda const_table fv_table params opt body index =
    if (index = 1)
    then make_opt_lambda_base const_table fv_table params body index
    else make_opt_lambda_not_base const_table fv_table params body index

  (* Create an empty env *)
  and make_opt_lambda_base const_table fv_table params body index =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let comment = Printf.sprintf ";MAKE_LAMBDA_OPT_BASE%i \n" index in
    let expected_params = ((List.length params) + 1) in
    let make_list_out_of_remain = Printf.sprintf
    "mov r15, PARAM_COUNT
    mov r14, %i
    MAKE_PAIR (r13, SOB_NIL_ADDRESS, SOB_NIL_ADDRESS)
    mov rcx, r15
    sub rcx, r14
    mov r10, r13 ; save pointer to the start of the list
    mov rdi, r10
    add rdi, 9

    ; prepare r12 with first argument to put in the list
    mov r12, r14
    add r12, 3
    shl r12, 3
    add r12, rbp

    MAKELIST%i:
    mov r8, qword [r12]
    mov qword [r13+1], r8 ; Pair(0) = args(m)
    add r12, 8  ; m++
    MAKE_PAIR (r11, SOB_NIL_ADDRESS, SOB_NIL_ADDRESS)
    mov qword [r13+9], r11
    add r13, 17
    mov rdx, qword [rdi]
    add rdi, 17

    loop MAKELIST%i
    inc r13
    mov r8, qword [r12]
    mov qword [r13], r8
    mov PVAR(%i), r10

    \n" expected_params current_label_counter  current_label_counter (expected_params - 1) in
    let code1 = (Printf.sprintf
    "
    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, CLOSURELABEL%i)
    jmp ENDOFMAKECLOSURE%i

    CLOSURELABEL%i:
    push rbp
    mov rbp,rsp
    mov r9, PARAM_COUNT
    cmp r9, %i
    je NOSTACKMANIPULATION%i
    jb USEMAGIC%i\n" current_label_counter current_label_counter current_label_counter expected_params current_label_counter current_label_counter) in
    let code2 = (Printf.sprintf
    "jmp BEGINFUNCBODY%i

    USEMAGIC%i:
    mov rdx, qword [rbp+8*3]
    add rdx, 4
    shl rdx, 3
    add rdx, rbp
    mov qword [rdx], SOB_NIL_ADDRESS
    jmp BEGINFUNCBODY%i

    NOSTACKMANIPULATION%i:
    mov r15, PVAR(%i)
    MAKE_PAIR (r14, r15, SOB_NIL_ADDRESS)
    mov PVAR(%i), r14

    BEGINFUNCBODY%i:

    %s
    leave
    ret

    ENDOFMAKECLOSURE%i:
    " current_label_counter current_label_counter current_label_counter current_label_counter (expected_params-1) (expected_params-1) current_label_counter (semi_generate const_table fv_table body index) current_label_counter ) in
    comment ^ code1 ^ make_list_out_of_remain ^ code2

  (* We extend at least one env *)
  and make_opt_lambda_not_base const_table fv_table params body index =
  let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let comment = Printf.sprintf ";MAKE_LAMBDA_OPT_NOT_BASE%i \n" index in
    let allocating_commands = "MALLOC rax, "^(string_of_int (8*(index-1))) ^ "\n" in
    let expected_params = ((List.length params) + 1) in
    let env_code = Printf.sprintf " mov rcx, %i
    mov r10, rax ; r10 now holds the pointer to the start of the env
    add rax, 8   ; we increment the poitner from malloc to skip env[0]
    mov r8, qword [rbp+16] ;r8 contains the start of the last env
    cmp rcx, 1
    je skip_env_loop%i
  start_of_env_loop%i:
    mov r9, qword [r8]   ;we use r9 to dereference.
    mov qword [rax], r9
    add rax, 8    ;we increment the pointer to env[i]
    add r8, 8     ; we increment the pointer to env[j]

  loop start_of_env_loop%i

  skip_env_loop%i:
  push r10

  mov r15, qword [rbp+8*3]
  CHECK_MAGIC rdx
  JNE .case_no_magic1
  inc r15
  .case_no_magic1:
  shl r15, 3
  MALLOC rax, r15 ; we allocate a pointer to env0
  shr r15, 3
  pop r10           ; we take back the pointer to where the pointer to env0 is stored in memory
  mov qword [r10], rax    ;we hang our pointer to env0 in place.

  ;this loop assigns each parameter to it's place in the env0
  mov qword [rax], SOB_NIL_ADDRESS
  mov rcx, qword [rbp+8*3]
  CHECK_MAGIC rdx
  JNE .case_no_magic2
  inc rcx
  .case_no_magic2:
  cmp rcx, 0              ;we make sure there's some parameters otherwise we skip the assignment
  je end_of_params_loop%i
  mov r11, rbp
  add r11, 8*4           ; now r11 points to the first argument.
  start_of_env0_loop%i:  ;start of assignement loop
  mov r12, qword [r11]
  mov qword [rax], r12;
  add rax, 8 ; we increment i in extenv[0][i]
  add r11, 8  ; we increment the parameters pointer.

  loop start_of_env0_loop%i
  end_of_params_loop%i:

  push r10
  ;MALLOC rax, 17  ; allocate memory for closure.
  pop r10" (index-1) current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter current_label_counter in
    let make_list_out_of_remain = Printf.sprintf
        "mov r15, PARAM_COUNT
    mov r14, %i
    MAKE_PAIR (r13, SOB_NIL_ADDRESS, SOB_NIL_ADDRESS)
    mov rcx, r15
    sub rcx, r14
    mov r10, r13 ; save pointer to the start of the list
    mov rdi, r10
    add rdi, 9

    ; prepare r12 with first argument to put in the list
    mov r12, r14
    add r12, 3
    shl r12, 3
    add r12, rbp

    MAKELIST%i:
    mov r8, qword [r12]
    mov qword [r13+1], r8 ; Pair(0) = args(m)
    add r12, 8  ; m++
    MAKE_PAIR (r11, SOB_NIL_ADDRESS, SOB_NIL_ADDRESS)
    mov qword [r13+9], r11
    add r13, 17
    mov rdx, qword [rdi]
    add rdi, 17

    loop MAKELIST%i
    inc r13
    mov r8, qword [r12]
    mov qword [r13], r8
    mov PVAR(%i), r10

    \n" expected_params current_label_counter  current_label_counter (expected_params - 1) in
    let code1 = (Printf.sprintf
    "
    MAKE_CLOSURE(rax, r10, CLOSURELABEL%i)
    jmp ENDOFMAKECLOSURE%i

    CLOSURELABEL%i:
    push rbp
    mov rbp,rsp
    mov r9, PARAM_COUNT
    cmp r9, %i
    je NOSTACKMANIPULATION%i
    jb USEMAGIC%i\n" current_label_counter current_label_counter current_label_counter expected_params current_label_counter current_label_counter) in
    let code2 = (Printf.sprintf
    "jmp BEGINFUNCBODY%i

    USEMAGIC%i:
    mov rdx, qword [rbp+8*3]
    add rdx, 4
    shl rdx, 3
    add rdx, rbp
    mov qword [rdx], SOB_NIL_ADDRESS
    jmp BEGINFUNCBODY%i

    NOSTACKMANIPULATION%i:
    mov r15, PVAR(%i)
    MAKE_PAIR (r14, r15, SOB_NIL_ADDRESS)
    mov PVAR(%i), r14

    BEGINFUNCBODY%i:

    %s
    leave
    ret

    ENDOFMAKECLOSURE%i:
    " current_label_counter current_label_counter current_label_counter current_label_counter (expected_params-1) (expected_params-1) current_label_counter (semi_generate const_table fv_table body index) current_label_counter ) in
    comment ^ allocating_commands ^ env_code ^ code1 ^ make_list_out_of_remain ^ code2

  and make_applic const_table fv_table proc args index =
    let comment = ";MAKE_APPLIC \n" in
    let push_args = List.fold_left (fun curr acc -> acc ^ curr) "" (List.map (fun arg -> (semi_generate const_table fv_table arg index) ^ " \n push rax \n") args) in
    let push_num_of_args = Printf.sprintf "push %i\n" (List.length args) in
    let generated_proc = semi_generate const_table fv_table proc index in
    comment ^ magic ^ push_args ^ push_num_of_args ^ generated_proc ^ "
    CLOSURE_ENV r8, rax ; Now r8 holds the start of our closure.
    push r8
    CLOSURE_CODE r8, rax
    call r8             ; ??
    add rsp , 8*1       ; pop env
    pop rbx             ; pop arg count
    shl rbx , 3         ; rbx = rbx * 8
    add rsp , rbx       ; pop args
    add rsp, 8          ; pop magic \n"

  and make_applicTP const_table fv_table proc args index =
    let num_of_args = List.length args in
    let comment = ";MAKE_APPLICTP \n" in
    let generated_args = List.fold_left (fun curr acc -> acc ^ curr) "" (List.map (fun arg -> (semi_generate const_table fv_table arg index) ^ " \n push rax \n") args) in
    let push_num_of_args = Printf.sprintf "push %i\n" num_of_args in
    let generated_proc = (semi_generate const_table fv_table proc index) in
    let code = Printf.sprintf
    "
    CLOSURE_ENV r8, rax ; Now r8 holds the start of our closure.
    push r8

    push qword [rbp + 8 * 1] ; old ret addr
    ;mov r14, qword [rbp]
    ;mov rbp, qword [rbp]
    mov rsi, [rbp]
    SHIFT_FRAME %i

    CLOSURE_CODE r8, rax
    add rsp, 8   ;WE HAVE TO POP ONCE BECAUSE WE FUCKED UP EARLIER AND WE ARE IN TOO DEEP.
    mov rbp, rsi
    jmp r8


    \n" (5+num_of_args)

    in comment ^ magic ^ generated_args ^ push_num_of_args ^ generated_proc ^ code;;

  let naive_table_no_dups e = remove_dups_strings (naive_free_var_table e primitives) [];;

  let wrapper_make_free_val_table e = make_free_val_table (naive_table_no_dups e) 0 [];;

  let make_consts_tbl asts = make_const_table (final_table asts) 0 [];;
  let make_fvars_tbl asts = wrapper_make_free_val_table asts;;
  let generate consts fvars e = semi_generate consts fvars e 0 ;;
end;;