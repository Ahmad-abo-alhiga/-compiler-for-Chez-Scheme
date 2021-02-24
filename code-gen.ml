 #use "semantic-analyser.ml";;

open Semantics;;


(* This module is here for you convenience only!
 You are not required to use it.
 you are allowed to change it. *)

module type CODE_GEN = sig
 
 (* This signature assumes the structure of the constants table is
 a list of key-value pairs:
 - The keys are constant values (Sexpr(x) or Void)
 - The values are pairs of:
 * the off set from the base const_table address in bytes; and
 * a string containing the byte representation (or a sequence of nasm macros)
 of the constant value
 For example: [(Sexpr(Nil), (1, "T_NIL"))]
 *)
 val make_consts_tbl : expr' list -> (constant * (int * string)) list

 (* This signature assumes the structure of the fvars table is
 a list of key-value pairs:
 - The keys are the fvar names as strings
 - The values are the off sets from the base fvars_table address in bytes
 For example: [("boolean?", 0)]
 *) 
 val make_fvars_tbl : expr' list -> (string * int) list

 (* If you change the types of the constants and fvars tables, you will have to update
 this signature to match: The first argument is the constants table type, the second 
 argument is the fvars table type, and the third is an expr' that has been annotated 
 by the semantic analyser.
 *)
 val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;




module Code_Gen : CODE_GEN = struct
(*module Code_Gen : CODE_GEN = struct*)
 
 
 
 
 
 let nil_size = 1;;
 let void_size = 1;;
 let char_size = 2;;
 let boolean_size = 2;;
 let rational_size = 17;;
 let flonum_size=9;;
 let string_size len = len+9;;
 let symbol_size = 9;;
 let pair_size = 17;;
 let closure_size = 17;;
 
 let rec get_consts expr_' lst =
   match expr_' with
    | Const' (x) -> lst @ [x]
    
    | Var' (VarParam(v,minor))-> lst
    
    | Var' (VarBound(v,major, minor))-> lst
    
    | Var'(VarFree v1) -> lst
    
    | BoxGet'(var1)-> lst
    
    | BoxSet'(x,y) -> (get_consts y lst )
    
    | If'(e_test,e_then,e_else) -> (get_consts e_test lst) @ (get_consts e_then lst ) @ (get_consts e_else lst )
    
    | Seq'(list_of_exps) -> let constants= List.map (fun(x)-> get_consts x lst) list_of_exps in 
                            List.concat constants
    
    | Set'(var1,_val) -> (get_consts _val lst )
    
    | Def'(var1,_val) -> (get_consts _val lst )
    
    | Or'(list_of_exps) -> let constants= (List.map (fun(x)-> get_consts x lst)list_of_exps ) in 
                            List.concat constants
    
    | LambdaSimple'(vars,body) -> (get_consts body lst ) 
    
    | LambdaOpt'(vars,var1,body) -> (get_consts body lst ) 
    
    | Applic'(e1,args) -> let constants= (List.map (fun(x)-> get_consts x lst)) args in
                        (get_consts e1 lst ) @ List.concat (constants)
    
    | ApplicTP'(e1,args) -> let constants= (List.map (fun(x)-> get_consts x lst)) args in
                            (get_consts e1 lst ) @ List.concat (constants)
    
    | _ -> lst ;;
  
 
 
 
 
 let rec extend_every_constant lst = 
   match lst with
    | Sexpr(Symbol x):: xs -> (Sexpr(String x) :: [Sexpr(Symbol x)]) @ (extend_every_constant xs)
    | Sexpr(Pair(x,y)) :: xs -> let extended_car =extend_every_constant [Sexpr(x)] in
                          let extended_cdr =extend_every_constant [Sexpr(y)] in 
                          (extended_car @ extended_cdr @
                          [Sexpr(x)] @ [Sexpr(y)] @ [Sexpr(Pair(x,y))]) @ (extend_every_constant xs) 
                          | Sexpr(x)::xs -> Sexpr(x) :: (extend_every_constant xs)
                          | x::xs -> x :: (extend_every_constant xs)
                          | _ ->[]
                          ;;
 
 
 
 
 
 
 
 
 let handle_sub_ast sub_ast = 
      let lst_of_consts = (get_consts sub_ast []) in 
      let consts_set = List.fold_left (fun a b -> if ( List.mem b a) then a else a@[b]) [] lst_of_consts in (* here we removing duplicates *)
      let lst_of_extended_consts = (extend_every_constant consts_set) in
      let set_of_extended_consts=List.fold_left (fun a b -> if ( List.mem b a) then a else a@[b]) [] lst_of_extended_consts in
      set_of_extended_consts;;
 
 
 
 
 
 let rec get_address_in_triplets x lst= 
  match lst with
    |[] -> -1
    |(a,b,c)::tail-> if(a=x) then b else (get_address_in_triplets x tail) 
 
 ;;
 
 
 
 
 let rec handle_triple_string str=
    match str with
      | []-> ""
      | first::[] ->string_of_int (int_of_char first)
      | first::last -> string_of_int(int_of_char first) ^"," ^ handle_triple_string last
 ;; 
 
 
 
 
 let rec make_triplets index lst_acc set_of_consts= 
      match set_of_consts with
          |[] -> lst_acc

          |Void::lst' -> make_triplets (index + void_size) (lst_acc @ [(Void, index, "MAKE_VOID")]) lst'

          |Sexpr(Nil)::lst' -> make_triplets (index + nil_size) (lst_acc @ [(Sexpr(Nil), index, "MAKE_NIL")]) lst'

          |Sexpr(Bool false)::lst' -> make_triplets (index + boolean_size) (lst_acc @ [(Sexpr(Bool false), index, "MAKE_BOOL(0)")]) lst'

          |Sexpr(Bool true)::lst' -> make_triplets (index + boolean_size) (lst_acc @ [(Sexpr(Bool true), index, "MAKE_BOOL(1)")]) lst'

          |Sexpr(Char x)::lst' -> make_triplets (index + char_size) (lst_acc @ [(Sexpr(Char x), index, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char x)) ^ ")")]) lst'

          |Sexpr(String x)::lst' -> make_triplets (index + (string_size (String.length x)))
                                     (lst_acc @ [(Sexpr(String x), index, "MAKE_LITERAL_STRING \""^x^"\"")]) lst'
           

          |Sexpr(Number(Fraction (n1, d1)))::lst' -> make_triplets (index + rational_size) 
                                                   (lst_acc @ [(Sexpr(Number(Fraction (n1, d1))), index, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int n1)^ "," ^ (string_of_int d1) ^")")]) lst'

          |Sexpr(Number(Float x))::lst' -> make_triplets (index + flonum_size) 
                                           (lst_acc @ [(Sexpr(Number(Float x)), index, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^")")]) lst'

          |Sexpr(Pair(x,y))::lst' -> make_triplets (index + pair_size)
                                    (lst_acc @ [(Sexpr(Pair(x,y)), index, "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (get_address_in_triplets (Sexpr(x)) lst_acc)) ^", const_tbl+"^(string_of_int(get_address_in_triplets (Sexpr(y)) lst_acc))^")")]) lst'

          |Sexpr(Symbol(x))::lst' -> make_triplets (index + symbol_size)
                                     (lst_acc @ [(Sexpr(Symbol(x))), index, 
                                     "MAKE_LITERAL_SYMBOL(const_tbl+"^ (string_of_int (get_address_in_triplets (Sexpr(String x)) lst_acc)) ^")"]) lst'

          
          ;; 
 
 
 
 
 
 
 let make_consts_tbl ast_nodes=
    let lsts= List.map (fun(node)-> handle_sub_ast node) ast_nodes in
    let lst_of_consts =[Void ; Sexpr(Nil) ; Sexpr(Bool (false)) ; Sexpr(Bool (true))] @ List.concat lsts in 
    let consts_set= List.fold_left (fun a b -> if ( List.mem b a) then a else a @ [b]) [] lst_of_consts in
    let const_triplets= make_triplets 0 [] consts_set in
    let const_table= List.fold_left (fun lst (a,b,c) -> let ans = (a,(b,c)) in 
    lst @ [ans]) [] const_triplets in 
    const_table;;
 
 
 
 (**********************************************FREE VARIABLES TABLE**************************)
 let rec get_fvars_table expr_' tbl=
  match expr_' with
    | Const' (x) -> tbl
    
    | Var'(VarParam(v,minor))-> tbl
    
    | Var'(VarBound(v,major,minor))-> tbl
    
    | Var'(VarFree(v1)) -> expr_' :: tbl
    
    | BoxGet'(_)-> tbl
    
    | BoxSet'(x,y) -> (get_fvars_table y tbl)
    
    | If'(e_test,e_then,e_else) -> (get_fvars_table e_test tbl) @ (get_fvars_table e_then tbl) @ (get_fvars_table e_else tbl)
    
    | Seq'(list_of_exps) -> let tabels= List.map (fun (expr_')->get_fvars_table expr_' tbl) list_of_exps in
    List.concat tabels
    
    | Set'(var1,_val) ->begin match var1 with
                        | VarFree(name)-> Var'(var1) :: (get_fvars_table _val tbl ) 
                        | _ -> (get_fvars_table _val tbl) end
    
    | Def'(var1,_val) -> begin match var1 with
                          |VarFree(name)->Var'(var1) :: (get_fvars_table _val tbl) 
                          | _ -> (get_fvars_table _val tbl) end
    
    | Or'(list_of_exps) -> let tabels= List.map (fun (expr_')->get_fvars_table expr_' tbl) list_of_exps in
                          List.concat tabels
    | LambdaSimple'(vars,body) -> (get_fvars_table body tbl) 
    
    | LambdaOpt'(vars,var1,body) -> (get_fvars_table body tbl) 
    
    | Applic'(e1,args) -> (get_fvars_table e1 tbl) @ List.concat (List.map (fun (expr_')->get_fvars_table expr_' tbl) args)
    
    | ApplicTP'(e1,args) -> (get_fvars_table e1 tbl) @ List.concat (List.map (fun (expr_')->get_fvars_table expr_' tbl) args)
    
    | _ -> tbl ;;
 
 
 let primitive_names_to_labels =[
 (* Type queries *)
 "boolean?" ; "flonum?"; "rational?" ;
 "pair?"; "null?"; "char?"; "string?";
 "procedure?"; "symbol?";
 (* String procedures *)
 "string-length"; "string-ref"; "string-set!";
 "make-string"; "symbol->string";
 (* Type conversions *)
 "char->integer"; "integer->char"; "exact->inexact";
 (* Identity test *)
 "eq?";
 (* Arithmetic ops *)
 "+"; "*"; "/"; "="; "<";
 (* Additional rational numebr ops *)
 "numerator"; "denominator"; "gcd";
 (* you can add yours here *)
 "car"; "cdr";"set-car!";"set-cdr!"; "cons";"apply" ];;
 
 let get_fvar_name frvar = 
      match frvar with
      | Var'(VarFree(v1))-> v1
      | _-> raise PC.X_no_match 
      ;;
 
 
 
 
 
 let rec make_fvars_pairs fvars_lst index= 
        match fvars_lst with
        |[]-> []
        |hd::tl-> (hd,index):: make_fvars_pairs tl (index+1)
        ;; 
 
 

 
 
 let make_fvars_tbl ast_lst = 
        let free_vars_table= List.concat (List.map ( fun(expr_') -> get_fvars_table expr_' []) ast_lst) in
        let list_of_fvars_strings = List.map get_fvar_name free_vars_table in
        let fvars_set = List.fold_left (fun a b -> if ( List.mem b a) then a else a@[b]) [] list_of_fvars_strings in
        let fvars_without_indexes = primitive_names_to_labels @ fvars_set in
        let fvars_with_indexes = make_fvars_pairs fvars_without_indexes 0 in
        fvars_with_indexes;;
 
 
 
 
 
 (* generate *)
 
 
 
 let label_unique_counter= (ref 0);;
 let applictp_counter= (ref 0);;
 
 let increase_unique_counter_tp counter=
    counter := !counter + 1; counter;;

 let append_unique_number_to_label_tp label=
      label ^ (string_of_int(!(increase_unique_counter_tp applictp_counter)));;

 let increase_unique_counter counter=
    counter := !counter + 1; counter;;
 
 let append_unique_number_to_label label=
    label ^ (string_of_int(!(increase_unique_counter label_unique_counter)));;
 
 
 
 
 
   
let get_address_in_consts_tbl x consts_tbl=
  let (a,(b,c)) = (List.find (fun (a,(b,c))->
   let aa=Const(a) in
    let xx= Const(x) in
  (expr_eq aa  xx)) consts_tbl)  in 
    "const_tbl+" ^ (string_of_int b);;
  
 
 
 
 
 let rec get_address_in_fvars_tbl x fvars_tbl= 
      match fvars_tbl with
      |[] -> -1
      |(a,b)::tail-> if(String.equal a x) then b else (get_address_in_fvars_tbl x tail) 
      ;;
 
 
 let get_overide_frame_code_Apptp applic_tp_label =
 
  let asm_code= "mov r8, [rbp+3*8] ;r8= old number of args" ^ "\n" ^
                "add r8, 3 ; ( add 3 to it (num of args,env,ret addres))" ^ "\n" ^
                "shl r8, 3 ; ( (make it (n+3) *8 so now if we add it to rbp we get the start of previous frame and we start override" ^ "\n"^
                "add r8, rbp ; r8 = ARG(n-1), that mean r9 points to the top of stack in where we should overide" ^ "\n"^
                "mov r9, [rsp+2*8] ; r9 is the counter of the loop so we make it equal to new arg number+3" ^ "\n"^ 
                "add r9, 3 ; adding 3 (num of args, env,ret addres)" ^ "\n"^
                "mov r10, [rbp] ;r10= old rbp, we save old rbp before overiding loop" ^ "\n"^
                applic_tp_label^": ;( in this loop we overrite the stack from down to top) the loop continue while rcx!=0" ^ "\n"^
                " mov r11, [rsp+8*(r9-1)] ; r11 = the first value of the new frame" ^ "\n"^
                " mov [r8], r11 ; put it in [r9] ( overiding) " ^ "\n"^
                " sub r8, 8 ; r9=r9-8 (8 is the size of every cell in stack )" ^ "\n"^
                " dec r9 ; r9=r9-1 " ^ "\n"^
                " cmp r9, 0 ; " ^ "\n"^
                " jne " ^applic_tp_label ^ "\n" ^ 

                "mov rbp, r10 ;Make rbp points to old rbp (exists in r10)" ^ "\n"^
                "add r8,8 ;" ^ "\n"^ 
                "mov rsp, r8 ; " ^ "\n"^
                "CLOSURE_CODE rdi,rax ; " ^ "\n"^
                "jmp rdi"^"\n" in
 asm_code;; 
  
 
 
 let get_major_0_array_code register_ = 
            let loop_start_label= append_unique_number_to_label  "loop_start" in
            let loop_finish_label= append_unique_number_to_label  "loop_finish" in
            let asm_code="xor r12, r12" ^ "\n"^
            "mov r12, qword [rbp + 8 * 3] ; r12=number of args"^"\n"^ 
            "mov rbx, r12 ; rbx= number of args"^ "\n"^ (* here rbx = the number of args*)
            "mov r10, r12" ^ "\n"^
            "shl r10, 3" ^ "\n"^
            "push rbx" ^ "\n" ^
            "MALLOC "^register_^", r10 ; allocate memory" ^ "\n" ^ 
            "pop rbx" ^ "\n" ^
            "cmp r12, 0" ^ "\n"^ 
            "je "^loop_finish_label^"\n"^ 
            loop_start_label^":"^"\n"^
            " mov r12, qword [rbp+(3+rbx)*WORD_SIZE] ; getting arg number rbx-1" ^"\n"^ 
            " mov ["^ register_ ^ " + 8 * (rbx-1)], r12 ; putting the arg in the array" ^ "\n"^
            " dec rbx " ^ "\n" ^
            " cmp rbx, 0" ^ "\n"^ 
            " jne "^loop_start_label^"\n"^
            loop_finish_label^":"^"\n" in
            asm_code;;
 
 let get_extend_env_code register_ env_major =
      let loop_start_label= append_unique_number_to_label  "extend_loop_start" in
      let loop_finish_label= append_unique_number_to_label  "extend_loop_finish" in
      let asm_code= "MALLOC " ^ register_ ^ ", "^(string_of_int ((env_major + 1)*8))^" ; allocate \n"^ (* here we allocate with prevEnvSize+1 *)
                    "mov rbx, " ^ (string_of_int env_major) ^ " ; here rbx=prevEnvSize" ^ "\n"^ 
                    "mov r9, rbx"^"\n"^
                    "cmp r9,0" ^ "\n"^
                    "je "^loop_finish_label^ "\n" ^
                    "mov r12, qword [rbp + 8 * 2]" ^" ; here r12 ponits to tha majors array (prevEnv)" ^ "\n" ^ 
                    loop_start_label^":"^"\n"^
                    " mov r9, qword[r12 + 8 * (rbx - 1)]"^"\n"^ (* getting prevenv[i+1] array*) 
                    " mov qword[" ^ register_ ^ " + 8 * rbx],r9" ^ "\n" ^ (* here we make extendedenv[i+1]=prevEnv[i] *) 
                    " dec rbx " ^ "\n"^
                    " cmp rbx, 0" ^ "\n"^
                    " jne "^loop_start_label^"\n"^
                    loop_finish_label^":"^"\n" in
      asm_code;;
 
 
 
 let get_shift_eq_loop_code=let loop_start_label= append_unique_number_to_label  "shift_loop_start" in
                            let asm_code= loop_start_label ^": " ^ "\n" ^
                            " mov r10, [rsp + rdx*8]" ^ "\n" ^
                            " mov qword[rsp + (rdx-1)*8], r10 " ^ "\n" ^
                            " inc rdx" ^ "\n" ^
                            " dec r8" ^ "\n" ^
                            " cmp r8, 0" ^ "\n"^
                            " jne "^loop_start_label^ "\n" in
                            asm_code;; 
 
 
 
 let get_opt_args_lst_code args_len= let loop_start_label= append_unique_number_to_label  "optArgs_loop_start" in
                                     let asm_code=" xor r15,r15" ^ "\n" ^
                                     " xor r8, r8" ^ "\n" ^
                                     " sub r8, "^ args_len ^ "\n" ^
                                     " add r8, [rsp+2*8] ; now r8= the size of opr params " ^ "\n" ^
                                     " mov r9, SOB_NIL_ADDRESS" ^ "\n"^
                                     loop_start_label^":" ^ "\n" ^
                                     " mov r10, [rsp + 8*(r8 + " ^ args_len ^") + 2*8]" ^ "\n" ^
                                     " MAKE_PAIR (r15, r10, r9)" ^"\n"^ (* her we make the list, element by element*)
                                     " mov r9, r15" ^ "\n"^
                                     " dec r8 " ^ "\n" ^ 
                                     " cmp r8, 0" ^ "\n"^
                                     " jne "^loop_start_label^ "\n" in
                                     asm_code;; 
 
 
 let get_shift_noteq_loop_code args_len_plus_one=
                                                  let loop_start_label= append_unique_number_to_label  "shifArgs_loop_start" in
                                                  let finish_shift_label= append_unique_number_to_label  "finish_shift" in
                                                  let asm_code= " xor r8, r8" ^ "\n" ^
                                                  " sub r8, " ^ args_len_plus_one ^ "\n" ^
                                                  " add r8, [rsp+2*8]" ^ "\n" ^
                                                  " mov r10, r8" ^ "\n" ^
                                                  " cmp r8,0 " ^ "\n"^ (* if number of optparams=1 no need to shif *)
                                                  " je " ^ finish_shift_label ^ "\n" ^
                                                  (* here r10 have number of opt args and we need to shift*) 
                                                  " xor r8, r8" ^ "\n" ^
                                                  " sub r8, r10"^ "\n" ^
                                                  " add r8, [rsp+2*8]" ^ "\n" ^
                                                  " add r8, 3" ^ "\n" ^ (* here r8 = number of args+3-number of opt args, and this is the loop times number *)
                                                  " mov r12, [rsp+2*8]" ^ "\n" ^ (*here r12 have number of args *) 
                                                  loop_start_label ^ ":" ^ "\n" ^
                                                  " mov r14, [rsp + (r8-3)*8 + 8*2]" ^ "\n"^
                                                  " mov qword[rsp + r12*8 + 8*2 ], r14" ^ "\n"^ 
                                                  " dec r12" ^ "\n" ^
                                                  " dec r8" ^ "\n" ^
                                                  " cmp r8, 0" ^ "\n"^
                                                  " jne "^loop_start_label ^ "\n" ^
                                                  " shl r10, 3" ^ "\n" ^
                                                  " add rsp, r10" ^ "\n" ^ (* fixing rsp to be rsp+ numOfOptArgs*8 and in fact this is the number of cells that we shifted *)
                                                  finish_shift_label ^ ":" ^ "\n" in
                                                  asm_code;;
 
 
 let rec generate_with_depth env_major consts_tbl fvars_tbl expr_' =
    match expr_' with
 
         | Const'(x) -> "mov rax,"^ (get_address_in_consts_tbl x consts_tbl ) ^ "\n" 
        
         | Var'(VarParam(v,minor))-> "mov rax, qword [rbp + 8*(4 + " ^ (string_of_int(minor))^ ")]" ^ "\n"
        
         | Var'(VarBound(v,major,minor))-> let env_code="mov rax, qword [rbp + 8*2]" in
                                           let major_code="mov rax, qword [rax + 8*" ^ (string_of_int(major)) ^ "]" in
                                           let minor_code= "mov rax, qword [rax + 8*" ^ (string_of_int(minor)) ^ "]" in
                                           env_code ^ "\n" ^ major_code ^ "\n" ^ minor_code ^ "\n"
        
         | Var'(VarFree(v1)) -> "mov rax, qword [fvar_tbl+"^ string_of_int(get_address_in_fvars_tbl v1 fvars_tbl)^"* WORD_SIZE ]"
        
        
         |Box'(x) -> let var_to_generate = Var'(x) in
                     let generated_var = (generate_with_depth env_major consts_tbl fvars_tbl var_to_generate) in
                     generated_var ^
                     "MALLOC r8, 8 \n"^
                     "mov [r8], rax \n"^
                     "mov rax,r8 \n"
        
        
         | BoxGet'(x)-> let v=Var'(x) in
                        let var_str= (generate_with_depth env_major consts_tbl fvars_tbl v) in
                        var_str ^ "\n" ^"mov rax, qword [rax]"^ "\n"
        
        
         | BoxSet'(x,y) -> let v=Var'(x) in
                            (generate_with_depth env_major consts_tbl fvars_tbl y ) ^ "\n" ^ 
                            "push rax" ^ "\n" ^ 
                            (generate_with_depth env_major consts_tbl fvars_tbl v ) ^ "\n" ^ 
                            "pop qword [rax]" ^ "\n" ^
                            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
        
        
         | If'(e_test,e_then,e_else) -> let lelse_label= (append_unique_number_to_label  "lelse") in
                                        let lexit_label= (append_unique_number_to_label  "lexit") in
                                        (generate_with_depth env_major consts_tbl fvars_tbl e_test)^"\n"^
                                        "cmp rax, SOB_FALSE_ADDRESS"^"\n"^
                                        "je "^lelse_label^"\n"^
                                        (generate_with_depth env_major consts_tbl fvars_tbl e_then )^"\n"^
                                        "jmp "^lexit_label^"\n"^
                                        lelse_label^":\n"^
                                        (generate_with_depth env_major consts_tbl fvars_tbl e_else)^"\n"^
                                        lexit_label^":"
        
         
         | Seq'(list_of_exps) -> let generated_exps_'= List.map (fun (expr_')-> (generate_with_depth env_major consts_tbl fvars_tbl expr_')) list_of_exps in
                                (String.concat "\n" generated_exps_') 
        
         | Set'(var1,_val) -> begin match var1 with
                              |(VarParam(n, minor))-> (generate_with_depth env_major consts_tbl fvars_tbl _val ) ^ "\n" ^
                              "mov qword [rbp + 8* (4 + "^ (string_of_int(minor)) ^ ")], rax" ^ "\n"^
                              "mov rax, SOB_VOID_ADDRESS" ^ "\n"          
        
                              |(VarBound(n,major,minor))-> (generate_with_depth env_major consts_tbl fvars_tbl _val )^"\n"^ 
                              "mov rbx, qword [rbp + 8 * 2]"^"\n"^
                              "mov rbx, qword [rbx + 8 * "^(string_of_int major)^"]"^"\n"^
                              "mov qword [rbx + 8 * "^(string_of_int minor)^"], rax"^"\n"^
                              "mov rax, SOB_VOID_ADDRESS"         
        
                              |(VarFree(v1)) -> (generate_with_depth env_major consts_tbl fvars_tbl _val )^"\n"^ 
                              "mov qword [fvar_tbl + WORD_SIZE*"^ string_of_int(get_address_in_fvars_tbl v1 fvars_tbl )^"], rax"^"\n"^
                              "mov rax, SOB_VOID_ADDRESS" 
                              end
        
        
         | Def'(var1,_val) -> begin match var1 with 
                               |VarFree(v1) ->(generate_with_depth env_major consts_tbl fvars_tbl _val) ^ "\n" ^ 
                               "mov qword [fvar_tbl + WORD_SIZE*" ^ string_of_int(get_address_in_fvars_tbl v1 fvars_tbl )^"], rax"^"\n"^
                               "mov rax, SOB_VOID_ADDRESS"
                               | _ -> "" 
                              end
         | Or'(list_of_exps) -> let generated_exps_'= List.map (fun (expr_')-> (generate_with_depth env_major consts_tbl fvars_tbl expr_')) list_of_exps in
                                let _Or_lexit_label = (append_unique_number_to_label  "lexit") in
                                (String.concat ("\n" ^ "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^ "jne " ^ _Or_lexit_label^"\n") generated_exps_') ^
                                "\n" ^ _Or_lexit_label ^ ":\n" 
        
      
        
        
        
        
        
        | Applic'(e1,args) -> let num_of_args= "push "^(string_of_int (List.length args)) in
                              let generated_proc= (generate_with_depth env_major consts_tbl fvars_tbl e1) in
                              let generated_args_list = List.map (fun (expr_')-> (generate_with_depth env_major consts_tbl fvars_tbl expr_')^ "\npush rax\n" ) (List.rev args) in 
                              let generated_args= String.concat "" generated_args_list in
                              generated_args ^ "\n" ^
                              num_of_args^ "\n" ^
                              generated_proc ^ "\n" ^
                              (* here i skiped checking if the type of proc is closure*)
                              "CLOSURE_ENV rbx,rax \n" ^ (* here rbx points to the env of proc closure *)
                              "push rbx\n" ^ 
                              "CLOSURE_CODE rax,rax \n" ^ (* here rbx points to the code of proc*)
                              "call rax \n" ^ (* calling the code*)
                              "add rsp, 8*1 \n" ^ (* after ret, we clean the stack (n,envs, args*)
                              "pop rbx \n" ^
                              "shl rbx, 3 \n" ^
                              "add rsp, rbx \n"  
        
        
        
        
        
        
        
        
         | ApplicTP'(e1,args)-> let applic_tp_label= append_unique_number_to_label_tp  "overideFrame" in
                                let num_of_args= "push "^(string_of_int (List.length args)) in
                                let generated_proc= (generate_with_depth env_major consts_tbl fvars_tbl e1) in
                                let generated_args_list = List.map (fun (expr_')-> (generate_with_depth env_major consts_tbl fvars_tbl expr_')^ "\npush rax\n" ) (List.rev args) in 
                                let generated_args= String.concat "" generated_args_list in
                                generated_args ^ "\n" ^
                                num_of_args^ "\n" ^
                                generated_proc ^ "\n" ^ 
                                
                                "CLOSURE_ENV rbx,rax \n" ^ (* here rbx points to the env of proc closure *)
                                "push rbx " ^"\n" ^ 
                                "push qword [rbp + 8 * 1] "^"\n"^
                                
                                (***** here we make the code that fixing the stack and make overiding ****)
                                get_overide_frame_code_Apptp applic_tp_label ^ "\n" ^
                               
                               
                               
        
                               
                                "mov rbp, r10 ;Make rbp points to old rbp (exists in r10)" ^ "\n"^
                                "add r8,8 ;" ^ "\n"^ 
                                "mov rsp, r8 ; " ^ "\n"^
                                "CLOSURE_CODE rdi,rax ; " ^ "\n"^
                                "jmp rdi"^"\n"^
                                (* rax points to the proc clousre code, its in rax since the last generate call was with proc *)
                                "CLOSURE_CODE rbx,rax ; rbx now points to the proc clousre code, its in rax since the last generate call was with proc" ^ "\n"^
                                "jmp rbx ; make the application, jumping to the code" ^"\n"   
        
        
                 
        
         | LambdaSimple'(vars,body) -> let generated_body=(generate_with_depth (env_major+1) consts_tbl fvars_tbl body) in
                                       let current_parametrs_array_code = (get_major_0_array_code "r11" ) in (* now r11 points to array of new parameters*)
                                       let extended_env_code= get_extend_env_code "r13" env_major in (* now r13 points to extended env *)
                                       let lcode_label= append_unique_number_to_label  "Lcode" in
                                       let lcont_label= append_unique_number_to_label  "Lcont" in
                                       extended_env_code^ "\n" ^ (* after extinding env, major 0 is empty*)
                                       current_parametrs_array_code ^ "\n" ^
                                       "mov qword [r13],r11 ; putting the array in the first major,"^ "\n" ^
                                       "MAKE_CLOSURE(rax, r13, "^lcode_label^" ) " ^ "\n" ^
                                       "jmp " ^ lcont_label ^ "\n" ^
                                       lcode_label^":" ^"\n" ^
                                       " push rbp"^"\n"^
                                       " mov rbp, rsp"^"\n "^ 
                                       generated_body ^"\n"^
                                       " leave" ^ "\n" ^
                                       " ret" ^ "\n" ^ 
                                       lcont_label^":"^"\n" 
                                       
        
      
        
        
        
        
         | LambdaOpt'(args, opt, body) -> let loopsh_start_label= append_unique_number_to_label  "shift_loop_start" in
                                          let pre_lcont_label= append_unique_number_to_label "pre_lcont_label" in
                                          (*let generated_body= (generate_with_depth (env_major+1) consts_tbl fvars_tbl body) in*)
                                          let current_parametrs_array_code = (get_major_0_array_code "r11" ) in (* now r11 points to array of new parameters*)
                                          let extended_env_code= get_extend_env_code "r13" env_major in (* now r13 points to extended env *)
                                          let lcode_label= append_unique_number_to_label  "LcodeOpt" in
                                          let lcont_label= append_unique_number_to_label  "LcontOpt" in
                                          let argsnum_greater_than_argslen_label= append_unique_number_to_label  "argsnum_greater_than_argslen" in
                                          let args_len= string_of_int (List.length args) in
                                          let args_len_plus_one= string_of_int ((List.length args)+1) in
                                                extended_env_code^ "\n" ^ (* after extinding env, major 0 is empty*)
                                                current_parametrs_array_code ^ "\n" ^
                                                "mov qword [r13],r11 ; putting the array in the first major,"^ "\n" ^
                                                "MAKE_CLOSURE(rax, r13, "^lcode_label^" ) " ^ "\n" ^
                                                "jmp " ^ lcont_label ^ "\n" ^
                                                lcode_label ^": " ^ "\n" ^
        
                                                "xor rcx, rcx" ^ "\n" ^
                                                "add rcx, [rsp + 8*2]" ^ "\n" ^
                                                "cmp rcx, "^args_len ^"; here rcx= num of args" ^ "\n" ^
                                                "jne " ^ argsnum_greater_than_argslen_label ^ "\n" ^
        
                                                (* here argsnum equal to argsnum (in the stack)*)
                                                "xor r8, r8" ^ "\n" ^
                                                "add r8, 3" ^ "\n" ^
                                                "add r8, " ^ args_len ^ "\n" ^
                                                "xor rdx, rdx " ^ "\n" ^
                                                loopsh_start_label ^": " ^ "\n" ^
                                                " mov r10, [rsp + rdx*8]" ^ "\n" ^
                                                " mov qword[rsp + (rdx-1)*8], r10 " ^ "\n" ^
                                                " inc rdx" ^ "\n" ^
                                                " dec r8" ^ "\n" ^
                                                " cmp r8, 0" ^ "\n"^
                                                " jne "^loopsh_start_label^ "\n"  ^ "\n" ^
                                                (* now we fix rsp and add 1 to argnum and make the last arg in the top of the stack empty list*)
                                                "sub rsp, 8 ; fixing rsp" ^ "\n"^ 
                                                "mov qword[rsp+2*8], " ^ args_len_plus_one ^ " ; adding 1 to argnum in the stack" ^ "\n" ^
                                                "mov qword[rsp + 2*8 + 8*" ^args_len_plus_one ^ "], SOB_NIL_ADDRESS" ^ "\n" ^
                                                "jmp " ^ pre_lcont_label ^ "\n" ^
        
        
                                                argsnum_greater_than_argslen_label ^": " ^ "\n" ^ 
                                                " "^(get_opt_args_lst_code args_len) ^ "\n" ^ (*we save the list pointer in r15 *)
                                                " "^(get_shift_noteq_loop_code args_len_plus_one) ^ "\n" ^
                                                " "^ "mov qword[rsp+ 2*8], " ^ args_len_plus_one ^ "\n" ^
                                                " "^ "mov qword[rsp+ 2*8 + 8*" ^ args_len_plus_one ^ "], r15 ; here we put the list af opt args as the last arg" ^ "\n" ^
                                                pre_lcont_label ^ ":" ^ "\n" ^
                                                "   "^ "push rbp"^"\n"^
                                                "   "^ "mov rbp, rsp"^"\n "^ 
                                                "   "^ (generate_with_depth (env_major+1) consts_tbl fvars_tbl body) ^ "\n"^
                                                "   "^"leave" ^ "\n" ^
                                                "   "^"ret" ^ "\n" ^
                                                lcont_label ^ ": " ^ "\n" 
        
 
 ;;
 
 
 let generate consts fvars e = generate_with_depth 0 consts fvars e ;;



end;;

open Code_Gen;; 


