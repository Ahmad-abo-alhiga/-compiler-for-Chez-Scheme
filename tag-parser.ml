 #use "reader.ml";;
open Reader;;
open PC;;


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
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let rec list_of_tuples tuple =
  match tuple with 
  | Nil ->  []
  | Pair(a, Pair(b,c))    ->  a :: (list_of_tuples (Pair(b,c)))
  | Pair(a , Nil) -> [a]
  | Pair(a,b) -> a :: [b]
  | _ -> [];;

let rec tuple_of_lis lis = 
  match lis with 
  | [] -> Nil
  | head :: [] -> Pair(head,Nil)
  | head :: tail -> Pair(head, tuple_of_lis tail)


let rec is_properList tuples = 
  match tuples with 
  | Nil -> true
  | Pair(x, Nil)-> true
  | Pair(x, Pair(y, z)) -> is_properList(Pair(y, z))
  | Pair (x,y) -> false
  | _ ->  false;;


  let str_of_sym_list lis = 
    List.map (fun sym -> match sym with 
    | Symbol(s) -> s
    | _ -> raise PC.X_no_match) lis;;

let rec get_left_side lis = 
  match lis with 
  | [ele] ->  []
  | head :: tail -> head :: get_left_side(tail)
  | _ -> [];;

let get_right_side lis = 
  let lis_reverse = List.rev lis in
   match lis_reverse with
  | last :: rest -> last
  
  | _ -> raise PC.X_no_match;;


let split_args args_with_vals = 
  let args = List.map (fun rib -> match rib with 
  | Pair(Symbol(name),Pair(sexp,_)) -> Symbol(name)
  | _ -> raise PC.X_no_match) args_with_vals in 
  tuple_of_lis args;;
  

  let  split_vals args_with_vals = 
    List.map (fun rib -> match rib with 
    | Pair(Symbol(name),Pair(sexp,_)) -> sexp
    | _ -> raise PC.X_no_match) args_with_vals;;




    let rec get_sets args=
      match args with
      | Pair(arg, Nil)-> Pair(Pair(Symbol("set!"),arg),Nil)
      | Pair(arg,tail)-> Pair(Pair(Symbol("set!"),arg) ,get_sets tail)
      | _ -> raise PC.X_no_match

    
    let rec get_whatevers varslst=
      match varslst with
      | [] -> Nil
      | Symbol(head) :: tail -> Pair(Pair(Symbol(head),Pair(Pair(Symbol("quote"), Pair (Symbol("whatever"), Nil)),Nil)),get_whatevers tail)
      | _ -> raise PC.X_no_match
       
      
      
    let rec append_sets_let sets emptylet=
      match sets with
      | Pair(lastarg,Nil) -> Pair(lastarg, Pair(emptylet,Nil))
      |Pair(head,rest) -> Pair (head,append_sets_let rest emptylet)
      | _ -> raise PC.X_no_match    


let rec tag_parse_sexps sexpr = 
  match sexpr with
  | Pair(Symbol ("quote"), Pair(sexp,Nil))   -> Const(Sexpr(sexp))
  | Pair(Symbol ("unquote"), Pair(sexp,Nil)) -> Const(Sexpr(sexp))
  | Bool   (_)    -> Const(Sexpr (sexpr))
  | Char   (_)    -> Const(Sexpr (sexpr))
  | Number (_)    -> Const(Sexpr (sexpr))
  | Symbol (_)    -> parse_Vars sexpr
  | String (_)    -> Const(Sexpr (sexpr))
  |Pair (Symbol("let*"),_) -> parse_let_star sexpr
  | Pair (Symbol("if"), sexp)   -> parse_if_exp sexp
  | Pair (Symbol("or"), sexp)   -> parse_disjunction sexp
  | Pair (Symbol("set!"),   Pair(var,  Pair(vals,Nil)))  -> handleSet var vals
  | Pair (Symbol ("define"), Pair(Pair(func_name,args), body)) -> handle_MIT_macro func_name args body
  | Pair (Symbol("define"), Pair(name, Pair(expr,Nil)))  -> handleDefine name expr
  | Pair (Symbol("begin"),sexp)    -> parse_sequences sexp
  | Pair (Symbol("lambda"),sexp)   -> parse_lambda sexp
  | Pair (Symbol("and"), _)   -> handle_and sexpr
  | Pair (Symbol("quasiquote"), _)            -> handle_quasiquote sexpr
  | Pair (Symbol("let"),Pair(args,body))-> leet_macro args body
  | Pair(Symbol ("cond"), sexps)    ->  cond_expand sexps
  | Pair(Symbol ("pset!"), sexps)    ->  parse_pset sexpr
  | Pair (Symbol("letrec"),Pair(args,body))      -> handle_letrec_macro  args body

  | Pair (func, prams) -> handleApplic func prams
  | _ ->  raise PC.X_no_match
  

and handleVar str = 
  if List.mem str reserved_word_list then raise PC.X_no_match
                                     else Var(str)

  
and parse_Vars sexpr = 
  match sexpr with 
  |Symbol(varName) -> handleVar(varName)
  | _ -> raise PC.X_no_match

and parse_disjunction sexp = 
  match sexp with  
  | Nil          -> Const(Sexpr(Bool(false)))
  | Pair(s, Nil) -> tag_parse_sexps s 
  | Pair (b1,b2) -> handle_bool_pairs sexp
  | _            -> raise PC.X_no_match


and handle_bool_pairs sexp = 
  Or(List.map tag_parse_sexps (list_of_tuples sexp))
  

and handleSet var vals = 
  Set( (tag_parse_sexps var) , (tag_parse_sexps vals))


and handleDefine name expr = 
  Def(parse_Vars name, (tag_parse_sexps expr))



and handle_seq_list lst = 
   let exps = List.map tag_parse_sexps lst in
   Seq(exps)

and parse_sequences sexp = 
 match sexp with
 | Nil -> Const(Void)
 | Pair(head,Nil)  -> tag_parse_sexps head
 | Pair(head,tail) -> handle_seq_list (list_of_tuples sexp)
 | _ -> raise PC.X_no_match


and parse_improper_sequences body = 
match body with
| Pair(head,Nil)  -> tag_parse_sexps head
| Pair(head,tail) -> handle_seq_list (list_of_tuples body)
| _ -> raise PC.X_no_match


and handle_lambda_simpl args body =
  LambdaSimple(str_of_sym_list(list_of_tuples args) ,parse_improper_sequences body)


and make_required_args args = 
  let arg_list = str_of_sym_list(list_of_tuples args) in
    get_left_side(arg_list)

and make_optional_args args =
  match args with 
  |Symbol(varName)-> varName 
  |_-> let arg_list = str_of_sym_list(list_of_tuples args) in
    get_right_side(arg_list)

and handle_lambda_opt args body =
  LambdaOpt (make_required_args(args), make_optional_args(args),parse_improper_sequences body)  

 and parse_lambda sexp = 
 match sexp with 
 |Pair(args, body) -> if(is_properList args) then handle_lambda_simpl args body
                                             else handle_lambda_opt args body 
 | _ -> raise PC.X_no_match


and  handleApplic func prams = 
  let lis = list_of_tuples prams in 
  Applic((tag_parse_sexps func), List.map tag_parse_sexps lis)


and parse_if_exp sexp = 
  match sexp with 
  | Pair(predicate, Pair(success, Pair(fail, Nil))) -> 
        If(tag_parse_sexps predicate, tag_parse_sexps success,tag_parse_sexps fail )
  | Pair(predicate, Pair(success, Nil)) ->
        If(tag_parse_sexps predicate, tag_parse_sexps success, Const(Void))
  | _ -> raise PC.X_no_match

(********************************************)
(****************NOT-MACROS******************)
(********************************************)

and expers_params_pset ribs op =
  match op with
  | 0 -> (match ribs with 
          | Nil -> Nil
          | Pair(car, cdr) ->
                (match car with
                | Pair(caar, cdar) -> Pair(caar, expers_params_pset cdr 0)
                | _ -> raise PC.X_no_match
                )
          | _ -> raise PC.X_no_match
          )
  | 1 -> (match ribs with
        | Nil -> Nil
        | Pair(car, cdr) ->
              (match car with
              | Pair(caar, cdar) -> Pair(cdar, expers_params_pset cdr 1)
              | _ -> raise PC.X_no_match
              )
              | _ -> raise PC.X_no_match
              )
  | _ -> raise PC.X_no_match     
  
 
and make_names exprs count = 
  match exprs with 
  | Nil -> Nil
  | Pair(e, rest) ->
     Pair(Pair(Symbol(String.concat "v_" ["";(string_of_int count)]), e), make_names rest (count + 1))
  | _ -> raise PC.X_no_match   

and make_set params vals = 
  match params, vals with
  | Nil, _ -> Nil
  | Pair(var1, rest_vars), Pair(expr1, rest_exprs) ->  Pair(Pair(Symbol("set!"), Pair(var1, Pair(expr1, Nil))),make_set rest_vars rest_exprs)
  | _ -> raise PC.X_no_match

and parse_pset sexpr = 
  match sexpr with
  | Pair(Symbol("pset!"), ribs) -> 
  let pset_ribs_params = expers_params_pset ribs 0 in
  let pset_ribs_exprs = expers_params_pset ribs 1 in
  let new_vars = make_names pset_ribs_exprs 0 in 
  let ts = expers_params_pset new_vars 0 in 
  let assign_sets = make_set pset_ribs_params ts in
  tag_parse_sexps (Pair(Symbol("let"), Pair(new_vars, assign_sets))) 
  | _ -> raise PC.X_no_match
 
and handle_and sexp = 
    match sexp with
    | Pair (Symbol("and"),Nil)-> tag_parse_sexps (Bool(true))
    | Pair (Symbol("and"),Pair(exp1,Nil))-> tag_parse_sexps (exp1)
    | Pair (Symbol("and"),Pair(exp1,body))-> tag_parse_sexps (Pair(Symbol"if",(Pair(exp1,Pair(Pair(Symbol("and"),body),Pair(Bool(false),Nil))))))
    | _ -> raise PC.X_no_match

and handle_quasiquote sexp=
      match sexp with
      | Pair (Symbol("quasiquote"),Pair(Symbol("unquote"),Pair(sexpr1,Nil)))-> tag_parse_sexps sexpr1
      | Pair (Symbol("quasiquote"),Pair(Symbol("unquote-splicing"), _ ))-> raise PC.X_no_match  
      
      | Pair (Symbol("quasiquote"),Pair(sexprs,Nil))->  let rec expand sexplst =
                                                                    match sexplst with  
                                                                      | Pair(Symbol("unquote"), Pair(head, Nil)) -> head 
                                                                      | Pair(Symbol("unquote-splicing"), _) -> raise PC.X_no_match 
                                                                      | Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
                                                                      | Symbol(x) -> Pair(Symbol("quote"), Pair(sexplst, Nil))
                                                                      | Pair(car', cdr') -> ( match (car', cdr') with
                                                                                            | ( Pair (Symbol("unquote-splicing"), Pair(head, Nil)), _)-> Pair(Symbol("append"),Pair(head, Pair(expand cdr', Nil)))
                                                                                            | (_ , Pair(Symbol("unquote-splicing"), Pair(head, Nil)))-> Pair(Symbol("cons"), Pair(expand car', Pair(head , Nil)))
                                                                                            | (_ , _) -> Pair(Symbol("cons"), Pair(expand car', Pair(expand cdr', Nil))))
                                                                      | _ -> raise PC.X_no_match 
                                                                  in 
                                                                  let x= expand (sexprs) in
                                                                  tag_parse_sexps (x)       
    

    | _ -> raise PC.X_no_match    

and handle_MIT_macro func_name args body =
  let x = create_def_lambda func_name args body in
  tag_parse_sexps x  

and create_def_lambda func_name args body =
Pair (Symbol "define",
Pair (func_name,
 Pair
  (Pair (Symbol "lambda",
    Pair (args, body)),
  Nil)))

and cond_without_rest test app = 
Pair (Symbol "let",
Pair
 (Pair (Pair (Symbol "value", Pair (test, Nil)),
   Pair
    (Pair (Symbol "f",
      Pair (Pair (Symbol "lambda", Pair (Nil, Pair (app, Nil))),
       Nil)),
    Nil)),
 Pair
  (Pair (Symbol "if",
    Pair (Symbol "value",
     Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
      Nil))),
  Nil)))


and cond_with_rest test app rest = 
Pair (Symbol "let",
Pair
 (Pair (Pair (Symbol "value", Pair ( test, Nil)),
   Pair
    (Pair (Symbol "f",
      Pair (Pair (Symbol "lambda", Pair (Nil, Pair (app, Nil))),
       Nil)),
    Pair
     (Pair (Symbol "rest",
       Pair
        (Pair (Symbol "lambda", Pair (Nil, Pair (cond_macro_expander rest,  Nil))),
        Nil)),
     Nil))),
 Pair
  (Pair (Symbol "if",
    Pair (Symbol "value",
     Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
     Pair(Pair(Symbol "rest", Nil), Nil)))),
  Nil)))


and if_cond_with_rest test sequance rest =  
 (Pair(Symbol("if"),
  Pair (test, Pair(
   Pair(Symbol("begin"), sequance), Pair(cond_macro_expander rest,Nil)))))

and if_cond_without_rest test sequance = 
(Pair(Symbol("if"),
  Pair (test, Pair(
   Pair(Symbol("begin"), sequance),Nil))))


and lambda_of_cond test app rest= 
  match rest with 
  | Nil -> cond_without_rest test app
  | _   -> cond_with_rest test app rest

and ifExpr_of_cond test sequance rest = 
  match rest with 
  | Nil -> if_cond_without_rest test sequance
  | _   -> if_cond_with_rest test sequance rest


  and parse_let_star sexpr =
  match sexpr with
  | Pair(Symbol("let*"), Pair(Nil, body)) -> tag_parse_sexps (Pair(Symbol("let"), Pair(Nil, body)))
  | Pair(Symbol("let*"), Pair(Pair(rib, Nil), body)) -> tag_parse_sexps (Pair(Symbol("let"), Pair(Pair(rib, Nil), body)))
  | Pair(Symbol("let*"), Pair(Pair(rib, ribs), body)) -> tag_parse_sexps (Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(ribs, body)), Nil))))
  | _ -> raise PC.X_no_match   

  and cond_macro_expander sexps =
    match sexps with
    | Pair(Pair(Symbol "else" , sequance), _) -> (Pair(Symbol "begin", sequance))
    | Pair(Pair(test, Pair(Symbol("=>"),Pair(app,Nil))),rest) -> lambda_of_cond test app rest
    | Pair(Pair(test,sequance),rest) -> ifExpr_of_cond test sequance rest
    | _ -> raise PC.X_no_match


  and cond_expand sexps =
    let x = (cond_macro_expander sexps) in
    tag_parse_sexps x  



    and  handle_letrec_macro args body =
     let helplst=  List.map (fun rib -> match rib with 
      | Pair(Symbol(name),Pair(sexp,_)) -> Symbol(name)
      | _ -> raise PC.X_no_match) (list_of_tuples args)  in (*  here we get [f1,f2,...]   *)
      
      
      let whateverargs = get_whatevers helplst in
      let sets = get_sets args in
      let emptylet= Pair (Symbol("let"),Pair(Nil,body)) in
      let letrec_body= append_sets_let sets emptylet in
      tag_parse_sexps (Pair(Symbol("let"),Pair(whateverargs,letrec_body)))
       


  and leet_macro args_with_vals body =
    let list_ribs = list_of_tuples args_with_vals in
    let args = split_args list_ribs in
    let vals = split_vals list_ribs in
    Applic((handle_lambda_simpl args body), List.map tag_parse_sexps vals);;


  let tag_parse_expressions sexpr = 
   List.map(tag_parse_sexps)sexpr;;
  
end;; (* struct Tag_Parser *)
 


