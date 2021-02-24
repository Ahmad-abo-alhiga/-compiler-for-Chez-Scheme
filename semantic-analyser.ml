
 #use "tag-parser.ml";;
open PC;;
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
  | Set' of var * expr'
  | Def' of var * expr'
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
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
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
  let list_of_string s = 
    List.append [s] [];;
  
  let rec getElement lis index = 
    match lis,index with
    | [] , _  -> []
    | head::tail, i -> if (i = 0) then  head
                                    else (getElement tail (i-1));;
  
  
  let rec getIndex lis str index= 
    match lis with 
    | [] -> -1
    | head :: tail -> if(head = str) then index else (getIndex tail str (index+1));;
    
  let rec get_major_index env str index = 
    match env with
    | [] -> -1
    | head::tail -> let check4Str = getIndex head str 0 in
                    if(check4Str = -1) then (get_major_index tail str (index+1)) else index;;
  
  let get_minor_index env str index =
    let major_index = get_major_index env str 0 in
    if(major_index != -1) then  getIndex (getElement env major_index) str 0
                          else -1;;
  
      
   let rec chech_4_same_parent to_check args_env check_env  = 
    match args_env with
    | [] -> false
    | head::tail -> get_T_F_parent to_check args_env check_env head tail

    and get_T_F_parent to_check args_env check_env head tail = 
      let exp1 =  List.exists (fun x -> x = head) check_env in
      if (exp1 = true) then check_not_mem to_check args_env check_env head tail
      else chech_4_same_parent to_check tail check_env 

  and check_not_mem to_check args_env check_env head tail = 
      let exp2 = List.mem to_check  head in 
      if(exp2 = true) then chech_4_same_parent to_check tail check_env
       else true;;





      
     let rec check_4_same reads writes = 
      match reads with 
      | head :: tail  -> check_4_same_rib_write head tail reads writes
      | [] ->   return_t_if_no_writes writes


      and return_t_if_no_writes lis = 
      match lis with 
      | [] ->   true
      | _ ->    false



    and check_4_same_rib_write head tail lis1 lis2 = 
      match lis2 with 
      | [] -> false
      | head2::tail2 -> if(head = head2) then check_4_same tail tail2 else false   


      let continue_check_vars2 check_read_v reads check_write_v writes=  
        if ((check_4_same reads writes)) then false else true    
    
  

      let continue_check_vars1 check_read_v reads check_write_v writes =
        if  (chech_4_same_parent check_read_v reads writes ) then false
         else  continue_check_vars2 check_read_v reads check_write_v writes



      let check_vars check_read_v reads check_write_v writes = 
        if ( check_read_v = check_write_v) 
          then continue_check_vars1 check_read_v reads check_write_v writes
          else false



  


        
      
  
  
  
      
  
  (***DONE**)
      let rec extend_criteria_fst_helper vars params = 
          match vars with 
          | [] -> []
          | head :: tail -> Set'( VarParam(head, getIndex params head 0), Box'(VarParam(head, getIndex params head 0 ))) :: (extend_criteria_fst_helper tail params)
          
  
          let append_set_as_seq to_be_reaplaced body = 
            match body with 
            | Seq'(seq) -> Seq'(List.append to_be_reaplaced seq)
            | expr -> Seq'(List.append to_be_reaplaced [expr])    
  
      let extend_criteria_fst vars params body =
        let to_be_reaplaced = extend_criteria_fst_helper vars params in 
        append_set_as_seq to_be_reaplaced body;;
        
  
  
      let rec get_read_occur_as_list expr depth env curr_params = 
        match expr with
        | Const'(exp')      ->  []
        | Var'(_)           ->   get_read_occur_var expr depth curr_params env
        | Def'(var, _val)   ->   get_read_occur_as_list _val depth env curr_params
        | Set'(var, _val)   ->   get_read_occur_as_list _val depth env curr_params
        | If'(test,first,second)  -> if_read_occur  test first second depth env curr_params
        | Or' (or_list)    ->   handle_list_read or_list expr depth env curr_params
        | Seq'(e_list)     ->   handle_list_read e_list expr depth env curr_params
        | LambdaSimple'(args, body)             -> get_read_occur_as_list body (depth + 1) ( curr_params::env) args
        | LambdaOpt'(args, opt, body)           ->  get_read_occur_as_list body (depth + 1) ( curr_params::env) (((List.append args [opt])))
        | Applic'(body, args) ->  List.append (get_read_occur_as_list body depth env curr_params) ( List.fold_left ( fun acc exp -> List.append acc (get_read_occur_as_list exp depth env curr_params))  [] args)
        | ApplicTP'(body, args) -> List.append (get_read_occur_as_list body depth env curr_params) ( List.fold_left ( fun acc exp -> List.append acc (get_read_occur_as_list exp depth env curr_params))  [] args)
        | BoxGet'(_) -> []
        | Box'(_) -> []
        | BoxSet'(var,_val) -> get_read_occur_as_list _val depth env curr_params
        



        and handle_list_read lis expr depth env curr_params =
          List.fold_left (fun acc exp -> (List.append acc (get_read_occur_as_list exp depth env curr_params)) ) [] lis
          
  
        and if_read_occur test dit dif depth env cur_closure_params= 
        let test_read = get_read_occur_as_list test depth env cur_closure_params in
        let dit_read = get_read_occur_as_list dit depth env cur_closure_params in
        let dif_read = get_read_occur_as_list dif depth env cur_closure_params in
        List.append (List.append test_read dit_read) dif_read
  
  
      and get_read_occur_var expr depth curr_params env = 
        match expr with
        | Var'(VarBound(v,major,minor)) -> if(depth -1 == major) then [v, curr_params::env] else []
        | Var'(VarParam(v , minor))     -> if(depth == 0 ) then [v,curr_params::env] else []
        | _ -> [];;
  
  
        let rec get_write_occur_as_list expr depth env curr_params = 
          match expr with
          | Const'(exp')      ->  []
          | Var'(_)           ->  []
          | Def'(var, _val)   ->   get_write_def var _val depth env curr_params
          | Set'(var, _val)   ->   get_write_def var _val depth env curr_params
          | If'(test,first,second)  -> if_write_occur  test first second depth env curr_params
          | Or' (or_list)    -> handle_list_write or_list expr depth env curr_params
          | Seq'(e_list)     -> handle_list_write e_list expr depth env curr_params
          | LambdaSimple'(args, body)             -> get_write_occur_as_list body (depth + 1) ( curr_params::env) args
          | LambdaOpt'(args, opt, body)           ->  get_write_occur_as_list body (depth + 1) ( curr_params::env) (((List.append args [opt])))
          | Applic'(body, args) ->  List.append (get_write_occur_as_list body depth env curr_params) ( List.fold_left ( fun acc exp -> List.append acc (get_write_occur_as_list exp depth env curr_params))  [] args)
          | ApplicTP'(body, args) -> List.append (get_write_occur_as_list body depth env curr_params) ( List.fold_left ( fun acc exp -> List.append acc (get_write_occur_as_list exp depth env curr_params))  [] args)
          | BoxGet'(_) -> []
          | Box'(_) -> []
          | BoxSet'(var,_val) -> get_write_occur_as_list _val depth env curr_params
          



      and handle_list_write lis expr depth env curr_params =
        List.fold_left (fun acc exp -> (List.append acc (get_write_occur_as_list exp depth env curr_params)) ) [] lis    
  
  
      and get_or_rw lst depth env curr_params = 
        match lst with 
        | [] -> []
        | head::tail ->  get_write_occur_as_list head depth env curr_params :: get_or_rw tail depth env curr_params
        
  
      and get_write_def var _val depth env curr_params = 
        let lst = get_write_occur_as_list  _val depth env curr_params in 
         (List.append (get_write_occur_var var depth curr_params env ) lst)
  
      and if_write_occur test dit dif depth env cur_closure_params= 
        let test_write = get_write_occur_as_list test depth env cur_closure_params in
        let dit_write = get_write_occur_as_list dit depth env cur_closure_params in
        let dif_write = get_write_occur_as_list dif depth env cur_closure_params in
        List.append (List.append test_write dit_write) dif_write
  
        and get_write_occur_var var depth curr_params env = 
        match var with
        | VarBound(v,major,minor) -> if(depth -1 == major) then [v, curr_params::env] else []
        | VarParam(v , minor)     -> if(depth == 0 ) then [v,curr_params::env] else []
        | _ -> [];;
  
  
    let rec extend_criteria_thrd (var : string) expr'=
      match expr' with
      | Const'(exp')        ->      Const'(exp')
      | Var'(_)             ->      handle_3_crit_var  var expr'
      | Def'(_var, _val)    ->      Def'(_var, extend_criteria_thrd var _val )
      | Set'(_)             ->      handle_set_thrd var expr'
      | If'(test,first,second)  ->  If'(extend_criteria_thrd var test , extend_criteria_thrd var first , extend_criteria_thrd var second )
      | Or' (or_list)       ->      Or'(handle_or_thrd var or_list)
      | Seq'(e_list)        ->      Seq'(handle_or_thrd var e_list )
      | LambdaSimple'(args, body)             -> handle_lambdaSimpl_thrd var args body
      | LambdaOpt'(args, opt, body)           -> handle_lambdaOpt_thrd var args opt body 
      | Applic'(body, args) ->       handle_applic_thrd var body args
      | ApplicTP'(body, args) ->     handle_applicTP_thrd var body args 
      | BoxGet'(_var) -> BoxGet'(_var)
      | Box'(_var) -> Box'(_var)
      | BoxSet'(_var,_val) -> BoxSet'(_var,extend_criteria_thrd var _val) 
      
  
  
  
    and handle_set_thrd var expr' = 
      match expr' with 
      | Set'(_var,Box'(var_box))               ->   Set'(_var,Box'(var_box))
      | Set'(VarParam(v,minor),_val)           ->   check_name_set var _val v (VarParam(v,minor))
      | Set'(VarBound(v,major,minor),_val)     ->   check_name_set var _val v (VarBound(v,major,minor))
      | Set'(VarFree(v), _val)                 ->   check_name_set var _val v (VarFree(v))
      | _ -> raise X_no_match
      
    and handle_3_crit_var  var expr' = 
      match expr' with 
      | Var'(VarParam(v,minor)) -> check_name_varParam v var minor
      | Var'(VarBound(v,major,minor))  -> check_name_varBound v major minor var
      | e -> e
      
      
    and check_name_varParam v var minor= 
      if v = var then BoxGet'(VarParam(v,minor))  else Var'(VarParam(v,minor))
    
    and check_name_varBound v major minor var = 
      if v = var then BoxGet'(VarBound(v,major,minor))  else Var'(VarBound(v,major,minor))
  
    and check_name_set var _val v set_var=  
      if (v = var)
       then BoxSet'(set_var,extend_criteria_thrd v _val) else Set'(set_var,extend_criteria_thrd var _val)
          
    and handle_or_thrd var or_list = 
    
      match or_list with 
      | [] -> []
      | head :: tail ->  extend_criteria_thrd var head :: handle_or_thrd var tail
      
  
  
    and handle_lambdaSimpl_thrd var args body = 
      let i = getIndex args var 0  in
      if i = -1 then LambdaSimple'(args,extend_criteria_thrd var body) else LambdaSimple'(args,body)
  
    and handle_lambdaOpt_thrd var args opt body  = 
      let all_params  = (List.append args [opt]) in 
      let i = getIndex all_params var 0 in 
      if i = -1 then LambdaOpt'(args,opt,extend_criteria_thrd var body) else LambdaOpt'(args,opt,body)
  
  
    and handle_applic_thrd var body args = 
      let new_args =  handle_or_thrd var args in 
      Applic'(extend_criteria_thrd var body , new_args)
  
  
    and handle_applicTP_thrd var body args = 
      let new_args =  handle_or_thrd var args in 
      ApplicTP'(extend_criteria_thrd var body , new_args)
  
  
  
      let rec handle_boxing e = 
        match e with
        | Const'(exp')      ->   Const'(exp')
        | Var'(exp')        ->   Var'(exp')
        | Def'(var, _val)   ->   Def'(var, handle_boxing _val )
        | Set'(var, _val)   ->   Set'(var, handle_boxing _val )
        | If'(test,first,second)  -> If'(handle_boxing test , handle_boxing first , handle_boxing second )
        | Or' (or_list)    -> Or'(handle_list_boxing or_list )
        | Seq'(e_list)     -> Seq'(handle_list_boxing e_list )
        | LambdaSimple'(args, body)             -> handle_lambdaSimpl_boxing args body
        | LambdaOpt'(args, opt, body)           -> handle_lambdaOpt_boxing args opt body 
        | Applic'(body, args) -> handle_Applic_boxing body args 
        | ApplicTP'(body, args) -> handle_ApplicTP_boxing body args 
        | _ -> let () = Printf.printf "\n%s\n" ("BOXING") in raise X_no_match
      
      
      
        and handle_list_boxing lis  =
        match lis with
        | []   ->   []
        | head::tail ->   (List.append [(handle_boxing head )] (handle_list_boxing tail ))
        
        
        and handle_Applic_boxing body args = 
         Applic'(handle_boxing body , handle_list_boxing args )
        
        and handle_ApplicTP_boxing body args= 
          ApplicTP'(handle_boxing body , handle_list_boxing args )
      
      
       and handle_lambdaOpt_boxing args opt body = 
        let lambda = LambdaOpt'(args, opt, handle_boxing body ) in 
          start_boxing lambda
        
       
       and handle_lambdaSimpl_boxing args  body = 
        let lambda = LambdaSimple'(args, handle_boxing body )  in
        start_boxing lambda
      
       and start_boxing lambda = 
          match lambda with
          | LambdaSimple'(args, body) -> create_box lambda args body
          | LambdaOpt'(args, opt, body) -> create_box lambda (List.append args [opt]) body 
          | _ -> let () = Printf.printf "\n%s\n" ("start_boxing") in raise X_no_match
      
      and create_box lambda args body = 
        if(args = []) then  lambda else  get_boxing lambda args body
      
      and get_boxing lambda args body = 
        let box_me  = get_vars_boxing  args body in  
        if (box_me = [] ) then lambda else continue_boxing box_me lambda args body
      
      and continue_boxing box_me lambda args body= 
        let get_body_fst = extend_criteria_fst box_me args body   in
        let done_fst =  get_body_boxing get_body_fst box_me  in
          get_lambdas done_fst lambda body args
      
      
      and get_body_boxing get_body_fst box_me= 
        List.fold_left (fun acc var -> extend_criteria_thrd var acc) get_body_fst box_me 
      
      
      and get_lambdas done_fst lambda body args= 
        match lambda with 
        | LambdaOpt'(mandatory, optional, _) -> LambdaOpt'(mandatory, optional, done_fst)
        | LambdaSimple'(params,_) -> LambdaSimple'(params,done_fst)
        | _ -> let () = Printf.printf "\n%s\n" ("Get-BOXING") in raise X_no_match
      
      
      and  get_vars_boxing (params : string list)  body  =
        let reads = get_read_occur_as_list body 0 [] params   in
        let writes = get_write_occur_as_list body 0 [] params in
        check_read_write_criteria reads writes params
      
      
      
      and check_read_write_criteria reads writes args= 
        continue_read_write ( (List.fold_left (fun acc (var1, env1) -> 
        if (List.exists (fun (var2, env2) ->
        check_vars var1 env1 var2 env2) writes)
         then var1::acc else acc )
          [] reads) ) args
        
      
      and continue_read_write lis args = 
        List.fold_right (fun param acc  -> 
        if (List.mem param lis) 
        then param::acc else acc) 
        args []
      
      
      
            
      
      let rec handle_tail_calls e in_tp = 
        match e with 
        | Const'(exp')      ->   Const'(exp')
        | Var'(exp')        ->   Var'(exp')
        | Def'(var, _val)   ->   Def'(var, handle_tail_calls _val false)
        | Set'(var, _val)   ->   Set'(var, handle_tail_calls _val false)
        | If'(test,first,second)  -> If'(handle_tail_calls test false, handle_tail_calls first in_tp, handle_tail_calls second in_tp)
        | Or' (or_list)    -> Or'(List.mapi (fun index expr -> if (index == ((List.length or_list) -1)) then handle_tail_calls expr in_tp else handle_tail_calls expr false) or_list)
        | Seq'(e_list)     -> Seq'(List.mapi (fun index expr -> if (index == ((List.length e_list) -1)) then handle_tail_calls expr in_tp else handle_tail_calls expr false) e_list)
        | LambdaOpt'(args, opt, body)           -> LambdaOpt'(args, opt, handle_tail_calls body true)
        | LambdaSimple'(args, body)             -> LambdaSimple'(args, handle_tail_calls body true)
        | Applic'(body, args) -> handle_Applic' body args in_tp 
        | _ -> let () = Printf.printf "\n%s\n" ("TC") in raise X_no_match
      
      
      and handle_Applic' body args in_tp = 
      if(in_tp = false) then 
            Applic'(handle_tail_calls body false, handle_list_TC args false)
      else
            ApplicTP'(handle_tail_calls body false, handle_list_TC args false) 
      
      and handle_list_TC lis in_tp =
        List.map (fun arg -> handle_tail_calls arg false ) lis
      
      let rec handle_lexical_addresses e env = 
          match e with 
          | Const(exp)  ->  Const'(exp)
          | LambdaSimple(args,body) ->(handleLambda args body (args::env))
          | LambdaOpt(strict_args , additional_args, body) ->(handleLambdaOpt strict_args additional_args body env)
          | Seq(args)   -> handle_seq args env
          | If(test,t,f) ->  If'(handle_lexical_addresses test env, handle_lexical_addresses t env, handle_lexical_addresses f env)
          | Set(Var(str),_val) ->    Set'((handle_var str env), handle_lexical_addresses _val env) 
          | Or(lis)        -> Or'(handle_OrExp lis env)
          | Def(Var(str),_val) -> Def'((handle_var str env), handle_lexical_addresses _val env)
          | Applic(lambda, vals) -> Applic' (handle_lexical_addresses lambda env, handle_OrExp vals env )
          | Var  (str)  ->  Var'(handle_var str env)
          | _ -> let () = Printf.printf "\n%s\n" ("lex") in raise X_no_match
      
      and handle_OrExp lis env=  
        List.map (fun x -> handle_lexical_addresses x env) lis
      
      and handle_seq args env = 
        Seq'(List.map (fun var -> handle_lexical_addresses var env) args) 
        
        
      and handleLambdaOpt strict_args additional_args body env = 
        let new_env=  List.append strict_args (list_of_string additional_args) in 
        let new_env=  new_env :: env in
        LambdaOpt'(strict_args,additional_args,(handle_lexical_addresses body new_env))    
      and handleLambda args body env' =
        LambdaSimple'(args,(handle_lexical_addresses body env'))
      
      and generate_var_bound_param list_params env str =
      
      
         if ( (getIndex list_params str 0)>= 0)  then VarParam(str, (getIndex list_params str 0)) 
                                                                   else gen_bound env str
      
      and gen_bound env str =
        if((get_major_index env str 0) >= 0 ) then VarBound(str,(get_major_index env str 0), (get_minor_index env str 0)) 
                                              else VarFree(str)        
      
      and handle_var str env =
        match env with 
        | list_params :: env' -> generate_var_bound_param list_params env' str
        | [] -> VarFree(str)
        ;;
                                                        
      let annotate_lexical_addresses e = (handle_lexical_addresses e []);; 
      let annotate_tail_calls e = (handle_tail_calls e false);;
      let box_set e = (handle_boxing e);;
      
      
      let run_semantics expr =
        box_set
          (annotate_tail_calls
             (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)



