
#use "pc.ml";;


open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


  let rec sexpr_eq s1 s2 =
    match s1, s2 with
    | Bool(b1), Bool(b2) -> b1 = b2
    | Nil, Nil -> true
    | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
    | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
    | Char(c1), Char(c2) -> c1 = c2
    | String(s1), String(s2) -> s1 = s2
    | Symbol(s1), Symbol(s2) -> s1 = s2
    | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
    | _ -> false;;
  
  
    let make_paired nt_left nt_right nt =
      let nt = caten nt_left nt in
      let nt = pack nt (function (_, e) -> e) in
      let nt = caten nt nt_right in
      let nt = pack nt (function (e, _) -> e) in
        nt;;  
  
  (****************************************************)
  (********************NUMBERS*************************)
  (****************************************************)
  (****************************************************)
  (**added list 2 int*)
  let list_to_int l=
  let rec f_helper l num=
    match l with
    | [] -> num
    | (h::t) -> f_helper t ((num * 10 ) + h)  in
     f_helper l 0;;
  let nt_digit_0_to_9 =
    pack ( const (fun ch -> '0' <= ch && ch <= '9'))
    (fun ch -> ( int_of_char ch) - 48 );;

  let nt_bool_t = 
    let nt_t  = word_ci "#t" in
     pack nt_t (fun(e) -> Bool(true));;
  
  let nt_bool_f =
    let nt_f = word_ci "#f" in
    pack nt_f (fun(e) -> Bool(false));;


  let nt_bool = disj nt_bool_t  nt_bool_f ;;
  
  let nt_div_slash = word "/";;

let nt_sign_plus = word "+";;
let nt_sign_minus = word "-";;
let nt_sign = disj nt_sign_plus nt_sign_minus;;
let nt_f_dot = word ".";;

  
  let nt_digit_0_to_9 =
    pack ( const (fun ch -> '0' <= ch && ch <= '9'))
    (fun ch -> ( int_of_char ch) - 48 );;
  
  let nt_natural_int =
    let rec make_nt_natural () =
    pack ( caten nt_digit_0_to_9
    ( disj ( delayed make_nt_natural )
    nt_epsilon ))
    (function (a, s) -> a :: s) in
    make_nt_natural () ;;

    


let nt_handleFloat =
  let rec make_nt_frac () =
  pack (caten nt_digit_0_to_9
  (disj (delayed make_nt_frac)
  nt_epsilon))
  (function (a, s) -> a :: s) in
  pack (make_nt_frac())
    ( fun s ->
              (List.fold_right
              ( fun a b -> float_of_int(a) *. 0.1 +. b *. 0.1)
              s
              0.0));;    
  
  
let abs_val value = 
  if value < 0 then
    -value
  else
    value

   
let nt_INT = 
  pack (caten nt_sign (nt_natural_int ))
  (fun (e,s) -> if ((List.nth (e) 0 ) = '-') then  Number(Fraction( (-1) * list_to_int s , 1)) 
                                             else Number(Fraction(  list_to_int s , 1)) );;

                                             
let nt_INT_noSign = 
  pack nt_natural_int 
  (fun (e) -> Number(Fraction(  list_to_int e , 1)) );;
 

let mul_minus = fun s -> (-1) * s;;
let mul_1 = fun s -> s;; 
let mul_minus_f = fun s -> (-1.0) *. s;;


let nt_INT_1 = 
  let nt =  nt_sign in
  pack (caten nt (nt_natural_int ))
  (fun (e,s) -> if ((List.nth (e) 0 ) = '-') then  (mul_minus (list_to_int s ) )
                                              else    (mul_1( list_to_int s ) ));;



let nt_INT_1_noSign = 
  pack nt_natural_int 
  (fun (e) -> list_to_int e );;



let nt_INT_2 = 
  let nt = nt_none in
  pack (caten nt (nt_natural_int ))
  (fun (e,s) -> list_to_int s);;


let float_frac_add = fun a b ->
                    if a >= 0 then float_of_int(a) +. b 
                    else float_of_int(a) -. b ;;

let rec  gcd a b =
   if b = 0 then a else gcd b (a mod b);;



let parse_first = disj_list [nt_INT_1; nt_INT_1_noSign];;
              
let nt_number1 a = 
  let (numerator, s)          = nt_INT_1 a in 
  try let (slash, de)         = nt_div_slash s in
      let (denominator, s)    = nt_INT_2 de in
      let _gcd = gcd (abs_val numerator) denominator in
      Number(Fraction((numerator/_gcd) , (denominator/_gcd)))

  with PC.X_no_match -> 
    try let (dot, rhs) = nt_f_dot s in 
        let (frac,rst) = nt_handleFloat rhs in
        Number(Float (float_frac_add numerator frac))

  with PC.X_no_match -> 
        Number(Fraction( numerator , 1)) ;;

let nt_frac_2nd = 
  pack nt_natural_int (fun (e) -> list_to_int e);;

let nt_frac = 
  pack (caten parse_first (caten nt_div_slash nt_frac_2nd))
  (fun (n0 , (_,n1)) -> Number(Fraction((n0/ (gcd (abs_val n0) n1) ) , (n1/(gcd (abs_val n0) n1)))));;

let nt_float = pack 
(caten parse_first (caten nt_f_dot nt_handleFloat))
(fun (n0, (_, n1)) ->  Number(Float (float_frac_add n0 n1)) );;

let nt_e = word_ci "e";; 
let nt_f_i =disj_list [nt_float ;nt_INT; nt_INT_noSign];;

let nt_scientific = pack  (caten (caten nt_f_i nt_e) parse_first)
                    (fun ((e1,_),e2)  -> 
                    match e1 with 
                    | Number(Fraction (num,1)) -> Number(Float ((float_of_int(num)  *. (10.0 ** (float_of_int e2 )))))
                    | Number(Float (num)) -> Number(Float( num *. (10.0 ** (float_of_int e2 ))))
                    |_-> raise PC.X_no_match
                    ) ;;


let nt_number = disj_list [nt_frac; nt_scientific ; nt_float; nt_INT; nt_INT_noSign];;


   
(****************************************************)
(****************************************************)
(******************SYMBOLS***************************)
(****************************************************)

let nt_digits = range '0' '9';;
let nt_lc_letters = range_ci 'a' 'z';;
let nt_lc_letters = range_ci 'A' 'Z';;
let nt_dot = char '.';;
let nt_punctuation = disj_list (
                      char '?' ::
                      char '_' ::
                      char ':' ::
                      char '/' ::
                      char '>' ::
                      char '<' ::
                      char '*' ::
                      char '+' ::
                      char '=' ::
                      char '-' ::
                      char '^' ::
                      char '$' ::
                      char '!' ::
                      []);;




let nt_punct_letter = disj nt_punctuation nt_lc_letters ;;
let nt_no_dot = disj nt_digits nt_punct_letter;;
let nt_sym = disj nt_no_dot nt_dot;;
let nt_no_one_dot = pack nt_no_dot (fun x -> [x]);;
let nt_read_all_symbols = pack (caten nt_sym  (plus nt_sym)) (fun (e,s) -> e::s);;



let nt_symbol = 
  pack
  (disj nt_read_all_symbols nt_no_one_dot)
  (fun sym_lst -> Symbol(list_to_string sym_lst ));;          
  
  let nt_number_all = (not_followed_by nt_number nt_symbol);;  
(****************************************************)
(*********************STRINGS************************)
(****************************************************)

let _return       = pack (word "\\r")  (fun _ -> char_of_int 13);;
let _newline      = pack (word "\\n")  (fun _ -> char_of_int 10);;
let _tab          = pack (word "\\t")  (fun _ -> char_of_int 9);;
let _page         = pack (word "\\f")  (fun _ -> char_of_int 12);;
let _dq           = pack (word "\\\"") (fun _ -> char_of_int 34);;
let _backslash    = pack (word "\\\\") (fun _ -> char_of_int 92);;

let nt_backslash     = char '\\' ;;
let nt_doubleQuote   = char '"';;


let str_meta = disj_list[_return    ; _newline ;
                         _tab       ; _page    ;
                         _backslash ; _dq      ];;

                         
let string_literal_char = diff nt_any (disj nt_doubleQuote nt_backslash);;
let nt_stringChar       = disj string_literal_char str_meta;;
let nt_stringChar_end   = (caten (star nt_stringChar) nt_doubleQuote);;
let nt_left             = caten nt_doubleQuote  nt_stringChar_end ;;

let nt_string = 
  pack nt_left 
          (fun (dq0,(str_lst,dq1)) ->  String(list_to_string str_lst)) ;;
          

(****************************************************)
(***********************CHARS************************)
(****************************************************)

let nt_charPrefix        = word "#\\" ;; 

let nt_char_nul          = pack (word_ci "nul")  (fun _ -> char_of_int 0);;
let nt_char_newline      = pack (word_ci "newline")  (fun _ -> char_of_int 10);;
let nt_char_return       = pack (word_ci "return") (fun _ -> char_of_int 13);;
let nt_char_tab          = pack (word_ci "tab")  (fun _ -> char_of_int 9);;
let nt_char_page         = pack (word_ci "page")  (fun _ -> char_of_int 12);;
let nt_char_space        = pack (word_ci "space") (fun _ -> char_of_int 32);;



let named_char = disj_list[ nt_char_nul      ; nt_char_newline     ;
                            nt_char_return   ; nt_char_tab         ;
                            nt_char_page     ; nt_char_space       ];;


let nt_visible_SimpleChar = guard nt_any (fun ch -> ch > char_of_int 32);;


let nt_char = pack 
              (caten nt_charPrefix (disj named_char nt_visible_SimpleChar))
              (fun (pre, ch) -> Char(ch));;




(****************************************************)
(**********************COMMENTS**********************)
(****************************************************)
let rec create_nested_list = fun (_list) ->
match _list with 
| [] -> Nil
| head::tail -> Pair(head, (create_nested_list tail)) ;;

let rec create_nested_dotted_list = fun (_list) ->
match _list with 
| [] -> Nil
| head::tail -> Pair(head, (create_nested_list tail)) ;;


let nt_whiteSpace = range (char_of_int 0) ' ';;
let nt_semicolon = char ';';;
let nt_end_of_line = char (char_of_int 10);;
let nt_read_comment = diff nt_any nt_end_of_line;;
let nt_comment_end  = disj nt_end_of_line (pack nt_end_of_input
  (fun (any) -> 'b'));;

let nt_line_comment = pack (caten nt_semicolon (caten (star nt_read_comment) nt_comment_end))
                        (fun (semicolon,(lst,dunno)) -> 'b');;

                      
let rec nt_sexp sexprs = 
    let sexps = spaceOrComment (disj_list [
            nt_bool;
            nt_number_all;          
            nt_symbol;
            nt_string;
            nt_char;
            nt_list;
            nt_dotted_list;
            nt_quoted;
            nt_qQuoted;
            nt_unQuoted;
            nt_unQuoted_splicing] )
            in sexps sexprs                

and nt_sexp_comments s = pack (caten (word "#;") nt_sexp)
                            (fun (any) -> 'b' ) 


                            


and nt_spaces_comments exp = star (disj_list [ nt_whiteSpace;
nt_line_comment  ;nt_sexp_comments exp ]  )                         

and spaceOrComment nt exp= make_paired ( nt_spaces_comments exp) ( nt_spaces_comments exp) nt exp
                       

(****************************************************)
(***********************LISTS************************)
(****************************************************)
(*
and nt_lparen s= char '(' 
and nt_rparen s= char ')'
and nt_lst_body = caten (star nt_sexp) nt_rparen 
and nt_lst_remove_spaces = 
*)

and nt_list lst = 
  let nt_lparen = char '(' in 
  let nt_rparen = char ')' in
  let nt_lst_body = caten (star nt_sexp) nt_rparen in
  let nt = caten (nt_spaces_comments lst) nt_lst_body in
  let nt = caten nt_lparen nt in 
  let nt = pack nt 
  (fun (lpar,(toSkip,(e, rpar))) -> create_nested_list  e) in 
  nt lst 

 
 (*and nt_dotted_list lst= 
  let nt_lparen = char '(' in 
  let nt_rparen = char ')' in
  let nt_rhs_lst = caten nt_sexp  nt_rparen in
  let nt = caten (char '.') nt_rhs_lst in
  let nt = caten nt_lparen (plus nt_sexp) in
  let nt = caten nt nt_rhs_lst in
  let nt = pack nt 
  (fun (e,r) -> match  List.fold_right (fun sexpr1 sexpr2 -> Pair(sexpr1, sexpr2)) s1 b
  )in nt lst
  fun (lpar , (s0, (dotte, s1),_))
  *)

  and nt_dotted_list lst= 
  let nt_dotted =  char '.' in
  let nt_lparen = char '(' in 
  let nt_rparen = char ')' in
  let nt_rhs_lst = caten nt_dotted nt_sexp  in
  let nt = caten (plus nt_sexp) nt_rhs_lst in
  let nt = caten nt_lparen (caten nt nt_rparen) in
  let nt = pack nt (
      fun (lpar, ((s0, (dotte, s1)) ,rpar)) -> List.fold_right (fun car cdr -> Pair(car,cdr)) s0 s1
  )in nt lst
(****************************************************)
(**********************QUOTES************************)
(****************************************************)
and nt_quoted exp = 
  let nt_quote = char (char_of_int 39) in 
  let nt = caten nt_quote nt_sexp in 
  let nt = pack nt
  (fun (q,s) -> Pair(Symbol ("quote"), Pair (s,Nil))) in 
  nt exp


and nt_qQuoted exp = 
  let nt_qq = char (char_of_int 96) in 
  let nt = caten nt_qq nt_sexp in 
  let nt = pack nt
  (fun (q,s) -> Pair(Symbol ("quasiquote"), Pair (s,Nil))) in 
  nt exp



and nt_unQuoted exp = 
  let nt_uq = char (char_of_int 44) in 
  let nt = caten nt_uq nt_sexp in 
  let nt = pack nt
  (fun (q,s) -> Pair(Symbol ("unquote"), Pair (s,Nil))) in 
  nt exp



and nt_unQuoted_splicing exp = 
  let nt_uq_s = word ",@" in 
  let nt = caten nt_uq_s nt_sexp in 
  let nt = pack nt
  (fun (q,s) -> Pair(Symbol ("unquote-splicing"), Pair (s,Nil))) in 
  nt exp;;




let read_sexprs str1 = 
  let (e,r) = (star nt_sexp) (string_to_list(str1)) in
  e;;

end;; (* struct Reader *)
open Reader;;
