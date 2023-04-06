#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen of string;;

let rec is_member a = function
  | [] -> false
  | a' :: s -> (a = a') || (is_member a s);;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
  val nt_sexpr : sexpr PC.parser
  (* val print_sexpr : out_channel -> sexpr -> unit
  val print_sexprs : out_channel -> sexpr list -> unit
  val sprint_sexpr : 'a -> sexpr -> string
  val sprint_sexprs : 'a -> sexpr list -> string
  val scheme_sexpr_list_of_sexpr_list : sexpr list -> sexpr *)
end;; (* end of READER signature *)

module Reader : READER = struct
  open PC;;

  type string_part =
    | Static of string
    | Dynamic of sexpr;;

  let unitify nt = pack nt (fun _ -> ());;

  let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str =
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input in
    let nt1 = disj nt1 nt2 in
    nt1 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str =
    let nt1 = caten (char '{') (star nt_whitespace) in
    let nt1 = caten nt1 (star nt_sexpr) in
    let nt1 = caten nt1 (star nt_whitespace) in
    let nt1 = caten nt1 (star nt_symbol_char) in
    let nt1 = caten nt1 (star nt_whitespace) in
    let nt1 = caten nt1 (char '}') in
    let nt1 = pack nt1 (fun _ -> ()) in
    nt1 str
  and nt_sexpr_comment str =
    let nt1 = caten (word "#;") nt_sexpr in
    let nt1 = pack nt1 (fun _ -> ()) in
    nt1 str
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str
  and nt_void str =
    let nt1 = word_ci "#void" in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    let nt1 = pack nt1 (fun _ -> ScmVoid) in
    nt1 str
  and nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str
  and make_skipped_star (nt : 'a parser) =
    let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
    nt1
  and nt_digit str =
    let nt1 = range '0' '9' in
    let nt1 = pack nt1 (let delta = int_of_char '0' in
                        fun digit -> int_of_char digit - delta)in
    nt1 str
  and nt_hex_digit str =
    let nt1 = range 'a' 'f' in
    let nt1 = pack nt1 (let delta = int_of_char 'a' - 10 in
                        fun hex_digit -> int_of_char hex_digit - delta) in
    let nt2 = range 'A' 'F' in
    let nt2 = pack nt2 (let delta = int_of_char 'A' - 10 in
                        fun hex_digit -> int_of_char hex_digit - delta) in
    let nt3 = range '0' '9' in
    let nt3 = pack nt3 (let delta = int_of_char '0' in
                        fun digit -> int_of_char digit - delta)in
    let nt1 = disj nt1 nt2 in
    let nt1 = disj nt1 nt3 in
    nt1 str
  and nt_nat str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1 (fun digits ->
                  List.fold_left
                    (fun number digit -> 10 * number + digit)
                    0
                    digits) in
    nt1 str
  and nt_hex_nat str = 
    let nt1 = plus nt_hex_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit ->
                      16 * num + digit)
                    0
                    digits) in
    nt1 str
  and nt_optional_sign str =
    let nt1 = pack (char '+') (fun _ -> true) in
    let nt2 = pack (char '-') (fun _ -> false) in
    let nt1 = disj nt1 nt2 in
    let nt1 = maybe nt1 in
    let nt1 = pack nt1 (function
                  |None -> true
                  |Some sign -> sign) in
    nt1 str
  and nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str
  and nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd (abs num) (abs den) in
                  ScmRational(num / d, den / d)) in
    nt1 str
  and nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str
  and nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str
  and make_maybe nt none_value =
    pack (maybe nt)
      (function
       | None -> none_value
       | Some(x) -> x)
  and nt_float str =
    (* float c *)
    let integer_exponent = caten nt_integer_part nt_exponent  in
    let floatc = pack integer_exponent( fun(x,y)-> if (y = 0.) then x else x*.y) in
    (* float b *)
    let floatb = caten (char '.') nt_mantissa in
    let floatb = pack floatb (fun(_,x) -> x) in
    let floatb = caten floatb (make_maybe nt_exponent 0.) in
    let floatb = pack floatb (fun (m, t)-> if ( t = 0.) then  m else m*.t) in

    (* float a *)
    let nt1 = caten nt_integer_part (char '.') in
    let nt1 = pack nt1 (fun (x, _) -> x) in
    let nt2 = caten nt1 (make_maybe nt_mantissa 0.) in
    let nt2Pack = pack nt2 (fun (x,m)-> if ( m = 0.) then x else x+.m ) in
    let nt3  = caten nt2Pack (make_maybe nt_exponent 0.) in
    let floata = pack nt3 (fun (x,t)-> if ( t = 0.) then x else x*.t) in
    let nt1 = caten nt_optional_sign (disj_list [floatc;floatb;floata]) in
    let nt1 = pack nt1 (fun (isPos, n) -> if isPos then ScmReal(n) else ScmReal(-1.0 *. n)) in
    nt1 str
  and nt_number str =
    let nt1 = nt_float in
    let nt2 = nt_frac in
    let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
    let nt1 = disj nt1 (disj nt2 nt3) in
    let nt1 = pack nt1 (fun r -> ScmNumber r) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str
  and nt_boolean str =
    let nt1 = char '#' in
    let nt2 = char_ci 'f' in
    let nt2 = pack nt2 (fun _ -> ScmBoolean false) in
    let nt3 = char_ci 't' in
    let nt3 = pack nt3 (fun _ -> ScmBoolean true) in
    let nt2 = disj nt2 nt3 in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_, value) -> value) in
    let nt2 = nt_symbol_char in
    let nt1 = not_followed_by nt1 nt2 in
    nt1 str
  and nt_char_simple str =
    let nt1 = const(fun ch -> ' ' < ch) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str
  and nt_char_named str =
    let nt1 =
      disj_list [pack (word_ci "newline") (fun _ -> '\n');
                 pack (word_ci "null") (fun _ -> '\000');
                 pack (word_ci "nul") (fun _ -> '\000');
                 pack (word_ci "page") (fun _ -> '\012');
                 pack (word_ci "return") (fun _ -> '\r');
                 pack (word_ci "space") (fun _ -> ' ');
                 pack (word_ci "tab") (fun _ -> '\t')] in
    nt1 str
  and nt_char_hex str =
    let nt1 = caten (char_ci 'x') nt_hex_nat in
    let nt1 = pack nt1 (fun (_, n) -> n) in
    let nt1 = only_if nt1 (fun n -> n < 256) in
    let nt1 = pack nt1 (fun n -> char_of_int n) in
    nt1 str
  and nt_char str =
    let nt1 = word "#\\" in
    let nt2 = disj nt_char_simple (disj nt_char_named nt_char_hex) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_, ch) -> ScmChar ch) in
    nt1 str
  and nt_symbol_char str =
    let nt1 = range_ci 'a' 'z' in
    let nt1 = pack nt1 Char.lowercase_ascii in
    let nt2 = range '0' '9' in
    let nt3 = one_of "!$^*_-+=<>?/" in
    let nt1 = disj nt1 (disj nt2 nt3) in
    nt1 str
  and nt_symbol str =
    let nt1  = plus nt_symbol_char in
    let nt2  = pack nt1 (fun (x) -> ScmSymbol(string_of_list x)) in
    nt2 str
  and nt_string_part_simple str =
    let nt1 =
      disj_list [unitify (char '"'); unitify (char '\\'); unitify (word "~~");
                 unitify nt_string_part_dynamic] in
    let nt1 = diff nt_any nt1 in
    nt1 str
  and nt_string_part_meta str =
    let nt1 =
      disj_list [pack (word "\\\\") (fun _ -> '\\');
                 pack (word "\\\"") (fun _ -> '"');
                 pack (word "\\n") (fun _ -> '\n');
                 pack (word "\\r") (fun _ -> '\r');
                 pack (word "\\f") (fun _ -> '\012');
                 pack (word "\\t") (fun _ -> '\t');
                 pack (word "~~") (fun _ -> '~')] in
    nt1 str
  and nt_string_part_hex str =
    let nt1 = word_ci "\\x" in
    let nt2 = nt_hex_nat in
    let nt2 = only_if nt2 (fun n -> n < 256) in
    let nt3 = char ';' in
    let nt1 = caten nt1 (caten nt2 nt3) in
    let nt1 = pack nt1 (fun (_, (n, _)) -> n) in
    let nt1 = pack nt1 char_of_int in
    nt1 str
  and nt_string_part_dynamic str =
    let nt1 = word_ci "~{" in
    let nt2 = nt_sexpr in
    let nt3 = caten nt1 nt2 in
    let nt4  = word_ci "}" in
    let nt5 = caten nt3 nt4 in
    let nt5Pack = pack nt5 (fun ((_,sexp),_) -> ScmPair( ScmSymbol "format", ScmPair(ScmString "~a", ScmPair(sexp, ScmNil)))) in
    let nt6 = pack nt5Pack (fun sexp -> Dynamic sexp) in
    nt6 str
  and nt_string_part_static str =
    let nt1 = disj_list [nt_string_part_simple;
                         nt_string_part_meta;
                         nt_string_part_hex] in
    let nt1 = plus nt1 in
    let nt1 = pack nt1 string_of_list in
    let nt1 = pack nt1 (fun str -> Static str) in
    nt1 str
  and nt_string_part str =
    disj nt_string_part_static nt_string_part_dynamic str
  and nt_string str =
    let nt1 = char '"' in
    let nt2 = star nt_string_part in
    let nt3 = char '"' in
    let nt1 = caten nt1 (caten nt2 nt3) in
    let nt1 = pack nt1 (fun (_, (parts, _)) -> parts) in
    let nt1 = pack nt1
                (fun parts ->
                  match parts with
                  | [] -> ScmString ""
                  | [Static(str)] -> ScmString str
                  | [Dynamic(sexpr)] -> sexpr
                  | parts ->
                     let argl =
                       List.fold_right
                         (fun car cdr ->
                           ScmPair((match car with
                                    | Static(str) -> ScmString(str)
                                    | Dynamic(sexpr) -> sexpr),
                                   cdr))
                         parts
                         ScmNil in
                     ScmPair(ScmSymbol "string-append", argl)) in
    nt1 str
  and nt_vector str =
    let nt1  = word "#(" in
    let nt4 = star nt_whitespace in
    let nt2  = star nt_sexpr in
    let nt3  = char ')' in
    let nt1  = caten nt1 ( caten nt4 (caten (caten nt2 nt4) nt3)) in
    let nt1Pack  = pack nt1 (fun (_, (_,((x, _), _))) -> ScmVector(x)) in
    nt1Pack str
  and nt_list str =
    let nt1 = (char '(') in
    let nt6 = caten (star nt_whitespace) (star nt_comment) in
    let nt6 = caten nt6 (star nt_whitespace) in
    let nt2 = pack (caten nt6 (caten (char ')') nt6)) (fun _ -> ScmNil) in
    let nt2' = plus nt_sexpr in
    let nt3 = pack (char ')') (fun _ -> ScmNil) in
    let nt4 = char '.' in
    let nt5 = caten nt_sexpr (char ')') in
    let nt5 = pack nt5 (fun (sexpr,_) -> sexpr) in
    let nt4 = pack (caten nt4 nt5) (fun (_,sexpr) -> sexpr) in
    let nt3 = disj nt3 nt4 in
    let nt2' = pack (caten nt2' nt3) (fun (sexprs, sexpr) ->
                   List.fold_right
                     (fun car cdr -> ScmPair (car, cdr))
                     sexprs
                     sexpr) in
    let nt2 = disj nt2 nt2' in
    let nt1 = pack (caten nt1 nt2) (fun (_, sexpr) -> sexpr) in
    nt1 str
  and make_quoted_form nt_qf qf_name =
    let nt1 = caten nt_qf nt_sexpr in
    let nt1 = pack nt1
                (fun (_, sexpr) ->
                  ScmPair(ScmSymbol qf_name,
                          ScmPair(sexpr, ScmNil))) in
    nt1
  and nt_quoted_forms str =
    let nt1 =
      disj_list [(make_quoted_form (unitify (char '\'')) "quote");
                 (make_quoted_form (unitify (char '`')) "quasiquote");
                 (make_quoted_form
                    (unitify (not_followed_by (char ',') (char '@')))
                    "unquote");
                 (make_quoted_form (unitify (word ",@")) "unquote-splicing")] in
    nt1 str
  and nt_sexpr str = 
    let nt1 =
      disj_list [nt_void; nt_number; nt_boolean; nt_char; nt_symbol;
                 nt_string; nt_vector; nt_list; nt_quoted_forms] in
    let nt1 = make_skipped_star nt1 in
    nt1 str;;

  
end;; (* end of struct Reader *)
let rec string_of_sexpr = function
    | ScmVoid -> "#<void>"
    | ScmNil -> "()"
    | ScmBoolean(false) -> "#f"
    | ScmBoolean(true) -> "#t"
    | ScmChar('\n') -> "#\\newline"
    | ScmChar('\r') -> "#\\return"
    | ScmChar('\012') -> "#\\page"
    | ScmChar('\t') -> "#\\tab"
    | ScmChar(' ') -> "#\\space"
    | ScmChar(ch) ->
       if (ch < ' ')
       then let n = int_of_char ch in
            Printf.sprintf "#\\x%x" n
       else Printf.sprintf "#\\%c" ch
    | ScmString(str) ->
       Printf.sprintf "\"%s\""
         (String.concat ""
            (List.map
               (function
                | '\n' -> "\\n"
                | '\012' -> "\\f"
                | '\r' -> "\\r"
                | '\t' -> "\\t"
                | '\"' -> "\\\""
                | ch ->
                   if (ch < ' ')
                   then Printf.sprintf "\\x%x;" (int_of_char ch)
                   else Printf.sprintf "%c" ch)
               (list_of_string str)))
    | ScmSymbol(sym) -> sym
    | ScmNumber(ScmRational(0, _)) -> "0"
    | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
    | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
    | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
    | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
    | ScmVector(sexprs) ->
       let strings = List.map string_of_sexpr sexprs in
       let inner_string = String.concat " " strings in
       Printf.sprintf "#(%s)" inner_string
    | ScmPair(ScmSymbol "quote",
              ScmPair(sexpr, ScmNil)) ->
       Printf.sprintf "'%s" (string_of_sexpr sexpr)
    | ScmPair(ScmSymbol "quasiquote",
              ScmPair(sexpr, ScmNil)) ->
       Printf.sprintf "`%s" (string_of_sexpr sexpr)
    | ScmPair(ScmSymbol "unquote",
              ScmPair(sexpr, ScmNil)) ->
       Printf.sprintf ",%s" (string_of_sexpr sexpr)
    | ScmPair(ScmSymbol "unquote-splicing",
              ScmPair(sexpr, ScmNil)) ->
       Printf.sprintf ",@%s" (string_of_sexpr sexpr)
    | ScmPair(car, cdr) ->
       string_of_sexpr' (string_of_sexpr car) cdr
  and string_of_sexpr' car_string = function
    | ScmNil -> Printf.sprintf "(%s)" car_string
    | ScmPair(cadr, cddr) ->
       let new_car_string =
         Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
       string_of_sexpr' new_car_string cddr
    | cdr ->
       let cdr_string = (string_of_sexpr cdr) in
       Printf.sprintf "(%s . %s)" car_string cdr_string;;

  let print_sexpr chan sexpr = output_string chan (string_of_sexpr sexpr);;

  let print_sexprs chan sexprs =
    output_string chan
      (Printf.sprintf "[%s]"
         (String.concat "; "
            (List.map string_of_sexpr sexprs)));;

  let sprint_sexpr _ sexpr = string_of_sexpr sexpr;;

  let sprint_sexprs chan sexprs =
    Printf.sprintf "[%s]"
      (String.concat "; "
         (List.map string_of_sexpr sexprs));;

  let scheme_sexpr_list_of_sexpr_list sexprs =
    List.fold_right (fun car cdr -> ScmPair (car, cdr)) sexprs ScmNil;;

(* //////////////////////////////////tag parser //////////////////////////////////////////*)
exception X_not_yet_implemented;;
exception X_this_should_not_happen of string;;

let rec is_member a = function
  | [] -> false
  | a' :: s -> (a = a') || (is_member a s);;

(* the tag-parser *)

exception X_syntax of string;;

type var = 
  | Var of string;;

type lambda_kind =
  | Simple
  | Opt of string;;

type expr =
  | ScmConst of sexpr
  | ScmVarGet of var
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmOr of expr list
  | ScmVarSet of var * expr
  | ScmVarDef of var * expr
  | ScmLambda of string list * lambda_kind * expr
  | ScmApplic of expr * expr list;;

module type TAG_PARSER = sig
  val tag_parse : sexpr -> expr
  (* val print_expr : out_channel -> expr -> unit
  val print_exprs : out_channel -> expr list -> unit
  val sprint_expr : 'a -> expr -> string
  val sprint_exprs : 'a -> expr list -> string     *)
end;;

module Tag_Parser : TAG_PARSER = struct
  open Reader;;
  
  let reserved_word_list =
    ["and"; "begin"; "cond"; "do"; "else"; "if"; "lambda";
     "let"; "let*"; "letrec"; "or"; "quasiquote"; "quote";
     "unquote"; "unquote-splicing"];;

  let rec scheme_list_to_ocaml = function
    | ScmNil -> ([], ScmNil)
    | ScmPair(car, cdr) ->
       ((fun (rdc, last) -> (car :: rdc, last))
          (scheme_list_to_ocaml cdr))  
    | rac -> ([], rac);;

  let is_reserved_word name = is_member name reserved_word_list;;

  let unsymbolify_var = function
    | ScmSymbol var -> var
    | _ -> raise (X_syntax "not a symbol");;

  let unsymbolify_vars = List.map unsymbolify_var;;

  let list_contains_unquote_splicing =
    ormap (function
        | ScmPair (ScmSymbol "unquote-splicing",
                   ScmPair (_, ScmNil)) -> true
        | _ -> false);;

  let rec macro_expand_qq = function
    | ScmNil -> ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil))
    | (ScmSymbol _) as sexpr ->
       ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
    | ScmPair (ScmSymbol "unquote", ScmPair (sexpr, ScmNil)) -> sexpr
    | ScmPair (ScmPair (ScmSymbol "unquote",
                        ScmPair (car, ScmNil)),
               cdr) ->
       let cdr = macro_expand_qq cdr in
       ScmPair (ScmSymbol "cons", ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (sexpr, ScmNil)),
               ScmNil) ->
       sexpr
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (car, ScmNil)), cdr) ->
       let cdr = macro_expand_qq cdr in
       ScmPair (ScmSymbol "append",
                ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmPair (car, cdr) ->
       let car = macro_expand_qq car in
       let cdr = macro_expand_qq cdr in
       ScmPair
         (ScmSymbol "cons",
          ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmVector sexprs ->
       if (list_contains_unquote_splicing sexprs)
       then let sexpr = macro_expand_qq
                          (scheme_sexpr_list_of_sexpr_list sexprs) in
            ScmPair (ScmSymbol "list->vector",
                     ScmPair (sexpr, ScmNil))
       else let sexprs = 
              (scheme_sexpr_list_of_sexpr_list
                 (List.map macro_expand_qq sexprs)) in
            ScmPair (ScmSymbol "vector", sexprs)
    | sexpr -> sexpr;;

  let rec macro_expand_cond_ribs ribs =
    match ribs with
    | ScmNil -> ScmVoid
    | ScmPair (ScmPair (ScmSymbol "else", exprs), ribs) ->
         ScmPair
              (ScmSymbol "begin", exprs)
    | ScmPair (ScmPair (expr,
                        ScmPair (ScmSymbol "=>",
                                 ScmPair (func, ScmNil))),
               ribs) ->
       let remaining = macro_expand_cond_ribs ribs in
       ScmPair
         (ScmSymbol "let",
          ScmPair
            (ScmPair
               (ScmPair (ScmSymbol "value", ScmPair (expr, ScmNil)),
                ScmPair
                  (ScmPair
                     (ScmSymbol "f",
                      ScmPair
                        (ScmPair
                           (ScmSymbol "lambda",
                            ScmPair (ScmNil, ScmPair (func, ScmNil))),
                         ScmNil)),
                   ScmPair
                     (ScmPair
                        (ScmSymbol "rest",
                         ScmPair
                           (ScmPair
                              (ScmSymbol "lambda",
                               ScmPair (ScmNil, ScmPair (remaining, ScmNil))),
                            ScmNil)),
                      ScmNil))),
             ScmPair
               (ScmPair
                  (ScmSymbol "if",
                   ScmPair
                     (ScmSymbol "value",
                      ScmPair
                        (ScmPair
                           (ScmPair (ScmSymbol "f", ScmNil),
                            ScmPair (ScmSymbol "value", ScmNil)),
                         ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
                ScmNil)))
    | ScmPair (ScmPair (pred, exprs), ribs) ->
       let remaining = macro_expand_cond_ribs ribs in
       ScmPair (ScmSymbol "if",
                ScmPair (pred,
                         ScmPair
                           (ScmPair (ScmSymbol "begin", exprs),
                            ScmPair (remaining, ScmNil))))
    | _ -> raise (X_syntax "malformed cond-rib");;

    (*(a x) (y c)-> (a y) (x c)*)
  let rec names_values = function
    | ScmNil -> ([], [])
    | ScmPair (ScmPair (name, ScmPair (value, ScmNil)), ribs) ->
       let (names, values) = names_values ribs in
       (name :: names, value :: values)
    | _ -> raise (X_syntax "Invalid let-rib structure");;

  (* ((x e1) (y e2) ...)-> ((x 'whatever) (y 'whatever)...)*)
  let rec makeWhatEverRibs = function
    | ScmNil -> ScmNil
    | ScmPair (ScmPair (name, ScmPair (value, ScmNil)), ribs) ->
       ScmPair
         (ScmPair (name, ScmPair (ScmSymbol "'whatever", ScmNil)),
          makeWhatEverRibs ribs)
    | _ -> raise (X_syntax "Invalid rib structure");;

 (* (f1 f2 ...) ( ex1 ex2 ...) -> (set! f1 ex1) (set! f2 ex2)...*)
  let rec set_values names values =
    match (names, values) with
    | ([], []) -> ScmNil
    | (name :: names, value :: values) ->
       ScmPair
         (ScmPair
            (ScmSymbol "set!",
             ScmPair (name, ScmPair (value, ScmNil))),
          set_values names values)
    | _ -> raise (X_syntax "Invalid let-rib structure");;
(*
   ((a b) , c)-> (a b c)
*) 
  let rec append list1 list2 = 
    match list1 with
    | ScmNil -> list2
    | ScmPair (car, cdr) -> ScmPair (car, append cdr list2)
    | _ -> raise (X_syntax "Invalid pair-rib structure");;

  let rec setbang_exprs exprs = function
    |ScmNil-> exprs
    |ScmPair (rib, ribs) -> ScmPair(ScmPair(ScmSymbol("set!"), rib), (setbang_exprs exprs ribs))
    |ScmPair(rib, ScmNil) -> ScmPair(ScmPair(ScmSymbol("set!"), rib), exprs)
    | _ -> raise (X_syntax "malformed setbang_ribs");;

(* (a b)-> a*)
 let rec car = function
   | ScmPair (a, _) -> a
   | _ -> raise (X_syntax "Invalid pair-rib structure");;
let rec cdr = function
   | ScmPair (_, b) -> b
   | _ -> raise (X_syntax "Invalid pair-rib structure");;
  let rec tag_parse sexpr =
    match sexpr with
    | ScmPair (ScmSymbol "or", ScmNil) -> (tag_parse (ScmBoolean false))
    | ScmPair (ScmSymbol "or", ScmPair(expr, ScmNil)) -> (tag_parse expr)
    | ScmPair (ScmSymbol "or", exprs) ->
      (match (scheme_list_to_ocaml exprs) with
      | exprs, ScmNil -> ScmOr(List.map tag_parse exprs)
      | _ -> raise (X_syntax "malforamed or"))
    | ScmVoid | ScmBoolean _ | ScmChar _ | ScmString _ | ScmNumber _ ->
       ScmConst sexpr
    | ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil)) ->
       ScmConst(sexpr)
    | ScmPair (ScmSymbol "quasiquote", ScmPair (sexpr, ScmNil)) ->
       tag_parse (macro_expand_qq sexpr)
    | ScmSymbol var ->
       if (is_reserved_word var)
       then raise (X_syntax "Variable cannot be a reserved word")
       else ScmVarGet(Var var)
    | ScmPair (ScmSymbol "if",
               ScmPair (test, ScmPair (dit, ScmNil))) ->
       ScmIf(tag_parse test,
             tag_parse dit,
             tag_parse ScmVoid)
    | ScmPair (ScmSymbol "if",
               ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil)))) ->
       ScmIf(tag_parse test,
             tag_parse dit,
             tag_parse dif)
    | ScmPair (ScmSymbol "begin", ScmNil) -> ScmConst(ScmVoid)
    | ScmPair (ScmSymbol "begin", ScmPair (sexpr, ScmNil)) ->
       tag_parse sexpr
    | ScmPair (ScmSymbol "begin", sexprs) ->
       (match (scheme_list_to_ocaml sexprs) with
        | (sexprs', ScmNil) -> ScmSeq(List.map tag_parse sexprs')
        | _ -> raise (X_syntax "Improper sequence"))
    | ScmPair (ScmSymbol "set!",
               ScmPair (ScmSymbol var,
                        ScmPair (expr, ScmNil))) ->
       if (is_reserved_word var)
       then raise (X_syntax "cannot assign a reserved word")
       else ScmVarSet(Var var, tag_parse expr)
    | ScmPair (ScmSymbol "define", ScmPair (ScmPair (var, params), exprs)) ->
       tag_parse
         (ScmPair (ScmSymbol "define",
                   ScmPair (var,
                            ScmPair (ScmPair (ScmSymbol "lambda",
                                              ScmPair (params, exprs)),
                                     ScmNil))))
    | ScmPair (ScmSymbol "define",
               ScmPair (ScmSymbol var,
                        ScmPair (expr, ScmNil))) ->
       if (is_reserved_word var)
       then raise (X_syntax "cannot define a reserved word")
       else ScmVarDef(Var var, tag_parse expr)
    | ScmPair (ScmSymbol "lambda", ScmPair (params, exprs)) ->
       let expr = tag_parse (ScmPair(ScmSymbol "begin", exprs)) in
       (match (scheme_list_to_ocaml params) with
        | params, ScmNil -> ScmLambda(unsymbolify_vars params, Simple, expr)
        | params, ScmSymbol opt ->
           ScmLambda(unsymbolify_vars params, Opt opt, expr)
        | _ -> raise (X_syntax "invalid parameter list"))
    | ScmPair (ScmSymbol "let", ScmPair (ribs, exprs)) ->
       let (names, values) = names_values ribs in
       let names = scheme_sexpr_list_of_sexpr_list names
       and values = scheme_sexpr_list_of_sexpr_list values in
       tag_parse (ScmPair
                    (ScmPair
                       (ScmSymbol "lambda", ScmPair (names, exprs)),
                     values))
    | ScmPair (ScmSymbol "let*", ScmPair (ScmNil, exprs)) ->
        tag_parse (ScmPair (ScmSymbol "let", ScmPair (ScmNil, exprs)))
    | ScmPair (ScmSymbol "let*",
               ScmPair
                 (ScmPair
                    (ScmPair (var, ScmPair (value, ScmNil)), ScmNil),
                  exprs)) -> tag_parse (ScmPair
                                          (ScmSymbol "let",
                                           ScmPair
                                             (ScmPair
                                                (ScmPair (var,
                                                          ScmPair (value,
                                                                   ScmNil)),
                                                 ScmNil),
                                              exprs)))
    | ScmPair (ScmSymbol "let*",
               ScmPair (ScmPair (ScmPair (var,
                                          ScmPair (arg, ScmNil)),
                                 ribs),
                        exprs)) -> tag_parse (ScmPair
                                                (ScmSymbol "let",
                                                 ScmPair
                                                   (ScmPair
                                                      (ScmPair (var,
                                                                ScmPair (arg,
                                                                         ScmNil)),
                                                       ScmNil),
                                                    ScmPair
                                                      (ScmPair
                                                         (ScmSymbol "let*",
                                                          ScmPair (ribs,
                                                                   exprs)),
                                                       ScmNil))))
    | ScmPair (ScmSymbol "letrec", ScmPair (ribs, exprs)) ->
      let rib = makeWhatEverRibs ribs in
        tag_parse (ScmPair(ScmSymbol "let", ScmPair(rib, setbang_exprs exprs ribs)))
    | ScmPair (ScmSymbol "and", ScmNil) -> tag_parse (ScmBoolean true)
    | ScmPair (ScmSymbol "and", ScmPair (expr, ScmNil)) -> tag_parse expr
    | ScmPair (ScmSymbol "and", ScmPair (expr1, exprs)) ->
       let dit = ScmPair (ScmSymbol "and", exprs) in
       tag_parse (ScmPair
                    (ScmSymbol "if",
                     ScmPair (expr1,
                              ScmPair (dit,
                                       ScmPair (ScmBoolean false, ScmNil)))))
    | ScmPair (ScmSymbol "cond", ribs) ->
       tag_parse (macro_expand_cond_ribs ribs)
    | ScmPair (proc, args) ->
       let proc =
         (match proc with
          | ScmSymbol var ->
             if (is_reserved_word var)
             then raise (X_syntax "reserved word in proc position")
             else proc
          | proc -> proc) in
       (match (scheme_list_to_ocaml args) with
        | args, ScmNil ->
           ScmApplic (tag_parse proc, List.map tag_parse args)
        | _ -> raise (X_syntax "malformed application"))
    | sexpr -> raise (X_syntax
                       (Printf.sprintf
                          "Unknown form: \n%a\n"
                          sprint_sexpr sexpr));;

  

end;; (* end of struct Tag_Parser *)
let rec sexpr_of_expr = function
    | ScmConst(ScmVoid) -> ScmVoid
    | ScmConst((ScmBoolean _) as sexpr) -> sexpr
    | ScmConst((ScmChar _) as sexpr) -> sexpr
    | ScmConst((ScmString _) as sexpr) -> sexpr
    | ScmConst((ScmNumber _) as sexpr) -> sexpr
    | ScmConst((ScmSymbol _) as sexpr)
      | ScmConst(ScmNil as sexpr)
      | ScmConst(ScmPair _ as sexpr)
      | ScmConst((ScmVector _) as sexpr) ->
       ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
    | ScmVarGet(Var var) -> ScmSymbol var
    | ScmIf(test, dit, ScmConst ScmVoid) ->
       let test = sexpr_of_expr test in
       let dit = sexpr_of_expr dit in
       ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
    | ScmIf(e1, e2, ScmConst (ScmBoolean false)) ->
       let e1 = sexpr_of_expr e1 in
       (match (sexpr_of_expr e2) with
        | ScmPair (ScmSymbol "and", exprs) ->
           ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
        | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
    | ScmIf(test, dit, dif) ->
       let test = sexpr_of_expr test in
       let dit = sexpr_of_expr dit in
       let dif = sexpr_of_expr dif in
       ScmPair
         (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
    | ScmOr([]) -> ScmBoolean false
    | ScmOr([expr]) -> sexpr_of_expr expr
    | ScmOr(exprs) ->
      ScmPair (ScmSymbol "or",
              scheme_sexpr_list_of_sexpr_list
                (List.map sexpr_of_expr exprs))
    | ScmSeq([]) -> ScmVoid
    | ScmSeq([expr]) -> sexpr_of_expr expr
    | ScmSeq(exprs) ->
       ScmPair(ScmSymbol "begin",
               scheme_sexpr_list_of_sexpr_list
                 (List.map sexpr_of_expr exprs))
    | ScmVarSet(Var var, expr) ->
       let var = ScmSymbol var in
       let expr = sexpr_of_expr expr in
       ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
    | ScmVarDef(Var var, expr) ->
       let var = ScmSymbol var in
       let expr = sexpr_of_expr expr in
       ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
    | ScmLambda(params, Simple, expr) ->
       let params = scheme_sexpr_list_of_sexpr_list
                      (List.map (fun str -> ScmSymbol str) params) in
       let expr = sexpr_of_expr expr in
       ScmPair (ScmSymbol "lambda",
                ScmPair (params,
                         ScmPair (expr, ScmNil)))
    | ScmLambda([], Opt opt, expr) ->
       let expr = sexpr_of_expr expr in
       let opt = ScmSymbol opt in
       ScmPair
         (ScmSymbol "lambda",
          ScmPair (opt, ScmPair (expr, ScmNil)))
    | ScmLambda(params, Opt opt, expr) ->
       let expr = sexpr_of_expr expr in
       let opt = ScmSymbol opt in
       let params = List.fold_right
                      (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                      params
                      opt in
       ScmPair
         (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
    | ScmApplic (ScmLambda (params, Simple, expr), args) ->
       let ribs =
         scheme_sexpr_list_of_sexpr_list
           (List.map2
              (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
              params
              (List.map sexpr_of_expr args)) in
       let expr = sexpr_of_expr expr in
       ScmPair
         (ScmSymbol "let",
          ScmPair (ribs,
                   ScmPair (expr, ScmNil)))
    | ScmApplic (proc, args) ->
       let proc = sexpr_of_expr proc in
       let args =
         scheme_sexpr_list_of_sexpr_list
           (List.map sexpr_of_expr args) in
       ScmPair (proc, args)
    | _ -> raise (X_syntax "Unknown form");;

  let string_of_expr expr =
    Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr expr);;

  let print_expr chan expr =
    output_string chan
      (string_of_expr expr);;

  let print_exprs chan exprs =
    output_string chan
      (Printf.sprintf "[%s]"
         (String.concat "; "
            (List.map string_of_expr exprs)));;

  let sprint_expr _ expr = string_of_expr expr;;

  let sprint_exprs chan exprs =
    Printf.sprintf "[%s]"
      (String.concat "; "
         (List.map string_of_expr exprs));;
         
type app_kind = Tail_Call | Non_Tail_Call;;

type lexical_address =
  | Free
  | Param of int
  | Bound of int * int;;

type var' = Var' of string * lexical_address;;

type expr' =
  | ScmConst' of sexpr
  | ScmVarGet' of var'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmOr' of expr' list
  | ScmVarSet' of var' * expr'
  | ScmVarDef' of var' * expr'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmLambda' of string list * lambda_kind * expr'
  | ScmApplic' of expr' * expr' list * app_kind;;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_address : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val auto_box : expr' -> expr'
  val semantics : expr -> expr'
end;; (* end of signature SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env =
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> Var' (name, Free)
        | Some(major, minor) -> Var' (name, Bound (major, minor)))
    | Some minor -> Var' (name, Param minor);;

  (* run this first *)
  let annotate_lexical_address =
    let rec run expr params env =
      match expr with
      | ScmConst sexpr -> ScmConst' sexpr
      | ScmVarGet (Var str) -> ScmVarGet' (tag_lexical_address_for_var str params env)
      | ScmIf (test, dit, dif) -> ScmIf' (run test params env,
                                         run dit params env,
                                         run dif params env)
      | ScmSeq exprs -> ScmSeq' (List.map (fun expr -> run expr params env) exprs) (* we want to run ( compute) every expr in exprs*)
      | ScmOr exprs -> ScmOr' (List.map (fun expr -> run expr params env) exprs)
      | ScmVarSet(Var v, expr) -> ScmVarSet' (tag_lexical_address_for_var v params env,
                                             run expr params env)
      (* this code does not [yet?] support nested define-expressions *)
      | ScmVarDef(Var v, expr) -> ScmVarDef' (tag_lexical_address_for_var v params env,
                                             run expr params env)
      | ScmLambda (params', Simple, expr) -> ScmLambda' (params', Simple, run expr params' (params :: env))
      | ScmLambda (params', Opt opt, expr) -> ScmLambda' (params', Opt opt, run expr (params' @ [opt]) (params :: env))
      | ScmApplic (proc, args) ->
         ScmApplic' (run proc params env,
                     List.map (fun arg -> run arg params env) args,
                     Non_Tail_Call)
    in
    fun expr ->
    run expr [] [];;

  (* run this second *)
let annotate_tail_calls =
    let rec run in_tail = function
      | (ScmConst' _) as orig -> orig
      | (ScmVarGet' _) as orig -> orig
      | ScmIf' (test, dit, dif) -> ScmIf' (run false test,
                                          run in_tail dit,
                                          run in_tail dif)
      | ScmSeq' [] -> ScmSeq' []
      | ScmSeq' (expr :: exprs) -> ScmSeq' (runl in_tail expr exprs)
      | ScmOr' [] -> ScmOr' []
      | ScmOr' (expr :: exprs) -> ScmOr' (runl in_tail expr exprs)
      | ScmVarSet' (var', expr') -> ScmVarSet' (var', run false expr')
      | ScmVarDef' (var', expr') -> ScmVarDef' (var', run false expr')
      | (ScmBox' _) as expr' -> raise  (X_this_should_not_happen "no box before tail call")
      | (ScmBoxGet' _) as expr' -> raise   (X_this_should_not_happen "no box before tail call")
      | ScmBoxSet' (var', expr') ->  raise   (X_this_should_not_happen "no box before tail call")
      | ScmLambda' (params, Simple, expr) -> ScmLambda' (params, Simple, run true expr) (* when entering a new prame we computr with true*)
      | ScmLambda' (params, Opt opt, expr) -> ScmLambda' (params, Opt opt, run true expr)
      | ScmApplic' (proc, args, app_kind) ->
         if in_tail
         then ScmApplic' (run false proc,
                          List.map (fun arg -> run false arg) args,
                          Tail_Call)
         else ScmApplic' (run false proc,
                          List.map (fun arg -> run false arg) args,
                          Non_Tail_Call)
    and runl in_tail expr = function
      | [] -> [run in_tail expr]
      | expr' :: exprs -> (run false expr) :: (runl in_tail expr' exprs)
    in
    fun expr' -> run false expr';;

  (* auto_box *)

  let copy_list = List.map (fun si -> si);;

  let combine_pairs =
    List.fold_left
      (fun (rs1, ws1) (rs2, ws2) -> (rs1 @ rs2, ws1 @ ws2))
      ([], []);;

  let find_reads_and_writes =
    let rec run name expr params env =
      match expr with
      | ScmConst' _ -> ([], [])
      | ScmVarGet' (Var' (_, Free)) -> ([], [])
      | ScmVarGet' (Var' (name', _) as v) ->
         if name = name'
         then ([(v, env)], [])
         else ([], [])
      | ScmBox' _ -> ([], [])
      | ScmBoxGet' _ -> ([], [])
      | ScmBoxSet' (_, expr) -> run name expr params env
      | ScmIf' (test, dit, dif) ->
         let (rs1, ws1) = (run name test params env) in
         let (rs2, ws2) = (run name dit params env) in
         let (rs3, ws3) = (run name dif params env) in
         (rs1 @ rs2 @ rs3, ws1 @ ws2 @ ws3)
      | ScmSeq' exprs ->
         combine_pairs
           (List.map
              (fun expr -> run name expr params env)
              exprs)
      | ScmVarSet' (Var' (_, Free), expr) -> run name expr params env
      | ScmVarSet' ((Var' (name', _) as v), expr) ->
         let (rs1, ws1) =
           if name = name'
           then ([], [(v, env)])
           else ([], []) in
         let (rs2, ws2) = run name expr params env in
         (rs1 @ rs2, ws1 @ ws2)
      | ScmVarDef' (_, expr) -> run name expr params env
      | ScmOr' exprs ->
         combine_pairs
           (List.map
              (fun expr -> run name expr params env)
              exprs)
      | ScmLambda' (params', Simple, expr) ->
         if (List.mem name params')
         then ([], [])
         else run name expr params' ((copy_list params) :: env)
      | ScmLambda' (params', Opt opt, expr) ->
         let params' = params' @ [opt] in
         if (List.mem name params')
         then ([], [])
         else run name expr params' ((copy_list params) :: env)
      | ScmApplic' (proc, args, app_kind) ->
         let (rs1, ws1) = run name proc params env in
         let (rs2, ws2) =
           combine_pairs
             (List.map
                (fun arg -> run name arg params env)
                args) in
         (rs1 @ rs2, ws1 @ ws2)
    in
    fun name expr params ->
    run name expr params [];;

  let cross_product as' bs' =
    List.concat (List.map (fun ai ->
                     List.map (fun bj -> (ai, bj)) bs')
                   as');;

  (*functions for should_box*)
  let getFirst lst= match lst with
      |(e1, e2) -> e1;;

  let getSecond lst = match lst with
      |(e1, e2) -> e2;;

  let getValOfAdd = function
      |Free -> 1
      |Param(a) -> -1
      |Bound(a, b) -> a;;

  let rec find_rib name = function
    |[] -> []
    |rib::env ->
      if (List.mem name rib)
         then rib
              else find_rib name env;;

  let comp = (fun ((Var' (name1, add1), env1)) -> (fun (Var' (name2, add2), env2) ->
      if (((find_rib name1 env1) != (find_rib name2 env2)) & ((getValOfAdd add1) > -1 or (getValOfAdd add2) > -1)) then true else false));;

  let rec getFinalVal check read = function
    |[] -> check
    |write :: t -> ((getFinalVal (check or ((comp read) write)) read) t);;

  let should_box_var name expr params =
    let nt1 = (find_reads_and_writes name expr params) in
    (List.fold_left
       (fun x check -> x or check)
       false
       (List.map
       (fun read -> ((getFinalVal false read) (getSecond nt1) ))
       (getFirst nt1) ));;

  let box_sets_and_gets name body =
    let rec run expr =
      match expr with
      | ScmConst' _ -> expr
      | ScmVarGet' (Var' (_, Free)) -> expr
      | ScmVarGet' (Var' (name', _) as v) ->
         if name = name'
         then ScmBoxGet' v
         else expr
      | ScmBox' _ -> expr
      | ScmBoxGet' _ -> expr
      | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, run expr)
      | ScmIf' (test, dit, dif) ->
         ScmIf' (run test, run dit, run dif)
      | ScmSeq' exprs -> ScmSeq' (List.map run exprs)
      | ScmVarSet' (Var' (_, Free) as v, expr') ->
         ScmVarSet'(v, run expr')
      | ScmVarSet' (Var' (name', _) as v, expr') ->
         if name = name'
         then ScmBoxSet' (v, run expr')
         else ScmVarSet' (v, run expr')
      | ScmVarDef' (v, expr) -> ScmVarDef' (v, run expr)
      | ScmOr' exprs -> ScmOr' (List.map run exprs)
      | (ScmLambda' (params, Simple, expr)) as expr' ->
         if List.mem name params
         then expr'
         else ScmLambda' (params, Simple, run expr)
      | (ScmLambda' (params, Opt opt, expr)) as expr' ->
         if List.mem name (params @ [opt])
         then expr'
         else ScmLambda' (params, Opt opt, run expr)
      | ScmApplic' (proc, args, app_kind) ->
         ScmApplic' (run proc, List.map run args, app_kind)
    in
    run body;;

  let make_sets =
    let rec run minor names params =
      match names, params with
      | [], _ -> []
      | name :: names', param :: params' ->
         if name = param
         then let v = Var' (name, Param minor) in
              (ScmVarSet' (v, ScmBox' v)) :: (run (minor + 1) names' params')
         else run (minor + 1) names params'
      | _, _ -> raise (X_this_should_not_happen
                        "no free vars should be found here")
    in
    fun box_these params -> run 0 box_these params;;

  let rec auto_box expr =
    match expr with
    | ScmConst' _ | ScmVarGet' _ | ScmBox' _ | ScmBoxGet' _ -> expr
    | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, auto_box expr)
    | ScmIf' (test, dit, dif) ->
       ScmIf' (auto_box test, auto_box dit, auto_box dif)
    | ScmSeq' exprs -> ScmSeq' (List.map auto_box exprs)
    | ScmVarSet' (v, expr) -> ScmVarSet'(v, auto_box expr)
    | ScmVarDef' (v, expr) -> ScmVarDef'(v, auto_box expr)
    | ScmOr' exprs ->  ScmOr' (List.map auto_box exprs)
    | ScmLambda' (params, Simple, expr') ->
       let box_these =
         List.filter
           (fun param -> should_box_var param expr' params)
           params in
       let new_body =
         List.fold_left
           (fun body name -> box_sets_and_gets name body)
           (auto_box expr')
           box_these in
       let new_sets = make_sets box_these params in
       let new_body =
         match box_these, new_body with
         | [], _ -> new_body
         | _, ScmSeq' exprs -> ScmSeq' (new_sets @ exprs)
         | _, _ -> ScmSeq'(new_sets @ [new_body]) in
       ScmLambda' (params, Simple, new_body)
    | ScmLambda' (params, Opt opt, expr') ->
        let box_these =
         List.filter
           (fun param -> should_box_var param expr' (params @ [opt]))
            (params @ [opt]) in
       let new_body =
         List.fold_left
           (fun body name -> box_sets_and_gets name body)
           (auto_box expr')
           box_these in
       let new_sets = make_sets box_these  (params @ [opt]) in
       let new_body =
         match box_these, new_body with
         | [], _ -> new_body
         | _, ScmSeq' exprs -> ScmSeq' (new_sets @ exprs)
         | _, _ -> ScmSeq'(new_sets @ [new_body]) in
       ScmLambda' (params, Opt opt, new_body)
    | ScmApplic' (proc, args, app_kind) ->
       ScmApplic' (auto_box proc, List.map auto_box args, app_kind);;

  let semantics expr =
    auto_box
      (annotate_tail_calls
         (annotate_lexical_address expr));;

end;; (* end of module Semantic_Analysis *)

let sexpr_of_var' (Var' (name, _)) = ScmSymbol name;;

let rec sexpr_of_expr' = function
  | ScmConst' (ScmVoid) -> ScmVoid
  | ScmConst' ((ScmBoolean _) as sexpr) -> sexpr
  | ScmConst' ((ScmChar _) as sexpr) -> sexpr
  | ScmConst' ((ScmString _) as sexpr) -> sexpr
  | ScmConst' ((ScmNumber _) as sexpr) -> sexpr
  | ScmConst' ((ScmSymbol _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmConst'(ScmNil as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmConst' ((ScmVector _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmVarGet' var -> sexpr_of_var' var
  | ScmIf' (test, dit, ScmConst' ScmVoid) ->
     let test = sexpr_of_expr' test in
     let dit = sexpr_of_expr' dit in
     ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
  | ScmIf' (e1, e2, ScmConst' (ScmBoolean false)) ->
     let e1 = sexpr_of_expr' e1 in
     (match (sexpr_of_expr' e2) with
      | ScmPair (ScmSymbol "and", exprs) ->
         ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
      | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
  | ScmIf' (test, dit, dif) ->
     let test = sexpr_of_expr' test in
     let dit = sexpr_of_expr' dit in
     let dif = sexpr_of_expr' dif in
     ScmPair
       (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
  | ScmSeq' ([]) -> ScmVoid
  | ScmSeq' ([expr]) -> sexpr_of_expr' expr
  | ScmSeq' (exprs) ->
     ScmPair (ScmSymbol "begin", 
              scheme_sexpr_list_of_sexpr_list
                (List.map sexpr_of_expr' exprs))
  | ScmVarSet' (var, expr) ->
     let var = sexpr_of_var' var in
     let expr = sexpr_of_expr' expr in
     ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmVarDef' (var, expr) ->
     let var = sexpr_of_var' var in
     let expr = sexpr_of_expr' expr in
     ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmLambda' (params, Simple, expr) ->
     let expr = sexpr_of_expr' expr in
     let params = scheme_sexpr_list_of_sexpr_list
                    (List.map (fun str -> ScmSymbol str) params) in
     ScmPair (ScmSymbol "lambda",
              ScmPair (params,
                       ScmPair (expr, ScmNil)))
  | ScmLambda' ([], Opt opt, expr) ->
     let expr = sexpr_of_expr' expr in
     let opt = ScmSymbol opt in
     ScmPair
       (ScmSymbol "lambda",
        ScmPair (opt, ScmPair (expr, ScmNil)))
  | ScmLambda' (params, Opt opt, expr) ->
     let expr = sexpr_of_expr' expr in
     let opt = ScmSymbol opt in
     let params = List.fold_right
                    (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                    params
                    opt in
     ScmPair
       (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
  | ScmApplic' (ScmLambda' (params, Simple, expr), args, app_kind) ->
     let ribs =
       scheme_sexpr_list_of_sexpr_list
         (List.map2
            (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
            params
            (List.map sexpr_of_expr' args)) in
     let expr = sexpr_of_expr' expr in
     ScmPair
       (ScmSymbol "let",
        ScmPair (ribs,
                 ScmPair (expr, ScmNil)))
  | ScmApplic' (proc, args, app_kind) ->
     let proc = sexpr_of_expr' proc in
     let args =
      scheme_sexpr_list_of_sexpr_list
         (List.map sexpr_of_expr' args) in
     ScmPair (proc, args)
  | _ -> ScmNil;;

let string_of_expr' expr =
  Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr' expr);;

let print_expr' chan expr =
  output_string chan
    (string_of_expr' expr);;

let print_exprs' chan exprs =
  output_string chan
    (Printf.sprintf "[%s]"
       (String.concat "; "
          (List.map string_of_expr' exprs)));;

let sprint_expr' _ expr = string_of_expr' expr;;

let sprint_exprs' chan exprs =
  Printf.sprintf "[%s]"
    (String.concat "; "
       (List.map string_of_expr' exprs));;

(* end-of-input *)
