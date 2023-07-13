(*  Title:      HOL/Tools/SMT/SMT_string.ML
    Author:     Hanna Lachnitt, Stanford

SMT setup for strings.
*)

signature SMT_String = 
sig 
   val string_type_parser : SMTLIB.tree * typ list -> typ option
   val string_term_parser :  SMTLIB.tree * term list -> term option
end


structure SMT_String: SMT_String =
struct

fun mk_const n U = Const (n, U)

fun mk_unary n U t =
  let val T = fastype_of t
  in Const (n, T --> U) $ t end

fun mk_binary n U t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
  in Const (n, [T1, T2] ---> U) $ t1 $ t2 end

fun mk_ternary n U t1 t2 t3 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T3 = fastype_of t3
  in Const (n, [T1, T2, T3] ---> U) $ t1 $ t2 $ t3 end

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_lassoc' n U = mk_lassoc (mk_binary n U)

fun string_type_parser (SMTLIB.Sym "String", []) = SOME \<^typ>\<open>String.string\<close>
  | string_type_parser (SMTLIB.Sym "RegLan", []) = SOME \<^typ>\<open>RegLan\<close>
  | string_type_parser _ = NONE

fun  string_term_parser (SMTLIB.Sym "str.++", t::ts) = SOME (mk_lassoc' \<^const_name>\<open>smtlib_str_concat\<close> \<^typ>\<open>String.string\<close> t ts)
  | string_term_parser (SMTLIB.Sym "str.len", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_len\<close> \<^typ>\<open>Int.int\<close> t1)
  | string_term_parser (SMTLIB.Sym "str.const", [t1]) = SOME (Free ("''''", \<^typ>\<open>String.string\<close>))
  | string_term_parser (SMTLIB.Sym "str.const", []) = SOME (Free ("''''", \<^typ>\<open>String.string\<close>))
  (*| string_term_parser (SMTLIB.Sym "str.less", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_less\<close> \<^typ>\<open>HOL.bool\<close> t1 t2)*)
  | string_term_parser (SMTLIB.Sym "str.to_re", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_to_re\<close> \<^typ>\<open>RegLan\<close> t1)
  | string_term_parser (SMTLIB.Sym "str.in_re", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_in_re\<close> \<^typ>\<open>HOL.bool\<close> t1 t2)
  | string_term_parser (SMTLIB.Sym "re.none", []) = SOME (mk_const \<^const_name>\<open>smtlib_re_none\<close> \<^typ>\<open>RegLan\<close>)
  | string_term_parser (SMTLIB.Sym "re.all", []) = SOME (mk_const \<^const_name>\<open>smtlib_re_all\<close> \<^typ>\<open>RegLan\<close>)
  | string_term_parser (SMTLIB.Sym "re.allchar", []) = SOME (mk_const \<^const_name>\<open>smtlib_re_allchar\<close> \<^typ>\<open>RegLan\<close>)
  | string_term_parser (SMTLIB.Sym "re.++", t::ts) = SOME (mk_lassoc' \<^const_name>\<open>smtlib_re_concat\<close> \<^typ>\<open>RegLan\<close> t ts)
  | string_term_parser (SMTLIB.Sym "re.union", t::ts) = SOME (mk_lassoc' \<^const_name>\<open>smtlib_re_union\<close> \<^typ>\<open>RegLan\<close> t ts)
  | string_term_parser (SMTLIB.Sym "re.inter", t::ts) = SOME (mk_lassoc' \<^const_name>\<open>smtlib_re_inter\<close> \<^typ>\<open>RegLan\<close> t ts)
  | string_term_parser (SMTLIB.Sym "re.*", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_re_star\<close> \<^typ>\<open>RegLan\<close> t1)
  (*| string_term_parser (SMTLIB.Sym "str.leq", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_leq\<close> \<^typ>\<open>HOL.bool\<close> t1 t2)*)
  | string_term_parser (SMTLIB.Sym "str.at", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_at\<close> \<^typ>\<open>String.string\<close> t1 t2)
  | string_term_parser (SMTLIB.Sym "str.substr", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_substr\<close> \<^typ>\<open>String.string\<close> t1 t2 t3)
  | string_term_parser (SMTLIB.Sym "str.prefixof", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_prefixof\<close> \<^typ>\<open>HOL.bool\<close> t1 t2)
  | string_term_parser (SMTLIB.Sym "str.suffixof", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_suffixof\<close> \<^typ>\<open>HOL.bool\<close> t1 t2)
  | string_term_parser (SMTLIB.Sym "str.contains", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_str_contains\<close> \<^typ>\<open>HOL.bool\<close> t1 t2)
  | string_term_parser (SMTLIB.Sym "str.indexof", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_indexof\<close> \<^typ>\<open>Int.int\<close> t1 t2 t3)
  | string_term_parser (SMTLIB.Sym "str.replace", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_replace\<close> \<^typ>\<open>String.string\<close> t1 t2 t3)
  | string_term_parser (SMTLIB.Sym "str.replace_all", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_replace_all\<close> \<^typ>\<open>String.string\<close> t1 t2 t3)
  | string_term_parser (SMTLIB.Sym "str.replace_re", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_replace_re\<close> \<^typ>\<open>String.string\<close> t1 t2 t3)
  | string_term_parser (SMTLIB.Sym "str.replace_re_all", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_replace_re_all\<close> \<^typ>\<open>String.string\<close> t1 t2 t3)
  | string_term_parser (SMTLIB.Sym "re.comp", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_re_comp\<close> \<^typ>\<open>RegLan\<close> t1)
  | string_term_parser (SMTLIB.Sym "re.diff", t::ts) = SOME (mk_lassoc' \<^const_name>\<open>smtlib_re_diff\<close> \<^typ>\<open>RegLan\<close> t ts)
  | string_term_parser (SMTLIB.Sym "re.plus", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_re_plus\<close> \<^typ>\<open>RegLan\<close> t1)
  | string_term_parser (SMTLIB.Sym "re.opt", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_re_opt\<close> \<^typ>\<open>RegLan\<close> t1)
  | string_term_parser (SMTLIB.Sym "re.range", [t1,t2]) = SOME (mk_binary \<^const_name>\<open>smtlib_re_range\<close> \<^typ>\<open>RegLan\<close> t1 t2)
  | string_term_parser (SMTLIB.Sym "re.^", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_re_pow\<close> \<^typ>\<open>RegLan\<close> t1) (*TODO*)
  | string_term_parser (SMTLIB.Sym "re.loop", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_re_loop\<close> \<^typ>\<open>RegLan\<close> t1) (*TODO*)
  | string_term_parser (SMTLIB.Sym "str.is_digit", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_is_digit\<close> \<^typ>\<open>HOL.bool\<close> t1)
  | string_term_parser (SMTLIB.Sym "str.to_code", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_to_code\<close> \<^typ>\<open>Int.int\<close> t1)
  | string_term_parser (SMTLIB.Sym "str.from_code", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_from_code\<close> \<^typ>\<open>String.string\<close> t1)
  | string_term_parser (SMTLIB.Sym "str.to_int", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_to_int\<close> \<^typ>\<open>Int.int\<close> t1)
  | string_term_parser (SMTLIB.Sym "str.from_int", [t1]) = SOME (mk_unary \<^const_name>\<open>smtlib_str_from_int\<close> \<^typ>\<open>String.string\<close> t1)
(*Non SMT-LIB: https://github.com/cvc5/cvc5/blob/proof-new/docs/theories/strings.rst*)
  | string_term_parser (SMTLIB.Sym "str.update", [t1,t2,t3]) = SOME (mk_ternary \<^const_name>\<open>smtlib_str_update\<close> \<^typ>\<open>String.string\<close> t1 t2 t3)
  | string_term_parser _ = NONE

(*val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser string_type_parser #>
  SMTLIB_Proof.add_term_parser string_term_parser))*)

end;
