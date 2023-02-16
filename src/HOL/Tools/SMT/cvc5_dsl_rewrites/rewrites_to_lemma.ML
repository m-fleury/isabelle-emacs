signature WRITE_LEMMA =
sig
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

  val write_lemma: PARSE_REWRITE.rewrite_tree -> Proof.context -> string list list
  val write_lemmas: PARSE_REWRITE.rewrite_tree list -> string -> string -> Proof.context -> string list list
end;

open PARSE_REWRITE
open SMTLIB_Proof

structure WRITE_LEMMA: WRITE_LEMMA =
struct
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

fun string_of_term ctxt s =
  let
    val t = Syntax.read_term ctxt s;
    val T = Term.type_of t;
    val ctxt' = Proof_Context.augment t ctxt;
  in
    Pretty.string_of
      (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)])
  end;

fun hackish_string_of_term ctxt =
 Print_Mode.setmp [] (Syntax.string_of_term ctxt)
  #> YXML.content_of

fun hackish_string_of_type ctxt =
 Print_Mode.setmp [] (Syntax.string_of_typ ctxt)
  #> YXML.content_of

fun nary_assoc ((Const operator) $ (Free (var1,typ1)) $ (Free (var2,typ2))) lvars = 
 let
  val var1_is_in_list = List.find (fn a => var1 = a) lvars
  val var2_is_in_list = List.find (fn a => var2 = a) lvars
  val _ = @{print}("operator",operator)

  fun neutral_for_operator "HOL.conj" = Const (\<^const_name>\<open>HOL.True\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "HOL.disj" = Const (\<^const_name>\<open>HOL.False\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "Groups.plus_class.plus" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Orderings.ord_class.less_eq" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Groups.times_class.times" = Const (\<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>) |
      (*neutral_for_operator "Smtlib_String.cvc_re_concat" = Free ("{''''}", \<^typ>\<open>RegLan\<close>) | (*TODO*)*)
      neutral_for_operator "Smtlib_String.cvc_str_concat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) |
      neutral_for_operator l = (@{print}("neutral_for_operator", l);Free ("PutInNeutral", \<^typ>\<open>HOL.bool\<close>))

  val new_operator =
    if var1_is_in_list = NONE andalso var2_is_in_list = NONE
      then Const operator
    else if var1_is_in_list = NONE
      then Const(\<^const_name>\<open>cvc_list_right\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>) $ Const operator
    else if var2_is_in_list = NONE 
      then Const(\<^const_name>\<open>cvc_list_left\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a \<Rightarrow> 'a\<close>) $ Const operator
    else
      Const(\<^const_name>\<open>cvc_list_both\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar
          \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a \<Rightarrow> 'a\<close>) $ Const operator $ (neutral_for_operator (fst operator))
 in 
  (new_operator $ (Free (var1,typ1)) $ (Free (var2,typ2)))
 end |
nary_assoc (Const operator $ (Free (var1,typ1)) $ l2) lvars = 
 let
  val var1_is_in_list = List.find (fn a => var1 = a) lvars
  val new_operator =
    if var1_is_in_list = NONE
    then Const operator
    else Const (\<^const_name>\<open>cvc_list_left\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>)
        $ Const operator
 in 
  (new_operator $ (Free (var1,typ1)) $ (nary_assoc l2 lvars))
 end |
nary_assoc (Const operator $ l1 $ (Free (var2,typ2))) lvars = 
let
  val var2_is_in_list = List.find (fn a => var2 = a) lvars
  val new_operator =
    if var2_is_in_list = NONE
    then Const operator
    else Const (\<^const_name>\<open>cvc_list_right\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>)
         $ Const operator
in  
  (new_operator $ (nary_assoc l1 lvars) $ (Free (var2,typ2)) )
 end |
nary_assoc (l1$l2) lvars = (nary_assoc l1 lvars) $ (nary_assoc l2 lvars) |
nary_assoc l1 lvars = (@{print}("l1",l1);l1)


fun collect_lists [] = [] |
    collect_lists ((SMTLIB.S [SMTLIB.Sym var,SMTLIB.S [SMTLIB.Sym "cvc_ListVar", SMTLIB.Sym typ]])::ts)
      = var :: collect_lists ts |
    collect_lists (t::ts) = collect_lists ts

fun get_term tree pars ctxt = 
hackish_string_of_term ctxt
 (nary_assoc (fst (SMTLIB_Proof.term_of tree (empty_context ctxt Symtab.empty Symtab.empty))) (collect_lists pars))

fun write_file_header theory_name theory_imports 
= [["theory " ^ theory_name ^ "\n"],["  imports Dsl_Nary_Ops " ^ theory_imports ^ "\n"], ["begin\n\n"]
  ,["(* This is a theory automatically created from a rare file! All that remains to do is to prove\n",
    "any lemma whose auto proof fails and to to import this file in SMT.thy. \n",
    "If your rare statements use nary operators over lists that would be binarised by Isabelle \n",
    "you have to add it in Dsl_Nary_Ops.thy. Currently supported are the operators:\n",
    "and,",
    "or",
    "*)\n\n"]]
val write_file_footer = ["end"]

(*TODO: Do better named_theorems word_and_rbl_bvand \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>*)
fun write_lemma_header name = ["named_theorems " ^ name ^ " \<open>automatically_generated\<close>\n\n"] @ ["lemma [" ^ name ^ "]:\n"]
fun write_fixes pars ctxt = 
let
  val cx = (empty_context ctxt Symtab.empty Symtab.empty)
  fun write_par (SMTLIB.S [var,typ]) = 
let
  val _ = @{print}("test",(SMTLIB_Proof.type_of cx typ))
in
 hackish_string_of_term ctxt (fst (SMTLIB_Proof.term_of var (empty_context ctxt Symtab.empty Symtab.empty)))
 ^ "::\"" ^ hackish_string_of_type ctxt (SMTLIB_Proof.type_of cx typ) ^ "\""
end
  fun write_params [] = [] |
  write_params (p::ps) = write_par p ^ (if ps = [] then "" else " and ") :: write_params ps
in
  ["  fixes " ] @ write_params pars @ ["\n"]
end



(*TODO: Only collect_lists pars once*)
fun write_shows pars match target ctxt
    = ["  shows \"((" ^ get_term match pars ctxt ^ ") = (" ^ get_term target pars ctxt ^ "))\"\n" ] (*Use term_of? and then parse to string? Need context*)
fun write_shows_wth_assump pars ass match target ctxt
   =  ["  assumes \"" ^ get_term ass pars ctxt ^ "\"\n" ^
"  shows \"((" ^ get_term match pars ctxt ^ ") = (" ^ get_term target pars ctxt ^ "))\"\n" ] 
(*val write_auto = ["  by auto\n\n"]*)
fun write_auto pars name =
let
  val lists = (collect_lists pars) (*TODO: Should not do this twice*)
  fun write_cases [] = "" |
    write_cases (x::xs) = "  apply (cases " ^ x ^ ")\n" ^  write_cases xs
  fun write_subgoal [] = "" | (*TODO: use fold*)
    write_subgoal (x::xs) = x ^ " " ^  write_subgoal xs
  val tactic = write_cases lists ^ "  subgoal for " ^ write_subgoal lists ^ "\n" ^
               "    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)\n" ^ 
               "    by (simp add: " ^ name ^  "_lemma)\n" ^
               "  done\n\n"
in
 if lists = [] then ["  by auto\n\n"] else [tactic]
end
fun write_lemma (Rewrite_Rule ((Rule_Type DEFINE_RULE)::(Rule_Name name)::rest )) ctxt =
    let
      val [Par param, Match m, Target t] = rest
val _ = @{print}("rest",rest)

     (* val [Target t] = rest*)




      (*val (m_tree,m_both_empty) = (nary_assoc (fst (SMTLIB_Proof.term_of m (empty_context ctxt Symtab.empty Symtab.empty))) (collect_lists pars))
      val (t_tree,t_both_empty) = (nary_assoc (fst (SMTLIB_Proof.term_of t (empty_context ctxt Symtab.empty Symtab.empty))) (collect_lists pars))

      val both_empty = m_both_empty (*TODO: No duplicate add t_both_empty*)
*)
      (*Have write function that takes in empty_list and call it for any combination of elements in both_empty including 0?*)

      (*val write_base_lemma = [write_lemma_header name, write_fixes param ctxt, write_shows param m t ctxt, write_auto param name]*)
val test = (SMTLIB_Proof.term_of t (empty_context ctxt Symtab.empty Symtab.empty))
val _ = @{print}("test",test)


(*("test",
 (Const ("HOL.All", "(??a7586076 word \<Rightarrow> bool) \<Rightarrow> bool") $
    Abs ("x", "??a7586076 word",
      Const ("HOL.All", "(??a7586078 word \<Rightarrow> bool) \<Rightarrow> bool") $
        Abs ("y", "??a7586078 word",
          Const ("HOL.All", "(... ... ... ...) \<Rightarrow> bool") $ Abs ("z", "... word", Const ("...", ...) $ Bound 0 $ ...)))*)


val res = ["\"" ^ hackish_string_of_term ctxt
 (fst (SMTLIB_Proof.term_of t (empty_context ctxt Symtab.empty Symtab.empty))) ^ "\"\n"]
    in 
      (* [write_lemma_header name, write_fixes param ctxt, write_shows param m t ctxt, write_auto param name]*)
       [write_lemma_header name, res]

 
    end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_COND_RULE)::(Rule_Name name)::rest )) ctxt =
    let
      val [Par param, Precondition ass, Match m, Target t] = rest
    in 
      [write_lemma_header name, write_fixes param ctxt, write_shows_wth_assump param ass m t ctxt, write_auto param name]
    end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_STAR_RULE)::(Rule_Name name)::rest )) ctxt =
    let
      val [Par param, Context_Expr context_expr, Match m, Target t] = rest
    in (*TODO*)
      (write_lemma_header name) :: [write_fixes param ctxt, write_shows param m t ctxt,write_auto param name]
    end |
    write_lemma rwr ctxt = 
let val _ = @{print}("rwr",rwr)
in
raise WRITE_LEMMA_FROM_DSL_REWRITE ("Could not write rewrite rule to lemma, has wrong form" ) (*^ PARSE_REWRITE.to_str rwr)*)
end

local
  fun write_lemmas_h [] _ = [] |
      write_lemmas_h (c::cs) ctxt = (write_lemma c ctxt) @ write_lemmas_h cs ctxt
in 
  fun write_lemmas cs theory_name theory_imports ctxt
    = write_file_header theory_name theory_imports @ write_lemmas_h cs ctxt @ [write_file_footer]
end

end;