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

(* Utilities *)

fun hackish_string_of_term ctxt =
 Print_Mode.setmp [] (Syntax.string_of_term ctxt)
  #> YXML.content_of

fun hackish_string_of_type ctxt =
 Print_Mode.setmp [] (Syntax.string_of_typ ctxt)
  #> YXML.content_of

fun generalize_types ctxt t =
let
  (*Don't erase simple types here.*)
  (*val erase_types = map_types (fn x => dummyT)*)
  (* use schematic type variables *)
  val ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern
  val infer_types = singleton (Type_Infer_Context.infer_types ctxt)
in
  t  |> infer_types
end


(* Writing Utility Functions *)

(*TODO: List of lists and line-breaks*)
fun write_file_header theory_name theory_imports 
= [["theory " ^ theory_name ^ "\n"],["  imports Dsl_Nary_Ops " ^ theory_imports ^ "\n"], ["begin\n\n"]
  ,["(* This is a theory automatically created from a rare file! All that remains to do is to prove\n",
    "any lemma whose provided proof fails and to to import this file in SMT.thy. \n",
    "If your rare statements use nary operators over lists that would be binarised by Isabelle \n",
    "you have to add it in Dsl_Nary_Ops.thy. Currently already supported are the operators:\n",
    "and,\n",
    "or,\n",
    "plus,\n",
    "times,\n",
    "append,\n",
    "re_concat,\n",
    "str_concat,\n",
    "*)\n\n"]]
val write_file_footer = ["end"]
fun write_lemma_header name = ["named_theorems rewrite_" ^ name ^ " \<open>automatically_generated\<close>\n\n"]
                            @ ["lemma [rewrite_" ^ name ^ "]:\n"]

fun write_auto lists name =
let
  fun write_cases xs = if xs = [] then ""
    else map (fn str => "  apply (cases " ^ str ^ ")\n") xs |> foldl1 (String.^)
  fun write_subgoal xs = if xs = [] then "" else map (fn str => str ^ "s ") xs |> foldl1 (String.^)

  val tactic = write_cases lists ^ "  subgoal for " ^ write_subgoal lists ^ "\n" ^
               "    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)\n" ^ 
               "    by (simp add: " ^ name ^  "_lemma)\n" ^
               "  done\n\n"
in
 if lists = [] then ["  by auto\n\n"] else [tactic]
end

(* Functions to Manipulate Terms *)
(*TODO decrease m instead of giving two arguments*)
fun mk_nary ((Const (operator_name,operator_typ)) $ (Bound m1) $ (Bound m2)) lvars lists n m =
let
 val var1_is_in_list = List.find (fn a => m1 = a) lvars
 val var2_is_in_list = List.find (fn a => m2 = a) lvars

 fun neutral_for_operator "HOL.conj" = Const (\<^const_name>\<open>HOL.True\<close>, \<^typ>\<open>HOL.bool\<close>) |
     neutral_for_operator "HOL.disj" = Const (\<^const_name>\<open>HOL.False\<close>, \<^typ>\<open>HOL.bool\<close>) |
     neutral_for_operator "Groups.plus_class.plus" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
     neutral_for_operator "Orderings.ord_class.less_eq" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
     neutral_for_operator "Groups.times_class.times" = Const (\<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>) |
     neutral_for_operator "Smtlib_String.smtlib_re_concat" = Free ("{''''}", \<^typ>\<open>RegLan\<close>) |
     neutral_for_operator "Smtlib_String.smtlib_str_concat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) |
     neutral_for_operator "Word.word_cat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) | (*TODO*)
     neutral_for_operator l = (@{print}("neutral_for_operator", l);Free ("PutInNeutral", \<^typ>\<open>HOL.bool\<close>))

  val T = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

  val new_operator =
    if var1_is_in_list = NONE andalso var2_is_in_list = NONE
      then Const (operator_name,dummyT)
    else if var1_is_in_list = NONE (* \<^typ>\<open>(T \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>*)
      then Const(\<^const_name>\<open>cvc_list_right\<close>,T ) $ Const (operator_name,dummyT)
    else if var2_is_in_list = NONE (* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a \<Rightarrow> 'a\<close>*)
      then Const(\<^const_name>\<open>cvc_list_left\<close>,T) $ Const (operator_name,dummyT)
    else (* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar
          \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a \<Rightarrow> 'a\<close>*)
      Const(\<^const_name>\<open>cvc_list_both\<close>,T) $ Const (operator_name,dummyT) $ (neutral_for_operator (fst (operator_name,dummyT)))
 in 
  (new_operator $ (Bound m1) $ (Bound m2))
end |
mk_nary ((Const (operator_name,operator_typ)) $ (Bound m1) $ l2) lvars lists n m =
let 
 val var1_is_in_list = List.find (fn a => m1 = a) lvars
  val T = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

 val new_operator =
    if var1_is_in_list = NONE
    then Const (operator_name,dummyT) (* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow>'a \<Rightarrow> 'a\<close>*)
    else Const (\<^const_name>\<open>cvc_list_left\<close>,T)
        $ Const (operator_name,dummyT)
 in 
  (new_operator $ (Bound m1) $ (mk_nary l2 lvars lists n m))
 end |
mk_nary ((Const (operator_name,operator_typ)) $ l1 $ (Bound m2)) lvars lists n m =
let
  val var2_is_in_list = List.find (fn a => m2 = a) lvars
  val T = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

  val new_operator =
    if var2_is_in_list = NONE
    then Const (operator_name,dummyT)(* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>*)
    else Const (\<^const_name>\<open>cvc_list_right\<close>,T)
         $ Const (operator_name,dummyT)
in  
  (new_operator $ (mk_nary l1 lvars lists n m) $ (Bound m2))
 end
 |
mk_nary (Const ("HOL.All", Type (t1,[Type(t2a,[t2b1,t2b2]),t3])) $ (Abs (name, typ,l2))) lvars lists n m= (*TODO also need to change Const*)
let
(*val _ = @{print}("t1",t1);
val _ = @{print}("t2a",t2a);
val _ = @{print}("t2b",t2b1);

val _ = @{print}("t3",t3);

val _ = @{print}("lists",lists);*)
 val var1_is_in_list = List.find (fn a => name = a) lists

val (new_typ,new_lvars) = if var1_is_in_list = NONE then (typ,lvars)  
else (Type("Dsl_Nary_Ops.cvc_ListVar",[typ]),(m-n)::lvars)

(*val _ = @{print}("new_lvars",new_lvars);*)
(*TODO: make list here if var1_is_in_list*)

in
 (Const ("HOL.All", Type (t1,[Type(t2a,[new_typ,t2b2]),t3])) $ (Abs (name, new_typ,mk_nary l2 new_lvars lists (n+1) m)))
end |
mk_nary (l1 $ l2) lvars lists n m = ((*@{print}("l1$l2",l1$l2);*) (mk_nary l1 lvars lists n m) $ (mk_nary l2 lvars lists n m)) |
mk_nary l1 _ _ _ _ = l1

fun write_body res param ctxt =
let
  val str_res = hackish_string_of_term ctxt res
  val _ = @{print}("str_res",str_res)

  fun wth_forall ("."::" "::xs) = xs |
      wth_forall ("."::"\n"::" "::" "::" "::xs) = xs |
      wth_forall ("."::xs) = xs | 
      wth_forall (_::xs) = wth_forall xs |
      wth_forall [] = []
  fun write_params [] = "" |
      write_params [p] =  p |
      write_params (p::ps) = p ^ " and " ^ write_params ps

  val pars = "" (*get_pars ctxt res (rev param) [] |> write_params*)
  val _ = @{print}("pars", pars)
  val goal = raw_explode str_res |> wth_forall |> implode
in 
  ["  fixes " ^ pars  ^ "\n"] @ ["  shows \"" ^ goal ^ "\"\n" ]
end


local
 fun parse_tree smtlib_tree list_param nr_pars ctxt =
  let
    val _ = @{print}("smtlib_tree",smtlib_tree)
    (*First the tree is parsed without considering lists*)
    val cx = empty_context ctxt Symtab.empty Symtab.empty
    val term = SMTLIB_Proof.term_of smtlib_tree cx |> fst
    val _ = @{print}("smtlib_tree as term",term)
    (*Then, the whole term is traversed to make terms lists and introduce corresponding operators*)
    val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) list_param
    val _ = @{print}("list_param2", list_param2)

    val nary_term = mk_nary term [] list_param2 0 (nr_pars - 1)
    val _ = @{print}("nary_term", nary_term)
  val str_body = hackish_string_of_term ctxt nary_term
  val _ = @{print}("str_body",str_body)


    (*Finally, types are reinferred to allow gradual types*)
    (*val ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern
    val infer_types = singleton (Type_Infer_Context.infer_types ctxt)
    val term_gen_types = nary_term |> infer_types*)

    val term_gen_types = nary_term |> generalize_types ctxt
    val _ = @{print}("term_gen_types",term_gen_types)

  in
   (term_gen_types,ctxt)
  end

 fun write_pars res ctxt = 
 let
   fun write_params [] = "" |
       write_params [Const (str,typ)] = str ^ ":: \"" ^ hackish_string_of_type ctxt typ ^ "\"" |
       write_params (Const (str,typ)::ps) = 
let 
  val t2 = dest_Type typ(*'a word*)
val _ = @{print}("t2222",t2)
in
  str ^ ":: \"" ^ hackish_string_of_type ctxt typ ^ "\"" ^ " and " ^ write_params ps
end

fun delete_question_mark l = 
if hd l = "?" then tl (tl l) else l


fun temp ("w"::"o"::"r"::"d"::ts) = (":"::":"::"l"::"e"::"n"::" ":: "w"::"o"::"r"::"d"::ts) |
    temp (t::ts) = t :: temp ts|
    temp [] = []

fun test (Const ("HOL.All", _) $ Abs (str, typ,((Const ("HOL.All", typ1) $ t1))))
=
let
val _ = @{print}("typ IN PARM",dest_Type typ) (*"Word.word", ["??'a"]*)


val new_type
 = implode (temp (hackish_string_of_type ctxt typ |> raw_explode |> delete_question_mark)) (*LENGTH thing should happen in parser eventually*)
in
 str ^ "::\"" ^ new_type ^ "\"" ^ " and " ^ test ((Const ("HOL.All", typ1) $ t1))
end |
 test (Const ("HOL.All", _) $ Abs (str, typ,ts))
= str ^ "::\"" ^  (implode (temp (hackish_string_of_type ctxt typ |> raw_explode |> delete_question_mark)))  ^ "\""
 in
  ["  fixes " ^ test res ^ "\n"]
 end

 fun write_body body ctxt =
 let
  val str_body = hackish_string_of_term ctxt body
  val _ = @{print}("str_body",str_body)
  
  fun wth_forall ("."::" "::xs) = xs |
      wth_forall ("."::"\n"::" "::" "::" "::xs) = xs |
      wth_forall ("."::xs) = xs | 
      wth_forall (_::xs) = wth_forall xs |
      wth_forall [] = []

  val goal = raw_explode str_body |> wth_forall |> filter (fn x => not (x = "?")) |> implode

 in
  ["  shows \"" ^ goal ^ "\"\n" ]
 end

(*Would the use of Pure.all change this all?!*)
 fun quant_letify_tree tree param (NONE)
   = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (rev param), tree]
  | quant_letify_tree tree param (SOME lets)
   = (@{print}("lets",lets);SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (rev param),
                   SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S lets, tree]])

in 
  fun write_lemma (Rewrite_Rule ((Rule_Type DEFINE_RULE)::(Rule_Name name):: [Par (param,list_param), Let_Defs ld, Match m, Target t])) ctxt =
   let
    val _ = @{print}("current define-rule to write: ", name)
    val _ = @{print}("param: ", param)
    val _ = @{print}("list_param: ", list_param)
    val _ = @{print}("let_def: ", ld)

    (*Build up smtlib tree*)
    val smtlib_tree_body = SMTLIB.S [SMTLIB.Sym "=", m, t]
    val smtlib_tree = quant_letify_tree smtlib_tree_body param ld
    (*Get term of smtlib_tree*)
    val (res,ctxt) = parse_tree smtlib_tree list_param (length param) ctxt
    (*Get components of term for printing*)
  (*  val (pars,rest) = parse_pars res []
    val _ = @{print}("pars: ", pars)
    val _ = @{print}("rest: ", rest)*)
    val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) list_param

   in
    [write_lemma_header name, write_pars res ctxt, write_body res ctxt, write_auto list_param2 name]
   end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_COND_RULE)::(Rule_Name name)::[Par (param,list_param), Let_Defs ld, Precondition ass, Match m, Target t])) ctxt =
   let
    val _ = @{print}("current define-cond-rule to write: ", name)
    val smtlib_tree_body = SMTLIB.S [SMTLIB.Sym "implies", ass, SMTLIB.S [SMTLIB.Sym "=", m, t]]
    val smtlib_tree = quant_letify_tree smtlib_tree_body param ld
    val (res,ctxt) = parse_tree smtlib_tree list_param (length param) ctxt
    val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) list_param

   in 
     [write_lemma_header name, write_pars res ctxt, write_body res ctxt, write_auto list_param2 name]
   end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_STAR_RULE)::(Rule_Name name)::[Par (param,list_param), Let_Defs ld, Context_Expr context_expr, Match m, Target t])) ctxt =
   let (*TODO*)
     val _ = @{print}("current define-star-rule to write: ", name)
     val smtlib_tree = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S param, SMTLIB.S [SMTLIB.Sym "=", m, t]]
     val res = parse_tree smtlib_tree list_param (length param) ctxt
   in
      [write_lemma_header name]
   end |
  write_lemma rwr _ = (@{print}("rwr",rwr);raise WRITE_LEMMA_FROM_DSL_REWRITE ("Could not write rewrite rule to lemma, has wrong form"))
end

local
  fun write_lemmas_h [] _ = [] |
      write_lemmas_h (c::cs) ctxt = (write_lemma c ctxt) @ write_lemmas_h cs ctxt
in 
  fun write_lemmas cs theory_name theory_imports ctxt
    = write_file_header theory_name theory_imports @ write_lemmas_h cs ctxt @ [write_file_footer]
end

end;