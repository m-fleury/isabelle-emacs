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


fun hackish_string_of_term ctxt =
 Print_Mode.setmp [] (Syntax.string_of_term ctxt)
  #> YXML.content_of

fun hackish_string_of_type ctxt =
 Print_Mode.setmp [] (Syntax.string_of_typ ctxt)
  #> YXML.content_of

fun generalize_types ctxt t =
  let
    val erase_types = map_types (fn _ => dummyT)
    (* use schematic type variables *)
    val ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern
    val infer_types = singleton (Type_Infer_Context.infer_types ctxt)
  in
     t |> erase_types |> infer_types
  end


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

fun write_lemma_header name = ["named_theorems rewrite_" ^ name ^ " \<open>automatically_generated\<close>\n\n"] @ ["lemma [rewrite_" ^ name ^ "]:\n"]
fun write_fixes pars = 
let
  fun write_params [] = "" |
      write_params [p] =  p |
      write_params (p::ps) = p ^ " and " ^ write_params ps
in
  ["  fixes " ^ write_params pars  ^ "\n"]
end

fun write_shows goal =
let 
  (*TODO: check if starts with forall first*)
  fun wth_forall ("."::" "::xs) = xs | 
      wth_forall ("."::xs) = xs | 
      wth_forall (_::xs) = ((*@{print}("c",c);*) wth_forall xs) 
  val res = implode (wth_forall (raw_explode goal))
in
 ["  shows \"" ^ res ^ "\"\n" ]
end

val write_auto = ["  by auto\n\n"]



(*fun write_shows_wth_assump pars ass match target ctxt
   =  ["  assumes \"" ^ get_term ass pars ctxt ^ "\"\n" ^
"  shows \"((" ^ get_term match pars ctxt ^ ") = (" ^ get_term target pars ctxt ^ "))\"\n" ] *)
(*val write_auto = ["  by auto\n\n"]*)
(*fun write_auto pars name =
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
end*)


(*(*("res",
 Const ("HOL.All", "(??'a word \<Rightarrow> bool) \<Rightarrow> bool") $
   Abs ("xs", "??'a word",
     Const ("HOL.All", "(??'b word \<Rightarrow> bool) \<Rightarrow> bool") $
       Abs ("s", "??'b word",
         Const ("HOL.All", "(... word ... bool) \<Rightarrow> bool") $
           Abs ("ys", "??'c word",
             Const ("HOL.All", "...") $ Abs ("i", ..., ...))))) (line 259 of "~~/src/HOL/Tools/SMT/cvc5_dsl_rewrites/rewrites_to_lemma.ML") 
("param",
 [S [Sym "xs", S [Sym "ListVar", S [Sym "?BitVec"]]], S [Sym "s", Sym "?BitVec"], S [Sym "ys", S [Sym "ListVar", S [Sym "?BitVec"]]],
  S [Sym "i", Sym "Int"], S [Sym "j", Sym "Int"],
  S [Sym "k", Sym "Int"]])*)*)


fun
get_pars ctxt (Const ("HOL.All", _) $ (Abs (new_par_name, new_par_type, xs)))
 ((SMTLIB.S [SMTLIB.Sym org_par_name, SMTLIB.S [SMTLIB.Sym "ListVar", SMTLIB.S [SMTLIB.Sym org_par_type]]]) :: ys) pars = 
  let 
val _ = @{print}("ListVar detected in get_pars")

val _ = @{print}("  new_par_name",new_par_name)
val _ = @{print}("  new_par_type",new_par_type)
val _ = @{print}("  org_par_name",org_par_name)
val _ = @{print}("  org_par_type",org_par_type)

(*TODO: Test for ? or something in case this is not a bitvec but still parametric*)
    val par = 
        (if (not (org_par_type = "?BitVec"))
         then 
           let
            val term = SMTLIB_Proof.type_of (empty_context ctxt Symtab.empty Symtab.empty) ( SMTLIB.S [SMTLIB.Sym "ListVar", SMTLIB.S [SMTLIB.Sym org_par_type]]) 
            val par_type_str = hackish_string_of_type ctxt term
           in new_par_name ^ "::\"" ^ par_type_str ^ "\"" end
         else
           let (*TODO*)
            val par_type_str = hackish_string_of_type ctxt new_par_type
           in new_par_name ^ "::\"" ^ par_type_str ^ "\"" end)

val _ = @{print}("  Added par",par)

  in
    get_pars ctxt xs ys (par :: pars)
  end |

 get_pars ctxt
 (Const ("HOL.All", _) $ (Abs (new_par_name, new_par_type, xs)))
 ((SMTLIB.S [SMTLIB.Sym org_par_name, SMTLIB.Sym org_par_type]) :: ys) pars = 
  let 
  val _ = @{print}("org_par_type",org_par_type)
  val _ = @{print}("org_par_name",org_par_name)
  val _ = @{print}("new_par_name",new_par_name)

    val par = 
        (if (org_par_type = "?BitVec")
         then 
            let (*Take ??a from new_par_type and make a word of length ??a *)
            val _ = @{print}("new_par_type",new_par_type)

            (*val new_typ = Type((hackish_string_of_type ctxt new_par_type)^"::len word",[])*)
            val new_typ = Type("Word.word",[new_par_type])

            val par_type_str = hackish_string_of_type ctxt new_typ
            val new_par_type_str = if hd (raw_explode par_type_str) = "?" 
                                   then (implode (tl (tl (raw_explode par_type_str))))
                                   else par_type_str
           in new_par_name ^ "::\"" ^ new_par_type_str ^ "\"" end (*TODO: Only cut first two digits if they are question marks*)
         else
         if (org_par_type = "?")
         then 
            let (*Take ??a from new_par_type and make a word of length ??a *)
               val _ = @{print}("new_par_type",new_par_type)
               val par_type_str = hackish_string_of_type ctxt new_par_type
               val new_par_type_str = if hd (raw_explode par_type_str) = "?" 
                                   then (implode (tl (tl (raw_explode par_type_str))))
                                   else par_type_str
           in new_par_name ^ "::\"" ^ new_par_type_str ^ "\"" end
         else
            let
            val term = SMTLIB_Proof.type_of (empty_context ctxt Symtab.empty Symtab.empty) (SMTLIB.Sym org_par_type) 
            val par_type_str = hackish_string_of_type ctxt term
            in new_par_name ^ "::\"" ^ par_type_str ^ "\"" end  )
  in
    get_pars ctxt xs ys (par :: pars)
  end |

  get_pars ctxt xs ys pars = (@{print}("Qword",xs);@{print}("werwerer",ys);pars)

(*Not that happy with this, maybe do this in smtlib_proof after all?*)


(* Const ("HOL.eq", "bool \<Rightarrow> bool \<Rightarrow> bool") $
   (Const ("HOL.conj", "bool \<Rightarrow> bool \<Rightarrow> bool") $ Free ("xs", "_") $
     (Const ("HOL.conj", "bool \<Rightarrow> bool \<Rightarrow> bool") $ Free ("w", "_") $
       (Const ("HOL.conj", "bool \<Rightarrow> bool \<Rightarrow> bool") $ Free ("ys", "_") $
         (Const ("HOL.conj", "bool \<Rightarrow> bool ... bool") $
           (Const ("HOL.Not", "... ... ...") $ Free ("w", "...")) $ Free ("zs", "..."))))) $
   Const ("HOL.False",
          "bool")*)

fun mk_nary1 ((Const operator) $ (Free (var_name1,typ1)) $ (Free (var_name2,typ2))) lvars =
let 
  val var1_is_in_list = List.find (fn a => var_name1 = a) lvars
  val var2_is_in_list = List.find (fn a => var_name2 = a) lvars

 fun neutral_for_operator "HOL.conj" = Const (\<^const_name>\<open>HOL.True\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "HOL.disj" = Const (\<^const_name>\<open>HOL.False\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "Groups.plus_class.plus" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Orderings.ord_class.less_eq" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Groups.times_class.times" = Const (\<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>) |
      (*neutral_for_operator "Smtlib_String.cvc_re_concat" = Free ("{''''}", \<^typ>\<open>RegLan\<close>) | (*TODO*)*)
      neutral_for_operator "Smtlib_String.cvc_str_concat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) |
      neutral_for_operator "Word.word_cat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) | (*TODO*)
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
  (new_operator $ (Free (var_name1,typ1)) $ (Free (var_name2,typ2)))
end
| mk_nary1 ((Const operator) $ (Free (var_name1,typ1)) $ l2) lvars =
 let
   val var1_is_in_list = List.find (fn a => var_name1 = a) lvars
   val new_operator =
     if var1_is_in_list = NONE
     then Const operator
     else Const (\<^const_name>\<open>cvc_list_left\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>)
         $ Const operator
 in 
  (new_operator $ (Free (var_name1,typ1)) $ (mk_nary1 l2 lvars))
 end
| mk_nary1 ((Const operator) $ l1 $ (Free (var_name2,typ2))) lvars =
 let
   val var2_is_in_list = List.find (fn a => var_name2 = a) lvars
   val new_operator =
     if var2_is_in_list = NONE
     then Const operator
     else Const (\<^const_name>\<open>cvc_list_right\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>)
         $ Const operator
 in 
  (new_operator $ (mk_nary1 l1 lvars) $ (Free (var_name2,typ2)))
 end
| mk_nary1 (l1 $ l2) lvars = (mk_nary1 l1 lvars) $ (mk_nary1 l2 lvars)
| mk_nary1 l lvars = l








fun mk_nary ((Const operator) $ (Bound m1) $ (Bound m2)) lvars n =
let
val _ = @{print}("lvars",lvars)
val _ = @{print}("m1",m1)
val _ = @{print}("m2",m2)

 val var1_is_in_list = List.find (fn a => m1 = a) lvars
 val var2_is_in_list = List.find (fn a => m2 = a) lvars

 fun neutral_for_operator "HOL.conj" = Const (\<^const_name>\<open>HOL.True\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "HOL.disj" = Const (\<^const_name>\<open>HOL.False\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "Groups.plus_class.plus" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Orderings.ord_class.less_eq" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Groups.times_class.times" = Const (\<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>) |
      (*neutral_for_operator "Smtlib_String.cvc_re_concat" = Free ("{''''}", \<^typ>\<open>RegLan\<close>) | (*TODO*)*)
      neutral_for_operator "Smtlib_String.cvc_str_concat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) |
      neutral_for_operator "Word.word_cat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) | (*TODO*)
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
  (new_operator $ (Bound m1) $ (Bound m2))
end |
mk_nary ((Const operator) $ (Bound m1) $ l2) lvars n =
let 
val _ = @{print}("lvars4",lvars)
val _ = @{print}("m1",m1)
val _ = @{print}("l2",l2)

 val var1_is_in_list = List.find (fn a => m1 = a) lvars
 val new_operator =
    if var1_is_in_list = NONE
    then Const operator
    else Const (\<^const_name>\<open>cvc_list_left\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>)
        $ Const operator
 in 
  (new_operator $ (Bound m1) $ (mk_nary l2 lvars n))
 end |
mk_nary ((Const operator) $ l1 $ (Bound m2)) lvars n =
let
val _ = @{print}("lvars3",lvars)
val _ = @{print}("m2",m2)
val _ = @{print}("l1",l1)

 val var2_is_in_list = List.find (fn a => m2 = a) lvars
  val new_operator =
    if var2_is_in_list = NONE
    then Const operator
    else Const (\<^const_name>\<open>cvc_list_right\<close>, \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>)
         $ Const operator
in  
  (new_operator $ (mk_nary l1 lvars n) $ (Bound m2))
 end

 |(* Abs ("xs", "_ word cvc_ListVar",*)
mk_nary (Abs (name, typ,l2)) lvars n =
let
val _ = @{print}("name",name)
val _ = @{print}("Increase n ",n + 1)
val x = dest_Type typ
val _ = @{print}("Test type XXX ",x)

val new_lvars = if (fst (dest_Type typ) = "Dsl_Nary_Ops.cvc_ListVar") then (@{print}("Add it to lvars with n= ",n)
;(n::lvars)) else  (@{print}("Don't add to lvars with n= ",n)
;lvars)
in
 (Abs (name, typ,mk_nary l2 new_lvars (n+1)))
end | (*TODO: Add name to list here if listvar*)
mk_nary (l1 $ l2) lvars n = (@{print}("lvars1",lvars);@{print}("l1",l1);@{print}("l2",l2);(mk_nary l1 lvars n) $ (mk_nary l2 lvars n)) |
mk_nary l1 lvars n = l1




(* Const ("HOL.eq", "bool \<Rightarrow> bool \<Rightarrow> bool") $ (Const ("HOL.eq", "??'a \<Rightarrow> ??'a \<Rightarrow> bool") $ Bound 2 $ Bound 3) $
   (Const ("HOL.eq", "??'b \<Rightarrow> ??'b \<Rightarrow> bool") $ Bound 0 $
     Bound 1)*)


fun write_body res param ctxt =
let
  val str_res = hackish_string_of_term ctxt res
  val _ = @{print}("str_res",str_res)
  val _ = @{print}("res",res)
  val _ = @{print}("param",rev param)

  fun wth_forall ("."::" "::xs) = xs |
      wth_forall ("."::"\n"::" "::" "::" "::xs) = xs |
      wth_forall ("."::xs) = xs | 
      wth_forall (_::xs) = wth_forall xs |
      wth_forall [] = []
  fun write_params [] = "" |
      write_params [p] =  p |
      write_params (p::ps) = p ^ " and " ^ write_params ps

  val pars = get_pars ctxt res (rev param) [] |> write_params
  val _ = @{print}("pars", pars)
  val goal = raw_explode str_res |> wth_forall |> implode
in 
  ["  fixes " ^ pars  ^ "\n"] @ ["  shows \"" ^ goal ^ "\"\n" ]
end


local

 fun write_tree smtlib_tree2 param ctxt =
  let
    (*val _ = @{print}("smtlib_tree",smtlib_tree)*)
    (*val term = empty_context ctxt Symtab.empty Symtab.empty |> SMTLIB_Proof.term_of smtlib_tree*)
    val cx = empty_context ctxt Symtab.empty Symtab.empty
    val term2 = SMTLIB_Proof.term_of smtlib_tree2 cx

    (*val _ = @{print}("term",fst term)
    val _ = @{print}("term",snd term)*)
    val _ = @{print}("term2",fst term2)


    (*val nary = mk_nary (fst term) [] 0*)
    val nary2 = mk_nary1 (fst term2) ["xs","ys","zs"]

    (*val _ = @{print}("nary",nary)*)
    val _ = @{print}("nary2",nary2)

    val str_res = hackish_string_of_term ctxt nary2
    val _ = @{print}("str_res",str_res)

(*  "\<forall>(s1::char list) (s2::char list cvc_ListVar)\n   (s3::char list cvc_ListVar) (t1::char list) (t2::char list cvc_ListVar)\n   t3::char list cvc_ListVar.\n   \<not> cvc_list_both (=) (PutInNeutral::bool) s1 t1 \<and>\n   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>\n   (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat s1 s2)\n     s3 =\n    smtlib_str_concat (cvc_list_left smtlib_str_concat t1 t2) t3) =\n   False") (line 314 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/cvc5_dsl_rewrites/rewrites_to_lemma.ML") 
*)
val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))

fun dest_var cx (SMTLIB.S [SMTLIB.Sym name, ty]) = (name, (desymbolize name, type_of cx ty))
  | dest_var cx (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym "ListVar", ty]) (*TODO*)
        = (name, (desymbolize name, type_of cx (SMTLIB.S [SMTLIB.Sym "cvc_ListVar", ty])))
  | dest_var _ v = raise SMTLIB_PARSE ("bad SMT quantifier variable format", v)


fun quant vars body cx =
  let val vs = map (dest_var cx) vars
      (*val _ = @{print} "In quant"
      val _ = @{print} "str_of tree quant "
      val _ = @{print} "Until here "
      val _ = (SMTLIB.str_of (SMTLIB.S vars))
      val _ = "but not done?"*)
  in
    cx
    |> with_bindings (map (apsnd (Term o Free)) vs) body
    |>> fold_rev (fn (_, (n, T)) => fn t => HOLogic.mk_all (n, T, t)) vs
  end

  val test = quant param (fn x => (nary2, snd term2)) cx
    val _ = @{print}("test",test)



    val term_gen_types = (fst test) |> generalize_types ctxt
    val _ = @{print}("term_gen_types",term_gen_types)

  in
   term_gen_types
  end

(*

fixes x::'a word
assumes LENGTH('a) = 5 



n::'a \<rightarrow> n::int \<rightarrow> n::int
n::'a \<rightarrow> n::?Bitvec \<longrightarrow> 'a word
n::'a \<longrightarrow> n::? \<longrightarrow> 'a 

*)



in 
fun write_lemma (Rewrite_Rule ((Rule_Type DEFINE_RULE)::(Rule_Name name)::[Par param, Match m, Target t])) ctxt =
  let
    val smtlib_tree = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (rev param), SMTLIB.S [SMTLIB.Sym "=", m, t]]
    val _ = @{print}("smtlib_tree",smtlib_tree)
    val smtlib_tree2 = SMTLIB.S [SMTLIB.Sym "=", m, t]

    val res = write_tree smtlib_tree2 param ctxt
  in 
    [write_lemma_header name, write_body res param ctxt, write_auto]
  end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_COND_RULE)::(Rule_Name name)::[Par param, Precondition ass, Match m, Target t])) ctxt =
    let
      val smtlib_tree = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (rev param),
                        SMTLIB.S [SMTLIB.Sym "implies", ass, SMTLIB.S [SMTLIB.Sym "=", m, t]]]
      val smtlib_tree2 = SMTLIB.S [SMTLIB.Sym "implies", ass, SMTLIB.S [SMTLIB.Sym "=", m, t]]
      val res = write_tree smtlib_tree2 param ctxt
    in 
       [write_lemma_header name, write_body res param ctxt]
    end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_STAR_RULE)::(Rule_Name name)::[Par param, Context_Expr context_expr, Match m, Target t])) ctxt =
    let (*TODO*)
      val smtlib_tree = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S param, SMTLIB.S [SMTLIB.Sym "=", m, t]]
      val smtlib_tree2 = SMTLIB.S [SMTLIB.Sym "=", m, t]

      val res = write_tree smtlib_tree2 param ctxt
    in (*TODO*)
       [write_lemma_header name, write_body res param ctxt]
    end |
    write_lemma rwr ctxt = 
let val _ = @{print}("rwr",rwr)
in
raise WRITE_LEMMA_FROM_DSL_REWRITE ("Could not write rewrite rule to lemma, has wrong form" ) (*^ PARSE_REWRITE.to_str rwr)*)
end
end

local
  fun write_lemmas_h [] _ = [] |
      write_lemmas_h (c::cs) ctxt = (write_lemma c ctxt) @ write_lemmas_h cs ctxt
in 
  fun write_lemmas cs theory_name theory_imports ctxt
    = write_file_header theory_name theory_imports @ write_lemmas_h cs ctxt @ [write_file_footer]
end

end;