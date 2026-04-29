(*  Title:      HOL/CVC/ML/alethe_replay_rare_simplify_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying Alethe proofs for rare-simplify
*)

signature ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
sig
  val rare_rewrite: Alethe_Replay_Methods.alethe_tac_step_args
  val rare_rec_mode: int Config.T
  exception RARE_REPLAY of string
end;

structure Alethe_Replay_RARE_Simplify_Methods: ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
struct

exception RARE_REPLAY of string

(*
0: use lemma & simplify if not possible (default)
1: use only lemma
2: use only simplify
3: use only simplify but add all lemmas to the simpset
4: use lemma for complex cases & and simplify for easy ones
5: use lemma for complex cases & and simplify for easy ones and add all simple lemmas to the simpset (see below but mainly those without lists in them that are not * rules)
6: use only match (and assume_tac for premises)
7: use lemma for complex case & match for simple case
8: use lemma but first try to resolve without instantiation

complex case: lemma includes lists
*)
val rare_rec_mode = Attrib.setup_config_int \<^binding>\<open>rare_rec_mode\<close> (K 0)


(*imports*)
val TRY' = Alethe_Replay_Methods.TRY'
val REPEAT' = Alethe_Replay_Methods.REPEAT'
val simplify_tac = Alethe_Replay_Methods.simplify_tac
val low = SMT_Config.low
val middle = SMT_Config.middle
val high = SMT_Config.high


fun debug_msg ctxt = SMT_Config.alethe_debug_msg ctxt "alethe_replay_rare"
fun debug_msg_tac' ctxt verbosity str = K (SMT_Config.alethe_debug_msg_tac ctxt "alethe_replay_rare" verbosity str)

(*Tactics for experiments*)
fun try_auto_solo ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ => TRY' (K (Clasimp.auto_tac ctxt)))

fun dest_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = t
  | dest_prop t = t


(* Evaluation of constants *)
(* Any additional lemmas should be added to cvc_evaluate or cvc_evaluate_bv*)

fun evaluate_tac ctxt _ =
  debug_msg_tac' ctxt high "evaluate start" THEN'
  TRY' (Code_Simp.dynamic_tac ctxt)
  THEN' debug_msg_tac' ctxt high "evaluate after Code_Simp.dynamic_tac"
  THEN' TRY' (Lin_Arith.tac ctxt)
  THEN' debug_msg_tac' ctxt high "evaluate after Linarith"
  THEN' TRY' (simplify_tac ctxt (
    (Named_Theorems.get ctxt @{named_theorems cvc_evaluate}) 
  @ (Named_Theorems.get ctxt @{named_theorems cvc_evaluate_bv})
  ))
  THEN' debug_msg_tac' ctxt high "evaluate after unfolding cvc_evaluate lemmas"

(*We have to abstract the terms because foralls in if then elses. The code generator cannot
deal with those. This unfortunately includes adding all operators.*)
fun try_evaluate ctxt t =
  SMT_Replay_Methods.prove_abstract' ctxt t evaluate_tac
    (SMT_Replay_Methods.abstract_for_code_eval ctxt (dest_prop t))

(*The simpset is cleared after each step which might not be what we want*)
fun try_simp_tac thms ctxt  =
     TRY' (K (HEADGOAL (simplify_tac ctxt thms)))
     THEN' debug_msg_tac' ctxt high "try_simp after (maybe) trying out a subset of lemmas"
     THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rare_simplify_temp})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt @{thms arith_simps alethe_minus_simplify})))  
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
     THEN' TRY' (K (Clasimp.auto_tac ctxt))

fun try_simp ctxt t thms = SMT_Replay_Methods.prove ctxt t (fn ctxt => try_simp_tac thms ctxt)

fun try_match_tac thms ctxt  =
     (K (HEADGOAL (match_tac ctxt thms)))
     THEN' debug_msg_tac' ctxt high "try_match after applying lemma"
     THEN' TRY' (K (unfold_tac ctxt @{thms NO_MATCH_def}))
     THEN' debug_msg_tac' ctxt high "try_match after applying lemma"

     THEN' (K (ALLGOALS (assume_tac ctxt)))

     THEN' (try_simp_tac [] ctxt)

fun try_match ctxt t thms = SMT_Replay_Methods.prove ctxt t (fn ctxt => try_match_tac thms ctxt)


(* Rare rewrite reconstruction *)


fun normalize_list_arg (Const (\<^const_name>\<open>Dsl_Nary_Ops.cvc_ListVar.ListVar\<close>, _) $ Const (\<^const_name>\<open>List.Nil\<close>, _)) t =
  (case try hd (dest_Type t |> snd) of
    NONE => @{term "ListVar (List.Nil::dummy List.list) :: dummy cvc_ListVar"} |
    SOME (t') => 
      Const (\<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[t']) --> Type(\<^type_name>\<open>cvc_ListVar\<close>, [t']))
      $ Const (\<^const_name>\<open>List.Nil\<close>, Type(\<^type_name>\<open>List.list\<close>,[t']))
  )
| normalize_list_arg a _ = a

fun rewrite_lemma_inst ctxt lemma [] [] = lemma
  (*| rewrite_lemma_inst _ [] (_::_) =
              raise RARE_REPLAY("Too few arguments for RARE rewrite " ^ rewrite_name)
  | rewrite_lemma_inst _ _ [] =
              raise RARE_REPLAY("Too many arguments for RARE rewrite " ^ rewrite_name)*)
  | rewrite_lemma_inst ctxt lemma (a :: args') (t :: typs') =
  let
    val _ = debug_msg ctxt high (fn () => @{print} ("(args',typs')",(args',typs')));
    val _ = debug_msg ctxt high (fn () => @{print} ("lemma",lemma));

    val rec_lemma = rewrite_lemma_inst ctxt lemma args' typs' (*TODO: Is it faster to instantiate with all types at once? This is good for testing though*)
    val _ = debug_msg ctxt high (fn () => @{print} ("One instantiation further:",rec_lemma));
    val _ = debug_msg ctxt high (fn () => @{print} ("a before:",a));
    val _ = debug_msg ctxt high (fn () => @{print} ("t before:",t));

    val a_normalized = normalize_list_arg a t |> Thm.cterm_of ctxt |> SOME |> single

    val _ = debug_msg ctxt high (fn () => @{print} ("a_normalized:",a_normalized));
    val res = Drule.infer_instantiate' ctxt a_normalized rec_lemma
    val _ = debug_msg ctxt high (fn () => @{print} ("res:",(res)));

   in res  end
  | rewrite_lemma_inst ctxt lemma xs ys = lemma


      
fun instantitate_lemma ctxt args lemma =
let
  fun get_types lemma = map snd (rev (Term.add_vars (Thm.full_prop_of lemma) []))
  val args_types_from_lemma = rev (get_types lemma) (*TODO: get rid of revs if possible*)
  val args_terms =  rev (Const ("Groups.zero_class.zero",@{typ int}) :: args) (*The extra term is for the dummy argument we need to add the expected order to the arguments*)
  val _ = debug_msg ctxt high (fn () => @{print} ("Argument types extracted from lemma",args_types_from_lemma));
  val _ = debug_msg ctxt high (fn () => @{print} ("Arguments ",args_terms));
in rewrite_lemma_inst ctxt lemma args_terms args_types_from_lemma end

fun dsl_tac_initialize rewrite_name args ctxt t prems =
  let
    val rare_mode = (Config.get ctxt rare_rec_mode)

    val _ = debug_msg ctxt high (fn () => @{print} ("rare_rec_mode " ^ Int.toString rare_mode))
    val all_rare_rewrite_lemmas = (Named_Theorems.get ctxt @{named_theorems rare_rewrites_all})
    val simple_rare_rewrite_lemmas = (Named_Theorems.get ctxt @{named_theorems rare_rewrites_simple})
    val simple_rare_rewrites_names = [
      "arith_elim_gt", "arith_elim_lt", "arith_elim_int_gt",
      "arith_elim_int_lt", "arith_elim_leq", "arith_leq_norm",
      "arith_geq_tighten", "arith_geq_norm1_int", "arith_eq_elim_int",
      "bool_double_not_elim", "bool_not_true", "bool_not_false",
      "bool_eq_true", "bool_eq_false", "bool_eq_nrefl",
      "bool_impl_false1", "bool_impl_false2", "bool_impl_true1",
      "bool_impl_true2", "bool_impl_elim", "bool_dual_impl_eq",
      "bool_implies_de_morgan", "bool_xor_refl", "bool_xor_nrefl",
      "bool_xor_false", "bool_xor_true", "bool_xor_comm",
      "bool_xor_elim", "bool_not_xor_elim", "bool_not_eq_elim1",
      "bool_not_eq_elim2", "ite_neg_branch", "ite_then_true",
      "ite_else_false", "ite_then_false", "ite_else_true",
      "ite_then_lookahead_self", "ite_else_lookahead_self", "ite_then_lookahead_not_self",
      "ite_else_lookahead_not_self", "ite_expand", "bool_not_ite_elim",
      "ite_true_cond", "ite_false_cond", "ite_not_cond",
      "ite_eq_branch", "ite_then_lookahead", "ite_else_lookahead",
      "ite_then_neg_lookahead", "ite_else_neg_lookahead",
      "eq_refl", "eq_symm", "eq_cond_deq",
      "eq_ite_lift", "distinct_binary_elim",
      "ite_eq", "distinct_binary_elim", "bool_not_eq_false",
      "arith_geq_norm1_real", "arith_eq_elim_real",
      "arith_to_int_to_real", "arith_int_eq_conflict",
      "arith_int_geq_tighten", "arith_geq_ite_lift",
      "arith_leq_ite_lift"
      ]
      val is_simple = List.exists (fn x => x = rewrite_name) simple_rare_rewrites_names 
  in
    if rare_mode = 2 (*Use only simplify*)
    then try_simp ctxt t []
    else if rare_mode = 3 (*Use only simplify but add all lemmas to the simpset*)
    then try_simp ctxt t all_rare_rewrite_lemmas
    else if rare_mode = 4 andalso is_simple (*Use lemma for complex cases & and simplify for easy ones *)
    then try_simp ctxt t []
    else if rare_mode = 5 andalso is_simple (*Use lemma for complex cases & and simplify for easy ones and add all simple lemmas to the simpset (see below but mainly those without lists in them that are not * rules) *)
    then try_simp ctxt t simple_rare_rewrite_lemmas
    else if rare_mode = 6 (*Use only match (and assume_tac for premises)*)
    then try_match ctxt t simple_rare_rewrite_lemmas
    else if rare_mode = 7 andalso not is_simple (*7: use lemma for complex case & match for simple case *)
    then try_match ctxt t simple_rare_rewrite_lemmas
    else
      (case rewrite_name of (*cheating: hardcoding some common rules, saving around 3ms each time TODO: Should be measured again*)
        "bool_double_not_elim" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt [@{thm not_not}])
       | "arith_to_int_to_real" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt (CVC5_Rare.rare_rule (Context.Proof ctxt) ("rewrite_arith_to_int_to_real2")))
       | "eq_refl" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt [@{lemma \<open>(a=a) = True\<close> by blast}])
       | "eq_symm" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt @{thms eq_commute})
       | "distinct_false" => SMT_Replay_Methods.prove ctxt t (fn _ =>
         try_simp_tac [] ctxt)
       | _ => 
          (case (CVC5_Rare.rare_lookup (Context.Proof ctxt) ("rewrite_" ^ rewrite_name)) of
           NONE  => 
             if rare_mode = 1 orelse (List.exists (fn x => x = rare_mode) [4,5,7,8]) then
               let
                val _ = debug_msg ctxt high (fn () => @{print} ("undeclared RARE rule: " ^ rewrite_name ^ ". Use cvc5_rare \"full_name\"."))
               in raise RARE_REPLAY("could not find lemma for rare rewrite" ^ rewrite_name) end
              else try_simp ctxt t []   
           | (SOME rewrite_lemmas) => (*lemma found and we are supposed to use it*)
              let
                val _ = debug_msg ctxt middle (fn () => @{print} ("Lemmas corresponding to the current rewrite rule",rewrite_lemmas));

                val inst_lemmas = map_filter (try (instantitate_lemma ctxt args)) rewrite_lemmas
                val _ = debug_msg ctxt middle (fn () => @{print} ("Instantiated lemmas",inst_lemmas));

                val cvc_list_defs = @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_both_Singleton
                  cvc_list_right_Cons cvc_list_left_Cons cvc_list_both_Cons
                  cvc_list_both_Cons_0 cvc_list_both_Cons_1 NO_MATCH_def}
                val inst_lemmas_without_list = 
                  map (Local_Defs.unfold ctxt (cvc_list_defs @ (Named_Theorems.get ctxt @{named_theorems smt_rewrite_lemma_simplify}))) inst_lemmas

                (*This is done to get rid of the bogus term used to enforce the expected ordering on the arguments*)
                val inst_lemmas_without_true
                  = map (Tactic.rule_by_tactic ctxt (resolve_tac ctxt [@{thm TrueI}] 1)) inst_lemmas_without_list
                val _ = debug_msg ctxt middle (fn () => @{print} ("Instantiated lemmas without custom list operators",inst_lemmas_without_true));
                val _ = debug_msg ctxt middle (fn () => @{print} ("nr of viable instantiated lemmas",length inst_lemmas_without_true));

                val cvc_evaluate_thms = Named_Theorems.get ctxt @{named_theorems cvc_evaluate}
                fun debug_msg_tac'' ctxt verbosity str = debug_msg_tac' ctxt verbosity ("rare_rewrite: " ^ str)

                fun try_lemma_i i = 
                (fn t => (SMT_Replay_Methods.prove ctxt t (fn ctxt =>
                  debug_msg_tac'' ctxt high "start"
                  (*THEN' K (print_tac ctxt "start")*)
                  THEN' (
                   (
                     CHANGED_GOAL
                       (if rare_mode = 8
                        then  (*This would also need to work on the premises etc. kind of annoying*)
                              (CHANGED_GOAL (EqSubst.eqsubst_tac ctxt [0] rewrite_lemmas)
                              (*THEN' K (print_tac ctxt "trying to use lemma without instantiation")*)
                              THEN' ((match_tac ctxt @{thms NO_MATCH_def NO_MATCH_cong}))
                              (*THEN' K (print_tac ctxt "here")*))
                            ORELSE' (EqSubst.eqsubst_tac ctxt [0] [nth inst_lemmas_without_true 0] )
                        else (EqSubst.eqsubst_tac ctxt [0] [nth inst_lemmas_without_true 0] (*TODO: Use lemma i*))
                    (*THEN' K (print_tac ctxt "after applying lemma")*)

                     THEN' debug_msg_tac'' ctxt high "applied lemma"
                     THEN' REPEAT' (resolve_tac ctxt prems)
                     THEN' TRY' (resolve_tac ctxt [@{thm refl}])))
                  ORELSE' (*TODO: This is wrong but I don't get how to change it. I want a UNLESS changed*)
                   (if rare_mode = 1 orelse (List.exists (fn x => x = rare_mode) [4,5,7])
                   then (let val _ = @{print}("lemma,goal",(nth inst_lemmas_without_true 0,Thm.cterm_of ctxt t)) in 
                   (debug_msg_tac'' ctxt high "could not apply lemma" THEN' (K no_tac) (* This won't work: raise RARE_REPLAY("Lemmas could not be used to discharge rewrite rule."*)) end)
                   else ((*K (print_tac ctxt "lemmas could not be used, continue to simplify") THEN'*) try_simp_tac [] ctxt THEN' K (print_tac ctxt "after simplification")))
                  )
                  THEN_ALL_NEW (
                    debug_msg_tac'' ctxt high "trying to discharge assumption of RARE lemma"
                    THEN' TRY' (simplify_tac ctxt cvc_evaluate_thms THEN' debug_msg_tac'' ctxt high "simplifed goal with cvc_evaluate")
                    THEN' TRY'
                    (simplify_tac ctxt cvc_evaluate_thms
                    THEN' debug_msg_tac'' ctxt high "simplifed goal with cvc_evaluate and arith_mult_poly_norm_cvc5")
                    THEN' TRY' (Code_Simp.dynamic_tac ctxt THEN' debug_msg_tac'' ctxt high "applied code evaluator") (*slowest method, so at the end*)
                    )
                  THEN' debug_msg_tac'' ctxt high "should be solved now"
                ))) t
             in
               if length inst_lemmas_without_true > 0
               then (if (List.exists (fn x => x = rare_mode) [0,1,4,5,7,8]) 
                then try_lemma_i 0
                else raise ERROR("Rule could not be used") )
               else (if rare_mode = 0 then try_simp ctxt t [] else raise ERROR("Rule could not be instantiated") )
             end))
end



local 
  fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
in 

  fun rare_rewrite ctxt (th : thm list) (x:: args) t =
    let
      val rewrite_name = String.map (fn #"-"  => #"_" | x => x) (HOLogic.dest_string x)
    in
      (debug_msg ctxt low (fn () => @{print} "Found rare rewrite " ^ rewrite_name);
      dsl_tac_initialize rewrite_name args ctxt t th)
      handle (RARE_REPLAY msg) => raise (SMT_Failure.SMT (SMT_Failure.Replay("rare-rewrite",ERROR msg)))
    end
  | rare_rewrite ctxt _ args _ =
      (SMT_Config.verbose_msg ctxt (pretty ("No dsl rule found, try to simplify" ^
         List.foldr op^ "" (map ML_Syntax.print_term args))) [];
       raise (SMT_Failure.SMT (SMT_Failure.Replay("rare-rewrite",ERROR "could not find lemma for rare rewrite ")))
    (*try_simp ctxt t*))


  fun evaluate ctxt _ _  = try_evaluate ctxt
end

val rules = [
   ("rare_rewrite", rare_rewrite),
   ("evaluate",evaluate)
]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Alethe_Replay_Methods.declare_alethe_rule) rules))

end
