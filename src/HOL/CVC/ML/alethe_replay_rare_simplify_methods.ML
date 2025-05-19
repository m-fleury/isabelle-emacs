(*  Title:      HOL/CVC/ML/alethe_replay_rare_simplify_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying Alethe proofs for rare-simplify
*)

signature ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
sig
  val rare_rewrite: Alethe_Replay_Methods.alethe_tac_step_args
  val rare_rec_mode: int Config.T
  val arith_poly_norm : Proof.context -> term -> thm
  exception RARE_REPLAY of string
end;

structure Alethe_Replay_RARE_Simplify_Methods: ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
struct

exception RARE_REPLAY of string

(*
0: use lemma & simplify if not possible
1: use only lemma
2: use only simplify
*)
val rare_rec_mode = Attrib.setup_config_int \<^binding>\<open>rare_rec_mode\<close> (K 0)


val TRY' = Alethe_Replay_Methods.TRY'
val simplify_tac = Alethe_Replay_Methods.simplify_tac

fun debug_msg ctxt = SMT_Config.alethe_debug_msg ctxt "alethe_replay_rare"
val low = SMT_Config.low
val middle = SMT_Config.middle
val high = SMT_Config.high


(*Tactics for experiments*)
fun try_auto_solo ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ => TRY' (K (Clasimp.auto_tac ctxt)))


fun dest_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = t
  | dest_prop t = t
(* Evaluation of constants *)
(* Any additional lemmas should be added to cvc_evaluate *)

fun evaluate_tac ctxt _ =
  (*K (print_tac ctxt "evaluate 0") THEN'*)

  TRY' (Code_Simp.dynamic_tac ctxt )
  THEN' K (print_tac ctxt "evaluate 1")

  THEN' TRY' (Lin_Arith.tac ctxt)
  THEN' K (print_tac ctxt "evaluate 2")

  THEN' TRY' (simplify_tac ctxt (
    (Named_Theorems.get ctxt @{named_theorems cvc_evaluate}) 
  @ (Named_Theorems.get ctxt @{named_theorems cvc_evaluate_bv})
  )) (*TODO: Discuss there are several possibilities to guard the bvs*)
  THEN' K (print_tac ctxt "evaluate")
THEN' TRY' (Skip_Proof.cheat_tac ctxt)

(*Abstrahieren wegen foralls in if then else. The code generator cannot
deal with this *)
fun try_evaluate ctxt t =
  SMT_Replay_Methods.prove_abstract' ctxt t evaluate_tac
    (SMT_Replay_Methods.abstract_for_code_eval ctxt (dest_prop t))



fun arith_poly_norm ctxt t = 
  let
    fun simplify_tac ctxt thms =
      ctxt
      |> empty_simpset
      |> put_simpset HOL_basic_ss
      |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
      |> (Simplifier.add_cong @{thm if_weak_cong})
      |> (fn ctxt => ctxt
           addsimprocs [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
             @{simproc divide_cancel_numeral_factor}, @{simproc divide_cancel_factor},
             @{simproc intle_cancel_numerals}, @{simproc intless_cancel_numerals}, @{simproc inteq_cancel_numerals},
             @{simproc field_combine_numerals},
             @{simproc ring_le_cancel_numeral_factor},
             @{simproc HOL.NO_MATCH}, @{simproc Numeral_Simprocs.semiring_assoc_fold},
             @{simproc Numeral_Simprocs.field_divide_cancel_numeral_factor},
             @{simproc Numeral_Simprocs.field_eq_cancel_numeral_factor}])
      |> Simplifier.full_simp_tac
    fun simplify_tac_with_background_simp ctxt thms =
      ctxt
      |> (fn ctxt => ctxt addsimps thms)
      |> Simplifier.full_simp_tac
    val tac = (fn _ => fn _ =>
      SOLVED' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_norm}))
        (*if the previous does not solve, use full simplification power with the current content*)
      ORELSE'
        simplify_tac_with_background_simp ctxt (Named_Theorems.get ctxt @{named_theorems field_simps})
        THEN' TRY' (Code_Simp.dynamic_tac ctxt))
  in
  SMT_Replay_Methods.prove_abstract' ctxt t tac
    (SMT_Replay_Methods.abstract_for_poly_norm ctxt (dest_prop t))
  end

fun arith_poly_norm_mult ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    (*K (print_tac ctxt "arith mult 0") THEN'*)

    TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate}) @ (Named_Theorems.get ctxt @{named_theorems arith_mult_poly_norm_cvc5})
      @ (Named_Theorems.get ctxt @{named_theorems field_simps})))
    (*THEN' K (print_tac ctxt "arith mult 1")*)
    THEN' TRY' (Lin_Arith.tac ctxt)
    (*THEN' K (print_tac ctxt "arith mult 2")*)
  )

fun try_arith ctxt t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (*K (print_tac ctxt "arith 0") THEN'*)
   TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate}) @ (Named_Theorems.get ctxt @{named_theorems arith_mult_poly_norm_cvc5})
     @ (Named_Theorems.get ctxt @{named_theorems field_simps})))

  (*THEN' K (print_tac ctxt "arith 1")*)

  THEN' TRY' (Lin_Arith.tac ctxt)
  (*THEN' K (print_tac ctxt "arith 2")*)
  THEN' TRY' (Code_Simp.dynamic_tac ctxt )

  (*THEN' K (print_tac ctxt "arith")*)
 )

(*TODO: Have different method based on theory rewrite is in*)
fun try_simp ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ =>
     TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rare_simplify_temp})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt @{thms arith_simps alethe_minus_simplify})))  
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
     THEN' TRY' (K (Clasimp.auto_tac ctxt))
  )

(* Rare rewrite reconstruction *)
fun dsl_tac_initialize rewrite_name args ctxt t _ =
  let
    val rare_mode = (Config.get ctxt rare_rec_mode)
  in
    if rare_mode = 2
    then try_simp ctxt t
    else
      if is_none (CVC5_Rare.rare_lookup (Context.Proof ctxt) ("rewrite_" ^ rewrite_name))
      then if rare_mode = 0
        then
          let
            val _ = debug_msg ctxt high (fn () => @{print} ("undeclared RARE rule: " ^ rewrite_name ^ ". Use cvc5_rare \"full_name\"."))
          in raise RARE_REPLAY("could not find lemma for rare rewrite"^ rewrite_name) end
        else
          try_simp ctxt t
    else
      (case rewrite_name of (*cheating: hardcoding some common rules, saving around 3ms each time*)
        "bool_double_not_elim" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt [@{thm not_not}])
      | "arith_to_int_to_real" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt (CVC5_Rare.rare_rule (Context.Proof ctxt) ("rewrite_arith_to_int_to_real2")))
      | "eq_refl" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt [@{lemma \<open>(a=a) = True\<close> by blast}])
      | "eq_symm" => SMT_Replay_Methods.prove ctxt t (fn _ =>
          match_tac ctxt @{thms eq_commute})
      | _ =>
        let
          val rewrite_lemma = CVC5_Rare.rare_rule (Context.Proof ctxt) ("rewrite_" ^ rewrite_name) |> try hd |> the
            handle Option.Option => raise RARE_REPLAY ("Found more then one lemma corresponding to RARE rule " ^ rewrite_name)
      
          val get_types = map snd (rev (Term.add_vars (Thm.full_prop_of rewrite_lemma) []))
      
          fun is_list_arg (Const (\<^const_name>\<open>Dsl_Nary_Ops.cvc_ListVar.ListVar\<close>, _) $ Const (\<^const_name>\<open>List.Nil\<close>, _)) = true
            | is_list_arg _ = false
      
          fun instantiate_with_arg a t =
            if is_list_arg a
            then
              let
                val _ = debug_msg ctxt high (fn () => @{print} ("Detected List Argument", a));
                val t' = dest_Type t |> snd |> hd
                val new_a = Const (\<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[t']) --> Type(\<^type_name>\<open>cvc_ListVar\<close>, [t']))
                        $ Const (\<^const_name>\<open>List.Nil\<close>, Type(\<^type_name>\<open>List.list\<close>,[t']))
              in
                single ((SOME o Thm.cterm_of ctxt) new_a)
              end
            else
              single ((SOME o Thm.cterm_of ctxt) a)
      
      
          fun rewrite_lemma_inst [] []  = rewrite_lemma
           | rewrite_lemma_inst [] (_::_)  =
              raise RARE_REPLAY("Too few arguments for RARE rewrite " ^ rewrite_name)
           | rewrite_lemma_inst _ []  =
              raise RARE_REPLAY("Too many arguments for RARE rewrite " ^ rewrite_name)
           | rewrite_lemma_inst (a :: args') (t :: typs') = 
              Drule.infer_instantiate' ctxt (instantiate_with_arg a t) (rewrite_lemma_inst args' typs') 
      
          val inst_lemma = 
            rewrite_lemma_inst (rev args @ [Const ("Groups.zero_class.zero",@{typ int})]) (rev get_types)
          val _ = debug_msg ctxt middle (fn () => @{print} ("Instantiated lemma",inst_lemma));
      
          val cvc_list_defs = @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_both_Singleton
            cvc_list_right_Cons cvc_list_left_Cons cvc_list_both_Cons
            cvc_list_both_Cons_0 cvc_list_both_Cons_1 NO_MATCH_def}
          val inst_lemma_without_list = (Local_Defs.unfold ctxt) cvc_list_defs inst_lemma
      
          (*Should only happen if we have the extra argument*)
          val inst_lemma_without_true
            = Basic_Tactic.rule_by_tactic ctxt (resolve_tac ctxt [@{thm TrueI}] 1) inst_lemma_without_list
          fun REPEAT' tac = fn i => REPEAT (tac i)
      
        in
          (SMT_Replay_Methods.prove ctxt t (fn _ =>
          TRY' (EqSubst.eqsubst_tac ctxt [0] [inst_lemma_without_true])
          THEN_ALL_NEW (
            (*K (print_tac ctxt "debug0") THEN'*)
            SOLVED' (resolve_tac ctxt [@{thm refl}])
            ORELSE' (*K (print_tac ctxt "debug1") THEN' *)
               TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems cvc_evaluate}))
              (*THEN' K (print_tac ctxt "debug3")*)
              THEN' TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems cvc_evaluate}
                @ Named_Theorems.get ctxt @{named_theorems arith_mult_poly_norm_cvc5}))
              THEN' TRY' (Code_Simp.dynamic_tac ctxt) (*slowest method, so at the end*)))
           )
      end)
end



local 
  fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
in 

  fun arith_poly_norm_reconstruct ctxt _ _ t =
    arith_poly_norm ctxt t

  fun rare_rewrite ctxt (th : thm list) (x:: args) t =
    let
      val rewrite_name = String.map (fn #"-"  => #"_" | x => x) (HOLogic.dest_string x)
    in
      ((case rewrite_name of
        "evaluate" =>
          (debug_msg ctxt low (fn () => @{print} "Found evaluate, try to simplify");
          try_evaluate ctxt t)
      | "arith_poly_norm" => arith_poly_norm ctxt t
      | "arith_poly_norm_mult" => arith_poly_norm_mult ctxt t
      | "arith_poly_norm_uminus" => 
          (debug_msg ctxt low (fn () => @{print} "Found arithmetric norm rule, try to normalize");
            try_arith ctxt t)
      | "arith_poly_norm_minus" => 
          (debug_msg ctxt low (fn () => @{print} "Found arithmetric norm rule, try to normalize");
            try_arith ctxt t)
      | _ =>
         (debug_msg ctxt low (fn () => @{print} "Found rare rewrite " ^ rewrite_name);
          dsl_tac_initialize rewrite_name args ctxt t th))
      handle (RARE_REPLAY msg) => raise (SMT_Failure.SMT (SMT_Failure.Replay("rare-rewrite",ERROR msg))))
    end
  | rare_rewrite ctxt _ args _ =
      (SMT_Config.verbose_msg ctxt (pretty ("No dsl rule found, try to simplify" ^
         List.foldr op^ "" (map ML_Syntax.print_term args))) [];
       raise (SMT_Failure.SMT (SMT_Failure.Replay("rare-rewrite",ERROR "could not find lemma for rare rewrite ")))
    (*try_simp ctxt t*))

  fun true_tac ctxt _ _ t = 
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      resolve_tac ctxt @{thms TrueI})
end

val rules = [
   ("rare_rewrite", rare_rewrite),
   ("true", true_tac),
   ("arith_poly_norm", arith_poly_norm_reconstruct)]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Alethe_Replay_Methods.declare_alethe_rule) rules))

end
