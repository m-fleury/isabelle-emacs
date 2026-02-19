(*  Title:      HOL/Tools/SMT/alethe_replay_bv_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Stanford

Proof method for replaying Alethe proofs for bitvector steps.
*)

(*TODO: Had to make this work again quickly and changed all alethe_tac to alethe_tac_step_args. 
This could be changed back but declare_alethe_rule would need to accept rules without arguments*)
signature ALETHE_REPLAY_BV_METHODS =
sig
  val xor_pos1: Alethe_Replay_Methods.alethe_tac
  val xor_pos2: Alethe_Replay_Methods.alethe_tac
  val xor_neg1: Alethe_Replay_Methods.alethe_tac
  val xor_neg2: Alethe_Replay_Methods.alethe_tac

  val bv_bitblast_step_var: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_const: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvand: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvor: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvxor: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvxnor: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvnot: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvadd: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvneg: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvmult: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_extract: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_concat: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvequal: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvult: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitblast_step_bvule: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_aci_simp: Alethe_Replay_Methods.alethe_tac_step_args
  val bv_bitwise_slicing: Alethe_Replay_Methods.alethe_tac_step_args
end;


structure Alethe_Replay_BV_Methods: ALETHE_REPLAY_BV_METHODS =
struct

open SMT_Config
fun debug_msg ctxt = alethe_debug_msg ctxt "alethe_replay_bv_methods"
fun debug_msg_tac' ctxt verbosity str = K (SMT_Config.alethe_debug_msg_tac ctxt "alethe_replay_bv_methods" verbosity str)

val TRY' = Alethe_Replay_Methods.TRY'
val simplify_tac = Alethe_Replay_Methods.simplify_tac
val REPEAT_CHANGED = Alethe_Replay_Methods.REPEAT_CHANGED
val replay_error = Alethe_Replay_Methods.replay_error


(* Bitblasting *)
(* Note: These reconstructions will become much shorter. For debugging reasons and as this is ongoing
   work they are not yet optimized.*)

(* Bitblasting a variable *)
local
  fun prove_bitblast_step_var ctxt _ [] t =
  let         
    (*obtain bitblasted variable*)
    fun find_bbT_var (_ $ (_ $ x $ _)) = x |
        find_bbT_var _ = error ("Bitblasting step (variable) has the wrong form!")
    val bit_blasted_var = find_bbT_var t

    (*instantiate with bitblasted variable*)
    val word_var_rbl_list_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_var_rbl_list}) 0
    val word_var_rbl_list_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [bit_blasted_var]) word_var_rbl_list_lemma

  in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("bv bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_var_rbl_list_lemma_inst]))
      THEN' REPEAT_CHANGED (

        REPEAT_CHANGED (

        (*THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 2 "))*)
         (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))
        (*THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 3"))*)
        THEN' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}))
        (*THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 4"))*)
        THEN' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5}))
        (*THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 5"))*)
        THEN' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists})))
        THEN' (debug_msg_tac' ctxt high ("bv bitblast reconstruction debug 6"))
      )
       THEN' TRY' (Code_Simp.dynamic_tac ctxt)
      THEN' (debug_msg_tac' ctxt high ("bv bitblast reconstruction debug 7"))
      )
      ))
  end
in
  val bv_bitblast_step_var = prove_bitblast_step_var
end

(* Bitblasting a constant *)
local
  fun prove_bitblast_step_const ctxt a b t =
  let
   
    (*obtain bitblasted variable*)
    fun find_bbT_var (_ $ (_ $ x $ (_ $(_ $ xs)))) = (x,xs) |
        find_bbT_var _ = error ("Bitblasting step (const) has the wrong form!")
    val bit_blasted_var = find_bbT_var t

    (*instantiate with bitblasted variable*)
    val bv_reconstruction_const_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_const}) 0

    val bv_reconstruction_const_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_var, snd bit_blasted_var]) bv_reconstruction_const_lemma

  in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("bv bitblast const reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [bv_reconstruction_const_lemma_inst]))
      (*THEN' K (print_tac ctxt ("bv bitblast const reconstruction debug 2"))*)
      THEN' REPEAT_CHANGED (

       REPEAT_CHANGED (
       TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_const_test}))
       THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))))
       THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
       THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs}))))
       THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
       THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
       THEN' (TRY' (simplify_tac ctxt (@{thms monoid_mult_class.power_Suc0_right power_0})))

       THEN' TRY' (assume_tac ctxt)
       THEN' (debug_msg_tac' ctxt high ("bv bitblast const reconstruction debug 5"))
      )
       THEN' TRY' (Code_Simp.dynamic_tac ctxt)
       THEN' (debug_msg_tac' ctxt high ("bv bitblast const reconstruction debug 6"))
)

      ))
  end
in
  val bv_bitblast_step_const = prove_bitblast_step_const
end


(* Bitblasting a bitwise binary operation *)
local
  fun prove_bitblast_step_bitwise_op bitwise_op_lemma ctxt _ _ t =
  let
    (*obtain bitblasted variables*)
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ x) $ (_ $ y)) $ _)) = (x,y) |
        find_bbT_vars _ = error ("Bitblasting step (bitwise operation) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t

    (*instantiate with bitblasted variable*)
    val bitwise_op_lemma =
        nth (Named_Theorems.get ctxt bitwise_op_lemma) 0
        handle Subscript =>  error ("Could not find lemma for bitblasting step (bitwise operation)")
    val bitwise_op_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) bitwise_op_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("bitwise operation bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [bitwise_op_lemma_inst]))
      THEN' (debug_msg_tac' ctxt high ("bitwise operation bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (debug_msg_tac' ctxt high ("bitwise operation bitblast reconstruction debug 3"))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvand = prove_bitblast_step_bitwise_op @{named_theorems word_and_rbl_bvand}
  val bv_bitblast_step_bvor = prove_bitblast_step_bitwise_op @{named_theorems word_or_rbl_bvor}
  val bv_bitblast_step_bvxor = prove_bitblast_step_bitwise_op @{named_theorems word_xor_rbl_bvxor}
  val bv_bitblast_step_bvxnor = prove_bitblast_step_bitwise_op @{named_theorems word_notxor_rbl_bvxnor}
end

(* Bitblasting a bvnot *)

local
  fun prove_bitblast_step_bvnot ctxt _ _ t =
  let
    (*obtain bitblasted variables*) (*TODO: test*)
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ x)) $ _)) = x |
        find_bbT_vars _ = error ("Bitblasting step (bvnot) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t
    (*val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))*)

    (*instantiate with bitblasted variable*)
    val bitwise_op_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_not_rbl_bvnot}) 0
    val bitwise_op_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [bit_blasted_vars]) bitwise_op_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("bitwise operation bvnot bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [bitwise_op_lemma_inst]))
      THEN' (debug_msg_tac' ctxt high ("bitwise operation bvnot bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bitwise operation bvnot bitblast reconstruction debug 3"))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvnot = prove_bitblast_step_bvnot
end



(* Bitblasting a bvadd *)
local
  fun prove_bitblast_step_bvadd ctxt _ _ t =
  let
    (*obtain bitblasted variables*)
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ (_ $ x)) $ (_ $ (_ $ y))) $ _)) = (x,y) |
        find_bbT_vars _ = error ("Bitblasting step (bvadd) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t
    val _ = @{print}("bit_blasted_vars",bit_blasted_vars)

    (*val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))*)

    (*instantiate with bitblasted variable*)
    val word_plus_rbl_bvadd_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd}) 0
    val word_plus_rbl_bvadd_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) word_plus_rbl_bvadd_lemma
    val _ = @{print}("word_plus_rbl_bvadd_lemma_inst",word_plus_rbl_bvadd_lemma_inst)
   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      K (print_tac ctxt ("bvadd bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_plus_rbl_bvadd_lemma_inst]))
      THEN' (debug_msg_tac' ctxt high ("bvadd bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
           (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (debug_msg_tac' ctxt high ("bvadd bitblast reconstruction debug 3"))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvadd = prove_bitblast_step_bvadd
end


(* Bitblasting a bvneg *)
local
  fun prove_bitblast_step_bvneg ctxt _ _ t =
  let
    (*obtain bitblasted variables*)
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t bvneg =",t))
    fun find_bbT_vars (_ $ (_$ (_ $ (_ $ (_ $ x ))) $ _)) = x |
        find_bbT_vars _ = error ("Bitblasting step (bvneg) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t

    (*instantiate with bitblasted variable*)
    val word_minus_rbl_bvneg_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg}) 0
    val word_minus_rbl_bvneg_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [bit_blasted_vars]) word_minus_rbl_bvneg_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("bvneg bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_minus_rbl_bvneg_lemma_inst]))
      THEN' K (unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg_fun}))
      THEN' (debug_msg_tac' ctxt high ("bvneg bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
             K (unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_xor_temp}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg_fun})))
      THEN' (TRY' (simplify_tac ctxt @{thms xor_simps}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg_fun})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (debug_msg_tac' ctxt high ("bvneg bitblast reconstruction debug 3"))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvneg = prove_bitblast_step_bvneg
end

(* Bitblasting a bvmult *)
local
  fun prove_bitblast_step_bvmult ctxt _ _ t =
  let
    (*obtain bitblasted variables*)
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ (_ $ x)) $ (_ $ (_ $ y))) $ _)) = (x,y) |
        find_bbT_vars _ = error ("Bitblasting step (bvmult) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t

    (*instantiate with bitblasted variable*)
    val word_mult_rbl_bvmult_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_mult_rbl_bvmult}) 0
    val word_mult_rbl_bvmult_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) word_mult_rbl_bvmult_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("bvmult bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_mult_rbl_bvmult_lemma_inst]))
      THEN' (debug_msg_tac' ctxt high ("bvmult bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_mult_rbl_bvmult_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd_fun})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (debug_msg_tac' ctxt high ("bvmult bitblast reconstruction debug 3"))
      )
THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_mult_rbl_bvmult_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd_fun2})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (debug_msg_tac' ctxt high ("bvmult bitblast reconstruction debug 4"))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvmult = prove_bitblast_step_bvmult
end

(* Bitblasting an extract *)
local
  fun prove_bitblast_step_extract ctxt thms _ t =
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("Found a bitblast extract step "))

    (*obtain bitblasted variables*)
    fun find_bbT_index (_ $ (_ $ (_ $ i $ j $ _) $ _)) = (i,j) |
        find_bbT_index _ = error ("Bitblasting step (extend) has the wrong form!")
    val indices = find_bbT_index t
    val _ = debug_msg ctxt high (fn () => \<^print> ("indices ",apsnd (Thm.cterm_of ctxt) ( apfst (Thm.cterm_of ctxt) indices)))

    fun find_bbT_orig (_ $ (_ $ (_ $ _ $ _ $ (_ $ x)) $ _)) = x |
        find_bbT_orig _ = error ("Bitblasting step (extend) has the wrong form!")
    val find_bbT_var = find_bbT_orig t
    val _ = debug_msg ctxt high (fn () => \<^print> ("find_bbT_var ",Thm.cterm_of ctxt find_bbT_var))



    (*instantiate with bitblasted variable*)
    val rbl_extract_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems rbl_extract}) 0
       val _ = debug_msg ctxt high (fn () => \<^print> ("rbl_extract_lemma ",rbl_extract_lemma))

    val rbl_extract_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [snd indices, fst indices, find_bbT_var]) rbl_extract_lemma

  in  SMT_Replay_Methods.prove ctxt t (fn _ =>(

      (debug_msg_tac' ctxt high ("bv bitblast extract reconstruction debug 1"))
      THEN' 

       K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [rbl_extract_lemma_inst]))
      THEN' (debug_msg_tac' ctxt high ("bv bitblast extract reconstruction debug 2"))
        THEN' TRY' (Code_Simp.dynamic_tac ctxt)

      (*First goal is of the form nat (c1::int) \<le> nat (c2::int)*)
      THEN' (TRY' (simplify_tac ctxt 
         (@{thms nat_numeral nat_1 le0 Suc_inject Suc_le_mono Suc_less_eq length_rev} @ (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}))))
      THEN' (debug_msg_tac' ctxt high ("resolved indices constraint"))

      (*Second goal has the form Suc c1 < length xs *)
      THEN' (TRY' (simplify_tac ctxt @{thms length_rev append.left_neutral list.size numeral_nat Suc_inject Suc_le_mono Suc_less_eq}))
      THEN' (debug_msg_tac' ctxt high ("resolved Suc c1 < length xs constraint"))
 THEN' (TRY' (simplify_tac ctxt 
         (@{thms nat_numeral Suc_inject Suc_le_mono Suc_less_eq length_rev} @ (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}))))
 THEN' (TRY' (simplify_tac ctxt 
         (@{thms nat_numeral numeral_eq_Suc numeral_nat pred_numeral_simps})))


      THEN' REPEAT_CHANGED (
            (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (debug_msg_tac' ctxt high ("bitwise operation bitblast reconstruction debug 3"))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
        THEN' TRY' (Code_Simp.dynamic_tac ctxt)

      )
)
  end
in
  val bv_bitblast_step_extract = prove_bitblast_step_extract
end


(* Bitblasting a bvequal *)
local
  fun prove_bitblast_step_bvequal ctxt _ _ t =
  let
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))

    (*obtain bitblasted variables*)
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ (_ $ x)) $ (_ $ (_ $ y))) $ _)) = (x,y) |
        find_bbT_vars _ = error ("Bitblasting step (bvequal) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t

    (*instantiate with bitblasted variable*)
    val word_equal_rbl_bvequal_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_equal_rbl_bvequal}) 0
    val word_equal_rbl_bvequal_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) word_equal_rbl_bvequal_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      Method.insert_tac ctxt [word_equal_rbl_bvequal_lemma_inst]

      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_equal_rbl_bvequal_lemma_inst]))
      THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvequal_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvequal = prove_bitblast_step_bvequal
end

(* Bitblasting a concat *)
local
  fun prove_bitblast_step_concat ctxt thms _ t =
  let
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction concat t =",t))
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction concat thms =",thms))

    (*obtain bitblasted variable*)
    fun find_bbT_var (_ $ (_ $ (_$ (_ $ (_ $ xs)) $ (_ $ (_ $ ys))) $ _ )) = (xs,ys) |
        find_bbT_var _ = error ("Bitblasting step (concat) has the wrong form!")
    val bit_blasted_var = find_bbT_var t
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction concat bit_blasted_var =",bit_blasted_var))


    (*instantiate with bitblasted variables*)
    val rbl_concat_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems rbl_concat}) 0
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction concat rbl_concat_lemma =",rbl_concat_lemma))

    val rbl_concat_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_var,snd bit_blasted_var]) rbl_concat_lemma

    val arith_simps2 = @{thms Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
                     Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral}

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (debug_msg_tac' ctxt high ("concat bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [rbl_concat_lemma_inst]))
      THEN' (debug_msg_tac' ctxt high ("concat bitblast reconstruction debug 2 "))
      THEN' REPEAT_CHANGED (
          TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists})))))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms Num.numeral_2_eq_2 Nat.One_nat_def eval_nat_numeral})))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms arith_simps alethe_minus_simplify})))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt arith_simps2)))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_const_test})))))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rbl_extract_fun})))))
      THEN' (debug_msg_tac' ctxt high ("bv bitblast concat reconstruction debug 3")))
      ))
  end
in
  val bv_bitblast_step_concat = prove_bitblast_step_concat
end


(* Bitblasting a bvult *)
local
  fun prove_bitblast_step_bvult ctxt _ _ t =
  let
    (*obtain bitblasted variables*)
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ x) $ (_ $ y)) $ _)) = (x,y) |
        find_bbT_vars _ = error ("Bitblasting step (bvult) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t
    (*val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))*)

    (*instantiate with bitblasted variable*)
    val word_less_rbl_bvult_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_less_rbl_bvult}) 0
    val word_less_rbl_bvult_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) word_less_rbl_bvult_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      (*K (print_tac ctxt ("bvult bitblast reconstruction debug 1"))
      THEN'*) K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_less_rbl_bvult_lemma_inst]))
      (*THEN' K (print_tac ctxt ("bvult bitblast reconstruction debug 2"))*)
      THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms alethe_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      (*THEN' K (print_tac ctxt ("bvult bitblast reconstruction debug 3"))*)
      )
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun})))
      ))
  end
in
  val bv_bitblast_step_bvult = prove_bitblast_step_bvult
  val bv_bitblast_step_bvule = prove_bitblast_step_bvult (*TODO*)
end

local
  fun xor_neg_term ctxt thm (\<^term>\<open>Trueprop\<close> $
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>SMT_CVC_Util.xor\<close> $ a $ b) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | xor_neg_term ctxt thm  t =
        replay_error ctxt "invalid application in xor neg" Alethe_Replay_Methods.Unsupported [thm] [] t


(*TODO: Might be able to get rid of this with better instantiation *)
  fun xor_pos_term ctxt thm (\<^term>\<open>Trueprop\<close> $
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>HOL.Not\<close> $ (\<^term>\<open>SMT_CVC_Util.xor\<close> $ a $ b)) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | xor_pos_term ctxt thm t =(@{print}("thm",thm);@{print}("t",t);
        replay_error ctxt "invalid application in xor pos" Alethe_Replay_Methods.Unsupported [thm] [] t)

  fun prove_xor_pos_neg xor_pos_neg_term thm ctxt _ t =
    let
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast xor reconstruction t =",t))

 val thm = xor_pos_neg_term ctxt thm t
    in
      SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [thm]
        THEN' TRY' (assume_tac ctxt))
    end
in

val xor_pos1  = prove_xor_pos_neg xor_pos_term @{thm xor_pos1}
val xor_pos2  = prove_xor_pos_neg xor_pos_term @{thm xor_pos2}
val xor_neg1  = prove_xor_pos_neg xor_neg_term @{thm xor_neg1}
val xor_neg2  = prove_xor_pos_neg xor_neg_term @{thm xor_neg2}

end

fun ignore_args f ctxt thm _ t = f ctxt thm t

val xor_rules = map (fn (x,y) => (x,ignore_args y)) [
  ("xor_pos1", xor_pos1),
  ("xor_pos2", xor_pos2),
  ("xor_neg1", xor_neg1),
  ("xor_neg2", xor_neg2)]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Alethe_Replay_Methods.declare_alethe_rule) xor_rules))

local
  fun dest_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = t
  | dest_prop t = t

  fun prove_bv_poly_norm2 ctxt t =
  let
    val word_thms = @{thms Word.word_eq_numeral_iff_iszero Word.iszero_word_no Type_Length.len_bit0 Type_Length.len_num1
take_bit_num_simps }
    fun simplify_tac ctxt thms =
      ctxt
      |> empty_simpset
      |> put_simpset HOL_basic_ss
      |> (fn ctxt => ctxt addsimps (@{thms simp_thms}@word_thms) addsimps thms)
      |> (Simplifier.add_cong @{thm if_weak_cong})
      |> (fn ctxt => ctxt
           addsimprocs [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
             @{simproc divide_cancel_numeral_factor}, @{simproc divide_cancel_factor},
             @{simproc intle_cancel_numerals}, @{simproc intless_cancel_numerals}, @{simproc inteq_cancel_numerals},
             @{simproc field_combine_numerals},
             @{simproc ring_le_cancel_numeral_factor},
             @{simproc HOL.NO_MATCH}, @{simproc Numeral_Simprocs.semiring_assoc_fold},
             @{simproc Numeral_Simprocs.field_divide_cancel_numeral_factor},
             @{simproc Numeral_Simprocs.field_eq_cancel_numeral_factor}
             ])
      |> Simplifier.full_simp_tac
    fun simplify_tac_with_background_simp ctxt thms =
      ctxt
      |> (fn ctxt => ctxt addsimps thms)
      |> Simplifier.full_simp_tac
    val tac = (fn _ => fn _ =>
      SOLVED' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_norm})
        THEN' K (print_tac ctxt "hi"))
        (*if the previous does not solve, use full simplification power with the current content*)
      ORELSE'
        simplify_tac_with_background_simp ctxt (Named_Theorems.get ctxt @{named_theorems field_simps})
        THEN' TRY' (Code_Simp.dynamic_tac ctxt))
  in
  SMT_Replay_Methods.prove_abstract' ctxt t tac
    (SMT_Replay_Methods.abstract_for_poly_norm ctxt (dest_prop t))
  end

  fun prove_bv_poly_norm ctxt _ _ t =
    prove_bv_poly_norm2 ctxt t

in
  val bv_poly_norm = prove_bv_poly_norm
end

fun bv_aci_simp ctxt _  _ t = 
SMT_Replay_Methods.prove ctxt t (fn _ =>(
     REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_aci_simp}))
)))

(*
bvand x c = concat(
             (bvand (smt_extract i0 j0 x) (smt_extract i0 j0 c))
             (concat
               (bvand (smt_extract i1 j1) (smt_extract i1 j1 c))
               ...
             )
            )
I start from the innermost concat and merge its two bvand children together. I'd rather do it more
fine-grained but alas no time
*)
fun REPEAT' tac = fn i => REPEAT (tac i)
fun REPEAT_DETERM_N' times tac = fn i => REPEAT_DETERM_N times (tac i)
fun bv_bitwise_slicing ctxt _  _ t = 
SMT_Replay_Methods.prove ctxt t (fn _ =>(
     K(print_tac ctxt "here") THEN'
      REPEAT'
      ((EqSubst.eqsubst_tac ctxt [0] @{thms xor_word_cat_smt_extract_step})
     THEN' K(print_tac ctxt "after applying lemma") 
     THEN' (REPEAT_DETERM_N' 11 ( (simplify_tac ctxt  @{thms arith_simps nat_mono nat_0 nat_1})
        THEN' (Code_Simp.dynamic_tac ctxt)
        THEN' K(print_tac ctxt "resolving assumptions") )))
    THEN' K(print_tac ctxt "before final step") 
    THEN' (EqSubst.eqsubst_tac ctxt [0] @{thms bitwise_slicing_smt_extract_identity})
    THEN' (Code_Simp.dynamic_tac ctxt)
    THEN' K(print_tac ctxt "afterfinal step") 
    THEN' (EqSubst.eqsubst_tac ctxt [0] @{thms bitwise_slicing_smt_extract_identity})
    THEN' (Code_Simp.dynamic_tac ctxt)
    THEN' K(print_tac ctxt "afterfinal step")
    THEN' (match_tac ctxt @{thms semiring_bit_operations_class.xor.commute})
    THEN' K(print_tac ctxt "afterfinal step")

))
(* smt_extract (nat (7::int)) (nat 0) (27::8 word) XOR smt_extract (nat (7::int)) (nat 0) (lift_shiftla v0__ 1)*)


val bv_rules = [
  ("bv_bitblast_step_var", bv_bitblast_step_var) ,
  ("bv_bitblast_step_const", bv_bitblast_step_const),
  ("bv_bitblast_step_bvand", bv_bitblast_step_bvand),
  ("bv_bitblast_step_bvor", bv_bitblast_step_bvor),
  ("bv_bitblast_step_bvxor", bv_bitblast_step_bvxor),
  ("bv_bitblast_step_bvxnor", bv_bitblast_step_bvxnor),
  ("bv_bitblast_step_bvnot", bv_bitblast_step_bvnot),
  ("bv_bitblast_step_bvadd", bv_bitblast_step_bvadd),
  ("bv_bitblast_step_bvneg", bv_bitblast_step_bvneg),
  ("bv_bitblast_step_bvmult", bv_bitblast_step_bvmult),
  ("bv_bitblast_step_extract", bv_bitblast_step_extract),
  ("bv_bitblast_step_concat", bv_bitblast_step_concat),
  ("bv_bitblast_step_bvequal", bv_bitblast_step_bvequal),
  ("bv_bitblast_step_bvult", bv_bitblast_step_bvult),
  ("bv_bitblast_step_bvule", bv_bitblast_step_bvule),
  ("bv_poly_norm", bv_poly_norm),
  ("bv_aci_simp",bv_aci_simp),
  ("bv_bitwise_slicing",bv_bitwise_slicing)]


val _ = Theory.setup (Context.theory_map (
   fold (uncurry Alethe_Replay_Methods.declare_alethe_rule) bv_rules))

end;
