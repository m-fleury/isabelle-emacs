(*  Title:      HOL/Tools/SMT/lethe_replay_bv_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Stanford

Proof method for replaying Alethe proofs for bitvector steps.
*)

(*TODO: Had to make this work again quickly and changed all lethe_tac to lethe_tac_args. 
This could be changed back but declare_alethe_rule would need to accept rules without arguments*)
signature LETHE_REPLAY_BV_METHODS =
sig
  val xor_pos1: Lethe_Replay_Methods.lethe_tac
  val xor_pos2: Lethe_Replay_Methods.lethe_tac
  val xor_neg1: Lethe_Replay_Methods.lethe_tac
  val xor_neg2: Lethe_Replay_Methods.lethe_tac

  val bv_bitblast_step_var: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_const: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvand: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvor: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvxor: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvxnor: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvnot: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvadd: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvneg: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvmult: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_extract: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_concat: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvequal: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvult: Lethe_Replay_Methods.lethe_tac_args
  val bv_bitblast_step_bvule: Lethe_Replay_Methods.lethe_tac_args

end;


structure Lethe_Replay_BV_Methods: LETHE_REPLAY_BV_METHODS =
struct

val TRY' = Lethe_Replay_Methods.TRY'
val simplify_tac = Lethe_Replay_Methods.simplify_tac
val REPEAT_CHANGED = Lethe_Replay_Methods.REPEAT_CHANGED
val replay_error = Lethe_Replay_Methods.replay_error


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
      K (print_tac ctxt ("bv bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_var_rbl_list_lemma_inst]))
      THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 2 "))
      THEN' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))
      THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 3"))
      THEN' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}))
      THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 4"))
      THEN' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5}))
      THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 5"))
      THEN' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists})))
      THEN' K (print_tac ctxt ("bv bitblast reconstruction debug 6"))
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
      K (print_tac ctxt ("bv bitblast const reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [bv_reconstruction_const_lemma_inst]))
      THEN' K (print_tac ctxt ("bv bitblast const reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
       TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_const_test}))
       THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))))
       THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
       THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs}))))
       THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
       THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
       THEN' (TRY' (simplify_tac ctxt (@{thms monoid_mult_class.power_Suc0_right power_0})))
       THEN' K (print_tac ctxt ("bv bitblast const reconstruction debug 5"))
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
    val bitwise_op_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) bitwise_op_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      K (print_tac ctxt ("bitwise operation bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [bitwise_op_lemma_inst]))
      THEN' K (print_tac ctxt ("bitwise operation bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bitwise operation bitblast reconstruction debug 3"))
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
      K (print_tac ctxt ("bitwise operation bvnot bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [bitwise_op_lemma_inst]))
      THEN' K (print_tac ctxt ("bitwise operation bvnot bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
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
    fun find_bbT_vars (_ $ (_ $ (_ $ (_ $ x) $ (_ $ y)) $ _)) = (x,y) |
        find_bbT_vars _ = error ("Bitblasting step (bvadd) has the wrong form!")
    val bit_blasted_vars = find_bbT_vars t
    (*val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))*)

    (*instantiate with bitblasted variable*)
    val word_plus_rbl_bvadd_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd}) 0
    val word_plus_rbl_bvadd_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [fst bit_blasted_vars,snd bit_blasted_vars]) word_plus_rbl_bvadd_lemma

   in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      K (print_tac ctxt ("bvadd bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_plus_rbl_bvadd_lemma_inst]))
      THEN' K (print_tac ctxt ("bvadd bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
           (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bvadd bitblast reconstruction debug 3"))
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
      K (print_tac ctxt ("bvneg bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_minus_rbl_bvneg_lemma_inst]))
      THEN' K (unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg_fun}))
      THEN' K (print_tac ctxt ("bvneg bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
             K (unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_xor_temp}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg_fun})))
      THEN' (TRY' (simplify_tac ctxt @{thms xor_simps}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_minus_rbl_bvneg_fun})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bvneg bitblast reconstruction debug 3"))
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
      K (print_tac ctxt ("bvmult bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_mult_rbl_bvmult_lemma_inst]))
      THEN' K (print_tac ctxt ("bvmult bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_mult_rbl_bvmult_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd_fun})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bvmult bitblast reconstruction debug 3"))
      )
THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_mult_rbl_bvmult_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems word_plus_rbl_bvadd_fun2})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bvmult bitblast reconstruction debug 4"))
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
    (*val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction t =",t))
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("bv bitblast reconstruction thms =",thms))*)

    (*obtain bitblasted variables*)
    fun find_bbT_index (_ $ (_ $ (_ $ i $ j $ _) $ _)) = (i,j) |
        find_bbT_index _ = error ("Bitblasting step (extend) has the wrong form!")
    val indices = find_bbT_index t
    fun find_bbT_orig (_ $ (_ $ (_ $ _ $ _ $ (_ $ x)) $ _)) = x |
        find_bbT_orig _ = error ("Bitblasting step (extend) has the wrong form!")
    val find_bbT_var = find_bbT_orig t

    (*instantiate with bitblasted variable*)
    val rbl_extract_lemma =
        nth (Named_Theorems.get ctxt @{named_theorems rbl_extract}) 0
   val rbl_extract_lemma_inst =
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt)
 [fst indices, snd indices,find_bbT_var]) rbl_extract_lemma


  in  SMT_Replay_Methods.prove ctxt t (fn _ =>(
      K (print_tac ctxt ("bv bitblast extract reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [rbl_extract_lemma_inst]))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists})))))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 2a"))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 2b"))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 2c"))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms Num.numeral_2_eq_2 Nat.One_nat_def eval_nat_numeral})))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5}))))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 2d"))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms arith_simps verit_minus_simplify})))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}))))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 2e"))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rbl_extract_fun})))))
      THEN' K (print_tac ctxt ("bv bitblast extract reconstruction debug 3")))
      ))
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
      K (print_tac ctxt ("bvequal bitblast reconstruction debug 1"))
      THEN' Method.insert_tac ctxt [word_equal_rbl_bvequal_lemma_inst]
      THEN' K (print_tac ctxt ("bvequal bitblast reconstruction debug 2a"))

      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_equal_rbl_bvequal_lemma_inst]))
      THEN' K (print_tac ctxt ("bvequal bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvequal_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bvequal bitblast reconstruction debug 3"))
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
      K (print_tac ctxt ("concat bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [rbl_concat_lemma_inst]))
      THEN' K (print_tac ctxt ("concat bitblast reconstruction debug 2 "))
      THEN' REPEAT_CHANGED (
          TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists})))))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length}))))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms Num.numeral_2_eq_2 Nat.One_nat_def eval_nat_numeral})))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt @{thms arith_simps verit_minus_simplify})))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt arith_simps2)))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_const_test})))))
      THEN' TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rbl_extract_fun})))))
      THEN' K (print_tac ctxt ("bv bitblast concat reconstruction debug 3")))
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
      K (print_tac ctxt ("bvult bitblast reconstruction debug 1"))
      THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [word_less_rbl_bvult_lemma_inst]))
      THEN' K (print_tac ctxt ("bvult bitblast reconstruction debug 2"))
      THEN' REPEAT_CHANGED (
            (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems rbl_bvult_fun}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_length})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems smt_arith_simplify})))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))
      THEN' (TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems bv_reconstruction_lists}))))
      THEN' (TRY' (simplify_tac ctxt @{thms verit_and_simplify1}))
      THEN' (TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems bv_reconstruction_list_funs})))
      THEN' K (print_tac ctxt ("bvult bitblast reconstruction debug 3"))
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
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>Dsl_Nary_Ops.xor\<close> $ a $ b) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | xor_neg_term ctxt thm  t =
        replay_error ctxt "invalid application in xor neg" Lethe_Replay_Methods.Unsupported [thm] t


(*TODO: Might be able to get rid of this with better instantiation *)
  fun xor_pos_term ctxt thm (\<^term>\<open>Trueprop\<close> $
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>HOL.Not\<close> $ (\<^term>\<open>Dsl_Nary_Ops.xor\<close> $ a $ b)) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | xor_pos_term ctxt thm t =(@{print}("thm",thm);@{print}("t",t);
        replay_error ctxt "invalid application in xor pos" Lethe_Replay_Methods.Unsupported [thm] t)

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
   fold (uncurry Lethe_Replay_Methods.declare_alethe_rule) xor_rules))

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
  ("bv_bitblast_step_bvule", bv_bitblast_step_bvule)]


val _ = Theory.setup (Context.theory_map (
   fold (uncurry Lethe_Replay_Methods.declare_alethe_rule) bv_rules))

end;
