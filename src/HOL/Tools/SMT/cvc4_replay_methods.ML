(*  Title:      HOL/Tools/SMT/cvc4_replay_methods.ML
    Author:     Mathias Fleury, JKU
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying veriT proofs.
*)

signature CVC4_REPLAY_METHODS =
sig
  (*methods for verit proof rules*)
  val method_for: string -> Proof.context -> thm list -> term list -> term Symtab.table ->
     (string * term) list -> term -> thm

  val discharge: Proof.context -> thm list -> term -> thm
end;


structure CVC4_Replay_Methods: CVC4_REPLAY_METHODS =
struct

open Lethe_Replay_Methods

fun cvc4_rule_of "bind" = Bind
  | cvc4_rule_of "cong" = Cong
  | cvc4_rule_of "refl" = Refl
  | cvc4_rule_of "equiv1" = Equiv1
  | cvc4_rule_of "equiv2" = Equiv2
  | cvc4_rule_of "equiv_pos1" = Equiv_pos1
   (*Equiv_pos2 covered below*)
  | cvc4_rule_of "equiv_neg1" = Equiv_neg1
  | cvc4_rule_of "equiv_neg2" = Equiv_neg2
  | cvc4_rule_of "sko_forall" = Skolem_Forall
  | cvc4_rule_of "sko_ex" = Skolem_Ex
  | cvc4_rule_of "eq_reflexive" = Eq_Reflexive
  | cvc4_rule_of "forall_inst" = Forall_Inst
  | cvc4_rule_of "implies_pos" = Implies_Pos
  | cvc4_rule_of "or" = Or
  | cvc4_rule_of "not_or" = Not_Or
  | cvc4_rule_of "resolution" = Resolution
  | cvc4_rule_of "trans" = Trans
  | cvc4_rule_of "false" = False
  | cvc4_rule_of "ac_simp" = AC_Simp
  | cvc4_rule_of "and" = And
  | cvc4_rule_of "not_and" = Not_And
  | cvc4_rule_of "xor_pos1" = Xor_Pos1
  | cvc4_rule_of "xor_pos2" = Xor_Pos2
  | cvc4_rule_of "xor_neg1" = Xor_Neg1
  | cvc4_rule_of "xor_neg2" = Xor_Neg2
  | cvc4_rule_of "and_pos" = And_Pos
  | cvc4_rule_of "and_neg" = And_Neg
  | cvc4_rule_of "or_pos" = Or_Pos
  | cvc4_rule_of "or_neg" = Or_Neg
  | cvc4_rule_of "not_equiv1" = Not_Equiv1
  | cvc4_rule_of "not_equiv2" = Not_Equiv2
  | cvc4_rule_of "not_implies1" = Not_Implies1
  | cvc4_rule_of "not_implies2" = Not_Implies2
  | cvc4_rule_of "implies_neg1" = Implies_Neg1
  | cvc4_rule_of "implies_neg2" = Implies_Neg2
  | cvc4_rule_of "implies" = Implies
  | cvc4_rule_of "bfun_elim" = Bfun_Elim
  | cvc4_rule_of "ite1" = ITE1
  | cvc4_rule_of "ite2" = ITE2
  | cvc4_rule_of "not_ite1" = Not_ITE1
  | cvc4_rule_of "not_ite2" = Not_ITE2
  | cvc4_rule_of "ite_pos1" = ITE_Pos1
  | cvc4_rule_of "ite_pos2" = ITE_Pos2
  | cvc4_rule_of "ite_neg1" = ITE_Neg1
  | cvc4_rule_of "ite_neg2" = ITE_Neg2
  | cvc4_rule_of "la_disequality" = LA_Disequality
  | cvc4_rule_of "lia_generic" = LIA_Generic
  | cvc4_rule_of "la_generic" = LA_Generic
  | cvc4_rule_of "la_tautology" = LA_Tautology
  | cvc4_rule_of "la_totality" = LA_Totality
  | cvc4_rule_of "la_rw_eq"= LA_RW_Eq
  | cvc4_rule_of "nla_generic"= NLA_Generic
  | cvc4_rule_of "eq_transitive" = Eq_Transitive
  | cvc4_rule_of "qnt_rm_unused" = Qnt_Rm_Unused
  | cvc4_rule_of "onepoint" = Onepoint
  | cvc4_rule_of "qnt_join" = Qnt_Join
  | cvc4_rule_of "subproof" = Subproof
  | cvc4_rule_of "bool_simplify" = Bool_Simplify
  | cvc4_rule_of "or_simplify" = Or_Simplify
  | cvc4_rule_of "ite_simplify" = ITE_Simplify
  | cvc4_rule_of "and_simplify" = And_Simplify
  | cvc4_rule_of "not_simplify" = Not_Simplify
  | cvc4_rule_of "equiv_simplify" = Equiv_Simplify
  | cvc4_rule_of "eq_simplify" = Eq_Simplify
  | cvc4_rule_of "implies_simplify" = Implies_Simplify
  | cvc4_rule_of "connective_def" = Connective_Def
  | cvc4_rule_of "minus_simplify" = Minus_Simplify
  | cvc4_rule_of "sum_simplify" = Sum_Simplify
  | cvc4_rule_of "prod_simplify" = Prod_Simplify
  | cvc4_rule_of "all_simplify" = All_Simplify
  | cvc4_rule_of "comp_simplify" = Comp_Simplify
  | cvc4_rule_of "qnt_simplify" = Qnt_Simplify
  | cvc4_rule_of "tautology" = Tautological_Clause
  | cvc4_rule_of "qnt_cnf" = Qnt_CNF
  | cvc4_rule_of "symm" = Symm
  | cvc4_rule_of "not_symm" = Not_Symm
  | cvc4_rule_of "reordering" = Reordering
  | cvc4_rule_of "bv_bitblast_step_var" = BV_Bitblast_Step_Var
  | cvc4_rule_of "bv_bitblast_step_const" = BV_Bitblast_Step_Const
  | cvc4_rule_of "bv_bitblast_step_bvadd" = BV_Bitblast_Step_Bvadd
  | cvc4_rule_of "bv_bitblast_step_bvneg" = BV_Bitblast_Step_Bvneg
  | cvc4_rule_of "bv_bitblast_step_bvult" = BV_Bitblast_Step_Bvult
  | cvc4_rule_of "bv_bitblast_step_bvule" = BV_Bitblast_Step_Bvule
  | cvc4_rule_of "bv_bitblast_step_extract" = BV_Bitblast_Step_Extract
  | cvc4_rule_of "bv_bitblast_step_bvequal" = BV_Bitblast_Step_Bvequal
  | cvc4_rule_of "bv_bitblast_step_concat" = BV_Bitblast_Step_Concat
  | cvc4_rule_of "unary_minus_simplify" = Minus_Simplify
  | cvc4_rule_of "quantifier_simplify" = Tmp_Quantifier_Simplify (*TODO Remove*)
  | cvc4_rule_of r =
     if r = Lethe_Proof.normalized_input_rule then Normalized_Input
     else if r = Lethe_Proof.local_input_rule then Local_Input
     else if r = Lethe_Proof.lethe_def then Definition
     else if r = Lethe_Proof.not_not_rule then Not_Not
     else if r = Lethe_Proof.contract_rule orelse r = "duplicate_literals" then Duplicate_Literals     
     else if r = Lethe_Proof.ite_intro_rule then ITE_Intro
     else if r = Lethe_Proof.eq_congruent_rule then Eq_Congruent
     else if r = Lethe_Proof.eq_congruent_pred_rule then Eq_Congruent_Pred
     else if r = Lethe_Proof.theory_resolution2_rule then Theory_Resolution2
     else if r = Lethe_Proof.th_resolution_rule then Theory_Resolution
     else if r = Lethe_Proof.equiv_pos2_rule then Equiv_pos2
     else (@{print} ("Unsupport rule", r); Unsupported)

fun normalized_input ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
let
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("normalized input t =",t))
    val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("normalized ipput prems =",prems))

in
  resolve_tac ctxt prems
    (*TODO: should only be used for lambda encoding*)
    ORELSE' Clasimp.force_tac ctxt
end)

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
      K (Clasimp.auto_tac ctxt))


fun unsupported_failback ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
let
    val _ = @{print} "fallback!"

in
  Method.insert_tac ctxt prems
    (*TODO: should only be used for lambda encoding*)
    THEN' Clasimp.force_tac ctxt
end)

(*
Example:
lemma \<open>(\<forall>x y. P x = Q y) \<Longrightarrow> (\<forall> y z. Q y = R z) \<Longrightarrow> (\<forall>x z. P x = R z)\<close>
*)
fun trans ctxt prems t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt prems
    THEN' (REPEAT_CHANGED (resolve_tac ctxt @{thms trans} THEN' assume_tac ctxt))
    THEN' (resolve_tac ctxt @{thms refl}))


(* Combining all together *)

fun unsupported rule ctxt thms _ _ _ = SMT_Replay_Methods.replay_error ctxt "Unsupported verit rule"
  rule thms

fun ignore_args f ctxt thm _ _ _ t = f ctxt thm t
fun ignore_decls f ctxt thm args insts _ t = f ctxt thm args insts t
fun ignore_insts f ctxt thm args _ _ t = f ctxt thm args t

fun choose And = ignore_args and_rule
  | choose And_Neg = ignore_args and_neg_rule
  | choose And_Pos = ignore_args and_pos
  | choose And_Simplify = ignore_args rewrite_and_simplify
  | choose Bind = ignore_insts bind
  | choose Bool_Simplify = ignore_args rewrite_bool_simplify
  | choose Comp_Simplify = ignore_args rewrite_comp_simplify
  | choose Cong = ignore_args cong
  | choose Connective_Def = ignore_args rewrite_connective_def
  | choose Duplicate_Literals = ignore_args duplicate_literals
  | choose Eq_Congruent = ignore_args eq_congruent
  | choose Eq_Congruent_Pred = ignore_args eq_congruent_pred
  | choose Eq_Reflexive = ignore_args eq_reflexive
  | choose Eq_Simplify = ignore_args rewrite_eq_simplify
  | choose Eq_Transitive = ignore_args eq_transitive
  | choose Equiv1 = ignore_args equiv1
  | choose Equiv2 = ignore_args equiv2
  | choose Equiv_neg1 = ignore_args equiv_neg1
  | choose Equiv_neg2 = ignore_args equiv_neg2
  | choose Equiv_pos1 = ignore_args equiv_pos1
  | choose Equiv_pos2 = ignore_args equiv_pos2
  | choose Equiv_Simplify = ignore_args rewrite_equiv_simplify
  | choose False = ignore_args false_rule
  | choose Forall_Inst = ignore_decls forall_inst
  | choose Implies = ignore_args implies_rules
  | choose Implies_Neg1 = ignore_args implies_neg1
  | choose Implies_Neg2 = ignore_args implies_neg2
  | choose Implies_Pos = ignore_args implies_pos
  | choose Implies_Simplify = ignore_args rewrite_implies_simplify
  | choose ITE1 = ignore_args ite1
  | choose ITE2 = ignore_args ite2
  | choose ITE_Intro = ignore_args ite_intro
  | choose ITE_Neg1 = ignore_args ite_neg1
  | choose ITE_Neg2 = ignore_args ite_neg2
  | choose ITE_Pos1 = ignore_args ite_pos1
  | choose ITE_Pos2 = ignore_args ite_pos2
  | choose ITE_Simplify = ignore_args rewrite_ite_simplify
  | choose LA_Disequality = ignore_args la_disequality
  | choose LA_Generic = ignore_insts la_generic
  | choose LA_RW_Eq = ignore_args la_rw_eq
  | choose LA_Tautology = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose LA_Totality = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose LIA_Generic = ignore_args lia_generic
  | choose Local_Input = ignore_args refl
  | choose Minus_Simplify = ignore_args rewrite_minus_simplify
  | choose NLA_Generic = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose Normalized_Input = ignore_args normalized_input
  | choose Not_And = ignore_args not_and_rule
  | choose Xor_Pos1 = ignore_args xor_pos1
  | choose Xor_Pos2 = ignore_args xor_pos2
  | choose Xor_Neg1 = ignore_args xor_neg1
  | choose Xor_Neg2 = ignore_args xor_neg2
  | choose Not_Equiv1 = ignore_args not_equiv1
  | choose Not_Equiv2 = ignore_args not_equiv2
  | choose Not_Implies1 = ignore_args not_implies1
  | choose Not_Implies2 = ignore_args not_implies2
  | choose Not_ITE1 = ignore_args not_ite1
  | choose Not_ITE2 = ignore_args not_ite2
  | choose Not_Not = ignore_args not_not
  | choose Not_Or = ignore_args not_or_rule
  | choose Not_Simplify = ignore_args rewrite_not_simplify
  | choose Or = ignore_args or
  | choose Or_Neg = ignore_args or_neg_rule
  | choose Or_Pos = ignore_args or_pos_rule
  | choose Or_Simplify = ignore_args rewrite_or_simplify
  | choose Theory_Resolution2 = ignore_args theory_resolution2
  | choose Prod_Simplify = ignore_args prod_simplify
  | choose All_Simplify = ignore_insts all_simplify
  | choose Qnt_Join = ignore_args qnt_join
  | choose Qnt_Rm_Unused = ignore_args qnt_rm_unused
  | choose Onepoint = ignore_args onepoint
  | choose Qnt_Simplify = ignore_args qnt_simplify
  | choose Refl = ignore_args refl
  | choose Resolution = ignore_args unit_res
  | choose Skolem_Ex = ignore_args skolem_ex
  | choose Skolem_Forall = ignore_args skolem_forall
  | choose Subproof = ignore_args subproof
  | choose Sum_Simplify = ignore_args sum_simplify
  | choose Tautological_Clause = ignore_args tautological_clause
  | choose Theory_Resolution = ignore_args unit_res
  | choose AC_Simp = ignore_args tmp_AC_rule
  | choose Bfun_Elim = ignore_args bfun_elim
  | choose Qnt_CNF = ignore_args qnt_cnf
  | choose Trans = ignore_args trans
  | choose Symm = ignore_args symm
  | choose Not_Symm = ignore_args not_symm
  | choose Reordering = ignore_args reordering
  | choose BV_Bitblast_Step_Var = ignore_args bv_bitblast_step_var
  | choose BV_Bitblast_Step_Const = ignore_args bv_bitblast_step_const
  | choose BV_Bitblast_Step_Bvadd = ignore_args bv_bitblast_step_bvadd
  | choose BV_Bitblast_Step_Bvneg = ignore_args bv_bitblast_step_bvneg
  | choose BV_Bitblast_Step_Bvule = ignore_args bv_bitblast_step_bvule
  | choose BV_Bitblast_Step_Bvult = ignore_args bv_bitblast_step_bvult
  | choose BV_Bitblast_Step_Extract = ignore_args bv_bitblast_step_extract
  | choose BV_Bitblast_Step_Bvequal = ignore_args bv_bitblast_step_bvequal
  | choose BV_Bitblast_Step_Concat = ignore_args bv_bitblast_step_concat
  | choose Tmp_Quantifier_Simplify = ignore_args qnt_simplify
  | choose r = ignore_args unsupported_failback

type verit_method = Proof.context -> thm list -> term -> thm
type abs_context = int * term Termtab.table

fun with_tracing rule method ctxt thms args insts decls t =
  let val _ = SMT_Replay_Methods.trace_goal ctxt rule thms t
  in method ctxt thms args insts decls t end

fun method_for rule = with_tracing rule (choose (cvc4_rule_of rule))

fun discharge ctxt [thm] t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    resolve_tac ctxt [thm] THEN_ALL_NEW (resolve_tac ctxt @{thms refl}))

end;
