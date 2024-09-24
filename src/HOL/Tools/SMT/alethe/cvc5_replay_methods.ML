(*  Title:      HOL/Tools/SMT/cvc5_replay_methods.ML
    Author:     Mathias Fleury, JKU, Uni Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying cvc5 proofs.
*)

signature CVC5_REPLAY_METHODS =
sig
  (*methods for verit proof rules*)
  val method_for: string -> Proof.context -> thm list -> term list -> term list -> term ->
     Alethe_Node.tactic_args option -> thm

  val discharge: Proof.context -> thm list -> term -> thm
end;


structure CVC5_Replay_Methods: CVC5_REPLAY_METHODS =
struct

open Alethe_Replay_Methods

fun cvc5_rule_of "bind" = Bind
  | cvc5_rule_of "cong" = Cong
  | cvc5_rule_of "refl" = Refl
  | cvc5_rule_of "equiv1" = Equiv1
  | cvc5_rule_of "equiv2" = Equiv2
  | cvc5_rule_of "equiv_pos1" = Equiv_pos1
   (*Equiv_pos2 covered below*)
  | cvc5_rule_of "equiv_neg1" = Equiv_neg1
  | cvc5_rule_of "equiv_neg2" = Equiv_neg2
  | cvc5_rule_of "sko_forall" = Sko_Forall
  | cvc5_rule_of "sko_ex" = Sko_Ex
  | cvc5_rule_of "eq_reflexive" = Eq_Reflexive
  | cvc5_rule_of "forall_inst" = Forall_Inst
  | cvc5_rule_of "implies_pos" = Implies_Pos
  | cvc5_rule_of "or" = Or
  | cvc5_rule_of "not_or" = Not_Or
  | cvc5_rule_of "resolution" = Resolution
  | cvc5_rule_of "trans" = Trans
  | cvc5_rule_of "false" = False
  | cvc5_rule_of "ac_simp" = AC_Simp
  | cvc5_rule_of "and" = And
  | cvc5_rule_of "not_and" = Not_And
  | cvc5_rule_of "and_pos" = And_Pos
  | cvc5_rule_of "and_neg" = And_Neg
  | cvc5_rule_of "or_pos" = Or_Pos
  | cvc5_rule_of "or_neg" = Or_Neg
  | cvc5_rule_of "not_equiv1" = Not_Equiv1
  | cvc5_rule_of "not_equiv2" = Not_Equiv2
  | cvc5_rule_of "not_implies1" = Not_Implies1
  | cvc5_rule_of "not_implies2" = Not_Implies2
  | cvc5_rule_of "implies_neg1" = Implies_Neg1
  | cvc5_rule_of "implies_neg2" = Implies_Neg2
  | cvc5_rule_of "implies" = Implies
  | cvc5_rule_of "bfun_elim" = Bfun_Elim
  | cvc5_rule_of "ite1" = ITE1
  | cvc5_rule_of "ite2" = ITE2
  | cvc5_rule_of "not_ite1" = Not_ITE1
  | cvc5_rule_of "not_ite2" = Not_ITE2
  | cvc5_rule_of "ite_pos1" = ITE_Pos1
  | cvc5_rule_of "ite_pos2" = ITE_Pos2
  | cvc5_rule_of "ite_neg1" = ITE_Neg1
  | cvc5_rule_of "ite_neg2" = ITE_Neg2
  | cvc5_rule_of "la_disequality" = LA_Disequality
  | cvc5_rule_of "lia_generic" = LIA_Generic
  | cvc5_rule_of "la_generic" = LA_Generic
  | cvc5_rule_of "la_tautology" = LA_Tautology
  | cvc5_rule_of "la_totality" = LA_Totality
  | cvc5_rule_of "la_rw_eq"= LA_RW_Eq
  | cvc5_rule_of "nla_generic"= NLA_Generic
  | cvc5_rule_of "la_mult_pos"= LA_Mult_Pos
  | cvc5_rule_of "la_mult_neg"= LA_Mult_Neg
  | cvc5_rule_of "eq_transitive" = Eq_Transitive
  | cvc5_rule_of "qnt_rm_unused" = Qnt_Rm_Unused
  | cvc5_rule_of "onepoint" = Onepoint
  | cvc5_rule_of "qnt_join" = Qnt_Join
  | cvc5_rule_of "subproof" = Subproof
  | cvc5_rule_of "bool_simplify" = Bool_Simplify
  | cvc5_rule_of "or_simplify" = Or_Simplify
  | cvc5_rule_of "ite_simplify" = ITE_Simplify
  | cvc5_rule_of "and_simplify" = And_Simplify
  | cvc5_rule_of "not_simplify" = Not_Simplify
  | cvc5_rule_of "equiv_simplify" = Equiv_Simplify
  | cvc5_rule_of "eq_simplify" = Eq_Simplify
  | cvc5_rule_of "implies_simplify" = Implies_Simplify
  | cvc5_rule_of "connective_def" = Connective_Def
  | cvc5_rule_of "minus_simplify" = Minus_Simplify
  | cvc5_rule_of "sum_simplify" = Sum_Simplify
  | cvc5_rule_of "prod_simplify" = Prod_Simplify
  | cvc5_rule_of "comp_simplify" = Comp_Simplify
  | cvc5_rule_of "qnt_simplify" = Qnt_Simplify
  | cvc5_rule_of "all_simplify" = All_Simplify
  | cvc5_rule_of "tautology" = Tautological_Clause
  | cvc5_rule_of "rare_rewrite" = RARE_Rewrite
  | cvc5_rule_of "qnt_cnf" = Qnt_CNF
  | cvc5_rule_of "symm" = Symm
  | cvc5_rule_of "not_symm" = Not_Symm
  | cvc5_rule_of "reordering" = Reordering
  | cvc5_rule_of "unary_minus_simplify" = Unary_Minus_Simplify
  | cvc5_rule_of "quantifier_simplify" = Tmp_Quantifier_Simplify (*TODO Remove*)
  | cvc5_rule_of r =
     if r = Alethe_Proof.normalized_input_rule then Normalized_Input
     else if r = Alethe_Proof.local_input_rule then Local_Input
     else if r = Alethe_Proof.skolem_def then Definition
     else if r = Alethe_Proof.not_not_rule then Not_Not
     else if r = Alethe_Proof.contract_rule orelse r = "duplicate_literals" then Duplicate_Literals
     else if r = Alethe_Proof.ite_intro_rule then ITE_Intro
     else if r = Alethe_Proof.eq_congruent_rule then Eq_Congruent
     else if r = Alethe_Proof.eq_congruent_pred_rule then Eq_Congruent_Pred
     else if r = Alethe_Proof.theory_resolution2_rule then Theory_Resolution2
     else if r = Alethe_Proof.th_resolution_rule then Theory_Resolution
     else if r = Alethe_Proof.equiv_pos2_rule then Equiv_pos2
     else if r = Alethe_Proof.hole orelse r = "undefined" then Hole
     else Other_Rule r

(*work-around should not be needed anymore*)
fun normalized_input' ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  let
     (*val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("conclusion t t =",t))
     val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("normalized input prems =",prems))*)
  in
    (*resolve_tac ctxt prems
     ORELSE' (Method.insert_tac ctxt prems THEN' Clasimp.force_tac (ctxt addsimps @{thms cvc5_normalized_input}))
  *)
 (Skip_Proof.cheat_tac ctxt) 
 end)

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
      K (Clasimp.auto_tac ctxt))


fun hole ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  (*K (print_tac ctxt "stuff")
    THEN'*) Method.insert_tac ctxt prems
    (*TODO: should only be used for lambda encoding*)
(*THEN' K (print_tac ctxt "stuff")*)
    THEN' Clasimp.force_tac ctxt
(*THEN' K (print_tac ctxt "stuff")*)
)

(*
Example:
lemma \<open>(\<forall>x y. P x = Q y) \<Longrightarrow> (\<forall> y z. Q y = R z) \<Longrightarrow> (\<forall>x z. P x = R z)\<close>
*)
fun trans ctxt prems t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
      (*K (print_tac ctxt ("trans reconstruction debug 0"))

    THEN'*)
    ( match_tac ctxt @{thms refl}(* THEN' K (print_tac ctxt ("trans reconstruction debug 9"))*))
  ORELSE'
    (
     (* K (print_tac ctxt ("trans reconstruction debug 0"))
THEN'*) Method.insert_tac ctxt prems
     (*THEN' K (print_tac ctxt ("trans reconstruction debug 1"))*)
    THEN' (REPEAT_CHANGED (resolve_tac ctxt @{thms trans}      (*THEN' K (print_tac ctxt ("trans reconstruction debug 2"))*)
THEN' assume_tac ctxt))
     (*THEN' K (print_tac ctxt ("trans reconstruction debug 3")*)

    THEN' (resolve_tac ctxt @{thms refl})))


(* Combining all together *)

(*ctxt thms step_args context_assignment t args*)
fun ignore_args       f ctxt prems _ _ goal _ = f ctxt prems goal
fun include_step_args f ctxt prems step_args _ goal _ = f ctxt prems step_args goal
fun include_context_ass f ctxt prems _ context_ass goal _ = f ctxt prems context_ass goal
fun include_context_ass_and_args f ctxt prems _ context_ass goal args = f ctxt prems context_ass goal args
fun include_args f ctxt prems _ _ goal args = f ctxt prems goal args

fun choose _ And = ignore_args and_rule
  | choose _ And_Neg = ignore_args and_neg_rule
  | choose _ And_Pos = ignore_args and_pos
  | choose _ And_Simplify = ignore_args rewrite_and_simplify
  | choose _ Bind = include_context_ass bind
  | choose _ Bool_Simplify = ignore_args rewrite_bool_simplify
  | choose _ Comp_Simplify = ignore_args rewrite_comp_simplify
  | choose _ Cong = include_args cong
  | choose _ Connective_Def = ignore_args rewrite_connective_def
  | choose _ Duplicate_Literals = ignore_args duplicate_literals
  | choose _ Eq_Congruent = ignore_args eq_congruent
  | choose _ Eq_Congruent_Pred = ignore_args eq_congruent_pred
  | choose _ Eq_Reflexive = ignore_args eq_reflexive
  | choose _ Eq_Simplify = ignore_args rewrite_eq_simplify
  | choose _ Eq_Transitive = ignore_args eq_transitive
  | choose _ Equiv1 = ignore_args equiv1
  | choose _ Equiv2 = ignore_args equiv2
  | choose _ Equiv_neg1 = ignore_args equiv_neg1
  | choose _ Equiv_neg2 = ignore_args equiv_neg2
  | choose _ Equiv_pos1 = ignore_args equiv_pos1
  | choose _ Equiv_pos2 = ignore_args equiv_pos2
  | choose _ Equiv_Simplify = ignore_args rewrite_equiv_simplify
  | choose _ False = ignore_args false_rule
  | choose _ Forall_Inst = include_args forall_inst
  | choose _ Implies = ignore_args implies_rules
  | choose _ Implies_Neg1 = ignore_args implies_neg1
  | choose _ Implies_Neg2 = ignore_args implies_neg2
  | choose _ Implies_Pos = ignore_args implies_pos
  | choose _ Implies_Simplify = ignore_args rewrite_implies_simplify
  | choose _ ITE1 = ignore_args ite1
  | choose _ ITE2 = ignore_args ite2
  | choose _ ITE_Intro = ignore_args ite_intro
  | choose _ ITE_Neg1 = ignore_args ite_neg1
  | choose _ ITE_Neg2 = ignore_args ite_neg2
  | choose _ ITE_Pos1 = ignore_args ite_pos1
  | choose _ ITE_Pos2 = ignore_args ite_pos2
  | choose _ ITE_Simplify = ignore_args rewrite_ite_simplify
  | choose _ LA_Disequality = ignore_args la_disequality
  | choose _ LA_Generic = include_args la_generic
  | choose _ LA_RW_Eq = ignore_args la_rw_eq
  | choose _ LA_Tautology = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose _ LA_Totality = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose _ LIA_Generic = ignore_args lia_generic
  | choose _ LA_Mult_Pos = ignore_args la_mult_pos
  | choose _ LA_Mult_Neg = ignore_args la_mult_neg
  | choose _ Local_Input = ignore_args normalized_input (* ignore_args (refl "cvc5")*)
  | choose _ Minus_Simplify = ignore_args rewrite_minus_simplify
  | choose _ NLA_Generic = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose _ Normalized_Input = ignore_args normalized_input
  | choose _ Not_And = ignore_args not_and_rule
  | choose _ Not_Equiv1 = ignore_args not_equiv1
  | choose _ Not_Equiv2 = ignore_args not_equiv2
  | choose _ Not_Implies1 = ignore_args not_implies1
  | choose _ Not_Implies2 = ignore_args not_implies2
  | choose _ Not_ITE1 = ignore_args not_ite1
  | choose _ Not_ITE2 = ignore_args not_ite2
  | choose _ Not_Not = ignore_args not_not
  | choose _ Not_Or = ignore_args not_or_rule
  | choose _ Not_Simplify = ignore_args rewrite_not_simplify
  | choose _ Or = ignore_args or
  | choose _ Or_Neg = ignore_args or_neg_rule
  | choose _ Or_Pos = ignore_args or_pos_rule
  | choose _ Or_Simplify = ignore_args rewrite_or_simplify
  | choose _ Theory_Resolution2 = ignore_args theory_resolution2
  | choose _ Prod_Simplify = ignore_args prod_simplify
  | choose _ All_Simplify = ignore_args all_simplify
  | choose _ Qnt_Join = ignore_args qnt_join
  | choose _ Qnt_Rm_Unused = ignore_args qnt_rm_unused
  | choose _ Onepoint = ignore_args onepoint
  | choose _ Qnt_Simplify = ignore_args qnt_simplify
  | choose _ Refl = include_args refl
  | choose _ Resolution = ignore_args unit_res
  | choose _ Sko_Ex = include_context_ass_and_args sko_ex
  | choose _ Sko_Forall = include_context_ass_and_args sko_forall
  | choose _ Subproof = ignore_args subproof
  | choose _ Sum_Simplify = ignore_args sum_simplify
  | choose _ Tautological_Clause = ignore_args tautological_clause
  | choose _ Theory_Resolution = ignore_args unit_res
  | choose _ AC_Simp = ignore_args tmp_AC_rule
  | choose _ Bfun_Elim = ignore_args bfun_elim
  | choose _ Qnt_CNF = ignore_args qnt_cnf
  | choose _ Trans = ignore_args trans
  | choose _ Symm = ignore_args symm
  | choose _ Not_Symm = ignore_args not_symm
  | choose _ Reordering = ignore_args reordering
  | choose _ Tmp_Quantifier_Simplify = ignore_args qnt_simplify
  | choose _ Unary_Minus_Simplify = ignore_args rewrite_minus_simplify
  | choose ctxt (x as Other_Rule r) =
    (case get_alethe_tac r ctxt of
      NONE => ignore_args hole(*unsupported (string_of_alethe_rule x)*)
    | SOME a => include_step_args a)
  | choose _ Hole = ignore_args hole
  | choose _ RARE_Rewrite = ignore_args rare_rewrite

  | choose _ r = (@{print} ("unknown rule, using hole", r); ignore_args hole)
(*unsupported (string_of_alethe_rule r)*)

fun with_tracing rule method ctxt prems step_args context_assignment t args =
  let val _ = SMT_Replay_Methods.trace_goal ctxt rule prems step_args t
  in method ctxt prems step_args context_assignment t args end

fun method_for rule ctxt = with_tracing rule (choose (Context.Proof ctxt) (cvc5_rule_of rule)) ctxt

fun discharge ctxt [thm] t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    resolve_tac ctxt [thm] THEN_ALL_NEW (resolve_tac ctxt @{thms refl}))

end;
