(*  Title:      HOL/Tools/SMT/alethe_replay_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg

Proof method for replaying veriT proofs.
*)

signature ALETHE_REPLAY_METHODS =
sig

  (*
  TODO possibly add:
   Add Weakening
   xor1, xor2, not_xor1, not_xor2
   xor_pos1, xor_pos2, xor_neg1, xor_neg2
   div_simplify
   let, bind_let
   nary_elim
   eq_symmetric
  *)
  datatype alethe_rule =
   (*input: a repeated (normalized) assumption of  assumption of in a subproof*)
   Normalized_Input | Local_Input |
   (*Used to introduce skolem constants*)
   Definition |
   (*Subproof:*)
   Subproof |
   (*Quantifiers:*)
   Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Onepoint | Bind | Sko_Forall | Sko_Ex |
   (*Boolean Constants*)
   False | True |
   (*Conjunction:*)
   And | Not_And | And_Pos | And_Neg |
   (*Disjunction""*)
   Or | Or_Pos | Not_Or | Or_Neg |
   (*Implication:*)
   Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
   (*Equivalence:*)
   Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
   (*If-then-else:*)
   ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
   (*Equality:*)
   Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans |  Refl |  Cong |
   (*xor:*)
   Xor_Pos1 | Xor_Pos2 | Xor_Neg1 | Xor_Neg2 | Xor1 | Xor2 | Not_Xor1  | Not_Xor2 |
   (*Arithmetic:*)
   LA_Disequality | LA_Generic | LA_Tautology |  LIA_Generic | LA_Totality | LA_RW_Eq |
   NLA_Generic |  LA_Mult_Pos | LA_Mult_Neg | Poly_Simp | Poly_Simp_Rel |
   (*Resolution:*)
   Theory_Resolution | Resolution |
   (*Simplification Rules*)
   Bool_Simplify | Or_Simplify | Not_Simplify | And_Simplify | Equiv_Simplify |
   Implies_Simplify | Connective_Def | Minus_Simplify | Unary_Minus_Simplify | Comp_Simplify |
   Eq_Simplify | ITE_Simplify | Sum_Simplify | Prod_Simplify | Div_Simplify | All_Simplify | RARE_Rewrite |
   Qnt_Simplify | Not_Not | Tautological_Clause | Duplicate_Literals | Distinct_Elim |
   Miniscope_Distribute | Miniscope_Split | Miniscope_ITE |
   AC_Simp | ACI_Simp |
   (*Extended rules*)
   Symm | Not_Symm | Reordering | Shuffle | Tmp_Quantifier_Simplify | Contraction | 
   And_Intro |
   (*Other Rules*)
   Other_Rule of string |
   Hole | Trust |
   (*Temporary rules, that the veriT developers want to remove:*)
   Bfun_Elim |
   Qnt_CNF |
   (*For compression*)
   Theory_Resolution2 |
   (*Unsupported rule*)
   Unsupported

  val requires_subproof_assms : string list -> string -> bool
  val requires_local_input: string list -> string -> bool

  val string_of_alethe_rule: alethe_rule -> string

  type alethe_tac_step_args = Proof.context -> thm list -> term list -> term -> thm
  type alethe_tac_context_args = Proof.context -> thm list -> term list -> term -> thm
  type alethe_tac_args = Proof.context -> thm list -> term -> Alethe_Node.tactic_args option -> thm
  type alethe_tac_context_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
  type alethe_tac_step_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
  type alethe_tac = Proof.context -> thm list -> term -> thm

  val bind: alethe_tac_context_args
  val and_rule: alethe_tac
  val and_neg_rule: alethe_tac
  val and_pos: alethe_tac_args
  val rewrite_and_simplify: alethe_tac
  val rewrite_bool_simplify: alethe_tac
  val rewrite_comp_simplify: alethe_tac
  val rewrite_minus_simplify: alethe_tac
  val rewrite_not_simplify: alethe_tac
  val rewrite_eq_simplify: alethe_tac
  val rewrite_equiv_simplify: alethe_tac
  val rewrite_implies_simplify: alethe_tac
  val rewrite_or_simplify: alethe_tac
  val cong: alethe_tac_args
  val rewrite_connective_def: alethe_tac
  val duplicate_literals: alethe_tac
  val distinct_elim: alethe_tac
  val eq_congruent: alethe_tac
  val eq_congruent_pred: alethe_tac
  val eq_reflexive: alethe_tac
  val eq_transitive: alethe_tac
  val equiv1: alethe_tac
  val equiv2: alethe_tac
  val equiv_neg1: alethe_tac
  val equiv_neg2: alethe_tac
  val equiv_pos1: alethe_tac
  val equiv_pos2: alethe_tac
  val xor_pos1: alethe_tac
  val xor_pos2: alethe_tac
  val xor_neg1: alethe_tac
  val xor_neg2: alethe_tac
  val xor1: alethe_tac
  val xor2: alethe_tac
  val not_xor1: alethe_tac
  val not_xor2: alethe_tac
  val false_rule: alethe_tac
  val forall_inst: alethe_tac_args
  val implies_rules: alethe_tac
  val implies_neg1: alethe_tac
  val implies_neg2: alethe_tac
  val implies_pos: alethe_tac
  val ite1: alethe_tac
  val ite2: alethe_tac
  val ite_intro: alethe_tac
  val ite_neg1: alethe_tac
  val ite_neg2: alethe_tac
  val ite_pos1: alethe_tac
  val ite_pos2: alethe_tac
  val rewrite_ite_simplify: alethe_tac
  val la_disequality: alethe_tac
  val la_generic: alethe_tac_args
  val la_rw_eq: alethe_tac
  val lia_generic: alethe_tac
  val la_mult_pos: alethe_tac
  val la_mult_neg: alethe_tac
  val poly_simp: alethe_tac
  val poly_simp_rel: alethe_tac
  val refl: alethe_tac_args
  val normalized_input: alethe_tac
  val not_and_rule: alethe_tac
  val not_equiv1: alethe_tac
  val not_equiv2: alethe_tac
  val not_implies1: alethe_tac
  val not_implies2: alethe_tac
  val not_ite1: alethe_tac
  val not_ite2: alethe_tac
  val not_not: alethe_tac
  val not_or_rule: alethe_tac
  val or: alethe_tac
  val or_neg_rule: alethe_tac_args
  val or_pos_rule: alethe_tac
  val theory_resolution2: alethe_tac
  val prod_simplify: alethe_tac
  val div_simplify: alethe_tac
  val qnt_join: alethe_tac
  val qnt_rm_unused: alethe_tac
  val onepoint: alethe_tac
  val qnt_simplify: alethe_tac
  val all_simplify: alethe_tac
  val rare_rewrite: alethe_tac
  val unit_res: alethe_tac
  val sko_ex: alethe_tac_context_args_and_arg
  val sko_forall: alethe_tac_context_args_and_arg
  val subproof: alethe_tac
  val sum_simplify: alethe_tac
  val tautological_clause: alethe_tac
  val AC_rule: alethe_tac
  val ACI_rule: alethe_tac
  val bfun_elim: alethe_tac
  val qnt_cnf: alethe_tac
  val trans: alethe_tac
  val strict_trans: alethe_tac (*assumes assumptions in the right order*)
  val symm: alethe_tac
  val not_symm: alethe_tac
  val reordering: alethe_tac
  val shuffle: alethe_tac_step_args_and_arg
  val contraction: alethe_tac
  val miniscope_distribute: alethe_tac
  val miniscope_split: alethe_tac
  val miniscope_ITE: alethe_tac
  val and_intro: alethe_tac
  val trust: alethe_tac

  (*Extension to declare new alethe rules*)
  val declare_alethe_rule:  string -> alethe_tac_step_args -> Context.generic -> Context.generic
  val rm_alethe_rule: string -> Context.generic -> Context.generic
  val get_alethe_tac: string -> Context.generic -> alethe_tac_step_args option
  val print_alethe_tac: Context.generic -> Pretty.T

  (*Useful lifting of tactics*)
  val REPEAT_CHANGED: ('a -> tactic) -> 'a -> tactic
  val TRY': ('a -> tactic) -> 'a -> tactic

  val simplify_tac: Proof.context -> thm list -> int -> tactic
  val replay_error: Proof.context -> string -> alethe_rule -> thm list -> term list -> term -> 'a

end;


structure Alethe_Replay_Methods: ALETHE_REPLAY_METHODS =
struct

open SMT_Config
fun debug_msg ctxt = alethe_debug_msg ctxt "alethe_replay_methods"
fun debug_msg_tac' ctxt verbosity str = K (SMT_Config.alethe_debug_msg_tac ctxt "alethe_replay_methods" verbosity str)

type alethe_tac_step_args = Proof.context -> thm list -> term list -> term -> thm
type alethe_tac_context_args = Proof.context -> thm list -> term list -> term -> thm
type alethe_tac_args = Proof.context -> thm list -> term -> Alethe_Node.tactic_args option -> thm
type alethe_tac_context_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
type alethe_tac_step_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
type alethe_tac = Proof.context -> thm list -> term -> thm

datatype alethe_rule =
   (*normalized_input: a repeated (normalized) assumption of  assumption of in a subproof*)
   Normalized_Input | Local_Input |
   (*Used to introduce skolem constants*)
   Definition |
   (*Subproof:*)
   Subproof |
   (*Quantifiers:*)
   Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Onepoint | Bind | Sko_Forall | Sko_Ex |
   (*Boolean Constants*)
   False | True |
   (*Conjunction:*)
   And | Not_And | And_Pos | And_Neg |
   (*Disjunction""*)
   Or | Or_Pos | Not_Or | Or_Neg |
   (*Implication:*)
   Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
   (*Equivalence:*)
   Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
   (*If-then-else:*)
   ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
   (*Equality:*)
   Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans |  Refl |  Cong |
   (*xor:*)
   Xor_Pos1 | Xor_Pos2 | Xor_Neg1 | Xor_Neg2 | Xor1 | Xor2 | Not_Xor1  | Not_Xor2 |
   (*Arithmetic:*)
   LA_Disequality | LA_Generic | LA_Tautology |  LIA_Generic | LA_Totality | LA_RW_Eq |
   NLA_Generic |  LA_Mult_Pos | LA_Mult_Neg | Poly_Simp | Poly_Simp_Rel |
   (*Resolution:*)
   Theory_Resolution | Resolution |
   (*Simplification Rules*)
   Bool_Simplify | Or_Simplify | Not_Simplify | And_Simplify | Equiv_Simplify |
   Implies_Simplify | Connective_Def | Minus_Simplify | Unary_Minus_Simplify | Comp_Simplify |
   Eq_Simplify | ITE_Simplify | Sum_Simplify | Prod_Simplify | Div_Simplify | All_Simplify | RARE_Rewrite |
   Qnt_Simplify | Not_Not | Tautological_Clause | Duplicate_Literals | Distinct_Elim | 
   AC_Simp | ACI_Simp |
   (*Extended rules*)
   Symm | Not_Symm | Reordering | Shuffle | Tmp_Quantifier_Simplify | Contraction |
   Miniscope_Distribute | Miniscope_Split | Miniscope_ITE |
   And_Intro |
   (*Other Rules*)
   Other_Rule of string |
   Hole | Trust |
   (*Temporary rules, that the veriT developers want to remove:*)
   Bfun_Elim |
   Qnt_CNF |
   (*For compression*)
   Theory_Resolution2 |
   (*Unsupported rule*)
   Unsupported



fun string_of_alethe_rule Bind = "Bind"
  | string_of_alethe_rule Cong = "Cong"
  | string_of_alethe_rule Refl = "Refl"
  | string_of_alethe_rule Equiv1 = "Equiv1"
  | string_of_alethe_rule Equiv2 = "Equiv2"
  | string_of_alethe_rule Equiv_pos1 = "Equiv_pos1"
  | string_of_alethe_rule Equiv_pos2 = "Equiv_pos2"
  | string_of_alethe_rule Equiv_neg1 = "Equiv_neg1"
  | string_of_alethe_rule Equiv_neg2 = "Equiv_neg2"
  | string_of_alethe_rule Sko_Forall = "Sko_Forall"
  | string_of_alethe_rule Sko_Ex = "Sko_Ex"
  | string_of_alethe_rule Eq_Reflexive = "Eq_Reflexive"
  | string_of_alethe_rule Theory_Resolution = "Theory_Resolution"
  | string_of_alethe_rule Theory_Resolution2 = "Theory_Resolution2"
  | string_of_alethe_rule Forall_Inst = "forall_inst"
  | string_of_alethe_rule Or = "Or"
  | string_of_alethe_rule Not_Or = "Not_Or"
  | string_of_alethe_rule Resolution = "Resolution"
  | string_of_alethe_rule Eq_Congruent = "eq_congruent"
  | string_of_alethe_rule Trans = "trans"
  | string_of_alethe_rule False = "false"
  | string_of_alethe_rule And = "and"
  | string_of_alethe_rule And_Pos = "and_pos"
  | string_of_alethe_rule Not_And = "not_and"
  | string_of_alethe_rule And_Neg = "and_neg"
  | string_of_alethe_rule Or_Pos = "or_pos"
  | string_of_alethe_rule Or_Neg = "or_neg"
  | string_of_alethe_rule AC_Simp = "ac_simp"
  | string_of_alethe_rule ACI_Simp = "aci_simp"
  | string_of_alethe_rule Not_Equiv1 = "not_equiv1"
  | string_of_alethe_rule Not_Equiv2 = "not_equiv2"
  | string_of_alethe_rule Xor_Pos1 = "xor_pos1"
  | string_of_alethe_rule Xor_Pos2 = "xor_pos2"
  | string_of_alethe_rule Xor_Neg1 = "xor_neg1"
  | string_of_alethe_rule Xor_Neg2 = "xor_neg2"
  | string_of_alethe_rule Xor1 = "xor1"
  | string_of_alethe_rule Xor2 = "xor2"
  | string_of_alethe_rule Not_Xor1 = "not_xor1"
  | string_of_alethe_rule Not_Xor2 = "not_xor2"
  | string_of_alethe_rule Not_Implies1 = "not_implies1"
  | string_of_alethe_rule Not_Implies2 = "not_implies2"
  | string_of_alethe_rule Implies_Neg1 = "implies_neg1"
  | string_of_alethe_rule Implies_Neg2 = "implies_neg2"
  | string_of_alethe_rule Implies = "implies"
  | string_of_alethe_rule Bfun_Elim = "bfun_elim"
  | string_of_alethe_rule ITE1 = "ite1"
  | string_of_alethe_rule ITE2 = "ite2"
  | string_of_alethe_rule Not_ITE1 = "not_ite1"
  | string_of_alethe_rule Not_ITE2 = "not_ite2"
  | string_of_alethe_rule ITE_Pos1 = "ite_pos1"
  | string_of_alethe_rule ITE_Pos2 = "ite_pos2"
  | string_of_alethe_rule ITE_Neg1 = "ite_neg1"
  | string_of_alethe_rule ITE_Neg2 = "ite_neg2"
  | string_of_alethe_rule ITE_Intro = "ite_intro"
  | string_of_alethe_rule LA_Disequality = "la_disequality"
  | string_of_alethe_rule LA_Generic = "la_generic"
  | string_of_alethe_rule LIA_Generic = "lia_generic"
  | string_of_alethe_rule LA_Tautology = "la_tautology"
  | string_of_alethe_rule LA_RW_Eq = "la_rw_eq"
  | string_of_alethe_rule LA_Totality = "LA_Totality"
  | string_of_alethe_rule NLA_Generic = "nla_generic"
  | string_of_alethe_rule LA_Mult_Pos = "la_mult_pos"
  | string_of_alethe_rule LA_Mult_Neg = "la_mult_neg"
  | string_of_alethe_rule Poly_Simp = "poly_simp"
  | string_of_alethe_rule Poly_Simp_Rel = "poly_simp_rel"
  | string_of_alethe_rule Eq_Transitive = "eq_transitive"
  | string_of_alethe_rule Qnt_Rm_Unused = "qnt_remove_unused"
  | string_of_alethe_rule Onepoint = "onepoint"
  | string_of_alethe_rule Qnt_Join = "qnt_join"
  | string_of_alethe_rule Eq_Congruent_Pred = "eq_congruent_pred"
  | string_of_alethe_rule Normalized_Input = Alethe_Proof.normalized_input_rule
  | string_of_alethe_rule Local_Input = Alethe_Proof.local_input_rule
  | string_of_alethe_rule Subproof = "subproof"
  | string_of_alethe_rule Bool_Simplify = "bool_simplify"
  | string_of_alethe_rule Equiv_Simplify = "equiv_simplify"
  | string_of_alethe_rule Eq_Simplify = "eq_simplify"
  | string_of_alethe_rule Not_Simplify = "not_simplify"
  | string_of_alethe_rule And_Simplify = "and_simplify"
  | string_of_alethe_rule Or_Simplify = "or_simplify"
  | string_of_alethe_rule ITE_Simplify = "ite_simplify"
  | string_of_alethe_rule Implies_Simplify = "implies_simplify"
  | string_of_alethe_rule Connective_Def = "connective_def"
  | string_of_alethe_rule Minus_Simplify = "minus_simplify"
  | string_of_alethe_rule Sum_Simplify = "sum_simplify"
  | string_of_alethe_rule Prod_Simplify = "prod_simplify"
  | string_of_alethe_rule Div_Simplify = "div_simplify"
  | string_of_alethe_rule All_Simplify = "all_simplify"
  | string_of_alethe_rule RARE_Rewrite = "rare_rewrite"
  | string_of_alethe_rule Comp_Simplify = "comp_simplify"
  | string_of_alethe_rule Qnt_Simplify = "qnt_simplify"
  | string_of_alethe_rule Symm = "symm"
  | string_of_alethe_rule Not_Symm = "not_symm"
  | string_of_alethe_rule Reordering = "reordering"
  | string_of_alethe_rule Shuffle = "shuffle"
  | string_of_alethe_rule Contraction = "contraction"
  | string_of_alethe_rule Miniscope_Distribute = "miniscope_distribute"
  | string_of_alethe_rule Miniscope_Split = "miniscope_split"
  | string_of_alethe_rule Miniscope_ITE = "miniscope_ITE"
  | string_of_alethe_rule And_Intro = "and_intro"
  | string_of_alethe_rule Not_Not = Alethe_Proof.not_not_rule
  | string_of_alethe_rule Tautological_Clause = "tautology"
  | string_of_alethe_rule Duplicate_Literals = Alethe_Proof.contract_rule
  | string_of_alethe_rule Distinct_Elim = "distinct_elim"
  | string_of_alethe_rule Qnt_CNF = "qnt_cnf"
  | string_of_alethe_rule Trust = "trust"
  | string_of_alethe_rule (Other_Rule r) = r
  | string_of_alethe_rule r = "Unknown rule: " ^ \<^make_string> r

fun debug_rule_tac' ctxt verbosity rule str = debug_msg_tac' ctxt verbosity ("Reconstruct " ^ (string_of_alethe_rule rule) ^ ": " ^ str)

(** Context Extension for Rules **)
(*We currently do not distinguish between the extension required for each solver. Maybe later
it will be needed.*)
type alethe_rule_ext = {rules: (string * alethe_tac_step_args) list}

fun mk_alethe_rule_ext rules : alethe_rule_ext = 
   {rules=rules}

val empty_data = mk_alethe_rule_ext []

fun merge_data ({rules=rules1}:alethe_rule_ext, {rules=rules2}:alethe_rule_ext) : alethe_rule_ext =
  mk_alethe_rule_ext (AList.merge (op =) (fn _ => true) (rules1, rules2))

structure Data = Generic_Data
(
  type T = alethe_rule_ext
  val empty = empty_data
  val merge = merge_data
)

fun declare_alethe_rule rule tac context =
  let
    val {rules} = Data.get context
  in
    Data.map
      (K (mk_alethe_rule_ext (AList.update (op =) (rule, tac) rules)))
      context
  end

fun rm_alethe_rule stgy context =
  let
    val {rules} = Data.get context
  in
    Data.map
      (K (mk_alethe_rule_ext (AList.delete (op =) stgy rules)))
      context
  end

fun get_alethe_tac rule context =
  let
    val {rules} = Data.get context
  in
    AList.lookup (op =) rules rule
  end

fun print_alethe_tac context =
  let
    val {rules} = Data.get context
  in
    rules
    |> map (fn (a, b) => a ^ "->" ^ @{make_string} b)
    |> map Pretty.str
    |> Pretty.big_list "Declared alethe rules:\n"
  end


(** Tactics for Reconstruction **)
(* General Notes:
t is usually the goal as a term
prems are usually the premises of the rule as a list of theorems
*)

fun replay_error ctxt msg rule thms args t =
  SMT_Replay_Methods.replay_error ctxt msg (string_of_alethe_rule rule) thms args t

(* utility function *)                            

fun eqsubst_all ctxt thms =
   K ((REPEAT o HEADGOAL) (EqSubst.eqsubst_asm_tac ctxt [0] thms))
   THEN' K ((REPEAT o HEADGOAL) (EqSubst.eqsubst_tac ctxt [0] thms))

fun simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.asm_full_simp_tac

(*This is a weaker simplification form. It is weaker, but is also less likely to loop*)
fun partial_simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.full_simp_tac

fun partial_simplify_tac_with_cong cong simprocs ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.add_cong cong
  |> (fn ctxt => ctxt addsimprocs simprocs)
  |> Simplifier.full_simp_tac

(* sko_forall requires the assumptions to be able to prove the equivalence in case of double
skolemization. See comment below. *)
fun requires_subproof_assms _ t =
  member (op =) ["sko_forall", "sko_ex", "refl"] t

fun requires_local_input _ t =
  member (op =) [Alethe_Proof.local_input_rule] t

val try_provers = SMT_Replay_Methods.try_provers

fun TRY' tac = fn i => TRY (tac i)
fun REPEAT' tac = fn i => REPEAT (tac i)
fun REPEAT1' tac = fn i => REPEAT1 (tac i)
fun REPEAT_CHANGED tac = fn i => REPEAT (CHANGED (tac i))
fun REPEAT_DETERM_N' k tac = fn i => REPEAT_DETERM_N k (tac i)

fun extract_single_premise rule ctxt thm t =
  case thm of
   [thm] => thm |
   thms => replay_error ctxt "Expected only one premise" rule thms [] t


(* Bind *)

(*The bind rule is non-obvious due to the handling of quantifiers:
  "\<And>x y a. x = y ==> (\<forall>b. P a b x) \<longleftrightarrow> (\<forall>b. P' a b y)"
  ------------------------------------------------------
            \<forall>a. (\<forall>b x. P a b x) \<longleftrightarrow> (\<forall>b y. P' a b y)
is a valid application.*)

val bind_thms =
  [@{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<forall>x. P x) = (\<forall>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<exists>x. P x) = (\<exists>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<exists>x. P x = Q x)\<close> by blast},
   @{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<forall>x. P x = Q x)\<close> by blast}]

val bind_thms_same_name =
  [@{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<forall>x. P x) = (\<forall>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>x. P x) = (\<exists>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>x. P x = Q x)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<forall>x. P x = Q x)\<close> by blast}]

fun extract_quantified_names_q (_ $ Abs (name, _, t)) =
   apfst (curry (op ::) name) (extract_quantified_names_q t)
  | extract_quantified_names_q t = ([], t)

fun extract_forall_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, ty, t)) =
   (name,  ty) :: (extract_forall_quantified_names_q t)
  | extract_forall_quantified_names_q _ = []

val extract_quantified_names_ba =
  SMT_Replay_Methods.dest_prop
  #> extract_quantified_names_q
  ##> HOLogic.dest_eq
  ##> fst
  ##> extract_quantified_names_q
  ##> fst

val extract_quantified_names =
  extract_quantified_names_ba
  #> (op @)

fun extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_exists_quantified_names_q t)
  | extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_exists_quantified_names_q t)
  | extract_all_forall_exists_quantified_names_q (t $ u) =
      extract_all_forall_exists_quantified_names_q t @ extract_all_forall_exists_quantified_names_q u
  | extract_all_forall_exists_quantified_names_q _ = []

val to_upper = raw_explode #> map Symbol.to_ascii_upper #> implode;

val extract_bind_names =
   HOLogic.dest_eq
   #> apply2 (fn (Free (name, _)) => name |> to_upper | _ => raise Fail "could not extract bound variable names in reconstruction of bind rule")

fun ignore_new_bound_var [] = [] |
    ignore_new_bound_var (Free (_, _) :: xs) = ignore_new_bound_var xs |
    ignore_new_bound_var (t :: xs) = t::ignore_new_bound_var xs

fun combine_quant ctxt ((n1, n2) :: bounds) (n1' :: formula) =
    TRY' (if n1 = n1'
     then if n1 <> n2
       then
         resolve_tac ctxt bind_thms
         THEN' TRY'(resolve_tac ctxt [@{thm refl}])
         THEN' combine_quant ctxt bounds formula
       else resolve_tac ctxt bind_thms_same_name THEN' combine_quant ctxt bounds formula
     else resolve_tac ctxt @{thms allI} THEN' combine_quant ctxt ((n1, n2) :: bounds) formula)
  | combine_quant _ _ _ = K all_tac


fun bind_quants ctxt args t =
  combine_quant ctxt 
  (map extract_bind_names (ignore_new_bound_var (map HOLogic.dest_Trueprop args)))
    (extract_quantified_names t |> map to_upper)

fun generalize_prems_q [] prems = prems
  | generalize_prems_q (_ :: quants) prems =
      generalize_prems_q quants (@{thm spec} OF [prems])

fun generalize_prems t = generalize_prems_q (fst (extract_quantified_names_ba t))

fun bind ctxt [prems] context_ass t =
 (SMT_Replay_Methods.prove ctxt t (fn _ =>
   bind_quants ctxt context_ass t
   THEN' TRY' (SOLVED' (resolve_tac ctxt [generalize_prems t prems]
   THEN_ALL_NEW TRY' (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms refl})))))
 | bind ctxt thms _ t = replay_error ctxt "invalid bind application" Bind thms [] t


(* Congruence/Refl *)

fun get_solver_name (SOME (Solver_Name name)) = name |
  get_solver_name _ = "unkown solver name"  

fun cong ctxt thms t args = try_provers (get_solver_name args) ctxt
    (string_of_alethe_rule Cong) [
  ("basic", SMT_Replay_Methods.cong_basic ctxt thms),
  ("unfolding then reflexivity", SMT_Replay_Methods.cong_unfolding_trivial ctxt thms),
  ("unfolding then auto", SMT_Replay_Methods.cong_unfolding_first ctxt thms),
  ("full", SMT_Replay_Methods.cong_full ctxt thms)] thms [] t

fun refl ctxt thm t args = (
  (case find_first (fn thm => t = Thm.full_prop_of thm) thm of
      SOME thm => thm
    | NONE =>
        (case try (fn t => SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}) t of
          NONE => cong ctxt thm t args
        | SOME thm => thm))
)
(* Instantiation *)

local
fun dropWhile _ [] = []
  | dropWhile f (x :: xs) = if f x then dropWhile f xs else x :: xs
in

fun forall_inst ctxt _ t (SOME (Insts insts)) =
  let
    fun instantiate_and_solve i ({context = ctxt, prems = [prem], ...}: Subgoal.focus) =
        let
          val t = Thm.prop_of prem
          val quants = t
            |> SMT_Replay_Methods.dest_prop
            |> extract_forall_quantified_names_q
          val insts = map (Symtab.lookup insts o fst) (rev quants)
            |> dropWhile (curry (op =) NONE)
            |> rev
          fun option_map _ NONE = NONE
            | option_map f (SOME a) = SOME (f a)
          fun instantiate_with inst prem =
            Drule.infer_instantiate' ctxt [NONE, inst] @{thm spec} OF [prem]
          val inst_thm =
            fold instantiate_with
              (map (option_map (Thm.cterm_of ctxt)) insts)
              prem
        in
           ((*  (K (print_tac ctxt "sd 0")) THEN'  *)Method.insert_tac ctxt [inst_thm]
           (* THEN' (K (print_tac ctxt "sd 0")) *)
           THEN' TRY' (fn i => assume_tac ctxt i)
           (* THEN' (K (print_tac ctxt "sd 1")) *)
           THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute ac_simps})
           (* THEN' (K (print_tac ctxt "sd 2")) *)
           THEN' TRY' (blast_tac ctxt)) i
        end
     | instantiate_and_solve _ ({context = ctxt, prems = thms, ...}: Subgoal.focus) =
         replay_error ctxt "invalid application" Forall_Inst thms [] t
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      match_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}]]
      THEN' (fn i => Subgoal.FOCUS (instantiate_and_solve i) ctxt i))
  end |
 forall_inst _ _ _ _ = raise Fail ""

end


(* Or *)

fun or _ (thm :: _) _ = thm
  | or ctxt thms t = replay_error ctxt "invalid bind application" Or thms [] t


(* Implication *)

val implies_pos_thm =
  [@{lemma \<open>\<not>(A \<longrightarrow> B) \<or> \<not>A \<or> B\<close> by blast}]

fun implies_pos ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt implies_pos_thm)

(* Skolemization *)
local
  fun split _ [] = ([], [])
    | split f (a :: xs) =
        split f xs
        |> (if f a then apfst (curry (op ::) a) else apsnd (curry (op ::) a))
in
fun extract_rewrite_rule_assumption _ thms =
  let
    fun is_rewrite_rule thm =
      (case Thm.prop_of thm of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Free(_, _)) => true
      | _ => false)
    fun is_context_rule thm =
      (case Thm.prop_of thm of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Free(_, _) $ Free(_, _)) => true
      | _ => false)
    val (ctxt_eq, other) =
      thms
      |> split is_context_rule
    val (rew, other) =
      other
      |> split is_rewrite_rule
  in
    (ctxt_eq, rew, other)
  end
end
(*
Without compression, we have to rewrite skolems only once. However, it can happen than the same
skolem constant is used multiple times with a different name under the forall.

For strictness, we use the multiple rewriting only when compressing is activated.
*)
local
  fun rewrite_all_skolems ctxt_eq thm_indirect ctxt ((_,SOME thm) :: thms) =
     let
       val rewrite_sk_thms =
         List.mapPartial (fn tm => SOME (tm OF [thm]) handle THM _ => NONE) thm_indirect
       val multiple_rew = if SMT_Config.compress_verit_proofs ctxt then REPEAT_CHANGED else fn x => x
     in
       multiple_rew (EqSubst.eqsubst_tac ctxt [0] rewrite_sk_thms
         (* THEN' K (print_tac ctxt "In rewrite_all_skolems")*)
         THEN' SOLVED' (K (HEADGOAL (partial_simplify_tac ctxt (ctxt_eq @ @{thms eq_commute}))))
         (*THEN' K (print_tac ctxt "In rewrite_all_skolems 2")*))
       THEN' rewrite_all_skolems ctxt_eq thm_indirect ctxt thms
         (*THEN' K (print_tac ctxt "In rewrite_all_skolems 3")*)

     end
   | rewrite_all_skolems ctxt_eq thm_indirect ctxt ((_,NONE) :: thms) =
       rewrite_all_skolems ctxt_eq thm_indirect ctxt thms
   | rewrite_all_skolems _ _ _ [] = K (all_tac)

   fun extract_var_name (thm :: thms) =
       let val name = Thm.concl_of thm
         |> SMT_Replay_Methods.dest_prop
         |> HOLogic.dest_eq
         |> fst
         |> (fn Const(_,_) $ Abs(name, _, _) => [(name,@{thm sym} OF [thm])]
             | _ => [])
       in name :: extract_var_name thms end
    | extract_var_name [] = []

fun skolem_tac extractor thm1 thms1 ctxt prems context_ass (decl:string list * string list) t =
  let
   
  (*                              
    val (context_ass_thm,_) = Assumption.add_assumes (map (Thm.cterm_of ctxt) context_ass) ctxt

   val context_ass_thm_sym = map (fn x => @{thm sym} OF [x]) context_ass_thm
    val _ = @{print}("context_ass_thm_sym",context_ass_thm_sym))*)

(*
lemma alethe_sko_forall: \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma alethe_sko_forall': \<open>P (SOME x. \<not>P x) = A \<Longrightarrow> (\<forall>x. P x) = A\<close>
  by (subst alethe_sko_forall)

lemma alethe_sko_forall'': \<open>B = A \<Longrightarrow> (SOME x. P x) = A \<equiv> (SOME x. P x) = B\<close>
  by auto

lemma alethe_sko_forall_indirect: \<open>x = (SOME x. \<not>P x) \<Longrightarrow> (\<forall>x. P x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma alethe_sko_forall_indirect2:
    \<open>x = (SOME x. \<not>P x) \<Longrightarrow> (\<And>x :: 'a. (P x = P' x)) \<Longrightarrow>(\<forall>x. P' x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto*)
(*
    val _ = @{print}("thm1",thm1)
    val _ = @{print}("thms1",thms1)
    val _ = @{print}("prems",prems)
    val _ = @{print}("context_ass",context_ass)

    val _ = @{print}("t",t)
    val _ = @{print}("decl",decl)
*)
    val (ctxt_eq, rew, other) = extract_rewrite_rule_assumption ctxt prems
(*
    val _ = @{print}("ctxt_eq",ctxt_eq)

    val _ = @{print}("rew",rew)
    val _ = @{print}("other",other)
*)
    fun ordered_definitions () =
      let
        val var_order = extractor t
        (*val _ = @{print}("var_order",var_order)*)

        val thm_names_with_var = extract_var_name rew |> flat
        (*val _ = @{print}("thm_names_with_var",thm_names_with_var)*)

      in map (fn v => (v, AList.lookup (op =) thm_names_with_var v)) var_order end
    (*veriT produces longer terms for skolem function like
    SK1 = eps x. P x
    SK2 = eps y. Q x (eps x. P x)

    instead of the shorter:
    SK1 = eps x. P x
    SK2 = eps y. Q x SK1

    When the option --proof-with-sharing is activated, we take care of this during parsing, but
    if not (and especially if using check_smt), we need to fold SK1 into SK2. As we cannot know
    whether the option was used, we always rewrite.
    *)
    fun fold_definition [] _ = []
      | fold_definition ((v, NONE) :: xs) acc = (v, NONE) :: fold_definition xs acc
      | fold_definition ((v, SOME thm) :: xs) acc = 
        let 
          val acc' = (thm COMP @{thm eq_commute[THEN iffD1]}) :: acc
          val simp_ctxt =
           ctxt
           |> empty_simpset
           |> put_simpset HOL_basic_ss
           |> (fn ctxt => ctxt addsimps acc)
        in ((v, SOME (Simplifier.full_simplify simp_ctxt thm)) :: fold_definition xs acc') end
    val defs = fold_definition (ordered_definitions ()) []
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      rewrite_all_skolems ctxt_eq thms1 ctxt defs

      THEN' ((*((resolve_tac ctxt @{thms refl}) THEN' K (print_tac ctxt "sko 0")))
      ORELSE' 
      (
*) (*K (print_tac ctxt "sko 2")
      THEN'*) TRY' (eqsubst_all ctxt (map (fn thm => thm RS sym) other))
      THEN_ALL_NEW TRY' (resolve_tac ctxt @{thms refl})
      THEN' K (unfold_tac ctxt ctxt_eq)
      THEN' TRY' (partial_simplify_tac ctxt (@{thms eq_commute}))))
  end
in

(*forall a b c d e f. P(a,b,c,d,e,f)

extract_all_forall_exists_quantified_names_q: returns a b c d e f

The context has the definitions of the skolems
Then, they are ordered
THEN' rewrite_all_skolems thm2 ctxt (ordered_definitions ())

We should be able to stop there:
but skolems can appear in each other, they might be folded in or only partially
choices in choices
in cvc5: order guaranteed to be respected, no choice inside choice.

If 
      THEN' (eqsubst_all ctxt (map (fn thm => thm RS sym) other))
unfolding all things that might be in the context (should not happen but never sure)
if skolem_forall closes subproof that is in another subproof.

Then, we hope that everything works out:
      THEN_ALL_NEW TRY' (resolve_tac ctxt @{thms refl})

If it doesn't work we brute force it by unfolding everything. And then use the simplifier:
      THEN' K (unfold_tac ctxt ctxt_eq)
Mathias does not remember a case where this happens.

  type alethe_tac_args = Proof.context -> thm list -> term -> Alethe_Node.tactic_args -> thm

*)
fun sko_forall ctxt prems context_ass t (SOME (Sko_Def_Prems decl)) =
  skolem_tac extract_all_forall_exists_quantified_names_q @{thm alethe_sko_forall_indirect}
    @{thms alethe_sko_forall_indirect2 alethe_sko_ex_indirect2} ctxt prems context_ass decl t

fun sko_ex ctxt prems context_ass t (SOME (Sko_Def_Prems decl)) =
  skolem_tac extract_all_forall_exists_quantified_names_q @{thm alethe_sko_ex_indirect}
    @{thms alethe_sko_ex_indirect2 alethe_sko_forall_indirect2} ctxt prems context_ass decl t

end

fun eq_reflexive ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}

local
  fun not_not_prove ctxt _ =
    K (unfold_tac ctxt @{thms not_not})
    THEN' match_tac ctxt @{thms alethe_or_simplify_1}

  fun duplicate_literals_prove ctxt prems =
    Method.insert_tac ctxt prems
    THEN' match_tac ctxt @{thms ccontr}
    THEN' K (unfold_tac ctxt @{thms de_Morgan_disj not_not})
    THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
    THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
    THEN' REPEAT' (ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))

  fun tautological_clause_prove ctxt _ =
    match_tac ctxt @{thms alethe_or_neg}
    THEN' K (unfold_tac ctxt @{thms not_not disj_assoc[symmetric]})
    THEN' TRY' (match_tac ctxt @{thms notE} THEN_ALL_NEW assume_tac ctxt)

  val theory_resolution2_lemma = @{lemma \<open>a \<Longrightarrow> a = b \<Longrightarrow> b\<close> by blast}

in

fun prove_abstract abstracter tac ctxt thms t =
  let
    val _ = debug_msg ctxt low (fn () => \<^print> ("Current goal is abstracted"))

    val thms = map (Conv.fconv_rule Thm.eta_long_conversion) thms
    val _ = (if (length thms = 0) then () else debug_msg ctxt middle (fn () => \<^print> ("Premises after ",thms)))

    val t' = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("Current goal (term) as thm before abstraction",t'))
    val (_, t2) = Logic.dest_equals (Thm.prop_of t')
    val thm =
      (SMT_Replay_Methods.prove_abstract ctxt thms t2 tac (
        fold_map (abstracter o SMT_Replay_Methods.dest_thm) thms ##>>
        abstracter (SMT_Replay_Methods.dest_prop t2)))
      (*handle (ERROR _) => (@{print}("here");raise (Fail "")*)

    val _ = debug_msg ctxt middle (fn () => \<^print> ("Current goal (term) as thm after abstraction",thm))

  in
    @{thm alethe_Pure_trans} OF [t', thm]
  end

val not_not = prove_abstract SMT_Replay_Methods.abstract_bool_shallow not_not_prove

val tautological_clause =
  prove_abstract SMT_Replay_Methods.abstract_bool_shallow tautological_clause_prove

val duplicate_literals =
  prove_abstract SMT_Replay_Methods.abstract_bool_shallow duplicate_literals_prove

val unit_res = prove_abstract SMT_Replay_Methods.abstract_bool_shallow SMT_Replay_Methods.prop_tac

(*match_instantiate does not work*)
fun theory_resolution2 ctxt prems t =
  SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt [theory_resolution2_lemma OF prems])

end

(*TODO: Check if this is still needed*)
(*Modulo implicit reordering*)
fun is_same_assms_eq_ac (Abs (_, _,  u)) (Abs (_, _, u')) = 
     is_same_assms_eq_ac u u' (*the name cannot be relevant due to implicit eta-contraction*)
  | is_same_assms_eq_ac (Free (var, _)) (Free (var', _)) =
    (var = var')
  | is_same_assms_eq_ac (Bound var) (Bound var') =
    (var = var')
  | is_same_assms_eq_ac (Const (var, _)) (Const (var', _)) =
    (var = var')
  | is_same_assms_eq_ac (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ u $ v) (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ u' $ v') =
    (is_same_assms_eq_ac u u' andalso is_same_assms_eq_ac v v') orelse
    (is_same_assms_eq_ac u v' andalso is_same_assms_eq_ac v u')
  | is_same_assms_eq_ac (u $ v) (u' $ v') =
    (is_same_assms_eq_ac u u' andalso is_same_assms_eq_ac v v')
  | is_same_assms_eq_ac _ _  = (false)

fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of

fun normalized_input ctxt prems t = 
  let
    (* External problems only: Retrieve correct assertion for this assume *)
    val all_assms = SMT_Config.alethe_no_provided_assms ctxt
    val termify = Thm.prop_of #> (fn x => single (0, x)) #> SMT_Translate.eta_expand ctxt Termtab.empty #> hd #> snd
    val normalized =
       let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy (Named_Theorems.get ctxt \<^named_theorems>\<open>cvc5_normalized_input\<close>) []
        #> Object_Logic.atomize_term ctxt
        #> HOLogic.mk_Trueprop
      end
    fun matched_assm () =
      (case find_first (is_same_assms_eq_ac (normalized t) o normalized o termify) prems of
        SOME thm => [thm]
      | NONE => [])
    val m_assm = matched_assm ()
    val _ = if length m_assm = 0 then SMT_Config.trace_msg ctxt (pretty ("warning: could not find assumption, had to add all premises")) [] else ()
    val prems = (if all_assms andalso not (length m_assm = 0) then m_assm else prems)
    val _ = debug_msg ctxt low (fn () => \<^print> ("showing normalized input, premises",prems))

  in
    (SMT_Replay_Methods.prove ctxt t (fn _ =>
      Method.insert_tac ctxt prems
      THEN' debug_msg_tac' ctxt high "normalized input after inserting premises"
      THEN' TRY' (K (unfold_tac ctxt (@{thms SMT.trigger_def} @  Named_Theorems.get ctxt \<^named_theorems>\<open>nat_normalized_input\<close>)))
      THEN' debug_msg_tac' ctxt high "normalized input after unfolding triggers and nat_normalized_input"
      THEN' TRY' (partial_simplify_tac ctxt (@{thms eq_commute} @ Named_Theorems.get ctxt \<^named_theorems>\<open>cvc5_normalized_input\<close>))
      THEN' debug_msg_tac' ctxt high "normalized input after simplifying eq_commute and cvc5_normalized_input"
    ))
end

val false_rule_thm = @{lemma \<open>\<not>False\<close> by blast}

fun false_rule ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t false_rule_thm


(* Transitivity *)

(*cvc5 is not using this at the moment (see cvc5_replay_methods)*)

val trans_bool_thm =
  @{lemma \<open>P = Q \<Longrightarrow> Q \<Longrightarrow> P\<close> by blast}

fun trans ctxt thms t =
  let

    val prop_of = HOLogic.dest_Trueprop o Thm.full_prop_of
    fun combine_thms [thm1, thm2] =
          (case (prop_of thm1, prop_of thm2) of
            ((Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2),
             (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t3 $ t4)) =>
            if t2 aconv t3 then thm1 RSN (1, thm2 RSN (2, @{thm trans}))
            else if t2 aconv t4 then thm1 RSN ((1, ((thm2 RS sym)) RSN (2, @{thm trans})))
            else if t1 aconv t4 then thm2 RSN (1, thm1 RSN (2, @{thm trans}))
            else raise Fail "invalid trans theorem"
          | _ => trans_bool_thm OF [thm1, thm2])
      | combine_thms (thm1 :: thm2 :: thms) =
          combine_thms (combine_thms [thm1, thm2] :: thms)
      | combine_thms thms = replay_error ctxt "invalid bind application" Trans thms [] t
     val t' = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
     val _ = debug_msg ctxt high (fn () => \<^print> ("trans t'",t'))

     val (_, t2) = Logic.dest_equals (Thm.prop_of t')
     val _ = debug_msg ctxt high (fn () => \<^print> ("trans t2",t'))

     val thms = map (Conv.fconv_rule Thm.eta_long_conversion) thms
     val _ = debug_msg ctxt high (fn () => \<^print> ("trans thms ",thms))

     val trans_thm = combine_thms thms
     val _ = debug_msg ctxt high (fn () => \<^print> ("trans_thm ",trans_thm))

  in
     ((case (prop_of trans_thm, t2) of
       ((Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ _),
             (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t3 $ _)) =>
       if t1 aconv t3 then trans_thm else trans_thm RS sym
      | _ => trans_thm (*to be on the safe side*)))
  end


local
 fun trans_steps _ [prem] = prem
   | trans_steps ctxt (prem1::prem2::prems) =
       (@{thm trans} OF [prem1, prem2])::prems
       |> trans_steps ctxt
in

fun strict_trans ctxt [] t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    (match_tac ctxt @{thms refl}))
 | strict_trans ctxt prems t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    match_tac ctxt (trans_steps ctxt prems |> single))
end

fun AC_rule ctxt thms t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt thms
    THEN' REPEAT_ALL_NEW (partial_simplify_tac ctxt @{thms eq_commute}
    THEN' TRY' (simplify_tac ctxt @{thms ac_simps conj_ac})
    THEN' TRY' (assume_tac ctxt)
    THEN' TRY' (Classical.fast_tac ctxt)))

local
  val idempotency_thms =
   @{thms Groups.group_add_class.diff_0_right
   Groups.monoid_add_class.add_0_right Groups.group_add_class.add.group_left_neutral
   Rings.mult_zero_class.mult_zero_left Rings.mult_zero_class.mult_zero_right
   } (*TODO: Add bit-vector theorems if necessary. TODO: Not clear if it helps to add some of these or not.*)
  fun aci_simps_extra_thms ctxt = (Named_Theorems.get ctxt @{named_theorems alethe_aci_simp})
in
 
fun ACI_rule ctxt thms t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt thms 
    THEN' debug_msg_tac' ctxt high "aci_simp before commute"
    THEN' REPEAT_ALL_NEW (partial_simplify_tac ctxt @{thms eq_commute}
    THEN' debug_msg_tac' ctxt high "aci_simp before simplification"
    THEN' TRY' (simplify_tac ctxt (idempotency_thms @ aci_simps_extra_thms ctxt @ @{thms ac_simps conj_ac}))
    THEN' debug_msg_tac' ctxt high "aci_simp after simplification"
    THEN' TRY' (assume_tac ctxt)
    THEN' TRY' (Classical.fast_tac ctxt)))
end


(* And/Or *)

local
  fun not_and_rule_prove ctxt prems =
     Method.insert_tac ctxt prems
     THEN' K (unfold_tac ctxt @{thms de_Morgan_conj})
     THEN_ALL_NEW TRY' (assume_tac ctxt)

  fun or_pos_prove ctxt _ =
     K (unfold_tac ctxt @{thms de_Morgan_disj not_not})
     THEN' match_tac ctxt @{thms alethe_and_pos alethe_farkas}
     THEN' K (unfold_tac ctxt @{thms de_Morgan_conj de_Morgan_disj not_not})
     THEN' TRY' (assume_tac ctxt)

  fun not_or_rule_prove ctxt prems =
     Method.insert_tac ctxt prems
     THEN' K (unfold_tac ctxt @{thms de_Morgan_disj not_not})
     (*THEN' K (print_tac ctxt "not_or")*)
     THEN' TRY' (REPEAT' (match_tac ctxt @{thms conjI}     THEN' K (print_tac ctxt "not_or1")
))
     THEN_ALL_NEW ((REPEAT' (ematch_tac ctxt @{thms conjE})     THEN' K (print_tac ctxt "not_or2")
)
       THEN' TRY' (assume_tac ctxt))

  fun and_rule_prove ctxt prems =
     Method.insert_tac ctxt prems
     THEN' REPEAT' (eresolve_tac ctxt @{thms conjE} THEN' TRY' (assume_tac ctxt))
     THEN' TRY' (assume_tac ctxt)

  fun and_neg_rule_prove ctxt _ =
     match_tac ctxt @{thms alethe_and_neg}
     THEN' K (unfold_tac ctxt @{thms de_Morgan_conj not_not})
     THEN' TRY' (assume_tac ctxt)

  fun prover tac = prove_abstract SMT_Replay_Methods.abstract_prop tac

in

val and_rule = prover and_rule_prove

val not_and_rule = prover not_and_rule_prove


val or_pos_rule = prover or_pos_prove

val and_neg_rule = prover and_neg_rule_prove

(*not_or and or_neg should use the same *)
fun not_or_rule ctxt prems t = 
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    let
      val y = Thm.cterm_of ctxt (HOLogic.dest_Trueprop (Thm.prop_of (hd prems)))
      val t2 = Thm.cterm_of ctxt (HOLogic.dest_Trueprop t)
    
      val x = Drule.infer_instantiate' ctxt [SOME y, SOME t2] @{thm alethe_not_or(1)}
    
    in
      (resolve_tac ctxt [x])
      THEN' (resolve_tac ctxt prems)
      THEN' K (unfold_tac ctxt @{thms alethe_not_or(2)})
      THEN' (resolve_tac ctxt @{thms alethe_or_neg})
    
      THEN' K (unfold_tac ctxt @{thms not_not})
      THEN_ALL_NEW
        (REPEAT'
          (SOLVED' (match_tac ctxt @{thms disjI1} THEN_ALL_NEW assume_tac ctxt)
           ORELSE' (match_tac ctxt @{thms disjI2} THEN' TRY' (assume_tac ctxt))))
    end)


(*TODO: Improve now that we have arguments*)
(* TODO Benchmark or_neg versions *)

(* Version 1: Old initial version *)
(*
val or_neg_rule = prove_abstract SMT_Replay_Methods.abstract_bool (fn ctxt => fn _ =>

  resolve_tac ctxt @{thms alethe_or_neg}

  THEN' K (unfold_tac ctxt @{thms not_not})
  THEN_ALL_NEW
    (REPEAT'
      (SOLVED' (match_tac ctxt @{thms disjI1} THEN_ALL_NEW assume_tac ctxt)
       ORELSE' (match_tac ctxt @{thms disjI2} THEN' TRY' (assume_tac ctxt)))))
*)
(* Version 2: Index usage *)
fun or_neg_rule ctxt _ t (SOME (Index k)) = 
   SMT_Replay_Methods.prove ctxt t (fn _ =>
     resolve_tac ctxt @{thms alethe_or_neg}
     THEN' (REPEAT_DETERM_N' k (match_tac ctxt @{thms disjI2}))
     THEN' FIRST' [
                   (match_tac ctxt @{thms disjI1}) THEN' (assume_tac ctxt),
                   (assume_tac ctxt)
                  ]
) |
  or_neg_rule ctxt _ t _ = SMT_Replay_Methods.prove ctxt t (fn _ => K no_tac)

(* TODO Version 3: Theorem construction *)

(* TODO Benchmark and_pos versions *)

(* Version 1: Old initial version *)
(*
fun and_pos ctxt _ t (SOME (Index k)) =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_DETERM_N' k (resolve_tac ctxt @{thms alethe_and_pos})  
  THEN' TRY' (
    resolve_tac ctxt @{thms excluded_middle}
    ORELSE'
    resolve_tac ctxt [@{lemma "(a \<Longrightarrow> A) \<Longrightarrow> \<not>(a \<and> b) \<or> A" by blast}]
  )
  THEN' TRY' (assume_tac ctxt)) |
and_pos ctxt _ t _ = (*legacy*)
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_CHANGED (resolve_tac ctxt @{thms alethe_and_pos})
  THEN' TRY' (assume_tac ctxt))
*)

(* 
SMT-LIB (and a b (and c d)), i = 2 ==> (and c d)

Isabelle (and a b c d) ==> (and a (and b (and c d)))

Isabelle (and a b (and c d)) ==> (and a (and b (and c d)))
*)

(* Version 2: d-tact and assume *)
fun and_pos ctxt _ t (SOME (Index k)) =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [@{lemma "(A \<Longrightarrow> B) \<Longrightarrow> (\<not>A \<or> B)" by blast}]
  THEN' REPEAT_DETERM_N' k (dmatch_tac ctxt @{thms conjunct2})
  THEN' FIRST' [
                (dmatch_tac ctxt @{thms conjunct1}) THEN' (assume_tac ctxt),
                (assume_tac ctxt)
               ]
) |
  and_pos ctxt _ t _ = SMT_Replay_Methods.prove ctxt t (fn _ => K no_tac)

(* TODO Version 3: Theorem construction *)


end


(* Equivalence Transformation *)

local
  fun prove_equiv equiv_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [equiv_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_equiv _ ctxt thms t = replay_error ctxt "invalid application in some equiv rule" Unsupported thms [] t
in

val not_equiv1 = prove_equiv @{lemma \<open>\<not>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> B\<close> by blast}
val not_equiv2 = prove_equiv @{lemma \<open>\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> \<not>B\<close> by blast}
val equiv1  = prove_equiv @{lemma \<open>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> B\<close> by blast}
val equiv2 = prove_equiv @{lemma \<open>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> \<not>B\<close> by blast}
val not_implies1 = prove_equiv @{lemma \<open>\<not>(A \<longrightarrow> B) \<Longrightarrow> A\<close> by blast}
val not_implies2 = prove_equiv @{lemma \<open>\<not>(A \<longrightarrow>B) \<Longrightarrow> \<not>B\<close> by blast}

end


(* Equivalence Lemma *)
(*equiv_pos2 is very important for performance. We have tried various tactics, including
a specialisation of SMT_Replay_Methods.match_instantiate, but there never was a measurable
and consistent gain.*)
local
  fun prove_equiv_pos_neg2 thm ctxt _ t =
    SMT_Replay_Methods.match_instantiate ctxt t thm
in

val equiv_pos1_thm = @{lemma \<open>\<not>(a \<longleftrightarrow> b) \<or> a \<or> \<not>b\<close> by blast+}
val equiv_pos1 = prove_equiv_pos_neg2 equiv_pos1_thm

val equiv_pos2_thm = @{lemma \<open>\<And>a b. (a \<noteq> b) \<or> \<not>a \<or> b\<close> by blast+}
val equiv_pos2 = prove_equiv_pos_neg2 equiv_pos2_thm

val equiv_neg1_thm = @{lemma \<open>(a \<longleftrightarrow> b) \<or> \<not>a \<or> \<not>b\<close> by blast+}
val equiv_neg1 = prove_equiv_pos_neg2 equiv_neg1_thm

val equiv_neg2_thm = @{lemma \<open>(a \<longleftrightarrow> b) \<or> a \<or> b\<close> by blast}
val equiv_neg2 = prove_equiv_pos_neg2 equiv_neg2_thm

end

(* xor Transformation *)
local
 fun prove_xor xor_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [xor_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_xor _ ctxt thms t = replay_error ctxt "invalid application in some xor rule" Unsupported thms [] t
in

val xor1_thm = @{lemma \<open>\<not>(a = b) \<Longrightarrow> a \<or> b\<close> by blast}
val xor1 = prove_xor xor1_thm

val xor2_thm = @{lemma \<open>\<not>(a = b) \<Longrightarrow> \<not>a \<or> \<not>b\<close> by blast}
val xor2 = prove_xor xor2_thm

val not_xor1_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<Longrightarrow> a \<or> \<not>b\<close> by blast}
val not_xor1 = prove_xor not_xor1_thm

val not_xor2_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<Longrightarrow> \<not>a \<or> b\<close> by blast}
val not_xor2 = prove_xor not_xor2_thm

end


(* xor Lemma *)
local
  fun prove_xor thm ctxt _ t =
    SMT_Replay_Methods.match_instantiate ctxt t thm
in

val xor_pos1_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<or> a \<or> b\<close> by blast}
val xor_pos1 = prove_xor xor_pos1_thm

val xor_pos2_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<or> \<not>a \<or> \<not>b\<close> by blast}
val xor_pos2 = prove_xor xor_pos2_thm

val xor_neg1_thm = @{lemma \<open>\<not>(a = b) \<or> a \<or> \<not>b\<close> by blast}
val xor_neg1 = prove_xor xor_neg1_thm

val xor_neg2_thm = @{lemma \<open>\<not>(a = b) \<or> \<not>a \<or> b\<close> by blast}
val xor_neg2 = prove_xor xor_neg2_thm

end


local
  fun implies_pos_neg_term ctxt thm (\<^term>\<open>Trueprop\<close> $
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>HOL.implies\<close> $ a $ b) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | implies_pos_neg_term ctxt thm  t =
        replay_error ctxt "invalid application in Implies" Unsupported [thm] [] t

  fun prove_implies_pos_neg thm ctxt _ t =
    let val thm = implies_pos_neg_term ctxt thm t
    in
      SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [thm]
        THEN' TRY' (assume_tac ctxt))
    end
in


fun distinct_elim ctxt _ t =
let
  fun extract_clauses thm =
    REPEAT_CHANGED (resolve_tac ctxt @{thms alethe_distinct_elim_1(1)})
    THEN' (resolve_tac ctxt @{thms alethe_distinct_elim_1(2)})
    THEN' (resolve_tac ctxt @{thms alethe_distinct_elim_1(3)})
    THEN' (match_tac ctxt thm)
    THEN_ALL_NEW (assume_tac ctxt)
in
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  SOLVED'
     (TRY'(
      (resolve_tac ctxt @{thms alethe_distinct_elim_two_clauses})
      ORELSE'
      (resolve_tac ctxt @{thms alethe_distinct_elim_0}
      THEN' (REPEAT_DETERM_N' 2 (extract_clauses @{thms alethe_distinct_elim_2}))
      )
    )
    THEN' TRY' (resolve_tac ctxt @{thms refl})
   )
  ORELSE' (Classical.fast_tac ctxt)
  )
end



val implies_neg1_thm = @{lemma \<open>(a \<longrightarrow> b) \<or> a\<close> by blast}
val implies_neg1  = prove_implies_pos_neg implies_neg1_thm

val implies_neg2_thm = @{lemma \<open>(a \<longrightarrow> b) \<or> \<not>b\<close> by blast}
val implies_neg2 = prove_implies_pos_neg implies_neg2_thm

val implies_thm = @{lemma \<open>(a \<longrightarrow> b) \<Longrightarrow> \<not>a \<or> b\<close> by blast}

(*<eigentlich will man backwards proven, aber zu dem Zeitpunkt war das reordering der conclusion
noch nicht klar, ausserdem einfacher zu debuggen

Um es backwards zu machen:

resolve_tac ctxt [implies_thm OF prems]

Koennte man am schluss aendern

*)
fun implies_rules ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [implies_thm OF prems]
  THEN' TRY' (assume_tac ctxt))

end


(* BFun *)

local
  val bfun_theorems = @{thms alethe_bfun_elim}
in

fun bfun_elim ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' TRY' (eqsubst_all ctxt bfun_theorems)
  THEN' TRY' (assume_tac ctxt)
  THEN' TRY' (simplify_tac ctxt @{thms ac_simps eq_commute all_conj_distrib ex_disj_distrib}))

end


(* If-Then-Else *)

local
  fun prove_ite ite_thm thm ctxt =
  resolve_tac ctxt [ite_thm OF [thm]]
  THEN' TRY' (assume_tac ctxt)

  fun prove_by_resolve ctxt thm t = SMT_Replay_Methods.prove ctxt t (fn _ => resolve_tac ctxt thm)
in

val ite_pos1_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<or> x \<or> Q\<close> by auto}

fun ite_pos1 ctxt _ = prove_by_resolve ctxt [ite_pos1_thm]

val ite_pos2_thms =
  @{lemma \<open>\<not>(if x then P else Q) \<or> \<not>x \<or> P\<close> \<open>\<not>(if \<not>x then P else Q) \<or> x \<or> P\<close> by auto}

fun ite_pos2 ctxt _ = prove_by_resolve ctxt ite_pos2_thms

val ite_neg1_thms =
  @{lemma \<open>(if x then P else Q) \<or> x \<or> \<not>Q\<close> \<open>(if x then P else \<not>Q) \<or> x \<or> Q\<close> by auto}

fun ite_neg1 ctxt _ = prove_by_resolve ctxt ite_neg1_thms

val ite_neg2_thms =
  @{lemma \<open>(if x then P else Q) \<or> \<not>x \<or> \<not>P\<close> \<open>(if \<not>x then P else Q) \<or> x \<or> \<not>P\<close>
          \<open>(if x then \<not>P else Q) \<or> \<not>x \<or> P\<close> \<open>(if \<not>x then \<not>P else Q) \<or> x \<or> P\<close>
      by auto}

fun ite_neg2 ctxt _ t = prove_by_resolve ctxt ite_neg2_thms t

val ite1_thm =
  @{lemma \<open>(if x then P else Q) \<Longrightarrow> x \<or> Q\<close> by (auto split: if_splits) }

fun ite1 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite ite1_thm (extract_single_premise ITE1 ctxt thm t) ctxt)

val ite2_thm =
  @{lemma \<open>(if x then P else Q) \<Longrightarrow> \<not>x \<or> P\<close> by (auto split: if_splits) }

fun ite2 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite ite2_thm (extract_single_premise ITE2 ctxt thm t) ctxt)

val not_ite1_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<Longrightarrow> x \<or> \<not>Q\<close> by (auto split: if_splits) }

fun not_ite1 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite not_ite1_thm (extract_single_premise Not_ITE1 ctxt thm t) ctxt)

val not_ite2_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<Longrightarrow> \<not>x \<or> \<not>P\<close> by (auto split: if_splits) }

fun not_ite2 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite not_ite2_thm (extract_single_premise Not_ITE2 ctxt thm t) ctxt)

(*ite_intro can introduce new terms that are in the proof exactly the sames as the old one, but are
not internally, hence the possible reordering.

TODO: after updating this in 2026, I did not find any example that needed anything
besides the first rule. The rest is kept as legacy though, because there are very few
case of this rule in our tests.*)
fun ite_intro ctxt _ t =
  let
    fun simplify_ite ctxt thms cong =
      ctxt
      |> empty_simpset
      |> put_simpset HOL_basic_ss
      |> (fn ctxt => ctxt addsimps thms @ @{thms simp_thms})
      |> cong ? (Raw_Simplifier.add_eqcong @{thm alethe_ite_if_cong})
      |> Simplifier.full_simp_tac
    val use_cong = (0 = 0)
  in
    SMT_Replay_Methods.prove ctxt t (fn _ => 
      simplify_ite ctxt @{thms alethe_ite_intro(1-4)} (not use_cong)
      THEN' TRY' (simplify_ite ctxt @{thms alethe_ite_intro} (not use_cong))
      THEN' TRY' (simplify_ite ctxt @{thms if_cancel} use_cong)
      THEN' TRY' (simplify_ite ctxt @{thms eq_commute} use_cong))
  end
end


(* Quantifiers *)

local
  val rm_unused = @{lemma \<open>(\<forall>x. P) = P\<close> \<open>(\<exists>x. P) = P\<close> by blast+}
  val qnt_cnf_basic = @{lemma \<open>(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> (\<not>(\<forall>x. P x)) \<or> (\<forall>x. Q x)\<close> by blast+}
  (*We try to recontruct the proof without looking too much into the structure, hence
  first trying simp. The main issue is that the simplifer call can loop in complicated
  cases.*)
  fun qnt_cnf_tac ctxt =
   (debug_msg_tac' ctxt high "qnt_cnf start") THEN'
    SOLVED' (resolve_tac ctxt [qnt_cnf_basic]
      THEN' (debug_msg_tac' ctxt high "qnt_cnf after resolving with qnt_cnf_basic")
      THEN' simplify_tac ctxt (@{thms
        iff_conv_conj_imp if_bool_eq_disj ex_simps all_simps ex_disj_distrib
        alethe_connective_def(3)  all_conj_distrib not_all not_ex} @ 
        (*not_not is repeated as last theorem:*)
        (curry List.take @{thms nnf_simps} (length @{thms nnf_simps} - 1)))
      THEN' (debug_msg_tac' ctxt high "qnt_cnf after resolving simplifying")
      THEN' TRY' (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []))
    ORELSE' Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []

  val all_comm = @{lemma "(\<forall>x y. P x y) \<equiv> (\<forall>y x. P x y)" by (subst all_comm)}
  fun plunge_down ctxt str ctrm =
   case Thm.term_of ctrm of
     _ $ Abs (v, _, _) => 
       if String.isPrefix v str
       then
           (Conv.try_conv (Conv.rewr_conv all_comm) then_conv Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => plunge_down ctxt str) ctxt)) ctrm
       else Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => plunge_down ctxt str) ctxt) ctrm
   | _ => Conv.all_conv ctrm


  fun reorder_prefix_to _ [] ctrm = Conv.all_conv ctrm
   | reorder_prefix_to ctxt (str :: xs) ctrm =
     (case (Thm.term_of ctrm) of
       _ $ Abs (v, _, _) => 
         if String.isPrefix v str
         then
           Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => reorder_prefix_to ctxt xs) ctxt) ctrm
         else 
           (plunge_down ctxt v then_conv reorder_prefix_to ctxt (str :: xs)) ctrm
     | _ => Conv.all_conv ctrm)

  fun extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (name, _, t)) =
        name :: (extract_all_forall_exists_quantified_names_q t)
    | extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
        name :: (extract_all_forall_exists_quantified_names_q t)
    | extract_all_forall_exists_quantified_names_q _ = []
  fun reorder_quantifer ctxt prop = 
    let val strs =
      prop
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
      |> fst
      |> extract_all_forall_exists_quantified_names_q
    in
      CONVERSION (HOLogic.Trueprop_conv (Conv.arg_conv (reorder_prefix_to ctxt strs)))
    end
in
fun qnt_rm_unused ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  K (unfold_tac ctxt rm_unused)
  THEN' (debug_msg_tac' ctxt high "qnt_rm_unused")
  THEN' TRY' (SUBGOAL (fn (prop, i) => reorder_quantifer ctxt prop i))
  THEN' TRY' (resolve_tac ctxt @{thms refl})
  )

local
  fun aconv_untyped (tm1, tm2) =
    pointer_eq (tm1, tm2) orelse
      (case (tm1, tm2) of
        (t1 $ u1, t2 $ u2) => aconv_untyped (t1, t2) andalso aconv_untyped (u1, u2)
      | (Abs (_, _, t1), Abs (_, _, t2)) => aconv_untyped (t1, t2)
      | (Const (a, _), Const (b, _)) => a = b
      | (Free (x, _), Free (y, _)) => x = y
      | (Var (xi, _), Var (yj, _)) => xi = yj
      | (Bound i, Bound j) => i = j
      | _ => false);
  fun subst_var_untyped [] = I
    | subst_var_untyped pairs =
        let fun substf u =
              case AList.lookup aconv_untyped pairs u of
                  SOME u' => u'
                | NONE => (case u of Abs(a,T,t) => Abs(a, T, substf t)
                                   | t$u' => substf t $ substf u'
                                   | _ => u)
        in  substf  end;
  fun resolve_and_instantiate_onepoint (_, i : term) insts {context, params, ...} =
    let
       val i = i
         |> Term.subst_free insts
         |> subst_var_untyped (map (fn (x, t) => (Var ((x, 0), @{typ dummy}), Thm.term_of t)) params)
         |> Thm.cterm_of context
       val thms = map (Drule.infer_instantiate' context [SOME i])
           @{thms alethe_onepoint2_all alethe_onepoint2_ex}
    in
      resolve_tac context thms 1
    end
  fun onepoint_combine_quant ctxt (n1 :: bounds1) (n2 :: bounds2) (i :: insts) past_ints =
      TRY' (if n1 = n2
        then resolve_tac ctxt @{thms alethe_onepoint(1,3)}
         THEN' onepoint_combine_quant ctxt bounds1 bounds2 (i :: insts) past_ints
       else Subgoal.FOCUS (resolve_and_instantiate_onepoint i past_ints) ctxt
         THEN' onepoint_combine_quant ctxt bounds1 (n2 :: bounds2) insts (past_ints @ [i]))
    | onepoint_combine_quant ctxt (_ :: bounds1) [] (i :: insts) past_ints =
      Subgoal.FOCUS (resolve_and_instantiate_onepoint i past_ints) ctxt
      THEN' onepoint_combine_quant ctxt bounds1 [] insts (past_ints @ [i])
    | onepoint_combine_quant _ _ _ _ _ = K all_tac

  fun extract_implications 
     (Const (\<^const_name>\<open>Pure.imp\<close>,_) $ 
       (Const (\<^const_name>\<open>Trueprop\<close>,_) $ (Const (\<^const_name>\<open>HOL.eq\<close>,_) $ u $ v)) $
       t) = (u, v) :: extract_implications t
    | extract_implications _ = []

  val extract_instantiations =
    Thm.prop_of
    #> extract_implications
 
  fun onepoint_quants ctxt prems t =
    let
      val insts = extract_instantiations prems
      val (t1, t2) = 
        t
        |> Thm.cterm_of ctxt
        |> Thm.term_of o Object_Logic.dest_judgment ctxt
        |> HOLogic.dest_eq
    in
       onepoint_combine_quant ctxt 
         (extract_quantified_names_q t1 |> fst |> map to_upper)
         (extract_quantified_names_q t2 |> fst |> map to_upper)
         insts
    end
in
fun onepoint ctxt [prem] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  onepoint_quants ctxt prem t []
  THEN' REPEAT' (resolve_tac ctxt @{thms refl})
  THEN_ALL_NEW 
    (*cheap version: hope that nothing got reorder and simp will solve the goal. Otherwise,
    try to move all equalities out of the quantifiers rewrite them with @{thm alethe_rewrite_in_imp}
    and only afterwards try metis.*)
    ((SOLVED' ( 
      (ctxt
      |> empty_simpset
      |> put_simpset HOL_basic_ss
      |> (fn ctxt => ctxt addsimps @{thms simp_thms all_simps ex_simps de_Morgan_conj
        not_all not_ex de_Morgan_disj disj_not1 triv_forall_equality eq_commute alethe_imp_commute})
      |> Simplifier.add_cong @{thm alethe_rewrite_in_imp}
      |> (fn ctxt => ctxt
           addsimprocs [@{simproc defined_All}, @{simproc defined_Ex}])
      |> Simplifier.asm_full_simp_tac)))
    ORELSE' 
      (*
      This part becomes really messy:
        - veriT can still reorder equalities, so we need something stronger 
        than just reordering the implication as done above.
        - simp can destroy the structure
        - metis is not always able to solve the goal, even if it falls within
        the fragment of logic where it for sure should be able to.
      *)
      (SOLVED' (Meson.meson_tac ctxt [])
      ORELSE' Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []
      ORELSE' K (Clasimp.auto_tac ctxt))))
end

fun qnt_join ctxt _ t = SMT_Replay_Methods.prove ctxt t Classical.fast_tac

fun qnt_cnf ctxt _ t = SMT_Replay_Methods.prove ctxt t qnt_cnf_tac

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
      partial_simplify_tac ctxt [])

end

(* Equality *)

fun eq_transitive ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn  _ =>
  REPEAT_CHANGED (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF @{thms impI}])
  THEN' REPEAT' (resolve_tac ctxt @{thms impI})
  THEN' REPEAT' (eresolve_tac ctxt @{thms conjI})
  THEN' REPEAT' (fn i => dresolve_tac ctxt @{thms alethe_eq_transitive} i THEN assume_tac ctxt (i+1))
  THEN' resolve_tac ctxt @{thms refl})

local
  fun find_rew rews t t' =
    (case AList.lookup (op =) rews (t, t') of
      SOME thm => SOME (thm COMP @{thm symmetric})
    | NONE =>
      (case AList.lookup (op =) rews (t', t) of
        SOME thm => SOME thm
      | NONE => NONE))

  fun eq_pred_conv rews t ctxt ctrm =
    (case find_rew rews t (Thm.term_of ctrm) of
      SOME thm => Conv.rewr_conv thm ctrm
    | NONE =>
      (case t of
        f $ arg =>
          (Conv.fun_conv (eq_pred_conv rews f ctxt) then_conv
             Conv.arg_conv (eq_pred_conv rews arg ctxt)) ctrm
      | Abs (_, _, f) => Conv.abs_conv (eq_pred_conv rews f o snd) ctxt ctrm
      | _ => Conv.all_conv ctrm))

  fun eq_pred_rewrite_tac ({context = ctxt, prems, concl, ...}: Subgoal.focus) =
    let
      val rews = prems
       |> map_filter (try (apfst (HOLogic.dest_eq o Thm.term_of o Object_Logic.dest_judgment ctxt o
            Thm.cconcl_of) o `(fn x => x)))
       |> map (apsnd (fn x => @{thm eq_reflection} OF [x]))
      fun conv_left conv = Conv.arg_conv (Conv.arg_conv conv)
      fun conv_left_neg conv = Conv.arg_conv (Conv.arg_conv (Conv.arg_conv conv))
      val (t1, conv_term) =
        (case Thm.term_of (Object_Logic.dest_judgment ctxt concl) of
          Const(_, _) $ (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ t1) $ _ => (t1, conv_left)
        | Const(_, _) $ t1 $ (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ _) => (t1, conv_left_neg)
        | Const(_, _) $ t1 $ _ => (t1, conv_left)
        | t1 => (t1, conv_left))
    fun throwing_CONVERSION cv i st = Seq.single (Conv.gconv_rule cv i st)
    in
      throwing_CONVERSION (conv_term (eq_pred_conv rews t1 ctxt))
    end
in

fun eq_congruent_pred ctxt _ t =
   SMT_Replay_Methods.prove ctxt t (fn _ =>
   REPEAT' (resolve_tac ctxt [@{thm disj_not1[of \<open>_ = _\<close>]} RSN (1, @{thm iffD2}) OF @{thms impI}])
   THEN' (fn i => Subgoal.FOCUS (fn focus => eq_pred_rewrite_tac focus i) ctxt i)
   THEN' (resolve_tac ctxt @{thms refl excluded_middle excluded_middle[of \<open>\<not>_\<close>, unfolded not_not]}
     ORELSE' assume_tac ctxt))

val eq_congruent = eq_congruent_pred

end


(* Subproof *)

(* Reordering *)
val split_neq = @{lemma "\<not>a \<or> \<not>c \<Longrightarrow> a \<or> c ==> a \<noteq> c" by auto}

local
  fun prove_reordering ctxt = 
      REPEAT' (resolve_tac ctxt [split_neq])
      THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})

      THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})

      THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})

      THEN' REPEAT'(ematch_tac ctxt @{thms notE}
      THEN' TRY' (assume_tac ctxt))
in
  val reordering2 = prove_reordering
end

(*
The reconstruction of subproof changed a lot over time, thanks to the stricter assumptions.
There are currently three paths:
  1. The most efficient which might however not work if the conclusion of
  the subproof is A & B

  2. The second step where we unify with the premise and the we enable
  reordering of equalities assuming

  3. We hammer on the goal.


*)
fun subproof ctxt [prem] t =
     SMT_Replay_Methods.prove ctxt t (fn _ =>
      SOLVED' (REPEAT' (resolve_tac ctxt @{thms alethe_and_neg(2)})
        THEN' TRY' (resolve_tac ctxt [prem])
        THEN' REPEAT' (assume_tac ctxt))
      ORELSE' SOLVED' (
        REPEAT' (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}],
           @{thm disj_not1[of \<open>\<not>_\<close>, unfolded not_not]} RSN (1, @{thm iffD2}) OF [@{thm impI}]])
        THEN' resolve_tac ctxt [prem]
        THEN_ALL_NEW (assume_tac ctxt
          ORELSE'
            SOLVED' ((partial_simplify_tac ctxt @{thms eq_commute ac_simps}
            THEN' TRY' (assume_tac ctxt))))
          THEN' TRY' (assume_tac ctxt))
      ORELSE' TRY' (Method.insert_tac ctxt [prem]
        THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute ac_simps})
        THEN' TRY' (Blast.blast_tac ctxt)))
  | subproof ctxt prems t =
      replay_error ctxt "invalid application, only one assumption expected" Subproof prems [] t


(* Simplifying Steps *)

(* The reconstruction is a bit tricky: At first we only rewrite only based on the rules that are
passed as argument. Then we simply use simp_thms to reconstruct all the proofs (and these theorems
cover all the simplification below).
*)
local
  fun rewrite_only_thms ctxt thms =
    ctxt
    |> empty_simpset
    |> put_simpset HOL_basic_ss
    |> (fn ctxt => ctxt addsimps thms)
    |> Simplifier.full_simp_tac

  fun rewrite_thms ctxt thms =
    ctxt
    |> empty_simpset
    |> put_simpset HOL_basic_ss
    |> Raw_Simplifier.add_eqcong @{thm eq_reflection[OF imp_cong]}
    |> (fn ctxt => ctxt addsimps thms addsimps @{thms simp_thms})
    |> Simplifier.full_simp_tac

  fun chain_rewrite_thms ctxt thms =
    TRY' (rewrite_only_thms ctxt thms)
    THEN' TRY' (rewrite_thms ctxt thms)

  fun chain_rewrite_two_step_with_ac_simps ctxt thms1 thms2 =
    TRY' (rewrite_only_thms ctxt thms1)
    THEN' TRY' (rewrite_thms ctxt thms2)

in
fun rewrite_bool_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_thms ctxt @{thms alethe_bool_simplify}))

fun rewrite_and_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt @{thms alethe_and_simplify alethe_and_simplify1}
     @{thms alethe_and_simplify}))

(*
Currently the tatic does not support steps like
  (P False \<or> P True \<or> \<not> P False) = True
hence the fast at the end.
*)
fun rewrite_or_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt @{thms alethe_or_simplify alethe_or_simplify_1}
    @{thms alethe_or_simplify})
    THEN' TRY' (REPEAT' (match_tac ctxt @{thms alethe_and_pos}) THEN' (assume_tac ctxt))
    THEN' TRY' (Classical.fast_tac ctxt))

fun rewrite_not_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms ctxt @{thms alethe_not_simplify}))

fun rewrite_equiv_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms ctxt @{thms alethe_equiv_simplify}))

fun rewrite_eq_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt
      @{thms alethe_eq_simplify}
      (Named_Theorems.get ctxt @{named_theorems ac_simps})))

fun rewrite_implies_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    (rewrite_only_thms ctxt @{thms alethe_implies_simplify}))

fun rewrite_connective_def ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
 ((*K (print_tac ctxt "before1")THEN'*)
      match_tac ctxt @{thms alethe_connective_def}
  (*    THEN' K (print_tac ctxt "after step 1")*)
)
ORELSE'
 ((*K (print_tac ctxt "before2")THEN'*)
    K (unfold_tac ctxt @{thms not_ex not_not not_all})
      (*THEN' K (print_tac ctxt "after step 0")*)

     THEN'  REPEAT' (match_tac ctxt @{thms alethe_connective_def_forall})
    (*  THEN' K (print_tac ctxt "after step 2")*)

      THEN' K (unfold_tac ctxt @{thms not_not })
     (*   THEN' K (print_tac ctxt "after step 3")*)

      THEN' TRY' (resolve_tac ctxt @{thms refl})
     (*   THEN' K (print_tac ctxt "after step 4")*)
)
)

fun rewrite_minus_simplify ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      chain_rewrite_two_step_with_ac_simps ctxt
         @{thms arith_simps alethe_minus_simplify}
         (Named_Theorems.get ctxt @{named_theorems ac_simps} @
          @{thms numerals arith_simps arith_special
             numeral_class.numeral.numeral_One}))

fun rewrite_comp_simplify ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
        chain_rewrite_thms ctxt @{thms alethe_comp_simplify})

fun rewrite_ite_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms ctxt @{thms alethe_ite_simplify}))

local
  fun simplify_arith ctxt thms = partial_simplify_tac ctxt
    (thms @ Named_Theorems.get ctxt @{named_theorems ac_simps} @ @{thms arith_simps})
in

fun all_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ => K (print_tac ctxt "in all_simp0")
     THEN' TRY' (K (Clasimp.auto_tac ctxt))
     (*THEN' K (print_tac ctxt "in all_simp1")*)
     THEN' TRY' (Code_Simp.dynamic_tac ctxt )
     (*THEN' K (print_tac ctxt "in all_simp2")*)

     THEN' TRY' (Lin_Arith.tac ctxt)

     THEN' TRY' (simplify_arith ctxt @{thms alethe_sum_simplify arith_special zmult_eq_1_iff})
 
     THEN' TRY' (simplify_arith ctxt @{thms alethe_prod_simplify})

     THEN' TRY' (chain_rewrite_two_step_with_ac_simps ctxt
         @{thms arith_simps alethe_minus_simplify}
         (Named_Theorems.get ctxt @{named_theorems ac_simps} @
          @{thms numerals arith_simps arith_special
             numeral_class.numeral.numeral_One}))

     THEN' TRY' (Code_Simp.dynamic_tac ctxt )
    THEN' TRY' (K (Clasimp.auto_tac ctxt)) 
) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)
end
end


(* Simplifications *)

local
  fun simplify_arith ctxt thms = partial_simplify_tac ctxt
    (thms @ Named_Theorems.get ctxt @{named_theorems ac_simps} @ @{thms arith_simps})
  fun simplify_arith_ifcong ctxt thms = partial_simplify_tac_with_cong @{thm if_weak_cong}
    [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
         @{simproc divide_cancel_numeral_factor}, @{simproc divide_cancel_factor},
         @{simproc intle_cancel_numerals}, @{simproc intless_cancel_numerals}, @{simproc inteq_cancel_numerals},
         @{simproc field_combine_numerals},
         @{simproc ring_le_cancel_numeral_factor},
         @{simproc Numeral_Simprocs.semiring_assoc_fold},
         @{simproc Numeral_Simprocs.field_divide_cancel_numeral_factor},
         @{simproc Numeral_Simprocs.field_eq_cancel_numeral_factor}]
     ctxt
    (thms @ Named_Theorems.get ctxt @{named_theorems ac_simps} @ @{thms arith_simps})
in

fun sum_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith ctxt @{thms alethe_sum_simplify arith_special}
    ) 

fun prod_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith ctxt @{thms alethe_prod_simplify}
    )

fun div_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith_ifcong ctxt @{thms alethe_div_simplify}
    )

end

fun rare_rewrite ctxt prems t = (@{print}("t",t);
  SMT_Replay_Methods.prove ctxt t (fn _ =>
     Method.insert_tac ctxt prems
    THEN' K (print_tac ctxt "use cvc5 extension for better success rate")
    THEN' TRY' (K (Clasimp.auto_tac ctxt)
     THEN' TRY' (Code_Simp.dynamic_tac ctxt )
)))


(* Arithmetics *)
local
val la_rw_eq_thm = @{lemma \<open>((a :: 'a :: linorder) = b) = ((a \<le> b) \<and> (b \<le> a))\<close> by auto}
in
fun la_rw_eq ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t la_rw_eq_thm

fun la_generic_prove args ctxt _ = SMT_Replay_Arith.la_farkas args ctxt

fun la_generic ctxt thms t args =
  prove_abstract (SMT_Replay_Methods.abstract_arith_shallow ctxt) (la_generic_prove args) ctxt [] t

fun lia_generic ctxt _ t =
  SMT_Replay_Methods.prove_arith_rewrite SMT_Replay_Methods.abstract_neq ctxt t

fun la_disequality ctxt _ t =
  SMT_Replay_Methods.match_instantiate ctxt t @{thm alethe_la_disequality}

fun la_mult_extract (Const ("HOL.Trueprop", _) $ (Const ("HOL.implies", _) 
 $ (Const ("HOL.conj",_) $ (_ $ _ $ factor) $ (rel $ l $ r))
 $ _)) = (rel,(factor,l,r))

fun to_lemma "Orderings.ord_class.less" = @{thm alethe_la_mult_pos_less}

(*Oct 18: I am not done here yet but it works already*)
fun la_mult_pos ctxt _ t =
let
 (* val (rel,(factor,l,r)) = la_mult_extract t*)
(*  val _ = @{print}("factor",(Thm.cterm_of ctxt factor))
  val _ = @{print}("lemma",infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt factor),NONE,NONE] @{thm alethe_la_mult_pos_less} )
  val _ = @{print}("lemma",infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt factor),SOME (Thm.cterm_of ctxt l),SOME (Thm.cterm_of ctxt r)] @{thm alethe_la_mult_pos_less} )
*)
in 
 (* SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt factor),NONE,NONE] @{thm alethe_la_mult_pos_less} ]))*)
  SMT_Replay_Methods.prove ctxt t (fn _ =>
(*K (print_tac ctxt "la_mult")
THEN'*) match_tac ctxt @{thms alethe_la_mult_pos}
THEN' TRY' (assume_tac ctxt)
(*THEN' K (print_tac ctxt "la_mult 1")*)
THEN' Simplifier.full_simp_tac ctxt
(*THEN' K (print_tac ctxt "la_mult 2")*)

)

end

fun la_mult_neg ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
(*K (print_tac ctxt "la_mult")       
THEN'*) match_tac ctxt @{thms alethe_la_mult_neg}
THEN' TRY' (assume_tac ctxt)
(*THEN' K (print_tac ctxt "la_mult 1")*)
THEN' Simplifier.full_simp_tac ctxt
(*THEN' K (print_tac ctxt "la_mult 2")*)

)
end

fun poly_simp ctxt _ = 
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
        SOLVED' (
        simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_norm})
        THEN' debug_msg_tac' ctxt high "tried to solve arith_poly_norm with custom simplify tac")
        (*if the previous does not solve, use full simplification power with the current content*)
      ORELSE'
        (simplify_tac_with_background_simp ctxt (Named_Theorems.get ctxt @{named_theorems field_simps})
        THEN' debug_msg_tac' ctxt high "tried full simplifier power on current arith_poly_norm step")
      THEN' TRY' (Code_Simp.dynamic_tac ctxt)
      THEN' debug_msg_tac' ctxt high "tried code evaluation on arith_poly_norm step since nothing else worked")
  in
    prove_abstract (SMT_Replay_Methods.abstract_for_poly_norm ctxt) tac ctxt []
  end

local
  val lemma = @{lemma "((a::'a::{field}) \<noteq> 0 \<and> b \<noteq> 0) \<Longrightarrow> (a / b \<noteq> 0)" by simp}
  val poly_simp_rel_assms_thms = @{thms divide_eq_0_iff ring_char_0_class.neg_numeral_neq_zero zero_neq_one_class.one_neq_zero ring_char_0_class.neg_one_neq_zero semiring_char_0_class.numeral_neq_zero}
in
fun poly_simp_rel ctxt [thm] t =
        SMT_Replay_Methods.prove ctxt t (fn _ => (    
         (resolve_tac ctxt [@{lemma "P \<Longrightarrow> P \<longrightarrow> Q \<Longrightarrow> Q" by simp} OF [thm]] )
         THEN' debug_msg_tac' ctxt high "poly_simp_rel before applying lemma"
         THEN' TRY' (resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_simp_rel}))
         THEN' debug_msg_tac' ctxt high "poly_simp_rel after applying lemma"
         THEN' TRY' (assume_tac ctxt)
         (*TODO: This should be replaced by something quicker.
         For constants cx and cy you'd have to prove that: ((cx > 0) = (cy > 0)), cx \<noteq> 0, cy \<noteq> 0
         For one of the cases you only need to prove the latter two.*)
         THEN' REPEAT' (SOLVED' (partial_simplify_tac ctxt (@{thms poly_simp_rel} @ @{thms arith_simps})))
         THEN' REPEAT' 
            (TRY' (resolve_tac ctxt [lemma])
             THEN' TRY' (resolve_tac ctxt @{thms conjI}) 
             THEN' resolve_tac ctxt poly_simp_rel_assms_thms
             )
         THEN' debug_msg_tac' ctxt high "poly_simp_rel after resolving premises"
         ))
    | poly_simp_rel ctxt thms t = replay_error ctxt "invalid application in some poly_simp_rel rule" Unsupported thms [] t
end

(* Symm and Not_Symm*)

local
  fun prove_symm symm_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [symm_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_symm _  ctxt thms t = replay_error ctxt "invalid application in some symm rule" Unsupported thms [] t
in
  val symm_thm =
  @{lemma \<open>(B = A) \<Longrightarrow> A = B\<close> by blast }
  val symm = prove_symm symm_thm

  val not_symm_thm =
  @{lemma \<open>\<not>(B = A) \<Longrightarrow> \<not>(A = B)\<close> by blast }
  val not_symm = prove_symm not_symm_thm
end

(* Shuffling Clauses and Arguments of Nary Commutative Operators *)

fun reordering ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ => (
    Method.insert_tac ctxt [thm]
    THEN' match_tac ctxt @{thms ccontr}
    THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})
    THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
    THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
    THEN' REPEAT'(ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))
    ))
  | reordering ctxt thms t =
    replay_error ctxt "Too many or no premises in some reordering rule" Unsupported thms [] t

local

fun simplify_shuffle_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps thms addsimps [])
  |> Simplifier.asm_full_simp_tac


in 

fun shuffle ctxt _ _ t (SOME (CommOp @{term "HOL.conj"})) = 
 (prove_abstract (SMT_Replay_Methods.abstract_shuffle @{term "HOL.conj"}) (fn ctxt => fn _ =>
    simplify_shuffle_tac ctxt @{thms Lattices.conj.commute Lattices.conj.left_commute conj_assoc}) ctxt [] t) |
shuffle ctxt _ _ t  (SOME (CommOp @{term "HOL.disj"})) =
  (prove_abstract (SMT_Replay_Methods.abstract_shuffle @{term "HOL.disj"}) (fn ctxt => fn _ =>
    simplify_shuffle_tac ctxt @{thms Lattices.disj.commute Lattices.disj.left_commute disj_assoc}) ctxt [] t) |
shuffle ctxt thms _ t _ =
    replay_error ctxt "Unsupported commutative operator in shuffle rule" Unsupported thms [] t
end

fun contraction ctxt [prem] t = 
  if Term.size_of_term t < 100
  then
    SMT_Replay_Methods.prove ctxt t (fn _ => (
       Method.insert_tac ctxt [prem]
       THEN' match_tac ctxt @{thms ccontr}
       THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})
       THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
       THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
       THEN' REPEAT'(ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))
       ))
   else
    (*cvc5 produces steps with a lot of repetition (think about: 60 times the same literal).
    In those cases, the simplifier is much faster, because it can reduce the size
    of the term.*)
    prove_abstract SMT_Replay_Methods.abstract_bool_shallow (fn ctxt => fn prems => (
       Method.insert_tac ctxt prems
       THEN' simplify_tac ctxt @{thms disj.commute disj.left_commute})) ctxt [prem] t
| contraction ctxt thms t = replay_error ctxt "Unsupported commutative operator in contraction rule" Unsupported thms [] t


fun miniscope_distribute ctxt _ t = 
 SMT_Replay_Methods.prove ctxt t (fn _ => (
    debug_rule_tac' ctxt high Miniscope_Distribute "start" THEN'
    REPEAT_CHANGED
    (
      K (unfold_tac ctxt @{thms alethe_miniscope_distribute})
      THEN' TRY' (debug_rule_tac' ctxt high Miniscope_Distribute "applied lemma")
    )
    THEN' debug_rule_tac' ctxt high Miniscope_Distribute "after repeating application of lemma"
    THEN' TRY' (resolve_tac ctxt @{thms refl})))

fun miniscope_split ctxt _ t = 
 SMT_Replay_Methods.prove ctxt t (fn _ => (
    debug_rule_tac' ctxt high Miniscope_Split "start" THEN'
    REPEAT_CHANGED
    (
      K (unfold_tac ctxt @{thms alethe_miniscope_split})
      THEN' TRY' (debug_rule_tac' ctxt high Miniscope_Split "applied lemma")
    )
    THEN' debug_rule_tac' ctxt high Miniscope_Split "after repeating application of lemma"
    THEN' TRY' (resolve_tac ctxt @{thms refl})
    THEN' TRY' (blast_tac ctxt) (*variable reordering*)
))

fun miniscope_ITE ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ => (
    eqsubst_all ctxt @{thms alethe_miniscope_ITE}
    THEN' TRY' (resolve_tac ctxt @{thms refl})))

fun and_intro ctxt thms t = 
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt thms
  THEN' REPEAT'
   ((match_tac ctxt [@{thm conjI}])
     THEN' TRY' (assume_tac ctxt))
  THEN' TRY' (assume_tac ctxt))

fun trust ctxt _ t = 
  SMT_Replay_Methods.prove ctxt t (fn _ => (
    Skip_Proof.cheat_tac ctxt))
end;
