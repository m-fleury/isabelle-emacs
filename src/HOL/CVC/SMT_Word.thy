theory SMT_Word
  imports SMT_CVC "HOL-Library.Word" "HOL.Real" "cvc5_dsl_rewrites/Rare_Interface"
    "HOL-Library.Sublist" "HOL-Library.Log_Nat"
begin
declare  [[smt_cvc_lethe = true]]

lemma cvc_ListOp_neutral_bv_and [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (semiring_bit_operations_class.and) (-1::'a::len word))"
  by auto
lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (word_cat) y (ListVar xs) = (if xs = [] then y else (word_cat) y (fold (word_cat) (butlast xs) (last xs)))"
  apply (induction xs)
   apply (simp add: cvc_list_right_def)
  by (metis (no_types, opaque_lifting) Dsl_Nary_Ops.cvc_nary_op_fold_Cons Dsl_Nary_Ops.cvc_nary_op_fold_Nil butlast.simps(2) cvc_bin_op2.simps cvc_list_right_def fold_simps(1) fold_simps(2) last.simps neq_Nil_conv word_cat_id)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (semiring_bit_operations_class.and) y (ListVar xs) = (semiring_bit_operations_class.and) y (foldr (semiring_bit_operations_class.and) xs (-1::'a::len word))"
  by (simp add: cvc_list_right_transfer smtlib_str_concat_def)

subsection \<open>Tool support\<close>

context
begin
qualified definition smt_extract  :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'b ::len word" where
  \<open>smt_extract j i w = slice i (take_bit (Suc j) w)\<close>

(* Use x!0 \<and> (x & (x-1)) = 0 somehow? Do I need to cast everything to word?
(i = 0) \<and> ((and (Word.Word i) ((Word.Word i)-1)) = 0)
*)
definition is_pow2 :: "int \<Rightarrow> bool" where
  \<open>is_pow2 i \<equiv> (i = 0) \<and> (and i (i-1) = 0)\<close>


fun repeat where
"repeat (Suc 0) x = x" |
"repeat (Suc n) x = word_cat x (repeat n x)"

definition smt_repeat :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
  \<open>smt_repeat i x = repeat i x\<close>


(*

(define-rule bv-redor-eliminate ((x ?BitVec)) (bvredor x) (not (bvcomp x (bv 0 (bvsize x)))))
(define-rule bv-redand-eliminate ((x ?BitVec)) (bvredand x) (not (bvcomp x (not (bv 0 (bvsize x))))))
*)

definition smt_comp :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 1 word" where
  \<open>smt_comp x y = (if (x = y) then 1 else 0)\<close>

definition smt_redor :: "'a::len word \<Rightarrow> 1 word" where
  \<open>smt_redor x = not (smt_comp x 0)\<close>

definition smt_redand :: "'a::len word \<Rightarrow> 1 word" where
  \<open>smt_redand x = not (smt_comp x (not (0::'a word)))\<close>

(*'c is 'a + 1*)
definition smt_uaddo  :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_uaddo x y = (smt_extract (size x) (size x)
 ((Word.word_cat (0::1 word) x) + (Word.word_cat (0::1 word) y) :: 'c::len word) = (1:: 1 word))"

definition smt_saddo :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_saddo x y = (smt_extract ((size x)-1) ((size y)-1)
 ((Word.word_cat (0::1 word) x) + (Word.word_cat (0::1 word) y) :: 'c::len word) = (1:: 1 word))"

definition smt_sdivo :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_sdivo x y = (x = (word_cat (1::1 word) (0::'c::len word)::'a word) \<and> y = (mask (size y)::'b word))"

definition smt_usubo :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where
"smt_usubo x y = ((smt_extract ((size x)-1) ((size y)-1) (Word.cast x - Word.cast y)) = (1::1 word))"
(*(define-rule bv-ssubo-eliminate
	((x ?BitVec) (y ?BitVec))
	(def
		(n (bvsize x))
		(xLt0 (= (extract (- n 1) (- n 1) x) (bv 1 1)))
		(yLt0 (= (extract (- n 1) (- n 1) y) (bv 1 1)))
		(s (bvsub x y))
		(sLt0 (= (extract (- n 1) (- n 1) s) (bv 1 1)))
	)
	(bvssubo x y)
	(or
		(and xLt0 (not yLt0) (not sLt0))
		(and (not xLt0) yLt0 sLt0)))*)
definition smt_ssubo :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where (*TODO*)
"smt_ssubo x y = 
(let n = size x in 
(let xLt0 = ((smt_extract ((size x)-1) ((size x)-1) x) = (1::1 word)) in
(let yLt0 = ((smt_extract ((size x)-1) ((size x)-1) y) = (1::1 word)) in
(let sLt0 = ((smt_extract ((size x)-1) ((size x)-1) (x -y)) = (1::1 word)) in
((xLt0 \<and> \<not>yLt0 \<and> \<not>sLt0) \<or> (\<not>xLt0 \<and> yLt0 \<and> sLt0))))))
"


definition smt_urem :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_urem s t = (if (unat s = 0) then s
 else of_nat ((unat s) mod (unat t)))"

definition smt_smod :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_smod s t =
(let size_s = size s in
(let msb_s = smt_extract (size_s-1) (size_s-1) s in
(let msb_t = smt_extract (size_s-1) (size_s-1) t in 
(let abs_s = (if (msb_s = (0::1 word)) then s else -s) in 
(let abs_t = (if (msb_t = (0::1 word)) then t else -t) in 
(let u = (smt_urem abs_s abs_t) in 
(if (u = (0::'a word)) then u
 else if ((msb_s = (0::1 word)) \<and> (msb_t = (0::1 word))) then u
 else if ((msb_s = (1::1 word)) \<and> (msb_t = (0::1 word))) then (-u + t)
 else if ((msb_s = (0::1 word)) \<and> (msb_t = (1::1 word))) then (u + t)
 else -u)))))))
"

definition smt_srem :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_srem s t =
(let size_s = size s in
(let msb_s = smt_extract (size_s-1) (size_s-1) s in
(let msb_t = smt_extract (size_s-1) (size_s-1) t in 
(if ((msb_s = (0::1 word)) \<and> (msb_t = (0::1 word)))
 then (smt_urem s t)
 else (if ((msb_s = 1) \<and> (msb_t = 0))
 then (- (smt_urem (-s) t))
 else (if ((msb_s = 0) \<and> (msb_t = 1))
 then (smt_urem s (-t))
 else (- (smt_urem (-s) (-t)))
))))))
"

end
(*

ML \<open>Lethe_Replay_Methods.print_alethe_tac (Context.Proof @{context})\<close>
ML \<open>
local

  val nat_as_int_bv = Attrib.setup_config_bool \<^binding>\<open>smt_nat_as_int_bv\<close> (K false)
  val simple_nat_ops = [
    @{const HOL.eq (nat)}, @{const less (nat)}, @{const less_eq (nat)},
    \<^const>\<open>Suc\<close>, @{const plus (nat)}, @{const minus (nat)}]

  val nat_consts = simple_nat_ops @
    [@{const numeral (nat)}, @{const zero_class.zero (nat)}, @{const one_class.one (nat)}] @
    [@{const times (nat)}, @{const divide (nat)}, @{const modulo (nat)}] @
    [@{term \<open>unsigned :: 'a :: len word \<Rightarrow> nat\<close>}, @{const of_nat (nat)} ] @
    [@{term \<open>unat :: 'a :: len word \<Rightarrow> nat\<close>}]

  fun is_nat_const x = if member (Term.aconv_untyped) nat_consts x then (@{print} x; true) else false
  val bv_thms = @{lemma "int (unat v) = uint v"
 by simp_all} |> single
  val nat_int_thm = map (Thm.symmetric o mk_meta_eq) (bv_thms @ @{thms nat_int})
|> @{print}
  val nat_int_comp_thms = map mk_meta_eq (@{thms nat_int_comparison})
  val int_ops_thms = map mk_meta_eq @{thms int_ops}
  val int_if_thm = mk_meta_eq @{thm int_if}

  fun if_conv cv1 cv2 = Conv.combination_conv (Conv.combination_conv (Conv.arg_conv cv1) cv2) cv2

  fun int_ops_conv cv ctxt ct =
    (case Thm.term_of ct of
      @{const of_nat (int)} $ (Const (\<^const_name>\<open>If\<close>, _) $ _ $ _ $ _) =>
        Conv.rewr_conv int_if_thm then_conv
        if_conv (cv ctxt) (int_ops_conv cv ctxt)
    | @{const of_nat (int)} $ _ =>
        (Conv.rewrs_conv int_ops_thms then_conv
          Conv.top_sweep_conv (int_ops_conv cv) ctxt) else_conv
        Conv.arg_conv (Conv.sub_conv cv ctxt)
    | _ => Conv.no_conv) ct

  val unfold_nat_let_conv = Conv.rewr_conv @{lemma "Let (n::nat) f \<equiv> f n" by (rule Let_def)}
  val drop_nat_int_conv = Conv.rewrs_conv (map Thm.symmetric nat_int_thm |> @{print})


  fun nat_to_int_conv ctxt ct = (
    Conv.top_conv (K (Conv.try_conv unfold_nat_let_conv)) ctxt then_conv
    (Conv.top_conv nat_conv ctxt else_conv Conv.all_conv) then_conv
    Conv.top_conv (K (Conv.try_conv drop_nat_int_conv)) ctxt) (@{print}ct)
|> tap (@{print} o Thm.cprop_of)

  and nat_conv ctxt ct = (
      (Conv.rewrs_conv (nat_int_thm @ nat_int_comp_thms) then_conv
      Conv.top_conv (int_ops_conv nat_to_int_conv) ctxt)
      else_conv Conv.all_conv) (@{print}ct)
|> tap (@{print} o Thm.cprop_of)

  fun add_int_of_nat vs ct cu (q, cts) =
    (case Thm.term_of ct of
      @{const of_nat(int)} =>
        if Term.exists_subterm (member (op aconv) vs) (Thm.term_of cu) then (true, cts)
        else (q, insert (op aconvc) cu cts)
    | _ => (q, cts))

  fun add_apps f vs ct = 
    (case Thm.term_of ct of
      _ $ _ =>
        let val (cu1, cu2) = Thm.dest_comb ct
        in f vs cu1 cu2 #> add_apps f vs cu1 #> add_apps f vs cu2 end
    | Abs _ =>
        let val (cv, cu) = Thm.dest_abs_global ct
        in add_apps f (Thm.term_of cv :: vs) cu end
    | _ => I)

  val int_thm = @{lemma "(0::int) <= int (n::nat)" by simp}
  val nat_int_thms = @{lemma
    "\<forall>n::nat. (0::int) <= int n"
    "\<forall>n::nat. nat (int n) = n"
    "\<forall>i::int. int (nat i) = (if 0 <= i then i else 0)"
    by simp_all}
  val var = Term.dest_Var (Thm.term_of (funpow 3 Thm.dest_arg (Thm.cprop_of int_thm)))
in

fun nat_as_int_conv ctxt = SMT_Util.if_exists_conv is_nat_const (nat_to_int_conv ctxt)

fun add_int_of_nat_constraints thms =
  let
 val (q, cts) = fold (add_apps add_int_of_nat [] o Thm.cprop_of) thms (false, [])
  in
    if q then (thms, nat_int_thms)
    else (thms, map (fn ct => Thm.instantiate (TVars.empty, Vars.add (var, ct) Vars.empty) int_thm) cts)
  end

  val setup_nat_as_int =
    fold (SMT_Builtin.add_builtin_fun_ext' o Term.dest_Const) simple_nat_ops
  val _ = Theory.setup (Context.theory_map (setup_nat_as_int))
  val _ = SMT_Normalize.add_normalization "nat_as_int_bv" (nat_as_int_bv, nat_as_int_conv, add_int_of_nat_constraints)
   |> Theory.setup o Context.theory_map 
end
\<close>

type_synonym w32 = "32 word"

declare [[show_types=true]]
declare [[cvc4_options = "--proof-format-mode=alethe --produce-proofs --simplification=none --dag-thres=0 --lang=smt2 --full-saturate-quant"]]

declare [[smt_nat_as_int_bv=true,smt_nat_as_int]]


(*
definition bound :: nat where
  [simplified, simp]: "bound = unat (2^11 :: w32)"

definition bseg :: "w32 \<Rightarrow> w32 \<Rightarrow> bool" where
  [simp]: "bseg x s \<longleftrightarrow> unat x < bound \<and> unat x + unat s \<le> bound"

lemma \<open>LENGTH(32) = 32\<close>
  supply [[smt_trace]]
  apply (smt (cvc4))
  oops

ML \<open>@{term \<open>LENGTH(32) = 32\<close>}\<close>
term len_of

declare [[cvc4_options = "--proof-format-mode=alethe --produce-proofs --simplification=none --dag-thres=0 --lang=smt2 --full-saturate-quant"]]

lemma b2:
  assumes
  "bseg x s"
   "i < unat s"
 shows "unat x + i < bound"
  supply [[smt_trace,smt_nat_as_int=true,smt_nat_as_int_bv=true]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto

lemma b2:
  fixes a :: nat
  assumes
  "bseg x s"
   "i < unat s" and
   "a < 2"
 shows "unat x + i < bound"
  supply [[smt_trace,smt_nat_as_int=true,smt_nat_as_int_bv=true]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto

ML \<open>@{term "unat :: w32 \<Rightarrow> nat"} aconv @{term "unat :: 'a :: len word \<Rightarrow> nat"}\<close>
ML \<open>
SMT_Config.solver_class_of @{context}
\<close>

definition bound :: int where
  [simplified, simp]: "bound = uint (2^11 :: w32)"

definition bseg :: "w32 \<Rightarrow> w32 \<Rightarrow> bool" where
  [simp]: "bseg x s \<longleftrightarrow> uint x < bound \<and> uint x + uint s \<le> bound"

(* bv2nat *)
lemma b2:
  assumes
  "bseg x s"
   "i < uint s"
 shows "uint x + i < bound"
  supply [[smt_trace,smt_nat_as_int=false]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto

ML \<open>

open Word_Lib;
let
  fun if_fixed pred m n T ts =
    let val (Us, U) = Term.strip_type T
    in
      if pred (U, Us) then SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T))) else NONE
    end

  fun is_conv [(Type (\<^type_name>\<open>Int.int\<close>, [])), a] = can dest_wordT a
    | is_conv x = (@{print} x; false)

  fun if_fixed_all m = if_fixed (is_conv o (op ::)) m
in
if_fixed_all "string" "t" @{typ "w32 \<Rightarrow> int"} "e"
end
\<close>
*)

ML \<open>
(Scan.optional (\<^keyword>\<open>(\<close> |-- (Parse.string ) --|
      \<^keyword>\<open>)\<close>)
    "cvc4"
)
\<close>
lemmas [arith_poly_norm] =  realrel_def

ML_file \<open>Tools/SMT/SMT_string.ML\<close>

ML \<open>
local
  fun int_num _ i = SOME (string_of_int i)

  fun is_linear [t] = SMT_Util.is_number t
    | is_linear [t, u] = SMT_Util.is_number t orelse SMT_Util.is_number u
    | is_linear _ = false

  fun times _ _ ts =
    let val mk = Term.list_comb o pair \<^Const>\<open>times \<^Type>\<open>int\<close>\<close>
    in if is_linear ts then SOME ("*", 2, ts, mk) else NONE end
in

val setup_builtins =
fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
(\<^Const>\<open>divide \<^Type>\<open>Real.real\<close>\<close>, "/") (*TODO Hanna: This should go in a CVC5_Interface file similar to Z3_Interface.*)
(*Shouldn't this be done elsewhere? Might be the bug Mathias mentioned about not using the Real files correctly*)
] #>
  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (Term.dest_Const \<^Const>\<open>times \<^Type>\<open>int\<close>\<close>, times)
end
\<close>
*)
end