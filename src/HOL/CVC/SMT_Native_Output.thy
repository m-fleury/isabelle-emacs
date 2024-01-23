theory SMT_Native_Output
  imports SMT_CVC
begin

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


declare [[smt_nat_as_int_bv=true,smt_nat_as_int]]


definition bound :: nat where
  [simplified, simp]: "bound = unat (2^11 :: 32 word)"

definition bseg :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool" where
  [simp]: "bseg x s \<longleftrightarrow> unat x < bound \<and> unat x + unat s \<le> bound"

lemma b2:
  assumes
  "bseg x s"
   "i < unat s"
 shows "unat x + i < bound"
  supply [[smt_trace,smt_nat_as_int=true,smt_nat_as_int_bv=true,smt_trace]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc5))
  using assms by auto
end
