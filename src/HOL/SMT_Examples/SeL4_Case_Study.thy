section \<open>SeL4 case study\<close>

theory SeL4_Case_Study       
imports "HOL-Library.Word"  "Word_Lib.More_Word" "HOL-Eisbach.Eisbach_Tools" "HOL.SMT_CVC_Word"
"Word_Lib.Aligned" "Word_Lib.Word_EqI" "Word_Lib.Syntax_Bundles" "Word_Lib.Word_Syntax"

begin
unbundle bit_projection_infix_syntax
unbundle filter_syntax

(*
Note: We might miss some context information. Always check the original when
you cannot prove the version here and think you should be.
E.g., L4 uses the following bundle in some places and this will change the behavior of the simplifier
bundle l4v_word_context =
  \<open>?a !! 0 = odd ?a\<close> ["simp" del]
  \<open>?P (of_bool ?p) = (\<not> (?p \<and> \<not> ?P 1 \<or> \<not> ?p \<and> \<not> ?P 0))\<close> ["split" del]
Or I might have missed copying over an assumption.
*)


lemma shiftl_lift:
  "(x << i) \<equiv> push_bit i x"
  unfolding shiftl_def by simp
thm drop_bit_lift_def
lemma shiftr_lift:
  "(x >> i) \<equiv> drop_bit i x"
  unfolding shiftr_def by simp


ML \<open>
val nat_native_ops_tab =
[
("Bit_Shifts_Infix_Syntax.semiring_bit_operations_class.shiftl", @{thms shiftl_lift push_bit_lift}),
("Bit_Shifts_Infix_Syntax.semiring_bit_operations_class.shiftr", @{thms shiftr_lift drop_bit_lift})

]
val ops_tab = fold SMT_Normalize.add_nat_native_ops_tab nat_native_ops_tab
val _ = Theory.setup (Context.theory_map (ops_tab))

\<close>
(*options*)

declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_expert_debug_alethe_files="alethe_replay_bv_methods"]]

declare[[ML_print_depth=1000]]
declare[[smt_verbose=false,smt_trace=true,smt_timeout=10]]


context semiring_bits
begin 

(*Definitions and lemmas used in the lemmas*)

type_synonym word32 = "32 word"

definition asid_high_bits :: nat where
  "asid_high_bits \<equiv> LENGTH(7)"

definition asid_low_bits :: nat where
  "asid_low_bits \<equiv> LENGTH(10)"

definition asid_high_bits_of :: "32 word \<Rightarrow> 7 word" where
  "asid_high_bits_of asid \<equiv> Word.ucast (asid >> asid_low_bits)"

definition asid_bits :: nat where
  "asid_bits \<equiv> LENGTH(17)"

datatype vmpage_size =
    ARMSmallPage
  | ARMLargePage
  | ARMSection
  | ARMSuperSection

definition
pageBitsForSize :: "vmpage_size \<Rightarrow> nat"
where
"pageBitsForSize x0\<equiv> (case x0 of
    ARMSmallPage \<Rightarrow>    12
  | ARMLargePage \<Rightarrow>    16
  | ARMSection \<Rightarrow>    20
  | ARMSuperSection \<Rightarrow>    24
  )"


definition pageBits :: "nat" where
  "pageBits \<equiv> 12"

definition pd_bits :: "nat" where
  "pd_bits \<equiv> pageBits + 2"

definition pde_mapping_bits :: "nat" where
 "pde_mapping_bits \<equiv> pageBitsForSize ARMSection"

type_synonym irq = "8 word" (*simplified this a bit, should be automatically done for the original lemma though*)

definition init_objs_base :: "32 word" where
  "init_objs_base = 0xf0000000"

definition init_irq_node_ptr :: word32 where
  "init_irq_node_ptr = init_objs_base + 0x8000"

definition cte_level_bits :: nat where
  "cte_level_bits \<equiv> 4"

definition
  "vmsz_aligned ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

type_synonym machine_word_len = 32
type_synonym machine_word = \<open>machine_word_len word\<close>
type_synonym vspace_ref         = machine_word

definition page_base :: "vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vspace_ref" where
  "page_base vaddr vmsize \<equiv> vaddr && ~~ mask (pageBitsForSize vmsize)"

definition config_PLAT_OMAP3 :: bool where
  "config_PLAT_OMAP3 \<equiv> False"  (* CONFIG_PLAT_OMAP3 *)

definition pptrBase :: word32 where
  "pptrBase \<equiv> if config_PLAT_OMAP3 then 0xf0000000 else 0xe0000000"

definition pd_asid_slot :: word32
  where "pd_asid_slot \<equiv> 0xff0"

definition valid_pde_mapping_offset' :: "machine_word \<Rightarrow> bool" where
 "valid_pde_mapping_offset' offset \<equiv> offset \<noteq> pd_asid_slot * 4"


(*Definitions and lemmas used in the original proofs*)

(*Quick additions to reconstruction, if successful should be ported to "earlier" in the code base*)

lemmas [bv_reconstruction_const_test] = arith_simps word_0_bl of_bl_False rev.simps of_bl_True append_Nil append_Cons bin_to_bl_aux_Bit0_minus_simp bin_to_bl_aux_Bit1_minus_simp bin_to_bl_aux_zero_minus_simp bin_to_bl_aux.Z bin_last_numeral_simps
drop_bit_int_code int_shiftr_numeral and_one_eq int_and_1
lemmas [bv_reconstruction_length] = smt_word_len_evaluate
lemmas [rbl_bvult_fun] = le_Suc_numeral pred_numeral_simps
lemmas[nat_normalized_input] = Word_eq_word_of_int


(*
Benchmark Nr: 1
Origin:
  l4v/proof/invariant-abstract/ARM/ArchAcc_AI.thy
Description:
  No custom functions & no casts between bit-widths. Is aligned uses power 2.
*)
lemma pde_shifting:
  "\<lbrakk>is_aligned (vptr::word32) 24; x \<le> 0xF\<rbrakk> \<Longrightarrow> x + (vptr >> 20) < 0x1000"
  using is_aligned_iff_take_bit_eq_0
  supply[[smt_trace=false]]
  sorry
(*
  apply (rule order_less_le_trans)
   apply (subst upper_bits_unset_is_l2p_32 [where n=12, symmetric])
    apply (clarsimp simp: word_bits_def)
   prefer 2
   apply simp
  apply (clarsimp simp: word_bits_def)
  subgoal premises prems for n'
  proof -
  have H: "(0xF::word32) < 2 ^ 4" by simp
  from prems show ?thesis
    apply (subst (asm) word_plus_and_or_coroll)
     apply word_eqI
     subgoal for n
       apply (spec "20 + n")
       apply (simp add: word_size)
       apply (insert H)
        apply (drule (1) order_le_less_trans)
        apply (drule bang_is_le)
        apply (drule_tac z="2 ^ 4" in order_le_less_trans, assumption)
        apply (drule word_power_increasing)
        by simp+
    apply (clarsimp simp: word_size nth_shiftl nth_shiftr is_aligned_nth)
    apply (erule disjE)
     apply (insert H)[1]
      apply (drule (1) order_le_less_trans)
      apply (drule bang_is_le)
      apply (drule order_le_less_trans[where z="2 ^ 4"], assumption)
      apply (drule word_power_increasing; simp)
    apply (spec "20 + n'")
      apply (frule test_bit_size) 
    by (simp add: word_size)
  qed
  done
*)

(*
Benchmark Nr: 2
Origin:
  l4v/proof/invariant-abstract/ARM/ArchVSpace_AI.thy
Description:
  Few custom functions (no datatypes) & casts between bit-widths.
  I found the case distinction interesting and want to see what the SMT solver does.
*)
lemma asid_low_high_bits:
  "\<lbrakk> x && mask asid_low_bits = y && mask asid_low_bits;
    ucast (asid_high_bits_of x) = (ucast (asid_high_bits_of y)::word32);
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  sorry
(*
  apply (rule word_eqI)
  apply (simp add: upper_bits_unset_is_l2p_32 [symmetric] bang_eq nth_ucast word_size)
  apply (clarsimp simp: asid_high_bits_of_def nth_ucast nth_shiftr)
  apply (simp add: asid_high_bits_def asid_bits_def asid_low_bits_def word_bits_def)
  subgoal premises prems[rule_format] for n
  apply (cases "n < 10")
   using prems(1)
   apply fastforce
  apply (cases "n < 17")
   using prems(2)[where n="n - 10"]
   apply fastforce
  using prems(3-)
  by (simp add: linorder_not_less)
  done
*)

(*
Benchmark Nr: 3
Origin:
  l4v/proof/invariant-abstract/ARM/ArchIpc_AI.thy
Description:
  Simple helper lemma (inside of a proof) I found interesting, to test goals with datatypes.
  Needs two user defined datatype definitions that basically only define constants though.
Note: the same statement appears in l4v/proof/invariant-abstract/ARM/ArchTcbAcc_AI.thy
*)

lemma aligned_offset_ignore:
    "\<And>(l::word32) (p::word32) sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  sorry
(*
  proof -
    fix l p sz
    assume al: "(p::word32) && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBitsForSize sz" by (case_tac sz, simp_all)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
  qed
*)



(*
Benchmark Nr: 4
Origin:
  l4v/proof/invariant-abstract/ARM/ArchAcc_AI.thy
Description:
  Just a simple and clean lemma
*)

lemma [smt_arith_simplify]: " Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))) =
    (32::nat)"
  by simp
lemma [smt_arith_simplify]: "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) < (32::nat)"
"nat (20::int) \<le> nat (31::int)" "Suc (nat (31::int)) \<le> (32::nat)"
  by simp_all

declare[[smt_expert_debug_alethe_level=0]]
declare[[smt_expert_debug_alethe_files="alethe_replay_bv_methods"]]

declare[[smt_verbose=false,smt_trace=false]]















(*Same lemma but proof with the smt tactic*)

definition pageBits :: "nat" where "pageBits \<equiv> 12"

lemma vptr_shiftr_le_2pu:
  "(vptr :: word32)  >> 20 < 2 ^ pageBits"

  sledgehammer[provers=cvc5_proof]

























(*
Benchmark Nr: 5
Origin:
  l4v/proof/invariant-abstract/ARM/ArchADT_AI.thy
Description:
  Right up our alley, bv operators all around
Note: Apparently also in ArchAcc_R where ever that is
*)


lemma shiftr_shiftl_mask_pd_bits:
  "(((vptr :: word32) >> 20) << 2) && mask pd_bits = (vptr >> 20) << 2"
   apply (smt (cvc5))

  (*
apply (rule iffD2 [OF mask_eq_iff_w2p])
   apply (simp add: pd_bits_def pageBits_def word_size)
  apply (rule shiftl_less_t2n)
   apply (simp_all add: pd_bits_def word_bits_def pageBits_def word_size)
  apply (cut_tac shiftr_less_t2n'[of vptr 20 12])
    apply simp
   apply (simp add: mask_eq_iff)
   apply (cut_tac lt2p_lem[of 32 vptr], simp)
   apply (cut_tac word_bits_len_of, simp)
  done
*)


(*
Benchmark Nr: 6
Origin:
  l4v/proof/invariant-abstract/ARM/ArchAcc_AI.thy
Description:
  Right up our alley, bv operators all around
*)
lemma vptr_shiftr_le_2pt:
  "((vptr :: word32) >> 12) && 0xFF < 2 ^ (pt_bits - 2)"
  sorry
(*
  apply (clarsimp simp: word_FF_is_mask pt_bits_def pageBits_def)
  apply (rule and_mask_less_size[where n=8, simplified])
  apply (clarsimp simp: word_size)
  done
*)


(*
Benchmark Nr: 7
Origin:
  l4v/proof/invariant-abstract/ARM/ArchKernelInit_AI.thy
Description:
  Shift & casts with nat bound.
*)
lemma pde_mapping_bits_shift:
  fixes x :: "12 word"
  shows "x \<noteq> 0 \<Longrightarrow> 2 ^ pde_mapping_bits - 1 < (ucast x << pde_mapping_bits :: word32)"
  sorry
(*
  apply (simp only:shiftl_t2n pde_mapping_bits_def)
  apply (unfold word_less_alt)
  apply simp
  apply (unfold word_mult_def)
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply simp
   apply (subst uint_up_ucast)
    apply (simp add: is_up_def source_size_def target_size_def word_size)
   apply (cut_tac 'a = "12" and x = x in uint_lt2p)
   apply simp
  apply (rule order_less_le_trans)
   prefer 2
   apply (rule pos_mult_pos_ge)
    apply (subst uint_up_ucast)
     apply (simp add: is_up_def source_size_def target_size_def word_size)
    apply (simp add: word_neq_0_conv word_less_alt)
   apply simp
  apply simp
  done
*)

(*
Benchmark Nr: 8
Origin:
  l4v/proof/invariant-abstract/ARM/ArchKernelInit_AI.thy
Description:
  Bit-vector addition
*)
lemma init_irq_ptrs_ineqs:
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + 2 ^ cte_level_bits - 1
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
  sorry
(*
proof -
  have P: "ucast irq < (2 ^ (14 - cte_level_bits) :: word32)"
    apply (rule order_le_less_trans[OF
        ucast_le_ucast[where 'a=irq_len and 'b=32,simplified,THEN iffD2, OF word_n1_ge]])
    apply (simp add: cte_level_bits_def minus_one_norm)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
    apply (rule is_aligned_no_wrap'[where sz=14])
     apply (simp add: is_aligned_def init_irq_node_ptr_def init_objs_base_def)
    apply (rule shiftl_less_t2n[OF P])
    apply simp
    done
  show Q: "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + 2 ^ cte_level_bits - 1
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
    apply (simp only: add_diff_eq[symmetric] add.assoc)
    apply (rule word_add_le_mono2)
     apply (simp only: trans [OF shiftl_t2n mult.commute])
     apply (rule nasty_split_lt[OF P])
      apply (simp_all add: cte_level_bits_def word_bits_def init_objs_base_def
                           init_irq_node_ptr_def)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
    apply (simp only: add_diff_eq[symmetric])
    apply (rule word_add_le_mono2)
     apply (rule word_le_minus_one_leq, rule shiftl_less_t2n[OF P])
     apply simp
    apply (simp add: init_objs_base_def cte_level_bits_def word_bits_def init_irq_node_ptr_def)
    done
qed
*)


(*
Benchmark Nr: 9
Origin:
  l4v/proof/invariant-abstract/ARM/ArchAcc_AI.thy
Description:
  BV addition shifts and one simple function with datatypes
*)
lemma vptr_shifting_helper_magic:
  "(x = 0) \<or> (x < 2 ^ 4 \<and> vmsz_aligned (vptr::word32) ARMSuperSection)
   \<Longrightarrow> (x << 2) + (vptr >> 20 << 2) = ((vptr + (x << 20)) >> 20 << 2)"
  sorry
(*
  apply (erule disjE, simp_all)
  apply (clarsimp simp: vmsz_aligned_def)
  apply (subst is_aligned_add_or, assumption)
   apply (rule shiftl_less_t2n)
    apply simp
   apply simp
  apply (simp add: shiftl_over_or_dist shiftr_over_or_dist)
  apply (subst shiftl_shiftr_id)
    apply (simp add: word_bits_def)
   apply (simp add: word_bits_def)
   apply unat_arith
  apply (subst field_simps, rule is_aligned_add_or[where n=6])
   apply (intro is_aligned_shiftl is_aligned_shiftr)
   apply simp
  apply (rule shiftl_less_t2n, simp_all)
  done
*)

(*
Benchmark Nr: 10
Origin:
  l4v/proof/invariant-abstract/ARM/TcbAcc_AI.thy
Description:

Note: Formerly parametric bit-width, I restricted the length because I liked this so much.
Orignal Proof might not work anymore.
*)
lemma shiftr_eq_mask_eq:
  "(a::32 word) && ~~ mask b = c && ~~ mask b \<Longrightarrow> a >> b = c >> b"
  sorry
(*
  apply (rule word_eqI)
  apply (drule_tac x="b + n" in word_eqD)
  apply (case_tac "b + n < size a")
   apply (simp add: nth_shiftr word_size word_ops_nth_size)
  apply (auto dest!: test_bit_size simp: word_size)
  done
*)


(*
Benchmark Nr: 11
Origin:
  l4v/proof/invariant-abstract/ARM/Untyped_AI.thy
Description:

Note: Formerly parametric bit-width, I restricted the length because I liked this so much.
Orignal Proof might not work anymore.

*)
lemma shiftr_and_eq_shiftl:
  fixes w x y :: "32 word"
  assumes r: "(w >> n) && x = y"
  shows "w && (x << n) = (y << n)"
  sorry
(*
  using assms
  proof -
    { fix i
      assume i: "i < LENGTH('a)"
      hence "test_bit (w && (x << n)) i \<longleftrightarrow> test_bit (y << n) i"
        using word_eqD[where x="i-n", OF r]
        by (cases "n \<le> i") (auto simp: nth_shiftl nth_shiftr)
    }
    thus ?thesis using word_eq_iff by blast
  qed
*)

(*
Benchmark Nr: 12
Origin:
  l4v/proof/invariant-abstract/AARCH64/ArchMove_C.thy
Description:
*)
lemma more_pageBits_inner_beauty:
  fixes x :: "9 word"
  fixes p :: machine_word
  assumes x: "x \<noteq> ucast (p && mask pageBits >> 3)"
  shows "(p && ~~ mask pageBits) + (ucast x * 8) \<noteq> p"
  sorry
(*
  apply clarsimp
  apply (simp add: word_shift_by_3)
  apply (subst (asm) word_plus_and_or_coroll)
   apply (word_eqI_solve dest: test_bit_size simp: pageBits_def)
  apply (insert x)
  apply (erule notE)
  apply word_eqI
  apply (erule_tac x="3+n" in allE)
  apply (clarsimp simp: word_size pageBits_def)
  done
*)

(*
Benchmark Nr: 13
Origin:
  l4v/proof/invariant-abstract/ARM/ARCH_C.thy
Description:
*)

lemma shiftr_asid_low_bits_mask_eq_0:
  "\<lbrakk> (asid :: word32) \<le> mask asid_bits; asid >> asid_low_bits = 0 \<rbrakk>
        \<Longrightarrow> (asid && mask asid_low_bits = 0) = (asid = 0)"
  sorry
(*
  apply (rule iffI[rotated])
   apply simp
  apply (rule asid_low_high_bits)
     apply simp
    apply (simp add: ucast_asid_high_bits_is_shift)
   apply (simp add: mask_def)
  apply simp
  done
*)

(*
Benchmark Nr: 14
Origin:
  l4v/proof/invariant-abstract/ARM/ARCH_C.thy
Description:
*)

lemma flush_range_le_helper:
  assumes assms: "page_base start a = page_base end a"
        "start \<le> end" "w && mask (pageBitsForSize a) = start && mask (pageBitsForSize a)"
      shows  "w && mask (pageBitsForSize a) \<le> (w && mask (pageBitsForSize a)) + (end - start)"
  sorry
(*
    using assms
    apply (subst AND_NOT_mask_plus_AND_mask_eq
      [where w = start,symmetric,where n = "pageBitsForSize a"])
    apply (simp add: page_base_def)
    apply (drule word_le_minus_mono_left[where x= "start && ~~ mask (pageBitsForSize a)"])
     apply (rule word_and_le2)
    apply (simp(no_asm_use), simp)
    done
*)

(*
Benchmark Nr: 15
Origin:
  l4v/proof/invariant-abstract/ARM/ARCH_R.thy
Description:
*)
lemma less_pptrBase_valid_pde_offset':
  "\<lbrakk> vptr < pptrBase; x = 0 \<or> is_aligned vptr 24; x \<le> 0xF \<rbrakk>
     \<Longrightarrow> valid_pde_mapping_offset' (((x * 4) + (vptr >> 20 << 2)) && mask pdBits)"
(*
  apply (clarsimp simp: pdBits_def pageBits_def
                        valid_pde_mapping_offset'_def pd_asid_slot_def)
  apply (drule word_le_minus_one_leq, simp add: pdeBits_def)
  apply (drule le_shiftr[where u=vptr and n=20])
  apply (subst(asm) iffD2[OF mask_eq_iff_w2p])
    apply (simp add: word_size)
   apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem] pptrBase_def
               split: if_split_asm)
  apply (erule disjE)
   apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem] pptrBase_def
               split: if_split_asm)
  apply (frule arg_cong[where f="\<lambda>v. v && mask 6"])
  apply (subst(asm) field_simps, subst(asm) is_aligned_add_helper[where n=6],
         rule is_aligned_shiftl)
    apply (rule is_aligned_shiftr, simp)
   apply (simp add: unat_arith_simps iffD1[OF unat_mult_lem])
  apply (simp add: mask_def[where n=6])
  apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem] pptrBase_def
              split: if_split_asm)
  done
*)



(*TODO
Benchmark Nr: 
Origin:
  l4v/proof/refine/ARM/ArchArchAcc_R.thy
Description:
  Quantification unfortunately also sets and fairly complicated.
  Maybe we can replace this with something better eventually
  or just unfold the set to a property first.
*)
lemma obj_relation_cuts_range_limit:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk>
   \<Longrightarrow> \<exists>x n. p' = p + x \<and> is_aligned x n \<and> n \<le> obj_bits ko \<and> x \<le> mask (obj_bits ko)"
(*
  apply (erule (1) obj_relation_cutsE; clarsimp)
        apply (drule (1) wf_cs_nD)
        apply (clarsimp simp: cte_map_def simp flip: shiftl_t2n')
        apply (rule_tac x=cte_level_bits in exI)
        apply (simp add: is_aligned_shift of_bl_shift_cte_level_bits)
       apply (rule_tac x=tcbBlockSizeBits in exI)
       apply (simp add: tcbBlockSizeBits_def)
      apply (rule_tac x=pteBits in exI)
      apply (simp add: bit_simps is_aligned_shift mask_def pteBits_def)
      apply word_bitwise
     apply (rule_tac x=pdeBits in exI)
     apply (simp add: bit_simps is_aligned_shift mask_def pdeBits_def)
     apply word_bitwise
    apply (rule_tac x=pageBits in exI)
    apply (simp add: is_aligned_shift pbfs_atleast_pageBits is_aligned_mult_triv2)
    apply (simp add: mask_def shiftl_t2n mult_ac)
    apply (frule word_less_power_trans2, rule pbfs_atleast_pageBits)
     apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
    apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
   apply fastforce+
  done
*)
end