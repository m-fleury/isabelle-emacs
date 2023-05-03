(*  Title:      HOL/Library/Tools/smt_word.ML
    Author:     Sascha Boehme, TU Muenchen

SMT setup for words.
*)

signature SMT_WORD =
sig
  val add_word_shift': term * string -> Context.generic -> Context.generic

   val bv_type_parser : SMTLIB.tree * typ list -> typ option
   val bv_term_parser :  SMTLIB.tree * term list -> term option
end

structure SMT_Word : SMT_WORD =
struct

open Word_Lib

(* SMT-LIB logic *)

(* "QF_AUFBV" is too restrictive for Isabelle's problems, which contain aritmetic and quantifiers.
   Better set the logic to "" and make at least Z3 happy. *)
fun smtlib_logic "z3" ts =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts then SOME "" else NONE
  | smtlib_logic "verit" _ = NONE
  | smtlib_logic _ ts =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts then SOME "AUFBVLIRA" else NONE


(* SMT-LIB builtins *)

local
  val smtlibC = SMTLIB_Interface.bvsmlibC

  val wordT = \<^typ>\<open>'a::len word\<close>

  fun index1 s i = "(_ " ^ s ^ " " ^ string_of_int i ^ ")"
  fun index2 s i j = "(_ " ^ s ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^ ")"

  fun word_typ (Type (\<^type_name>\<open>word\<close>, [T])) =
      (@{print}("T sss", T);Option.map (rpair [] o index1 "BitVec") (try dest_binT T))
    | word_typ _ = NONE

  (*CVC4 does not support "_bvk T" when k does not fit in the BV of size T, so remove the bits that
   will be ignored according to the SMT-LIB*)
  fun word_num (Type (\<^type_name>\<open>word\<close>, [T])) k =
        let
          val size = try dest_binT T
          fun max_int size = Integer.pow size 2
        in
          (case size of
            NONE => NONE
          | SOME size => SOME (index1 ("bv" ^ string_of_int (Int.rem(k, max_int size))) size))
        end
    | word_num _ _ = NONE

  fun if_fixed pred m n T ts =
    let val (Us, U) = Term.strip_type T
    in
      if pred (U, Us) then SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T))) else NONE
    end

  fun if_fixed_all m = if_fixed (forall (can dest_wordT) o (op ::)) m
  fun if_fixed_args m = if_fixed (forall (can dest_wordT) o snd) m

  fun is_conv [(Type (\<^type_name>\<open>Int.int\<close>, [])), a] = can dest_wordT a
    | is_conv x = (@{print} ("not conv",x); false)

  fun is_word_to_uint m = if_fixed (is_conv o (op ::)) m

  fun is_conv [a, (Type (\<^type_name>\<open>Int.int\<close>, []))] = can dest_wordT a
    | is_conv x = (@{print} ("not conv",x); false)

  fun is_uint_to_word m = if_fixed (is_conv o (op ::)) m

  fun add_word_fun f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end

  val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>

  fun mk_shift c [u, t] = Const c $ mk_nat (snd (HOLogic.dest_number u)) $ t
    | mk_shift c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift m n T ts =
    let val U = Term.domain_type (Term.range_type T)
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) =>
          SOME (n, 2, [hd (tl ts), HOLogic.mk_number U i], mk_shift (m, T))
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

  fun mk_shift' c [t, u] = Const c $ t $ mk_nat (snd (HOLogic.dest_number u))
    | mk_shift' c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift' m n T ts =
    let val U = Term.domain_type T
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd o tl) ts) of
        (true, SOME i) =>
          SOME (n, 2, [hd ts, HOLogic.mk_number U i], mk_shift' (m, T))
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

  fun mk_extract c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun extract m n T ts =
    let val U = Term.range_type (Term.range_type T)
    in
      (case (try (snd o HOLogic.dest_number o hd) ts, try dest_wordT U) of
        (SOME lb, SOME i) =>
          SOME (index2 n (i + lb - 1) lb, 1, tl ts, mk_extract (m, T) lb)
      | _ => NONE)
    end

  fun mk_extend c ts = Term.list_comb (Const c, ts)

  fun extend m n T ts =
    let val (U1, U2) = Term.dest_funT T
    in
      (case (try dest_wordT U1, try dest_wordT U2) of
        (SOME i, SOME j) =>
          if j-i >= 0 then SOME (index1 n (j-i), 1, ts, mk_extend (m, T))
          else NONE
      | _ => NONE)
    end

  fun mk_rotate c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun rotate m n T ts =
    let val U = Term.domain_type (Term.range_type T)
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) => SOME (index1 n i, 1, tl ts, mk_rotate (m, T) i)
      | _ => NONE)
    end
in
(*Generate smt-problem*)
val setup_builtins =
  SMT_Builtin.add_builtin_typ smtlibC (wordT, word_typ, word_num) #>
  fold (add_word_fun if_fixed_all) [
    (\<^term>\<open>uminus :: 'a::len word \<Rightarrow> _\<close>, "bvneg"),
    (\<^term>\<open>plus :: 'a::len word \<Rightarrow> _\<close>, "bvadd"),
    (\<^term>\<open>minus :: 'a::len word \<Rightarrow> _\<close>, "bvsub"),
    (\<^term>\<open>times :: 'a::len word \<Rightarrow> _\<close>, "bvmul"),
    (\<^term>\<open>not :: 'a::len word \<Rightarrow> _\<close>, "bvnot"),
    (\<^term>\<open>and :: 'a::len word \<Rightarrow> _\<close>, "bvand"),
    (\<^term>\<open>or :: 'a::len word \<Rightarrow> _\<close>, "bvor"),
    (\<^term>\<open>Bit_Operations.xor :: 'a::len word \<Rightarrow> _\<close>, "bvxor"),
    (\<^term>\<open>word_cat :: 'a::len word \<Rightarrow> _\<close>, "concat") ] #>
  fold (add_word_fun shift) [
    (\<^term>\<open>push_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _ \<close>, "bvshl"),
    (\<^term>\<open>drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>signed_drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvashr") ] #>
  add_word_fun extract
    (\<^term>\<open>slice :: _ \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "extract") #>
  fold (add_word_fun extend) [
    (\<^term>\<open>ucast :: 'a::len word \<Rightarrow> _\<close>, "zero_extend"),
    (\<^term>\<open>scast :: 'a::len word \<Rightarrow> _\<close>, "sign_extend") ] #>
  fold (add_word_fun rotate) [
    (\<^term>\<open>word_rotl\<close>, "rotate_left"),
    (\<^term>\<open>word_rotr\<close>, "rotate_right") ] #>
  fold (add_word_fun if_fixed_args) [
    (\<^term>\<open>less :: 'a::len word \<Rightarrow> _\<close>, "bvult"),
    (\<^term>\<open>less_eq :: 'a::len word \<Rightarrow> _\<close>, "bvule"),
    (\<^term>\<open>word_sless\<close>, "bvslt"),
    (\<^term>\<open>word_sle\<close>, "bvsle") ] #>
  fold (add_word_fun is_word_to_uint) [
    (\<^term>\<open>unsigned :: 'a::len word \<Rightarrow> int\<close>, "bv2nat") ] #>
  fold (add_word_fun is_uint_to_word) [
    (\<^term>\<open>word_of_int :: int \<Rightarrow> 'a::len word\<close>, "nat2bv") ]


val add_word_shift' = add_word_fun shift'

fun mk_unary n t =
  let val T = fastype_of t
  in Const (n, T --> T) $ t end

val split_last =
  let fun split_last [a] = ([], a)
       | split_last (x :: xs) = apfst (curry (op ::) x) (split_last xs)
  in apfst List.rev o split_last end

fun mk_concat (t, u) =
  let
    val T = fastype_of t
    val _ = @{print}("fastype_of t",fastype_of t)
    val U = fastype_of u

    (*TODO: If one of them is not concrete we need to use LENGTH('a) here. But how to add the extra restriction that LENGTH('c) = LENGTH('a) + LENGTH('b)?*)
    (*val TU = Word_Lib.dest_wordT T + Word_Lib.dest_wordT U
          |> Word_Lib.mk_wordT*)
    val TU = (TVar (("?a", serial ()), []))
  in Const (\<^const_name>\<open>Word.word_cat\<close>, T --> U --> TU) $ t $ u end;

fun mk_extract i j u =
  let
    val I = HOLogic.mk_number \<^typ>\<open>nat\<close> i
    val J = HOLogic.mk_number \<^typ>\<open>nat\<close> j
    val T = fastype_of u
    val TU = i - j + 1
          |> Word_Lib.mk_wordT
  in Const (\<^const_name>\<open>SMT.smt_extract\<close>, @{typ nat} --> @{typ nat} --> T --> TU) $ J $ I $ u end;

fun mk_zero_extend i u =
  let
    val T = fastype_of u
    val TU = Word_Lib.mk_wordT i
  in Const (\<^const_name>\<open>Word.cast\<close>, T --> TU) $ u end;

fun mk_scast i u =
  let
    val T = fastype_of u
    val TU = Word_Lib.mk_wordT i
  in Const (\<^const_name>\<open>Word.signed\<close>, T --> TU) $ u end;

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t
fun mk_test (t1, t2) = (Const (\<^const_name>\<open>Word.word_cat\<close>, dummyT --> dummyT --> dummyT))  $ t1 $ t2

fun bv_term_parser (SMTLIB.Sym bv, []) =
      (case try (unprefix "bv") bv of
        NONE => NONE
(*TODO*)
      (*| SOME t => SOME (HOLogic.mk_number \<^typ>\<open>Int.int\<close> (fst (read_int (raw_explode t)))))*)
      | SOME t => SOME ((HOLogic.mk_term_of \<^typ>\<open>32 word\<close> (HOLogic.mk_string t))))
  | bv_term_parser (SMTLIB.BV (int,base), []) =    
    let
        val ty = Word_Lib.mk_wordT base
      in
        SOME (HOLogic.mk_number ty int)
      end
  | bv_term_parser (SMTLIB.Sym "_", [int, base]) =
      let
        val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
        val num = snd (HOLogic.dest_number int)
      in
        SOME (HOLogic.mk_number ty num)
      end
  | bv_term_parser (SMTLIB.Sym "bvult", [t1, t2]) = 
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvule", [t1, t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvneg", [t]) =
      SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | bv_term_parser (SMTLIB.Sym "bvadd", t) =
      let val (xs, a) = split_last t
      in
        SOME (fold (curry (HOLogic.mk_binop \<^const_name>\<open>Groups.plus\<close>)) xs a)
      end
  | bv_term_parser (SMTLIB.Sym "bvsub", t) =
      let val (xs, a) = split_last t
      in
        SOME (fold (curry (HOLogic.mk_binop \<^const_name>\<open>Groups.minus\<close>)) xs a)
      end
  | bv_term_parser (SMTLIB.Sym "bvmul", (t::ts)) =
      let
        val T = fastype_of t
      in 
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>Groups.times\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end
  | bv_term_parser (SMTLIB.Sym "bvand", (t::ts)) =
      let
        val T = fastype_of t
      in 
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>semiring_bit_operations_class.and\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end
  | bv_term_parser (SMTLIB.Sym "bvor", (t::ts)) =
      let
        val T = fastype_of t
      in 
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>semiring_bit_operations_class.or\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end
  | bv_term_parser (SMTLIB.Sym "bvxor", (t::ts)) =
      let
        val T = fastype_of t
      in 
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>semiring_bit_operations_class.xor\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end
  | bv_term_parser (SMTLIB.Sym "bvxnor", [t1, t2]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> (HOLogic.mk_binop \<^const_name>\<open>semiring_bit_operations_class.xor\<close> (t1, t2)))
  | bv_term_parser (SMTLIB.Sym "bvnot", [t1]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> t1)
  | bv_term_parser (SMTLIB.Sym "xor", [t1, t2]) =
 (*TODO Hanna: Move somewhere else to general parsing of proof? Nothing bv specific, although
  only present in bv proofs.*)
      SOME (Const ("Word.xor", \<^typ>\<open>HOL.bool\<close> --> \<^typ>\<open>HOL.bool\<close> --> \<^typ>\<open>HOL.bool\<close> ) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "concat", [t1, t2]) =
      SOME (mk_concat (t1, t2))
  | bv_term_parser (SMTLIB.Sym "concat", t::ts) = 
      SOME (mk_lassoc (curry mk_test) t ts)
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "bitOf", SMTLIB.Num i], [t]) =
      SOME (Const (\<^const_name>\<open>semiring_bits_class.bit\<close>, (fastype_of t) --> HOLogic.natT --> \<^typ>\<open>HOL.bool\<close>)
      $ t $ (HOLogic.mk_nat i))
  | bv_term_parser (SMTLIB.Sym "bbT", xs) =
        SOME ((Const ("Reversed_Bit_Lists.of_bl", \<^typ>\<open>HOL.bool list\<close> --> mk_wordT(length xs))) 
        $ ((Const (\<^const_name>\<open>List.rev\<close>, \<^typ>\<open>HOL.bool list\<close> -->  \<^typ>\<open>HOL.bool list\<close>)) $ (HOLogic.mk_list \<^typ>\<open>bool\<close> xs)))
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "extract", SMTLIB.Num i, SMTLIB.Num j], [t]) =
      SOME (mk_extract i j t)
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "zero_extend", SMTLIB.Num i], [t]) =
      SOME (mk_zero_extend i t)
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "sign_extend", SMTLIB.Num i], [t]) =
      SOME (mk_scast i t)
  | bv_term_parser (SMTLIB.Sym "bv2nat", [t1]) =
      SOME (Const (\<^const_name>\<open>unsigned\<close>, (fastype_of t1) --> \<^typ>\<open>int\<close>) $ t1)
 (*TODO: These are in SMTLIB3 syntax for parametric bitwidths. Put in own parser? 
         Also should variants for concrete bitwidths be added for when smtlib3 terms appear in proofs?*)
  | bv_term_parser (SMTLIB.Sym "extract", [t1,t2,t3]) =
    let 
       val T1 = fastype_of t1
       val T2 = fastype_of t2

       val t1' = if T1 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T1 -->  \<^typ>\<open>Nat.nat\<close>) $ t1 else t1
       val t2' = if T2 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T2 -->  \<^typ>\<open>Nat.nat\<close>) $ t2 else t2
    in SOME (Const (\<^const_name>\<open>SMT.smt_extract\<close>, @{typ nat} --> @{typ nat} --> dummyT --> dummyT) $ t1' $ t2' $ t3)
    end

  | bv_term_parser (SMTLIB.Sym "bvnand", [t1, t2]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> (HOLogic.mk_binop \<^const_name>\<open>semiring_bit_operations_class.and\<close> (t1, t2)))
  | bv_term_parser (SMTLIB.Sym "bvnor", [t1, t2]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> (HOLogic.mk_binop \<^const_name>\<open>semiring_bit_operations_class.or\<close> (t1, t2)))
  | bv_term_parser (SMTLIB.Sym "int.log2", [t1]) =
    let
         val T1 = fastype_of t1
         val t1' = (Const (\<^const_name>\<open>nat\<close>, T1 --> \<^typ>\<open>Nat.nat\<close>) $ t1)
         val t2' = HOLogic.mk_number \<^typ>\<open>Nat.nat\<close> 2
        
     in
      SOME (Const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Int.int\<close> ) $ (Const (\<^const_name>\<open>Log_Nat.floorlog\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close>)
         $ t1' $ t2'))
     end
  | bv_term_parser (SMTLIB.Sym "int.ispow2", [t1]) =
      SOME (Const (\<^const_name>\<open>SMT.is_pow2\<close>,\<^typ>\<open>Int.int\<close> --> \<^typ>\<open>bool\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "bvugt", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvuge", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvsgt", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sless\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvslt", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sless\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvsge", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sle\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvsle", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sle\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvsmod", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_smod\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvurem", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_urem\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvsrem", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_srem\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvcomp", [t1,t2]) =
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>smt_comp\<close>, T1 --> T1 --> \<^typ>\<open>1 word\<close>) $ t1 $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "bvredor", [t1]) =
      SOME (Const (\<^const_name>\<open>smt_redor\<close>, fastype_of t1 --> \<^typ>\<open>1 word\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "bvredand", [t1]) =
      SOME (Const (\<^const_name>\<open>smt_redand\<close>, fastype_of t1 --> \<^typ>\<open>1 word\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "bvite", [t1,t2,t3]) =
      let
        val T = fastype_of t2
        val c = Const (\<^const_name>\<open>HOL.If\<close>, [\<^typ>\<open>HOL.bool\<close>, T, T] ---> T)
        val t1' = (Const (\<^const_name>\<open>semiring_bits_class.bit\<close>, fastype_of t1 --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>HOL.bool\<close>) $ t1 $ mk_nat 0)
      in SOME (c $ t1' $ t2 $ t3) end
(*TODO: Proofread until here*)
  | bv_term_parser (SMTLIB.Sym "repeat", [t1, t2]) =
    let
      val T2 = fastype_of t2
    in
      SOME (Const (\<^const_name>\<open>SMT.smt_repeat\<close>,\<^typ>\<open>Nat.nat\<close>--> T2 --> dummyT) $ (Const (\<^const_name>\<open>nat\<close>, \<^typ>\<open>Int.int\<close> --> \<^typ>\<open>Nat.nat\<close>) $ t1) $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "rotate_left", [t1, t2]) =
    let
      val T2 = fastype_of t2
    in
      SOME (Const (\<^const_name>\<open>word_rotl\<close>,\<^typ>\<open>Nat.nat\<close>--> T2 --> T2) $ (Const ( \<^const_name>\<open>nat\<close>,\<^typ>\<open>Int.int\<close> -->  \<^typ>\<open>Nat.nat\<close> ) $ t1) $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "rotate_right", [t1,t2]) =
    let
      val T2 = fastype_of t2
      val _ = @{print}("rotate_right t1",t1)
      val _ = @{print}("rotate_right t2",t2)
      val _ = @{print}("rotate_right T2",T2)
(*("rotate_right t1", Free ("amount", "int")) (line 351 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("rotate_right t2", Free ("x", "_ word")) (line 352 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("rotate_right T2", "_ word") (line 353 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bvsize t1", Free ("x", "_ word")) (line 413 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") *)

    in
      SOME (Const (\<^const_name>\<open>word_rotr\<close>,\<^typ>\<open>Nat.nat\<close>--> T2 --> T2) $ (Const ( \<^const_name>\<open>nat\<close>, \<^typ>\<open>Int.int\<close> --> \<^typ>\<open>Nat.nat\<close>) $ t1) $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "zero_extend", [t1, t2]) = (*This should push t1 0's before t2, solution above uses ucast, should I do too?*)
  let
    val T = fastype_of t2
    val TU = dummyT (*TODO: If known add concrete bitwidth*)
  in SOME (Const (\<^const_name>\<open>Word.cast\<close>, T --> TU) $ t2) end
  | bv_term_parser (SMTLIB.Sym "sign_extend", [t1, t2]) =
  let
    val _ = @{print}("sign_extend t1",t1)
    val _ = @{print}("sign_extend t2",t2)
    (*("sign_extend t1", Free ("n", "int")) (line 368 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
    ("sign_extend t2", Free ("x", "_ word"))*)
    (*If type of t2 is known I could calculate type of t1, otherwise I would just ignore t1? Maybe better don't use signed*)
  in
   (*SOME (Const (\<^const_name>\<open>signed_take_bit\<close>,\<^typ>\<open>Nat.nat\<close>--> fastype_of t2 --> dummyT) $ (Const ( \<^const_name>\<open>nat\<close>, \<^typ>\<open>Int.int\<close> --> \<^typ>\<open>Nat.nat\<close>) $ t1) $ t2)*)
    SOME (Const (\<^const_name>\<open>Word.signed_cast\<close>, fastype_of t2 --> dummyT) $ t2)
  end
  | bv_term_parser (SMTLIB.Sym "bvuaddo", [t1, t2]) =
      SOME (Const (\<^const_name>\<open>smt_uaddo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvsaddo", [t1, t2]) =
      SOME (Const (\<^const_name>\<open>smt_saddo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvsdivo", [t1,t2]) = (*TODO*)
      SOME (Const (\<^const_name>\<open>smt_sdivo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvusubo", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>smt_usubo\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvssubo", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>smt_ssubo\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bv", [int,(Const ("Nat.semiring_1_class.of_nat", _) $ (Const ("Nat.size_class.size", _) $
     Free ("x", typ)))]) =
      let
     val _ = @{print}("int",int)
     val _ = @{print}("typ",typ)
        (*This might not be possible since int might not be a int*)
      (*  val num = snd (HOLogic.dest_number int)
      in SOME (HOLogic.mk_number typ num) end*)
      (*Only possibility I see is to add a cast from int to word in these cases*)
      in SOME (Const  (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> typ) $ int) end
  | bv_term_parser (SMTLIB.Sym "bv", [int,base]) = (*TODO: Can get rid of case distinction now*)
     let
     (*There is one special case that is caught here, that is if the base is the size of another bitvector *)
     val _ = @{print}("int",int)
     val _ = @{print}("base",base)

(*("int", Const ("Groups.zero_class.zero", "int")) (line 371 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("base",
 Const ("Nat.semiring_1_class.of_nat", "nat \<Rightarrow> int") $
   (Const ("Word.size_word_inst.size_word", "_ \<Rightarrow> nat") $
     Free ("x", "_ word")))
*)



     (*   val res = case base of
    (Const ("Nat.semiring_1_class.of_nat", _) $ (Const ("Word.size_word_inst.size_word", _) $
     Free ("x", typ))) => let 
                            val num = snd (HOLogic.dest_number int)
                          in (@{print}("typ",typ);HOLogic.mk_number typ num) end |
     _ => let
            val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
            val num = snd (HOLogic.dest_number int)
          in  HOLogic.mk_number ty num end*)

      in
         SOME (Const  (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> dummyT) $ int) (*TODO: Use ty*)
      end

(*(Sym "bv",
  [Const ("Groups.one_class.one", "int"),
   Const ("Word.size_word_inst.size_word", "_ \<Rightarrow> _") $
     Free ("x",
           "_")]*)
  | bv_term_parser (SMTLIB.Sym "bvsize", [t1]) =
let
     val _ = @{print}("bvsize t1",t1)
     val T = fastype_of t1
     val _ = @{print}("T",T)

     val _ = @{print}("bvsize t1",(Const ( \<^const_name>\<open>of_nat\<close>,  \<^typ>\<open>Nat.nat\<close> -->  \<^typ>\<open>Int.int\<close>) $
Const ( \<^const_name>\<open>size\<close>, dummyT -->  \<^typ>\<open>Nat.nat\<close>) $ t1))
in
      SOME (Const ( \<^const_name>\<open>of_nat\<close>,  \<^typ>\<open>Nat.nat\<close> -->  \<^typ>\<open>Int.int\<close>) $
(Const ( \<^const_name>\<open>size\<close>, dummyT -->  \<^typ>\<open>Nat.nat\<close>) $ t1))
(*SOME (Const ( \<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>))*)

end
  | bv_term_parser (SMTLIB.Sym "bvsdiv", [t1,t2]) = (*TODO*)
      SOME (HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close> (t1, t2))
 | bv_term_parser (SMTLIB.Sym "bvudiv", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close> (t1, t2)) (*TODO: What about the case whre t2 is 0? SMTLIB semantics says it should be mask *)
  | bv_term_parser (SMTLIB.Sym "bvshl", [t1, t2]) = 
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.push_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1) $ (Const ( \<^const_name>\<open>unsigned\<close>, T1 --> \<^typ>\<open>Nat.nat\<close> ) $ t1) $ t2)
   end
  | bv_term_parser (SMTLIB.Sym "bvlshr", [t1, t2]) = 
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1) $ (Const ( \<^const_name>\<open>unsigned\<close>, T1 --> \<^typ>\<open>Nat.nat\<close> ) $ t1) $ t2)
   end
  | bv_term_parser (SMTLIB.Sym "bvashr", [t1, t2]) = 
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>signed_drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1) $ (Const ( \<^const_name>\<open>unsigned\<close>, T1 --> \<^typ>\<open>Nat.nat\<close> ) $ t1) $ t2)
   end
  | bv_term_parser xs = ((*@{print}("IN BV_TERM PARSER",xs);*)NONE)

val dummyLenWord =  \<^typ>\<open>'a::len word\<close>
val dummyLenWord2 = Type(\<^type_name>\<open>word\<close>,[TFree(\<^type_name>\<open>dummy\<close>,@{sort "len"})])
val temp = (Type (\<^type_name>\<open>word\<close>, [dummyT]))

fun bv_type_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "BitVec", SMTLIB.Num x], []) =
    SOME (Word_Lib.mk_wordT x)
  | bv_type_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "BitVec", SMTLIB.Sym x], []) =
    SOME (Word_Lib.mk_wordT 8) (*TODO: Delete*)
  | bv_type_parser (SMTLIB.Sym "?BitVec", []) = SOME temp (*TODO: Here it should be a 'a::len word not a word *)
  | bv_type_parser (SMTLIB.S [SMTLIB.Sym "?BitVec"], []) = SOME temp (*TODO*)
  | bv_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT])) (*TODO *)
  (*| bv_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [ \<^typ>\<open>'a\<close>])) (*TODO*)*)
  | bv_type_parser xs = ((*@{print} ("bv_type_parser", xs);*)NONE)
(*("bv_type_parser",
 (Sym "?BitVec",
  [])*)
end


(* setup *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (20, smtlib_logic) #>
  setup_builtins))


val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser bv_term_parser))


val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser bv_type_parser))

end;
