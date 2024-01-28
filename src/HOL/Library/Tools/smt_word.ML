(*  Title:      HOL/Library/Tools/smt_word.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

SMT setup for words.
*)

signature SMT_WORD =
sig
  val add_word_shift': term * string -> Context.generic -> Context.generic
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
     val _ = @{print}("in bv builtin")

  val wordT = \<^typ>\<open>'a::len word\<close>
  val wordT_concrete = \<^typ>\<open>num \<Rightarrow> 'a::len word\<close>

  fun index1 s i = "(_ " ^ s ^ " " ^ string_of_int i ^ ")"
  fun index2 s i j = "(_ " ^ s ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^ ")"

  fun word_typ (Type (\<^type_name>\<open>word\<close>, [T])) =
let 
     val temp = Option.map (rpair [] o index1 "BitVec") (try dest_binT T)

in
temp
end |
  word_typ (Type (_, [T])) =
Option.map (rpair [] o index1 "BitVec") (try dest_binT T)
    | word_typ T = NONE

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

  fun add_word_fun f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end
(*  val add_builtin_fun: SMT_Util.class -> (string * typ) * bfunr option bfun -> Context.generic ->
    Context.generic*)

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

  fun remove_cast (Const ("Int.nat", _) $ x) = x |
      remove_cast x = x
(*Third return is what is written in table in the
end and used to find the string. We can not put the
current term in there since it needs to be more general
Think of it as:

f_e = mk_extract (m, T) lb

term       |    string
----------------------
 f_e(x)    |    (extract 4 4)

where x is arbitrary and is actually mapped. We are not
doing the mapping here. We just add a function to the 
table that is used for mapping
*)
  fun extract m n T ts =
    let
      val _ = @{print}("m",m)
      val _ = @{print}("n",n)
      val _ = @{print}("ts",ts)
      val _ = @{print}("T",T)

      val U = Term.range_type (Term.range_type T)
      val _ = @{print}("U",U)

    in
      (case (try (snd o HOLogic.dest_number o remove_cast o hd) ts, try dest_wordT U) of
        (SOME lb, SOME i) => 
          (@{print}("lb",lb);@{print}("lb2",(i + lb - 1));@{print}("i",i);
           @{print}("index2 n (i + lb - 1) lb",index2 n (i + lb - 1) lb);
           @{print}("tl ts",tl ts);@{print}("mk_extract (m, T) lb",mk_extract (m, T) lb);
           @{print}("mk_extract (m, T) lb []",mk_extract (m, T) lb []);

          SOME (index2 n (i + lb - 1) lb, 1, tl ts, mk_extract (m, T) lb))
      | _ => NONE)
    end

  fun mk_bit c n ts = Const c $ hd ts $ mk_nat n


  (* (bit n w) should be translated to (= (extract n n w) #b1) *)
(*
Idee: 
Erst fuege 

(= #b1

hinzu

und mache einen dummy operator bit_word oder so und dann fuege den wieder zur Tabelle hinzu


Gucke = an um zu sehen wie das hinzugefuegt wurde


fun add_builtin_fun' cs (t, n) =
  let
    val c as (m, T) = Term.dest_Const t
    fun app U ts = Term.list_comb (Const (m, U), ts)
    fun bfun _ U ts = SOME (n, length (Term.binder_types T), ts, app U)
  in add_builtin_fun cs (c, bfun) end

 (SMT_Builtin.add_builtin_fun' smtlibC)(\<^Const>\<open>HOL.eq \<^typ>\<open>'a\<close>\<close>, "=")


t = \<^Const>\<open>HOL.eq \<^typ>\<open>'a\<close>\<close>
n = "="

val c as (m, T) = Term.dest_Const \<^Const>\<open>HOL.eq \<^typ>\<open>'a\<close>\<close>
m = HOL.eq
T = \<^typ>\<open>'a\<close>
c = (HOL.eq, \<^typ>\<open>'a\<close>)


Don't hardcode #b1 as string! Make word and then let Isabelle deal with it same way it deals with 
the two ways of equality above

*)

(*fun K x = fn _ => x;*)
  fun add_word_fun' f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun' smtlibC (t, (f m n)) end

(* (\<^Const>\<open>True\<close>, "true")*)

  fun bit m n T [w,i:term] =
    let
      val _ = @{print}("bit m",m)
      val _ = @{print}("bit n",n)
      val _ = @{print}("bit T",T)
      val _ = @{print}("bit w",w)
      val _ = @{print}("bit i",i)

      (*Build up right T for mk_extract*)
      val (wT, _) = Term.dest_funT T
      val T' = wT --> \<^typ>\<open>nat\<close> -->  \<^typ>\<open>1 word\<close>
      val _ = @{print}("bit wT",wT)
      val _ = @{print}("T",T)

      val _ = @{print}("bit mk",mk_bit (m, T) 66 [w])

    in  
       (case (try (snd o HOLogic.dest_number o remove_cast) i, try dest_wordT wT) of
        (SOME lb, SOME i') =>
          let
            (*val res_str = "= #b1 ((_ " ^ n ^ " " ^ Int.toString lb ^ " " ^ Int.toString lb ^ ")"*)
            val res_str = "="
            val _ = @{print}("res",res_str)
            val bit_word = Const("Word.smt_bit_word",T') $ w $ i
            val _ = @{print}("bit_word",bit_word)

          in
          SOME (res_str, 2, [\<^term>\<open>1::1 word\<close>,bit_word], mk_bit (m, T) lb)
          end
      | _ => NONE)
    end



 fun bit_word m n T [w,i:term] =
    let
      val _ = @{print}("bit word m",m)
      val _ = @{print}("bit n",n)
      val _ = @{print}("bit T",T)
      val _ = @{print}("bit w",w)
      val _ = @{print}("bit i",i)

      (*Build up right T for mk_extract*)
      val (wT, _) = Term.dest_funT T
      val T' = \<^typ>\<open>nat\<close> --> wT --> \<^typ>\<open>1 word\<close>
      val _ = @{print}("bit wT",wT)
      val _ = @{print}("T",T)

      val _ = @{print}("bit mk",mk_bit (m, T) 66 [w])

    in  
       (case (try (snd o HOLogic.dest_number o remove_cast) i, try dest_wordT wT) of
        (SOME lb, SOME i') =>
          let
            val res_str = "(" ^ n ^ " " ^ Int.toString lb ^ " " ^ Int.toString lb ^ ")"
          in
          SOME (res_str, 2, [w], mk_extract (m, T) lb)
          end
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
  fun mk_extend c ts = Term.list_comb (Const c, ts)

  fun power m n T ts =
    let
      val _ = @{print}("m",m)
      val _ = @{print}("n",n)
      val _ = @{print}("T",T)
      val _ = @{print}("ts",ts)

      val (U1, U2) = Term.dest_funT T
      val _ = @{print}("U1",U1)
      val _ = @{print}("U2",U2)

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

  fun len_of t m n T ts =
    let 
      val _ = @{print} ts
      fun mk_num T x = 
        let
          val _ = @{print} ("len_of -->", x, t) 
          val _ = HOLogic.mk_number HOLogic.intT (dest_binT T)  |> @{print}  
        in Const (\<^const_name>\<open>nat\<close>, @{typ "int => nat"}) $ 
            HOLogic.mk_number HOLogic.intT (dest_binT T) end
    in
     (case (head_of (hd ts)) |> @{print} of
         Const (_, Type (\<^type_name>\<open>itself\<close>, [T])) =>
           SOME ("LENGTHXXXXX", 0, [], (mk_num T))
       | _ => NONE)
    end
  fun add_len_of (t,n) = 
    let val (m, _) = Term.dest_Const (@{print}(head_of t))
val _ = @{print} ("len_of", t)

    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t), fn x => (@{print} x; 
   fn x => fn y => @{print} (len_of t m n x y))) |>
@{print}
 end

  fun of_nat t m n T ts =
    let 
      val _ = @{print} ts
      fun mk_num T x = 
        let
          val _ = @{print} ("of_nat -->", x, t) 
          val _ = HOLogic.mk_number HOLogic.natT (dest_binT T)  |> @{print}  
        in HOLogic.mk_number HOLogic.natT (dest_binT T) end
    in
     (case (head_of (hd ts)) |> @{print} of
         Const (_, Type (\<^type_name>\<open>itself\<close>, [T])) =>
           SOME ("LENGTHXXXXX", 0, [], (mk_num T))
       | _ => NONE)
    end
  fun add_of_nat (a as t,n) = 
    let val (m, _) = Term.dest_Const (@{print}(t))
      val _ = @{print} ("of_nat ", t)
      val n = HOLogic.dest_number t |> snd |> K true
               handle TERM _ => false

    in 
      if n then SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t), fn x => (@{print} x; 
         fn x => fn y => @{print} (of_nat t m n x y))) |>
        @{print}
       else  SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t),  K (K (K (NONE))))
   end
in

val setup_builtins =
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmlibC (wordT, word_typ, word_num) #>
(*Isabelle typ, typ uebersetzung, term uebersetzung*)
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmlibC
    (\<^typ>\<open>Num.num \<Rightarrow> 'a::len word\<close>, word_typ, word_num) #>
  fold (add_word_fun if_fixed_all) [
    (\<^term>\<open>uminus :: 'a::len word \<Rightarrow> _\<close>, "bvneg"),
    (\<^term>\<open>plus :: 'a::len word \<Rightarrow> _\<close>, "bvadd"),
    (\<^term>\<open>minus :: 'a::len word \<Rightarrow> _\<close>, "bvsub"),
    (\<^term>\<open>times :: 'a::len word \<Rightarrow> _\<close>, "bvmul"),
    (\<^term>\<open>not :: 'a::len word \<Rightarrow> _\<close>, "bvnot"),
    (\<^term>\<open>and :: 'a::len word \<Rightarrow> _\<close>, "bvand"),
    (\<^term>\<open>or :: 'a::len word \<Rightarrow> _\<close>, "bvor"),
    (\<^term>\<open>xor :: 'a::len word \<Rightarrow> _\<close>, "bvxor"),
    (\<^term>\<open>word_cat :: 'a::len word \<Rightarrow> _\<close>, "concat") ] #>
  fold (add_word_fun shift) [
    (\<^term>\<open>push_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _ \<close>, "bvshl"),
    (\<^term>\<open>drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>signed_drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvashr") ] #>
  add_word_fun extract
    (\<^term>\<open>slice :: _ \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "extract") #>
  add_len_of
    (\<^term>\<open>len_of :: 'a :: len0 itself => nat\<close>, "IDDD") #>
  add_of_nat
    (\<^term>\<open>of_nat :: nat \<Rightarrow> int\<close>, "of_nat") #>
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
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.bvsmlibC) [
    (\<^term>\<open>unsigned :: 'a::len word \<Rightarrow> Int.int\<close>, "bv2nat")
   ](* #>
  fold (add_word_fun' bit) [
    (\<^term>\<open>bit :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "=")
   ] #>
  fold (add_word_fun bit_word) [
    (\<^term>\<open>smt_bit_word :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "extract")
   ]*)


 (*#>
  fold (add_word_fun power) [
    (\<^term>\<open>power :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "ppower")
   ]*)
(*(bit$ w$ n$)*)


val add_word_shift' = add_word_fun shift'

end


(* Proof Reconstruction *)

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

(*TODO: Jan 8 hier weitermachen*)
fun bv_term_parser (SMTLIB.Sym bv, []) =
      (case try (unprefix "bv") bv of
        NONE => NONE
      | SOME t => (@{print}("TODO: when this happens in bv_term_parser investigate: ",bv);
        SOME ((HOLogic.mk_term_of \<^typ>\<open>32 word\<close> (HOLogic.mk_string t)))))
  | bv_term_parser (SMTLIB.Sym "bv", [int,(Const ("Nat.semiring_1_class.of_nat", _) $ (Const ("Nat.size_class.size", _) $
     Free ("x", typ)))]) = SOME (Const (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> typ) $ int)
  | bv_term_parser (SMTLIB.Sym "bv", [int, base]) =
     let
        val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
        val num = snd (HOLogic.dest_number int)
      in
        SOME (HOLogic.mk_number ty num)
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
  | bv_term_parser (SMTLIB.Sym "concat", [t1, t2]) =
      SOME (mk_concat (t1, t2))
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "zero_extend", SMTLIB.Num i], [t]) =
      SOME (mk_zero_extend i t)
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "sign_extend", SMTLIB.Num i], [t]) =
      SOME (mk_scast i t)
  | bv_term_parser _ = NONE

fun bv_type_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "BitVec", SMTLIB.Num x], []) =
    SOME (Word_Lib.mk_wordT x)
  | bv_type_parser _ = NONE

(* setup *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (20, smtlib_logic) #>
  setup_builtins))

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser bv_type_parser #>
  SMTLIB_Proof.add_term_parser bv_term_parser))

end