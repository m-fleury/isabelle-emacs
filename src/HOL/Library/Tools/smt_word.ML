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
fun smtlib_logic "z3" ts _ =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts
    then SOME (SMT_Translate.NO_LOGIC)
    else NONE
  | smtlib_logic "verit" _ _ = NONE
  | smtlib_logic _ ts _ =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts
    then SOME (SMT_Translate.SL ({fixedSizeBitVectors=true,real=true,set=false}:SMT_Translate.smtlib_theories))
    else NONE


(* SMT-LIB builtins *)

local
  val smtlibC = SMTLIB_Interface.bvsmtlibC
     val _ = @{print}("in bv builtin")

  val wordT = \<^typ>\<open>'a::len word\<close>
  val wordT_concrete = \<^typ>\<open>num \<Rightarrow> 'a::len word\<close>

  fun index1 s i = "(_ " ^ s ^ " " ^ string_of_int i ^ ")"
  fun index2 s i j = "(_ " ^ s ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^ ")"

  fun word_typ (Type (\<^type_name>\<open>word\<close>, [T]))
    = Option.map (rpair [] o index1 "BitVec") (try dest_binT T) |
  word_typ (Type (_, [T])) = Option.map (rpair [] o index1 "BitVec") (try dest_binT T) |
  word_typ T = NONE

  fun remove_cast (Const ("Int.nat", _) $ x) = x |
      remove_cast x = x

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
        val _ = @{print}("m",m)
        val _ = @{print}("n",n)

    in
      if pred (U, Us) then SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T))) else NONE
    end

  fun if_fixed_all m = if_fixed (forall (can dest_wordT) o (op ::)) m
  fun if_fixed_args m = if_fixed (forall (can dest_wordT) o snd) m

  fun add_word_fun f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end


  val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>

  fun mk_shift c [t,u] =
(case try HOLogic.dest_number u of
NONE => (@{print}("u",u);Const c $ mk_nat ( (HOLogic.dest_numeral u)) $ t) |
SOME _ =>  (@{print}("u",u);Const c $ mk_nat (snd (HOLogic.dest_number u)) $ t))
    | mk_shift c ts = raise TERM ("bad arguments", Const c :: ts)
  fun mk_shift_numeral c [u, t] = (@{print}("u",u);@{print}("t",t);Const c $ mk_nat (HOLogic.dest_numeral u) $ t)
    | mk_shift_numeral c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift m n T ts =
    let
      val _ = @{print}("------------------------")

      val _ = @{print}("m",m)
      val _ = @{print}("n",n)
      val _ = @{print}("T",T)
      val _ = @{print}("ts",ts)
      val ts = ts |> map (fn (Const ("Int.nat", _) $ x) => x | x => x) 

      val U = Term.domain_type (Term.range_type T)
      val _ = @{print}("U",U)

    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) =>
          let 
            val _ = @{print}("i",i)
            val _ = @{print}("[hd (tl ts), HOLogic.mk_number U i]",[hd (tl ts), HOLogic.mk_number U i])

          in
          SOME (n, 2, [hd (tl ts), HOLogic.mk_number U i], mk_shift (m, T)) end
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

  fun slice m n (T as (Type(_,[_,Type(_,[Tx,U])]))) ts =
   (case (try (snd o HOLogic.dest_number o remove_cast o hd) ts,
          try dest_wordT U,
          try dest_wordT Tx) of
    (SOME j, SOME k, SOME i') => 
     let
     val _ = @{print}("In slice9",(j,k,i'))
      val i = i' - 1
     in
      if i >= j andalso k = i' - j (*i > k is implicit*)
      then ( @{print}("In slice9");SOME (index2 n i j, 1, tl ts, mk_extract (m, T) j))
      else NONE
     end
    | _ => NONE) |
  slice _ _ _ _ = (@{print}("In slice1");NONE)



(* (bit n w) should be translated to (= (extract n n w) #b1) *)
(*

SOME (_, 2, [n,w], (fn [n',w'] \<Rightarrow> Const ("=") $ (Const ("extract") $ n' n' w') (Word 1))

Erstes Argument egal
Zweites: zwei, weil 2 arguments



*)
fun take_bit m n T ts =
    let
     
      val ts = ts |> map (fn (Const ("Int.nat", _) $ x) => x | x => x) 
      val offset = hd ts
      val word= hd (tl ts)
      val U = Term.domain_type (Term.range_type T)

    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) =>
          let 
            val str=""
            val offset' = HOLogic.mk_number @{typ "nat"} i
            val minus=  Const(\<^const_name>\<open>minus\<close>, U --> U --> U)

            val drop=  Const(\<^const_name>\<open>drop_bit\<close>, @{typ "nat"} --> U --> U)
            val push=  Const(\<^const_name>\<open>push_bit\<close>, @{typ "nat"} --> U --> U)
            fun mk_take_bit c ts = hd ts

            val new_term = minus $ word $
 (push $ offset' $ (drop $ offset' $ word))
            val _ = @{print}("new args",new_term)
          in
          SOME (str, 1, [new_term], mk_take_bit (m, T)) end
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end




fun bit m n T ts =
    let
      val _ = @{print}("m",m)
      val _ = @{print}("n",n)
      val _ = @{print}("T",T)
      val _ = @{print}("ts",ts)


      val word = hd ts
      val pos = hd (tl ts) (* |> (fn (Const ("Int.nat", _) $ x) => x | x => x) *)
      val _ = @{print}("word",word)
      val _ = @{print}("pos",pos)

      val suc_simplified =  
      (case (try (snd o HOLogic.dest_number o remove_cast) pos) of
        (SOME i') => (HOLogic.mk_number @{typ "int"} (i'+1))|
        NONE => (Const(\<^const_name>\<open>Nat.Suc\<close>,@{typ "nat"} --> @{typ "nat"}) $ pos))


      fun cond i =
      Const(\<^const_name>\<open>slice\<close>, @{typ "nat"} --> fastype_of (word) --> @{typ "1 word"})
        $ i
        $ (Const (\<^const_name>\<open>take_bit\<close>,@{typ "nat"} --> fastype_of word --> fastype_of word)
          $ i
          $ word)

      
      fun new_ts i =
          Const(\<^const_name>\<open>HOL.eq\<close>, @{typ "1 word"} -->  @{typ "1 word"} --> @{typ "bool"}) $
          cond i $
          @{term "1::1 word"}
    

      val _ = @{print}("new_ts pos",new_ts suc_simplified)

      fun mk_bit ts = (@{print}("mk_bit ts",ts);hd ts)


    in  SOME ("", 1, [new_ts suc_simplified], mk_bit) end

(*
      val U = Term.domain_type (Term.range_type T)
      fun mk_bit [w',n'] = Const ("HOL.eq", @{typ "1 word \<Rightarrow> 1 word \<Rightarrow> bool"})
      $ (Const ("smt_extract", @{typ "nat"} -->  @{typ "nat"} --> fastype_of w' --> @{typ "1 word"}  ) $ n' $ n' $ w') $
     Const ("Groups.one_class.one", @{typ "1 word"})
in SOME (n, 2, [nth ts 0, nth ts 1], mk_bit) end
*)





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

Wir bauen den neuen Term auf, vielleicht wollen wir die 
*)

fun mk_bit c n ts = Const c $ hd ts $ mk_nat n

(*fun K x = fn _ => x;*)
  fun add_word_fun' f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun' smtlibC (t, (f m n)) end

(* (\<^Const>\<open>True\<close>, "true")*)

  fun bit2 m n T [w,i:term] =
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
            val res_str = ""
            val _ = @{print}("res",res_str)
            val bit_word = Const("Word.smt_bit_word",T') $ w $ i
            val _ = @{print}("bit_word",bit_word)
          in
          SOME (res_str, 2, [\<^term>\<open>(1::1 word) = Word.smt_bit_word w i\<close>], mk_bit (m, T) lb)
          end
      | _ => NONE)
    end

 fun mk_extract2 c i j ts = Term.list_comb (Const c, mk_nat i :: mk_nat j :: ts)

(*

  fun add_word_fun f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end

t den wir uebersetzen aus dem Problem. bit bekommt gar nicht den Term nur Name (m), Typ des Terms(T)
und argumente

 K (f m n): Wenn f als funktion in die Tabelle hinzufuegt wird kommt nach n ein anderes 
Argument, dass unsere bit funktion nicht haben soll weil es whrs nichts bringt. Deshalb kommt
bei bit nach m n direkt T.

n has no use here, is useful if we have the same function (e.g. shift) for several bit-vector 
translations 

In der Tablle steht dann

("Bit_Operations.semiring_bits_class.bit","6 word \<Rightarrow> nat \<Rightarrow> bool") und eine Funktion die bei 
eingabe von Argumenten einen neuen Term ausgibt

Term T ist ein argument weil der erste Eintrag in der Tabelle genereller sein koennte als der 
konkrete Term. Zum Beispiel Tabelle hat Eintrag fuer = 'a \<Rightarrow> 'a \<Rightarrow> Bool aber konkreter Term 
arbeitet auf ints.


Funktion f gibt
 (string * int * term list * (term list -> term)) option
wenn Uebersetzung nicht funktionert gibt sie NONE sonst SOME

Das erste und zweite Returnvalue scheint nicht zu zaehlen und es ist egal was man reinmacht. 

          SOME (n, 2, [hd (tl ts), HOLogic.mk_number U i], mk_shift (m, T))

Der dritte ist whrs die Terme die rekursive in strings uebersetzt werden sollen
Das vierte ist ein Term
*)
(*
  fun bit m n T [w,i:term] =
    let
      val _ = @{print}("bit m",m)
      val _ = @{print}("bit n",n)
      val _ = @{print}("bit T",T)
      val _ = @{print}("bit w",w)
      val _ = @{print}("bit i",i)

      (*Build up right T for mk_extract*)
      val (wT, _) = Term.dest_funT T
      val _ = @{print}("bit wT",wT)

      val T' = wT --> \<^typ>\<open>nat\<close> -->  \<^typ>\<open>1 word\<close>
      val _ = @{print}("T'",T')
      val T'' = \<^typ>\<open>1 word\<close> --> \<^typ>\<open>1 word\<close> --> \<^typ>\<open>HOL.bool\<close> 


      val bit_word = Const("Word.smt_bit_word",T') $ w $ i


(*("bit m", "Bit_Operations.semiring_bits_class.bit") (line 203 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bit n", "=") (line 204 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bit T", "6 word \<Rightarrow> nat \<Rightarrow> bool") (line 205 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bit w",
 Const ("Num.numeral_class.numeral", "num \<Rightarrow> 6 word") $
   (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
     (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
       Const ("Num.num.One", "num")))) (line 206 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bit i",
 Const ("Int.nat", "int \<Rightarrow> nat") $
   (Const ("Num.numeral_class.numeral", "num \<Rightarrow> int") $
     (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
       Const ("Num.num.One", "num")))) (line 207 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bit wT", "6 word") (line 211 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("T'", "6 word \<Rightarrow> nat \<Rightarrow> 1 word") (line 214 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bit mk",
 Const ("Bit_Operations.semiring_bits_class.bit", "6 word \<Rightarrow> nat \<Rightarrow> bool") $
   (Const ("Num.numeral_class.numeral", "num \<Rightarrow> 6 word") $
     (Const ("Num.num.Bit0", "num \<Rightarrow> num") $ (Const ("Num.num.Bit0", "num \<Rightarrow> num") $ Const ("Num.num.One", "num")))) $
   (Const ("Num.numeral_class.numeral", "num \<Rightarrow> nat") $
     (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
       (Const ("Num.num.Bit1", "num \<Rightarrow> num") $
         (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
           (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
             (Const ("Num.num.Bit0", "... ... ...") $
               (Const ("Num.num.Bit0", "...") $
                 Const ("...", ...))))))))) *)
(*("ts!!!!",
 [Const ("HOL.eq", "1 word \<Rightarrow> 1 word \<Rightarrow> bool") $ Const ("Groups.one_class.one", "1 word") $
    (Const ("HOL.If", "bool \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word") $
      (Const ("smt_extract", "nat \<Rightarrow> nat \<Rightarrow> 6 word \<Rightarrow> bool") $
        (Const ("Int.nat", "int \<Rightarrow> nat") $
          (Const ("Num.numeral_class.numeral", "num \<Rightarrow> int") $
            (Const ("Num.num.Bit0", "num \<Rightarrow> num") $ Const ("Num.num.One", "num")))) $
        (Const ("Int.nat", "int \<Rightarrow> nat") $
          (Const ("Num.numeral_class.numeral", "num \<Rightarrow> int") $
            (Const ("Num.num.Bit0", "num ... num") $ Const ("Num.num.One", "num")))) $
        (Const ("Num.numeral_class.numeral", "num \<Rightarrow> 6 word") $
          (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
            (Const ("Num.num.Bit0", "... ... ...") $ Const ("Num.num.One", "..."))))) $
      Const ("Groups.one_class.one", "1 word") $
      Const ("Groups.zero_class.zero",
             "1 word"))])*)

            val test_term = @{term "HOL.eq::1 word => 1 word => bool"}
                          $ @{term "Groups.one_class.one::1 word"}
                          $ (Const("Word.smt_bit_word",  wT --> @{typ "nat"} --> @{typ "1 word"})
                            $ w $ i)
            fun test_f (m, T) ts = (@{print}("ts!!!!", map (Thm.cterm_of @{context}) ts); 
               @{term "HOL.eq::1 word => 1 word => bool"}
                          $ @{term "Groups.one_class.one::1 word"}
                          $ (Const("Word.smt_bit_word",  wT --> @{typ "nat"} --> @{typ "1 word"})
                            $ w $ i))

            val _ = @{print}("test_term",test_term)
(* Const ("HOL.eq", "1 word \<Rightarrow> 1 word \<Rightarrow> bool") $ Const ("Groups.one_class.one", "1 word") $
   (Const ("HOL.If", "bool \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word") $
     (Const ("Bit_Operations.semiring_bits_class.bit", "'a::semiring_bits \<Rightarrow> nat \<Rightarrow> bool") $ Free ("w", "'a::semiring_bits") $ Free ("i", "nat")) $
     Const ("Groups.one_class.one", "1 word") $
     Const ("Groups.zero_class.zero", "1 word")))*)
    in  
   (case (try (snd o HOLogic.dest_number o remove_cast) i) of
   (SOME i') => 
          SOME ("EXTRABIT", 2, [test_term], test_f (m, T))|
       _ => NONE)
    end
  | bit m n T xs = (@{print} (m,n,T,xs); NONE)
*)

 fun bit_word m n T (ts as [w,i:term]) =
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

      val i_as_nat = (HOLogic.dest_number o remove_cast) i |> snd |> HOLogic.mk_number @{typ nat}
      val _ = @{print}("i_as_nat",i_as_nat)

    in  
       (case (try (snd o HOLogic.dest_number o remove_cast) i, try dest_wordT wT) of
        (SOME lb, SOME i') =>
          let
            val res_str = "(_ " ^ n ^ " " ^ Int.toString lb ^ " " ^ Int.toString lb ^ ")"
            val T1 = mk_wordT (i'- lb)
            val _ = @{print}("T1",T1)
          in
          SOME (res_str, 2, [], fn _ => (Const (\<^const_name>\<open>slice\<close>, @{typ nat} --> fastype_of w  --> @{typ "1 word"}) $ i $ (Const (\<^const_name>\<open>take_bit\<close>,  @{typ nat} --> fastype_of w --> fastype_of w ) $ i $ w)) )
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
      fun mk_num T x = 
        let
          val _ = HOLogic.mk_number HOLogic.intT (dest_binT T)
        in Const (\<^const_name>\<open>nat\<close>, @{typ "int => nat"}) $ 
            HOLogic.mk_number HOLogic.intT (dest_binT T) end
    in
     (case head_of (hd ts) of
         Const (_, Type (\<^type_name>\<open>itself\<close>, [T])) =>
           SOME ("len_of" (*fudge*), 0, [], (mk_num T))
       | _ => NONE)
    end
  fun add_len_of (t,n) = 
    let val (m, _) = Term.dest_Const (head_of t)
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t), fn _ => (fn x => fn y =>len_of t m n x y))
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

fun concat op_name smt_name (typ as (Type(_,[T1,Type(_,[T2,T])]))) terms =
 (case (try dest_wordT T1, try dest_wordT T2, try dest_wordT T) of
  (SOME i, SOME j, SOME k) =>
   (if (i + j = k)
    then (if_fixed (forall (can dest_wordT) o (op ::)) op_name smt_name typ terms)
     else NONE) |
  _ => NONE) |
 concat _ _ _ _ = NONE

val setup_builtins =
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmtlibC (wordT, word_typ, word_num) #>
(*Isabelle typ, typ uebersetzung, term uebersetzung*)
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmtlibC
    (\<^typ>\<open>Num.num \<Rightarrow> 'a::len word\<close>, word_typ, word_num) #>
  fold (add_word_fun if_fixed_all) [
    (\<^term>\<open>uminus :: 'a::len word \<Rightarrow> _\<close>, "bvneg"),
    (\<^term>\<open>plus :: 'a::len word \<Rightarrow> _\<close>, "bvadd"),
    (\<^term>\<open>minus :: 'a::len word \<Rightarrow> _\<close>, "bvsub"),
    (\<^term>\<open>times :: 'a::len word \<Rightarrow> _\<close>, "bvmul"),
    (\<^term>\<open>not :: 'a::len word \<Rightarrow> _\<close>, "bvnot"),
    (\<^term>\<open>and :: 'a::len word \<Rightarrow> _\<close>, "bvand"),
    (\<^term>\<open>or :: 'a::len word \<Rightarrow> _\<close>, "bvor"),
    (\<^term>\<open>xor :: 'a::len word \<Rightarrow> _\<close>, "bvxor") ] #>
  add_word_fun concat
    (\<^term>\<open>word_cat :: 'a::len word \<Rightarrow> _\<close>, "concat")  #>
  fold (add_word_fun shift) [
    (\<^term>\<open>push_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _ \<close>, "bvshl"),
    (\<^term>\<open>drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>signed_drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvashr") ] #>
  add_word_fun slice
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
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.bvsmtlibC) [
    (\<^term>\<open>unsigned :: 'a::len word \<Rightarrow> Int.int\<close>, "bv2nat"),
    (\<^term>\<open>of_int ::  Int.int => 'a::len word\<close>, "nat2bv")

   ] #>
  fold (add_word_fun take_bit) [
    (\<^term>\<open>take_bit :: _ \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "TODO")
   ] #>
  fold (add_word_fun bit) [
    (\<^term>\<open>bit :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "bit")
   ] (*#>
  fold (add_word_fun bit_word) [
    (\<^term>\<open>smt_bit_word :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "extract")
   ]*)


 #>
  fold (add_word_fun power) [
    (\<^term>\<open>power :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "^")
   ]
(*(bit$ w$ n$)*)


val add_word_shift' = add_word_fun shift'

end


(* Proof Reconstruction *)

open SMT_Parser_Util

val split_last =
  let fun split_last [a] = ([], a)
       | split_last (x :: xs) = apfst (curry (op ::) x) (split_last xs)
  in apfst List.rev o split_last end

fun mk_concat t1 t2 =
  let
    val T1 = fastype_of t1 
    val T2 = fastype_of t2
  in
   case (try dest_wordT T1, try dest_wordT T2) of
    (SOME i, SOME j)
       => SOME (Const (\<^const_name>\<open>Word.word_cat\<close>, T1 --> T2 --> mk_wordT (i + j)) $ t1 $ t2) |
     _
       => NONE
  end

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

fun
  (*From the FixedSizeBitVectors theory*)
  bv_term_parser (SMTLIB.BVNum (i, base), []) = SOME (HOLogic.mk_number (mk_wordT(base)) i)
  | bv_term_parser (SMTLIB.Sym "bvnot", [t1]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> t1)
  | bv_term_parser (SMTLIB.Sym "bvneg", [t]) =
      SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | bv_term_parser (SMTLIB.Sym "bvand", (t::ts)) =
      SOME (mk_lassoc' \<^const_name>\<open>semiring_bit_operations_class.and\<close> t ts)
 (*| bv_term_parser (SMTLIB.Sym bv, []) =
      (case try (unprefix "bv") bv of
        NONE => NONE
      | SOME t => (@{print}("TODO: when this happens in bv_term_parser investigate: ",bv);
        SOME ((HOLogic.mk_term_of \<^typ>\<open>32 word\<close> (HOLogic.mk_string t)))))
*)
  (*| bv_term_parser (SMTLIB.Sym "bv", [int,(Const ("Nat.semiring_1_class.of_nat", _) $ (Const ("Nat.size_class.size", _) $
     Free ("x", typ)))]) = SOME (Const (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> typ) $ int)*)
  | bv_term_parser (SMTLIB.Sym "bv", [int, base]) =
     let
        val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
        val num = snd (HOLogic.dest_number int)
      in
        SOME (HOLogic.mk_number ty num)
      end
 (* | bv_term_parser (SMTLIB.Sym "@bv", [int, base]) =
     let
        val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
        val num = snd (HOLogic.dest_number int)
      in
        SOME (HOLogic.mk_number ty num)
      end*)
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
  | bv_term_parser (SMTLIB.Sym "bvshl", [t1, t2]) = 
    let
      val T1 = fastype_of t1
      val (_,t2') = HOLogic.dest_number t2
      val t2'' =  HOLogic.mk_number @{typ "int"} t2'
      val _ = @{print}("bvshl",t2'')
    in
      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.push_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1)
        $ (Const ( \<^const_name>\<open>nat\<close>,  \<^typ>\<open>int\<close>  --> \<^typ>\<open>Nat.nat\<close> ) $ t2'') $ t1)
   end
  | bv_term_parser (SMTLIB.Sym "bvlshr", [t1, t2]) = 
    let
      val T1 = fastype_of t1
      val (_,t2') = HOLogic.dest_number t2
      val t2'' =  HOLogic.mk_number @{typ "int"} t2'
      val _ = @{print}("bvlshr",t2'')
    in
      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1)
        $ (Const ( \<^const_name>\<open>nat\<close>,  \<^typ>\<open>int\<close>  --> \<^typ>\<open>Nat.nat\<close> ) $ t2'') $ t1)
   end
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
  SMTLIB_Interface.add_logic (30, smtlib_logic) #>
  setup_builtins))

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser bv_type_parser #>
  SMTLIB_Proof.add_term_parser bv_term_parser))

end