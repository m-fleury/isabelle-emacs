(*  Title:      HOL/Tools/SMT/SMT_real.ML
    Author:     Sascha Boehme, TU Muenchen

SMT setup for reals.
*)
(*TDODO: what about smt_real?*)
structure SMT_Real: sig end =
struct

fun real_type_parser (SMTLIB.Sym "Real", []) = SOME \<^typ>\<open>Real.real\<close>
  | real_type_parser (SMTLIB.Dec (i, 0), _) = SOME \<^typ>\<open>Real.real\<close>
  (*This is not working
  | real_type_parser (SMTLIB.Sym "*", [t1,t2]) =
    if fastype_of t1 = \<^typ>\<open>Real.real\<close> then SOME  \<^typ>\<open>Real.real => Real.real \<Rightarrow> Real.real\<close>
    else (if fastype_of t2 = \<^typ>\<open>Real.real\<close> then SOME  \<^typ>\<open>Real.real => Real.real \<Rightarrow> Real.real\<close>
    else NONE)*)
  | real_type_parser _ = NONE

fun real_term_parser (SMTLIB.Dec (i, 0), []) = SOME (HOLogic.mk_number \<^typ>\<open>Real.real\<close> i)
  | real_term_parser (SMTLIB.Sym "/", [t1, t2]) =
let 
    val T1 = fastype_of t1
    val T2 = fastype_of t2
in 
    if T1 = \<^typ>\<open>Real.real\<close> then SOME (\<^term>\<open>Rings.divide :: real => _\<close> $ t1 $ t2) else
    if T2 = \<^typ>\<open>Real.real\<close> then SOME (\<^term>\<open>Rings.divide :: real => _\<close> $ t1 $ t2) else
     SOME (\<^term>\<open>Rings.divide :: int => _\<close> $ t1 $ t2) (*TODO: Should be NONE and then parsed in core parser*)
end



  | real_term_parser (SMTLIB.Sym "to_real", [t]) = SOME (\<^term>\<open>Int.of_int :: int => Real.real\<close> $ t)
(*TODO: Delete is not called*)
  | real_term_parser (SMTLIB.Num i, []) = SOME (\<^term>\<open>Int.of_int :: int => Real.real\<close> $ (HOLogic.mk_number \<^typ>\<open>int\<close> i))
  | real_term_parser (SMTLIB.Sym "*", [t1,t2]) =
  let 
    val T1 = fastype_of t1
    val T2 = fastype_of t2

(* This is never 
        val _ = @{print} ("t1", t1)
        val _ = @{print} ("Type of t1", T1)
        val _ = @{print} ("t2", t2)
        val _ = @{print} ("Type of t2", T2)
    val (t1',t2',T3) = if T1 = \<^typ>\<open>Int.int\<close> andalso T2 = \<^typ>\<open>Real.real\<close>
                       then (Const ( \<^const_name>\<open>of_int\<close>, T1 --> T2)  $ t1,t2, T2)
                       else (if T1 = \<^typ>\<open>Real.real\<close> andalso T2 = \<^typ>\<open>Int.int\<close>
                       then (t1, Const ( \<^const_name>\<open>of_int\<close>, T2 --> T1)  $ t2,T1)
                       else (t1,t2,T1))
*)
  in
    (*SOME ( Const (\<^const_name>\<open>Groups.times\<close>, [T3, T3] ---> T3) $ t1' $ t2')*)

    SOME ( Const (\<^const_name>\<open>Groups.times\<close>, [\<^typ>\<open>Real.real\<close>, \<^typ>\<open>Real.real\<close>] ---> \<^typ>\<open>Real.real\<close>) $ t1 $ t2)
  end
  | real_term_parser _ = ((*@{print} "smt_real";*)NONE)

fun abstract abs t =
  (case t of
    (c as \<^term>\<open>Rings.divide :: real => _\<close>) $ t1 $ t2 =>
      abs t1 ##>> abs t2 #>> (fn (u1, u2) => SOME (c $ u1 $ u2))
  | (c as \<^term>\<open>Int.of_int :: int => Real.real\<close>) $ t =>
      abs t #>> (fn u => SOME (c $ u))
  | _ => pair NONE)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser real_type_parser #>
  SMTLIB_Proof.add_term_parser real_term_parser #>
  SMT_Replay_Methods.add_arith_abstracter abstract))


end;
