(*  Title:      HOL/Tools/SMT/SMT_string.ML
    Author:     Hanna Lachnitt, Stanford

SMT setup for sets. Note: There is no SMTLIB Set theory.
*)

signature SMT_Set = 
sig 
   val set_type_parser : SMTLIB.tree * typ list -> typ option
   val set_term_parser :  SMTLIB.tree * term list -> term option
end


structure SMT_Set: SMT_Set =
struct

fun mk_unary n U t =
  let val T = fastype_of t
  in Const (n, T --> U) $ t end

fun mk_binary n U t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
  in Const (n, [T1, T2] ---> U) $ t1 $ t2 end

fun set_type_parser (SMTLIB.Sym "?Set", []) = SOME (Type(\<^type_name>\<open>Set.set\<close>,[dummyT]))
  | set_type_parser _ = NONE

fun set_term_parser (SMTLIB.Sym "set.card", [t1]) =
   SOME (mk_unary \<^const_name>\<open>card\<close> \<^typ>\<open>nat\<close> t1)
  | set_term_parser (SMTLIB.Sym "set.member", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>Set.member\<close> \<^typ>\<open>bool\<close> t1 t2)

 |set_term_parser (SMTLIB.Sym "set.empty", []) =
   SOME (Const (\<^const_name>\<open>bot\<close>,Type(\<^type_name>\<open>Set.set\<close>,[dummyT])))
  | set_term_parser (SMTLIB.Sym "set.universe", []) =
   SOME (Const (\<^const_name>\<open>top\<close>,Type(\<^type_name>\<open>Set.set\<close>,[dummyT])))
  | set_term_parser (SMTLIB.Sym "set.singleton", [t1]) =
  let
   val T1 = fastype_of t1
   val U = Type(\<^type_name>\<open>Set.set\<close>,[T1])
  in
   SOME (mk_binary \<^const_name>\<open>insert\<close> U t1 (Const (\<^const_name>\<open>bot\<close>,U)))
  end
  | set_term_parser (SMTLIB.Sym "set.insert", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>insert\<close> (fastype_of t2) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.member", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>Set.member\<close> \<^typ>\<open>bool\<close> t1 t2)
  | set_term_parser (SMTLIB.Sym "set.subset", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>less_eq\<close> \<^typ>\<open>bool\<close> t1 t2)
  | set_term_parser (SMTLIB.Sym "set.union", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>sup\<close> (fastype_of t1) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.inter", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>inf\<close> (fastype_of t1) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.minus", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>minus\<close> (fastype_of t1) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.complement", [t1]) =
   SOME (mk_unary \<^const_name>\<open>uminus\<close> (fastype_of t1) t1)
  (*| set_term_parser (SMTLIB.Sym "set.choose", [t1]) = TODO*)
  (*| set_term_parser (SMTLIB.Sym "set.map", [t1]) = TODO*)
  (*| set_term_parser (SMTLIB.Sym "set.filter", [t1]) = TODO*)
  (*| set_term_parser (SMTLIB.Sym "set.fold", [t1]) = TODO*)
  | set_term_parser (SMTLIB.Sym "set.card", [t1]) =
   SOME (mk_unary \<^const_name>\<open>card\<close> \<^typ>\<open>nat\<close> t1)
  | set_term_parser _ = NONE

(*val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser set_type_parser #>
  SMTLIB_Proof.add_term_parser set_term_parser))*)



end;
