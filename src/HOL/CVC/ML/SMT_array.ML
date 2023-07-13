(*  Title:      HOL/Tools/SMT/SMT_array.ML
    Author:     Hanna Lachnitt, Stanford

SMT setup for arrays.
*)

signature SMT_Array = 
sig 
   val array_type_parser : SMTLIB.tree * typ list -> typ option
   val array_term_parser :  SMTLIB.tree * term list -> term option
end

(*TODO: We want to use Array.thy longterm but can't currently. Therefore we use maps for now which
don't restrict bounds. We could add these in additional assumptions easily but don't want to
*)
structure SMT_Array: SMT_Array =
struct

fun mk_binary n U t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
  in Const (n, [T1, T2] ---> U) $ t1 $ t2 end

fun mk_ternary n U t1 t2 t3 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T3 = fastype_of t3
  in Const (n, [T1, T2, T3] ---> U) $ t1 $ t2 $ t3 end

fun array_type_parser (SMTLIB.Sym "?Array", [])
    = SOME (Type(\<^type_name>\<open>fun\<close>,[dummyT,Type(\<^type_name>\<open>option\<close>,[dummyT])]))
    (* = SOME (Type(\<^type_name>\<open>List.list\<close>,[dummyT]))*)
    (* = SOME (Type(\<^type_name>\<open>Heap.array\<close>,[dummyT]))*)
  | array_type_parser _ = NONE

fun array_term_parser (SMTLIB.Sym "select", [t1,t2]) =
   let
    (*val U = fastype_of t1 |> dest_Type |> snd |> hd*)
   in
    SOME (t1 $ t2)
    (*SOME (mk_binary \<^const_name>\<open>List.nth\<close> U t1 t2)*)
    (*SOME (mk_binary \<^const_name>\<open>Array.get\<close> U t1 t2)*)
   end
  | array_term_parser (SMTLIB.Sym "store", [t1,t2,t3]) =
    let
      val _ = @{print}("store t1",t1)
      val _ = @{print}("store t2",t2)
      val _ = @{print}("store t3",t3)
      val T1 = fastype_of t1
      val T2 = fastype_of t2
      val T3 = fastype_of t3
      val _ = @{print}("store T1",T1)
      val _ = @{print}("store T2",T3)
      val _ = @{print}("store T2",T3)

      val temp = Type(\<^type_name>\<open>fun\<close>,[Type(\<^type_name>\<open>fun\<close>,[dummyT,dummyT]),
          Type(\<^type_name>\<open>fun\<close>,[dummyT,Type(\<^type_name>\<open>fun\<close>,[dummyT,Type(\<^type_name>\<open>fun\<close>,[dummyT,dummyT])])])])
    in 
     SOME ((Const (\<^const_name>\<open>Fun.fun_upd\<close>,temp) $ t1 $ t2 $ t3)) (*TODO: Replace dummyT*)
    end
(*
 "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)"
Const ("Fun.fun_upd", "('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b option \<Rightarrow> 'a \<Rightarrow> 'b option") $ Free ("m", "'a \<Rightarrow> 'b option") $ Free ("a", "'a") $
     (Const ("Option.option.Some", "'b \<Rightarrow> 'b option") $ Free ("x", "'b")):*)
   (*  SOME (mk_ternary \<^const_name>\<open>list_update\<close> (fastype_of t1) t1 t2 t3)end*)
   (*SOME (mk_ternary \<^const_name>\<open>Array.update\<close> (fastype_of t1) t1 t2 t3)*)
  | array_term_parser _ = NONE

(*val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser array_type_parser #>
  SMTLIB_Proof.add_term_parser array_term_parser))*)

end;