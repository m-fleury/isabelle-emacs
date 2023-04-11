signature SMTLIB_IMPL_ASSUMPTIONS =
sig
  val get_implicit_assms: term -> term list
  val add_implicit_assms: term -> term
end;

open SMTLIB_Proof

structure SMTLIB_Impl_Assumptions: SMTLIB_IMPL_ASSUMPTIONS =
struct

 fun mk_rassoc f t ts =
  let val us = rev (t :: ts)
  in fold f (tl us) (hd us) end

(*Might not need this because everything is already bound*)
 fun mk_bound (Free (var,typ)) bounds =
  let
   val bound = List.find (fn (b,Free (var1,typ1)) => var = var1) bounds
  in              
   if bound = NONE then (Free (var,typ)) else 
   (let val SOME (BOUND,b) = bound in BOUND end)
 end |
 mk_bound (l1 $ l2) bounds = mk_bound l1 bounds $ mk_bound l2 bounds |
 mk_bound (Abs (str,typ,l1)) bounds = (Abs (str,typ,mk_bound l1 bounds)) |
 mk_bound x _ = x

 fun add_assms ts [] bounds = (ts,bounds) |
 add_assms (Const ("HOL.All", all) $ (Abs (name, typ,l2))) ass bounds =
  let
    val bounds2 = (Bound (length bounds), Free (name,typ))::bounds
  in
   ((Const ("HOL.All", all) $ (Abs (name, typ,fst (add_assms l2 ass bounds2)))), bounds2)
  end |
 add_assms ts (a::ass) bounds =
  let
    val bounds2 = map (fn (x,y) => (let val (Bound k) = x in (Bound (length bounds - k - 1),y) end)) bounds
  in 
    ((Const ("HOL.implies", \<^typ>\<open>HOL.bool\<close> -->  \<^typ>\<open>HOL.bool\<close> --> \<^typ>\<open>HOL.bool\<close>)
  (* $ (mk_bound (mk_rassoc (curry HOLogic.mk_conj) a ass) bounds2) $ ts), bounds2)*)
   $ ( (mk_rassoc (curry HOLogic.mk_conj) a ass) ) $ ts), bounds2)

  end

 fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2
 fun mk_binary_pred n S t1 t2 =
   let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T =
      if T1 <> Term.dummyT then T1
      else if T2 <> Term.dummyT then T2
      else TVar (("?a", serial ()), S)
  in mk_binary' n T \<^typ>\<open>HOL.bool\<close> t1 t2 end

fun mk_less t1 t2 = mk_binary_pred \<^const_name>\<open>ord_class.less\<close> \<^sort>\<open>linorder\<close> t1 t2
fun mk_less_eq t1 t2 = mk_binary_pred \<^const_name>\<open>ord_class.less_eq\<close> \<^sort>\<open>linorder\<close> t1 t2

val eq = (fn (a,b) => (a = b))
val merge_sets = Library.union eq
fun merge_and_add t1 t2 assump = merge_sets t1 t2 |> Library.union eq (Library.distinct eq assump)

fun get_implicit_assms (Const _ $ (Abs (_,_,l1))) = get_implicit_assms l1 |
    get_implicit_assms (Const ("SMT.smt_extract", typ) $ t1 $ t2) = 
     let
       val assump = (mk_less_eq (HOLogic.mk_number \<^typ>\<open>Nat.nat\<close> 0) t1)
       (*val _ = @{print}("added assump here",assump)
       val _ = @{print}("(get_implicit_assms t1)",(get_implicit_assms t1))
       val _ = @{print}("(get_implicit_assms t2)",(get_implicit_assms t2))
       val _ = @{print}("test",merge_and_add [] [] [assump])*)
     in 
       merge_and_add (get_implicit_assms t1) (get_implicit_assms t2) [assump] end |
    get_implicit_assms (l1 $ l2) = merge_sets (get_implicit_assms l1) (get_implicit_assms l2) |
    get_implicit_assms _ = []

fun add_implicit_assms t = (@{print}("(get_implicit_assms t)",(get_implicit_assms t));add_assms t (get_implicit_assms t) [] |> fst)



end