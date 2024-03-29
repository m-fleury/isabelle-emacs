(*  Title:      HOL/MicroJava/Comp/AuxLemmas.thy
    Author:     Martin Strecker
*)


(* Auxiliary Lemmas *)

theory AuxLemmas
imports "../J/JBasis"
begin

(**********************************************************************)
(* List.thy *)
(**********************************************************************)



lemma app_nth_greater_len [simp]:
  "length pre \<le> ind \<Longrightarrow> (pre @ a # post) ! (Suc ind) = (pre @ post) ! ind"
  apply (induct pre arbitrary: ind)
   apply clarsimp
  apply (case_tac ind)
   apply auto
  done

lemma length_takeWhile: "v \<in> set xs \<Longrightarrow> length (takeWhile (\<lambda>z. z \<noteq> v) xs) < length xs"
  by (induct xs) auto

lemma nth_length_takeWhile [simp]: 
  "v \<in> set xs \<Longrightarrow> xs ! (length (takeWhile (%z. z~=v) xs)) = v"
  by (induct xs) auto


lemma map_list_update [simp]:
  "\<lbrakk> x \<in> set xs; distinct xs\<rbrakk> \<Longrightarrow> 
  (map f xs) [length (takeWhile (\<lambda>z. z \<noteq> x) xs) := v] = map (f(x:=v)) xs"
  apply (induct xs)
   apply simp
  apply (rename_tac a xs)
  apply (case_tac "x=a")
   apply auto
  done


(**********************************************************************)
(* Product_Type.thy *)
(**********************************************************************)


lemma split_compose: 
  "(case_prod f) \<circ> (\<lambda> (a,b). ((fa a), (fb b))) = (\<lambda> (a,b). (f (fa a) (fb b)))"
  by (simp add: split_def o_def)

lemma split_iter:
  "(\<lambda> (a,b,c). ((g1 a), (g2 b), (g3 c))) = (\<lambda> (a,p). ((g1 a), (\<lambda> (b, c). ((g2 b), (g3 c))) p))"
  by (simp add: split_def o_def)


(**********************************************************************)
(* Set.thy *)
(**********************************************************************)

lemma singleton_in_set: "A = {a} \<Longrightarrow> a \<in> A" by simp

(**********************************************************************)
(* Map.thy *)
(**********************************************************************)

lemma the_map_upd: "(the \<circ> f(x\<mapsto>v)) = (the \<circ> f)(x:=v)"
  by (simp add: fun_eq_iff)

lemma map_of_in_set: 
  "(map_of xs x = None) = (x \<notin> set (map fst xs))"
  by (induct xs, auto)

lemma map_map_upd [simp]: 
  "y \<notin> set xs \<Longrightarrow> map (the \<circ> f(y\<mapsto>v)) xs = map (the \<circ> f) xs"
  by (simp add: the_map_upd)

lemma map_map_upds [simp]: 
  "(\<forall>y\<in>set ys. y \<notin> set xs) \<Longrightarrow> map (the \<circ> f(ys[\<mapsto>]vs)) xs = map (the \<circ> f) xs"
  by (induct xs arbitrary: f vs) auto

lemma map_upds_distinct [simp]: 
  "distinct ys \<Longrightarrow> length ys = length vs \<Longrightarrow> map (the \<circ> f(ys[\<mapsto>]vs)) ys = vs"
  apply (induct ys arbitrary: f vs)
   apply simp
  apply (case_tac vs)
   apply simp_all
  done

lemma map_of_map_as_map_upd:
  "distinct (map f zs) \<Longrightarrow> map_of (map (\<lambda> p. (f p, g p)) zs) = Map.empty (map f zs [\<mapsto>] map g zs)"
  by (induct zs) auto

(* In analogy to Map.map_of_SomeD *)
lemma map_upds_SomeD: 
  "(m(xs[\<mapsto>]ys)) k = Some y \<Longrightarrow> k \<in> (set xs) \<or> (m k = Some y)"
  apply (induct xs arbitrary: m ys)
   apply simp
  apply (case_tac ys)
   apply fastforce+
  done

lemma map_of_upds_SomeD: "((map_of m) (xs[\<mapsto>]ys)) k = Some y 
  \<Longrightarrow> k \<in> (set (xs @ map fst m))"
  by (auto dest: map_upds_SomeD map_of_SomeD fst_in_set_lemma)

lemma map_of_map_prop:
  "\<lbrakk>map_of (map f xs) k = Some v; \<forall>x \<in> set xs. P1 x; \<forall>x. P1 x \<longrightarrow> P2 (f x)\<rbrakk> \<Longrightarrow> P2 (k, v)"
  by (induct xs) (auto split: if_split_asm)

lemma map_of_map2: "\<forall>x \<in> set xs. (fst (f x)) = (fst x) \<Longrightarrow>
  map_of (map f xs) a = map_option (\<lambda> b. (snd (f (a, b)))) (map_of xs a)"
  by (induct xs, auto)

end
