(* Author: Florian Haftmann, TU Muenchen *)

header {* Lists with elements distinct as canonical example for datatype invariants *}

theory Dlist
imports Main Fset
begin

section {* Prelude *}

text {* Without canonical argument order, higher-order things tend to get confusing quite fast: *}

setup {* Sign.map_naming (Name_Space.add_path "List") *}

primrec member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
    "member [] y \<longleftrightarrow> False"
  | "member (x#xs) y \<longleftrightarrow> x = y \<or> member xs y"

lemma member_set:
  "member = set"
proof (rule ext)+
  fix xs :: "'a list" and x :: 'a
  have "member xs x \<longleftrightarrow> x \<in> set xs" by (induct xs) auto
  then show "member xs x = set xs x" by (simp add: mem_def)
qed

lemma not_set_compl:
  "Not \<circ> set xs = - set xs"
  by (simp add: fun_Compl_def bool_Compl_def comp_def expand_fun_eq)

primrec fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
    "fold f [] s = s"
  | "fold f (x#xs) s = fold f xs (f x s)"

lemma foldl_fold:
  "foldl f s xs = List.fold (\<lambda>x s. f s x) xs s"
  by (induct xs arbitrary: s) simp_all

setup {* Sign.map_naming Name_Space.parent_path *}


section {* The type of distinct lists *}

typedef (open) 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> ?dlist" by simp
qed


text {* Formal, totalized constructor for @{typ "'a dlist"}: *}

definition Dlist :: "'a list \<Rightarrow> 'a dlist" where
  [code del]: "Dlist xs = Abs_dlist (remdups xs)"

lemma distinct_list_of_dlist [simp]:
  "distinct (list_of_dlist dxs)"
  using list_of_dlist [of dxs] by simp

lemma list_of_dlist_Dlist [simp]:
  "list_of_dlist (Dlist xs) = remdups xs"
  by (simp add: Dlist_def Abs_dlist_inverse)

lemma Dlist_list_of_dlist [simp, code abstype]:
  "Dlist (list_of_dlist dxs) = dxs"
  by (simp add: Dlist_def list_of_dlist_inverse distinct_remdups_id)


text {* Fundamental operations: *}

definition empty :: "'a dlist" where
  "empty = Dlist []"

definition insert :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "insert x dxs = Dlist (List.insert x (list_of_dlist dxs))"

definition remove :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "remove x dxs = Dlist (remove1 x (list_of_dlist dxs))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b dlist" where
  "map f dxs = Dlist (remdups (List.map f (list_of_dlist dxs)))"

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "filter P dxs = Dlist (List.filter P (list_of_dlist dxs))"


text {* Derived operations: *}

definition null :: "'a dlist \<Rightarrow> bool" where
  "null dxs = List.null (list_of_dlist dxs)"

definition member :: "'a dlist \<Rightarrow> 'a \<Rightarrow> bool" where
  "member dxs = List.member (list_of_dlist dxs)"

definition length :: "'a dlist \<Rightarrow> nat" where
  "length dxs = List.length (list_of_dlist dxs)"

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold f dxs = List.fold f (list_of_dlist dxs)"


section {* Executable version obeying invariant *}

lemma list_of_dlist_empty [simp, code abstract]:
  "list_of_dlist empty = []"
  by (simp add: empty_def)

lemma list_of_dlist_insert [simp, code abstract]:
  "list_of_dlist (insert x dxs) = List.insert x (list_of_dlist dxs)"
  by (simp add: insert_def)

lemma list_of_dlist_remove [simp, code abstract]:
  "list_of_dlist (remove x dxs) = remove1 x (list_of_dlist dxs)"
  by (simp add: remove_def)

lemma list_of_dlist_map [simp, code abstract]:
  "list_of_dlist (map f dxs) = remdups (List.map f (list_of_dlist dxs))"
  by (simp add: map_def)

lemma list_of_dlist_filter [simp, code abstract]:
  "list_of_dlist (filter P dxs) = List.filter P (list_of_dlist dxs)"
  by (simp add: filter_def)


section {* Implementation of sets by distinct lists -- canonical! *}

definition Set :: "'a dlist \<Rightarrow> 'a fset" where
  "Set dxs = Fset.Set (list_of_dlist dxs)"

definition Coset :: "'a dlist \<Rightarrow> 'a fset" where
  "Coset dxs = Fset.Coset (list_of_dlist dxs)"

code_datatype Set Coset

declare member_code [code del]
declare is_empty_Set [code del]
declare empty_Set [code del]
declare UNIV_Set [code del]
declare insert_Set [code del]
declare remove_Set [code del]
declare map_Set [code del]
declare filter_Set [code del]
declare forall_Set [code del]
declare exists_Set [code del]
declare card_Set [code del]
declare subfset_eq_forall [code del]
declare subfset_subfset_eq [code del]
declare eq_fset_subfset_eq [code del]
declare inter_project [code del]
declare subtract_remove [code del]
declare union_insert [code del]
declare Infimum_inf [code del]
declare Supremum_sup [code del]

lemma Set_Dlist [simp]:
  "Set (Dlist xs) = Fset (set xs)"
  by (simp add: Set_def Fset.Set_def)

lemma Coset_Dlist [simp]:
  "Coset (Dlist xs) = Fset (- set xs)"
  by (simp add: Coset_def Fset.Coset_def)

lemma member_Set [simp]:
  "Fset.member (Set dxs) = List.member (list_of_dlist dxs)"
  by (simp add: Set_def member_set)

lemma member_Coset [simp]:
  "Fset.member (Coset dxs) = Not \<circ> List.member (list_of_dlist dxs)"
  by (simp add: Coset_def member_set not_set_compl)

lemma is_empty_Set [code]:
  "Fset.is_empty (Set dxs) \<longleftrightarrow> null dxs"
  by (simp add: null_def null_empty member_set)

lemma bot_code [code]:
  "bot = Set empty"
  by (simp add: empty_def)

lemma top_code [code]:
  "top = Coset empty"
  by (simp add: empty_def)

lemma insert_code [code]:
  "Fset.insert x (Set dxs) = Set (insert x dxs)"
  "Fset.insert x (Coset dxs) = Coset (remove x dxs)"
  by (simp_all add: insert_def remove_def member_set not_set_compl)

lemma remove_code [code]:
  "Fset.remove x (Set dxs) = Set (remove x dxs)"
  "Fset.remove x (Coset dxs) = Coset (insert x dxs)"
  by (auto simp add: insert_def remove_def member_set not_set_compl)

lemma member_code [code]:
  "Fset.member (Set dxs) = member dxs"
  "Fset.member (Coset dxs) = Not \<circ> member dxs"
  by (simp_all add: member_def)

lemma map_code [code]:
  "Fset.map f (Set dxs) = Set (map f dxs)"
  by (simp add: member_set)
  
lemma filter_code [code]:
  "Fset.filter f (Set dxs) = Set (filter f dxs)"
  by (simp add: member_set)

lemma forall_Set [code]:
  "Fset.forall P (Set xs) \<longleftrightarrow> list_all P (list_of_dlist xs)"
  by (simp add: member_set list_all_iff)

lemma exists_Set [code]:
  "Fset.exists P (Set xs) \<longleftrightarrow> list_ex P (list_of_dlist xs)"
  by (simp add: member_set list_ex_iff)

lemma card_code [code]:
  "Fset.card (Set dxs) = length dxs"
  by (simp add: length_def member_set distinct_card)

lemma foldl_list_of_dlist:
  "foldl f s (list_of_dlist dxs) = fold (\<lambda>x s. f s x) dxs s"
  by (simp add: foldl_fold fold_def)

lemma inter_code [code]:
  "inf A (Set xs) = Set (filter (Fset.member A) xs)"
  "inf A (Coset xs) = fold Fset.remove xs A"
  by (simp_all only: Set_def Coset_def foldl_list_of_dlist inter_project list_of_dlist_filter)

lemma subtract_code [code]:
  "A - Set xs = fold Fset.remove xs A"
  "A - Coset xs = Set (filter (Fset.member A) xs)"
  by (simp_all only: Set_def Coset_def foldl_list_of_dlist subtract_remove list_of_dlist_filter)

lemma union_code [code]:
  "sup (Set xs) A = fold Fset.insert xs A"
  "sup (Coset xs) A = Coset (filter (Not \<circ> Fset.member A) xs)"
  by (simp_all only: Set_def Coset_def foldl_list_of_dlist union_insert list_of_dlist_filter)

context complete_lattice
begin

lemma Infimum_code [code]:
  "Infimum (Set As) = fold inf As top"
  by (simp only: Set_def Infimum_inf foldl_list_of_dlist inf.commute)

lemma Supremum_code [code]:
  "Supremum (Set As) = fold sup As bot"
  by (simp only: Set_def Supremum_sup foldl_list_of_dlist sup.commute)

end

hide (open) const member fold empty insert remove map filter null member length fold

end
