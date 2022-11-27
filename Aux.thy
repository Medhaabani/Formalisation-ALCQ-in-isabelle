theory Aux imports Main

begin


subsection {* Some list functions and list properties *}

constdefs
  -- "remove xs from ys"
  remove :: "['a list, 'a list] \<Rightarrow> 'a list"
  "remove xs ys == filter (\<lambda> y. \<not> (y mem xs)) ys"

lemma set_remove [simp]: "set (remove xs ys) = set ys - set xs"
by (auto simp add: remove_def mem_iff)

constdefs
  "list_union xs ys == remdups (xs @ ys)"

lemma set_list_union [simp]: "set (list_union xs ys) = set xs \<union> set ys"
by (simp add: list_union_def)

consts list_inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec
  "list_inter [] ys = []"
  "list_inter (x#xs) ys = 
     (if (x mem ys) then x#list_inter xs ys else list_inter xs ys)"

lemma set_list_inter [simp]: "set (list_inter xs ys) = (set xs) \<inter> (set ys)"
by (induct xs) (simp add: in_set_code)+

lemma foldr_list_union [rule_format,simp]:
  "\<forall> xs. set (foldr list_union xss xs) = (\<Union> set (map set xss)) \<union> set xs"
by (induct xss) auto


lemma list_ex_mono: 
  "set ab \<subseteq> set ab' \<Longrightarrow> list_ex p ab \<Longrightarrow> list_ex p ab'"
  by (fastsimp simp add: list_ex_iff)


lemma list_ex_pred_mono [rule_format]: 
  "list_ex p ab \<Longrightarrow> \<forall> x. (p x) \<longrightarrow> (p' x)  \<Longrightarrow> list_ex p' ab"
  by (fastsimp simp add: list_ex_iff)



subsection {* Allocation Type class  *}


class alloc = 
  fixes new_var :: "'a list \<Rightarrow> 'a"
  assumes new_var_gen: "(new_var vs \<notin> set vs)"


consts
  list_max :: "nat list \<Rightarrow> nat"
primrec
  "list_max [] = 0"
  "list_max (x # xs) = max x (list_max xs)"

lemma list_max_leq [rule_format]: "x \<in> set vs \<longrightarrow> x \<le> list_max vs"
by (induct vs) auto

lemma list_max_Suc: "Suc (list_max vs) \<notin> set vs"
by (fastsimp dest: list_max_leq)

instantiation nat :: alloc
begin
definition
  new_var_nat_def: "new_var vs = (Suc (list_max vs))"
instance proof
qed (simp add: new_var_nat_def list_max_Suc)

end

end
