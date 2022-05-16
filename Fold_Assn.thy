theory Fold_Assn
  imports Base
begin

abbreviation contains where
  "contains x xs \<equiv> x \<in> set xs"

notation
  contains ("(_/ \<in>\<^sub>L _)" [51, 51] 50)

definition fold_assn :: "assn list \<Rightarrow> assn" where
  "fold_assn assns = foldr (*) assns emp"

lemma fold_assn_emp[simp]: "fold_assn [] = emp"
  unfolding fold_assn_def
  by simp

lemma fold_assn_cons[simp]: "fold_assn (x#xs) = x * fold_assn xs"
  unfolding fold_assn_def
  by simp_all

lemma fold_assn_app [simp]: "fold_assn (xs@ys) = fold_assn xs * fold_assn ys"
  apply(induction xs)
  by(auto simp: algebra_simps)

lemma fold_assn_remove1: "x \<in>\<^sub>L xs \<Longrightarrow> fold_assn xs = x * fold_assn (remove1 x xs)"
  apply(induction xs)
  by(auto simp: algebra_simps)

lemma fold_assn_false [simp]: "false \<in>\<^sub>L xs \<Longrightarrow> fold_assn xs = false"
  using fold_assn_remove1
  by auto

lemma fold_assn_emp_remove1: "fold_assn xs = fold_assn (remove1 emp xs)"
  apply(induction xs)
  by auto

lemma fold_assn_emp_removeAll: "fold_assn xs = fold_assn (removeAll emp xs)"
  apply(induction xs)
  by auto  

lemma fold_assn_remove1_map: "x \<in>\<^sub>L xs
   \<Longrightarrow> fold_assn (remove1 (f x) (map f xs)) = fold_assn (map f (remove1 x xs))"
proof(induction xs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a xs)
  then show ?case
    using fold_assn_remove1[of "f a" "map f xs"] image_iff
    by fastforce
qed

end
