theory Hnr_Diff_Arr
  imports Hnr Diff_Arr_Safe
begin

named_theorems hnr_rule_diff_arr

lemma hnr_copy_diff_arr [hnr_rule_diff_arr]:
  "hnr (master_assn t * \<up>(t \<turnstile> x \<sim> xi)) (return xi) (\<lambda>x xi. master_assn t * \<up>(t \<turnstile> x \<sim> xi)) x"
  apply(rule hnrI)
  by sep_auto

lemma hnr_from_array: 
  "hnr 
    (array_assn xs xsi)
    (Diff_Arr.from_array xsi)
    (\<lambda>xs xsi. \<exists>\<^sub>At. master_assn t * \<up>(t \<turnstile> xs \<sim> xsi))
    xs
  "
  apply(rule hnrI)
  using ent_refl_true fi_rule from_array by blast

lemma hnr_from_list: 
  "hnr 
    emp
    (Diff_Arr.from_list xs)
    (\<lambda>xs xsi. \<exists>\<^sub>At. master_assn t * \<up>(t \<turnstile> xs \<sim> xsi))
    xs
  "
  apply(rule hnrI)
  using ent_refl_true fi_rule from_list by blast

lemma hnr_lookup[hnr_rule_diff_arr]: "
  hnr
    (master_assn t * id_assn i ii * \<up>(t \<turnstile> xs \<sim> xsi))
    (diff_arr_lookup_safe xsi ii)
    (\<lambda>r ri. master_assn t * id_assn r ri)
    (xs ! i)"
  unfolding id_rel_def
  apply(rule hnrI)
  using lookup_safe by fastforce

lemma hnr_realize: "
  hnr
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi))
    (Diff_Arr.realize xsi)
    (\<lambda> r ri. master_assn t  * array_assn r ri)
    xs"
  unfolding id_rel_def
  apply(rule hnrI)
  using realize[of t xs xsi]
  by(sep_auto simp: cons_post_rule ent_refl_true)

lemma hnr_update[hnr_rule_diff_arr]: "
  hnr
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi) * id_assn i ii * id_assn v vi)
    (diff_arr_update_safe xsi ii vi)
    (\<lambda>xs xsi. \<exists>\<^sub>At'. master_assn t' * 
              \<up>((\<forall>xs' xsi'. t \<turnstile> xs' \<sim>  xsi' \<longrightarrow> t' \<turnstile> xs' \<sim>  xsi') \<and> t' \<turnstile> xs \<sim> xsi))
    (xs [i:= v])"
  unfolding id_rel_def
  apply(rule hnrI)
  apply(sep_auto)
  apply(rule cons_post_rule)
  apply(rule fi_rule[OF update_safe])
  by sep_auto+  

lemma transfer_diff_arr_rel:
  assumes 
    "t \<turnstile> xs \<sim> xsi" 
    "\<forall>xs xsi. t \<turnstile> xs \<sim> xsi \<longrightarrow> t' \<turnstile> xs \<sim> xsi"
  shows 
    "t' \<turnstile> xs \<sim> xsi"
  using assms by blast

method hnr_transfer_diff_arr_rel = 
  ((drule(1) transfer_diff_arr_rel)+)?, (thin_tac "\<forall>xs' xsi'. _ \<turnstile> xs' \<sim> xsi' \<longrightarrow> _ \<turnstile> xs' \<sim> xsi'")

method hnr_diff_arr = hnr hnr_transfer_diff_arr_rel rule_set: hnr_rule_diff_arr

lemma bug_1: 
  assumes "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  shows "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  using assms
  sorry

lemma bug_2: "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  using triv_exI[of master_assn t]
  apply auto
  sorry

end
