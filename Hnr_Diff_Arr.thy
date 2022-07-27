theory Hnr_Diff_Arr
  imports Hnr Diff_Arr_Safe
begin

named_theorems hnr_rule_diff_arr

definition master_assn' where
  "master_assn' S = (\<exists>\<^sub>At. master_assn t * \<up>(\<forall> (xs, xsi) \<in> S. t \<turnstile> xs \<sim> xsi))"

lemma hnr_copy_diff_arr [hnr_rule_diff_arr]:
  "hnr 
      (master_assn' (insert (xs, xsi) S)) 
      (return xsi) 
      (\<lambda>xs' xsi'. master_assn' (insert (xs', xsi') S)) 
      (Some xs)"
  apply(rule hnrI)
  unfolding master_assn'_def
  by sep_auto

definition Diff_Arr_From_Arr where
  "Diff_Arr_From_Arr a = a"

lemma hnr_from_array [hnr_rule_diff_arr]: 
  "hnr 
    (array_assn xs xsi)
    (Diff_Arr.from_array xsi)
    (\<lambda>xs xsi. master_assn' { (xs, xsi) })
    (Some (Diff_Arr_From_Arr xs))"
  apply(rule hnrI)
  unfolding master_assn'_def Diff_Arr_From_Arr_def
  by(sep_auto simp: Let_def)

definition New_Diff_Arr where
  "New_Diff_Arr a = a"

lemma hnr_from_list [hnr_rule_diff_arr]: 
  "hnr 
    emp
    (Diff_Arr.from_list xs)
    (\<lambda>xs xsi. master_assn' { (xs, xsi) })
    (Some (New_Diff_Arr xs))
  "
  apply(rule hnrI)
  unfolding master_assn'_def New_Diff_Arr_def
  by(sep_auto simp: Let_def)

lemma hnr_lookup[hnr_rule_diff_arr]: "
  hnr
    (master_assn' (insert (xs, xsi) S) * id_assn i ii) 
    (Diff_Arr_Safe.lookup xsi ii)
    (\<lambda>r ri. id_assn r ri * master_assn' S)
    (Some (xs ! i))"
  unfolding id_rel_def master_assn'_def
  apply(rule hnrI)
  apply sep_auto
  subgoal for t
    apply(subgoal_tac "t \<turnstile> xs  \<sim> xsi")
     apply(rule cons_post_rule)
      apply(rule fi_rule[OF lookup_safe[of t xs]])
    by sep_auto+
  done

lemma hnr_realize: "
  hnr
    (master_assn' (insert (xs, xsi) S))
    (Diff_Arr.realize xsi)
    (\<lambda> r ri. master_assn' S * array_assn r ri)
    (Some xs)"
  unfolding id_rel_def master_assn'_def
  apply(rule hnrI)
  apply sep_auto
  subgoal for t
    apply(subgoal_tac "t \<turnstile> xs  \<sim> xsi")
    apply(rule cons_post_rule)
    apply(rule fi_rule[OF realize[of t xs]])
    by sep_auto+
  done

lemma hnr_update[hnr_rule_diff_arr]: "
  hnr
    (master_assn' (insert (xs, xsi) S) * id_assn i ii * id_assn v vi)
    (Diff_Arr_Safe.update xsi ii vi)
    (\<lambda>xs' xsi'. master_assn' (insert (xs', xsi') S))
    (Some (xs [i:= v]))"
  unfolding id_rel_def master_assn'_def
  apply(rule hnrI)
  apply(sep_auto)
  subgoal for t
    apply(subgoal_tac "t \<turnstile> xs  \<sim> xsi")
    apply(rule cons_post_rule)
    apply(rule fi_rule[OF update_safe[of t xs]])
    by sep_auto+
  done

lemma transfer_diff_arr_rel:
  assumes 
    "t \<turnstile> xs \<sim> xsi" 
    "\<forall>xs xsi. t \<turnstile> xs \<sim> xsi \<longrightarrow> t' \<turnstile> xs \<sim> xsi"
  shows 
    "t' \<turnstile> xs \<sim> xsi"
  using assms by blast

method hnr_transfer_diff_arr_rel = 
  ((drule(1) transfer_diff_arr_rel)+)?, (thin_tac "\<forall>xs' xsi'. _ \<turnstile> xs' \<sim> xsi' \<longrightarrow> _ \<turnstile> xs' \<sim> xsi'")

definition Si_Tag where
  "Si_Tag x = x"

lemma si_initialize: "A \<union> {} = Si_Tag B \<Longrightarrow> A = B"
  unfolding Si_Tag_def
  by simp

lemma si_move_tag: "Si_Tag (insert x B) = insert x (Si_Tag B)"
  unfolding Si_Tag_def
  by simp

lemma si_rotate: "A \<union> insert x B = C \<Longrightarrow> insert x A \<union> B = C"
  by simp

lemma si_match: "insert x A \<union> B = C \<Longrightarrow> insert x A \<union> B = insert x C"
  by auto

lemma si_rotate_back: "insert x A \<union> B = C \<Longrightarrow> A \<union> insert x B = C"
  by simp

lemma si_finish: "A \<union> {} = Si_Tag A"
  unfolding Si_Tag_def
  by simp

method si_try_match = then_else 
  \<open>rule si_match\<close>
  \<open>((rule si_rotate_back)+)?\<close>
  \<open>rule si_rotate, si_try_match\<close>

method si_initialize = rule si_initialize, (simp(no_asm) only: si_move_tag)?

method set_inference_keep = si_initialize, ((rule si_finish | si_try_match)+)?

method set_inference = set_inference_keep; fail

experiment
begin

schematic_goal "{ 1, 2, 3 } = ?S"
  apply set_inference
  done

schematic_goal "{ 1, 2, 3 } = insert 3 (insert 2 ?S)"
  apply set_inference
  done

schematic_goal "{ 1, 2, 3 } = insert 1 (insert 2 (insert 3 ?S))"
  apply set_inference
  done

schematic_goal "{ 1, 2, 3 } = insert 4 (insert 2 (insert 4 ?S))"
  apply set_inference_keep
  oops

end

lemma master_assn'_cong:
  assumes
    "S = S'"
  shows 
    "master_assn' S \<Longrightarrow>\<^sub>A master_assn' S'"
  using assms
  by simp

method hnr_diff_arr_match_atom = then_else
  \<open>rule master_assn'_cong\<close>
  \<open>set_inference\<close>
  \<open>rule ent_refl\<close>

lemma kdm_init: 
  assumes
    "S' \<subseteq> S"
    "S' = S'"
  shows
    "master_assn' S \<Longrightarrow>\<^sub>A master_assn' S'"
  using assms
  unfolding master_assn'_def
  by sep_auto

lemma kdm_keep:
  assumes
    "S' \<subseteq> S"
  shows
    "insert x S' \<subseteq> insert x S"
  using assms
  by auto

lemma kdm_drop:
  assumes
    "S' \<subseteq> S"
  shows
    "S' \<subseteq> insert x S"
  using assms
  by auto


method kdm_subset = ((rule kdm_keep | rule kdm_drop)+)?, rule subset_refl

method kdm_check_not_empty = then_else
  \<open>rule refl[of "{}"]\<close>
  \<open>fail\<close>
  \<open>rule refl\<close>

method kdm = rule kdm_init, kdm_subset, kdm_check_not_empty

method diff_arr_kdm = rule ent_refl | kdm

experiment
begin

schematic_goal "master_assn' ({ a, b, c }:: ('a :: heap list \<times> 'a cell ref) set)
   \<Longrightarrow>\<^sub>A master_assn' (?S :: ('a list \<times> 'a cell ref) set)"
  apply kdm
  done

schematic_goal 
  "\<And> a b c. master_assn' ({ a, b, c }:: ('a :: heap list \<times> 'a cell ref) set)
   \<Longrightarrow>\<^sub>A master_assn' (?S :: ('a list \<times> 'a cell ref) set)"
  apply(then_else kdm fail succeed)
  oops

schematic_goal 
  "\<And> a b c. master_assn' ({ a, b, c }:: ('a :: heap list \<times> 'a cell ref) set)
   \<Longrightarrow>\<^sub>A master_assn' (?S a c :: ('a list \<times> 'a cell ref) set)"
  apply kdm
  done

end
  
method hnr_diff_arr = hnr hnr_diff_arr_match_atom diff_arr_kdm rule_set: hnr_rule_diff_arr

method hnr_step_diff_arr = hnr_step hnr_diff_arr_match_atom diff_arr_kdm rule_set: hnr_rule_diff_arr

end
