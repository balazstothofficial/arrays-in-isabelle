theory Master_Assn
  imports Cell Fold_Assn
begin

definition master_assn :: "('a cell ref * 'a::heap cell') list \<Rightarrow> assn" where
  "master_assn C = fold_assn (map (\<lambda>(p, c'). \<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) C)"

lemma open_master_assn_cons: 
    "master_assn ((p,c')#t) = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn t"
  unfolding master_assn_def
  by auto

lemma open_master_assn': 
  assumes "(p, c') \<in>\<^sub>L t"
  shows "master_assn t = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn (remove1 (p, c') t)"
proof-
  from assms have 
    "(\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) \<in>\<^sub>L (map (\<lambda>(p, c'). \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c) t)"
    by auto

  with assms show ?thesis
    unfolding master_assn_def
    using 
        fold_assn_remove1
        fold_assn_remove1_map[of "(p, c')" t "(\<lambda>(p, c'). \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c)"]
    by auto
qed 

lemma open_master_assn: 
  assumes "(p, c') \<in>\<^sub>L t"
  shows "master_assn t \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn (remove1 (p, c') t)"
  using assms open_master_assn' by fastforce

lemma close_master_assn_array: "(a, Array' xs) \<in>\<^sub>L t
  \<Longrightarrow> a' \<mapsto>\<^sub>a xs * a \<mapsto>\<^sub>r cell.Array a' * master_assn (remove1 (a, Array' xs) t) \<Longrightarrow>\<^sub>A master_assn t"
  using open_master_assn'[of a "Array' xs" t]
  by sep_auto

lemma close_master_assn_upd: "(a, Upd' i x a') \<in>\<^sub>L t
     \<Longrightarrow> a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) \<Longrightarrow>\<^sub>A master_assn t"
  using open_master_assn'[of a "Upd' i x a'" t]
  by sep_auto

lemma close_master_assn_upd': "(a, Upd' i x a') \<in>\<^sub>L t
     \<Longrightarrow> a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) = master_assn t"
  using open_master_assn'[of a "Upd' i x a'" t]
  by(auto simp: ent_iffI entails_def)

lemma master_assn_distinct: "h \<Turnstile> master_assn t \<Longrightarrow> distinct (map fst t)"
  apply(rule ccontr)
  apply(drule not_distinct_decomp)
  apply(clarsimp simp: map_eq_Cons_conv Misc.map_eq_append_conv)
  unfolding master_assn_def
  by simp
  
lemma master_assn_distinct': "master_assn t \<Longrightarrow>\<^sub>A \<up>(distinct (map fst t)) * true"
  by(sep_auto simp: master_assn_distinct)

end
