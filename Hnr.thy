theory Hnr 
  imports Array_Safe Diff_Arr
begin

definition hnr where "hnr \<Gamma> c \<Gamma>' R a = <\<Gamma>> c <\<lambda>r. \<Gamma>' * R a r>\<^sub>t"

lemmas hnrD = hnr_def[THEN iffD1]
lemmas hnrI = hnr_def[THEN iffD2]

definition id_assn where "id_assn a c = \<up>(c = a)"

abbreviation array_assn where "array_assn xs xsi \<equiv> xsi \<mapsto>\<^sub>a xs"

named_theorems hnr_rule
named_theorems hnr_rule_2
named_theorems hnr_rule_diff_arr

lemma hnr_return: "hnr \<Gamma> (return x) \<Gamma> id_assn x"
  unfolding hnr_def id_assn_def
  by sep_auto

lemma keep_drop_1:
  assumes
    "\<Gamma>\<^sub>1 \<Longrightarrow>\<^sub>A K\<^sub>1 * D\<^sub>1"
    "\<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A K\<^sub>2 * D\<^sub>2"
  shows 
    "\<Gamma>\<^sub>1 * \<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A (K\<^sub>1 * K\<^sub>2) * (D\<^sub>1 * D\<^sub>2)"
  apply(sep_drule r: assms(1))
  apply(sep_drule r: assms(2))
  by sep_auto

lemma keep_drop_2: "A \<Longrightarrow>\<^sub>A A * emp"
  by sep_auto

lemma keep_drop_3: "A \<Longrightarrow>\<^sub>A emp * A"
  by sep_auto

lemmas keep_drop_step = keep_drop_1 keep_drop_2 keep_drop_3

definition keep_drop where "keep_drop \<Gamma> K D \<equiv> \<Gamma> \<Longrightarrow>\<^sub>A K * D"

lemma keep_drop_init:
  assumes
    "\<Gamma>  \<Longrightarrow>\<^sub>A K' * D'"
    "K' \<Longrightarrow>\<^sub>A K"
    "D' \<Longrightarrow>\<^sub>A D"
  shows
    "keep_drop \<Gamma> K D"
  unfolding keep_drop_def
  using assms(1) assms(2) assms(3) ent_star_mono ent_trans by blast

method keep_drop_simp = (simp only: star_aci)?; rule ent_refl

method keep_drop = 
  rule keep_drop_init, ((rule keep_drop_step)+; fail), keep_drop_simp, keep_drop_simp



lemma hnr_let[hnr_rule]:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 R\<^sub>1 v" 
    "\<And>xi x. hnr (\<Gamma>\<^sub>1 * R\<^sub>1 x xi) (fi xi) (\<Gamma>' x xi) R (f x)"
    "\<And>xi x. keep_drop (\<Gamma>' x xi) \<Gamma>'' (R\<^sub>1' x xi)"
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>'' R (let x = v in f x)"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  apply sep_auto
  apply(sep_drule r: assms(3)[unfolded keep_drop_def])
  by sep_auto

lemma hnr_if: 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a R\<^sub>a a"
    "hnr \<Gamma> bi \<Gamma>\<^sub>b R\<^sub>b b"
  shows 
    "hnr 
      \<Gamma> 
      (if c then ai else bi) 
      (\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) 
      (\<lambda>a r. R\<^sub>a a r * \<up> c \<or>\<^sub>A R\<^sub>b a r * \<up>(\<not>c)) 
      (if c then a else b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  by(sep_auto simp: ent_star_mono)

(* TODO: 
lemma hnr_tuple: 
assumes
  "hnr \<Gamma> ai \<Gamma>\<^sub>a R\<^sub>a a"
  "hnr \<Gamma> bi \<Gamma>\<^sub>b R\<^sub>b b"
shows 
  "hnr 
    \<Gamma> 
    (do { a \<leftarrow> ai; b \<leftarrow> bi; return (a, b) })
    (\<Gamma>\<^sub>a \<and>\<^sub>A \<Gamma>\<^sub>b) 
    (\<lambda>(a1, a2) (r1, r2). R\<^sub>a a1 r1 \<and>\<^sub>A R\<^sub>b a2 r2) 
    (a, b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  apply sep_auto
  apply(rule fi_rule[of "\<Gamma>"])
  sorry *)


lemma hnr_array_nth [hnr_rule, hnr_rule_2]: "
    hnr
     (xsi \<mapsto>\<^sub>a xs * id_assn i ii)
     (array_nth_safe xsi ii) 
     (xsi \<mapsto>\<^sub>a xs * id_assn i ii) 
     id_assn 
     (xs ! i)"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_array_update [hnr_rule, hnr_rule_2]: "
    hnr 
      (xsi \<mapsto>\<^sub>a xs * id_assn i ii * id_assn v vi) 
      (array_update_safe ii vi xsi) 
      (id_assn i ii * id_assn v vi) 
      array_assn 
      (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_pass: "hnr (id_assn x xi) (return xi) emp id_assn x"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_copy: "hnr (id_assn x xi) (return xi) (id_assn x xi) id_assn x"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_frame:
  assumes
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
    "hnr \<Gamma> fi \<Gamma>' R f"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<Gamma>' * F) R f"
  apply(rule hnrI)
  by (smt (verit) assms(1) assms(2) assn_aci(10) fi_rule hnrD hoare_triple_def)

lemma hnr_lookup[hnr_rule_diff_arr]: "
  hnr
    (master_assn t * id_assn i ii * \<up>(t \<turnstile> xs \<sim> xsi \<and> i < length xs))
    (lookup xsi ii)
    (master_assn t * id_assn i ii * \<up>(t \<turnstile> xs \<sim> xsi \<and> i < length xs))
    id_assn
    (xs ! i)"
  unfolding id_assn_def
  apply(rule hnrI)
  using lookup by fastforce

lemma hnr_realize: "
  hnr
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi))
    (realize xsi)
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi))
    array_assn
    xs"
  unfolding id_assn_def
  apply(rule hnrI)
  using realize[of t xs xsi]
  by(sep_auto simp: cons_post_rule ent_refl_true)

lemma ht_combine_post: "<P> c <Q> \<Longrightarrow> <P> c <Q'> \<Longrightarrow> <P> c <\<lambda>r. Q r \<and>\<^sub>A Q' r>"
  unfolding hoare_triple_def
  by(auto simp: Let_def mod_and_dist)

thm ht_combine_post[OF update update', simplified]

lemma hnr_update: "
  hnr
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi \<and> i < length xs) * id_assn i ii * id_assn v vi)
    (update xsi ii vi)
    (id_assn i ii * id_assn v vi)
    (\<lambda>xs xsi. \<exists>\<^sub>At'. master_assn t' * \<up>(t' \<turnstile> xs \<sim> xsi))
    (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  using update[of t xs xsi i v]
  by sep_auto

lemma hnr_update'[hnr_rule_diff_arr]: "
  hnr
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi \<and> i < length xs) * id_assn i ii * id_assn v vi)
    (update xsi ii vi)
    (id_assn i ii * id_assn v vi)
    (\<lambda>xs xsi. \<exists>\<^sub>At'. master_assn t' * \<up>((\<forall>xs' xsi'. t \<turnstile> xs' \<sim>  xsi' \<longrightarrow> t' \<turnstile> xs' \<sim>  xsi') \<and> t' \<turnstile> xs \<sim> xsi))
    (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  apply(sep_auto)
  apply(rule cons_post_rule)
   apply(rule fi_rule[OF update''])
  apply solve_entails
  by sep_auto

(* lemma hnr_array_update [hnr_rule, hnr_rule_2]: "
    hnr 
      (xsi \<mapsto>\<^sub>a xs * id_assn i ii * id_assn v vi) 
      (array_update_safe ii vi xsi) 
      (id_assn i ii * id_assn v vi) 
      array_assn 
      (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto *)

lemma hnr_update_2[hnr_rule_diff_arr]: "
  hnr
    (id_assn i ii * id_assn v vi)
    (update xsi ii vi)
    (id_assn i ii * id_assn v vi)
    (\<lambda>xs xsi. \<exists>\<^sub>At'. master_assn t' * \<up>((\<forall>xs' xsi'. t \<turnstile> xs' \<sim>  xsi' \<longrightarrow> t' \<turnstile> xs' \<sim>  xsi') \<and> t' \<turnstile> xs \<sim> xsi))
    (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  apply(sep_auto)
  apply(rule cons_post_rule)
   apply(rule fi_rule[OF update''])
   apply solve_entails
     apply sep_auto
  sorry

end
