theory Hnr 
  imports Array_Safe Diff_Arr
begin

definition hnr where "hnr \<Gamma> c \<Gamma>' R a = <\<Gamma>> c <\<lambda>r. \<Gamma>' * R a r>\<^sub>t"

lemmas hnrD = hnr_def[THEN iffD1]
lemmas hnrI = hnr_def[THEN iffD2]

definition id_assn where "id_assn a c = \<up>(c = a)"

abbreviation array_assn where "array_assn xs xsi \<equiv> xsi \<mapsto>\<^sub>a xs"

lemma hnr_return: "hnr \<Gamma> (return x) \<Gamma> id_assn x"
  unfolding hnr_def id_assn_def
  by sep_auto

lemma hnr_let:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 R\<^sub>1 v" 
    "\<And>xi x. hnr (\<Gamma>\<^sub>1 * R\<^sub>1 x xi) (fi xi) \<Gamma>' R (f x)"
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>' R (let x = v in f x)"
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
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


lemma hnr_array_nth: "
    hnr
     (xsi \<mapsto>\<^sub>a xs * id_assn i ii)
     (array_nth_safe xsi ii) 
     (xsi \<mapsto>\<^sub>a xs * id_assn i ii) 
     id_assn 
     (xs ! i)"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_array_update: "
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

(* TODO : *)
lemma hnr_frame:
  assumes
    "hnr \<Gamma> fi \<Gamma>' R f"
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<Gamma>' * F) R f"
  apply(rule hnrI)
  by (smt (verit) assms(1) assms(2) assn_aci(10) fi_rule hnrD hoare_triple_def)

lemma hnr_lookup: "
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

lemma hnr_update': "
  hnr
    (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi \<and> i < length xs) * id_assn i ii * id_assn v vi)
    (update xsi ii vi)
    (id_assn i ii * id_assn v vi)
    (\<lambda>_ _. \<exists>\<^sub>At'. master_assn t' * \<up>(\<forall>xs' xsi'. t \<turnstile> xs' \<sim>  xsi' \<longrightarrow> t' \<turnstile> xs' \<sim>  xsi'))
    (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  using update'[of t xs xsi i v]
  by sep_auto

end
