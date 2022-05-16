theory HNR 
  imports Array_Safe
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
    "hnr \<Gamma> (if c then ai else bi) (\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) id_assn (if c then a else b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  apply sep_auto
  sorry


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

lemma hnr_frame:
  assumes
    "hnr \<Gamma> fi \<Gamma>' R f"
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<Gamma>' * F) R f"
  sorry

(* for ifs and my arrays *)


end
