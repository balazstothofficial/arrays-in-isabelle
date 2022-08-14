theory Hnr_Base
  imports Base
begin                       

definition hnr where 
  "hnr \<Gamma> c \<Gamma>' a = (
    case a of None \<Rightarrow> True | 
              Some a \<Rightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' a r>\<^sub>t
  )"

lemma hnr_none [simp]: "hnr \<Gamma> c \<Gamma>' None"
  unfolding hnr_def
  by simp

named_theorems hnr_rule

lemma hnr_hoare: "(\<forall>x. a = Some x \<longrightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' x r>\<^sub>t) \<longleftrightarrow> (hnr \<Gamma> c \<Gamma>' a)"
  unfolding hnr_def
  by(simp split: option.split)

lemmas hnrI = hnr_hoare[THEN iffD1, rule_format]
lemmas hnrD = hnr_hoare[THEN iffD2, rule_format]

definition id_rel where "id_rel a c \<equiv> c = a"

abbreviation id_assn where "id_assn a c \<equiv> \<up>(id_rel a c)"

abbreviation array_assn where "array_assn xs xsi \<equiv> xsi \<mapsto>\<^sub>a xs"

lemma hnr_const: "hnr \<Gamma> (return x) (\<lambda>r ri. \<Gamma> * id_assn r ri) (Some x)"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_pass: "hnr (\<Gamma> x xi) (return xi) \<Gamma> (Some x)"
  apply(rule hnrI)
  by sep_auto

lemma hnr_copy: "hnr (id_assn x xi) (return xi) id_assn (Some x)"
  using hnr_pass.

end
