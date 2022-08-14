theory Keep_Drop
  imports Base
begin

lemma keep_drop_1:
  assumes
    "\<Gamma>\<^sub>1 \<Longrightarrow>\<^sub>A K\<^sub>1 * D\<^sub>1"
    "\<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A K\<^sub>2 * D\<^sub>2"
  shows 
    "\<Gamma>\<^sub>1 * \<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A (K\<^sub>1 * K\<^sub>2) * (D\<^sub>1 * D\<^sub>2)"
  apply(sep_drule r: assms(1))
  apply(sep_drule r: assms(2))
  by sep_auto

lemma keep_drop_2: 
  assumes
    "A \<Longrightarrow>\<^sub>A A'"
  shows
    "A \<Longrightarrow>\<^sub>A A' * emp"
  using assms
  by sep_auto

lemma keep_drop_3: "A \<Longrightarrow>\<^sub>A emp * A"
  by simp

lemmas keep_drop_step = keep_drop_1 keep_drop_2 keep_drop_3

definition Keep_Drop where "Keep_Drop \<Gamma> K D \<equiv> \<Gamma> \<Longrightarrow>\<^sub>A K * D"

definition Simp where
  "Simp a b \<equiv> a \<Longrightarrow>\<^sub>A b"

lemma keep_drop_init:
  assumes
    "\<Gamma>  \<Longrightarrow>\<^sub>A K * D"
  shows
    "Keep_Drop \<Gamma> K D"
  unfolding Keep_Drop_def
  using assms(1) ent_star_mono ent_trans by blast

lemma keep_drop_simpI: "a \<Longrightarrow>\<^sub>A b \<Longrightarrow> Simp a b"
  unfolding Simp_def
  by simp

method keep_drop_simp = 
  rule keep_drop_simpI, (simp only: star_aci)?; rule ent_refl

method keep_drop_step methods keep_atom = 
  rule keep_drop_1 | (rule keep_drop_2, keep_atom) | rule keep_drop_3

method keep_drop methods keep_atom = 
  rule keep_drop_init, ((keep_drop_step keep_atom)+; fail)

end
