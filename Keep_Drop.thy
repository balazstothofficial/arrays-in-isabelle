theory Keep_Drop
  imports Base
begin

definition Keep_Drop where 
  "Keep_Drop \<Gamma> K D \<equiv> \<Gamma> \<Longrightarrow>\<^sub>A K * D"

lemma init:
  assumes
    "\<Gamma> \<Longrightarrow>\<^sub>A K * D"
  shows
    "Keep_Drop \<Gamma> K D"
  unfolding Keep_Drop_def
  using assms by simp

lemma split:
  assumes
    "\<Gamma>\<^sub>1 \<Longrightarrow>\<^sub>A K\<^sub>1 * D\<^sub>1"
    "\<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A K\<^sub>2 * D\<^sub>2"
  shows 
    "\<Gamma>\<^sub>1 * \<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A (K\<^sub>1 * K\<^sub>2) * (D\<^sub>1 * D\<^sub>2)" 
  apply(sep_drule r: assms(1))
  apply(sep_drule r: assms(2))
  by sep_auto

lemma keep: 
  assumes
    "\<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>'"
  shows
    "\<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>' * emp"
  using assms
  by sep_auto

lemma drop: "\<Gamma> \<Longrightarrow>\<^sub>A emp * \<Gamma>"
  by simp

method keep_drop_step methods keep_atom =
  rule split | (rule keep, keep_atom) | rule drop

method keep_drop methods keep_atom = 
  rule init, ((keep_drop_step keep_atom)+; fail)

end
