theory Norm
  imports Base
begin

definition Norm where
  "Norm \<Gamma> \<Gamma>' \<equiv> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>'"

lemma normI: "\<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>' \<Longrightarrow> Norm \<Gamma> \<Gamma>'"
  unfolding Norm_def
  by simp

method normalize uses rules =
  rule normI, (simp only: star_aci rules)?; rule ent_refl
             
end
