theory Base
  imports "Separation_Logic_Imperative_HOL.Sep_Main" Named_Simpsets More_Eisbach_Tools
begin

no_notation Ref.update ("_ := _" 62)
notation Ref.update ("_ :=\<^sub>R _" 62)

lemma htriple_frame_fwd:
  assumes R: "P \<Longrightarrow>\<^sub>A R"
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes I: "<R*F> c <Q>"
  shows "<Ps> c <Q>"
  using assms
  by (metis cons_rule ent_refl fr_refl)

lemma htriple_combine_post: "<P> c <Q> \<Longrightarrow> <P> c <Q'> \<Longrightarrow> <P> c <\<lambda>r. Q r \<and>\<^sub>A Q' r>"
  unfolding hoare_triple_def
  by(auto simp: Let_def mod_and_dist)

method sep_drule uses r = 
  rule ent_frame_fwd[OF r] htriple_frame_fwd[OF r], (assumption+)?, frame_inference

end