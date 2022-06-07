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

lemma htriple_return_entails: "<P> return x <Q> \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q x"
  unfolding hoare_triple_def Let_def entails_def
  using effect_returnI effect_run by fastforce

lemma htriple_return_and: " \<lbrakk><\<Gamma>> return a <\<Gamma>\<^sub>a>; <\<Gamma>> return b <\<Gamma>\<^sub>b>\<rbrakk> \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma>\<^sub>a a \<and>\<^sub>A \<Gamma>\<^sub>b b"
  using htriple_return_entails[of \<Gamma> a \<Gamma>\<^sub>a] htriple_return_entails[of \<Gamma> b \<Gamma>\<^sub>b] ent_conjI
  by auto

method sep_drule uses r = 
  rule ent_frame_fwd[OF r] htriple_frame_fwd[OF r], (assumption+)?, frame_inference

end