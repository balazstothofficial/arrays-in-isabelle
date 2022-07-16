theory Base
  imports "Separation_Logic_Imperative_HOL.Sep_Main" Named_Simpsets More_Eisbach_Tools
begin

no_notation Ref.update ("_ := _" 62)
notation Ref.update ("_ :=\<^sub>R _" 62)

abbreviation contains where
  "contains x xs \<equiv> x \<in> set xs"

notation contains ("(_/ \<in>\<^sub>L _)" [51, 51] 50)

lemma ent_iff:"A = B \<longleftrightarrow> (B \<Longrightarrow>\<^sub>A A) \<and> (A \<Longrightarrow>\<^sub>A B)"
  using ent_iffI by auto

lemma htriple_frame_fwd:
  assumes R: "P \<Longrightarrow>\<^sub>A R"
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes I: "<R*F> c <Q>"
  shows "<Ps> c <Q>"
  using assms
  by (metis cons_rule ent_refl fr_refl)

(* TODO: Probably not needed *)
lemma htriple_return_entails: "<P> return x <Q> \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q x"
  unfolding hoare_triple_def Let_def entails_def
  using effect_returnI effect_run by fastforce

(* TODO: Probably not needed *)
lemma lookup_fwd: "<A> !a <\<lambda>c. A>"
  by (smt (verit, del_insts) deconstruct_rules(4) effect_returnI effect_run hoare_triple_def new_addr_refl run_lookup the_state.simps)

method sep_drule uses r = 
  rule ent_frame_fwd[OF r] htriple_frame_fwd[OF r], (assumption+)?, frame_inference

end
