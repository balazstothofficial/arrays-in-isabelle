theory Hnr_Fallback
  imports Hnr_Base
begin

lemma hnr_fallback: 
  assumes
    "\<And>h. h \<Turnstile> \<Gamma> \<Longrightarrow> c = ci"
  shows
    "hnr \<Gamma> (return ci) (\<lambda> r ri. \<Gamma> * id_assn r ri) (Some c)"
  apply(rule hnrI)
  apply(rule hoare_triple_preI)
  using assms 
  by(sep_auto simp: id_rel_def)

method extract_pre uses rule =
  (determ\<open>elim mod_starE rule[elim_format]\<close>)?

lemma models_id_assn:"h \<Turnstile> id_assn x xi \<Longrightarrow> x = xi" 
  by(simp add: id_rel_def)

(* TODO: This just works for non-refined fallbacks *)
method hnr_fallback = 
  rule hnr_fallback,
  extract_pre rule: models_id_assn,
  hypsubst,
  rule refl

end
