theory Hnr 
  imports Hnr_Case_Rules Hnr_Fallback Hnr_Frame Hnr_Recursion
begin

lemma let_to_bind: "(let x = v in f x) = (do { x \<leftarrow> Some v; f x })"
  by simp
  
lemma hnr_tuple [hnr_rule]: 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a (Some a)"
    "\<And>a ai. hnr (\<Gamma>\<^sub>a a ai * true) bi (\<Gamma>\<^sub>b a ai) (Some b)"
  shows 
    "hnr 
      \<Gamma>
      (do { ai' \<leftarrow> ai; bi' \<leftarrow> bi; return (ai', bi') })
      (\<lambda>x xi. \<Gamma>\<^sub>b (fst x) (fst xi) (snd x) (snd xi))
      (Some (a, b))"
  apply(rule hnrI)
  using assms[THEN hnrD]
  by sep_auto

method hnr_rule methods frame_match_atom uses rule_set = 
  (rule rule_set[framed] hnr_pass[framed], hnr_frame_inference frame_match_atom) 
  | rule hnr_rule hnr_const

method hnr_step methods frame_match_atom keep_atom uses rule_set =
     simp only: let_to_bind
   | hnr_rule frame_match_atom rule_set: rule_set
   | keep_drop keep_atom 
   | normalize 
   | merge
   | hnr_fallback

(* TODO: How to avoid back tracking? *)
method hnr methods frame_match_atom keep_atom uses rule_set =
  (hnr_step frame_match_atom keep_atom rule_set: rule_set)+
  
end
