theory Hnr 
  imports Hnr_Rules Hnr_Fallback Hnr_Frame Hnr_Recursion
begin

(* TODO: Find out when exactly this is needed *)
method special_frame = 
  rule hnr_frame, assumption, hnr_frame_inference \<open>rule ent_refl\<close>

lemma let_to_bind: "(let x = v in f x) = (do { x \<leftarrow> Some v; f x })"
  by simp

method hnr_rule methods frame_match_atom uses rule_set = 
  (rule rule_set[framed] hnr_pass[framed], hnr_frame_inference frame_match_atom) 
  | rule hnr_rule hnr_const

method hnr_step methods frame_match_atom keep_atom uses rule_set =
     simp only: let_to_bind
   | hnr_rule frame_match_atom rule_set: rule_set
   | keep_drop keep_atom 
   | normalize 
   | merge
   | partial_function_mono
   | hnr_fallback
   | special_frame

(* TODO: How to avoid back tracking? *)
method hnr methods frame_match_atom keep_atom uses rule_set =
  (hnr_step frame_match_atom keep_atom rule_set: rule_set)+
  
end
