theory Hnr_Frame
  imports Hnr_Base
begin

lemma hnr_frame:
  assumes
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
    "hnr \<Gamma> fi \<Gamma>' f"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<lambda>r ri. \<Gamma>' r ri * F) f"
  apply(rule hnrI)
  using hnrD[OF assms(2)] assms(1) fi_rule
  apply(cases f)
  apply sep_auto+
  by fastforce

attribute_setup framed =
    \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn thm => @{thm hnr_frame} OF [asm_rl, thm]))\<close>
    \<open>Add frame to hnr rule\<close>

lemma frame_prepare:
  assumes
    "emp * P * emp \<Longrightarrow>\<^sub>A emp * Q * F"
  shows
    "P \<Longrightarrow>\<^sub>A Q * F"
  using assms
  by sep_auto

lemma split_id_assn: "id_assn p pi = id_assn (fst p) (fst pi) * id_assn (snd p) (snd pi)"
  by(cases p)(auto simp: id_rel_def)

method frame_norm_assoc = (simp only: 
    mult.left_assoc[where 'a=assn] 
    split_id_assn 
    fst_conv 
    snd_conv
    )?

method frame_prepare = rule frame_prepare, frame_norm_assoc

lemma frame_no_match: 
  assumes
    "Ps1 * (P * Ps2) \<Longrightarrow>\<^sub>A Qs * Q * F"
  shows
    "Ps1 * P * Ps2 \<Longrightarrow>\<^sub>A Qs * Q * F"
  using assms
  by (simp add: mult.assoc)

lemma frame_match_pure:
  assumes
    "Ps1 * \<up>(P) * Ps2 \<Longrightarrow>\<^sub>A Qs * F"
  shows
    "Ps1 * \<up>(P) * Ps2 \<Longrightarrow>\<^sub>A Qs * \<up>(P) * F"
  using assms
  by simp

lemma frame_match:
  assumes
    "P \<Longrightarrow>\<^sub>A Q"
    "Ps1 * Ps2 \<Longrightarrow>\<^sub>A Qs * F"
  shows
    "Ps1 * P * Ps2 \<Longrightarrow>\<^sub>A Qs * Q * F"
  using assms
  by (metis assn_aci(10) ent_star_mono)

lemma frame_match_emp:
   assumes
    "Ps \<Longrightarrow>\<^sub>A Qs * F"
  shows
    "Ps \<Longrightarrow>\<^sub>A Qs * emp * F"
  using assms
  by sep_auto

lemma frame_done: "F * emp \<Longrightarrow>\<^sub>A emp * F" 
  by sep_auto

method frame_try_match methods match_atom = then_else 
  \<open>rule frame_match_pure | rule frame_match, (match_atom; fail) | rule frame_match_emp\<close> 
  \<open>frame_norm_assoc\<close> 
  \<open>rule frame_no_match, frame_try_match match_atom\<close>

method frame_done = simp only: assn_one_left mult_1_right[where 'a=assn], rule ent_refl  

method hnr_frame_inference methods match_atom =
  frame_prepare, (frame_try_match match_atom)+, frame_done
          
method hnr_frame_inference_dbg methods match_atom = 
  frame_prepare, ((frame_try_match match_atom)+)?, frame_done?

experiment
begin

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A a * c * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A emp * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

schematic_goal 
  fixes a b c d::assn
  shows "emp \<Longrightarrow>\<^sub>A emp * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A b * d * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

schematic_goal 
  shows "a * \<up>(b) * c * d \<Longrightarrow>\<^sub>A \<up>(b) * d * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

schematic_goal 
  shows "id_assn (fst p) (fst pi) * id_assn (snd p) (snd pi) \<Longrightarrow>\<^sub>A id_assn p pi * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

schematic_goal 
  shows "id_assn p pi * a \<Longrightarrow>\<^sub>A id_assn (fst p) (fst pi) * id_assn (snd p) (snd pi) * ?F"
  by(hnr_frame_inference \<open>rule ent_refl\<close>)

end

end
