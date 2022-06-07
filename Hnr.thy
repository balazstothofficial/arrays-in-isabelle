theory Hnr 
  imports Base
begin                       

definition hnr where "hnr \<Gamma> c \<Gamma>' a = <\<Gamma>> c <\<lambda>r. \<Gamma>' a r>\<^sub>t"

lemmas hnrD = hnr_def[THEN iffD1]
lemmas hnrI = hnr_def[THEN iffD2]

definition id_rel where "id_rel a c \<equiv> c = a"

abbreviation id_assn where "id_assn a c \<equiv> \<up>(id_rel a c)"

abbreviation array_assn where "array_assn xs xsi \<equiv> xsi \<mapsto>\<^sub>a xs"

named_theorems hnr_rule

lemma hnr_return: "hnr \<Gamma> (return x) (\<lambda> x xi. \<Gamma> * id_assn x xi) x"
  unfolding hnr_def id_rel_def
  by sep_auto

lemma keep_drop_1:
  assumes
    "\<Gamma>\<^sub>1 \<Longrightarrow>\<^sub>A K\<^sub>1 * D\<^sub>1"
    "\<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A K\<^sub>2 * D\<^sub>2"
  shows 
    "\<Gamma>\<^sub>1 * \<Gamma>\<^sub>2 \<Longrightarrow>\<^sub>A (K\<^sub>1 * K\<^sub>2) * (D\<^sub>1 * D\<^sub>2)"
  apply(sep_drule r: assms(1))
  apply(sep_drule r: assms(2))
  by sep_auto

lemma keep_drop_2: "A \<Longrightarrow>\<^sub>A A * emp"
  by sep_auto

lemma keep_drop_3: "A \<Longrightarrow>\<^sub>A emp * A"
  by sep_auto

lemmas keep_drop_step = keep_drop_1 keep_drop_2 keep_drop_3

definition keep_drop where "keep_drop \<Gamma> K D \<equiv> \<Gamma> \<Longrightarrow>\<^sub>A K * D"

lemma keep_drop_init:
  assumes
    "\<Gamma>  \<Longrightarrow>\<^sub>A K' * D'"
    "K' \<Longrightarrow>\<^sub>A K"
    "D' \<Longrightarrow>\<^sub>A D"
  shows
    "keep_drop \<Gamma> K D"
  unfolding keep_drop_def
  using assms(1) assms(2) assms(3) ent_star_mono ent_trans by blast

method keep_drop_simp = (simp only: star_aci)?; rule ent_refl

method keep_drop = 
  rule keep_drop_init, ((rule keep_drop_step)+; fail), keep_drop_simp, keep_drop_simp

lemma hnr_let[hnr_rule]:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 v" 
    "\<And>xi x. hnr (\<Gamma>\<^sub>1 x xi) (fi xi) (\<Gamma>' x xi) (f x)"
    "\<And>xi x ri r. keep_drop (\<Gamma>' x xi r ri) (\<Gamma>'' r ri) (\<Gamma>\<^sub>1' x xi r ri)"
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>'' (let x = v in f x)"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  apply sep_auto
  apply(sep_drule r: assms(3)[unfolded keep_drop_def])
  by sep_auto

lemma hnr_if: 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a a"
    "hnr \<Gamma> bi \<Gamma>\<^sub>b b"
  shows 
    "hnr 
      \<Gamma> 
      (if c then ai else bi) 
      (\<lambda>a r. \<Gamma>\<^sub>a a r \<or>\<^sub>A \<Gamma>\<^sub>b a r) 
      (if c then a else b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  by(sep_auto simp: ent_star_mono)

lemma hnr_if': 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a a"
    "hnr \<Gamma> bi \<Gamma>\<^sub>b b"
  shows 
    "hnr 
      \<Gamma> 
      (if c then ai else bi) 
      (\<lambda>a r. \<Gamma>\<^sub>a a r * \<up>c \<or>\<^sub>A \<Gamma>\<^sub>b a r * \<up>(\<not>c)) 
      (if c then a else b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  by(sep_auto simp: ent_star_mono)

lemma hnr_if''[hnr_rule]: 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a a"
    "hnr \<Gamma> bi \<Gamma>\<^sub>b b"
  shows 
    "hnr 
      \<Gamma> 
      (if c then ai else bi) 
      (\<lambda>a r. (\<up>c * \<Gamma>\<^sub>a a r  \<or>\<^sub>A \<up>(\<not>c) * \<Gamma>\<^sub>b a r) * emp) 
      (if c then a else b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  by(sep_auto simp: ent_star_mono)

lemma hnr_pass: "hnr (A x xi) (return xi) A x"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_copy: "hnr (id_assn x xi) (return xi) id_assn x"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_tuple: 
  assumes
    "hnr \<Gamma> (return ai) \<Gamma>\<^sub>a a"
    "hnr (\<Gamma>\<^sub>a a ai * true) (return bi) (\<Gamma>\<^sub>b a ai) b"
  shows 
    "hnr 
      \<Gamma>
      (return (ai, bi))
      (\<lambda>(a, b)(ai, bi). \<Gamma>\<^sub>b a ai b bi)
      (a, b)"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
    htriple_return_entails[of \<Gamma> ai "\<lambda>ai. \<Gamma>\<^sub>a a ai * true"] 
    htriple_return_entails[of "\<Gamma>\<^sub>a a ai * true" bi "\<lambda>bi. \<Gamma>\<^sub>b a ai b bi * true"]
    ent_trans[of \<Gamma>]
  by sep_auto

lemma merge_and_1: "a \<and>\<^sub>A a = a"
  by auto


lemma merge_and_2_3_1: "times_assn_raw (Rep_assn a) (Rep_assn (Abs_assn (\<lambda>h. h \<Turnstile> b \<and> h \<Turnstile> c))) h \<Longrightarrow> 
      times_assn_raw (Rep_assn a) (Rep_assn b) h \<and> times_assn_raw (Rep_assn a) (Rep_assn c) h"
  apply(induction "Rep_assn a" "Rep_assn (Abs_assn (\<lambda>h. h \<Turnstile> b \<and> h \<Turnstile> c))" h rule: times_assn_raw.induct)
  using inf_assn_def mod_and_dist by auto

lemma merge_and_2_3: "a * (b \<and>\<^sub>A c) \<Longrightarrow>\<^sub>A (a * b) \<and>\<^sub>A (a * c)"
  unfolding inf_assn_def times_assn_def entails_def
  apply auto
  by (metis ent_star_mono entails_def inf_assn_def mod_and_dist times_assn_def)

(*lemma merge_and_2_2_1: "h \<Turnstile> Abs_assn (times_assn_raw (Rep_assn a) (Rep_assn b)) \<and>
             h \<Turnstile> Abs_assn (times_assn_raw (Rep_assn a) (Rep_assn c)) 
  \<Longrightarrow> times_assn_raw (Rep_assn a) (Rep_assn (Abs_assn (\<lambda>h. h \<Turnstile> b \<and> h \<Turnstile> c))) h"
  apply(auto simp: Abs_assn_inverse)
  apply(induction "Rep_assn a" "Rep_assn b" h rule: times_assn_raw.induct)
  apply auto
  subgoal for h as1 as1a as2 as2a
    apply(subst exI[where x = as1])
     apply(subst exI[where x = "as2a"])
      apply auto
    sorry
  sorry

lemma merge_and_2_2: "(a * b) \<and>\<^sub>A (a * c) \<Longrightarrow>\<^sub>A a * (b \<and>\<^sub>A c)"
  unfolding inf_assn_def times_assn_def entails_def 
  apply auto
  using Abs_assn_inverse merge_and_2_2_1 by force

lemma merge_and_2: "(a * b) \<and>\<^sub>A (a * c) = a * (b \<and>\<^sub>A c)"
  unfolding inf_assn_def times_assn_def
  apply(auto simp: Abs_assn_inverse)
  sorry *)

lemma hnr_tuple_2[hnr_rule]:
  assumes
    "hnr \<Gamma> (return ai) \<Gamma>\<^sub>a a"
    "hnr \<Gamma> (return bi) \<Gamma>\<^sub>b b"
  shows 
    "hnr 
      \<Gamma>
      (return (ai, bi))
      (\<lambda>(a, b)(ai, bi). \<Gamma>\<^sub>a a ai * true \<and>\<^sub>A \<Gamma>\<^sub>b b bi * true)
      (a, b)"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  using htriple_return_and[of \<Gamma> ai "\<lambda>ai. \<Gamma>\<^sub>a a ai * true" bi "\<lambda>bi. \<Gamma>\<^sub>b b bi * true"] ent_true_drop(2)
  by sep_auto

lemma hnr_frame:
  assumes
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
    "hnr \<Gamma> fi \<Gamma>' f"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<lambda> r ri. \<Gamma>' r ri * F) f"
  apply(rule hnrI)
  by (smt (verit) assms(1) assms(2) assn_aci(10) fi_rule hnrD hoare_triple_def)

(* lemma merge_or: "a * x * b \<or>\<^sub>A c * x * d = x * (a * b \<or>\<^sub>A c * d)"
  by (simp add: star_aci(2) star_aci(3) star_or_dist2)

lemmas merge_ors = merge_or merge_or[of emp] *)

attribute_setup framed =
    \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn thm => @{thm hnr_frame} OF [asm_rl, thm]))\<close>
    \<open>Add frame to hnr rule\<close>

lemma frame_inference_trivial: "P \<Longrightarrow>\<^sub>A P * emp"
  by sep_auto

method frame_inference' = rule frame_inference_trivial | frame_inference

lemma move_pure_right: 
  "a * (b * c) = (a * b) * c" 
  "NO_MATCH (\<up>(x)) b \<Longrightarrow> \<up>(p) * b = b * \<up>(p)"
  "NO_MATCH (\<up>(x)) b \<Longrightarrow> a * \<up>(p) * b = a * b * \<up>(p)"
  by(auto simp: algebra_simps) 

lemma merge_ex: 
  "(\<exists>\<^sub>Aa _. P a) = (\<exists>\<^sub>Aa. P a)"
  "(\<exists>\<^sub>A_ a. P a) = (\<exists>\<^sub>Aa. P a)"
  by simp_all

lemma hnr_pre_cong: "\<Gamma> = \<Gamma>' \<Longrightarrow> hnr \<Gamma> c \<Gamma>'' a = hnr \<Gamma>' c \<Gamma>'' a"
  by simp

lemma hnr_pre_cong_or_1: "\<lbrakk>\<Gamma>\<^sub>a = \<Gamma>\<^sub>a'; \<Gamma>\<^sub>b = \<Gamma>\<^sub>b'\<rbrakk>
   \<Longrightarrow> hnr (\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) c \<Gamma>'' a = hnr (\<Gamma>\<^sub>a' \<or>\<^sub>A \<Gamma>\<^sub>b') c \<Gamma>'' a"
  by simp

lemma hnr_pre_cong_or_2: "\<lbrakk>\<Gamma>\<^sub>a = \<Gamma>\<^sub>a'; \<Gamma>\<^sub>b = \<Gamma>\<^sub>b'\<rbrakk>
   \<Longrightarrow> hnr ((\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) * \<Gamma>\<^sub>c)  c \<Gamma>'' a = hnr ((\<Gamma>\<^sub>a' \<or>\<^sub>A \<Gamma>\<^sub>b') * \<Gamma>\<^sub>c) c \<Gamma>'' a"
  by simp

lemmas hnr_pre_cong_or = hnr_pre_cong_or_1 hnr_pre_cong_or_2

lemma hnr_pre_cong_or_first_1: "\<lbrakk>\<Gamma>\<^sub>a = \<Gamma>\<^sub>a'\<rbrakk>
   \<Longrightarrow> hnr (\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) c \<Gamma>'' a = hnr (\<Gamma>\<^sub>a' \<or>\<^sub>A \<Gamma>\<^sub>b) c \<Gamma>'' a"
  by simp

lemma hnr_pre_cong_or_first_2: "\<lbrakk>\<Gamma>\<^sub>a = \<Gamma>\<^sub>a'\<rbrakk>
   \<Longrightarrow> hnr ((\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) * \<Gamma>\<^sub>c)  c \<Gamma>'' a = hnr ((\<Gamma>\<^sub>a' \<or>\<^sub>A \<Gamma>\<^sub>b) * \<Gamma>\<^sub>c) c \<Gamma>'' a"
  by simp

lemmas hnr_pre_cong_or_first = hnr_pre_cong_or_first_1 hnr_pre_cong_or_first_2

lemma hnr_extract_pure_1:
  assumes
    "p \<Longrightarrow> hnr \<Gamma> c \<Gamma>' a"
  shows 
    "hnr (\<Gamma> * \<up>(p)) c \<Gamma>' a"
  using assms 
  unfolding hnr_def
  apply(cases p) 
  by auto

lemma hnr_extract_pure_2:
  assumes
    "p \<Longrightarrow> hnr emp c \<Gamma>' a"
  shows 
    "hnr (\<up>(p)) c \<Gamma>' a"
  using assms 
  unfolding hnr_def
  apply(cases p) 
  by auto

lemma hnr_exE:
   assumes
   "\<And>x. hnr (P x) c (\<Gamma>' x) a"
  shows 
    "hnr (\<exists>\<^sub>Ax. P x) c (\<lambda>u v. \<exists>\<^sub>Ax. \<Gamma>' x u v) a"
  using assms
  unfolding hnr_def
  apply(sep_auto)
  apply(rule cons_post_rule)
   apply blast 
  by solve_entails

lemmas hnr_extract_pure = hnr_extract_pure_1 hnr_extract_pure_2 hnr_exE

lemma prepare_frame_1:
  assumes
    "emp * P * emp \<Longrightarrow>\<^sub>A emp * Q * F"
  shows
    "P \<Longrightarrow>\<^sub>A Q * F"
  using assms
  by sep_auto

lemma frame_no_match: 
  assumes
    "Ps1 * (P * Ps2) \<Longrightarrow>\<^sub>A Qs * Q * F"
  shows
    "Ps1 * P * Ps2 \<Longrightarrow>\<^sub>A Qs * Q * F"
  using assms
  by (simp add: mult.assoc)

lemma frame_match_pure:
  assumes
    "P"
    "Ps \<Longrightarrow>\<^sub>A Qs * F"
  shows
    "Ps \<Longrightarrow>\<^sub>A Qs * \<up>(P) * F"
  using assms
  by simp

lemma frame_match:
  assumes
    "Ps1 * Ps2 \<Longrightarrow>\<^sub>A Qs * F"
  shows
    "Ps1 * P * Ps2 \<Longrightarrow>\<^sub>A Qs * P * F"
  using assms
  by (metis assn_aci(10) fr_refl)

lemma frame_match_emp:
   assumes
    "Ps \<Longrightarrow>\<^sub>A Qs * F"
  shows
    "Ps \<Longrightarrow>\<^sub>A Qs * emp * F"
  using assms
  by sep_auto

lemma frame_done: "F * emp \<Longrightarrow>\<^sub>A emp * F" 
  by sep_auto

lemma ex_assn_move_in:
  "\<And>Q R. (\<exists>\<^sub>Ax. Q x * R) = (\<exists>\<^sub>Ax. Q x) * R"
  "\<And>Q R. (\<exists>\<^sub>Ax. Q * R x) = Q * (\<exists>\<^sub>Ax. R x)"
  "(\<exists>\<^sub>Ax. Q x * R x) = (\<exists>\<^sub>Ax. Q x) * (\<exists>\<^sub>Ax. R x)" 
   apply sep_auto
   apply sep_auto
  (* TODO Important: How to have rule just in one direction? *)
  sorry

lemma hnr_or_match_1:
  assumes
    "hnr ((As1 * As2 \<or>\<^sub>A Bs1 * Bs2) * (A * Cs)) fi \<Gamma>' f"
  shows
    "hnr ((As1 * A * As2 \<or>\<^sub>A Bs1 * A * Bs2) * Cs) fi \<Gamma>' f"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  by (metis star_aci(3) star_assoc star_or_dist2)

lemma hnr_or_match_2:
  assumes
    "hnr ((As1 * As2 \<or>\<^sub>A Bs1 * Bs2) * ((\<exists>\<^sub>A x. A x) * Cs)) fi \<Gamma>' f"
  shows
    "hnr ((As1 * (\<exists>\<^sub>A x. A x) * As2 \<or>\<^sub>A Bs1 * A x * Bs2) * Cs) fi \<Gamma>' f"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  by (smt (verit, ccfv_threshold) assn_aci(10) assn_times_comm cons_pre_rule ent_disjE ent_disjI1_direct ent_disjI2' fr_refl star_or_dist1 triv_exI)

lemma hnr_or_match_3:
  assumes
    "hnr ((As1 * As2 \<or>\<^sub>A Bs1 * Bs2) * ((\<exists>\<^sub>A x. A x) * Cs)) fi \<Gamma>' f"
  shows
    "hnr ((As1 * A x * As2 \<or>\<^sub>A Bs1 * (\<exists>\<^sub>A x. A x) * Bs2) * Cs) fi \<Gamma>' f"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  sorry
  (* TODO: 
  by (smt (verit, ccfv_SIG) SLN_right ac_operator.right_commute cons_pre_rule ent_disjE ent_disjI1_direct ent_disjI2_direct ent_frame_fwd ent_star_mono fr_refl keep_drop_2 mult.ac_operator_axioms triv_exI)
  *)

lemma hnr_or_match_4:
  assumes
    "hnr Cs fi \<Gamma>' f"
  shows
    "hnr ((\<up>c * emp \<or>\<^sub>A \<up>(\<not>c) * emp) * Cs) fi \<Gamma>' f"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  by simp

lemmas hnr_or_match = hnr_or_match_1 hnr_or_match_2 hnr_or_match_3 hnr_or_match_4

lemma hnr_or_prepare:
  assumes
    "hnr ((As * emp \<or>\<^sub>A Bs * emp) * Cs) fi \<Gamma>' f"
  shows
    "hnr ((As \<or>\<^sub>A Bs) * Cs) fi \<Gamma>' f"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  by simp

lemma hnr_or_no_match_1:
  assumes
    "hnr ((As1 * (A * As2) \<or>\<^sub>A Bs1 * B * Bs2) * Cs) fi \<Gamma>' f"
  shows
    "hnr ((As1 * A * As2 \<or>\<^sub>A Bs1 * B * Bs2) * Cs) fi \<Gamma>' f"
  apply(rule hnrI)
  using 
    assms[THEN hnrD]
  by (simp add: mult.left_assoc)

lemma id: "A = A"
  by simp

(* lemma frame_no_match: 
  assumes
    "Ps1 * (P * Ps2) \<Longrightarrow>\<^sub>A Qs * Q * F"
  shows
    "Ps1 * P * Ps2 \<Longrightarrow>\<^sub>A Qs * Q * F"
  using assms
  by (simp add: mult.assoc) *)

method normalize_hnr_pre = simp(no_asm) named_ss HOL_basic_ss_nomatch:
    move_pure_right assn_one_left mult_1_right[where 'a=assn] 
    merge_pure_star[symmetric] ex_assn_move_out pure_true
  cong: hnr_pre_cong

find_theorems "\<not>_" "(\<noteq>)"

method normalize_or_hnr_pre uses cong = simp(no_asm) named_ss HOL_basic_ss_nomatch:
    assn_one_left mult_1_right[where 'a=assn] (* TODO Name: *) move_pure_right(1)
    merge_pure_star[symmetric] ex_assn_move_in pure_true merge_ex
  cong: cong

method hnr_or_no_match = then_else 
  \<open>rule hnr_or_no_match_1\<close> 
  \<open>rule id\<close> 
  \<open>normalize_or_hnr_pre cong: hnr_pre_cong_or_first, rule hnr_or_prepare\<close>


lemma ex_or1: "(\<exists>\<^sub>Aa b. P a  \<or>\<^sub>A P b) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aa. P a)"
  by (simp add: ent_disjE ent_ex_preI)
 
lemma ex_or2: "(\<exists>\<^sub>Aa. P a) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aa b. P a  \<or>\<^sub>A P b)"
  by (meson ent_disjI1_direct ent_ex_postI ent_ex_preI)

lemma ex_or: "(\<exists>\<^sub>Aa b. P a  \<or>\<^sub>A P b) = (\<exists>\<^sub>Aa. P a)"
  apply(rule ent_iffI)
  using ex_or1 ex_or2 by auto

lemma ex_or_x: "(\<exists>\<^sub>Aa. P a \<or>\<^sub>A P b) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aa. P a)"
  by (simp add: ent_disjE ent_ex_preI)

(* 
lemma hnr_if: 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a a"
    "hnr \<Gamma> bi \<Gamma>\<^sub>b b"
  shows 
    "hnr 
      \<Gamma> 
      (if c then ai else bi) 
      (\<lambda>a r. \<Gamma>\<^sub>a a r * \<up> c \<or>\<^sub>A \<Gamma>\<^sub>b a r * \<up>(\<not>c)) 
      (if c then a else b)" 
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  by(sep_auto simp: ent_star_mono)*)

(* lemma merge_if_1:
  assumes 
    "c" 
    "hnr \<Gamma>\<^sub>a x \<Gamma> xi" 
  shows 
   "hnr (\<Gamma>\<^sub>a * \<up> c \<or>\<^sub>A \<Gamma>\<^sub>b * \<up>(\<not>c)) x \<Gamma> xi" 
  using assms
  by sep_auto

lemma merge_if_2:
  assumes 
    "\<not>c" 
    "hnr \<Gamma>\<^sub>b x \<Gamma> xi" 
   shows 
    "hnr (\<Gamma>\<^sub>a * \<up> c \<or>\<^sub>A \<Gamma>\<^sub>b * \<up>(\<not>c)) x  \<Gamma> xi"
  using assms
  by sep_auto

lemma merge_if_fallback:
  assumes 
    "hnr true x \<Gamma> xi" 
   shows 
    "hnr (\<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b) x  \<Gamma> xi"
  apply(rule hnrI)
  using assms[THEN hnrD]
  using cons_pre_rule ent_true by blast *)

(* Steps for merging: 
  1. Simply or [merge_or] and bring \<exists>. to the outside (if possible combine \<exists> already)
  2. Match real t with \<exists>. to \<exists>.
  3. Rest: c \<rightarrow> X * \<not>c \<rightarrow> Y (Does it work like this?)
*)



(* lemma merge_if_1:
  assumes 
    "hnr (\<exists>\<^sub>At'. master_assn t' * \<up>(t' \<turnstile> xs \<sim> xsi)) x \<Gamma> xi" 
   shows 
    "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi) \<or>\<^sub>A (\<exists>\<^sub>At'. master_assn t' * \<up>(t' \<turnstile> xs \<sim> xsi))) x  \<Gamma> xi"
  apply(rule hnrI)
  apply(rule split_rule)
  using cons_pre_rule assms[THEN hnrD] apply fastforce
  using assms[THEN hnrD] by simp

(* 
   hnr (master_assn t * \<up> (t \<turnstile> t1 \<sim> xia) * emp * \<up> True \<or>\<^sub>A
                (\<exists>\<^sub>At'.
                    master_assn t' *
                    \<up> ((\<forall>xs' xsi'. t \<turnstile> xs' \<sim> xsi' \<longrightarrow> t' \<turnstile> xs' \<sim> xsi') \<and> t' \<turnstile> t1 \<sim> xia)) *
                emp *
                \<up> (\<not> True))
*)

lemma merge_if_2:
  assumes 
    "hnr ((\<exists>\<^sub>At'. master_assn t' * \<up>(t' \<turnstile> xs \<sim> xsi))) x \<Gamma> xi" 
   shows 
    "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi) * emp \<or>\<^sub>A 
          (\<exists>\<^sub>At'. master_assn t' * \<up>(t' \<turnstile> xs \<sim> xsi))) x  \<Gamma> xi"
  apply(rule hnrI)
  apply(rule split_rule)
  using cons_pre_rule assms[THEN hnrD]
  apply fastforce
  using assms[THEN hnrD] cons_pre_rule by sep_auto

find_theorems "(\<Longrightarrow>\<^sub>A)" "\<exists>\<^sub>A _ . _"



lemma t: assumes "P" shows "P" using assms by simp

lemma wtf_1: "fold_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. fold_assn x" 
  by simp

lemma wtf_2: "master_assn t = master_assn t"
  by auto

lemma wtf_5: "master_assn t \<Longrightarrow>\<^sub>A master_assn t"
  by auto

lemma wtf_6: "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn t"
  by auto

lemma wtf_8: assumes "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  shows "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  using assms
  sorry

lemma wtf_7: "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  using triv_exI[of master_assn t]
  sorry

lemma merge_or_master_assn_1_1:
  assumes 
    "hnr (\<exists>\<^sub>At'. master_assn t') x \<Gamma> xi"
   shows 
    "hnr (master_assn t \<or>\<^sub>A (\<exists>\<^sub>At'. master_assn t')) x \<Gamma> xi"
  apply(rule hnrI)
  apply(rule split_rule)
  using cons_pre_rule[of "master_assn t" "\<exists>\<^sub>At'. master_assn t'" x  "(\<lambda>b. \<Gamma> xi b * true)"] assms[THEN hnrD] 
  using wtf_7[of t]
   apply blast
  using assms[THEN hnrD]
  apply blast
  sorry

lemma merge_or_master_assn_1:
  assumes 
    "hnr (\<exists>\<^sub>At'. master_assn t') x \<Gamma> xi"
   shows 
    "hnr (\<exists>\<^sub>At'. master_assn t \<or>\<^sub>A master_assn t') x  \<Gamma> xi"
  apply(rule hnrI)
  using assms[THEN hnrD]
  apply sep_auto
  sorry *)
  
method frame_norm_assoc = (simp only: mult.left_assoc[where 'a=assn])?

method frame_prepare = rule prepare_frame_1, frame_norm_assoc

method frame_try_match = then_else 
  \<open>rule frame_match_pure, assumption | rule frame_match frame_match_emp\<close> 
  \<open>frame_norm_assoc\<close> 
  \<open>rule frame_no_match, frame_try_match\<close>

method or_match = 
  (normalize_or_hnr_pre cong: hnr_pre_cong_or, rule hnr_or_prepare), 
  (rule hnr_or_match | hnr_or_no_match) 

method frame_done = simp only: assn_one_left mult_1_right[where 'a=assn], rule ent_refl  

method frame_inference_2 = frame_prepare, frame_try_match+, frame_done

method frame_inference_2_dbg = frame_prepare, (frame_try_match+)?, frame_done?

experiment
begin

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A a * c * ?F"
    apply frame_inference_2
  done

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A emp * ?F"
   apply frame_inference_2
  done

schematic_goal 
  fixes a b c d::assn
  shows "emp \<Longrightarrow>\<^sub>A emp * ?F"
   apply frame_inference_2
  done

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A b * d * ?F"
   apply frame_inference_2
  done

schematic_goal 
  shows "a * \<up>(b) * c * d \<Longrightarrow>\<^sub>A \<up>(b) * d * ?F"
   apply frame_inference_2
  done
end

method hnr_extract_pure methods post_processing = 
  normalize_hnr_pre?, ((rule hnr_extract_pure)+)?, post_processing?

method hnr_rule uses rule_set = 
  (rule rule_set[framed] hnr_copy[framed], frame_inference_2) | rule hnr_rule hnr_return

method hnr methods assumption_processing uses rule_set =
  (hnr_extract_pure assumption_processing, ((hnr_rule rule_set: rule_set) | keep_drop))+

end
