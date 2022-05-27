theory Test
  imports Diff_Arr HNR "HOL-Library.Code_Target_Nat" 
begin

(* Diff Array *)

definition create_diff_arr where
  "create_diff_arr n x = do {
    a \<leftarrow> Array.new n x;
    Diff_Arr.from_array a
  }"

definition test where "test = do {
  r \<leftarrow> create_diff_arr 3 (5::nat);
  y  \<leftarrow> Diff_Arr.update r 1 (7::nat);
  y' \<leftarrow> Diff_Arr.update r 1 (8::nat);
  x \<leftarrow> Diff_Arr.lookup y 1;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

(* Hnr *)

value "(xs[1 := 2], xs[1 := 3])"

definition test1 where
  "test1 xs = 
    (let c1 = (let x = 1 in x); c2 = 2; c3 = 3; t1 = xs[c1 := c2]; t2 = t1[c1 := c3]; t3 = t2 ! c2 in t3)"

definition test2 where
  "test2 xs = 
    (let c1 = 1; t1 = xs[c1 := c1] in t1)"

attribute_setup framed =
    \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn thm => @{thm hnr_frame} OF [asm_rl, thm]))\<close>
    \<open>Add frame to hnr rule\<close>

thm hnr_rule[framed]

lemma frame_inference_trivial: "P \<Longrightarrow>\<^sub>A P * emp"
  by sep_auto

method frame_inference' = rule frame_inference_trivial | frame_inference

lemma move_pure_right: 
  "a * (b * c) = (a * b) * c" 
  "NO_MATCH (\<up>(x)) b \<Longrightarrow> \<up>(p) * b = b * \<up>(p)"
  "NO_MATCH (\<up>(x)) b \<Longrightarrow> a * \<up>(p) * b = a * b * \<up>(p)"
  by(auto simp: algebra_simps)  

lemma hnr_pre_cong: "\<Gamma> = \<Gamma>' \<Longrightarrow> hnr \<Gamma> c \<Gamma>'' R a = hnr \<Gamma>' c \<Gamma>'' R a"
  by simp

lemma hnr_extract_pure_1:
  assumes
    "p \<Longrightarrow> hnr \<Gamma> c \<Gamma>' R a"
  shows 
    "hnr (\<Gamma> * \<up>(p)) c \<Gamma>' R a"
  using assms 
  unfolding hnr_def
  apply(cases p) 
  by auto

lemma hnr_extract_pure_2:
  assumes
    "p \<Longrightarrow> hnr emp c \<Gamma>' R a"
  shows 
    "hnr (\<up>(p)) c \<Gamma>' R a"
  using assms 
  unfolding hnr_def
  apply(cases p) 
  by auto

lemma hnr_exE:
   assumes
   "\<And>x. hnr (P x) c (\<Gamma>' x) (R x) a"
  shows 
    "hnr (\<exists>\<^sub>Ax. P x) c (\<exists>\<^sub>Ax. \<Gamma>' x) (\<lambda>u v. \<exists>\<^sub>Ax. R x u v) a"
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

find_theorems "\<up>(True)"

method normalize_hnr_pre = simp(no_asm) named_ss HOL_basic_ss_nomatch:
  move_pure_right assn_one_left mult_1_right[where 'a=assn] merge_pure_star[symmetric] ex_assn_move_out pure_true
  cong: hnr_pre_cong

method hnr_extract_pure = normalize_hnr_pre?, ((rule hnr_extract_pure)+)?

method frame_norm_assoc = (simp only: mult.left_assoc[where 'a=assn])?

method frame_prepare = rule prepare_frame_1, frame_norm_assoc

method frame_try_match = then_else 
  \<open>rule frame_match_pure, assumption | rule frame_match frame_match_emp\<close> 
  \<open>frame_norm_assoc\<close> 
  \<open>rule frame_no_match, frame_try_match\<close>

method frame_done = simp only: assn_one_left mult_1_right[where 'a=assn], rule ent_refl  

method frame_inference_2 = frame_prepare, frame_try_match+, frame_done

method frame_inference_2_dbg = frame_prepare, (frame_try_match+)?, frame_done?

method hnr_rule = 
  (rule hnr_rule[framed] hnr_copy[framed] hnr_return[framed], (frame_inference'; fail))

thm  hnr_return[of emp, framed]

method hnr_rule_diff_arr =
  (rule hnr_rule_diff_arr[framed] hnr_copy[framed], frame_inference_2) | rule hnr_rule_raw hnr_return

method hnr = (hnr_rule | keep_drop)+

method hnr_diff_arr = (hnr_rule_diff_arr | keep_drop)+

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
   unfolding test1_def
   by hnr

(* lemma norm_pre_ex_rule:
  assumes A: "\<And>x. <P x> f <Q>"
  shows "<\<exists>\<^sub>Ax. P x> f <Q>" 
*)

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


(*method frame_inference_init_2 = ((rule hnr_extract_pure move_pure_right)+)? 
method frame_inference_match_2 = ((rule hnr_pre_cong ent_refl)+)?

method frame_inference_2 = frame_inference_init_2, frame_inference_match_2

method hnr_rule_diff_arr_2 =
  (rule hnr_rule_diff_arr[framed] hnr_copy[framed] hnr_return[framed], (frame_inference_2))*)

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  unfolding test1_def 
  by hnr
 
schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  unfolding test1_def
  apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))+

  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' ?R (test2 xs)"
  unfolding test2_def
  apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))+
  done
    apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
   apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
     apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
   apply(hnr_extract_pure)
    apply(hnr_rule_diff_arr)
    supply[[unify_trace_failure]]
  supply[[show_main_goal]]
  apply(rule hnr_return)
  done

  thm hnr_let[framed]
  apply (hnr_rule_diff_arr)
   apply(hnr_extract_pure)
    apply (hnr_rule_diff_arr)
   apply(hnr_extract_pure)
      apply (hnr_rule_diff_arr) 
   apply(hnr_extract_pure)
     apply (hnr_rule_diff_arr)
  apply(hnr_extract_pure)
    apply keep_drop
  apply(hnr_extract_pure)
   apply(hnr_rule_diff_arr)
  apply(hnr_extract_pure)
     apply(hnr_rule_diff_arr)
  apply(hnr_extract_pure)
    apply(hnr_rule_diff_arr)
  apply(hnr_extract_pure)
      apply(hnr_rule_diff_arr)
    apply(hnr_extract_pure)
     apply(hnr_rule_diff_arr)
    apply(hnr_extract_pure)
       apply(hnr_rule_diff_arr)
    apply(hnr_extract_pure)
      apply(hnr_rule_diff_arr)
        apply(hnr_extract_pure)
        apply (rule hnr_rule_diff_arr[framed] hnr_copy[framed])
  apply(frame_inference_2)
        apply((hnr_rule_diff_arr | keep_drop))
     
  apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
         apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
        apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
       apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
      apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
     apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
    apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
apply(hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))
  done
  back
     apply frame_prepare
  apply frame_try_match
     apply(hnr_rule_diff_arr, frame_inference_2)
 apply(hnr_rule_diff_arr, frame_inference_2)
 apply(hnr_rule_diff_arr, frame_inference_2)
  apply(hnr_rule_diff_arr, frame_inference_2)
 apply(hnr_rule_diff_arr, frame_inference_2_dbg)
       apply(rule hnr_rule_diff_arr[framed])
  apply normalize_hnr_pre
        apply frame_inference_2
   find_theorems "<\<exists>\<^sub>A _. _> _ <_>"
       apply(simp only: ex_assn_move_out, intro hnr_exE)

       apply hnr_rule_diff_arr
         apply(rule hnr_rule_diff_arr[framed])
    apply FI_keep
   sorry

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test2 xs)"
  unfolding test2_def 
  apply hnr
     apply(rule hnr_rule[framed])
  apply frame_inference
  sorry

export_code array_nth_safe array_update_safe in SML_imp

end
