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

definition test3 where
  "test3 xs = 
    (let c1 = 1; t1 = xs[c1 := c1]; t2 = xs ! c1 in t1)"

definition test4 where
  "test4 xs =
    (let c1 = 1; t1 = if xs = [] then xs else let t2 = xs[c1 := c1] in t2 in t1)"

definition test4_2 where
  "test4_2 xs =
    (let c1 = 1; t1 = if xs = [] then xs else let t1 = xs[c1 := c1]; t2 = t1[c1:= c1] in t2 in t1)"

(* TODO: What to do if the bool depends on local variables? *)
definition test5 where
  "test5 xs = 
    (let c1 = 1; t1 = if c1 = 0 then xs else xs[c1 := c1] in t1)"

definition test6 where
  "test6 xs = 
    (let c1 = 1; c2 = 2; t1 = if xs = [] then xs[c2 := c2] else xs[c1 := c1] in t1)"

definition test7 where
  "test7 xs = 
    (let c1 = 1; c2 = 2; t1 = if xs = [] then let t2 = xs[c2 := c2]; t3 = xs[c1 := c1] in t3 else let t2 = xs[c1 := c1]; t3 = xs[c2 := c1] in t3 in t1)"

attribute_setup framed =
    \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn thm => @{thm hnr_frame} OF [asm_rl, thm]))\<close>
    \<open>Add frame to hnr rule\<close>

thm hnr_rule_arr[framed]

lemma frame_inference_trivial: "P \<Longrightarrow>\<^sub>A P * emp"
  by sep_auto

method frame_inference' = rule frame_inference_trivial | frame_inference

lemma move_pure_right: 
  "a * (b * c) = (a * b) * c" 
  "NO_MATCH (\<up>(x)) b \<Longrightarrow> \<up>(p) * b = b * \<up>(p)"
  "NO_MATCH (\<up>(x)) b \<Longrightarrow> a * \<up>(p) * b = a * b * \<up>(p)"
  by(auto simp: algebra_simps)  

lemma hnr_pre_cong: "\<Gamma> = \<Gamma>' \<Longrightarrow> hnr \<Gamma> c \<Gamma>'' a = hnr \<Gamma>' c \<Gamma>'' a"
  by simp

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

lemma transfer_diff_arr_rel:
  assumes 
    "t \<turnstile> xs \<sim> xsi" 
    "\<forall>xs xsi. t \<turnstile> xs \<sim> xsi \<longrightarrow> t' \<turnstile> xs \<sim> xsi"
  shows 
    "t' \<turnstile> xs \<sim> xsi"
  using assms by blast

method normalize_hnr_pre = simp(no_asm) named_ss HOL_basic_ss_nomatch:
    move_pure_right assn_one_left mult_1_right[where 'a=assn] 
    merge_pure_star[symmetric] ex_assn_move_out pure_true
  cong: hnr_pre_cong

lemma ex_or1: "(\<exists>\<^sub>Aa b. P a  \<or>\<^sub>A P b) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aa. P a)"
  by (simp add: ent_disjE ent_ex_preI)
 
lemma ex_or2: "(\<exists>\<^sub>Aa. P a) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aa b. P a  \<or>\<^sub>A P b)"
  by (meson ent_disjI1_direct ent_ex_postI ent_ex_preI)

lemma ex_or: "(\<exists>\<^sub>Aa b. P a  \<or>\<^sub>A P b) = (\<exists>\<^sub>Aa. P a)"
  apply(rule ent_iffI)
  using ex_or1 ex_or2 by auto

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

lemma merge_if_1:
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



lemma wtf_3: "(master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x) \<Longrightarrow> (master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x)" 
  try0
  sorry

lemma wtf_2: assumes "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  shows "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x"
  using assms
  apply auto
  sorry

lemma wtf_1: "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x" 
  using triv_exI[of master_assn t]
  sorry

lemma wtf: "master_assn t \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. master_assn x" 
  using triv_exI[of master_assn t]
  sorry



lemma merge_or_master_assn_1_1:
  assumes 
    "hnr (\<exists>\<^sub>At'. master_assn t') x \<Gamma> xi"
   shows 
    "hnr (master_assn t \<or>\<^sub>A (\<exists>\<^sub>At'. master_assn t')) x \<Gamma> xi"
  apply(rule hnrI)
  apply(rule split_rule)
  using wtf cons_pre_rule[of "master_assn t" "\<exists>\<^sub>At'. master_assn t'" x  "(\<lambda>b. \<Gamma> xi b * true)"] assms[THEN hnrD] 
  apply sep_auto
  sorry

lemma merge_or_master_assn_1:
  assumes 
    "hnr (\<exists>\<^sub>At'. master_assn t') x \<Gamma> xi"
   shows 
    "hnr (\<exists>\<^sub>At'. master_assn t \<or>\<^sub>A master_assn t') x  \<Gamma> xi"
  apply(rule hnrI)
  using assms[THEN hnrD]
  apply sep_auto
  sorry
  
method hnr_transfer_diff_arr_rel = 
  ((drule(1) transfer_diff_arr_rel)+)?, (thin_tac "\<forall>xs' xsi'. _ \<turnstile> xs' \<sim> xsi' \<longrightarrow> _ \<turnstile> xs' \<sim> xsi'")

method hnr_extract_pure = 
  normalize_hnr_pre?, ((rule hnr_extract_pure)+)?, hnr_transfer_diff_arr_rel?

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
  (rule hnr_rule_arr[framed] hnr_copy[framed], frame_inference_2) | rule hnr_rule_raw hnr_return

method hnr_rule_diff_arr =
  (rule hnr_rule_diff_arr[framed] hnr_copy[framed], frame_inference_2) | rule hnr_rule_raw hnr_return

method hnr_arr = (hnr_extract_pure, (hnr_rule | keep_drop))+

method hnr_diff_arr = (hnr_extract_pure, (hnr_rule_diff_arr | keep_drop))+

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

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test1 xs)"
  unfolding test1_def 
  apply hnr_arr
  done

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test2 xs)"
  unfolding test2_def 
  apply hnr_arr
  done  

(* Can't work, not linear! *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test3 xs)"
  unfolding test3_def 
  apply hnr_arr
  sorry

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test1 xs)"
  unfolding test1_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test2 xs)"
  unfolding test2_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test3 xs)"
  unfolding test3_def
  apply hnr_diff_arr
  done  

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test4 xs)"
  unfolding test4_def
  apply hnr_diff_arr
     apply (rule hnr_if)
      apply hnr_diff_arr
    apply(rule merge_if_2)
    apply hnr_diff_arr
  done

lemma cool_rule: "(\<exists>\<^sub>A x y. P x) = (\<exists>\<^sub>A x. P x)"
  by simp

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test4_2 xs)"
  unfolding test4_2_def
  apply hnr_diff_arr
     apply (rule hnr_if)
      apply hnr_diff_arr
  apply simp
    apply(rule merge_if_2)
    apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test7 xs)"
  unfolding test7_def
  apply hnr_diff_arr
     apply (rule hnr_if)
       apply hnr_diff_arr
     apply sep_auto
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  sorry

(* 
  Questions/Notes: 
  - Wouldn't it be more useful to always build up the master_assn instead of using existensials?
  - How to integrate standard operations like + and -?
  - transfer diff_arr_rel not directly in if for example
  - use simp for more than one existensial
*)


export_code array_nth_safe array_update_safe in SML_imp

end
