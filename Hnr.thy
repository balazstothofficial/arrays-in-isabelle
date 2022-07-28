theory Hnr 
  imports Base
begin                       

definition hnr where "hnr \<Gamma> c \<Gamma>' a = (
  case a of None \<Rightarrow> True | 
            Some a \<Rightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' a r>\<^sub>t
)"

lemma hnr_none [simp]: "hnr \<Gamma> c \<Gamma>' None"
  unfolding hnr_def
  by simp

lemma hnr_alt: "hnr \<Gamma> c \<Gamma>' a = (a \<noteq> None \<longrightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' (the a) r>\<^sub>t)"
  unfolding hnr_def
  by(auto split: option.splits)

lemmas hnrD = hnr_alt[THEN iffD1, rule_format]

lemma hnrI:
  assumes
    "\<And>x. a = Some x \<Longrightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' x r>\<^sub>t"
  shows "hnr \<Gamma> c \<Gamma>' a"
  using assms
  unfolding hnr_def
  by(auto split: option.splits)

definition id_rel where "id_rel a c \<equiv> c = a"

abbreviation id_assn where "id_assn a c \<equiv> \<up>(id_rel a c)"

abbreviation array_assn where "array_assn xs xsi \<equiv> xsi \<mapsto>\<^sub>a xs"

named_theorems hnr_rule

lemma hnr_return: "hnr \<Gamma> (return x) (\<lambda>r ri. \<Gamma> * id_assn r ri) (Some x)"
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

lemma keep_drop_2: 
  assumes
    "A \<Longrightarrow>\<^sub>A A'"
  shows
    "A \<Longrightarrow>\<^sub>A A' * emp"
  using assms
  by sep_auto

lemma keep_drop_3: "A \<Longrightarrow>\<^sub>A emp * A"
  by sep_auto

lemmas keep_drop_step = keep_drop_1 keep_drop_2 keep_drop_3

definition Keep_Drop where "Keep_Drop \<Gamma> K D \<equiv> \<Gamma> \<Longrightarrow>\<^sub>A K * D"

definition Keep_Drop_Simp where
  "Keep_Drop_Simp a b \<equiv> a \<Longrightarrow>\<^sub>A b"

lemma keep_drop_init:
  assumes
    "\<Gamma>  \<Longrightarrow>\<^sub>A K * D"
  shows
    "Keep_Drop \<Gamma> K D"
  unfolding Keep_Drop_def
  using assms(1) ent_star_mono ent_trans by blast

lemma keep_drop_simpI: "a \<Longrightarrow>\<^sub>A b \<Longrightarrow> Keep_Drop_Simp a b"
  unfolding Keep_Drop_Simp_def
  by simp

method keep_drop_simp = rule keep_drop_simpI, (simp only: star_aci)?; rule ent_refl

method keep_drop_step methods keep_atom = 
  rule keep_drop_1 | (rule keep_drop_2, keep_atom) | rule keep_drop_3

method keep_drop methods keep_atom = 
  rule keep_drop_init, ((keep_drop_step keep_atom)+; fail)

lemma hnr_bind[hnr_rule]:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 v" 
    "\<And>xi x. hnr (\<Gamma>\<^sub>1 x xi) (fi xi) (\<Gamma>' x xi) (f x)"
    "\<And>xi x ri r. Keep_Drop (\<Gamma>' x xi r ri) (\<Gamma>'' r ri) (\<Gamma>\<^sub>1' x xi r ri)"
    "\<And>r ri. Keep_Drop_Simp (\<Gamma>'' r ri) (\<Gamma>''' r ri)" 
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>''' (do { x \<leftarrow> v; f x })"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  apply(sep_auto split: option.splits Option.bind_splits)
  apply(sep_drule r: assms(3)[unfolded Keep_Drop_def])
  apply(sep_drule r: assms(4)[unfolded Keep_Drop_Simp_def])
  by sep_auto

(* Versteh ich noch nicht 100%: *)
(* lemma hnr_let[hnr_rule]:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 v" 
    "\<And>xi x. hnr (\<Gamma>\<^sub>1 x xi) (fi xi) (\<Gamma>' x xi) (f x)"
    "\<And>xi x ri r. Keep_Drop (\<Gamma>' x xi r ri) (\<Gamma>'' r ri) (\<Gamma>\<^sub>1' x xi r ri)"
    "\<And>r ri. Keep_Drop_Simp (\<Gamma>'' r ri) (\<Gamma>''' r ri)" 
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>''' (let x = v in f x)"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  apply sep_auto
  apply(sep_drule r: assms(3)[unfolded Keep_Drop_def])
  apply(sep_drule r: assms(4)[unfolded Keep_Drop_Simp_def])
  by sep_auto *)

lemma let_to_bind: "(let x = v in f x) = (do { x \<leftarrow> return v; f x }) "
  by simp

lemma let_to_bind': "(let x = v in f x) = (do { x \<leftarrow> Some v; f x }) "
  by simp

definition Merge where
  "Merge a b c \<equiv> a \<or>\<^sub>A b \<Longrightarrow>\<^sub>A c"

lemma hnr_if [hnr_rule]: 
  assumes
    "hnr (\<Gamma> * id_assn c ci) ai \<Gamma>\<^sub>a a"
    "hnr (\<Gamma> * id_assn c ci) bi \<Gamma>\<^sub>b b"
    "\<And>a r. Merge (\<Gamma>\<^sub>a a r) (\<Gamma>\<^sub>b a r) (\<Gamma>\<^sub>c a r)"
  shows 
    "hnr 
      (\<Gamma> * id_assn c ci)
      (if ci then ai else bi) 
      \<Gamma>\<^sub>c 
      (if c then a else b)" 
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  using assms(3)
  unfolding Merge_def
  apply(sep_auto simp: ent_star_mono id_rel_def)
  apply (smt (verit, del_insts) SLN_def SLN_right \<open>a \<noteq> None \<Longrightarrow> <\<Gamma> * id_assn c ci> ai <\<Gamma>\<^sub>a (the a)>\<^sub>t\<close> cons_post_rule ent_disjI1 fr_refl id_rel_def option.distinct(1) option.sel pure_true)
  apply sep_auto
  by (smt (verit) SLN_def SLN_right \<open>b \<noteq> None \<Longrightarrow> <\<Gamma> * id_assn c ci> bi <\<Gamma>\<^sub>b (the b)>\<^sub>t\<close> cons_post_rule ent_disjI2 fr_refl id_rel_def option.distinct(1) option.sel pure_true)


lemma hnr_case_nat[hnr_rule]:
  assumes 
    "hnr (\<Gamma> * id_assn n  ni) ci0 \<Gamma>\<^sub>a c0"
    "\<And>n' ni'. hnr (\<Gamma> * id_assn n ni * id_assn n' ni') (ci ni') (\<Gamma>\<^sub>b n' ni') (c n')"
    "\<And>n ni ri r. Keep_Drop (\<Gamma>\<^sub>b n ni r ri) (\<Gamma>\<^sub>b' r ri) (\<Gamma>Drop n ni r ri)"
    "\<And>r ri. Keep_Drop_Simp (\<Gamma>\<^sub>b' r ri) (\<Gamma>\<^sub>b'' r ri)" 
    "\<And>r ri. Merge (\<Gamma>\<^sub>a r ri) (\<Gamma>\<^sub>b'' r ri) (\<Gamma>\<^sub>c r ri)"
  shows
    "hnr (\<Gamma> * id_assn n ni)
         (case ni of 0 \<Rightarrow> ci0 | Suc n' \<Rightarrow> ci n') \<Gamma>\<^sub>c (case n of 0 \<Rightarrow> c0 | Suc n' \<Rightarrow> c n')"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  using assms(5)
  unfolding Merge_def
  apply(sep_auto simp: id_rel_def split: nat.splits) 
  apply(rule cons_post_rule)
  apply(rule fi_rule)
     apply(rule sep_heap_rules)
  apply simp
    apply(sep_auto simp: id_rel_def)+
  using ent_disjI1 fr_refl apply blast

  apply(rule cons_post_rule)
  apply(rule fi_rule)
     apply(rule sep_heap_rules)
  apply simp
    apply(sep_auto simp: id_rel_def)+
  using assms(3, 4) 
  unfolding Keep_Drop_def Keep_Drop_Simp_def
  apply -
  subgoal premises prems
    apply(sep_drule r: prems(5))
    apply(sep_drule r: prems(6))
    using ent_disjI2 ent_true_drop(1) ent_true_drop(2) prems(1) by blast
  done

lemma hnr_case_list[hnr_rule]:
  assumes 
    "hnr \<Gamma> ci0 \<Gamma>\<^sub>a c0"
    "\<And>x xs. hnr \<Gamma> (ci x xs) \<Gamma>\<^sub>b (c x xs)"
    "\<And>a r. Merge (\<Gamma>\<^sub>a a r) (\<Gamma>\<^sub>b a r) (\<Gamma>\<^sub>c a r)"
  shows
    "hnr \<Gamma> (case xs of [] \<Rightarrow> ci0 | x#xs \<Rightarrow> ci x xs) \<Gamma>\<^sub>c (case xs of [] \<Rightarrow> c0 | x#xs \<Rightarrow> c x xs)"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  using assms(3)
  unfolding Merge_def
  apply(sep_auto split: list.splits) 
  using ent_disjI1 fr_refl apply blast
  apply sep_auto
  using ent_disjI2 fr_refl by blast

lemma hnr_pass: "hnr (A x xi) (return xi) A (Some x)"
  apply(rule hnrI)
  by sep_auto

lemma hnr_copy: "hnr (id_assn x xi) (return xi) id_assn (Some x)"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto


(*
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
  by sep_auto *)

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
   using 
    assms[THEN hnrD]
   by sep_auto

(* Is sth like this possible? 
lemma hnr_case_1: 
  assumes "\<And>x1i x1. hnr \<Gamma> (ci x1i) \<Gamma>' (c x1)"
  shows "hnr \<Gamma> (case xi of x1i \<Rightarrow> ci x1i) \<Gamma>' (case x of x1 \<Rightarrow> c x1)"
  using assms
  by auto

lemma hnr_case_2: 
  assumes "\<And>x1i x1. hnr \<Gamma> (c1i x1i) \<Gamma>' (c1 x1)"
          "\<And>x2i x2. hnr \<Gamma> (c2i x2i) \<Gamma>' (c2 x2)"
  shows "hnr 
            \<Gamma> 
            (case xi of x1i \<Rightarrow> c1i x1i 
                      | x2i \<Rightarrow> c2i x2i) 
            \<Gamma>' 
            (case x of x1 \<Rightarrow> c1 x1 
                     | x2 \<Rightarrow> c2 x2)"
  using assms
  by auto

*)

(* TODO: Cases *)
lemma hnr_case_tuple:
  assumes 
    "\<And>a ai b bi. hnr \<Gamma> (ci ai bi) \<Gamma>' (c a b)"
  shows
    "hnr \<Gamma> (case xi of (ai, bi) \<Rightarrow> ci ai bi) \<Gamma>' (case x of (a, b) \<Rightarrow> c a b)"
  apply(rule hnrI)
  using assms[THEN hnrD]
  apply(sep_auto simp: split_beta)
  by fastforce

(* 
  lemma case_prod_rule: 
  "(\<And>a b. x = (a, b) \<Longrightarrow> <P> f a b <Q>) \<Longrightarrow> <P> case x of (a, b) \<Rightarrow> f a b <Q>"
  by (auto split: prod.split)

lemma case_list_rule:
  "\<lbrakk> l=[] \<Longrightarrow> <P> fn <Q>; \<And>x xs. l=x#xs \<Longrightarrow> <P> fc x xs <Q> \<rbrakk> \<Longrightarrow> 
  <P> case_list fn fc l <Q>"
  by (auto split: list.split)

lemma case_option_rule:
  "\<lbrakk> v=None \<Longrightarrow> <P> fn <Q>; \<And>x. v=Some x \<Longrightarrow> <P> fs x <Q> \<rbrakk> 
  \<Longrightarrow> <P> case_option fn fs v <Q>"
  by (auto split: option.split)

lemma case_sum_rule:
  "\<lbrakk> \<And>x. v=Inl x \<Longrightarrow> <P> fl x <Q>; 
     \<And>x. v=Inr x \<Longrightarrow> <P> fr x <Q> \<rbrakk> 
  \<Longrightarrow> <P> case_sum fl fr v <Q>"
  by (auto split: sum.split)

lemma let_rule: "(\<And>x. x = t \<Longrightarrow> <P> f x <Q>) \<Longrightarrow> <P> Let t f <Q>"
  by (auto)
*)


(* TODO: Automate *)
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

lemma hnr_frame:
  assumes
    "hnr \<Gamma> fi \<Gamma>' f"
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<lambda> r ri. \<Gamma>' r ri * F) f"
  apply(rule hnrI)
  apply(cases f)
   apply force
  apply simp
  using hnrD[OF assms(1)]
  apply simp
  by (smt (verit) assms(2) assn_aci(10) fi_rule hnrD hoare_triple_def)

attribute_setup framed =
    \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn thm => @{thm hnr_frame} OF [thm, asm_rl]))\<close>
    \<open>Add frame to hnr rule\<close>

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

lemma split_id_assn: "id_assn p pi = id_assn (fst p) (fst pi) * id_assn (snd p) (snd pi)"
  by(cases p)(auto simp: id_rel_def)

method frame_norm_assoc = (simp only: mult.left_assoc[where 'a=assn] split_id_assn)?

method frame_prepare = rule prepare_frame_1, frame_norm_assoc

method frame_try_match methods match_atom = then_else 
  \<open>rule frame_match_pure | rule frame_match, (match_atom; fail) | rule frame_match_emp\<close> 
  \<open>frame_norm_assoc\<close> 
  \<open>rule frame_no_match, frame_try_match match_atom\<close>

method frame_done = simp only: assn_one_left mult_1_right[where 'a=assn], rule ent_refl  

method frame_inference_2 methods match_atom =
  frame_prepare, (frame_try_match match_atom)+, frame_done

method frame_inference_2_dbg methods match_atom = 
  frame_prepare, ((frame_try_match match_atom)+)?, frame_done?

experiment
begin

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A a * c * ?F"
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  done

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A emp * ?F"
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  done

schematic_goal 
  fixes a b c d::assn
  shows "emp \<Longrightarrow>\<^sub>A emp * ?F"
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  done

schematic_goal 
  fixes a b c d::assn
  shows "a * b * c * d \<Longrightarrow>\<^sub>A b * d * ?F"
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  done

schematic_goal 
  shows "a * \<up>(b) * c * d \<Longrightarrow>\<^sub>A \<up>(b) * d * ?F"
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  done

schematic_goal 
  shows "id_assn (fst p) (fst pi) * id_assn (snd p) (snd pi) \<Longrightarrow>\<^sub>A id_assn p pi * ?F"
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  done

end

lemma merge_refl: "Merge a a a"
  unfolding Merge_def
  by simp

method merge = (simp only: star_aci)?, rule merge_refl

method hnr_rule methods frame_match_atom uses rule_set = 
  (rule rule_set[framed] hnr_copy[framed], frame_inference_2 frame_match_atom) 
 | rule hnr_rule hnr_return

method hnr_step methods frame_match_atom keep_atom uses rule_set =
   (simp only: let_to_bind')?, 
   (hnr_rule frame_match_atom rule_set: rule_set) | keep_drop keep_atom | keep_drop_simp | merge

(* TODO: How to avoid back tracking? *)
method hnr methods frame_match_atom keep_atom uses rule_set =
  (hnr_step frame_match_atom keep_atom rule_set: rule_set)+

thm hnr_rule hnr_return
  
end
