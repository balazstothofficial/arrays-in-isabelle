theory Hnr_Recursion
  imports Hnr_Base Hnr_Frame Norm
begin

lemma [simp]: "flat_lub b {} = b"
  by (simp add: flat_lub_def)

lemma [simp]: "fun_lub lub {} = (\<lambda>_. lub {})"
  by (simp add: fun_lub_def)

lemma admissible_fun:
    fixes le:: "'a \<Rightarrow> 'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
    assumes adm: "\<And>x. ccpo.admissible lub le (Q x)"
    shows "ccpo.admissible  (fun_lub lub) (fun_ord le) (\<lambda>f. \<forall>x. Q x (f x))"
  proof (rule ccpo.admissibleI)
    fix A :: "('b \<Rightarrow> 'a) set"
    assume Q: "\<forall>f\<in>A. \<forall>x. Q x (f x)"
    assume ch: "Complete_Partial_Order.chain (fun_ord le) A"
    assume "A \<noteq> {}"
    hence non_empty: "\<And>a. {y. \<exists>f\<in>A. y = f a} \<noteq> {}" by auto
    show "\<forall>x. Q x (fun_lub lub A x)"
      unfolding fun_lub_def
      by (rule allI, rule ccpo.admissibleD[OF adm chain_fun[OF ch] non_empty])
        (auto simp: Q)
  qed

lemma admissible_flat: "ccpo.admissible (flat_lub b) (flat_ord b) (P)"
  apply (rule ccpo.admissibleI)
  by (metis all_not_in_conv flat_interpretation flat_lub_in_chain flat_ord_def partial_function_definitions.lub_upper)


lemma hnr_recursion:
  assumes 
    mono_option: "\<And>x. mono_option (\<lambda>r. f r x)"
  and
    step: "\<And>r ri x xi F. (\<And>x' xi' F'. hnr (\<Gamma> F' x' xi') (ri xi') (\<Gamma>' F' x' xi') (r x'))
        \<Longrightarrow> hnr (\<Gamma> F x xi) (fi ri xi) (\<Gamma>' F x xi) (f r x)"
  and
    mono_heap: "\<And>x. mono_Heap (\<lambda>r. fi r x)"
  shows  
    "hnr (\<Gamma> F x xi) (heap.fixp_fun fi xi) (\<Gamma>' F x xi) (option.fixp_fun f x)"
proof(induction arbitrary: x xi F rule: ccpo.fixp_induct[OF option.ccpo])
  case 1
  then show ?case 
    apply(rule admissible_fun)
    by(rule admissible_flat)
next
  case 2
  then show ?case 
    using mono_option 
    by(simp add: monotone_def fun_ord_def)
next
  case 3
  then show ?case 
    by simp
next
  case 4
  then show ?case 
    apply(subst heap.mono_body_fixp[OF mono_heap])
    apply(rule step).
qed

lemma hnr_recursion':
  assumes 
    mono_option: "\<And>x. mono_option (\<lambda>r. f r x)"
  and
    step: "\<And>r ri x xi F. (\<And>x' xi' F'. hnr (\<Gamma> F' x' xi') (ri xi') (\<Gamma>' F' x' xi') (r x'))
        \<Longrightarrow> hnr (\<Gamma> F x xi) (fi ri xi) (\<Gamma>'' F x xi) (f r x)"
  and
    impl: "\<And>F x xi r ri. Norm (\<Gamma>'' F x xi r ri) (\<Gamma>' F x xi r ri)"
  and
    mono_heap: "\<And>x. mono_Heap (\<lambda>r. fi r x)"
  shows  
    "hnr (\<Gamma> F x xi) (heap.fixp_fun fi xi) (\<Gamma>' F x xi) (option.fixp_fun f x)"
  apply(rule hnr_recursion[OF mono_option _ mono_heap])
  apply(rule hnr_post_cons)
  apply(rule step, assumption)
  by(rule impl[unfolded Norm_def])

lemma tuple_selector_refl: "fst (a, b) = fst (a, b)" "snd (a, b) = snd (a, b)"
  by simp_all

(* TODO: Test thoroughly *)
method hnr_recursion 
  for \<Gamma>::"'F \<Rightarrow> 'x \<Rightarrow> 'xi \<Rightarrow> assn" and  \<Gamma>'::"'F \<Rightarrow> 'x \<Rightarrow> 'xi \<Rightarrow> 'r \<Rightarrow> 'ri \<Rightarrow> assn"
  methods frame_match_atom = 
  rule hnr_recursion'[where \<Gamma>=\<Gamma> and \<Gamma>'=\<Gamma>', framed],
  ((subst tuple_selector_refl, simp only: fst_conv snd_conv)+)?,
  hnr_frame_inference frame_match_atom

method_setup partial_function_mono_setup = 
  \<open>Scan.succeed (SIMPLE_METHOD' o Partial_Function.mono_tac)\<close>

method partial_function_mono = partial_function_mono_setup; fail

method hnr_solve_recursive_call methods frame_match_atom = 
  rule hnr_frame[rotated], assumption, hnr_frame_inference frame_match_atom

end
