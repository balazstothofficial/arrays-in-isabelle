theory Hnr_Recursion
  imports Hnr_Base
begin

(* TODO: Automate *)

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
    step: "\<And>r ri x xi. (\<And>x' xi'. hnr (\<Gamma> x' xi') (ri xi') (\<Gamma>' x' xi') (r x'))
        \<Longrightarrow> hnr (\<Gamma> x xi) (fi ri xi) (\<Gamma>' x xi) (f r x)"
  and
    mono_heap: "\<And>x. mono_Heap (\<lambda>r. fi r x)"
  shows  
    "hnr (\<Gamma> x xi) (heap.fixp_fun fi xi) (\<Gamma>' x xi) (option.fixp_fun f x)"
proof(induction arbitrary: x xi rule: ccpo.fixp_induct[OF option.ccpo])
  case 1
  then show ?case 
    apply(rule admissible_fun)
    by(rule admissible_flat)
next
  case 2
  then show ?case 
    using mono_option 
    by(auto simp: monotone_def fun_ord_def)
next
  case 3
  then show ?case 
    by auto
next
  case 4
  then show ?case 
    apply(subst heap.mono_body_fixp[OF mono_heap])
    apply(rule step)
    by simp
qed

method_setup partial_function_mono = 
  \<open>Scan.succeed (SIMPLE_METHOD' o Partial_Function.mono_tac)\<close>

end
