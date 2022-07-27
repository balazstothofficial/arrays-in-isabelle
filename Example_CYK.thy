theory Example_CYK
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" Definition_Utils
begin

datatype ('n, 't) RHS = NonTerminals 'n 'n | Terminal 't 

type_synonym ('n, 't) CNG = "('n \<times> ('n, 't) RHS) list"

(* 
  1. Write as case on list. How should HNR rule look like for it? 
     Go via length of (diff-)arr
  2. How to handle recursion?
*)
fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "member a [] = False" 
| "member a (x#xs) = (x = a \<or> member a xs)"

fun member' :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "member' a xs = (
    case xs of
      [] \<Rightarrow> False
    | x#xs \<Rightarrow> (x = a \<or> member' a xs)
  )" 

fun member'' :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "member'' a xs n = (case n of 
            0 \<Rightarrow> False 
         | (Suc n) \<Rightarrow> (xs ! n = a \<or> member'' a xs n)
  )"
print_theorems
declare member''.simps[simp del]

partial_function (option) member''_opt  where
  "member''_opt a xs n = do { 
      (case n of 
            0 \<Rightarrow> Some False 
         | (Suc n) \<Rightarrow> do {
        c1 \<leftarrow> Some (xs ! n);
        let c2 = (c1 = a);
        c3 \<leftarrow> member''_opt a xs n;
        let c4 = c2 \<or> c3;
        Some c4
      })
 }"

definition member''_opt2 where
  "member''_opt2 a xs \<equiv> option.fixp_fun (\<lambda> member''_opt2 n. 
     (case n of 
            0 \<Rightarrow> Some False 
         | (Suc n) \<Rightarrow> do {
        c1 \<leftarrow> Some (xs ! n);
        let c2 = (c1 = a);
        c3 \<leftarrow> member''_opt2 n;
        let c4 = c2 \<or> c3;
        Some c4
      })
  )"

method_setup partial_function_mono = \<open>Scan.succeed (SIMPLE_METHOD' o Partial_Function.mono_tac)\<close>

schematic_goal member''_unfold: "member''_opt2 a xs n \<equiv> ?v"
  apply(rule gen_code_thm_option_fixp[OF member''_opt2_def])
  thm gen_code_thm_option_fixp option.mono_body_fixp
  by(partial_function_mono)

find_theorems "option.fixp_fun"

lemma "member''_opt2 a xs n = Some (member'' a xs n)"
  apply(induction a xs n rule: member''.induct)
  apply(simp(no_asm) add: member''.simps member''_unfold)
  by(auto split: nat.splits)

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

lemma
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
 

definition member''_body where
  "member''_body r a xs n =  (
    case n of
      0 \<Rightarrow> False
    | (Suc n) \<Rightarrow> (let c1 = xs ! n; c2 = (c1 = a); c3 = r n; c4 = c2 \<or> c3 in c4)
  )"

definition member'_body where
  "member'_body r a xs =  (
    case xs of
      [] \<Rightarrow> False
    | x#xs \<Rightarrow> (x = a \<or> r a xs)
  )"

lemma member'_body: "member' = member'_body member'"
  unfolding member'_body_def fun_eq_iff
  by auto

lemma member''_body: "member'' a xs = member''_body (member'' a xs) a xs"
  unfolding member''_body_def fun_eq_iff Let_def
  by(auto simp: member''.simps)

lemma member'_induct:
  assumes "\<And>xs r. (\<And>xs'. length xs' < length xs \<Longrightarrow> P (r a xs')) \<Longrightarrow> P (member'_body r a xs)"
  shows "P (member' a xs)"
  apply(induction "length xs" arbitrary: xs rule: nat_less_induct)
  apply(subst member'_body)
  apply(rule assms)
  by auto

(*lemma member_refinement:
  assumes 
    mono: "\<And>xs. mono_Heap (\<lambda>f. member'_bodyi f xs)"
  and
    step: "\<And>r ri xs xsi. (\<And>xs' xsi'. length xs' < length xs \<Longrightarrow> hnr (\<Gamma> xs' xsi') (ri xsi')  (\<Gamma>' xs' xsi') (r a xs')) 
    \<Longrightarrow> hnr (\<Gamma> xs xsi) (member'_bodyi ri xsi) (\<Gamma>' xs xsi) (member'_body r a xs)"
  shows "hnr (\<Gamma> xs xsi) (heap.fixp_fun member'_bodyi xsi) (\<Gamma>' xs xsi) (member' a xs)"
  apply(induction "length xs" arbitrary: xs xsi rule: nat_less_induct)
  apply(rewrite heap.mono_body_fixp[OF mono])
  apply(rewrite member'_body)
  apply(rule step)
  by simp
  
lemma member''_refinement:
  assumes 
    mono: "\<And>xs. mono_Heap (\<lambda>f. member''_bodyi f xs)"
  and
    step: "\<And>r ri n. (\<And>n'. n' < n \<Longrightarrow> hnr (\<Gamma>) (ri n')  (\<Gamma>') (r n')) 
    \<Longrightarrow> hnr (\<Gamma>) (member''_bodyi ri n) (\<Gamma>') (member''_body r a xs n)"
  shows "hnr (\<Gamma>) (heap.fixp_fun member''_bodyi n) (\<Gamma>') (member'' a xs n)"
  apply(induction n rule: nat_less_induct)
  apply(rewrite heap.mono_body_fixp[OF mono])
  apply(rewrite member''_body)
  apply(rule step)
  by simp *)

lemma 
    "hnr (master_assn' (insert (xs, xsi) F)) (c  xsi) \<Gamma>' (member''_opt2 x xs)"
  
  apply(induction rule: member'_induct)
  sorry

fun match_prods :: "('n, 't) CNG \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> 'n list" where 
  "match_prods [] ls rs = []" 
| "match_prods ((X, NonTerminals A B)#ps) ls rs = (
    if member A ls \<and> member B rs 
    then X # match_prods ps ls rs
    else match_prods ps ls rs
  )" 
| "match_prods ((X, Terminal a)#ps) ls rs = match_prods ps ls rs"

function inner :: "('n, 't) CNG \<Rightarrow> (nat \<times> nat \<Rightarrow> 'n list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
 "inner G T i k j = (
    if k < j 
    then match_prods G (T(i, k)) (T(i + k, j - k)) @ inner G T i (k + 1) j
    else []
  )"
by pat_completeness auto
termination 
by(relation "measure(\<lambda>(a, b, c, d, e). e - d)", rule wf_measure, simp)

context
  fixes x :: "'a :: heap"
begin


synth_definition member'_impl is [hnr_rule_diff_arr]: 
    "hnr (master_assn' (insert (xs, xsi) F)) ((\<hole>  xsi):: ?'a Heap) ?\<Gamma>' (member'' x xs n)"
  apply(rule member''_refinement)
   defer
  unfolding member''_body_def
   apply hnr_diff_arr
  apply(subgoal_tac "c1 = xi", hypsubst)
          apply(rule hnr_return)
         defer
  apply hnr_diff_arr
  done



end
