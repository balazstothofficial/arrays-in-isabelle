theory Example_CYK
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" Definition_Utils
begin

datatype ('n, 't) RHS = NonTerminals 'n 'n | Terminal 't 

type_synonym ('n, 't) CNG = "('n \<times> ('n, 't) RHS) list"

fun member_original :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "member_original a [] = False" 
| "member_original a (x#xs) = (x = a \<or> member_original a xs)"

fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "member a xs n = (case n of 
            0 \<Rightarrow> False 
         | (Suc n) \<Rightarrow> (xs ! n = a \<or> member a xs n)
  )"
declare member.simps[simp del]

abbreviation member' where
  "member' a xs \<equiv> member a xs (length xs)"

definition member_opt where
  "member_opt a xs \<equiv> option.fixp_fun (\<lambda> member_opt n. 
    case n of 
      0     \<Rightarrow> Some False 
    | Suc n \<Rightarrow> do {
        c1 \<leftarrow> Some (xs ! n);
        let c2 = (c1 = a);
        c3 \<leftarrow> member_opt n;
        let c4 = c2 \<or> c3;
        Some c4
      }
  )"

method_setup partial_function_mono = \<open>Scan.succeed (SIMPLE_METHOD' o Partial_Function.mono_tac)\<close>

schematic_goal member_opt_unfold: "member_opt a xs n \<equiv> ?v"
  apply(rule gen_code_thm_option_fixp[OF member_opt_def])
  by(partial_function_mono)
  thm gen_code_thm_option_fixp option.mono_body_fixp

find_theorems "option.fixp_fun"

lemma member_opt_termination: "member_opt a xs n = Some (member a xs n)"
  apply(induction a xs n rule: member.induct)
  apply(simp(no_asm) add: member.simps member_opt_unfold)
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
 
definition member_body where
  "member_body r a xs n =  (
    case n of
      0    \<Rightarrow> False
    | Suc n \<Rightarrow> let c1 = xs ! n; c2 = (c1 = a); c3 = r n; c4 = c2 \<or> c3 in c4
  )"

lemma member_body: "member a xs = member_body (member a xs) a xs"
  unfolding member_body_def fun_eq_iff Let_def
  by(auto simp: member.simps)

fun match_prods_original :: "('n, 't) CNG \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> 'n list" where 
  "match_prods_original [] ls rs = []" 
| "match_prods_original ((X, NonTerminals A B)#ps) ls rs = (
    if member_original A ls \<and> member_original B rs 
    then X # match_prods_original ps ls rs
    else match_prods_original ps ls rs
  )" 
| "match_prods_original ((X, Terminal a)#ps) ls rs = match_prods_original ps ls rs"

fun match_prods :: "('n, 't) CNG \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> 'n list" where 
  "match_prods ps ls rs = (
    case ps of
      []   \<Rightarrow> []
    | p#ps \<Rightarrow> 
      (case p of
       (X, t) \<Rightarrow> 
        (case t of
          NonTerminals A B \<Rightarrow> 
            if member' A ls \<and> member' B rs 
            then X # match_prods ps ls rs
            else match_prods ps ls rs
        | Terminal a \<Rightarrow> match_prods ps ls rs
        )
      )
  )"

function inner :: "('n, 't) CNG \<Rightarrow> (nat \<times> nat \<Rightarrow> 'n list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
 "inner G T i k j = (
    if k < j 
    then match_prods_original G (T(i, k)) (T(i + k, j - k)) @ inner G T i (k + 1) j
    else []
  )"
by pat_completeness auto
termination
by(relation "measure(\<lambda>(a, b, c, d, e). e - d)", rule wf_measure, simp)

context
  fixes x :: "'a :: heap"
  fixes xsi :: "'a cell ref"
begin

definition Ref where
  "Ref A a b = A a b"

schematic_goal "Ref id_assn a b \<Longrightarrow>\<^sub>A Ref ?A a (?b::?'b) * ?F" "undefined ?A ?b ?F"
   apply(frame_inference_2_dbg \<open>rule ent_refl\<close>)
  oops

synth_definition member_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F) * id_assn n ni) (\<hole>:: ?'a Heap) ?\<Gamma>' (member_opt x xs n)"
  unfolding member_opt_def
  (* Could this problem partly be solved by the rule that the terminating branches always appear
     first*)
  supply r = hnr_recursion[where 
      \<Gamma> = "(\<lambda>n ni. master_assn' (insert (xs, xsi) F) * id_assn n ni)" and
      \<Gamma>' = "(\<lambda>n ni r ri. master_assn' (insert (xs, xsi) F) * id_assn n ni * id_assn r ri)"] 
  apply(rule r)
  apply(partial_function_mono)
  apply hnr_diff_arr
  apply(rule hnr_fallback)
  apply(extract_pre rule: models_id_assn)
  apply(hypsubst)
  apply(rule refl)
  apply hnr_diff_arr
  apply(rule hnr_frame)
  apply assumption
  apply(frame_inference_2 \<open>rule ent_refl\<close>)
  apply hnr_diff_arr
  apply(rule hnr_fallback)
  apply(extract_pre rule: models_id_assn)
  apply(hypsubst)
  apply(rule refl)
  apply hnr_diff_arr
  apply(partial_function_mono)
  done

end

end
