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

lemma member_refinement:
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
  by simp

lemma 
    "hnr (master_assn' (insert (xs, xsi) F)) (c  xsi) \<Gamma>' (member' x xs)"
  
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
