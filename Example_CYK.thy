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

synth_definition member'_impl is [hnr_rule_diff_arr]: 
    "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (member' x xs)"
  apply hnr_diff_arr
  done

end
