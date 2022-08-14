theory Example_CYK
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" Definition_Utils
begin

(* TODO: Verify with original implementation from CYK.thy *)
datatype ('n, 't) RHS = NonTerminals 'n 'n | Terminal 't 

type_synonym ('n, 't) CNG = "('n \<times> ('n, 't) RHS) list"

fun member_original :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "member_original a [] = False" 
| "member_original a (x#xs) = (x = a \<or> member_original a xs)"

(* TODO: Automatic rewriting to index-based iteration if tail is unused *)
fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "member a xs n = (case n of 
            0 \<Rightarrow> False 
         | (Suc n) \<Rightarrow> (xs ! n = a \<or> member a xs n)
  )"
declare member.simps[simp del]

abbreviation member' where
  "member' a xs \<equiv> member a xs (length xs)"

(* TODO: Automatic conversion from recursion to fixpoint operator *)
definition member_opt where
  "member_opt a xs \<equiv> option.fixp_fun (\<lambda>member_opt n. 
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

schematic_goal member_opt_unfold: "member_opt a xs n \<equiv> ?v"
  apply(rule gen_code_thm_option_fixp[OF member_opt_def])
  by(partial_function_mono)

thm gen_code_thm_option_fixp option.mono_body_fixp
find_theorems "option.fixp_fun"

lemma member_opt_termination: "member_opt a xs n = Some (member a xs n)"
  apply(induction a xs n rule: member.induct)
  apply(simp(no_asm) add: member.simps member_opt_unfold)
  by(simp split: nat.split)
 
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

function main :: "('n, 't) CNG \<Rightarrow> (nat \<times> nat \<Rightarrow> 'n list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'n list)"
where "main G T len i j = (let T' = T((i, j) := inner G T i 1 j) in
                            if i + j < len then main G T' len (i + 1) j
                            else if j < len then main G T' len 0 (j + 1)
                                 else T')"
by pat_completeness auto
termination 
by(relation "inv_image (less_than <*lex*> less_than) (\<lambda>(a, b, c, d, e). (c - e, c - (d + e)))", rule wf_inv_image, rule wf_lex_prod, (rule wf_less_than)+, simp_all)


context
  fixes x :: "'a :: heap"
  fixes xsi :: "'a cell ref"
begin

synth_definition member_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F) * id_assn n ni) (\<hole>:: ?'a Heap) ?\<Gamma>' (member_opt x xs n)"
  unfolding member_opt_def
  (* TODO: Could this problem partly be solved by the rule that the terminating branches always appear
     first? *)
  apply(rule hnr_recursion[where 
      \<Gamma> = "(\<lambda>n ni. master_assn' (insert (xs, xsi) F) * id_assn n ni)" and
      \<Gamma>' = "(\<lambda>n ni r ri. master_assn' (insert (xs, xsi) F) * id_assn n ni * id_assn r ri)"])
  apply partial_function_mono
  apply hnr_diff_arr
  (* TODO: What's that? *)
  apply(rule hnr_frame)
  apply assumption
  apply(hnr_frame_inference \<open>rule ent_refl\<close>)
  apply hnr_diff_arr
  apply partial_function_mono
  done

end

end
