theory Example_CYK
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" Definition_Utils
begin

(* TODO: Verify with original implementation from CYK.thy *)
datatype ('n, 't) RHS = NonTerminals 'n 'n | Terminal 't 

derive countable RHS
 
instance RHS :: (heap, heap) heap ..

lemma hnr_case_RHS [hnr_rule]:
  assumes 
    "\<And>A Ai B Bi. hnr (\<Gamma> * id_assn a ai * id_assn A Ai * id_assn B Bi * \<Gamma>') (cli Ai Bi) (\<Gamma>\<^sub>a A Ai B Bi) (cl A B)"
    "\<And>A Ai B Bi r ri. Keep_Drop (\<Gamma>\<^sub>a A Ai B Bi r ri) (\<Gamma>\<^sub>a' r ri) (Drop\<^sub>a A Ai B Bi r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>a' r ri) (\<Gamma>\<^sub>a'' r ri)"

    "\<And>T Ti. hnr (\<Gamma> * id_assn a ai * id_assn T Ti) (cri Ti) (\<Gamma>\<^sub>b T Ti) (cr T)"
    "\<And>T Ti r ri. Keep_Drop (\<Gamma>\<^sub>b T Ti r ri) (\<Gamma>\<^sub>b' r ri) (Drop\<^sub>b T Ti r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>b' r ri) (\<Gamma>\<^sub>b'' r ri)"
  
    "\<And>r ri. Merge (\<Gamma>\<^sub>a'' r ri) (\<Gamma>\<^sub>b'' r ri) (\<Gamma>\<^sub>c r ri)"
  shows
    "hnr 
      (\<Gamma> * id_assn a ai * \<Gamma>')
      (case ai of NonTerminals A B \<Rightarrow> cli A B | Terminal T \<Rightarrow> cri T)
       \<Gamma>\<^sub>c 
      (case a of NonTerminals A B \<Rightarrow> cl A B | Terminal T \<Rightarrow> cr T)"
  using assms(7)
  apply -
  apply(hnr_cases_prepare splits: RHS.splits)
  
  using assms(2, 3)
  apply -
  apply(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)

  using assms(5, 6)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(4) ent_disjI: ent_disjI2)

lemma hnr_case_RHS_2 [hnr_rule]:
  assumes 
    "\<And>A Ai B Bi. hnr (id_assn a ai * id_assn A Ai * id_assn B Bi * \<Gamma>') (cli Ai Bi) (\<Gamma>\<^sub>a A Ai B Bi) (cl A B)"
    "\<And>A Ai B Bi r ri. Keep_Drop (\<Gamma>\<^sub>a A Ai B Bi r ri) (\<Gamma>\<^sub>a' r ri) (Drop\<^sub>a A Ai B Bi r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>a' r ri) (\<Gamma>\<^sub>a'' r ri)"

    "\<And>T Ti. hnr (id_assn a ai * id_assn T Ti) (cri Ti) (\<Gamma>\<^sub>b T Ti) (cr T)"
    "\<And>T Ti r ri. Keep_Drop (\<Gamma>\<^sub>b T Ti r ri) (\<Gamma>\<^sub>b' r ri) (Drop\<^sub>b T Ti r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>b' r ri) (\<Gamma>\<^sub>b'' r ri)"
  
    "\<And>r ri. Merge (\<Gamma>\<^sub>a'' r ri) (\<Gamma>\<^sub>b'' r ri) (\<Gamma>\<^sub>c r ri)"
  shows
    "hnr 
      (id_assn a ai * \<Gamma>')
      (case ai of NonTerminals A B \<Rightarrow> cli A B | Terminal T \<Rightarrow> cri T)
       \<Gamma>\<^sub>c 
      (case a of NonTerminals A B \<Rightarrow> cl A B | Terminal T \<Rightarrow> cr T)"
  using assms(7)
  apply -
  apply(hnr_cases_prepare splits: RHS.splits)
  
  using assms(2, 3)
  apply -
  apply(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)

  using assms(5, 6)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(4) ent_disjI: ent_disjI2)

type_synonym ('n, 't) CNG = "('n \<times> ('n, 't) RHS) list"

fun member_original :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "member_original a [] = False" 
| "member_original a (x#xs) = (x = a \<or> member_original a xs)"

(* TODO: Automatic rewriting to index-based iteration if tail is unused *)
fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "member a xs n = (
    case n of 
        0 \<Rightarrow> False 
     | (Suc n) \<Rightarrow> xs ! n = a \<or> member a xs n
    )"
declare member.simps[simp del]

abbreviation member' where
  "member' a xs \<equiv> member a xs (length xs)"

(* TODO: Automatic conversion from recursion to fixpoint operator
   TODO: Keep short-circuit evaluations (Don't evaluate c3 if c2 is true \<rightarrow> Convert or to if?)
 *)
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

lemma member_opt_termination: "member_opt a xs n = Some (member a xs n)"
  apply(induction a xs n rule: member.induct)
  apply(simp(no_asm) add: member.simps member_opt_unfold)
  by(simp split: nat.split)
 
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

(* TODO: Automatic conversion from recursion to fixpoint operator
   TODO: Keep short-circuit evaluations (Don't evaluate c3 if c2 is true \<rightarrow> Convert or to if?)
 *)
definition match_prods_opt where
  "match_prods_opt ls rs \<equiv> option.fixp_fun (\<lambda>match_prods_opt ps. 
    case ps of
      []   \<Rightarrow> Some []
    | p#ps \<Rightarrow> do {
      let c1 = p;
      case c1 of
       (X, t) \<Rightarrow> do {
        let c2 = t;
        case c2 of
          NonTerminals A B \<Rightarrow> do {
              let c3 = member' A ls;
              let c4 = member' B rs;
              c5 \<leftarrow> match_prods_opt ps;
              let c6 = (c3 \<and> c4);
              if c6 then do {
                let c7 = X # c5;
                Some c7
              } else Some c5
            }
        | Terminal a \<Rightarrow> match_prods_opt ps
        }
      }
  )"

fun match_prods_2 :: "nat \<Rightarrow> ('n, 't) CNG \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> 'n list" where 
  "match_prods_2 i ps ls rs = (
    case i of
      0   \<Rightarrow> []
    | Suc n \<Rightarrow> 
      do {
        let p = ps ! n;
        case p of
          (X, t) \<Rightarrow> 
            (case t of
              NonTerminals A B \<Rightarrow> 
                if member' A ls \<and> member' B rs 
                then X # match_prods_2 n ps ls rs
                else match_prods_2 n ps ls rs
            | Terminal a \<Rightarrow> match_prods_2 n ps ls rs
            )
      }
  )"

definition match_prods_opt_2 where
  "match_prods_opt_2 ps ls rs \<equiv> option.fixp_fun (\<lambda>match_prods_opt n. 
    case n of
      0   \<Rightarrow> Some []
    | Suc n \<Rightarrow> do {
      let c1 = ps ! n;
      case c1 of
       (X, t) \<Rightarrow> do {
        let c2 = t;
        case c2 of
          NonTerminals A B \<Rightarrow> do {
              let c3 = member' A ls;
              let c4 = member' B rs;
              c5 \<leftarrow> match_prods_opt n;
              let c6 = (c3 \<and> c4);
              if c6 then do {
                let c7 = X # c5;
                Some c7
              } else Some c5
            }
        | Terminal a \<Rightarrow> match_prods_opt n
        }
      }
  )"

schematic_goal match_prods_opt_unfold: "match_prods_opt ls rs ps \<equiv> ?v"
  apply(rule gen_code_thm_option_fixp[OF match_prods_opt_def])
  by(partial_function_mono)

schematic_goal match_prods_opt2_unfold: "match_prods_opt_2 ps ls rs n \<equiv> ?v"
  apply(rule gen_code_thm_option_fixp[OF match_prods_opt_2_def])
  by(partial_function_mono)

lemma match_prods_opt_termination: "match_prods_opt ls rs ps = Some (match_prods ps ls rs)"
  apply(induction ps ls rs rule: match_prods.induct)
  apply(simp(no_asm) add: match_prods_opt_unfold)
  by(auto split: list.split RHS.split)

(* TODO: *)
lemma match_prods_opt_2_termination: 
    "match_prods_opt_2 ps ls rs (length ps) = Some (match_prods ps ls rs)"
  apply(induction ps ls rs rule: match_prods.induct)
  apply(simp(no_asm) add: match_prods_opt2_unfold)
  sorry

function inner_original :: "('n, 't) CNG \<Rightarrow> (nat \<times> nat \<Rightarrow> 'n list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
 "inner_original G T i k j = (
    if k < j 
    then match_prods_original G (T(i, k)) (T(i + k, j - k)) @ inner_original G T i (k + 1) j
    else []
  )"
by pat_completeness auto
termination
  by(relation "measure(\<lambda>(a, b, c, d, e). e - d)", rule wf_measure, simp)

function inner :: "('n, 't) CNG \<Rightarrow> (nat \<times> nat \<Rightarrow> 'n list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
 "inner G T i k j = (
    if k < j 
    then match_prods G (T(i, k)) (T(i + k, j - k)) @ inner G T i (k + 1) j
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
  fixes ls :: "'a list"
begin

synth_definition member_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F) * id_assn n ni) (\<hole>:: ?'a Heap) ?\<Gamma>' (member_opt x xs n)"
  unfolding member_opt_def
  (* TODO: Could this problem partly be solved by the rule that the terminating branches always appear
     first? *)
  apply(rule hnr_recursion[where
      \<Gamma> = "(\<lambda>n ni. master_assn' (insert (xs, xsi) F) * id_assn n ni)" and
      \<Gamma>' = "(\<lambda>n ni r ri. master_assn' (insert (xs, xsi) F) * id_assn n ni * id_assn r ri)"])
  by hnr_diff_arr

synth_definition member_impl_arr is [hnr_rule_arr]:
  "hnr (array_assn xs xsi' * id_assn n ni) (\<hole>:: ?'a Heap) ?\<Gamma>' (member_opt x xs n)"
  unfolding member_opt_def
  apply(rule hnr_recursion[where
      \<Gamma> = "(\<lambda>n ni. array_assn xs xsi' * id_assn n ni)" and
      \<Gamma>' = "(\<lambda>n ni r ri. array_assn xs xsi' * id_assn n ni * id_assn r ri)"])
  by hnr_arr

lemma helper: "a = ai \<Longrightarrow> as = asi \<Longrightarrow> a # as = ai # asi"
  by auto

synth_definition match_prods_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (rs, rsi) F) * 
        master_assn' (insert (ls, lsi) F') * 
        id_assn ps psi) 
       (\<hole>:: ?'a Heap) ?\<Gamma>'
       (match_prods_opt ls rs ps)"
  unfolding match_prods_opt_def
   apply(rule hnr_recursion[where
      \<Gamma> = "(\<lambda>ps psi. master_assn' (insert (rs, rsi) F) * 
        master_assn' (insert (ls, lsi) F') * 
        id_assn ps psi)" and
      \<Gamma>' = "(\<lambda>ps psi ps' psi'. master_assn' (insert (rs, rsi) F) * 
        master_assn' (insert (ls, lsi) F') * 
        id_assn ps psi *
        id_assn ps' psi')"])
    apply hnr_diff_arr
    (* apply(simp only: mult.left_assoc[where 'a=assn]) *)
    apply(rule hnr_fallback)
    apply(extract_pre rule: models_id_assn)
    apply(drule models_id_assn)
    apply(rule helper)
    apply simp
    apply simp
    apply hnr_diff_arr
    oops

synth_definition match_prods_impl_arr is [hnr_rule_arr]:
  "hnr (array_assn rs rsi * array_assn ls lsi * id_assn ps psi) 
       (\<hole>:: ?'a Heap) ?\<Gamma>'
       (match_prods_opt ls rs ps)"
  unfolding match_prods_opt_def
   apply(rule hnr_recursion[where
      \<Gamma> = "(\<lambda>ps psi. array_assn rs rsi * array_assn ls lsi  * id_assn ps psi)" and
      \<Gamma>' = "(\<lambda>ps psi ps' psi'. array_assn rs rsi * array_assn ls lsi * id_assn ps psi * id_assn ps' psi')"])
    apply hnr_arr
    apply(rule hnr_fallback)
    apply(extract_pre rule: models_id_assn)
    apply(drule models_id_assn)
    apply(rule helper)
    apply simp
    apply simp
    apply hnr_arr
  oops

end

context 
  fixes ps :: "('a::heap, 'b::heap) CNG"
begin

synth_definition match_prods_2_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (rs, rsi) F) * 
        master_assn' (insert (ls, lsi) F') * 
        master_assn' (insert (ps, psi) F'') * 
        id_assn n ni) 
       (\<hole>:: ?'a Heap) ?\<Gamma>'
       (match_prods_opt_2 ps ls rs n)"
  unfolding match_prods_opt_2_def
   apply(rule hnr_recursion[where
      \<Gamma> = "(\<lambda>n ni. master_assn' (insert (rs, rsi) F) * 
        master_assn' (insert (ls, lsi) F') * 
        master_assn' (insert (ps, psi) F'') * 
        id_assn n ni)" and
      \<Gamma>' = "(\<lambda>n ni n' ni'. master_assn' (insert (rs, rsi) F) * 
        master_assn' (insert (ls, lsi) F') * 
        master_assn' (insert (ps, psi) F'') * 
        id_assn n ni *
        id_assn n' ni')"])
  apply hnr_diff_arr
  oops

end

end
