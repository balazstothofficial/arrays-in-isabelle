theory Diff_Arr_Rel
  imports Cell
begin

fun diff_arr_rel' where
  "diff_arr_rel' t xs 0 a \<longleftrightarrow> (a, Array' xs) \<in>\<^sub>L t"
| "diff_arr_rel' t xs (Suc n) a \<longleftrightarrow> (\<exists>i x a' xs'. 
      (a, Upd' i x a') \<in>\<^sub>L t
    \<and> diff_arr_rel' t xs' n a'
    \<and> xs = xs'[i:=x] 
    \<and> i < length xs'
)"

(* TODO: Is precedence okay? + How to make subscript not just single char? *)
notation diff_arr_rel' ("(_ \<turnstile> _ \<sim>\<^sub>_ _)" [51, 51, 51, 51] 50) 
  
definition diff_arr_rel where
  "diff_arr_rel t xs a \<equiv> \<exists>n. t \<turnstile> xs \<sim>\<^sub>n a"

(* TODO: Is precedence okay? *)
notation diff_arr_rel ("(_ \<turnstile> _ \<sim> _)" [51, 51, 51] 50) 

lemma diff_arr_rel'_cons: "t \<turnstile> xs \<sim>\<^sub>n diff_arr \<Longrightarrow> x # t \<turnstile> xs \<sim>\<^sub>n diff_arr"
proof(induction t xs n diff_arr rule: diff_arr_rel'.induct)
  case 1
  then show ?case by auto
next
  case (2 t xs n a)
  then show ?case 
    apply auto
    subgoal for i v a' xs'
      apply(rule exI[where x = "i"])
      apply(rule exI[where x = "v"])
      apply(rule exI[where x = "a'"])
      by auto
    done
qed

lemma diff_arr_rel'_cons': "t \<turnstile> xs \<sim>\<^sub>n diff_arr \<Longrightarrow> \<exists>n. x # t \<turnstile> xs \<sim>\<^sub>n diff_arr"
  using diff_arr_rel'_cons
  by blast

lemma diff_arr_rel_cons: "t \<turnstile> xs \<sim> diff_arr \<Longrightarrow> x # t \<turnstile> xs \<sim> diff_arr"
  unfolding diff_arr_rel_def
  using diff_arr_rel'_cons by blast

end
