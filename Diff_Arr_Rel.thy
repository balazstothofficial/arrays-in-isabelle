theory Diff_Arr_Rel
  imports Master_Assn
begin

fun diff_arr_rel' where
  "diff_arr_rel' t xs 0 a \<longleftrightarrow> (a, Array' xs) \<in>\<^sub>L t"
| "diff_arr_rel' t xs (Suc n) a \<longleftrightarrow> (\<exists>i x a' xs'. 
      (a, Upd' i x a') \<in>\<^sub>L t
    \<and> diff_arr_rel' t xs' n a'
    \<and> xs = xs'[i:=x] 
    \<and> i < length xs'
)"
(* TODO: Is precedence okay? + How to make subscript not just single char *)
notation diff_arr_rel' ("(_ \<turnstile> _ \<sim>\<^sub>_ _)" [51, 51, 51, 51] 50) 
  
definition diff_arr_rel where
  "diff_arr_rel t xs a \<equiv> \<exists>n. t \<turnstile> xs \<sim>\<^sub>n a"
notation diff_arr_rel ("(_ \<turnstile> _ \<sim> _)" [51, 51, 51] 50) (* TODO: Is precedence okay? *)

lemma diff_arr_rel_cons: "t \<turnstile> xs \<sim> diff_arr \<Longrightarrow> (diff_arr', c') # t \<turnstile> xs \<sim> diff_arr"
  unfolding diff_arr_rel_def
  apply auto
  subgoal for n
    apply(rule exI[where x = n]) 
    proof(induction t xs n diff_arr rule: diff_arr_rel'.induct)
      case (1 C xs a)
      then show ?case
        by auto
    next
      case (2 C n xs a)
      then show ?case
        apply auto
        subgoal for i x diff_arr'
          apply(rule exI[where x = i]) 
          apply(rule exI[where x = x]) 
          apply(rule exI[where x = diff_arr']) 
          by auto
        done
    qed
    done

end
