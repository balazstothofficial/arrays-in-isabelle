theory Diff_Arr_Safe
  imports Diff_Arr
begin

context
begin

qualified definition lookup where
  "lookup arr i = do {
    len \<leftarrow>  Diff_Arr.length arr;
    if i < len
    then Diff_Arr.lookup arr i
    else do { 
      arr \<leftarrow> Diff_Arr.realize arr;
      xs  \<leftarrow> Array.freeze arr;
      return (xs ! i)
    }
  }"

qualified definition update  where
  "update arr i v = do {
    len \<leftarrow> Diff_Arr.length arr;
    if i < len
    then Diff_Arr.update arr i v 
    else return arr
  }"

end

lemma update_safe [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     Diff_Arr_Safe.update diff_arr i v
  <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') 
      \<and> (t' \<turnstile> xs[i := v] \<sim> diff_arr))>\<^sub>t"
  unfolding Diff_Arr_Safe.update_def
  apply sep_auto
  apply(rule fi_rule[OF length])
  apply sep_auto
  apply sep_auto
  apply(rule cons_post_rule)
  apply(rule fi_rule[OF update])
  by sep_auto+

lemma lookup_safe [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> a)> 
     Diff_Arr_Safe.lookup a i 
  <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
  unfolding  Diff_Arr_Safe.lookup_def
  apply sep_auto
  apply(rule fi_rule[OF length])
  apply sep_auto+
  apply(rule cons_post_rule)
  apply(rule fi_rule[OF lookup])
  apply sep_auto+
  apply(rule fi_rule[OF realize])
  by sep_auto+

end
