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
    else return (undefined(i - len))
  }"

qualified definition update where
  "update arr i v = do {
    len \<leftarrow> Diff_Arr.length arr;
    if i < len
    then Diff_Arr.update arr i v 
    else return arr
  }"

qualified definition update_tailrec where
  "update_tailrec arr i v = do {
    len \<leftarrow> Diff_Arr.length arr;
    if i < len
    then Diff_Arr.update_tailrec arr i v 
    else return arr
  }"

end

lemma lookup_safe [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> a)> 
     Diff_Arr_Safe.lookup a i 
  <\<lambda>r. master_assn t * \<up>(r = xs!i)>"
  unfolding Diff_Arr_Safe.lookup_def
  apply sep_auto
  using length 
  apply sep_auto
  apply sep_auto
  using lookup
  by(sep_auto simp: nth_undefined[of xs i])+

lemma update_safe [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     Diff_Arr_Safe.update diff_arr i v
  <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') 
      \<and> (t' \<turnstile> xs[i := v] \<sim> diff_arr))>"
  unfolding Diff_Arr_Safe.update_def
  apply sep_auto
  apply(rule fi_rule[OF length, where F = emp])
  apply sep_auto+
  apply(rule cons_post_rule)
  apply(rule fi_rule[OF update, where F = emp])
  by sep_auto+

lemma update_tailrec_safe [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     Diff_Arr_Safe.update_tailrec diff_arr i v
  <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') 
      \<and> (t' \<turnstile> xs[i := v] \<sim> diff_arr))>"
  unfolding Diff_Arr_Safe.update_tailrec_def
  apply sep_auto
  apply(rule fi_rule[OF length, where F = emp])
  apply sep_auto+
  apply(rule cons_post_rule)
  apply(rule fi_rule[OF update_tailrec, where F = emp])
  by sep_auto+

end
