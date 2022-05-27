theory Array_Safe
  imports  Diff_Arr
begin

(* TODO: Use locale? *)

definition array_nth_safe where
  "array_nth_safe arr i = do {
    len \<leftarrow> Array.len arr;
    if i < len
    then Array.nth arr i
    else do { 
      xs \<leftarrow> Array.freeze arr;
      return (xs ! i)
    }
  }"

definition array_update_safe where
  "array_update_safe i v arr = do {
    len \<leftarrow> Array.len arr;
    if i < len
    then Array.upd i v arr
    else return arr
  }"

definition diff_arr_lookup_safe where
  "diff_arr_lookup_safe arr i = do {
    len \<leftarrow>  Diff_Arr.length arr;
    if i < len
    then  Diff_Arr.lookup arr i
    else do { 
      arr \<leftarrow>  Diff_Arr.realize arr;
      xs \<leftarrow> Array.freeze arr;
      return (xs ! i)
    }
  }"

definition diff_arr_update_safe  where
  "diff_arr_update_safe arr i v = do {
    len \<leftarrow>  Diff_Arr.length arr;
    if i < len
    then Diff_Arr.update arr i v 
    else return arr
  }"

lemma nth_undefined: "i \<ge> length xs \<Longrightarrow> xs ! i = undefined(i - length xs)"
  apply(induction xs arbitrary: i)
  unfolding List.nth_def
  by(auto split: nat.splits)

lemma array_nth_safe [sep_heap_rules]: "
   <arr \<mapsto>\<^sub>a xs> 
    array_nth_safe arr i
   <\<lambda>res. \<up>(res = xs ! i) * arr \<mapsto>\<^sub>a xs>"
  unfolding array_nth_safe_def
  by(sep_auto simp: nth_undefined)

lemma array_update_safe [sep_heap_rules]:
  "<arr \<mapsto>\<^sub>a xs> array_update_safe i v arr <\<lambda>res. \<up>(res = arr) * arr \<mapsto>\<^sub>a xs[i := v]>"
  unfolding array_update_safe_def
  by sep_auto

lemma update_safe[sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     diff_arr_update_safe diff_arr i v
  <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') 
      \<and> (t' \<turnstile> xs[i := v] \<sim> diff_arr))>\<^sub>t
"
  unfolding diff_arr_update_safe_def
  apply sep_auto
   apply(rule fi_rule[OF length])
   apply sep_auto
  apply sep_auto
   apply(rule cons_post_rule)
    apply(rule fi_rule[OF update])
  by sep_auto+

lemma lookup_safe [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> a)> 
     diff_arr_lookup_safe a i 
  <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
  unfolding diff_arr_lookup_safe_def
  apply sep_auto
   apply(rule fi_rule[OF length])
   apply sep_auto+
  apply(rule cons_post_rule)
    apply(rule fi_rule[OF lookup])
    apply sep_auto+
   apply(rule fi_rule[OF realize])
  by sep_auto+

end
