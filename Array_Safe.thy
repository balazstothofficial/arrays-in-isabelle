theory Array_Safe
  imports Base
begin

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


end
