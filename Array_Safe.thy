theory Array_Safe
  imports Base
begin

(* TODO: Use locale? *)

context
begin

qualified definition lookup where
  "lookup arr i = do {
    len \<leftarrow> Array.len arr;
    if i < len
    then Array.nth arr i
    else do { 
      xs \<leftarrow> Array.freeze arr;
      return (xs ! i)
    }
  }"

qualified definition update where
  "update i v arr = do {
    len \<leftarrow> Array.len arr;
    if i < len
    then Array.upd i v arr
    else return arr
  }"

lemma lookup_safe [sep_heap_rules]: "
   <arr \<mapsto>\<^sub>a xs> 
    lookup arr i
   <\<lambda>res. \<up>(res = xs ! i) * arr \<mapsto>\<^sub>a xs>"
  unfolding lookup_def
  by sep_auto

lemma update_safe [sep_heap_rules]:
  "<arr \<mapsto>\<^sub>a xs> update i v arr <\<lambda>res. \<up>(res = arr) * arr \<mapsto>\<^sub>a xs[i := v]>"
  unfolding update_def
  by sep_auto

end

end
