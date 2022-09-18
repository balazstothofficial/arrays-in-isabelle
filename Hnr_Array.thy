theory Hnr_Array
  imports Hnr Array_Safe
begin

named_theorems hnr_rule_arr

lemma hnr_new: 
  "hnr 
    (id_assn n ni * id_assn x xi) 
    (Array.new ni xi)
    (\<lambda>xs xsi. array_assn xs xsi * id_assn n ni * id_assn x xi)
    (Some (replicate n x))"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

definition New_Arr :: "'a list \<Rightarrow> 'a list" where
  "New_Arr xs = xs"

lemma hnr_of_list [hnr_rule_arr]:
  "hnr 
    emp
    (Array.of_list xs) 
    array_assn 
    (Some (New_Arr xs))"
  unfolding id_rel_def New_Arr_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_lookup [hnr_rule_arr]:
   "hnr
     (xsi \<mapsto>\<^sub>a xs * id_assn i ii)
     (Array_Safe.lookup xsi ii) 
     (\<lambda>r ri. array_assn xs xsi * id_assn r ri) 
     (Some (xs ! i))"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_update [hnr_rule_arr]: 
   "hnr 
      (array_assn xs xsi * id_assn i ii * id_assn v vi) 
      (Array_Safe.update ii vi xsi) 
      array_assn
      (Some (xs [i:= v]))"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_length [hnr_rule_arr]:
   "hnr 
      (array_assn xs xsi) 
      (Array.len xsi) 
      (\<lambda>r ri. array_assn xs xsi * id_assn r ri)
      (Some (length xs))"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_pass_arr [hnr_rule_arr]:
  "hnr (array_assn x xi) (return xi) array_assn (Some x)"
  using hnr_pass_general.

method ent_refl = rule ent_refl

method hnr_arr = hnr ent_refl ent_refl rule_set: hnr_rule_arr

method hnr_step_arr = hnr_step ent_refl ent_refl rule_set: hnr_rule_arr

end
