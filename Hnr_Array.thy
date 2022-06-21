theory Hnr_Array
  imports Hnr Array_Safe
begin

named_theorems hnr_rule_arr

lemma hnr_new: 
  "hnr 
    (id_assn n ni * id_assn x xi) 
    (Array.new ni xi) 
    (\<lambda>xs xsi. xsi \<mapsto>\<^sub>a xs * id_assn n ni * id_assn x xi) 
    (replicate n x)"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

definition New_Arr where
  "New_Arr xs = xs"

lemma hnr_array_of_list [hnr_rule_arr]: 
  "hnr 
    emp
    (Array.of_list xs) 
    (\<lambda>xs xsi. xsi \<mapsto>\<^sub>a xs) 
    (New_Arr xs)"
  unfolding id_rel_def New_Arr_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_array_nth [hnr_rule_arr]: "
    hnr
     (xsi \<mapsto>\<^sub>a xs * id_assn i ii)
     (array_nth_safe xsi ii) 
     (\<lambda> r ri. xsi \<mapsto>\<^sub>a xs * id_assn r ri) 
     (xs ! i)"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_array_update [hnr_rule_arr]: "
    hnr 
      (xsi \<mapsto>\<^sub>a xs * id_assn i ii * id_assn v vi) 
      (array_update_safe ii vi xsi) 
      array_assn
      (xs [i:= v])"
  unfolding id_rel_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_copy_arr [hnr_rule_arr]:
  "hnr (array_assn x xi) (return xi) array_assn x"
  using hnr_pass by fastforce

method refl = rule ent_refl

method hnr_arr = hnr refl refl rule_set: hnr_rule_arr

method hnr_step_arr = hnr_step refl refl rule_set: hnr_rule_arr

end
