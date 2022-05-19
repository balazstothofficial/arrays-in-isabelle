theory Test
  imports Diff_Arr HNR "HOL-Library.Code_Target_Nat"
begin

(* Diff Array *)

definition create_diff_arr where
  "create_diff_arr n x = do {
    a \<leftarrow> Array.new n x;
    from_array a
  }"

definition test where "test = do {
  r \<leftarrow> create_diff_arr 3 (5::nat);
  y  \<leftarrow> update r 1 (7::nat);
  y' \<leftarrow> update r 1 (8::nat);
  x \<leftarrow> lookup y 1;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

(* Hnr *)

value "(xs[1 := 2], xs[1 := 3])"

definition test1 where
  "test1 xs = 
    (let c1 = (let x = 1 in x); c2 = 2; c3 = 3; t1 = xs[c1 := c2]; t2 = t1[c1 := c3]; t3 = t2 ! c2 in t3)"

attribute_setup framed =
    \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn thm => @{thm hnr_frame} OF [asm_rl, thm]))\<close>
    \<open>Add frame to hnr rule\<close>

thm hnr_rule[framed]

method hnr_rule = 
  (rule hnr_rule[framed] hnr_copy[framed] hnr_return[framed], (frame_inference; fail))

method hnr_rule_2 = 
  (rule hnr_rule_2[framed] hnr_copy[framed], (frame_inference; fail)) | (rule hnr_let hnr_return)

method hnr_rule_diff_arr =
  (rule hnr_rule_diff_arr[framed] hnr_copy[framed], (frame_inference; fail)) | (rule hnr_let hnr_return)

method hnr = (hnr_rule | keep_drop)+

method hnr_2 = (hnr_rule_2 | keep_drop)+

method hnr_diff_arr = (hnr_rule_diff_arr | keep_drop)+

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  by hnr_2

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  unfolding test1_def 
  apply(rule hnr_let)
  apply(rule hnr_let)
  apply(rule hnr_return)
  apply(rule hnr_copy[framed], frame_inference)
  apply keep_drop
     (* Here: *)
   (* apply(rule hnr_let[framed])
  apply(frame_inference) *)
  apply(rule hnr_let)
  apply(rule hnr_return)
  apply(rule hnr_let)
  apply(rule hnr_return)
  apply(rule hnr_let)
  apply(rule hnr_array_update[framed], frame_inference)
  apply(rule hnr_let)
  apply(rule hnr_array_update[framed], frame_inference)
  apply(rule hnr_let)
  apply(rule hnr_array_nth[framed], frame_inference)
  apply(rule hnr_copy[framed], frame_inference)
  by keep_drop+

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  unfolding test1_def 
  apply(hnr_rule_diff_arr)
    apply(hnr_rule_diff_arr)
      apply(hnr_rule_diff_arr)
     apply(hnr_rule_diff_arr)
  apply keep_drop
   apply(hnr_rule_diff_arr)
     apply(hnr_rule_diff_arr)
    apply(hnr_rule_diff_arr)
      apply(hnr_rule_diff_arr)
     apply(hnr_rule_diff_arr)
  (* How to get to master_assn in the first place? *)
       apply(rule hnr_update'[framed])
  sorry

export_code array_nth_safe array_update_safe in SML_imp

end
