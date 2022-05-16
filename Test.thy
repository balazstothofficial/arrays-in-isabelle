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

(* HNR *)

value "(xs[1 := 2], xs[1 := 3])"

definition test1 where
  "test1 xs = (let c1 = 1; c2 = 2; c3 = 3; t1 = xs[c1 := c2]; t2 = t1[c1 := c3]; t3 = t2 ! c2 in t3)"

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  unfolding test1_def 
  apply(rule hnr_let hnr_return)+
  apply(rule hnr_frame[OF hnr_array_update], frame_inference)
  apply(rule hnr_let)
  apply(rule hnr_frame[OF hnr_array_update], frame_inference)
  apply(rule hnr_let)
  apply(rule hnr_frame[OF hnr_array_nth], frame_inference)
  apply(rule hnr_frame[OF hnr_pass])
  sorry
  

datatype 'a list = Nil | Cons 'a "'a list"

export_code array_nth_safe array_update_safe in SML_imp

end
