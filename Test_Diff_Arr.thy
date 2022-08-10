theory Test_Diff_Arr
  imports Diff_Arr "HOL-Library.Code_Target_Nat"
begin         

definition create_diff_arr where
  "create_diff_arr n x = do {
    a \<leftarrow> Array.new n x;
    Diff_Arr.from_array a
  }"

definition test where "test = do {
  r  \<leftarrow> create_diff_arr 3 (5::nat);
  y  \<leftarrow> Diff_Arr.update_tailrec r 1 (7::nat);
  y' \<leftarrow> Diff_Arr.update r 1 (8::nat);
  x  \<leftarrow> Diff_Arr.lookup y 1;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

end
