theory Test_Diff_Arr
  imports Diff_Arr "HOL-Library.Code_Target_Nat"
begin         

definition test where "test = do {
  r  \<leftarrow> Diff_Arr.from_list [4, 2, 0];
  y  \<leftarrow> Diff_Arr.update_tailrec r 1 (7::nat);
  y' \<leftarrow> Diff_Arr.update r 1 (8::nat);
  x  \<leftarrow> Diff_Arr.lookup y 1;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

end
