theory Test_Hnr
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" Definition_Utils
begin

definition sequential_1 where
  "sequential_1 xs = 
    (let c1 = (let x = 1 in x); 
         c2 = 2; 
         c3 = 3; 
         t1 = xs[c1 := c2]; 
         t2 = t1[c1 := c3];
         t3 = t2 ! c2 
      in t3)"

definition sequential_2 where
  "sequential_2 xs = 
    (let c1 = 1; t1 = xs[c1 := c1] in t1)"

definition return_tuple_1 where
  "return_tuple_1 xs = 
    (let c1 = 1; c2 = 2 in (c1, c2))"

definition return_tuple_2 where
  "return_tuple_2 xs = 
    (let c1 = 1; t1 = xs[c1 := c1] in (c1, t1))"

definition return_tuple_3 where
  "return_tuple_3 xs = 
    (let c1 = 1; t1 = xs; t2 = xs[c1 := c1] in (t1, t2))"

definition return_tuple_4 where
  "return_tuple_4 xs = 
    (let p = let c1 = 1; c2 = 2 in (c1, c2) in p)"

definition not_linear where
  "not_linear xs = 
    (let c1 = 1; t1 = xs[c1 := c1]; t2 = xs ! c1 in t1)"

definition if_1 where
  "if_1 xs =
    (let c1 = 1; 
         t1 = if xs = [] 
              then xs 
              else let t2 = xs[c1 := c1]
                   in t2 
     in t1)"

definition if_2 where
  "if_2 xs =
    (let c1 = 1; 
         t1 = if xs = [] 
              then xs 
              else let t1 = xs[c1 := c1]; 
                       t2 = t1[c1 := c1] 
                   in t2 
      in t1)"

definition if_3 where
  "if_3 xs =
    (let c1 = 1; 
         t1 = if xs = [] 
              then let c2 = 2; t1 = xs[c2 := c2]; t2 = t1[c2:= c2] 
                   in xs 
              else let t1 = xs[c1 := c1]; t2 = t1[c1:= c1] 
                   in t2 
     in t1)"

definition if_4 where
  "if_4 xs = 
    (let c1 = 1; t1 = if True then xs else xs[c1 := c1] in t1)"

definition if_5 where
  "if_5 xs = 
    (let c1 = 1; 
         c2 = 2; 
         t1 = if xs = [] 
              then xs[c2 := c2] 
              else xs[c1 := c1] 
     in t1)"

definition if_6 where
  "if_6 xs = 
    (let c1 = 1; 
         c2 = 2; 
         t1 = if xs = [] 
              then let t2 = xs[c2 := c2]; t3 = xs[c1 := c1] in t3 
              else let t2 = xs[c1 := c1]; t3 = xs[c2 := c1] in t3 
         in t1)"

definition if_7 where
  "if_7 xs = (
    let c1 = 1 
    in if True
       then let t1 = xs[c1 := c1]
            in (t1, t1) 
       else let t1 = xs[c1 := c1] 
            in (t1, t1)
    )"

definition tuple_list where
  "tuple_list xs = (let c1 = 1; c2 = (c1, c1); t1 = xs[c1 := c2] in t1)"

definition nested where
  "nested xs = (let c1 = 1; t1 = xs[c1 := c1] in sequential_1 t1)"

definition fallback_1 where
  "fallback_1 xs = 
    (let c1 = 1; b = (c1 = c1); t1 = if b then xs else xs[c1 := c1] in t1)"

definition create_list where
  "create_list x = (let xs = [x] in xs)" 

definition create_arr where
  "create_arr xs = (let a = New_Arr xs in a)"

definition create_arr_2 where
  "create_arr_2 x = New_Arr [x]"

definition create_arr_3 :: "('a::heap) \<Rightarrow> ('b::heap) \<Rightarrow> 'a list * 'b list" where
  "create_arr_3 a b = (let xs = New_Arr [a]; ys = New_Arr [b] in (xs, ys))"

definition create_diff_arr_empty :: "('a::heap) list" where
  "create_diff_arr_empty = New_Diff_Arr []" 

definition create_diff_arr :: "'a::heap \<Rightarrow> 'a list" where
  "create_diff_arr x = New_Diff_Arr [x]" 

definition create_diff_arr_2 ::  "'a::heap \<Rightarrow> 'a list list" where
  "create_diff_arr_2 xs = (let a = New_Diff_Arr [xs]; b = New_Diff_Arr [a] in b)" 

definition create_diff_arr_3 :: "('a::heap) list" where
  "create_diff_arr_3 = (let xs = New_Diff_Arr [] in xs)"

definition create_diff_arr_4 :: "('a::heap) \<Rightarrow> ('b::heap) \<Rightarrow> 'a list * 'b list" where
  "create_diff_arr_4 a b = (let xs = New_Diff_Arr [a]; ys  = New_Diff_Arr [b] in (xs, ys))"

definition create_arr_diff_arr :: "('a::heap) \<Rightarrow> 'a list" where
  "create_arr_diff_arr xs = (let a = New_Arr [xs]; b = Diff_Arr_From_Arr a in b)" 

(* HNR Array *)

synth_definition sequential_1_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (sequential_1 xs)"
  unfolding sequential_1_def 
  by hnr_arr

synth_definition sequential_2_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (sequential_2 xs)"
  unfolding sequential_2_def 
  by hnr_arr

synth_definition return_tuple_1_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_1 xs)"
  unfolding return_tuple_1_def
  by hnr_arr

synth_definition return_tuple_2_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_2 xs)"
  unfolding return_tuple_2_def
  by hnr_arr

(* Can't work, not linear! *)
synth_definition return_tuple_3_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_3 xs)"
  unfolding return_tuple_3_def 
  apply hnr_arr
  oops  

synth_definition return_tuple_4_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_4 xs)"
  unfolding return_tuple_4_def
  by hnr_arr

(* Can't work, not linear! *)
synth_definition not_linear_arr is
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (not_linear xs)"
  unfolding not_linear_def 
  apply hnr_arr
  oops 

synth_definition if_1_arr is [hnr_rule_arr]:
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_1 xs)"
  unfolding if_1_def 
  by hnr_arr

synth_definition if_2_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_2 xs)"
  unfolding if_2_def 
  by hnr_arr

(* 
  Shouldn't work, not linear! (Or best behavior would be that if something is not 
  linear it leaves in lists, such that then there automatically diff arrs are put)
*)
synth_definition if_3_arr is
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_3 xs)"
  unfolding if_3_def 
  by hnr_arr

synth_definition if_4_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_4 xs)"
  unfolding if_4_def 
  by hnr_arr

synth_definition if_5_arr is [hnr_rule_arr]:   
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_5 xs)"
  unfolding if_5_def 
  by hnr_arr

(* Shouldn't work, not linear! *)
synth_definition if_6_arr is 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_6 xs)"
  unfolding if_6_def 
  by hnr_arr

(* Shouldn't work, not linear! *)
synth_definition if_7_arr is
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_7 xs)"
  unfolding if_7_def 
  by hnr_arr

synth_definition tuple_list_arr is [hnr_rule_arr]:
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (tuple_list xs)"
  unfolding tuple_list_def 
  by hnr_arr

synth_definition nested_arr is 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (nested xs)"
  unfolding nested_def 
  by hnr_step_arr+

synth_definition create_list_arr is [hnr_rule_arr]:
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_list x)"
  unfolding create_list_def 
  by hnr_arr

synth_definition create_arr_impl is [hnr_rule_arr]:
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_arr (xs :: ('a::heap) list))"
  unfolding create_arr_def 
  by hnr_arr

synth_definition create_arr_2_impl is [hnr_rule_arr]:
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_arr_2 (x :: 'a :: heap))"
  unfolding create_arr_2_def 
  by hnr_arr

(* TODO: This somehow just works with diff arrays *)
synth_definition create_arr_3_impl is [hnr_rule_arr]:
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_arr_3 (x :: 'a :: heap))"
  unfolding create_arr_3_def 
  by hnr_arr

(* HNR Diff-Array *)

synth_definition sequential_1_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (sequential_1 xs)"
  unfolding sequential_1_def 
  by hnr_diff_arr

synth_definition sequential_2_diff_arr is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (sequential_2 xs)"
  unfolding sequential_2_def
  by hnr_diff_arr

synth_definition return_tuple_1_diff_arr is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_1 xs)"
  unfolding return_tuple_1_def
  by hnr_diff_arr

synth_definition return_tuple_2_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_2 xs)"
  unfolding return_tuple_2_def 
  by hnr_diff_arr
   
synth_definition return_tuple_3_diff_arr is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_3 xs)"
  unfolding return_tuple_3_def 
  by hnr_diff_arr

synth_definition return_tuple_4_diff_arr is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_4 xs)"
  unfolding return_tuple_4_def
  by hnr_diff_arr

synth_definition not_linear_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (not_linear xs)"
  unfolding not_linear_def 
  by hnr_diff_arr

synth_definition if_1_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_1 xs)"
  unfolding if_1_def 
  by hnr_diff_arr

synth_definition if_2_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_2 xs)"
  unfolding if_2_def 
  by hnr_diff_arr

synth_definition if_3_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_3 xs)"
  unfolding if_3_def 
  by hnr_diff_arr

synth_definition if_4_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_4 xs)"
  unfolding if_4_def 
  by hnr_diff_arr

synth_definition if_5_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_5 xs)"
  unfolding if_5_def 
  by hnr_diff_arr

synth_definition if_6_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_6 xs)"
  unfolding if_6_def 
  by hnr_diff_arr

synth_definition if_7_diff_arr is [hnr_rule_diff_arr]: 
    "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_7 xs)"
  unfolding if_7_def   
  by hnr_diff_arr

synth_definition tuple_list_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (tuple_list xs)"
  unfolding tuple_list_def 
  by hnr_diff_arr

synth_definition nested_diff_arr is 
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (nested xs)"
  unfolding nested_def 
  by hnr_diff_arr

(* TODO: *)
schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (fallback_1 xs)"
  unfolding fallback_1_def 
  by hnr_diff_arr

synth_definition create_list_diff_arr is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_list x)"
  unfolding create_list_def 
  by hnr_diff_arr

synth_definition create_diff_arr_empty_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr_empty)"
  unfolding create_diff_arr_empty_def 
  by hnr_diff_arr

synth_definition create_diff_arr_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr x)"
  unfolding create_diff_arr_def 
  by hnr_diff_arr

(* TODO: Nested lists *)
synth_definition create_diff_arr_2_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr_2 x)"
  unfolding create_diff_arr_2_def 
  apply hnr_step_diff_arr+
  oops
                                                 
synth_definition create_diff_arr_3_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr_3)"
  unfolding create_diff_arr_3_def 
  by hnr_diff_arr

synth_definition create_diff_arr_4_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr_4 x y)"
  unfolding create_diff_arr_4_def 
  by hnr_diff_arr

(* TODO: Do I need a combined operator? *)
synth_definition create_diff_arr_arr_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_arr_diff_arr x)"
  unfolding create_arr_diff_arr_def 
  apply hnr_arr
  by hnr_diff_arr

export_code create_diff_arr_4_impl in SML_imp module_name foo

end
