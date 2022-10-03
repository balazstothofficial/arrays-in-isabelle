theory Test_Hnr
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" Definition_Utils
begin

definition example_1 where
  "example_1 xs = do {
    let c1 = List.length xs;
    let c2 = 2;
    let c3 = c1 < c2;
    if c3 then do {
      let c4 = 1;
      let c5 = xs[c4 := c4];
      Some c5
    } else do { 
      let c6 = 2;
      let c7 = xs[c6 := c6];
      Some c7
    }
  }"

definition sequential_1 where
  "sequential_1 xs = 
    do { 
         c1 \<leftarrow> (do {  x \<leftarrow> Some 1; Some x }); 
         c2 \<leftarrow>  Some 2; 
         c3 \<leftarrow>  Some 3; 
         t1 \<leftarrow>  Some (xs[c1 := c2]); 
         t2 \<leftarrow>  Some (t1[c1 := c3]);
         t3 \<leftarrow>  Some (t2 ! c2);
      Some t3 }"

definition sequential_2 where
  "sequential_2 xs = 
    (do {
       let c1 = 1;
       let t1 = (xs[c1 := c1]);
       Some t1
     }
    )"

definition return_tuple_1 where
  "return_tuple_1 xs = 
    do { 
        let c2 = 2; 
        let c1 = c2; 
        Some (c1, c2)
    }"

definition return_tuple_2 where
  "return_tuple_2 xs = 
    do {
      let c1 = 1; 
      let t1 = xs[c1 := c1];
      Some (t1, c1)
    }"

definition return_tuple_3 where
  "return_tuple_3 xs = 
     do {
      let c1 = 1; 
      let t1 = xs; 
      let t2 = xs[c1 := c1];
      Some (t1, t2)
    }"

definition return_tuple_4 where
  "return_tuple_4 xs =
    do {
      let p = do { 
          let c1 = 1; 
          let c2 = 2;
          Some (c1, c2) };
      Some p
    }"

definition not_linear where
  "not_linear xs = do {
      let c1 = 1; let t1 = xs[c1 := c1]; let t2 = xs ! c1; Some t1
    }"

definition if_1 where
  "if_1 xs =
   do { 
      let c1 = 1;
      let b = (xs = []);
      t1 \<leftarrow> if b
             then Some xs 
             else do {
                 let t2 = xs[c1 := c1];
                 Some t2 
              }; 
        Some t1
       }"

definition if_2 where
  "if_2 xs =
    do { 
      let c1 = 1; 
      let b = (xs = []);
      t1 \<leftarrow> if b 
           then Some xs 
           else do { 
              let t1 = xs[c1 := c1]; 
              let t2 = t1[c1 := c1];
              Some t2 
            };
      Some t1 
  }"

definition if_3 where
  "if_3 xs =
    do { 
      let c1 = 1; 
      let b = (xs = []);
      t1 \<leftarrow> if b
            then do { let c2 = 2; let t1 = xs[c2 := c2]; let t2 = t1[c2:= c2]; Some xs }
            else do { let t1 = xs[c1 := c1]; let t2 = t1[c1:= c1]; Some t2 };
     Some t1 }"

definition if_4 where
  "if_4 xs = 
    do { 
      let c1 = 1; 
      let b = True;
      t1 \<leftarrow> if b then Some xs else do { let t1 = xs[c1 := c1]; Some t1 }; 
      Some t1 
  }"

definition if_5 where
  "if_5 xs = 
    do {
      let c1 = 1; 
      let c2 = 2;
      let b = (xs = []); 
       t1 \<leftarrow> if b
              then Some (xs[c2 := c2]) 
              else Some (xs[c1 := c1]);
      Some t1 }"

definition if_6 where
  "if_6 xs = do { 
    let c1 = 1; 
    let c2 = 2; 
    let b = (xs = []);
    t1 \<leftarrow> if b 
          then do { let t2 = xs[c2 := c2]; let t3 = xs[c1 := c1]; Some t3 } 
          else do { let t2 = xs[c1 := c1]; let t3 = xs[c2 := c1]; Some t3 };
    Some t1 
  }"

definition if_7 where
  "if_7 xs = do {
    let c1 = 1;
    let b = True;
    t \<leftarrow> if b
         then do { let t1 = xs[c1 := c1]; let t2 = (t1, t1); Some t2 }
         else do { let t1 = xs[c1 := c1]; let t2 = (t1, t1); Some t2 };
    Some t
    }"

definition tuple_list where
  "tuple_list xs = do { 
    let c1 = 1; 
    let c2 = (c1, c1); 
    let t1 = xs[c1 := c2]; 
    Some t1 
  }"

definition nested where
  "nested xs = do { 
    let c1 = 1; 
    let t1 = xs[c1 := c1]; 
    sequential_1 t1 
  }"

definition fallback_1 where
  "fallback_1 xs = do { 
    let c1 = 1; 
    let b = (c1 = c1); 
    t1 \<leftarrow> if b then Some xs else do { let t1 = xs[c1 := c1]; Some t1 }; 
    Some t1 
  }"

definition fallback_2 where
  "fallback_2 xs = do { 
    let c1 = 1; 
    let t1 = xs[c1 := c1];
    let b = (t1 = t1); 
    t2 \<leftarrow> if b then Some xs else do { let t2 = t1[c1 := c1]; Some t2 }; 
    Some t2 
  }"

definition create_list :: "'a::heap \<Rightarrow> 'a list option" where
  "create_list x = do { let xs = [x]; Some xs }" 

definition create_arr :: "('a::heap) list \<Rightarrow> 'a list option" where
  "create_arr xs = do { let a = New_Arr xs; Some a }"

definition create_arr_2 :: "'a::heap \<Rightarrow> 'a list option" where
  "create_arr_2 x = Some (New_Arr [x])"

definition create_arr_3 :: "'a::heap \<Rightarrow> 'b::heap \<Rightarrow> ('a list * 'b list) option" where
  "create_arr_3 a b = do { 
    let xs = New_Arr [a]; 
    let ys = New_Arr [b];
    Some (xs, ys) 
   }"

definition create_diff_arr_empty :: "('a::heap) list option" where
  "create_diff_arr_empty = Some (New_Diff_Arr [])" 

definition create_diff_arr :: "'a::heap \<Rightarrow> 'a list option" where
  "create_diff_arr x = Some (New_Diff_Arr [x])" 

definition create_diff_arr_2 ::  "'a::heap \<Rightarrow> 'a list list option" where
  "create_diff_arr_2 xs = do { 
    let a = New_Diff_Arr [xs]; let b = New_Diff_Arr [a]; Some b 
  }" 

definition create_diff_arr_3 :: "('a::heap) list option" where
  "create_diff_arr_3 = do { 
    let xs = New_Diff_Arr []; Some xs 
  }"

definition create_diff_arr_4 :: "('a::heap) \<Rightarrow> ('b::heap) \<Rightarrow> ('a list * 'b list) option" where
  "create_diff_arr_4 a b = do { 
    let xs = New_Diff_Arr [a]; 
    let ys  = New_Diff_Arr [b]; 
    Some (xs, ys)
  }"

definition create_arr_diff_arr :: "('a::heap) \<Rightarrow> 'a list option" where
  "create_arr_diff_arr xs = do { 
    let a = New_Arr [xs]; let b = New_Diff_Arr a; Some b 
  }" 

definition nested_arr_diff_arr :: "('a::heap) \<Rightarrow> 'a list option" where
  "nested_arr_diff_arr xs = do { 
    let a = New_Arr [xs]; let b = New_Diff_Arr a; Some b 
  }"              

definition case_tuple where
  "case_tuple t xs =
     (case t of (c1, c2) \<Rightarrow> do {
      let t1 = xs[c1:= c2];
      Some t1
    })"

(* HNR Array *)

synth_definition example_1_arr is [hnr_rule_arr]:     
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (example_1 xs)"
  unfolding example_1_def 
  by hnr_arr

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

(* Not all lists are converted to arrays, because they are not used linearly! *)
synth_definition return_tuple_3_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_3 xs)"
  unfolding return_tuple_3_def 
  by hnr_arr

synth_definition return_tuple_4_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (return_tuple_4 xs)"
  unfolding return_tuple_4_def
  by hnr_arr

(* Not all lists are converted to arrays, because they are not used linearly! *)
synth_definition not_linear_arr is
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (not_linear xs)"
  unfolding not_linear_def 
  by hnr_arr

synth_definition if_1_arr is [hnr_rule_arr]:
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_1 xs)"
  unfolding if_1_def 
  by hnr_arr

synth_definition if_2_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_2 xs)"
  unfolding if_2_def 
  by hnr_arr

(* Can't work, not linear! *)
synth_definition if_3_arr is
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_3 xs)"
  unfolding if_3_def 
  apply hnr_arr
  oops

synth_definition if_4_arr is [hnr_rule_arr]: 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_4 xs)"
  unfolding if_4_def 
  by hnr_arr

synth_definition if_5_arr is [hnr_rule_arr]:   
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_5 xs)"
  unfolding if_5_def 
  by hnr_arr

(* Not all lists are converted to arrays, because they are not used linearly! *)
synth_definition if_6_arr is 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_6 xs)"
  unfolding if_6_def 
  by hnr_arr

(* Can't work, not linear! *)
synth_definition if_7_arr is
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_7 xs)"
  unfolding if_7_def 
  apply hnr_arr
  oops

synth_definition tuple_list_arr is [hnr_rule_arr]:
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (tuple_list xs)"
  unfolding tuple_list_def 
  by hnr_arr

synth_definition nested_arr is 
  "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (nested xs)"
  unfolding nested_def 
  by hnr_arr

synth_definition fallback_1_arr is [hnr_rule_arr]:
    "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (fallback_1 xs)"
  unfolding fallback_1_def 
  by hnr_arr

(* TODO: Find way to deal with fallback of non id_assn stuff *)
synth_definition fallback_2_arr is [hnr_rule_arr]:
    "hnr (array_assn xs xsi) (\<hole> :: ?'a Heap) ?\<Gamma>' (fallback_2 xs)"
  unfolding fallback_2_def 
  apply hnr_arr
  apply(rule hnr_fallback)
  oops
 
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

synth_definition create_arr_3_impl is [hnr_rule_arr]:
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_arr_3 x y)"
  unfolding create_arr_3_def 
  by hnr_arr

synth_definition case_tuple_impl is [hnr_rule_arr]:
  "hnr 
    (array_assn xs xsi * id_assn t ti) 
    (\<hole> :: ?'a Heap) 
    ?\<Gamma>' 
    (case_tuple t xs)"
  unfolding case_tuple_def
  by hnr_arr

(* HNR Diff-Array *)

synth_definition example_1_diff_arr is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (example_1 xs)"
  unfolding example_1_def
  by hnr_diff_arr

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

(* TODO: Lists nested in tuples *)
synth_definition if_7_diff_arr is [hnr_rule_diff_arr]: 
    "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_7 xs)"
  unfolding if_7_def   
  apply hnr_step_diff_arr+
  oops

synth_definition tuple_list_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (tuple_list xs)"
  unfolding tuple_list_def 
  by hnr_diff_arr

synth_definition nested_diff_arr is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (nested xs)"
  unfolding nested_def 
  by hnr_diff_arr

synth_definition fallback_1_diff_arr is [hnr_rule_diff_arr]:
    "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (fallback_1 xs)"
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
  apply(rule hnr_fallback)
  oops
                                                 
synth_definition create_diff_arr_3_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr_3)"
  unfolding create_diff_arr_3_def 
  by hnr_diff_arr

synth_definition create_diff_arr_4_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_diff_arr_4 x y)"
  unfolding create_diff_arr_4_def 
  by hnr_diff_arr

synth_definition case_tuple_diff_arr_impl is [hnr_rule_arr]:
  "hnr 
    (master_assn' (insert (xs, xsi) F) * id_assn t ti) 
    (\<hole> :: ?'a Heap) 
    ?\<Gamma>' 
    (case_tuple t xs)"
  unfolding case_tuple_def
  by hnr_diff_arr

(* TODO: Do I need a combined operator? *)
synth_definition create_diff_arr_arr_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (create_arr_diff_arr x)"
  unfolding create_arr_diff_arr_def 
  apply hnr_arr
  by hnr_diff_arr

(* TODO: Nested lists *)
synth_definition nested_arr_diff_arr_impl is [hnr_rule_diff_arr]: 
  "hnr emp (\<hole> :: ?'a Heap) ?\<Gamma>' (nested_arr_diff_arr x)"
  unfolding nested_arr_diff_arr_def 
  apply hnr_arr
  oops

export_code example_1_diff_arr in SML_imp module_name example

end
