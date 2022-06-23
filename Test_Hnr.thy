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
                       t2 = t1[c1:= c1] 
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



definition test where
  "test xs = (let c1 = 1; c2 = (c1, c1); t1 = xs[c1 := c2] in t1)"

definition test_2 where
  "test_2 xs = (let c1 = 1; t1 = xs[c1 := c1] in if_7 t1)"

definition fallback_1 where
  "fallback_1 xs = 
    (let c1 = 1; b = (c1 = c1); t1 = if b then xs else xs[c1 := c1] in t1)"

definition create_list where
  "create_list x = [x]" 

definition create_arr where
  "create_arr xs = New_Arr [xs]"

definition create_diff_arr_empty where
  "create_diff_arr_empty = New_Diff_Arr []" 

definition create_diff_arr where
  "create_diff_arr x = New_Diff_Arr [x]" 

definition create_diff_arr_2 where
  "create_diff_arr_2 xs = (let a = New_Diff_Arr [xs]; b = New_Diff_Arr [a] in b)" 

definition create_diff_arr_3 where
  "create_diff_arr_3 = (let xs = New_Diff_Arr [] in xs)"

definition create_arr_diff_arr where
  "create_arr_diff_arr xs = (let a = New_Arr [xs]; b = Diff_Arr_From_Arr a in b)" 

definition case_tuple where
  "case_tuple x = (case x of (x1, x2) \<Rightarrow> let c = x2 in x1)"

definition case_nat where
  "case_nat n = (case n of 
                        0 \<Rightarrow> let xs = New_Diff_Arr [] in xs 
                  | Suc n \<Rightarrow> let xs = New_Diff_Arr [] in xs)"

(* HNR Array *)

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (sequential_1 xs)"
  unfolding sequential_1_def 
  by hnr_arr

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (sequential_2 xs)"
  unfolding sequential_2_def 
  by hnr_arr


schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_1 xs)"
  unfolding return_tuple_1_def
  by hnr_arr

lemma tuple_simp: "(let x = (a, b) in f x) = (let x1 = a; x2 = b in f (x1, x2))"
  by simp
 
lemma hnr_t:
  assumes "hnr \<Gamma> pi \<Gamma>' (fst p, snd p)"
  shows "hnr \<Gamma> pi \<Gamma>' p"
  using assms 
  by auto

(* TODO: *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_4 xs)"
  unfolding return_tuple_4_def
  by hnr_arr

lemma hnr_tuple_2: 
  shows 
    "hnr 
      (A a ai * B b bi)
      (return (ai, bi))
      (\<lambda> p pi. A (fst p) (fst pi) * B (snd p) (snd pi))
      (a, b)"
  apply(rule hnrI)
  by sep_auto

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_2 xs)"
  unfolding return_tuple_2_def
  by hnr_arr

(* Can't work, not linear! *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_3 xs)"
  unfolding return_tuple_3_def 
  apply hnr_arr
  oops  

(* Can't work, not linear! *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (not_linear xs)"
  unfolding not_linear_def 
  apply hnr_arr
  oops 

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_1 xs)"
  unfolding if_1_def 
  by hnr_arr

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_2 xs)"
  unfolding if_2_def 
  by hnr_arr

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_3 xs)"
  unfolding if_3_def 
  by hnr_arr

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_4 xs)"
  unfolding if_4_def 
  by hnr_arr

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_5 xs)"
  unfolding if_5_def 
  by hnr_arr

(* TODO: There is something wrong here *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_6 xs)"
  unfolding if_6_def 
  by hnr_arr

(* TODO: There is something wrong here *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (if_7 xs)"
  unfolding if_7_def 
  by hnr_arr

(* TODO: Why does this work ? *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (fallback_1 xs)"
  unfolding fallback_1_def 
  by hnr_arr

(* TODO *)
schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_list x)"
  unfolding create_list_def 
  by hnr_arr

(* TODO *)
schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_arr x)"
  unfolding create_arr_def 
  by hnr_arr

(* TODO *)
schematic_goal "hnr (id_assn x xi) (?c :: ?'a Heap) ?\<Gamma>' (case_tuple x)"
  unfolding case_tuple_def
  by hnr_arr

(* TODO *)
schematic_goal "hnr (id_assn x xi) (?c :: ?'a Heap) ?\<Gamma>' (case_nat x)"
  unfolding case_nat_def
  by hnr_arr

(* HNR Diff-Array *)

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (test xs)"
  unfolding test_def 
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (sequential_1 xs)"
  unfolding sequential_1_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (sequential_2 xs)"
  unfolding sequential_2_def
  thm hnr_let
  by hnr_diff_arr

schematic_goal "hnr(master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_1 xs)"
  unfolding return_tuple_1_def
  by hnr_diff_arr

(* TODO: Why is there no assn afterwards? *)
schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_2 xs)"
  unfolding return_tuple_2_def 
  by hnr_diff_arr
    

find_theorems "hnr _ (return _) _ _ "


(* TODO: Why is there no assn afterwards? *)
schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (return_tuple_3 xs)"
  unfolding return_tuple_3_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (not_linear xs)"
  unfolding not_linear_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (if_1 xs)"
  unfolding if_1_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (if_2 xs)"
  unfolding if_2_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (if_3 xs)"
  unfolding if_3_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (if_4 xs)"
  unfolding if_4_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (if_5 xs)"
  unfolding if_5_def 
  by hnr_diff_arr

schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (if_6 xs)"
  unfolding if_6_def 
  by hnr_diff_arr

(* TODO: We don't want an id_assn for the tuple, right? *)
synth_definition if_7_impl is [hnr_rule_diff_arr]: 
    "hnr (master_assn' (insert (xs, xsi) F)) (\<hole> :: ?'a Heap) ?\<Gamma>' (if_7 xs)"
  unfolding if_7_def   
  apply hnr_diff_arr
  done

print_theorems

thm hnr_rule_diff_arr

schematic_goal "hnr (master_assn' (insert (xs, xsi) F)) (?c :: ?'a Heap) ?\<Gamma>' (test_2 xs)"
  unfolding test_2_def
  apply hnr_diff_arr
  done

(* TODO: *)
schematic_goal "hnr (master_assn' {(xs, xsi)}) (?c :: ?'a Heap) ?\<Gamma>' (fallback_1 xs)"
  unfolding fallback_1_def 
  by hnr_diff_arr

schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_list x)"
  unfolding create_list_def 
  by hnr_diff_arr

(* TODO: Doesn't seem to work correctly anymore *)
schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_diff_arr_empty)"
  unfolding create_diff_arr_empty_def 
  by hnr_diff_arr

(* TODO: Doesn't seem to work correctly anymore *)
schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_diff_arr x)"
  unfolding create_diff_arr_def 
  by hnr_diff_arr

schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_diff_arr_2 x)"
  unfolding create_diff_arr_2_def 
  by hnr_diff_arr
                                                 
schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_diff_arr_3)"
  unfolding create_diff_arr_3_def 
  by hnr_diff_arr

(* TODO: This worked before ^^ - Do I need a combined operator? *)
schematic_goal "hnr emp (?c :: ?'a Heap) ?\<Gamma>' (create_arr_diff_arr x)"
  unfolding create_arr_diff_arr_def 
  apply hnr_arr
  sorry

schematic_goal "hnr (id_assn x xi) (?c :: ?'a Heap) ?\<Gamma>' (case_tuple x)"
  unfolding case_tuple_def
  by hnr_diff_arr

schematic_goal "hnr (id_assn x xi) (?c :: ?'a Heap) ?\<Gamma>' (case_nat x)"
  unfolding case_nat_def
  by hnr_diff_arr


export_code array_nth_safe array_update_safe in SML_imp

end
