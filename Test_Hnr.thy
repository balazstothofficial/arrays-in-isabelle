theory Test_Hnr
  imports Hnr_Diff_Arr Hnr_Array "HOL-Library.Code_Target_Nat" 
begin

definition test1 where
  "test1 xs = 
    (let c1 = (let x = 1 in x); c2 = 2; c3 = 3; t1 = xs[c1 := c2]; t2 = t1[c1 := c3]; t3 = t2 ! c2 in t3)"

definition test2 where
  "test2 xs = 
    (let c1 = 1; t1 = xs[c1 := c1] in t1)"

definition test2_1 where
  "test2_1 xs = 
    (let c1 = 1; t1 = xs[c1 := c1] in (c1, t1))"

definition test2_2 where
  "test2_2 xs = 
    (let c1 = 1; t1 = xs; t2 = xs[c1 := c1] in (t1, t2))"

definition test2_3 where
  "test2_3 xs = 
    (let c1 = 1; c2 = 2 in (c1, c2))"

definition test3 where
  "test3 xs = 
    (let c1 = 1; t1 = xs[c1 := c1]; t2 = xs ! c1 in t1)"

definition test4 where
  "test4 xs =
    (let c1 = 1; t1 = if xs = [] then xs else let t2 = xs[c1 := c1] in t2 in t1)"

definition test4_2 where
  "test4_2 xs =
    (let c1 = 1; t1 = if xs = [] then xs else let t1 = xs[c1 := c1]; t2 = t1[c1:= c1] in t2 in t1)"

definition test4_3 where
  "test4_3 xs =
    (let c1 = 1; t1 = if xs = [] then let c2 = 2; t1 = xs[c2 := c2]; t2 = t1[c2:= c2] in xs else let t1 = xs[c1 := c1]; t2 = t1[c1:= c1] in t2 in t1)"

(* TODO: What to do if the bool depends on local variables? *)
definition test5 where
  "test5 xs = 
    (let c1 = 1; t1 = if c1 = 0 then xs else xs[c1 := c1] in t1)"

(* TODO: I need this form but need to find a way for comparisons *)
definition test5_1 where
  "test5_1 xs = 
    (let c1 = 1; b = (c1 = c1); t1 = if b then xs else xs[c1 := c1] in t1)"

definition test6 where
  "test6 xs = 
    (let c1 = 1; c2 = 2; t1 = if xs = [] then xs[c2 := c2] else xs[c1 := c1] in t1)"

definition test7 where
  "test7 xs = 
    (let c1 = 1; c2 = 2; t1 = if xs = [] then let t2 = xs[c2 := c2]; t3 = xs[c1 := c1] in t3 else let t2 = xs[c1 := c1]; t3 = xs[c2 := c1] in t3 in t1)"


schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test1 xs)"
  unfolding test1_def 
  apply hnr_arr
  done

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test2 xs)"
  unfolding test2_def 
  apply hnr_arr
  done  

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test2_1 xs)"
  unfolding test2_1_def 
  apply hnr_arr
  done  

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test2_3 xs)"
  unfolding test2_3_def 
  apply hnr_arr
  done  

(* Can't work, not linear! *)
schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' (test3 xs)"
  unfolding test3_def 
  apply hnr_arr
  sorry

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test1 xs)"
  unfolding test1_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test2 xs)"
  unfolding test2_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test2_1 xs)"
  unfolding test2_1_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test2_2 xs)"
  unfolding test2_2_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c :: ?'a Heap) ?\<Gamma>' (test2_3 xs)"
  unfolding test2_3_def
  apply hnr_diff_arr
  done

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test3 xs)"
  unfolding test3_def
  apply hnr_diff_arr
  done  

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test4 xs)"
  unfolding test4_def
  sorry
  (* apply hnr_diff_arr
     apply (rule hnr_if)
      apply hnr_diff_arr
  subgoal sorry
  subgoal 
    apply(rule merge_if_2)
    apply hnr_diff_arr
  sorry *)

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test4_2 xs)"
  unfolding test4_2_def
  apply hnr_diff_arr
  apply or_match 
  apply or_match 
  apply or_match 
  apply(hnr_extract_pure -)
  subgoal sorry       
  subgoal sorry
  subgoal sorry
  sorry
  (* apply hnr_diff_arr

     apply (rule hnr_if)
      apply hnr_diff_arr
  apply simp
    apply(rule merge_if_2)
    apply hnr_diff_arr
  done *)

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test4_3 xs)"
  unfolding test4_3_def
  apply hnr_diff_arr
  apply or_match+
  subgoal sorry       
  subgoal sorry
  subgoal sorry
  sorry

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test5_1 xs)"
  unfolding test5_1_def
  
  sorry

schematic_goal "hnr (master_assn t * \<up>(t \<turnstile> xs \<sim> xsi)) (?c xsi :: ?'a Heap) (?\<Gamma>' xsi xs) (test7 xs)"
  unfolding test7_def
  apply hnr_diff_arr
  apply or_match+
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  sorry

(* 
  Questions/Notes: 
  - Wouldn't it be more useful to always build up the master_assn instead of using existensials?
  - How to integrate standard operations like + and -? Bool ops? Simple function call? 
  - How to integrate Annotations?
*)


export_code array_nth_safe array_update_safe in SML_imp

end
