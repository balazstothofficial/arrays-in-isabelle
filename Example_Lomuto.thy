theory Example_Lomuto
  imports Hnr_Diff_Arr Hnr_Array  Definition_Utils "HOL-Library.Multiset" "HOL-Library.Rewrite"
begin

definition swap :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "swap i j xs \<equiv> (xs[i := xs!j])[j := xs!i]"
  
fun partition :: "nat \<Rightarrow> nat \<Rightarrow> ('a::linorder) list \<Rightarrow> ('a list * nat)" where
  "partition i j xs = (if 1 < j then
      (if xs ! 0 < xs ! (j - 1)
       then partition (i - 1) (j - 1) (swap (i - 1) (j - 1) xs)
       else partition i (j - 1) xs)
    else (swap (i - 1) 0 xs, i - 1)
  )"

declare partition.simps[simp del]

abbreviation partition' where
  "partition' xs \<equiv> partition (length xs) (length xs) xs"

definition inv :: "nat \<Rightarrow> nat \<Rightarrow> ('a::linorder) list \<Rightarrow> bool" where
  "inv i j xs \<equiv> 
    let p = xs ! 0 in
    0 < length xs \<and>
    0 < i \<and>
    i \<le> length xs \<and> 
    j \<le> length xs \<and> 
    j \<le> i \<and> 
   (\<forall>h \<in> set (drop i xs). p < h) \<and> 
   (\<forall>l \<in> set (take (i - j) (drop j xs)). l \<le> p)"

definition is_valid_partition where
  "is_valid_partition ys m \<equiv> \<forall>l \<in> set (take m ys). \<forall>h \<in> set (drop m ys). l \<le> h"

lemma mset_swap' [simp]:"i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> mset (swap i j xs) = mset xs"
  unfolding swap_def
  using mset_swap by auto

lemma swap_length [simp]: "length (swap i j xs) = length xs"
  unfolding swap_def
  by auto

lemma swap_pivot: "swap (Suc i) (Suc j) (p#xs) = p # (swap i j xs)"
  unfolding swap_def
  by auto

lemma swap_pivot_2: "0 < i \<Longrightarrow> 0 < j \<Longrightarrow> swap i j (p#xs) = p # (swap (i - 1) (j - 1) xs)"
  unfolding swap_def
  apply(cases i; cases j)
  by auto

lemma swap_nth_noop: "n < i \<Longrightarrow> n < j \<Longrightarrow> swap i j xs ! n = xs ! n"
  unfolding swap_def
  by auto

lemma drop_swap: "n \<le> i \<Longrightarrow> n \<le> j \<Longrightarrow> drop n (swap i j xs) = swap (i - n) (j - n) (drop n xs)"
  unfolding swap_def
  by (metis drop_eq_Nil drop_update_swap le_add_diff_inverse linorder_le_cases list_update_nonempty nth_drop)

lemma drop_swap': "\<lbrakk>
  Suc 0 < j;
  xs \<noteq> [];
  i \<le> length xs;
  j \<le> i\<rbrakk> \<Longrightarrow>
  drop (i - Suc 0) (swap (i - Suc 0) (j - Suc 0) xs) = xs ! (j - Suc 0) # (drop i xs)"
  unfolding swap_def 
  by(smt (verit, best) Cons_nth_drop_Suc One_nat_def drop_upd_irrelevant dual_order.strict_trans1 le_add_diff_inverse le_eq_less_or_eq length_list_update less_eq_Suc_le linorder_not_less nth_list_update_eq plus_1_eq_Suc)

lemma drop_swap'_2: "\<lbrakk>
  Suc 0 < j; 
  xs ! 0 < xs ! (j - Suc 0); 
  xs \<noteq> []; 
  i \<le> length xs; 
  j \<le> i\<rbrakk> \<Longrightarrow> drop (j - Suc 0) (swap (i - Suc 0) (j - Suc 0) xs) = swap (i - 1 - (j - Suc 0)) 0 (drop (j - Suc 0) xs)"
  using drop_swap[of "j - 1" "i - 1" "j - 1" xs]
  by auto

lemma test_2: "n < length xs \<Longrightarrow> drop n xs = drop n xs ! 0 # drop (Suc n) xs"
  apply auto
  by (simp add: Cons_nth_drop_Suc)

lemma test_3: "\<lbrakk>Suc 0 < j; i \<le> length xs; j \<le> i\<rbrakk>
   \<Longrightarrow> (drop (j - Suc 0) xs)[0 := xs ! (i - 1)] = xs ! (i - 1) # drop j xs"
  by (smt (verit, ccfv_SIG) Cons_nth_drop_Suc Suc_diff_le Suc_le_eq diff_Suc_Suc le_trans list_update_code(2) minus_nat.diff_0 nat_less_le)

lemma test_3_1: "\<lbrakk>Suc 0 < j; j \<le> length xs\<rbrakk> \<Longrightarrow> (drop (j - Suc 0) xs)[0 := y] = y # drop j xs"
  by (metis dual_order.refl list_update_code(2) list_update_overwrite test_3)

lemma test_3_2: "(take (i - j) (drop (j - Suc 0) xs))[0 := xs ! (i - Suc 0)] = (take (i - j) ((drop (j - Suc 0) xs)[0 := xs ! (i - Suc 0)]))"
  by simp

lemma test_4: "\<lbrakk>Suc 0 < j; i \<le> length xs; j \<le> i\<rbrakk>
   \<Longrightarrow> take (i - j) (drop (j - Suc 0) (swap (i - Suc 0) (j - Suc 0) xs)) = take (i -j) (xs ! (i - 1) # drop j xs)" 
  unfolding swap_def
  apply auto
  by (smt (z3) One_nat_def Suc_le_mono diff_Suc_Suc diff_self_eq_0 drop_update_swap dual_order.strict_trans1 le_add_diff_inverse less_or_eq_imp_le plus_1_eq_Suc take_update take_update_cancel test_3)

lemma test_5_1: "\<lbrakk>l \<in>\<^sub>L take (i - j) (xs ! (i - Suc 0) # drop j xs); l \<noteq> xs ! (i - Suc 0)\<rbrakk> \<Longrightarrow> l \<in>\<^sub>L take (i - j - 1) (drop j xs)" 
  apply auto 
  by (smt (verit) Suc_diff_Suc Suc_le_eq diff_is_0_eq less_or_eq_imp_le linorder_not_less set_ConsD take_Suc_Cons take_eq_Nil)

lemma test_5_2: "l \<in>\<^sub>L take (i - Suc j) (drop j xs) \<Longrightarrow> l \<in>\<^sub>L take (i - j) (drop j xs)" 
  by (meson Suc_n_not_le_n diff_le_mono2 nle_le set_take_subset_set_take subset_code(1))

lemma test_5: "\<lbrakk>
  xs \<noteq> [];
  Suc 0 < j; 
  i \<le> length xs; 
  j \<le> i; 
  i \<noteq> j;
  \<forall>l\<in>set (take (i - j) (drop j xs)). l \<le> xs ! 0;
  l \<in>\<^sub>L take (i - j) (xs ! (i - Suc 0) # drop j xs); 
  xs ! (i - Suc 0) \<le> xs ! 0
\<rbrakk> \<Longrightarrow> (l::'a::linorder) \<le> xs ! 0"
  apply(cases "l = xs ! (i - Suc 0)")
   apply auto
  apply(drule test_5_1)
  by(auto simp: test_5_2)

lemma test_6_1: "j < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs ! (i - Suc 0) \<in>\<^sub>L drop j xs"
  by (metis Suc_leI Suc_le_mono Suc_pred in_set_drop_conv_nth less_imp_Suc_add nz_le_conv_less zero_less_Suc)

lemma test_6: "j < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs ! (i - Suc 0) \<in>\<^sub>L take (i - j) (drop j xs)"
  using test_6_1
  by (smt (verit, ccfv_SIG) diff_less drop_take le_SucE le_zero_eq length_take less_zeroE min.absorb2 nth_take zero_induct zero_less_iff_neq_zero)

lemma test_7: "\<lbrakk>\<forall>l\<in>set xs. P l; x \<in>\<^sub>L xs\<rbrakk> \<Longrightarrow> P x"
  by simp

lemma aux_1_1: "\<lbrakk>
  Suc 0 < j;
  xs ! 0 < xs ! (j - Suc 0);
  xs \<noteq> [];
  i \<le> length xs;
  j \<le> i;
  \<forall>x\<in>set (drop i xs). xs ! 0 < x;
  x \<in>\<^sub>L drop (i - Suc 0) (swap (i - Suc 0) (j - Suc 0) xs)
\<rbrakk> \<Longrightarrow> xs ! 0 < x" 
  using drop_swap'[of j xs i]
  by auto

lemma aux_1_2: "\<lbrakk>
  Suc 0 < j; 
  xs ! 0 < xs ! (j - Suc 0); 
  xs \<noteq> []; 
  i \<le> length xs; 
  j \<le> i; 
  \<forall>l\<in>set (take (i - j) (drop j xs)). l \<le> xs ! 0;
  l \<in>\<^sub>L take (i - j) (drop (j - Suc 0) (swap (i - Suc 0) (j - Suc 0) xs))
\<rbrakk> \<Longrightarrow> (l::'a::linorder) \<le> xs ! 0"
  apply(auto simp: test_4)
  apply(cases "i = j")
   apply auto
  apply(subgoal_tac "xs ! (i - Suc 0) \<le> xs ! 0")
  using test_5[of xs]
   apply simp
  using test_6[of j i xs]
  by simp

lemma aux_2_1:  "\<lbrakk>l \<in>\<^sub>L take n xs\<rbrakk> 
  \<Longrightarrow>  l \<in>\<^sub>L take (Suc n) xs"
  apply(induction xs)
   apply auto
  by (metis lessI less_or_eq_imp_le set_ConsD set_take_subset_set_take subset_code(1) take_Suc_Cons)

lemma aux_2_2: "0 < j \<Longrightarrow> j \<le> length xs \<Longrightarrow> drop (j - Suc 0) xs =  xs ! (j - Suc 0) # drop j xs"
  by (metis Cons_nth_drop_Suc Suc_pred nz_le_conv_less)

lemma aux_3_1: "\<lbrakk>\<not> Suc 0 < j; xs \<noteq> []; 0 < i; i \<le> length xs; l \<in>\<^sub>L (take (i - Suc 0) xs)[0 := xs ! (i - Suc 0)]\<rbrakk>
   \<Longrightarrow> l \<in>\<^sub>L take (i - j) (drop j xs)" 
  by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc One_nat_def Suc_diff_Suc Suc_inject Suc_pred drop0 dual_order.strict_trans1 gr0I in_set_upd_cases list_update_code(2) set_ConsD take_Cons' take_eq_Nil2 take_update_swap test_5_2 test_6 zero_less_diff)

lemma aux_3_2: "\<lbrakk>
  \<not> Suc 0 < j; 
  (xs::('a::linorder) list) \<noteq> []; 0 < i; 
  i \<le> length xs; 
  \<forall>h \<in>set (drop i xs). xs ! 0 \<le> h
\<rbrakk> \<Longrightarrow> \<forall>h \<in>set  (drop (i - Suc 0) (xs[i - Suc 0 := xs ! 0, 0 := xs ! (i - Suc 0)])). xs ! 0 \<le> h"
  apply(cases "i = 1")
   apply auto
  subgoal for x
    apply(cases "x = xs ! 0")
     apply auto
    by (metis Cons_nth_drop_Suc drop_0 length_pos_if_in_set set_ConsD)
  by (smt (verit, best) Nat.diff_diff_eq One_nat_def Suc_diff_Suc diff_diff_cancel drop_update_swap le_add_diff_inverse less_eq_Suc_le order_le_less plus_1_eq_Suc set_ConsD test_3_1)

lemma partition: "inv i j xs \<Longrightarrow> partition i j xs = (ys, m) \<Longrightarrow> is_valid_partition ys m"
proof(induction i j xs arbitrary: ys m rule: partition.induct)
  case (1 i j xs)
  then have unfolded_partition: "(
      if Suc 0 < j
      then if xs ! 0 < xs ! (j - 1) 
           then partition (i - 1) (j - 1) (swap (i - 1) (j - 1) xs)
           else partition i (j - 1) xs
      else (swap (i - 1) 0 xs, i - 1)) = (ys, m)"
    by(simp add: partition.simps)

  have recursive_branch_1: 
    "\<lbrakk>1 < j; xs ! 0 < xs ! (j - Suc 0)\<rbrakk>
        \<Longrightarrow>  inv (i - Suc 0) (j - Suc 0) (swap (i - Suc 0) (j - Suc 0) xs)"
  using "1.prems"
  unfolding inv_def Let_def
  apply(auto simp: swap_nth_noop)
  by(auto simp: aux_1_1 aux_1_2)

  have recursive_branch_2: 
    "\<lbrakk>1 < j; \<not> xs ! 0 < xs ! (j - Suc 0)\<rbrakk> 
        \<Longrightarrow> inv i (j - Suc 0) xs"
  using "1.prems"
   unfolding inv_def Let_def
  apply auto
  subgoal for l
    apply(cases "l = xs ! (j - Suc 0)")
     apply(auto simp: aux_2_2)
    using take_Suc_Cons[of "i - j" "xs ! (j - Suc 0)"  "drop j xs"]
    by auto
  done

  have terminating_branch: 
     "\<not> Suc 0 < j \<Longrightarrow> is_valid_partition (swap (i - Suc 0) 0 xs) (i - Suc 0)"
     using "1.prems"
    unfolding inv_def Let_def is_valid_partition_def
  apply(auto)
  unfolding swap_def
  subgoal for l h
  using aux_3_1[of j xs i l] aux_3_2[of j xs i]
  apply(auto)
  by (meson order_less_imp_le order_trans)
  done

  from unfolded_partition 1 recursive_branch_1 recursive_branch_2 terminating_branch 
  show ?case
    by(auto split: if_splits)
qed

lemma inv: "inv (length (p#xs)) (length (p#xs)) (p#xs)"
  unfolding inv_def
  by auto

lemma partition': 
  "partition' (p#xs) = (ys, m) \<Longrightarrow> is_valid_partition ys m"
  using inv[of p xs] partition[of "length (p # xs)" "length (p # xs)" "p # xs" ys m]
  by auto

(* TODO: If c2 and c3 exchange then not linear anymore *)
definition swap_opt :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
  "swap_opt i j xs = do {
     let c1 = xs!j;
     let c2 = xs!i;
     let c3 = xs[i := c1];
     let c4 = c3[j := c2];
     Some c4
  }"

lemma swap_opt_termination: "swap_opt i j xs = Some (swap i j xs)"
  unfolding swap_opt_def swap_def
  by auto

synth_definition swap_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F) * id_assn i ii * id_assn j ji)(\<hole>:: ?'a Heap) ?\<Gamma>' (swap_opt i j xs)"
  unfolding swap_opt_def
  by hnr_diff_arr

synth_definition swap_impl_2 is [hnr_rule_arr]:
  "hnr (array_assn xs xsi * id_assn i ii * id_assn j ji)(\<hole>:: ?'a Heap) ?\<Gamma>' (swap_opt i j xs)"
  unfolding swap_opt_def
  by hnr_arr

definition partition_opt :: "nat \<times> nat \<times> ('a::linorder) list \<Rightarrow> (('a::linorder) list \<times> nat) option" 
  where 
    "partition_opt \<equiv> option.fixp_fun (\<lambda>partition_opt p. case p of (i, j, xs) \<Rightarrow> do {
      let c1 = 1;
      let c2 = c1 < j;
      if c2 then do {
        let c99 = 0;
        let c3 = xs ! c99;
        let c4 = 1;
        let c5 = j - c4;
        let c6 = xs ! c5;
        let c7 = c3 < c6;
        if c7 then do {
           let c8 = 1;
           let c9 = i - c8;
           let c10 = 1;
           let c11 = j - c10;
           c12 \<leftarrow> swap_opt c9 c11 xs;
           let c13 = (c9, c11, c12);
           partition_opt c13
        }
        else do {
          let c14 = 1;
          let c15 = j - c14;
          let c16 = (i, c15, xs);
          partition_opt c16
        }
      }
      else do {
        let c17 = 1;
        let c18 = i - c17;
        let c19 = 0;
        c20 \<leftarrow> swap_opt c18 c19 xs;
        Some (c20, c18)
      }
    }
   )"

schematic_goal partition_opt_unfold: "partition_opt p \<equiv> ?v"
  apply(rule gen_code_thm_option_fixp[OF partition_opt_def])
  by(partial_function_mono)

lemma partition_opt_termination: "partition_opt (i, j, xs) = Some (partition i j xs)"
  apply(induction i j xs rule: partition.induct)
  apply(rewrite partition_opt_unfold)
  apply(rewrite partition.simps)
  by(auto simp: Let_def)

context
  fixes xsi :: "('a::{linorder,heap}) cell ref"
begin

find_theorems "hnr"

thm hnr_frame[where F= emp, simplified]

lemma hnr_post_cons:
  assumes
    "hnr \<Gamma> fi \<Gamma>' f"
    "\<And>x xi. \<Gamma>' x xi \<Longrightarrow>\<^sub>A \<Gamma>'' x xi"
  shows
    "hnr \<Gamma> fi  \<Gamma>'' f"
   apply(rule hnrI)
  using hnrD[OF assms(1)] assms(2)
  apply(cases f)
   apply sep_auto+
  by (meson cons_post_rule fr_refl)

lemma hnr_recursion:
  assumes 
    mono_option: "\<And>x. mono_option (\<lambda>r. f r x)"
  and
    step: "\<And>r ri x xi F. (\<And>x' xi' F'. hnr (\<Gamma> F' x' xi') (ri xi') (\<Gamma>' F' x' xi') (r x'))
        \<Longrightarrow> hnr (\<Gamma> F x xi) (fi ri xi) (\<Gamma>' F x xi) (f r x)"
  and
    mono_heap: "\<And>x. mono_Heap (\<lambda>r. fi r x)"
  shows  
    "hnr (\<Gamma> F x xi) (heap.fixp_fun fi xi) (\<Gamma>' F x xi) (option.fixp_fun f x)"
proof(induction arbitrary: x xi F rule: ccpo.fixp_induct[OF option.ccpo])
  case 1
  then show ?case 
    apply(rule admissible_fun)
    by(rule admissible_flat)
next
  case 2
  then show ?case 
    using mono_option 
    by(simp add: monotone_def fun_ord_def)
next
  case 3
  then show ?case 
    by simp
next
  case 4
  then show ?case 
    apply(subst heap.mono_body_fixp[OF mono_heap])
    apply(rule step).
qed


synth_definition partition_impl is [hnr_rule_diff_arr]:
  "hnr (master_assn' (insert (xs, xsi) F) * id_assn i ii * id_assn j ji)(\<hole>:: ?'a Heap) ?\<Gamma>' (partition_opt (i, j, xs))" 
  unfolding partition_opt_def
  apply(rule hnr_frame)
   apply(rule hnr_recursion[where 
        xi = "(_, _, _)" and
        \<Gamma> = "(\<lambda>F (p::nat \<times> nat \<times> 'a list) (pi:: nat \<times> nat \<times> 'a cell ref). 
              master_assn' (insert (snd(snd p), snd (snd pi)) F) * id_assn (fst p) (fst pi) *  id_assn (fst (snd p)) (fst (snd pi)))" and
         \<Gamma>' = "(\<lambda>F (p::nat \<times> nat \<times> 'a list) (pi:: nat \<times> nat \<times> 'a cell ref) (r::'a list \<times> nat) (ri:: 'a cell ref \<times> nat). 
              master_assn' (insert (snd(snd p), snd (snd pi)) (insert (fst r, fst ri) F)) * 
              id_assn (snd r) (snd ri) *
              id_assn (fst p) (fst pi) *
              id_assn (fst (snd p)) (fst (snd pi)) * true
              )"
        ]
      )
     prefer 4
     apply(simp only: fst_conv snd_conv)
  apply(hnr_frame_inference hnr_diff_arr_match_atom)
    apply hnr_diff_arr      
  apply(rule hnr_post_cons)
  unfolding split_def
   apply hnr_diff_arr
        apply(hnr_diff_arr | rule hnr_fallback; extract_pre rule: models_id_assn; simp; fail)+
                     apply simp
                     apply(hnr_diff_arr | rule hnr_fallback; extract_pre rule: models_id_assn; simp; fail)+
       apply simp
       apply(hnr_diff_arr | rule hnr_fallback; extract_pre rule: models_id_assn; simp; fail)+
   apply(simp only: star_aci insert_commute)
   apply(rule ent_refl)
  by hnr_diff_arr      

  find_theorems "insert _ (insert _ _) = _"
    (* method normalize =
  rule normI, (simp only: star_aci)?; rule ent_refl *)
   apply(rule hnr_fallback)
        apply(extract_pre rule: models_id_assn)
        apply simp
       apply hnr_diff_arr
   apply(rule hnr_fallback)
  apply(extract_pre rule: models_id_assn)
                  apply simp
                 apply hnr_diff_arr
   apply(rule hnr_fallback)
  apply(extract_pre rule: models_id_assn)
  apply simp
                      apply(hnr_diff_arr | rule hnr_fallback; extract_pre rule: models_id_assn; simp; fail)+
                      apply(rule hnr_frame)
                      apply(assumption)
                      apply(frame_prepare)
                      apply(frame_try_match hnr_diff_arr_match_atom)
                      apply(frame_try_match hnr_diff_arr_match_atom)

  thm split_def
  find_theorems "case_prod" "fst" "snd"
  sorry

(* 
rule hnr_frame, assumption, hnr_frame_inference \<open>rule ent_refl\<close>


apply(frame_prepare)
     apply(frame_try_match hnr_diff_arr_match_atom)
     apply(rule frame_no_match)
  apply(rule frame_no_match)
     apply(rule frame_match)
      apply(rule master_assn'_cong)
      apply(si_initialize)
  apply(si_try_match)
  apply(set_inference)
  apply(rule ent_refl)
  apply(hnr_diff_arr_match_atom)
  apply(frame_try_match hnr_diff_arr_match_atom)
  apply(hnr_frame_inference_dbg hnr_diff_arr_match_atom)


method si_initialize = rule si_initialize, (simp(no_asm) only: si_move_tag)?

method set_inference_keep = si_initialize, ((rule si_finish | si_try_match)+)?

method set_inference = set_inference_keep; fail
*)


definition triple_case ::  "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list option" where 
  "triple_case i j xs = do {
     let c1 = (i, j, xs);
     case c1 of (ii, ji, xsi) \<Rightarrow> Some xsi
  }"

definition triple_case_2 ::  "(nat \<times> nat \<times> 'a list) \<Rightarrow> 'a list option" where 
  "triple_case_2 p = do {
     case p of (ii, ji, xsi) \<Rightarrow> Some xsi
  }"

lemma hnr_case_tuple_special [hnr_rule]:
  assumes 
    "\<And>i ii j ji xs xsi. 
      hnr 
        (master_assn' (insert (snd (snd x), snd (snd xi)) (insert (xs, xsi) F)) *
            id_assn (fst (snd x)) (fst (snd xi)) *
            id_assn (fst x) (fst xi) *
            id_assn i ii *
            id_assn j ji *
            \<Gamma>1 *  \<Gamma>2 *  \<Gamma>3 *  \<Gamma>4)
        (ci ii ji xsi)
        (\<Gamma>\<^sub>a i ii j ji xs xsi)
        (c i j xs)"
    "\<And>i ii j ji xs xsi ri r. Keep_Drop (\<Gamma>\<^sub>a i ii j ji xs xsi r ri) (\<Gamma>\<^sub>a' r ri) (\<Gamma>Drop i ii j ji xs xsi r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>a' r ri) (\<Gamma>\<^sub>a'' r ri)"
  shows
    "hnr (
      master_assn' (insert (snd (snd x), snd (snd xi)) F) *
            (id_assn (fst (snd x)) (fst (snd xi)) *
            id_assn (fst x) (fst xi) *
            \<Gamma>1 *  \<Gamma>2 *  \<Gamma>3 *  \<Gamma>4))
    (case xi of (i, j, xs) \<Rightarrow> ci i j xs) \<Gamma>\<^sub>a'' (case x of (i, j, xs) \<Rightarrow> c i j xs)"
  apply(hnr_cases_prepare splits: prod.splits)
  using assms(2, 3)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)  

lemma hnr_case_tuple_special_2 [hnr_rule]:
  assumes 
    "\<And>i ii j ji xs xsi. 
      hnr 
        (master_assn' (insert (snd (snd x), snd (snd xi)) (insert (xs, xsi) F)) *
            id_assn (fst (snd x)) (fst (snd xi)) *
            id_assn (fst x) (fst xi) *
            id_assn i ii *
            id_assn j ji) 
        (ci ii ji xsi)
        (\<Gamma>\<^sub>a i ii j ji xs xsi)
        (c i j xs)"
    "\<And>i ii j ji xs xsi ri r. Keep_Drop (\<Gamma>\<^sub>a i ii j ji xs xsi r ri) (\<Gamma>\<^sub>a' r ri) (\<Gamma>Drop i ii j ji xs xsi r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>a' r ri) (\<Gamma>\<^sub>a'' r ri)"
  shows
    "hnr (
      master_assn' (insert (snd (snd x), snd (snd xi)) F) *
            id_assn (fst (snd x)) (fst (snd xi)) *
            id_assn (fst x) (fst xi)) 
    (case xi of (i, j, xs) \<Rightarrow> ci i j xs) \<Gamma>\<^sub>a'' (case x of (i, j, xs) \<Rightarrow> c i j xs)"
  apply(hnr_cases_prepare splits: prod.splits)
  using assms(2, 3)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)  

synth_definition triple_case_impl is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (xs, xsi) F) * id_assn i ii * id_assn j ji) (\<hole> :: ?'a Heap) ?\<Gamma>' (triple_case i j xs)"
  unfolding triple_case_def
  by hnr_diff_arr
  (* apply(rule hnr_case_tuple_special[of _ _ "insert (xs, xsi) F" "id_assn i ii" "id_assn j ji" "true" "true" _ _ "\<lambda>_ _ xs. Some xs"]) *)

synth_definition triple_case_2_impl is [hnr_rule_diff_arr]: 
  "hnr (master_assn' (insert (snd(snd p), snd(snd pi)) F) * id_assn (fst (snd p)) (fst (snd pi)) * id_assn (fst p) (fst pi)) (\<hole> :: ?'a Heap) ?\<Gamma>' (triple_case_2 p)"
  unfolding triple_case_2_def
  (* apply(rule hnr_case_tuple_special_2[of p pi F _ _ "\<lambda>j k xs. Some xs"]) *)
  by hnr_diff_arr

end

end
