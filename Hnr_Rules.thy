theory Hnr_Rules
  imports Hnr_Base Keep_Drop Norm Merge
begin

lemma hnr_tuple [hnr_rule]: 
  assumes
    "hnr \<Gamma> ai \<Gamma>\<^sub>a (Some a)"
    "\<And>a ai. hnr (\<Gamma>\<^sub>a a ai * true) bi (\<Gamma>\<^sub>b a ai) (Some b)"
  shows 
    "hnr 
      \<Gamma>
      (do { ai' \<leftarrow> ai; bi' \<leftarrow> bi; return (ai', bi') })
      (\<lambda>x xi. \<Gamma>\<^sub>b (fst x) (fst xi) (snd x) (snd xi))
      (Some (a, b))"
  apply(rule hnrI)
  using assms[THEN hnrD]
  by sep_auto

lemma hnr_bind [hnr_rule]:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 v" 
    "\<And>x xi. hnr (\<Gamma>\<^sub>1 x xi) (fi xi) (\<Gamma>' x xi) (f x)"
    "\<And>x xi r ri. Keep_Drop (\<Gamma>' x xi r ri) (\<Gamma>'' r ri) (\<Gamma>\<^sub>1' x xi r ri)"
    "\<And>r ri. Norm (\<Gamma>'' r ri) (\<Gamma>''' r ri)" 
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>''' (do { x \<leftarrow> v; f x })"
  supply[sep_heap_rules] = assms(1, 2)[THEN hnrD]
  apply(rule hnrI)
  apply(sep_auto split: option.splits Option.bind_splits(2))
  apply(sep_drule r: assms(3)[unfolded Keep_Drop_def])
  apply(sep_drule r: assms(4)[unfolded Norm_def])
  by sep_auto

lemma hnr_if [hnr_rule]: 
  assumes
    "hnr (\<Gamma> * id_assn c ci) ai \<Gamma>\<^sub>a a"
    "hnr (\<Gamma> * id_assn c ci) bi \<Gamma>\<^sub>b b"
    "\<And>r ri. Merge (\<Gamma>\<^sub>a r ri) (\<Gamma>\<^sub>b r ri) (\<Gamma>\<^sub>c r ri)"
  shows 
    "hnr 
      (\<Gamma> * id_assn c ci)
      (if ci then ai else bi) 
      \<Gamma>\<^sub>c 
      (if c then a else b)" 
  apply(rule hnrI)
  using assms(1, 2)[THEN hnrD] assms(3)
  unfolding Merge_def
  apply(sep_auto simp: ent_star_mono id_rel_def split: if_splits)
  by(meson cons_post_rule ent_disjI1 ent_disjI2 fr_refl)+

(* TODO:
  - Is it possible to generalize that it works with every case distinction?
  - Find a way to make case distinctions also work if they are on a refined type/ a type that
    contains a refined type
*)

(* TODO: 
  Just temporary solution to at least avoid code duplication
  If generalization is not possible make this nicer
*) 

(* Precondition: Goal + Merge *)
method hnr_cases_prepare uses splits =
  rule hnrI,
  sep_auto simp: id_rel_def Merge_def split: splits

(* Precondition: Result of prepare + Keep_drop + Simp *)
method hnr_cases_solve_case uses case_hnr ent_disjI =  
    rule cons_post_rule,
    rule fi_rule,
    rule case_hnr[THEN hnrD],
    (sep_auto simp: Keep_Drop_def Norm_def id_rel_def)+,
    meson ent_disjI ent_refl_true ent_trans ent_true_drop(1)

lemma hnr_case_tuple [hnr_rule]:
  assumes 
    "\<And>a ai b bi. 
      hnr 
        (\<Gamma> * id_assn x xi * id_assn a ai * id_assn b bi) 
        (ci ai bi)
        (\<Gamma>\<^sub>a a ai b bi)
        (c a b)"
    "\<And>a ai b bi ri r. Keep_Drop (\<Gamma>\<^sub>a a ai b bi r ri) (\<Gamma>\<^sub>a' r ri) (\<Gamma>Drop a ai b bi r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>a' r ri) (\<Gamma>\<^sub>a'' r ri)"
  shows
    "hnr (\<Gamma> * id_assn x xi) (case xi of (ai, bi) \<Rightarrow> ci ai bi) \<Gamma>\<^sub>a'' (case x of (a, b) \<Rightarrow> c a b)"
  apply(hnr_cases_prepare splits: prod.splits)
  using assms(2, 3)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)

lemma hnr_case_sum [hnr_rule]:
  assumes 
    "\<And>s' si'. hnr (\<Gamma> * id_assn s si * id_assn s' si') (cli si') (\<Gamma>\<^sub>a s' si') (cl s')"
    "\<And>l' li' ri r. Keep_Drop (\<Gamma>\<^sub>a l' li' r ri) (\<Gamma>\<^sub>a' r ri) (Drop\<^sub>a l' li' r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>a' r ri) (\<Gamma>\<^sub>a'' r ri)" 

    "\<And>s' si'. hnr (\<Gamma> * id_assn s si * id_assn s' si') (cri si') (\<Gamma>\<^sub>b s' si') (cr s')"
    "\<And>r' ri' ri r. Keep_Drop (\<Gamma>\<^sub>b r' ri' r ri) (\<Gamma>\<^sub>b' r ri) (Drop\<^sub>b r' ri' r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>b' r ri) (\<Gamma>\<^sub>b'' r ri)" 

    "\<And>r ri. Merge (\<Gamma>\<^sub>a'' r ri) (\<Gamma>\<^sub>b'' r ri) (\<Gamma>\<^sub>c r ri)"
  shows
    "hnr 
      (\<Gamma> * id_assn s si)
      (case si of Inl l \<Rightarrow> cli l | Inr r \<Rightarrow> cri r)
       \<Gamma>\<^sub>c 
      (case s of Inl l \<Rightarrow> cl l | Inr r \<Rightarrow> cr r)"
  using assms(7)
  apply -
  apply(hnr_cases_prepare splits: sum.splits)
  
  using assms(2, 3)
  apply -
  apply(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)

  using assms(5, 6)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(4) ent_disjI: ent_disjI2)

lemma hnr_case_nat[hnr_rule]:
  assumes 
    "hnr (\<Gamma> * id_assn n ni) ci0 \<Gamma>\<^sub>a c0"

    "\<And>n' ni'. hnr (\<Gamma> * id_assn n ni * id_assn n' ni') (ci ni') (\<Gamma>\<^sub>b n' ni') (c n')"
    "\<And>n ni ri r. Keep_Drop (\<Gamma>\<^sub>b n ni r ri) (\<Gamma>\<^sub>b' r ri) (Drop n ni r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>b' r ri) (\<Gamma>\<^sub>b'' r ri)" 

    "\<And>r ri. Merge (\<Gamma>\<^sub>a r ri) (\<Gamma>\<^sub>b'' r ri) (\<Gamma>\<^sub>c r ri)"
  shows
    "hnr 
      (\<Gamma> * id_assn n ni)
      (case ni of 0 \<Rightarrow> ci0 | Suc n' \<Rightarrow> ci n') 
      \<Gamma>\<^sub>c 
      (case n of 0 \<Rightarrow> c0 | Suc n' \<Rightarrow> c n')"
  using assms(5)
  apply -
  apply(hnr_cases_prepare splits: nat.splits)
  
  apply(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)

  using assms(3, 4)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(2) ent_disjI: ent_disjI2)

lemma hnr_case_list [hnr_rule]:
  assumes 
    "hnr (\<Gamma> * id_assn xs xsi) ci0 \<Gamma>\<^sub>a c0"

    "\<And>x' xi' xs' xsi'. 
      hnr 
        (\<Gamma> * id_assn xs xsi * id_assn x' xi' * id_assn xs' xsi') 
        (ci xi' xsi')
        (\<Gamma>\<^sub>b x' xi' xs' xsi')
        (c x' xs')"
    "\<And>x xi xs xsi ri r. Keep_Drop (\<Gamma>\<^sub>b x xi xs xsi r ri) (\<Gamma>\<^sub>b' r ri) (Drop x xi xs xsi r ri)"
    "\<And>r ri. Norm (\<Gamma>\<^sub>b' r ri) (\<Gamma>\<^sub>b'' r ri)"

    "\<And>r ri. Merge (\<Gamma>\<^sub>a r ri) (\<Gamma>\<^sub>b'' r ri) (\<Gamma>\<^sub>c r ri)"
  shows
    "hnr 
      (\<Gamma> * id_assn xs xsi) 
      (case xsi of [] \<Rightarrow> ci0 | x#xs \<Rightarrow> ci x xs) 
      \<Gamma>\<^sub>c 
      (case xs of [] \<Rightarrow> c0 | x#xs \<Rightarrow> c x xs)"
  using assms(5)
  apply -
  apply(hnr_cases_prepare splits: nat.splits)
  
  apply(hnr_cases_solve_case case_hnr: assms(1) ent_disjI: ent_disjI1)

  using assms(3, 4)
  apply -
  by(hnr_cases_solve_case case_hnr: assms(2) ent_disjI: ent_disjI2)

end
