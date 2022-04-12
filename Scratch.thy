theory Scratch
  imports Main "Separation_Logic_Imperative_HOL.Sep_Main" "Deriving.Derive" "HOL-Library.Code_Target_Nat"
begin

(**

   'a cell = Array 'a array | Upd nat 'a ('a cell ref)

   'a la = 'a cell ref ref

*)
find_consts "_ set" name: fold
find_theorems "Finite_Set.fold _ _ (insert _ _)"
find_theorems "comp_fun_commute_on" "Finite_Set.fold"


interpretation mf: comp_fun_commute_on UNIV "((*)::_::comm_monoid_mult \<Rightarrow> _)"
  apply(unfold_locales)
  by(auto simp: algebra_simps)


definition fold_assn :: "assn list \<Rightarrow> assn" where
  "fold_assn assns = foldr (*) assns emp"

lemma fold_assn_emp[simp]: "fold_assn [] = emp"
  unfolding fold_assn_def
  by simp

lemma fold_assn_cons[simp]: "fold_assn (x#xs) = x * fold_assn xs"
  unfolding fold_assn_def
  by(simp_all)

lemma fold_assn_app [simp]: "fold_assn (xs@ys) = fold_assn xs * fold_assn ys"
  apply(induction xs)
  by(auto simp: algebra_simps)

lemma fold_assn_remove1: "List.member xs x \<Longrightarrow> fold_assn xs = x * fold_assn (remove1 x xs)"
  unfolding member_def
  apply(induction xs)
  by(auto simp: algebra_simps)

lemma fold_assn_false [simp]: "List.member xs false \<Longrightarrow> fold_assn xs = false"
  using fold_assn_remove1
  by auto

lemma fold_assn_emp_remove1: "fold_assn xs = fold_assn (remove1 emp xs)"
  apply(induction xs)
  by auto

lemma fold_assn_emp_removeAll: "fold_assn xs = fold_assn (removeAll emp xs)"
  apply(induction xs)
  by auto  

(*
definition fold_assn :: "assn set \<Rightarrow> assn" where
  "fold_assn assns = Finite_Set.fold (*) emp assns * \<up>(finite assns)"

lemma fold_assn_emp [simp]: "fold_assn {} = emp"
  unfolding fold_assn_def
  by simp

lemma fold_assn_false: "false \<in> S \<Longrightarrow> fold_assn S = false"
  unfolding fold_assn_def
  apply(cases "finite S")
  by(auto simp: mf.fold_rec)

lemma fold_assn_emp': "emp \<in> S \<Longrightarrow> fold_assn S = fold_assn (S - {emp})"
  unfolding fold_assn_def
  apply(cases "finite S")
  by(auto simp: mf.fold_rec)

thm  mf.fold_insert_remove
*)
lemma fold_assn_cons [simp]: "fold_assn (insert x xs) = x * fold_assn (xs - {x})"
  unfolding fold_assn_def
  apply(cases "finite xs")
  by(simp_all add: mf.fold_insert_remove)

lemma fold_assn_in: "x \<in> xs \<Longrightarrow> fold_assn xs = x * fold_assn (xs - {x})"
  by (metis fold_assn_cons insert_absorb)
*)

(*lemma fold_assn_app: "fold_assn (xs \<union> ys) = fold_assn xs * fold_assn ys"
  apply(induction xs)
  by(auto simp: algebra_simps)*)

datatype 'a::"countable" cell = Array "'a array" | Upd nat "'a" "'a cell ref"

derive countable cell

instance cell :: (heap) heap
   by standard

type_synonym 'a la = "'a cell ref"

datatype 'a::"countable" cell' = Array' "'a list" | Upd' nat "'a" "'a cell ref"

no_notation Ref.update ("_ := _" 62)
notation Ref.update ("_ :=\<^sub>R _" 62)

fun cell_assn where
  "cell_assn (Array' xs) (Array a) = a \<mapsto>\<^sub>a xs"
| "cell_assn (Upd' i' val' p') (Upd i val p) = \<up>(i = i' \<and> val = val' \<and> p = p')"
| "cell_assn _ _ = false"

(* remove1 *)


definition master_assn :: "('a cell ref * 'a::heap cell') list \<Rightarrow> assn" where
  "master_assn C = fold_assn (map (\<lambda>(p, c'). \<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) C)"


(*lemma test: "(p, c) \<in> Map.graph C \<Longrightarrow> Map.graph C - { (p, c) } =  Map.graph (C (p := None))"
  by (metis (mono_tags, lifting) Diff_insert_absorb fun_upd_same fun_upd_triv graph_map_upd in_graphD option.simps(3))

lemma test_2: "\<lbrakk>
    inj_on f (Map.graph C); (k, v) \<in> Map.graph C; 
    (k', v') \<in> Map.graph (C(k := None)); 
    f (k', v') = f (k, v)
\<rbrakk> \<Longrightarrow> False"
  by (metis Diff_iff inj_on_contraD singletonI test)

lemma test_3: "\<lbrakk>inj_on f (Map.graph C); (k, v) \<in> Map.graph C\<rbrakk>
   \<Longrightarrow> f ` Map.graph C - { f (k, v) } = f ` Map.graph (C(k := None))"
  apply(auto)
  apply (metis image_eqI insert_Diff insert_iff test)
  apply (metis DiffE rev_image_eqI test)
  by (meson test_2)

lemma test_5_1: "(cell_assn x z = cell_assn y z \<Longrightarrow> x = y) \<Longrightarrow> (cell_assn x = cell_assn y \<Longrightarrow> x = y)"
  by auto

lemma test21: "\<lbrakk>h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c; h \<Turnstile> aa \<mapsto>\<^sub>r ca * cell_assn ba ca\<rbrakk> \<Longrightarrow> a = aa"
  unfolding sngr_assn_def
  apply(induction b c rule: cell_assn.induct)
     apply auto
   apply(induction ba ca rule: cell_assn.induct)
      apply auto
    apply(induction a; induction aa)
    apply auto
  unfolding snga_assn_def
    apply(induction h)
  apply auto   
  sorry

lemma test20: "(\<exists>c. h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c) = (\<exists>c. h \<Turnstile> aa \<mapsto>\<^sub>r c * cell_assn ba c)
   \<Longrightarrow>  a = aa"
  apply auto
  sorry

lemma test19: "(\<lambda>h. \<exists>c. h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c) = (\<lambda>h. \<exists>c. h \<Turnstile> aa \<mapsto>\<^sub>r c * cell_assn ba c)
   \<Longrightarrow> (\<exists>c. h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c) = ( \<exists>c. h \<Turnstile> aa \<mapsto>\<^sub>r c * cell_assn ba c)"
  by meson

lemma test17: "
   Abs_assn (\<lambda>h. \<exists>c. h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c) = Abs_assn (\<lambda>h. \<exists>c. h \<Turnstile> aa \<mapsto>\<^sub>r c * cell_assn ba c) \<Longrightarrow> (\<lambda>h. \<exists>c. h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c) = (\<lambda>h. \<exists>c. h \<Turnstile> aa \<mapsto>\<^sub>r c * cell_assn ba c)"
  by (smt (verit, ccfv_threshold) Abs_assn_inverse mem_Collect_eq mod_relH models_in_range proper_def)

lemma test18: "(\<lambda>h. \<exists>c. h \<Turnstile> a \<mapsto>\<^sub>r c * cell_assn b c) = (\<lambda>h. \<exists>c. h \<Turnstile> aa \<mapsto>\<^sub>r c * cell_assn ba c) \<Longrightarrow> a = aa" 
  sorry

lemma test15:  "(\<exists>\<^sub>Ac. a \<mapsto>\<^sub>r c * cell_assn b c) = (\<exists>\<^sub>Ac. aa \<mapsto>\<^sub>r c * cell_assn ba c) \<Longrightarrow> a = aa"
  using test18[of a b aa ba]
  unfolding ex_assn_def
  using test17 by blast

lemma test14: "inj (\<lambda>x. case x of (p, c') \<Rightarrow> \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c)"
  apply(auto simp: inj_def test15 exI)
  sorry

lemma test_7: "(p, c') \<in> Map.graph C \<Longrightarrow>
    Finite_Set.fold g acc (f ` Map.graph C)  =
    g (f (p, c')) (Finite_Set.fold g acc (f ` Map.graph (C(p := None))))"
  apply auto
 sorry

lemma test_6: "(p, c') \<in> Map.graph C \<Longrightarrow>
    fold_assn (f ` Map.graph C) = (f (p, c') * fold_assn (f ` Map.graph (C(p := None))))" 
  unfolding fold_assn_def
  apply auto
  sorry

lemma "a \<mapsto>\<^sub>a xs = false \<Longrightarrow> False"
  unfolding snga_assn_def
  apply(induction a)
  sorry

lemma test_5_2: "cell_assn x z = cell_assn y z \<Longrightarrow> x = y"
  apply(induction x z rule: cell_assn.induct; induction y z rule: cell_assn.induct)
  apply auto
  sorry

lemma test_5: "inj cell_assn" 
  unfolding inj_def
  apply auto
  subgoal for x y
    apply(induction x; induction y)
       apply auto
    sorry
  sorry
  

lemma test_4_3: "h \<Turnstile> p \<mapsto>\<^sub>r a * F \<and>\<^sub>A p \<mapsto>\<^sub>r a' * F' \<longrightarrow> a = a'"
  using sngr_prec
  unfolding precise_def
  by blast

lemma test_4_2: "precise (\<lambda>c' p. \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c)"
  unfolding precise_def
  apply auto
  subgoal for a b p F Fa x xa aa xb
    using test_4_3[of p xa F x Fa "(a, b)"]
    apply auto
    sorry
  sorry
  

lemma test_4_1: "\<lbrakk>(\<exists>\<^sub>Ac. a \<mapsto>\<^sub>r c * cell_assn b c) = (\<exists>\<^sub>Ac. aa \<mapsto>\<^sub>r c * cell_assn ba c)\<rbrakk> \<Longrightarrow> a = aa"
  using sngr_prec
  unfolding precise_def
  apply sep_auto
  sorry

lemma test_4: "inj_on (\<lambda>x. case x of (p, c') \<Rightarrow> \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c) (Map.graph C)"
  unfolding inj_on_def
  apply auto
  using test_4_1
  sorry
*)


lemma open_master_assn': "master_assn ((p,c')#xs) = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn xs"
  unfolding master_assn_def
  by auto


lemma open_master_assn: "List.member xs  (p, c') \<Longrightarrow> master_assn xs = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn (remove1 (p, c') xs)"
  unfolding master_assn_def member_def
  apply auto
  sledgehammer
  sorry


fun la_rel' where
  "la_rel' C 0 xs a \<longleftrightarrow> List.member C (a, Array' xs)"
| "la_rel' C (Suc n) xs a \<longleftrightarrow> (\<exists>i x a' xs'. List.member C (a, Upd' i x a') \<and> la_rel' C n xs' a' \<and> xs = xs'[i:=x])"
  
definition la_rel where
  "la_rel C xs a \<equiv> \<exists>n. la_rel' C n xs a"
                               
definition array_to_la :: "('a::heap) array \<Rightarrow> 'a la Heap" where
  "array_to_la a = do {
    ref (Array a)
  }"

lemma array_to_la: "<a \<mapsto>\<^sub>a xs> array_to_la a <\<lambda>r. \<exists>\<^sub>At. master_assn t * \<up>(la_rel t xs r)>"
  unfolding array_to_la_def master_assn_def la_rel_def
  apply vcg
  subgoal for r
    apply(rule ent_ex_postI[where x = "[(r, Array' xs)]"])
    apply(subst exI[where x = "0"])
    apply(simp_all add: List.member_def)
    by(sep_auto simp: ent_ex_postI[where x = "cell.Array a"])
  done

partial_function (heap) lookup :: "('a::heap) la  \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "lookup la n = do {
      cell \<leftarrow> !la;
      case cell of
        Array array   \<Rightarrow> Array.nth array n
      | Upd m value r \<Rightarrow> if n = m 
                         then return value
                         else lookup r n
  }"
declare lookup.simps[code]


lemma [simp]:"cell_assn (Array' xs) c = (\<exists>\<^sub>Aa. \<up>(c = Array a) * a \<mapsto>\<^sub>a xs)"
  apply(cases c)
   apply(auto)
  apply (rule ent_iffI)
  by sep_auto+

lemma [simp]:"cell_assn (Upd' i x p) c = \<up>(c = Upd i x p)"
  apply(cases c)
  by auto



lemma close_master_assn_upd: "a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) \<Longrightarrow>\<^sub>A master_assn t"
  unfolding master_assn_def
  using open_master_assn
  sorry

lemma lookup: "<master_assn t * \<up>(la_rel' t n xs a \<and> i < length xs)> lookup a i <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
proof(induction n arbitrary: xs a)
  case 0
  then show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(subst open_master_assn, assumption)
    apply(sep_auto simp: List.member_def)
    (*apply (rule ent_frame_fwd[OF close_master_assn_upd], frame_inference)*)
     sorry
next
  case (Suc n)
  show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(subst open_master_assn, assumption)
    apply(sep_auto)
    apply (rule ent_frame_fwd[OF close_master_assn_upd], frame_inference)
    apply sep_auto
    apply(rule cons_pre_rule[OF close_master_assn_upd])
    apply (rule cons_post_rule)
    apply (rule fi_rule[OF Suc.IH])
    apply sep_auto
    apply sep_auto
    done
qed

partial_function (heap) update :: "('a::heap) la \<Rightarrow> nat \<Rightarrow> 'a::heap \<Rightarrow> 'a la Heap" where
  "update la n v = do {
      old_v \<leftarrow> lookup la n;
      cell \<leftarrow> !la;
      new_la \<leftarrow> case cell of       
         Array array \<Rightarrow> Array.upd n v array \<bind> array_to_la
       | Upd m w la' \<Rightarrow> 
            do {
                tmp \<leftarrow> update la' n v;
                ref (Upd m w tmp)
            };
      la :=\<^sub>R Upd n old_v new_la;
      return new_la
  }"
declare update.simps[code]

definition array_to_la' where
  "array_to_la' n x = do {
    a \<leftarrow> Array.new n x;
    Array.upd 0 (42::nat) a;
    array_to_la a
  }"

definition test where "test = do {
  r \<leftarrow> array_to_la' 3 (5::nat);
  y \<leftarrow> update r 1 (6::nat);
  x \<leftarrow> lookup y 2;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

