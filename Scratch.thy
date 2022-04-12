theory Scratch
  imports Main "Separation_Logic_Imperative_HOL.Sep_Main" "Deriving.Derive" "HOL-Library.Code_Target_Nat"
begin


abbreviation member where
  "member xs x \<equiv> x \<in> set xs"

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

lemma fold_assn_remove1: "member xs x \<Longrightarrow> fold_assn xs = x * fold_assn (remove1 x xs)"
  apply(induction xs)
  by(auto simp: algebra_simps)

lemma fold_assn_false [simp]: "member xs false \<Longrightarrow> fold_assn xs = false"
  using fold_assn_remove1
  by auto

lemma fold_assn_emp_remove1: "fold_assn xs = fold_assn (remove1 emp xs)"
  apply(induction xs)
  by auto

lemma fold_assn_emp_removeAll: "fold_assn xs = fold_assn (removeAll emp xs)"
  apply(induction xs)
  by auto  

lemma fold_assn_map: "member xs x \<Longrightarrow> fold_assn (remove1 (f x) (map f xs)) = fold_assn (map f (remove1 x xs))"
  apply(induction xs)
  apply auto
  by (metis fold_assn_remove1 image_eqI list.set_map)

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


definition master_assn :: "('a cell ref * 'a::heap cell') list \<Rightarrow> assn" where
  "master_assn C = fold_assn (map (\<lambda>(p, c'). \<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) C)"


lemma open_master_assn': "master_assn ((p,c')#xs) = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn xs"
  unfolding master_assn_def
  by auto

lemma open_master_assn: 
  assumes "member xs (p, c')"
  shows "master_assn xs = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn (remove1 (p, c') xs)"
proof-
  from assms have 
    "member (map (\<lambda>(p, c'). \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c) xs) (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c)"
    by auto

  with assms show ?thesis
    unfolding master_assn_def
    using 
        fold_assn_remove1
        fold_assn_map[of "(p, c')" xs "(\<lambda>(p, c'). \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c)"]
    by auto
qed 

fun la_rel' where
  "la_rel' C 0 xs a \<longleftrightarrow> member C (a, Array' xs)"
| "la_rel' C (Suc n) xs a \<longleftrightarrow> (\<exists>i x a' xs'. member C (a, Upd' i x a') \<and> la_rel' C n xs' a' \<and> xs = xs'[i:=x])"
  
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

lemma close_master_assn_array: "member t (a, Array' xs) 
  \<Longrightarrow> a' \<mapsto>\<^sub>a xs * a \<mapsto>\<^sub>r cell.Array a' * master_assn (remove1 (a, Array' xs) t) \<Longrightarrow>\<^sub>A master_assn t"
  using open_master_assn[of a "Array' xs" t]
  by sep_auto

lemma close_master_assn_upd: "member t (a, Upd' i x a')
     \<Longrightarrow> a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) \<Longrightarrow>\<^sub>A master_assn t"
  using open_master_assn[of a "Upd' i x a'" t]
  by sep_auto

lemma close_master_assn_upd': "member t (a, Upd' i x a')
     \<Longrightarrow> a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) = master_assn t"
  using open_master_assn[of a "Upd' i x a'" t]
  by(auto simp: ent_iffI entails_def)

(* How to inline these? *)
lemma helper1:
  assumes 
    "i < length xs'"
    "member t (a, Upd' i x a')"
    "la_rel' t n xs' a'"
    "xs = xs'[i := x]"
  shows
    "a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) \<Longrightarrow>\<^sub>A master_assn t * true"
proof-  
  from assms show ?thesis 
    using close_master_assn_upd[of a i x a' t]
    apply sep_auto
    using ent_true_drop(2) by blast
qed

lemma helper2: 
  assumes
     "i < length xs'" 
     "member t (a, Upd' ia x a')" 
     "la_rel' t n xs' a'" 
     "xs = xs'[ia := x]"
     "i \<noteq> ia"
   shows "
      <a \<mapsto>\<^sub>r Upd ia x a' * master_assn (remove1 (a, Upd' ia x a') t)> lookup a' i <\<lambda>r. master_assn t * true * \<up> (r = xs' ! i)>
       = <master_assn t> lookup a' i <\<lambda>x. master_assn t * true * \<up> (x = xs' ! i)>"
  using close_master_assn_upd'[of a ia x a' t] assms
  by auto

lemma lookup: "<master_assn t * \<up>(la_rel' t n xs a \<and> i < length xs)> lookup a i <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
proof(induction n arbitrary: xs a)
  case 0
  then have "\<And>a'. \<lbrakk>member t (a, Array' xs); i < length xs\<rbrakk>
         \<Longrightarrow> a' \<mapsto>\<^sub>a xs * a \<mapsto>\<^sub>r cell.Array a' * master_assn (remove1 (a, Array' xs) t) \<Longrightarrow>\<^sub>A master_assn t"
    using close_master_assn_array
    by sep_auto

  then show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(subst open_master_assn, assumption)
    apply(sep_auto)
    using ent_true_drop(2) by blast
next
  case (Suc n)

  show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(subst open_master_assn, assumption)
    apply(sep_auto simp: helper1 helper2)
    apply (rule cons_post_rule)
    apply (rule fi_rule[OF Suc.IH])
    by sep_auto+
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

definition create_la where
  "create_la n x = do {
    a \<leftarrow> Array.new n x;
    Array.upd 0 (42::nat) a;
    array_to_la a
  }"

definition test where "test = do {
  r \<leftarrow> create_la 3 (5::nat);
  y \<leftarrow> update r 1 (6::nat);
  x \<leftarrow> lookup y 2;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

