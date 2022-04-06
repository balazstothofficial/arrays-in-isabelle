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
  
definition fold_assn where
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

lemma fold_assn_cons [simp]: "fold_assn (insert x xs) = x * fold_assn (xs - {x})"
  unfolding fold_assn_def
  apply(cases "finite xs")
  by(simp_all add: mf.fold_insert_remove)

lemma fold_assn_in: "x \<in> xs \<Longrightarrow> fold_assn xs = x * fold_assn (xs - {x})"
  by (metis fold_assn_cons insert_absorb)

(*lemma fold_assn_app: "fold_assn (xs \<union> ys) = fold_assn xs * fold_assn ys"
  apply(induction xs)
  by(auto simp: algebra_simps)*)

datatype 'a::"countable" cell = Array "'a array" | Upd nat "'a" "'a cell ref"

derive countable cell

instance cell :: (heap) heap
   by standard

type_synonym 'a la = "'a cell ref"

datatype 'a::"countable" cell' = Array' "'a list" | Upd' nat "'a" "'a cell ref"

fun cell_assn where
  "cell_assn (Array' xs) (Array a) = a \<mapsto>\<^sub>a xs"
| "cell_assn (Upd' i' val' p') (Upd i val p) = \<up>(i = i' \<and> val = val' \<and> p = p')"
| "cell_assn _ _ = false"

definition master_assn :: "('a::heap cell' \<times> 'a cell ref) set \<Rightarrow> assn" where
  "master_assn C = fold_assn ((\<lambda>(c', p). \<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) ` C)"

find_theorems "_ ` (_ - _)"
find_theorems "(\<exists>\<^sub>A _. _) = (\<exists>\<^sub>A _. _)"
find_consts name:precise

(* 
lemma fold_assn_in: "x \<in> xs \<Longrightarrow> fold_assn xs = x * fold_assn (xs - {x})"
  by (metis fold_assn_cons insert_absorb)
*)

lemma sth: "a \<noteq> false \<Longrightarrow> true * a \<noteq> false"
  using ent_false ent_iffI ent_refl_true star_aci(2)
  by (metis ent_false ent_iffI ent_refl_true star_aci(2))


lemma testst: "\<lbrakk>a \<mapsto>\<^sub>a xs = true; a \<mapsto>\<^sub>a ys = true\<rbrakk> \<Longrightarrow> xs = ys"
  by (metis assn_basic_inequalities(5) merge_true_star snga_same_false)

lemma image_iff_2: "z \<notin> f ` A \<longleftrightarrow> \<not>(\<exists>x\<in>A. z = f x)"
  by blast

lemma open_master_assn: "(c', p) \<in> C \<Longrightarrow> master_assn C = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn (C - {(c', p)})"
  unfolding master_assn_def
proof(induction "(\<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c) = false")
  case True
  then have "false \<in> ((\<lambda>a. case a of (c', p) \<Rightarrow> \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c) ` C)"
    using image_iff by fastforce

  with True show ?case 
    by (simp add: fold_assn_false)
next
  case False
  then have "false \<notin> ((\<lambda>a. case a of (c', p) \<Rightarrow> \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c) ` C)"
    sorry

  with False show ?case
  apply sep_auto
  apply(subst fold_assn_in[where x = "\<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c"])
  apply(auto)[]
  apply(subst image_set_diff)
  apply auto
  apply rule
    apply auto
    sorry
qed

 (* apply sep_auto
  apply(subst fold_assn_in[where x = "\<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c"])
  apply(auto)[]
  apply(subst image_set_diff)
  apply auto
  apply rule
  apply auto
   sorry*)

no_notation Ref.update ("_ := _" 62)
notation Ref.update ("_ :=\<^sub>R _" 62)

fun la_rel' where
  "la_rel' C 0 xs a \<longleftrightarrow> (Array' xs, a) \<in> C"
| "la_rel' C (Suc n) xs a \<longleftrightarrow> (\<exists>i x a' xs'. (Upd' i x a', a) \<in> C \<and> la_rel' C n xs' a' \<and> xs = xs'[i:=x])"
  
definition la_rel where
  "la_rel C xs a \<equiv> \<exists>n. la_rel' C n xs a"

(*datatype 'a la_node = LA_node nat 'a "'a la_node list" "'a cell ref"
datatype 'a la_tree = LA_tree "'a list" "'a la_node list" "'a cell ref"



fun la_node_assn where
   "la_node_assn prev (LA_node i a succs p) = 
      (p \<mapsto>\<^sub>r Upd i a prev) * (fold_assn (map (la_node_assn p) succs))"

fun la_tree_assn where
  "la_tree_assn (LA_tree vals succs p) = 
     (\<exists>\<^sub>A ap. (p \<mapsto>\<^sub>r Array ap) * (ap  \<mapsto>\<^sub>a vals) * (fold_assn (map (la_node_assn p) succs)))"*)



(*fun node_to_map :: "'a list \<Rightarrow> 'a la_node \<Rightarrow> ('a cell ref \<rightharpoonup> 'a list)" where
  "node_to_map vals (LA_node i a succs p) = (
    let vals' = vals[i:= a] 
    in [p \<mapsto> vals'] ++ fold (++) (map (node_to_map vals') succs) Map.empty
  )"

fun node_to_map' :: "'a list \<Rightarrow> 'a la_node \<Rightarrow> ('a cell ref * 'a list) list" where
  "node_to_map' vals (LA_node i a succs p) = (
    let vals' = vals[i:= a] 
    in (p, vals') # concat (map (node_to_map' vals') succs)
  )"

fun refs_node where 
  "refs_node (LA_node i a succs p) = p # concat (map refs_node succs)"

definition invar_node :: "'a la_node \<Rightarrow> bool" where
  "invar_node node = distinct (refs_node node)"

fun tree_to_map' :: "'a la_tree \<Rightarrow> ('a cell ref \<times> 'a list) list" where
  "tree_to_map' (LA_tree vals succs p) = (p, vals) # concat (map (node_to_map' vals) succs)"

fun refs_tree where
  "refs_tree (LA_tree vals succs p) = p # concat (map refs_node succs)"

definition invar_tree :: "'a la_tree \<Rightarrow> bool" where
  "invar_tree tree = distinct (refs_tree tree)"

lemma "map fst (node_to_map' xs n) = refs_node n"
  apply(induction n arbitrary: xs)
  by(auto simp: Let_def map_concat intro!: arg_cong[where f = concat])

find_theorems "map _ (concat _)"
thm arg_cong[where f = concat]

lemma node_to_map'_refs: "map fst (node_to_map' xs n) = refs_node n"
  apply(induction xs n rule: node_to_map'.induct)
  by(auto simp: Let_def map_concat intro!: arg_cong[where f = concat])

lemma tree_to_map'_refs: "map fst (tree_to_map' t) = refs_tree t"
  apply(cases t) 
  by (auto simp: node_to_map'_refs map_concat intro!: arg_cong[where f = concat])

find_consts "(_ * _) list \<Rightarrow> (_ \<Rightarrow> _ option)"
find_theorems "map_of" "distinct"

lemma "invar_tree t \<Longrightarrow> distinct (map fst (tree_to_map' t))"
  by (simp add: invar_tree_def tree_to_map'_refs)

definition la_rel :: "'a la_tree \<Rightarrow> 'a list \<Rightarrow> 'a cell ref \<Rightarrow> bool" where
  "la_rel t xs p \<longleftrightarrow> map_of (tree_to_map' t) p = Some xs"*)
                               
definition array_to_la :: "('a::heap) array \<Rightarrow> 'a la Heap" where
  "array_to_la a = do {
    ref (Array a)
  }"

find_theorems "_ \<Longrightarrow>\<^sub>A \<exists>\<^sub>A _. _"

lemma array_to_la: "<a \<mapsto>\<^sub>a xs> array_to_la a <\<lambda>r. \<exists>\<^sub>At. master_assn t * \<up>(la_rel t xs r)>"
  unfolding array_to_la_def master_assn_def la_rel_def
  apply vcg
  subgoal for r
    apply(rule ent_ex_postI[where x = "{(Array' xs, r)}"])
    by(sep_auto simp: exI[where x = "0"] ent_ex_postI[where x = "cell.Array a"])
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


find_theorems "(=)" "(\<Longrightarrow>\<^sub>A)"

lemma [simp]:"cell_assn (Array' xs) c = (\<exists>\<^sub>Aa. \<up>(c = Array a) * a \<mapsto>\<^sub>a xs)"
  apply(cases c)
   apply(auto)
  apply (rule ent_iffI)
  by sep_auto+

lemma [simp]:"cell_assn (Upd' i x p) c = \<up>(c = Upd i x p)"
  apply(cases c)
  by auto

lemma close_master_assn_upd: "a \<mapsto>\<^sub>r Upd i x a' * master_assn (t - {(Upd' i x a', a)}) \<Longrightarrow>\<^sub>A master_assn t"
  unfolding master_assn_def
  using fold_assn_in
  apply(sep_auto simp: )
  sorry

lemma lookup: "<master_assn t * \<up>(la_rel' t n xs a \<and> i < length xs)> lookup a i <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
proof(induction n arbitrary: xs a)
  case 0
  then show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(subst open_master_assn, assumption)
    apply sep_auto
    
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
     thm fi_rule
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

