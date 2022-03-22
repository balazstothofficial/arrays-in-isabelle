theory Scratch
  imports Main "Separation_Logic_Imperative_HOL.Sep_Main" "Deriving.Derive" "HOL-Library.Code_Target_Nat"
begin

(**

   'a cell = Array 'a array | Upd nat 'a ('a cell ref)

   'a la = 'a cell ref ref

*)

datatype 'a::"countable" cell = Array "'a array" | Upd nat "'a" "'a cell ref"

derive countable cell

instance cell :: (heap) heap
   by standard

type_synonym 'a la = "'a cell ref"


datatype 'a la_node = LA_node nat 'a "'a la_node list" "'a cell ref"
datatype 'a la_tree = LA_tree "'a list" "'a la_node list" "'a cell ref"

definition fold_assn where
  "fold_assn assns = fold (*) assns emp"

fun la_node_assn where
   "la_node_assn prev (LA_node i a succs p) = (p \<mapsto>\<^sub>r Upd i a prev) * (fold_assn (map (la_node_assn p) succs))"

fun la_tree_assn where
  "la_tree_assn (LA_tree vals succs p) = (\<exists>\<^sub>A ap. (p \<mapsto>\<^sub>r Array ap) * (ap  \<mapsto>\<^sub>a vals) * (fold_assn (map (la_node_assn p) succs)))"

no_notation Ref.update ("_ := _" 62)
notation Ref.update ("_ :=\<^sub>R _" 62)

fun node_to_map :: "'a list \<Rightarrow> 'a la_node \<Rightarrow> ('a cell ref \<rightharpoonup> 'a list)" where
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

fun tree_to_map' where
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

definition la_rel where
  "la_rel t xs p \<longleftrightarrow> map_of (tree_to_map' t) p = Some xs"

definition array_to_la where
  "array_to_la a = do {
    ref (Array a)
  }"

lemma [simp]: "fold_assn [] = emp"
  unfolding fold_assn_def
  by auto

find_theorems "_ \<Longrightarrow>\<^sub>A \<exists>\<^sub>A _. _"

lemma array_to_la: "<a \<mapsto>\<^sub>a xs> array_to_la a <\<lambda>r. \<exists>\<^sub>At. la_tree_assn t * \<up>(la_rel t xs r)>"
  unfolding array_to_la_def 
  apply vcg
  subgoal for r
    apply(rule ent_ex_postI[where x = "LA_tree xs [] r"])
    by(sep_auto simp: la_rel_def)
  .

partial_function (heap) foo :: "nat \<Rightarrow> nat Heap"  where
  "foo n = do { 
      r \<leftarrow> foo (n);
      return (r + 1)
  }"


definition array_to_la' where
  "array_to_la' n x = do {
    a \<leftarrow> Array.new n x;
    Array.upd 0 (42::nat) a;
    array_to_la a
  }"

definition test where "test = do {
  r \<leftarrow> array_to_la' 2 (5::nat);
  return r
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

