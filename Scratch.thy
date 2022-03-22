theory Scratch
  imports Main "Separation_Logic_Imperative_HOL.Sep_Examples" "Deriving.Derive"
begin

(**

   'a cell = Array 'a array | Upd nat 'a ('a cell ref)

   'a la = 'a cell ref ref

*)

datatype 'a::"countable" cell = Array "'a array" | Upd nat "'a" "'a cell ref"

derive countable cell

instance cell :: (heap) heap
   by standard

type_synonym 'a la = "'a cell ref ref"


datatype 'a la_node = LA_node nat 'a "'a la_node list" "'a cell ref"
datatype 'a la_tree = LA_tree "'a list" "'a la_node list" "'a cell ref"


fun la_node_assn where
   "la_node_assn prev (LA_node i a succs p) = (p \<mapsto>\<^sub>r Upd i a prev) * (\<forall>n\<in>succs. la_node_assn p n)"
