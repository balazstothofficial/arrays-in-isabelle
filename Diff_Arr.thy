theory Diff_Arr
  imports Diff_Arr_Rel Master_Assn
begin

(* TODO: Use Locale instead of context *)
context
begin

type_synonym 'a diff_arr = "'a cell ref"

qualified definition from_array :: 
  "('a::heap) array \<Rightarrow> 'a diff_arr Heap" 
where
  "from_array a = do {
    ref (Array a)
  }"

qualified definition from_list :: 
  "('a::heap) list \<Rightarrow> 'a diff_arr Heap" 
where
  "from_list xs = do {
    a \<leftarrow> Array.of_list xs;
    from_array a
  }"

qualified partial_function (heap) lookup :: 
  "('a::heap) diff_arr \<Rightarrow> nat \<Rightarrow> 'a Heap" 
where
  "lookup diff_arr i = do {
      cell \<leftarrow> !diff_arr;
      case cell of
        Array array            \<Rightarrow>
          Array.nth array i
      | Upd i' value diff_arr' \<Rightarrow>
          if i = i'
          then return value
          else lookup diff_arr' i
  }"
declare lookup.simps[code]

(* TODO: use array_copy? *)
qualified partial_function (heap) realize :: 
  "('a::heap) diff_arr \<Rightarrow> 'a array Heap" 
where
  "realize diff_arr = do {
    cell \<leftarrow> !diff_arr;
     case cell of
        Array arr \<Rightarrow> do {
            len \<leftarrow> Array.len arr;
            xs  \<leftarrow> Array.freeze arr;
            Array.make len (List.nth xs)
        }
      | Upd i v diff_arr \<Rightarrow> do {
          arr \<leftarrow> realize diff_arr;
          Array.upd i v arr
        }
  }"
declare realize.simps[code]

abbreviation update_if_none where
  "update_if_none m i v \<equiv> (case m i of None \<Rightarrow> m(i \<mapsto> v) | Some _ \<Rightarrow> m)"

(* Tailrec version, ask Peter if this makes sense *)
qualified partial_function (heap) realize_tailrec :: 
  "(nat \<rightharpoonup> 'a) \<Rightarrow> ('a::heap) diff_arr \<Rightarrow> 'a array Heap" 
where
  "realize_tailrec upds diff_arr = do {
    cell \<leftarrow> !diff_arr;
     case cell of
        Array arr \<Rightarrow> do {
            len \<leftarrow> Array.len arr;
            xs  \<leftarrow> Array.freeze arr;
            Array.make len (\<lambda>i. case upds i of None \<Rightarrow> List.nth xs i | Some v \<Rightarrow> v)
        }
      | Upd i v diff_arr \<Rightarrow> realize_tailrec (update_if_none upds i v) diff_arr
  }"
declare realize_tailrec.simps[code]

qualified partial_function (heap) update' :: 
    "('a cell ref \<Rightarrow> 'a array Heap) \<Rightarrow>('a::heap) diff_arr \<Rightarrow> nat \<Rightarrow> 'a::heap \<Rightarrow> 'a diff_arr Heap"
where
  "update' realize_impl diff_arr i v = do {
      cell \<leftarrow> !diff_arr;
      case cell of
        Array arr \<Rightarrow> do {
          new_diff_arr \<leftarrow> ref (Array arr);
          old_v \<leftarrow> Array.nth arr i;
          diff_arr :=\<^sub>R Upd i old_v new_diff_arr;
          Array.upd i v arr;
          return new_diff_arr
        }
      | Upd _ _ _ \<Rightarrow> do {
          arr \<leftarrow> realize_impl diff_arr;
          Array.upd i v arr;
          ref (Array arr) 
        }
  }"
declare update'.simps[code]

abbreviation update where "update \<equiv> update' realize"

abbreviation update_tailrec where "update_tailrec \<equiv> update' (realize_tailrec Map.empty)"

qualified partial_function (heap) length :: 
  "('a::heap) diff_arr \<Rightarrow> nat Heap" 
where
  "length diff_arr = do {
      cell \<leftarrow> !diff_arr;
      case cell of
        Array array   \<Rightarrow> Array.len array
      | Upd m value r \<Rightarrow> length r
  }"
declare length.simps[code]

lemma ref_lookup_upd: "\<lbrakk>t \<turnstile> xs \<sim>\<^sub>n a; 0 < n\<rbrakk> \<Longrightarrow> 
  <master_assn t> !a <\<lambda>c. master_assn t * \<up>(\<exists>x y z. c = Upd x y z)>"
proof(induction n)
  case 0
  then show ?case
    by sep_auto
next
  case (Suc n)
  from Suc(2) show ?case 
    apply sep_auto
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    by sep_auto
qed 

(* TODO: Is it okay to have both from_array'/from_list' and from_array/from_list 
         in sep_heap_rules? *)
lemma from_array' [sep_heap_rules]: 
  "<a \<mapsto>\<^sub>a xs>
      from_array a
   <\<lambda>r. let t = [(r, Array' xs)] 
        in master_assn t * \<up>(t \<turnstile> xs \<sim> r)>"
  unfolding Diff_Arr.from_array_def diff_arr_rel_def master_assn_def
  apply auto
  by(sep_auto simp: exI[where x = "0"])
 
lemma from_list' [sep_heap_rules]:
  "<emp> 
    from_list xs 
   <\<lambda>r. let t = [(r, Array' xs)]
        in  master_assn t * \<up>(t \<turnstile> xs \<sim> r)>"
  unfolding Diff_Arr.from_list_def
  by sep_auto

lemma from_array [sep_heap_rules]:
  "<a \<mapsto>\<^sub>a xs> from_array a <\<lambda>r. \<exists>\<^sub>At. master_assn t * \<up>(t \<turnstile> xs \<sim> r)>"
  by(sep_auto simp: Let_def)

lemma from_list [sep_heap_rules]:
  "<emp> from_list xs <\<lambda>r. \<exists>\<^sub>At. master_assn t * \<up>(t \<turnstile> xs \<sim> r)>"
  by(sep_auto simp: Let_def)

lemma lookup_aux: 
  "<\<up>(t \<turnstile> xs \<sim>\<^sub>n a \<and> i < List.length xs) * master_assn t>
      lookup a i 
   <\<lambda>r. master_assn t * \<up>(r = xs!i)>"
proof(induction n arbitrary: xs a)
  case 0
  then show ?case 
    apply sep_auto
    apply(subst lookup.simps)
    apply(sep_drule r: open_master_assn)
    by(sep_auto simp: close_master_assn_array)
next
  case (Suc n)
  then show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(sep_drule r: open_master_assn)
    by(sep_auto simp: close_master_assn_upd')
qed

lemma lookup [sep_heap_rules]: 
  "<master_assn t * \<up>(t \<turnstile> xs \<sim> a \<and> i < List.length xs)> 
     lookup a i 
   <\<lambda>r. master_assn t * \<up>(r = xs!i)>"
  unfolding diff_arr_rel_def
  using lookup_aux[of t]
  by sep_auto

lemma realize_aux: 
 "<master_assn t * \<up>(t \<turnstile> xs \<sim>\<^sub>n diff_arr)> 
     realize diff_arr
  <\<lambda>arr. master_assn t * arr \<mapsto>\<^sub>a xs>" 
proof(induction n arbitrary: diff_arr xs)
  case 0
  then show ?case
    apply sep_auto
    apply(subst realize.simps)
    apply(sep_drule r: open_master_assn)
    apply(sep_auto simp: map_nth)
    apply(sep_drule r: close_master_assn_array)
    by sep_auto
next
  case (Suc n)
  then show ?case
    apply sep_auto
    apply(subst realize.simps)
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    by sep_auto+    
qed

lemma realize [sep_heap_rules]: 
  "<master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     realize diff_arr
   <\<lambda>arr. master_assn t * arr \<mapsto>\<^sub>a xs>" 
  unfolding diff_arr_rel_def
  using realize_aux[of t]
  by sep_auto

lemma realize_tailrec_aux: 
 "<master_assn t * \<up>(t \<turnstile> xs \<sim>\<^sub>n diff_arr)> 
     realize_tailrec upds diff_arr 
  <\<lambda>arr. master_assn t * arr \<mapsto>\<^sub>a 
        (map (\<lambda>i. case upds i of None \<Rightarrow> xs ! i | Some v \<Rightarrow> v) [0..<List.length xs])>" 
proof(induction n arbitrary: t diff_arr xs upds)
  case 0
  then show ?case
    apply sep_auto
    apply(subst realize_tailrec.simps)
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_array)
    by(sep_auto simp: map_nth)
next
  case (Suc n)
  
  have [simp]: "\<And>i i' xs' upds x. i < List.length xs' \<Longrightarrow>
  (case (case upds i of None \<Rightarrow> upds(i \<mapsto> x) | Some x \<Rightarrow> upds) i' of 
     None \<Rightarrow> xs' ! i'
   | Some v \<Rightarrow> v) = 
  (case upds i' of None \<Rightarrow> xs'[i := x] ! i' | Some v \<Rightarrow> v)"
  by(auto simp: nth_list_update split: option.splits)

  from Suc show ?case
    apply sep_auto
    apply(subst realize_tailrec.simps)
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    apply sep_auto+
    subgoal for i x a' xs'
      using Suc[of t xs' a' "update_if_none upds i x "]
      by sep_auto
    done
qed

lemma realize_tailrec [sep_heap_rules]: 
  "<master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     realize_tailrec Map.empty diff_arr 
   <\<lambda>arr. master_assn t * arr \<mapsto>\<^sub>a xs>" 
  unfolding diff_arr_rel_def
  using realize_tailrec_aux[of t xs _ diff_arr Map.empty]
  by(sep_auto simp: map_nth)

lemma update_diff_arr_rel: "\<lbrakk>
  i < List.length xs; 
  (diff_arr, Array' xs) \<in>\<^sub>L t; 
  distinct (map fst t);
  t \<turnstile> xs' \<sim>\<^sub>n' diff_arr'
\<rbrakk> \<Longrightarrow> \<exists>n. (new_diff_arr, Array' (xs[i := v])) #
          (diff_arr, Upd' i (xs ! i) new_diff_arr) #
          remove1 (diff_arr, Array' xs) t \<turnstile> xs' \<sim>\<^sub>n diff_arr'"
proof(induction t xs' n' diff_arr' arbitrary: xs' diff_arr' rule: diff_arr_rel'.induct)
  case (1 t xs' diff_arr')
  then show ?case
  proof(cases "diff_arr' = diff_arr")
    case True
    with 1 have "xs' = xs"
      using distinct_map_fstD[of t]
      by auto
  
    with True 1 show ?thesis
      apply -
      apply(rule exI[where x = 1])
      apply(sep_auto)
      apply(rule exI[where x = i])
      apply(rule exI[where x = "xs ! i"])
      apply(rule exI[where x = new_diff_arr])
      by sep_auto
  next
    case False
    with 1 show ?thesis
      by(sep_auto simp: exI[where x = 0])
  qed
next
  case (2 t xs' n' diff_arr')

  then obtain i' v' diff_arr'' xs'' where unfold_diff_arr_rel:
      "(diff_arr', Upd' i' v' diff_arr'') \<in>\<^sub>L t" 
      "t \<turnstile> xs'' \<sim>\<^sub>n' diff_arr''"
      "i' < List.length xs''"
      "xs' = xs''[i' := v']"
    by sep_auto

  with 2 obtain n'' where 
     "(new_diff_arr, Array' (xs[i := v])) #
      (diff_arr, Upd' i (xs ! i) new_diff_arr) #
      remove1 (diff_arr, Array' xs) t \<turnstile> xs'' \<sim>\<^sub>n'' diff_arr''"
    by blast
   
  with unfold_diff_arr_rel show ?case
    apply -
    apply(rule exI[where x = "Suc n''"])
    by auto
qed

lemma update'_aux: 
  assumes
    "i < List.length xs"
    "t \<turnstile> xs \<sim>\<^sub>n diff_arr"
    "\<And>t xs diff_arr. <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
       realize_impl diff_arr
     <\<lambda>arr. master_assn t * arr \<mapsto>\<^sub>a xs>"
  shows
    "<master_assn t> 
       update' realize_impl diff_arr i v
     <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
       \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') \<and> 
         (t' \<turnstile> xs[i := v] \<sim> diff_arr))>"
proof(cases "n = 0")
  case True
  with assms show ?thesis
      unfolding diff_arr_rel_def
      apply(simp add: update'.simps)
      apply(hoare_triple_preI rule: master_assn_distinct)
      apply(sep_drule r: open_master_assn)
      apply(sep_auto eintros del: exI)       
      subgoal for new_arr new_diff_arr
        apply(rule exI[where x = 
                     "(new_diff_arr, Array' (xs[i := v])) #
                      (diff_arr, Upd' i (xs ! i) new_diff_arr) #
                      (remove1 (diff_arr, Array' xs) t)"
                ]) 
        by(sep_auto simp: update_diff_arr_rel open_master_assn_cons exI[where x = 0])
      done
next
  case False
  with assms show ?thesis
  unfolding diff_arr_rel_def
  apply(subst update'.simps)
  apply(sep_auto heap: ref_lookup_upd eintros del: exI)
  subgoal for new_arr new_diff_arr
    apply(rule exI[where x = "(new_diff_arr, Array' (xs[i := v])) #  t"])
    by(sep_auto simp: diff_arr_rel'_cons' exI[where x = 0] open_master_assn_cons[of new_diff_arr])
   done
qed

lemma update [sep_heap_rules]: 
  "<master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr \<and> i < List.length xs)> 
     update diff_arr i v
   <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') \<and> 
      (t' \<turnstile> xs[i := v] \<sim> diff_arr))>"
  using realize
  by(sep_auto heap: update'_aux simp: diff_arr_rel_def)

lemma update_tailrec [sep_heap_rules]: 
  "<master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr \<and> i < List.length xs)> 
     update_tailrec diff_arr i v
   <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') \<and> 
      (t' \<turnstile> xs[i := v] \<sim> diff_arr))>"
  using realize_tailrec
  by(sep_auto heap: update'_aux simp: diff_arr_rel_def)

lemma length_aux: "t \<turnstile> xs \<sim>\<^sub>n diff_arr \<Longrightarrow> 
  <master_assn t> 
    length diff_arr 
  <\<lambda>len. master_assn t * \<up>(len = List.length xs)>"
proof(induction t xs n diff_arr rule: diff_arr_rel'.induct)
  case 1
  then show ?case 
    apply sep_auto
    apply(subst length.simps)
    apply(sep_drule r: open_master_assn)
    by(sep_auto simp: close_master_assn_array)
next
  case 2
  then show ?case 
    apply sep_auto
    apply(subst length.simps)
    apply(sep_drule r: open_master_assn)
    by(sep_auto simp: close_master_assn_upd')
qed

lemma length [sep_heap_rules]: 
  "<master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     length diff_arr
   <\<lambda>len. master_assn t * \<up>(len = List.length xs)>"
  unfolding diff_arr_rel_def
  by(sep_auto heap: length_aux)

end

end
