theory Diff_Arr
  imports Diff_Arr_Rel Master_Assn
begin

(* TODO: Use Locale instead of context *)
context
begin

type_synonym 'a diff_arr = "'a cell ref"

qualified definition from_array :: "('a::heap) array \<Rightarrow> 'a diff_arr Heap" where
  "from_array a = do {
    ref (Array a)
  }"

qualified definition from_list :: "('a::heap) list \<Rightarrow> 'a diff_arr Heap" where
  "from_list xs = do {
    a \<leftarrow> Array.of_list xs;
    from_array a
  }"

qualified partial_function (heap) lookup :: "('a::heap) diff_arr \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "lookup diff_arr n = do {
      cell \<leftarrow> !diff_arr;
      case cell of
        Array array   \<Rightarrow> Array.nth array n
      | Upd m value r \<Rightarrow> if n = m 
                         then return value
                         else lookup r n
  }"
declare lookup.simps[code]

(* TODO: Use size type class *)
qualified partial_function (heap) length :: "('a::heap) diff_arr \<Rightarrow> nat Heap" where
  "length diff_arr = do {
      cell \<leftarrow> !diff_arr;
      case cell of
        Array array   \<Rightarrow> Array.len array
      | Upd m value r \<Rightarrow> length r
  }"
declare length.simps[code]

(* TODO: use array_copy? *)
qualified partial_function (heap) realize :: "('a::heap) diff_arr \<Rightarrow> 'a array Heap" where
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

qualified partial_function (heap) update :: 
    "('a::heap) diff_arr \<Rightarrow> nat \<Rightarrow> 'a::heap \<Rightarrow> 'a diff_arr Heap"
where
  "update diff_arr i v = do {
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
          arr \<leftarrow> realize diff_arr;
          Array.upd i v arr;
          ref (Array arr) 
        }
  }"
declare update.simps[code]

end

lemma ref_lookup_upd: "\<lbrakk>t \<turnstile> xs \<sim>\<^sub>n a; 0 < n\<rbrakk>
   \<Longrightarrow> <master_assn t> !a <\<lambda>c. master_assn t * \<up>(\<exists>x y z. c = Upd x y z)>"
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

lemma from_array [sep_heap_rules]:
    "<a \<mapsto>\<^sub>a xs> Diff_Arr.from_array a <\<lambda>r. \<exists>\<^sub>At. master_assn t * \<up>(t \<turnstile> xs \<sim> r)>"
  unfolding Diff_Arr.from_array_def master_assn_def diff_arr_rel_def
  apply vcg
  subgoal for r
    apply(rule ent_ex_postI[where x = "[(r, Array' xs)]"])
    apply(subst exI[where x = "0"])
    by(sep_auto simp: ent_ex_postI[where x = "cell.Array a"])+
  done

lemma from_list [sep_heap_rules]:
    "<emp> Diff_Arr.from_list xs <\<lambda>r. \<exists>\<^sub>At. master_assn t * \<up>(t \<turnstile> xs \<sim> r)>"
  unfolding Diff_Arr.from_list_def 
  by sep_auto

lemma from_array' [sep_heap_rules]: 
 "<a \<mapsto>\<^sub>a xs * master_assn t>
     Diff_Arr.from_array a      
  <\<lambda>r. let t' = (r, Array' xs)#t 
    in master_assn t' * \<up>(diff_arr_rel t' xs r)>"
  unfolding Diff_Arr.from_array_def Let_def diff_arr_rel_def
  by(sep_auto simp: exI[where x = "0"] master_assn_def)
 
lemma from_list' [sep_heap_rules]:
    "<master_assn t> 
      Diff_Arr.from_list xs 
     <\<lambda>r. let t' = (r, Array' xs) # t 
          in  master_assn t' * \<up>(t' \<turnstile> xs \<sim> r)>"
  unfolding Diff_Arr.from_list_def
  by sep_auto

lemma lookup_aux: "
  <\<up>(t \<turnstile> xs \<sim>\<^sub>n a \<and> i < length xs) * master_assn t >
      Diff_Arr.lookup a i 
  <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
proof(induction n arbitrary: xs a)
  case 0
  show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(sep_drule r: open_master_assn)
    apply(sep_auto)
    apply(sep_drule r: close_master_assn_array)
    by sep_auto
next
  case (Suc n)

  show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply (sep_drule r: close_master_assn_upd)
    apply sep_auto
    apply (sep_drule r: close_master_assn_upd)
    apply sep_auto
    apply (rule cons_post_rule)
    apply (rule fi_rule[OF Suc.IH])
    by sep_auto+
qed

lemma lookup [sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> a \<and> i < length xs)> 
     Diff_Arr.lookup a i 
  <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t
" unfolding diff_arr_rel_def
  apply(sep_auto)
  apply(rule cons_post_rule)
  apply(rule fi_rule[OF lookup_aux])
  by solve_entails

lemma realize_aux: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim>\<^sub>n diff_arr)> 
     Diff_Arr.realize diff_arr
  <\<lambda>arr. master_assn t * \<up>(t \<turnstile> xs \<sim>\<^sub>n diff_arr) * arr \<mapsto>\<^sub>a xs>
" 
proof(induction n arbitrary: t diff_arr xs)
  case 0
  then show ?case
    apply sep_auto
    apply(subst realize.simps)
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_array)
    by(sep_auto simp: map_nth)
next
  case (Suc n)
  then show ?case
    apply sep_auto
    apply(subst realize.simps)
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    apply sep_auto
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    by sep_auto
qed

lemma realize [sep_heap_rules]: "
   <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
     Diff_Arr.realize diff_arr
  <\<lambda>arr. master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr) * arr \<mapsto>\<^sub>a xs>
" 
  unfolding diff_arr_rel_def
  apply sep_auto
  subgoal for n
    using realize_aux[of t xs n diff_arr]
    by sep_auto
  done

(* TODO: Simplify *)
lemma update[sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr \<and> i < length xs)> 
     Diff_Arr.update diff_arr i v
  <\<lambda>diff_arr. \<exists>\<^sub>At'. master_assn t' * 
    \<up>((\<forall>xs' diff_arr'. t \<turnstile> xs' \<sim> diff_arr' \<longrightarrow> t' \<turnstile> xs' \<sim> diff_arr') \<and> 
      (t' \<turnstile> xs[i := v] \<sim> diff_arr))>\<^sub>t"
  apply(subst update.simps)
  unfolding diff_arr_rel_def
  apply auto
  subgoal for n
  proof(induction "n = 0")
    case True
    then show ?thesis 
      apply -
      apply(rule hoare_triple_preI)
      apply(drule master_assn_distinct)
      apply simp
      apply(sep_drule r: open_master_assn)
      apply(sep_auto eintros del: exI)
      subgoal for new_arr new_diff_arr
        apply(rule exI[where x = "
                      (new_diff_arr, Array' (xs[i := v]))
                   #  (diff_arr, Upd' i (xs ! i) new_diff_arr)
                   #  (remove1 (diff_arr, Array' xs) t)"
                ]) 
        apply sep_auto
        subgoal for xs' diff_arr' h n' as
        proof(induction t==t xs' n' diff_arr' arbitrary: xs' diff_arr' rule: diff_arr_rel'.induct)
          case (1 xs' diff_arr')
          then show ?case 
          proof(cases "diff_arr' = diff_arr")
            case True

            with 1 have "distinct (map fst t)" 
              by auto

            with 1 True have "xs' = xs"
              by (meson cell'.inject(1) distinct_map_fstD diff_arr_rel'.simps(1))

            with True 1 show ?thesis
              apply -
              apply(rule exI[where x = 1])
              apply sep_auto
              apply(rule exI[where x = i])
              apply(rule exI[where x = "xs ! i"])
              apply(rule exI[where x = new_diff_arr])
              by sep_auto
          next
            case False
            with 1 show ?thesis
              apply -
              apply(rule exI[where x = 0])
              by sep_auto
          qed
        next
          case (2 xs' n' diff_arr')
          note LA_REL_PREM = \<open>diff_arr_rel' t  xs' (Suc n') diff_arr'\<close>
          note OTHER_PREMS = 2(2) 2(3) 2(4) 2(5) 2(7)

          from LA_REL_PREM show ?case
            apply sep_auto
            subgoal for i v diff_arr'' xs''
              using "2.hyps"[of xs'' diff_arr''] OTHER_PREMS
              apply(sep_auto)
              subgoal for n''
                apply(rule exI[where x = "Suc n''"])
                by(sep_auto)
              done
            done
        qed
        apply (meson diff_arr_rel'.simps(1) list.set_intros(1))
        by(sep_auto simp: open_master_assn_cons)
      done
  next
    case False
    then show ?thesis 
      apply(sep_auto heap: ref_lookup_upd)
      apply(rule fi_rule[OF realize_aux])
      apply(sep_auto eintros del: exI)+
      subgoal for new_arr new_diff_arr
        apply(cases "(new_diff_arr, Array' (xs[i := v])) \<in>\<^sub>L t")
        
        subgoal
          apply-
          apply(rule exI[where x = "t"])
          by(sep_auto intro: exI[where x = 0])
        
        subgoal
          apply-
          apply(rule exI[where x = "(new_diff_arr, Array' (xs[i := v])) #  t"])
          apply sep_auto
          using diff_arr_rel'_cons apply blast
          by(sep_auto simp: open_master_assn_cons intro: exI[where x = 0])+
        
        done
      done
  qed
  done

lemma length[sep_heap_rules]: "
  <master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr)> 
    Diff_Arr.length diff_arr 
  <\<lambda>len. master_assn t * \<up>(t \<turnstile> xs \<sim> diff_arr \<and> len = length xs)>"
  apply(subst length.simps)
  unfolding diff_arr_rel_def
  apply auto
  subgoal for n
  proof(induction t xs n diff_arr rule: diff_arr_rel'.induct)
    case (1 t xs a)
    then show ?case 
      apply simp
      apply(sep_drule r: open_master_assn)
      by(sep_auto simp: close_master_assn_array)
  next
    case (2 t xs n a)
    then show ?case 
      apply auto
      apply(sep_drule r: open_master_assn)
      apply(sep_auto simp: close_master_assn_upd')
      apply(subst length.simps)
      by sep_auto
  qed
  done

end
