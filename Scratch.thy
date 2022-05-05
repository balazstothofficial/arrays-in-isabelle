theory Scratch
  imports Main "Separation_Logic_Imperative_HOL.Sep_Main" "Deriving.Derive" "HOL-Library.Code_Target_Nat"
begin

(* TODO Rename *)
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

lemma fold_assn_remove1_map: "member xs x
   \<Longrightarrow> fold_assn (remove1 (f x) (map f xs)) = fold_assn (map f (remove1 x xs))"
proof(induction xs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a xs)
  then show ?case
    using fold_assn_remove1[of "f a" "map f xs"] image_iff
    by fastforce
qed
 
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

lemma open_master_assn_cons: "master_assn ((p,c')#xs) = (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn xs"
  unfolding master_assn_def
  by auto

lemma open_master_assn': 
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
        fold_assn_remove1_map[of "(p, c')" xs "(\<lambda>(p, c'). \<exists>\<^sub>Ac. p \<mapsto>\<^sub>r c * cell_assn c' c)"]
    by auto
qed 

lemma open_master_assn: 
  assumes "member xs (p, c')"
  shows "master_assn xs \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A c. p \<mapsto>\<^sub>r c * cell_assn c' c) * master_assn (remove1 (p, c') xs)"
  using assms open_master_assn' by fastforce

fun la_rel' where
  "la_rel' t 0 xs a \<longleftrightarrow> member t (a, Array' xs)"
| "la_rel' t (Suc n) xs a \<longleftrightarrow> (\<exists>i x a' xs'. 
      member t (a, Upd' i x a')
    \<and> la_rel' t n xs' a'
    \<and> xs = xs'[i:=x] 
    \<and> i < length xs'
)"
  
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
  using open_master_assn'[of a "Array' xs" t]
  by sep_auto

lemma close_master_assn_upd: "member t (a, Upd' i x a')
     \<Longrightarrow> a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) \<Longrightarrow>\<^sub>A master_assn t"
  using open_master_assn'[of a "Upd' i x a'" t]
  by sep_auto

lemma close_master_assn_upd': "member t (a, Upd' i x a')
     \<Longrightarrow> a \<mapsto>\<^sub>r Upd i x a' * master_assn (remove1 (a, Upd' i x a') t) = master_assn t"
  using open_master_assn'[of a "Upd' i x a'" t]
  by(auto simp: ent_iffI entails_def)

lemma htriple_frame_fwd:
  assumes R: "P \<Longrightarrow>\<^sub>A R"
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes I: "<R*F> c <Q>"
  shows "<Ps> c <Q>"
  using assms
  by (metis cons_rule ent_refl fr_refl)

method sep_drule uses r = rule ent_frame_fwd[OF r] htriple_frame_fwd[OF r], (assumption+)?, frame_inference

lemma lookup_aux: "<\<up>(la_rel' t n xs a \<and> i < length xs) * master_assn t > lookup a i <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t"
proof(induction n arbitrary: xs a)
  case 0
  show ?case
    apply(sep_auto)
    apply(subst lookup.simps)
    apply(sep_drule r: open_master_assn)
    apply(sep_auto)
    apply (sep_drule r: close_master_assn_array)
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

lemma lookup: "
  <master_assn t * \<up>(la_rel t xs a \<and> i < length xs)> 
    lookup a i 
  <\<lambda>r. master_assn t * \<up>(r = xs!i)>\<^sub>t
" unfolding la_rel_def
  apply(sep_auto)
  apply(rule cons_post_rule)
   apply(rule fi_rule[OF lookup_aux[of t _ xs]])
  by(solve_entails)

(* TODO: use array_copy *)
partial_function (heap) realize :: "('a::heap) la \<Rightarrow> 'a array Heap" where
  "realize la = do {
    cell \<leftarrow> !la;
     case cell of
        Array arr \<Rightarrow> do {
            len \<leftarrow> Array.len arr;
            xs  \<leftarrow> Array.freeze arr;
            Array.make len (List.nth xs)
        }
      | Upd i v la \<Rightarrow> do {
          arr \<leftarrow> realize la;
          Array.upd i v arr
        }
  }"
declare realize.simps[code]

lemma array_to_la': "
  <a \<mapsto>\<^sub>a xs * master_assn t>
  array_to_la a      
  <\<lambda>r. let t' = (r, Array' xs)#t 
    in master_assn t' * \<up>(la_rel t' xs r)>"
  unfolding array_to_la_def Let_def la_rel_def
  apply sep_auto
     apply (meson la_rel'.simps(1) la_rel_def list.set_intros(1))
  by (metis close_master_assn_array list.set_intros(1) remove1.simps(2) star_aci(2))

lemma realize_aux: "
   <master_assn t * \<up>(la_rel' t n xs la)> 
    realize la
  <\<lambda>arr. master_assn t * \<up>(la_rel' t n xs la) * arr \<mapsto>\<^sub>a xs>
" 
proof(induction n arbitrary: t la xs)
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

lemma realize: "
   <master_assn t * \<up>(la_rel t xs la)> 
    realize la
  <\<lambda>arr. master_assn t * \<up>(la_rel t xs la) * arr \<mapsto>\<^sub>a xs>
" 
  unfolding la_rel_def
  apply(sep_auto)
  subgoal for n
    using realize_aux[of t n xs la]
    by sep_auto
  done
 
find_theorems "<_> !_ <_>"

(* TODO: Is the c important? *)
lemma ref_lookup': "la_rel' t n xs la \<Longrightarrow> <master_assn t> !la <\<lambda>c. master_assn t>"
proof(induction n)
  case 0
  then show ?case
    apply sep_auto
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_array)
    by sep_auto
next
  case (Suc n)
  then show ?case 
    apply sep_auto
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    by sep_auto
qed

lemma ref_lookup_2: "\<lbrakk>la_rel' t n xs la; 0 < n\<rbrakk>
   \<Longrightarrow> <master_assn t> !la <\<lambda>c. master_assn t * \<up>(\<exists>x y z. c = Upd x y z)>"
proof(induction n)
  case 0
  then show ?case
    by sep_auto
next
  case (Suc n)
  then show ?case 
    apply sep_auto
    apply(sep_drule r: open_master_assn)
    apply sep_auto
    apply(sep_drule r: close_master_assn_upd)
    by sep_auto
qed

lemma ref_lookup: "la_rel t xs la \<Longrightarrow> <master_assn t> !la <\<lambda>c. master_assn t>"
  unfolding la_rel_def
  using ref_lookup'
  by sep_auto

partial_function (heap) update :: "('a::heap) la \<Rightarrow> nat \<Rightarrow> 'a::heap \<Rightarrow> 'a la Heap" where
  "update la i v = do {
      cell  \<leftarrow> !la;
      case cell of
        Array arr \<Rightarrow> do {
          new_la \<leftarrow> ref (Array arr);
          old_v \<leftarrow> Array.nth arr i;
          la :=\<^sub>R Upd i old_v new_la;
          Array.upd i v arr;
          return new_la
        }
      | Upd _ _ _ \<Rightarrow> do {
          arr \<leftarrow> realize la;
          Array.upd i v arr;
          ref (Array arr) 
        }
  }"
declare update.simps[code]

lemma update: "
  <master_assn t * \<up>(la_rel t xs la \<and> i < length xs)> 
    update la i v
  <\<lambda>la'. \<exists>\<^sub>At'. master_assn t' * \<up>(la_rel t' (xs[i := v]) la')>\<^sub>t
"
  apply(subst update.simps)
  unfolding la_rel_def
  apply clarsimp
  subgoal for n
    apply(cases "n = 0"; simp)
    subgoal
      apply(sep_drule r: open_master_assn)
      apply(sep_auto eintros del: exI)
      subgoal for new_arr new_la
        apply(rule exI[where x = " (new_la, Array' (xs[i := v]))
                                  # (la, Upd' i (xs ! i) new_la) 
                                  # (remove1 (la, Array' xs) t)"])
        by(sep_auto simp: open_master_assn_cons intro: exI[where x = 0])
      done
    
    subgoal
      apply(sep_auto heap: ref_lookup_2)
      (* TODO: work around *)
      apply(rule fi_rule[OF realize_aux])
      apply(sep_auto eintros del: exI)+
      subgoal for new_arr new_la
        apply(rule exI[where x = "(new_la, Array' (xs[i := v])) #  t"])
        by(sep_auto simp: open_master_assn_cons heap: realize_aux intro: exI[where x = 0])
    done
  done
  done

lemma la_rel_cons: "la_rel t xs la \<Longrightarrow> la_rel ((la', c') # t) xs la"
  unfolding la_rel_def
  apply auto
  subgoal for n
    apply(rule exI[where x = n]) 
    proof(induction t n xs la rule: la_rel'.induct)
      case (1 C xs a)
      then show ?case
        by auto
    next
      case (2 C n xs a)
      then show ?case
        apply auto
        subgoal for i x la'
          apply(rule exI[where x = i]) 
          apply(rule exI[where x = x]) 
          apply(rule exI[where x = la']) 
          by auto
        done
    qed
    done

  thm  map_eq_Cons_conv Misc.map_eq_append_conv
  find_theorems "map _ _ = _ @ _"

lemma master_assn_distinct_2: "h \<Turnstile> master_assn t \<Longrightarrow> distinct (map fst t)"
  apply(rule ccontr)
  apply(drule not_distinct_decomp)
  apply(clarsimp simp: map_eq_Cons_conv Misc.map_eq_append_conv)
  unfolding master_assn_def
  by simp
  

  

lemma master_assn_distinct: "master_assn t \<Longrightarrow>\<^sub>A \<up>(distinct (map fst t)) * true"
  by(sep_auto simp: master_assn_distinct_2)


lemma update_2: "
  <master_assn t * \<up>(la_rel t xs la \<and> i < length xs)> 
    update la i v
  <\<lambda>_. \<exists>\<^sub>At'. master_assn t' * \<up>(\<forall>xs' la'. la_rel t xs' la' \<longrightarrow> la_rel t' xs' la')>\<^sub>t
"
  apply(subst update.simps)
  unfolding la_rel_def
  apply auto
  subgoal for n
  proof(induction "n = 0")
    case True
    then show ?thesis
      apply -
      apply(rule hoare_triple_preI)
      apply(drule master_assn_distinct_2)
      find_theorems "<_> _ <_>" "_ \<Turnstile>_"
      apply simp
      apply(sep_drule r: open_master_assn)
      apply(sep_auto eintros del: exI)
      subgoal for new_arr new_la
        apply(rule exI[where x = "
                     (new_la, Array' (xs[i := v]))
                   #  (la, Upd' i (xs ! i) new_la)
                   #   (remove1 (la, Array' xs) t)"]) 
        apply sep_auto
         defer
         apply(sep_auto simp: open_master_assn_cons)
        subgoal for xs' la' h n' as
        proof(induction t==t n' xs' la' arbitrary: xs' la' rule: la_rel'.induct )
          case (1 xs' la')
          then show ?case 
          proof(cases "la' = la")
            case True

            with 1 have "distinct (map fst t)" 
              by auto

            with 1 True have "xs' = xs"
              by (meson cell'.inject(1) distinct_map_fstD la_rel'.simps(1))

            with True 1 show ?thesis
              apply sep_auto
              apply(rule exI[where x = 1])
              apply sep_auto
              apply(rule exI[where x = i])
              apply(rule exI[where x = "xs ! i"])
              apply(rule exI[where x = new_la])
              by sep_auto
          next
            case False
            with 1 show ?thesis
              apply sep_auto
              apply(rule exI[where x = 0])
              by sep_auto
          qed
        next
          case (2 n' xs' la')
          note LA_REL_PREM = \<open>la_rel' t (Suc n') xs' la'\<close>
          note OTHER_PREMS = 2(2) 2(3) 2(4) 2(5) 2(7)

          from LA_REL_PREM show ?case
            apply sep_auto
            subgoal for i v la'' xs''
              using "2.hyps"[of xs'' la''] OTHER_PREMS
              apply(sep_auto)
              subgoal for n''
                apply(rule exI[where x = "Suc n''"])
                by(sep_auto)
              done
            done
        qed
        done
      done  
  next
    case False
    then show ?thesis 
        apply(sep_auto heap: ref_lookup_2)
        (* TODO: work around *)
       apply(rule fi_rule[OF realize_aux])
       by sep_auto+
   qed
   done

 
definition create_la where
  "create_la n x = do {
    a \<leftarrow> Array.new n x;
    array_to_la a
  }"

definition test where "test = do {
  r \<leftarrow> create_la 3 (5::nat);
  y  \<leftarrow> update r 1 (7::nat);
  y' \<leftarrow> update r 1 (8::nat);
  x \<leftarrow> lookup y 1;
  return x
}"

ML_val \<open>@{code test} ()\<close>

export_code test in SML_imp module_name foo

lemma nth_undefined: "i \<ge> length xs \<Longrightarrow> xs ! i = undefined(i - length xs)"
  apply(induction xs arbitrary: i)
   apply auto
  unfolding List.nth_def
  apply simp
  done

definition array_nth_safe where
  "array_nth_safe arr i = do {
    len \<leftarrow> Array.len arr;
    if i < len
    then Array.nth arr i
    else do { 
      xs \<leftarrow> Array.freeze arr;
      return (xs ! i)
    }
  }"

definition array_update_safe where
  "array_update_safe i v arr = do {
    len \<leftarrow> Array.len arr;
    if i < len
    then Array.upd i v arr
    else do { 
      return arr
    }
  }"

value "(xs[1 := 2], xs[1 := 3])"

definition test1 where
  "test1 xs = (let c1 = 1; c2 = 2; c3 = 3; t1 = xs[c1 := c2]; t2 = t1[c1 := c3]; t3 = t2 ! c2 in t3)"

lemma array_nth_safe [sep_heap_rules]: "<arr \<mapsto>\<^sub>a xs> array_nth_safe arr i <\<lambda>res. \<up>(res = xs ! i) * arr \<mapsto>\<^sub>a xs>"
  unfolding array_nth_safe_def
  by(sep_auto simp: nth_undefined)

lemma array_update_safe [sep_heap_rules]:
  "<arr \<mapsto>\<^sub>a xs> array_update_safe i v arr <\<lambda>res. \<up>(res = arr) * arr \<mapsto>\<^sub>a xs[i := v]>"
  unfolding array_update_safe_def
  by(sep_auto)

definition hnr where "hnr \<Gamma> c \<Gamma>' R a = <\<Gamma>> c <\<lambda>r. \<Gamma>' * R a r>\<^sub>t"

lemmas hnrD = hnr_def[THEN iffD1]
lemmas hnrI = hnr_def[THEN iffD2]

definition id_assn where "id_assn a c = \<up>(c = a)"

lemma hnr_return: "hnr \<Gamma> (return x) \<Gamma> id_assn x"
  unfolding hnr_def id_assn_def
  by sep_auto

lemma hnr_let:
  assumes 
    "hnr \<Gamma> vi \<Gamma>\<^sub>1 R\<^sub>1 v" 
    "\<And>xi x. hnr (\<Gamma>\<^sub>1 * R\<^sub>1 x xi) (fi xi) \<Gamma>' R (f x)"
  shows 
    "hnr \<Gamma> (do { x \<leftarrow> vi; fi x }) \<Gamma>' R (let x = v in f x)"
  supply[sep_heap_rules] = assms[THEN hnrD]
  apply(rule hnrI)
  by sep_auto

lemma hnr_array_nth: "hnr (xsi \<mapsto>\<^sub>a xs * id_assn i ii) (array_nth_safe xsi ii) (xsi \<mapsto>\<^sub>a xs * id_assn i ii) id_assn (xs ! i)"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

abbreviation array_assn where "array_assn xs xsi \<equiv> xsi \<mapsto>\<^sub>a xs"

lemma hnr_array_update: "hnr (xsi \<mapsto>\<^sub>a xs * id_assn i ii * id_assn v vi) 
           (array_update_safe ii vi xsi) 
           (id_assn i ii * id_assn v vi) array_assn (xs [i:= v])"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_pass: "hnr (id_assn x xi) (return xi) emp id_assn x"
  unfolding id_assn_def
  apply(rule hnrI)
  by sep_auto

lemma hnr_frame:
  assumes
    "hnr \<Gamma> fi \<Gamma>' R f"
    "\<Gamma>\<^sub>P \<Longrightarrow>\<^sub>A \<Gamma> * F"
  shows
    "hnr \<Gamma>\<^sub>P fi (\<Gamma>' * F) R f"
  sorry

(* for ifs and my arrays *)

schematic_goal "hnr (array_assn xs xsi) (?c :: ?'a Heap) ?\<Gamma>' ?R (test1 xs)"
  unfolding test1_def 
  apply(rule hnr_let hnr_return)+
  apply(rule hnr_frame[OF hnr_array_update], frame_inference)
  apply(rule hnr_let)
   apply(rule hnr_frame[OF hnr_array_update], frame_inference)
  apply(rule hnr_let)
   apply(rule hnr_frame[OF hnr_array_nth], frame_inference)
 
  apply(rule hnr_frame[OF hnr_pass])
  sorry
  
  

export_code array_nth_safe array_update_safe in SML_imp

