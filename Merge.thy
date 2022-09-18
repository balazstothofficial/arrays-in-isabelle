theory Merge
  imports Base
begin

definition Merge where
  "Merge \<Gamma>\<^sub>a \<Gamma>\<^sub>b \<Gamma>\<^sub>c \<equiv> \<Gamma>\<^sub>a \<or>\<^sub>A \<Gamma>\<^sub>b \<Longrightarrow>\<^sub>A \<Gamma>\<^sub>c"

lemma merge_refl: "Merge \<Gamma> \<Gamma> \<Gamma>"
  unfolding Merge_def
  by simp

(* TODO: Require `normalize` before each merge, then this won't be necessary anymore *)
method merge = (simp only: star_aci)?, rule merge_refl

end
