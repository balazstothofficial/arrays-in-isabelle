theory Merge
  imports Base
begin

definition Merge where
  "Merge a b c \<equiv> a \<or>\<^sub>A b \<Longrightarrow>\<^sub>A c"

lemma merge_refl: "Merge a a a"
  unfolding Merge_def
  by simp

method merge = (simp only: star_aci)?, rule merge_refl

end
