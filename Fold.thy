theory Fold imports Main begin


fun
  foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
  foldl_Nil: "foldl f b [] = b" |
  foldl_Cons: "foldl f b (a#as) = foldl f (f b a) as"


fun
  foldr :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
  foldr_rev: "foldr f b as = foldl f b (rev as)"


theorem abel_semigroup_flip: "\<lbrakk> abel_semigroup f \<rbrakk> \<Longrightarrow> f (f b a1) a2 = f (f b a2) a1"
  apply(unfold abel_semigroup_def semigroup_def abel_semigroup_axioms_def)
  apply(clarify)
  apply(frule_tac x=b and P="\<lambda>a. \<forall>b c. f (f a b) c = f a (f b c)" in spec)
  apply(drule_tac x=a1 and P="\<lambda>ba. \<forall>c. f (f b ba) c = f b (f ba c)" in spec)
  apply(drule_tac x=a2 and P="\<lambda>c. f (f b a1) c = f b (f a1 c)" in spec)
  apply(erule ssubst)
  apply(drule_tac x=a1 and P="\<lambda>a. \<forall>b. f a b = f b a" in spec)
  apply(drule_tac x=a2 and P="\<lambda>b. f a1 b = f b a1" in spec)
  apply(erule ssubst)
  apply(drule_tac x=b and P="\<lambda>a. \<forall>b c. f (f a b) c = f a (f b c)" in spec)
  apply(drule_tac x=a2 and P="\<lambda>ba. \<forall>c. f (f b ba) c = f b (f ba c)" in spec)
  apply(drule_tac x=a1 in spec)
  apply(erule subst)
  apply(rule refl)
  done


lemma foldl_flip_ends: "\<lbrakk> abel_semigroup f \<rbrakk> \<Longrightarrow> foldl f b (xs@[x]) = foldl f b (x#xs)"
  apply(induction xs arbitrary: b)
  apply(subst append_Nil)
  apply(rule refl)
  apply(subst foldl_Cons)
  apply(subst foldl_Cons)
  apply(subst abel_semigroup_flip[of "f"])
  apply(assumption)
  apply(subst foldl_Cons[symmetric])
  apply(subst append_Cons)
  apply(subst foldl_Cons)
  apply(drule_tac x="f b a" in meta_spec)
  apply(erule meta_mp)
  apply(assumption)
  done


lemma foldl_rev: "\<lbrakk> abel_semigroup f \<rbrakk> \<Longrightarrow> foldl f b (rev as) = foldl f b as"
  apply(induction as arbitrary: b)
  apply(subst rev.simps(1))
  apply(rule refl)
  apply(subst foldl_Cons)
  apply(subst rev.simps(2))
  apply(subst foldl_flip_ends)
  apply(assumption)
  apply(subst foldl_Cons)
  apply(drule_tac x="f b a" in meta_spec)
  apply(assumption)
  done


theorem foldlr_iff: "\<lbrakk> abel_semigroup f \<rbrakk> \<Longrightarrow> foldl f b as = foldr f b as"
  apply(subst foldr_rev)
  apply(subst foldl_rev)
  apply(assumption)
  apply(rule refl)
  done
end