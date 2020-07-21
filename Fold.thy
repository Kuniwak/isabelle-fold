theory Fold imports Main begin

fun foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
  foldl_Nil: "foldl f b [] = b" |
  foldl_Cons: "foldl f b (a#as) = foldl f (f b a) as"

lemma foldl_Cons_sym: "foldl f (f b a) as = foldl f b (a#as)"
  apply(subst foldl_Cons)
  apply(rule refl)
  done

lemma foldl_append1[iff]: "foldl f b (as@[a]) = f (foldl f b as) a"
  apply(induction as arbitrary: b)
  apply(simp)
  apply(subst foldl_Cons)
  apply(subgoal_tac "(aa#as)@[a] = aa#(as@[a])")
  apply(erule_tac t="(aa#as)@[a]" in ssubst)
  apply(subst foldl_Cons)
  apply(auto)
  done

fun foldr :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
  foldr_rev: "foldr f b as = foldl f b (rev as)"

lemma foldr_Nil: "foldr f b [] = b"
  apply(auto)
  done

lemma foldr_rev_sym: "foldl f b (rev as) = foldr f b as"
  apply(subst foldr_rev)
  apply(rule refl)
  done

definition pseudo_commute :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "pseudo_commute f \<equiv> (\<forall>b a1 a2. f (f b a1) a2 = f (f b a2) a1)"

theorem pseudo_commute_iff[iff]: "\<lbrakk> pseudo_commute f \<rbrakk> \<Longrightarrow> f (f b a1) a2 = f (f b a2) a1"
  apply(unfold pseudo_commute_def)
  apply(drule_tac x=b in spec)
  apply(drule_tac x=a1 in spec)
  apply(erule_tac x=a2 in spec)
  done

lemma foldl_flip_ends: "\<lbrakk> pseudo_commute f \<rbrakk> \<Longrightarrow> foldl f b (xs@[x]) = foldl f b (x#xs)"
  apply(induction xs arbitrary: b)
  apply(subst append_Nil)
  apply(rule refl)
  apply(subst foldl_Cons)
  apply(subst foldl_Cons)
  apply(subst pseudo_commute_iff[of "f"])
  apply(assumption)
  apply(subst foldl_Cons_sym)
  apply(subst append_Cons)
  apply(subst foldl_Cons)
  apply(drule_tac x="f b a" in meta_spec)
  apply(erule meta_mp)
  apply(assumption)
  done

lemma foldl_rev: "\<lbrakk> pseudo_commute f \<rbrakk> \<Longrightarrow> foldl f b (rev as) = foldl f b as"
  apply(induction as arbitrary: b)
  apply(simp)
  apply(subst foldl_Cons)
  apply(subgoal_tac "rev (a#as) = (rev as)@[a]")
  apply(erule ssubst)
  apply(subst foldl_flip_ends)
  apply(assumption)
  apply(subst foldl_Cons)
  apply(drule_tac x="f b a" in meta_spec)
  apply(assumption)
  apply(simp)
  done

theorem foldlr_iff: "\<lbrakk> pseudo_commute f \<rbrakk> \<Longrightarrow> foldl f b as = foldr f b as"
  apply(subst foldr_rev)
  apply(subst foldl_rev)
  apply(assumption)
  apply(rule refl)
  done

definition assoc :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "assoc f \<equiv> \<forall>a b. f a b = f b a"

definition commute :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "commute f \<equiv> \<forall>a b c. f (f a b) c = f a (f b c)"

theorem pseudo_commuteI[intro]: "\<lbrakk> assoc f; commute f \<rbrakk> \<Longrightarrow> pseudo_commute f"
  apply(unfold assoc_def)
  apply(unfold commute_def)
  apply(unfold pseudo_commute_def)
  apply(intro allI)
  apply(frule_tac x="b" and P="\<lambda>a. \<forall>b c. f (f a b) c = f a (f b c)" in spec)
  apply(drule_tac x="a1" and P="\<lambda>ba. \<forall>c. f (f b ba) c = f b (f ba c)" in spec)
  apply(drule_tac x="a2" and P="\<lambda>c. f (f b a1) c = f b (f a1 c)" in spec)
  apply(erule ssubst)
  apply(drule_tac x="a1" and P="\<lambda>a. \<forall>b. f a b = f b a" in spec)
  apply(drule_tac x="a2" and P="\<lambda>b. f a1 b = f b a1" in spec)
  apply(erule ssubst)
  apply(drule_tac x="b" in spec)
  apply(drule_tac x="a2" in spec)
  apply(drule_tac x="a1" in spec)
  apply(erule subst)
  apply(rule refl)
  done

theorem "\<lbrakk> assoc f; commute f \<rbrakk> \<Longrightarrow> foldl f b as = foldr f b as"
  apply(drule pseudo_commuteI)
  apply(assumption)
  apply(erule foldlr_iff)
  done