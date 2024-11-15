theory Cups_to_Convex
imports Main EZ_bound
begin

(*the following lemma proves that if a list of points is an n-cap, then they are 
convex position, that is form the corner points of a convex hull*)
lemma fixes n
  assumes "cap n xs"
  shows "convex_pos (set xs)"
proof(induction xs)
  case Nil
  then show ?case unfolding convex_pos_def by simp
next
  case (Cons a xs)
  then show ?case sorry
qed

(*following lemma is needed for proving the bound*)
lemma fixes n
  shows "((2*n - 4) choose (n - 2)) + 1 \<le> 4^n"
proof(induction n)
  case 0
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed

end
