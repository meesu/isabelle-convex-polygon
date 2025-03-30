theory Four_Convex
imports Definitions
begin

lemma convex_pos_inherit': 
  assumes "convex_pos S"
  shows "\<forall> A \<subseteq> S. convex_pos (S - A)"
  unfolding convex_pos_def
proof(rule ccontr)
  assume "\<not> (\<forall>A\<subseteq>S. \<forall>s\<in>S - A. convex hull (S - A) \<noteq> convex hull (S - A - {s}))"
  then obtain A s where es:"A\<subseteq>S" "s\<in>S-A" "convex hull (S-A) = convex hull (S-A-{s})" 
    by blast
  hence "convex hull S = convex hull (S-{s})"
    by (smt (verit, ccfv_SIG) Diff_mono Diff_subset hull_inc hull_mono hull_redundant insert_Diff
        insert_mono rel_interior_empty rel_interior_subset subset_iff)
  thus False using assms convex_pos_def es(2) by blast
qed

lemma convex_pos_inherit0: 
  assumes "convex_pos S"
  shows "\<forall> e \<in> S. convex_pos (S - {e})"
  unfolding convex_pos_def
proof(rule ccontr)
  assume "\<not> (\<forall>e\<in>S. \<forall>s\<in>S - {e}. convex hull (S - {e}) \<noteq> convex hull (S - {e} - {s}))"
  then obtain e s where es:"e\<in>S" "s\<in>S-{e}" "convex hull (S-{e}) = convex hull (S-{e}-{s})" 
    by blast
  hence "convex hull S = convex hull (S-{s})"
    by (metis Diff_insert hull_insert insert_Diff_single insert_absorb insert_commute member_remove
        remove_def)
  thus False using assms convex_pos_def es(2) by blast
qed

lemma convex_pos_inherit: 
  assumes "convex_pos S"
  shows "\<forall> X \<subseteq> S. convex_pos X"
proof(rule ccontr)
  assume "\<not> (\<forall> X \<subseteq> S. convex_pos X)"
  then obtain X where X:"X \<subseteq> S" "\<not> (convex_pos X)" by auto
  then obtain x where x:"x \<in> X" "convex hull X = convex hull (X - {x})"
    unfolding convex_pos_def by blast
  then have "x \<in> convex hull (X - {x})" 
    by (metis hull_inc)
  then have "x \<in> convex hull ((X - {x}) \<union> (S - X))" 
    by (meson hull_mono in_mono sup.cobounded1)
  moreover have "((X - {x}) \<union> (S - X)) = (S - {x})" 
    using X(1) x(1) by fast
  ultimately have "x \<in>  convex hull (S - {x})" by simp
  hence "convex hull S = convex hull (S - {x})" using x(1) X(1) 
    by (metis hull_redundant in_mono insert_Diff)
  thus False using x(1) X(1) assms 
    using convex_pos_def by auto
qed

(*if every subset of S of cardinality four is in a convex position, 
then S is in a convex position. This is a proof of lemma 2.1*)
lemma four_convex:
  assumes "\<forall>X \<subseteq> (S::(real \<times> real) set). card X \<le> 4 \<longrightarrow> convex_pos X"
  shows "convex_pos S"
proof(rule ccontr)
  assume asm:"\<not> convex_pos S"
  then obtain p where p:"p \<in> S" "convex hull S = convex hull (S - {p})"
    using asm unfolding convex_pos_def by blast
  then have "p \<in> convex hull (S - {p})"
    using hull_inc by fastforce
  then obtain T where t:"finite T" "T \<subseteq> S - {p}" "card T \<le> DIM(real\<times>real) + 1" "p\<in>convex hull T" 
    using caratheodory[of "S-{p}"] by blast
  hence c1:"\<not> convex_pos (T\<union>{p})" unfolding convex_pos_def
    by (simp add: hull_insert insert_absorb subset_Diff_insert)
  have c2:"card (T\<union>{p}) \<le> 4" using t
    by (simp add: subset_Diff_insert)
  have "T\<union>{p} \<subseteq> S" using t(2) p(1) by auto
  thus False using c1 c2
    by (simp add: assms)
qed

lemma convex_four:
  assumes "convex_pos S"
  shows "\<forall>X \<subseteq> (S::(real \<times> real) set). card X \<le> 4 \<longrightarrow> convex_pos X"
  using assms convex_pos_inherit by auto

theorem fourConvexfour:
"convex_pos S = (\<forall>X \<subseteq> (S::(real \<times> real) set). card X \<le> 4 \<longrightarrow> convex_pos X)"
  using convex_four four_convex by blast
end