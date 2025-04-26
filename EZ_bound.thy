theory EZ_bound
imports Four_Convex Definitions
begin

(*** start of Theorem 2.2 Andrew Suk ***)

lemma ex_equiv_minconv:
  " (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs)) \<longrightarrow>
    (\<exists>xs. (set xs \<subseteq> S \<and> (sortedStrict xs)) \<longrightarrow> (cap k xs \<or> cup l xs))"
  by blast

lemma cross3_commutation_12[simp]: "cross3 x y z = 0 \<longrightarrow> cross3 y x z = 0"
  unfolding cross3_def by argo

lemma cross3_commutation_23[simp]: "cross3 x y z = 0 \<longrightarrow> cross3 x z y = 0"
  unfolding cross3_def by argo

lemma cross3_non0_distinct: "cross3 a b c \<noteq> 0 \<longrightarrow> distinct [a,b,c]" 
  unfolding cross3_def 
  by (metis cross3_commutation_23 cross3_def diff_self distinct_length_2_or_more
      distinct_singleton mult_zero_left mult_zero_right) 

lemma cap_reduct:
  assumes "cap (k+1) (a#xs)"
  shows "cap k xs"
  using assms add_left_cancel length_Cons list.distinct(1) list.inject list_check.elims(2)
  unfolding cap_def by fastforce

lemma cup_reduct:
  assumes "cup (k+1) (a#xs)"
  shows "cup k xs"
  using assms add_left_cancel length_Cons list.distinct(1) list.inject list_check.elims(2)
  unfolding cup_def by fastforce

lemma  card_of_s:
  assumes "set xs \<subseteq> S" "cap k xs" "distinct xs" "finite S"
  shows "card S \<ge> k"
  by (metis assms cap_def card_mono distinct_card)

theorem non_empty_cup_cap:
  fixes k l
  shows "{} \<noteq> {n :: nat. (\<forall>S :: R2 set. (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs)))}"
  sorry

lemma assumes "(X::nat set) \<noteq> {}" 
        shows "\<exists>S \<in> X. Inf X = S"
  using assms 
  by (simp add: Inf_nat_def1)

lemma fixes S
      assumes "finite S"
      shows "\<exists>xs.  length xs = card S \<and> set xs = S"
  using assms 
  by (metis distinct_card finite_distinct_list)

lemma set2list:
  assumes "finite (S :: R2 set)"
  shows   "\<exists>!xs. set xs = S \<and> sortedStrict xs \<and> distinct xs \<and> length xs = card S"
  using finite_sorted_distinct_unique[of "S"] strict_sorted_iff distinct_card assms
  by metis

lemma general_pos_subs:
  assumes "X \<subseteq> Y" and "general_pos Y"
  shows "general_pos X"
proof(rule ccontr)
  assume "\<not>general_pos X"
  then obtain S where S:"S \<in> X~ 3" "affine_dependent S" unfolding general_pos_def by blast
  have "S \<in> Y~3" using assms(1) unfolding nsubset_def 
    by (smt (verit) S mem_Collect_eq nsubset_def order_trans)  
  thus False using S(2) assms(2) unfolding general_pos_def by simp 
qed

lemma extract_cap_cup:
    assumes "min_conv k l = n"
        and "card (S :: R2 set) = n" 
        and "general_pos S"
        and "sdistinct(sorted_list_of_set S)"
      shows "\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs)"
  using assms Inf_nat_def1
  by (smt (verit, ccfv_threshold) assms(1) mem_Collect_eq min_conv_def non_empty_cup_cap order_refl)
(* lemma noname
lemma 
  assumes "cup k (y#z#ws)" and "x < y"
      and "\<not> cup (Suc k) (x#y#z#ws)"
    shows "(cross3 x y z) \<le> 0"
  using assms unfolding cup_def list_check.simps cup3_def
proof-
  have "sdistinct (x#y#z#ws)" using assms(1,2) unfolding cup_def sledgehammer
  moreover have "length (x#y#z#ws) = Suc k" 
    using assms(1) cup_def by force
  ultimately have 1:"\<not>list_check cup3 (x#y#z#ws)" using assms(3) unfolding cup_def
    by presburger
  then show ?thesis unfolding list_check.simps(4) unfolding cup3_def
    using assms(1) unfolding cup_def cup3_def  by argo
qed
*)
lemma affine_comb_affine_dep:
  assumes "(u :: real) \<ge> 0" and "x = (1 - u) *\<^sub>R y + u *\<^sub>R (z :: R2)" 
      and "distinct [x, y, z]"
    shows "affine_dependent {x, y, z}"
proof-
  have "x \<in> affine hull {y, z}" using assms affine_def hull_def by force
  thus ?thesis using assms by (simp add: affine_dependent_def)
qed

lemma pair_scal:"c *\<^sub>R u = (c * fst u, c * snd u)"
  by (simp add: scale_def)

(*this tells us that if cross product of three elements is 0 then they are 
affine dependent*)

lemma lindep_cross3_0:
  assumes "(x :: R2) = u *\<^sub>R y + (1 - (u :: real)) *\<^sub>R z"
  shows   "cross3 x y z = 0"
proof-
  have 1: "fst y - fst x =  (1 - u) * (fst y - fst z)" using assms by (simp, argo)
  have 2: "snd z - snd x =      - u * (snd y - snd z)" using assms by (simp, argo)
  have 3: "fst z - fst x =      - u * (fst y - fst z)" using 1 by argo
  have    "snd y - snd x =  (1 - u) * (snd y - snd z)" using 2 by argo
  thus ?thesis unfolding cross3_def using 1 2 3 
    by (smt (verit, best) minus_mult_minus mult.commute
        vector_space_over_itself.scale_scale) 
qed

lemma in_hull3_iscollinear: 
  assumes "(x :: R2) \<in> affine hull {y, z}"
  shows "cross3 x y z = 0"
proof-
  have "\<exists>v\<ge>0.\<exists>u\<ge>0. (u+v = 1) \<longrightarrow> (x = u *\<^sub>R y + v *\<^sub>R z)" 
    using assms unfolding hull_def affine_def by force
  then obtain u v where "u+v = 1" "x = u *\<^sub>R y + v *\<^sub>R z"
    using assms affine_hull_2 by fastforce
  thus ?thesis using lindep_cross3_0 assms    by (smt (verit))
qed

lemma distinct_snd_case_aux:
  assumes "distinct [snd x, snd y, snd z :: real]" 
      and "fst x = fst y" and "fst y = fst z"
  shows "affine_dependent {x, y, z :: R2}"
proof-
  have 1: "snd z - snd x \<noteq> 0" using assms(1) by force
  define u where u_def: "u = (snd y - snd x) / (snd z - snd x)"
  have  "snd y * (snd z - snd x) = (snd z - snd y) * snd x + (snd y - snd x) * snd z" by argo
  hence "snd y = ((snd z - snd y) / (snd z - snd x)) * snd x +  u * snd z" unfolding u_def
    by (smt (verit, ccfv_SIG) diff_divide_eq_iff times_divide_eq_left assms(1) 1)
  hence "snd y = (1 - u) * snd x + u * snd z" unfolding u_def 
    using assms add_divide_distrib divide_eq_1_iff by (smt (verit, ccfv_SIG) "1")
  hence "y = (1 - u) *\<^sub>R x + u *\<^sub>R z" using assms
    by (smt (verit, best) add_diff_cancel_left' fst_diff fst_scaleR prod_eq_iff 
        real_scaleR_def scaleR_collapse snd_add snd_scaleR)
  thus ?thesis using affine_comb_affine_dep assms(1)
    by (smt (verit, best) add.commute distinct_length_2_or_more distinct_singleton insert_commute)
qed 

lemma swap_coords:
  assumes "x = u *\<^sub>R y + (1 - u) *\<^sub>R (z :: R2)"
  shows   "prod.swap x = u *\<^sub>R prod.swap y + (1 - u) *\<^sub>R prod.swap z"
  using assms by (simp add: scaleR_prod_def)

lemma affine_swap:
  assumes "affine S"
  shows   "affine (prod.swap ` S)"
  using assms unfolding affine_def by force

(*"S hull s = \<Inter>{t. S t \<and> s \<subseteq> t}"*)
lemma hull_swap_1: 
  "prod.swap ` (affine hull s) \<subseteq> affine hull prod.swap ` s"
    unfolding hull_def
proof
  fix x assume "x \<in> prod.swap ` \<Inter> {t. affine t \<and> s \<subseteq> t}"
  hence "x \<in> \<Inter>{prod.swap ` t| t. affine t \<and> s \<subseteq> t}" by force
  hence "\<forall>t. affine t \<and> s \<subseteq> t \<longrightarrow> x \<in> prod.swap ` t" by blast
  hence "\<forall>t. affine (prod.swap ` t) \<and> prod.swap ` s \<subseteq> prod.swap ` t \<longrightarrow> x \<in> prod.swap ` t"
    by (metis (no_types, lifting) ext affine_swap image_ident image_image image_mono swap_swap)  
  hence "\<forall>t. affine t \<and> prod.swap ` s \<subseteq> t \<longrightarrow> x \<in> t" 
    by (metis subset_imageE surj_swap top_greatest)
  hence "x \<in> \<Inter> {t. affine t \<and> prod.swap ` s \<subseteq> t}" by blast
  thus  "x \<in> \<Inter> {t. affine t \<and> prod.swap ` s \<subseteq> t}" by blast
qed

lemma hull_swap_2: 
  "affine hull prod.swap ` s \<subseteq> prod.swap ` (affine hull s)"
  by (simp add: affine_swap hull_minimal hull_subset image_mono)

lemma hull_swap: 
  "prod.swap ` (affine hull (s :: R2 set)) =  affine hull prod.swap ` s"
  using hull_swap_1 hull_swap_2 by blast

lemma cross_affine_dep_aux3:
  assumes "affine_dependent (S :: R2 set)"
  shows   "affine_dependent (prod.swap ` S)"
  using swap_coords assms affine_swap hull_swap unfolding affine_dependent_def
  by (smt (verit) Diff_insert_absorb image_iff image_insert mk_disjoint_insert swap_swap)

lemma cross_affine_dependent_aux1:
  assumes "(y1 - x1) * (z2 - y2) - (z1 - y1) * (y2 - x2) = 0" 
      and "distinct [(x1, x2), (y1, y2), (z1, z2)]" 
      and "y1 = x1"
  shows   "affine_dependent {(x1, x2), (y1, y2), (z1, z2) :: R2}"
proof-
  have "(z1 - x1) * (y2 - x2) = 0" using assms by simp
  then have 1: "z1 = x1 \<or> y2 = x2" by simp
  then show ?thesis
  proof(cases "z1 = x1")
    case True
    hence "distinct [x2, y2, z2]" using assms distinct_singleton prod_eq_iff
      by (smt (verit, del_insts) distinct_length_2_or_more vector_space_over_itself.scale_eq_0_iff)
    then show ?thesis using distinct_snd_case_aux[of "(x1, x2)" "(y1, y2)" "(z1, z2)"] True assms
      by (smt (verit, best) distinct_length_2_or_more distinct_snd_case_aux fst_conv insert_commute snd_conv)
  next
    case False
    then have "(y1, y2) = (x1, x2)" using "1" assms prod_eq_iff by blast 
    thus ?thesis using assms(2) by simp
  qed
qed

lemma cross_affine_dependent: 
  assumes "cross3 x y z = 0" and "distinct [x, y, z]"
  shows   "affine_dependent {x, y, z :: R2}"
proof(cases "fst y = fst x")
  case True
  thus ?thesis using cross_affine_dependent_aux1 cross3_def assms(1,2) surjective_pairing
    by (smt (verit) mult_eq_0_iff)
next
  case False
  then show ?thesis
  proof(cases "snd y = snd x")
    case True
    then show ?thesis 
      using cross_affine_dependent_aux1[of "snd y" "snd x" "fst z" "fst y" "snd z" "fst x"] assms(1,2)
        cross3_def surjective_pairing cross_affine_dep_aux3[of "(prod.swap ` {x, y, z})"] prod.swap_def
      by (smt (verit, ccfv_SIG) distinct_length_2_or_more distinct_singleton image_empty
          image_insert mult_eq_0_iff swap_simp)      
  next
    case False
    assume a1: "fst y \<noteq> fst x"
    define "u" where u_def: "u = (fst z - fst y) / (fst y - fst x)"
    then have  "fst z = fst y - u * fst x + u * fst y" using "False" a1
      by (simp add: nonzero_eq_divide_eq right_diff_distrib)
    then have "fst z = (1 + u) * (fst y) - u * fst x"
      by argo
    then have z1:"fst z = (- u) * fst x + (1 + u) * (fst y) "
      by simp
    have "u = (snd z - snd y) / (snd y - snd x)" using u_def assms a1 
      by (simp add: False cross3_def frac_eq_eq mult.commute )
    then have "snd z = snd y - u * snd x + u * snd y" using "False" a1
      by (simp add: nonzero_eq_divide_eq right_diff_distrib)
    then have "snd z = (-u) * snd x + (1 + u) * snd y"
      by argo
     then have "z = (- u) *\<^sub>R x + (1 + u) *\<^sub>R y" using assms a1 False z1
      by (metis (mono_tags, lifting) add.commute add_left_cancel diff_add_cancel fst_diff
          fst_scaleR pair_scal real_scaleR_def  scaleR_one snd_diff snd_scaleR)
    then show "affine_dependent {x, y, z :: R2}"
      by (smt (verit, del_insts) add_diff_cancel_left' affine_comb_affine_dep assms(2)
          diff_add_cancel distinct_length_2_or_more insert_commute)
  qed
qed

lemma affinedep_cases:
  assumes "affine_dependent {x, y, z :: real \<times> real}"
  shows "x \<in> affine hull {y, z} \<or> y \<in> affine hull {x, z} \<or> z \<in> affine hull {x, y}"
  using assms unfolding affine_dependent_def hull_redundant_eq
  by (smt (verit, ccfv_SIG) Diff_insert_absorb insert_absorb insert_commute insert_not_empty)

lemma cross_affine_dependent_conv:
  assumes "affine_dependent {x, y, z :: real \<times> real}"
  shows "cross3 x y z = 0"
  using affinedep_cases assms cross3_commutation_12 
        cross3_commutation_23 in_hull3_iscollinear 
  by blast

lemma genpos_cross0:
  assumes "general_pos S" and "x \<in> S" and "y \<in> S" and "z \<in> S" and "distinct [x, y, z]"
  shows "cross3 x y z \<noteq> 0"
  using assms nsubset_def general_pos_def cross_affine_dependent
  by (smt (verit, del_insts) add.right_neutral add_Suc_right distinct_card empty_set 
      empty_subsetI insert_subset list.simps(15) list.size(3,4) mem_Collect_eq numeral_3_eq_3)

lemma exactly_one_true:
  assumes "A = collinear3 a b c" and "B = cap3 a b c" and "C = cup3 a b c"
  shows "(A \<or> B \<or> C) \<and> ((\<not>A \<and> \<not>B) \<or> (\<not>B \<and> \<not>C) \<or> (\<not>C \<and> \<not>A))"
  using assms unfolding collinear3_def cap3_def cup3_def by linarith

lemma lcheck_len2_T:
  assumes "length P \<le> 2" and "sdistinct P" shows "list_check f P"
proof(cases "length P = 2")
  case True
  hence "\<exists>x y. P=[x,y] \<and> sdistinct [x,y]" using assms(2)
    by (metis (no_types, lifting) One_nat_def Suc_1  length_0_conv length_Suc_conv)
  then show ?thesis using list_check.simps(3) by fastforce
next
  case False
  hence "(P = []) \<or> (\<exists>x. P=[x])"
    by (metis assms(1) length_0_conv length_Suc_conv less_2_cases_iff nat_less_le)
  then show ?thesis by fastforce
qed

lemma bad3_from_bad:
  assumes "sdistinct P" and "\<not> list_check cc P"
  shows   "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cc a b c"
  using assms
proof(induction "length P" arbitrary: P)
  case (Suc x)
  then show ?case
  proof(cases "length P \<le> 2")
    case False
    hence "\<exists>a u v rest. P = (a#u#v#rest)" using Suc(2) Suc.prems(2) assms(1) list.size(3)
      by (metis One_nat_def Suc_1 bot_nat_0.extremum length_Cons list.exhaust not_less_eq_eq)
    then obtain a u v rest where aP: "P = (a#u#v#rest)" by blast
    hence "\<not> cc a u v \<or> \<not> list_check cc (u#v#rest)" using Suc by simp
    then show ?thesis
    proof
      assume "\<not> cc a u v"
      thus "\<exists>a b c. sublist [a, b, c] P \<and> \<not> cc a b c" using aP
        by (metis append_Cons append_Nil sublist_append_rightI)
    next
      assume "\<not> list_check cc (u#v#rest)"
      moreover have "length (u#v#rest) = x" using aP Suc(2) by simp
      moreover have "sdistinct (u#v#rest)" using Suc(3) aP by simp
      ultimately have "\<exists>a b c. sublist [a, b, c] (u#v#rest) \<and> \<not> cc a b c" using Suc(1) by blast
      thus "\<exists>a b c. sublist [a, b, c] P \<and> \<not> cc a b c" using aP Suc by (meson sublist_Cons_right)
    qed
  qed(metis lcheck_len2_T)
qed(auto)

lemma get_cup_from_bad_cap:
  assumes "sdistinct P" and "\<not> cap (length P) P"
  shows "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cap3 a b c"
  using bad3_from_bad assms(1,2) cap_def
  by blast

lemma get_cap_from_bad_cup:
  assumes "sdistinct P" and "\<not> cup (length P) P"
  shows "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cup3 a b c"
  using bad3_from_bad assms(1,2) cup_def strict_sorted_iff by blast

lemma coll_is_affDep:
  "distinct [a,b,c] \<longrightarrow> (collinear3 a b c \<longleftrightarrow> affine_dependent {a, b, c})"
  using collinear3_def cross3_commutation_23 cross3_non0_distinct
    cross_affine_dependent cross_affine_dependent_conv by blast

lemma distinct_is_triple:
  "a\<in>S \<and> b\<in>S \<and> c\<in>S \<and> distinct [a,b,c] \<longleftrightarrow> {a,b,c} \<in> S ~ 3"
  by (smt (verit, del_insts) distinct.simps(2) distinct_card distinct_singleton
      empty_set empty_subsetI insert_absorb insert_subset length_Cons lessI
      list.set(2) list.size(3) mem_Collect_eq not_less_iff_gr_or_eq nsubset_def
      numeral_3_eq_3)

(*work with a simpler definition of general position*)
definition
  "gpos S \<equiv> \<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. distinct [a,b,c] \<longrightarrow> \<not> collinear3 a b c"
(*"general_pos S \<equiv>  (\<forall> P3 \<in> S~3. \<not> affine_dependent P3)"*)
lemma gpos_generalpos:
  "gpos S \<longleftrightarrow> general_pos S" 
  using coll_is_affDep distinct_is_triple nsubset_def[of "S" "3"] unfolding gpos_def general_pos_def
  by (smt (verit, ccfv_threshold) card_3_iff mem_Collect_eq)

definition v2 :: "real \<Rightarrow> R2" where "v2 \<equiv> \<lambda>a. (a, a * a)"
lemma f_prop0: "cross3 (v2 a) (v2 b) (v2 c) = (a - b) * (c - a) * (b - c)" 
  unfolding collinear3_def cross3_def v2_def by (simp, argo)
lemma f_prop1: "\<forall>x y. x \<noteq> y \<longleftrightarrow> v2 x \<noteq> v2 y"                  using v2_def fst_conv by metis
lemma f_prop2: "distinct [a,b,c] \<longrightarrow> distinct[v2 a, v2 b, v2 c]" using f_prop1 by auto
lemma f_prop3: "distinct [a,b,c] \<longrightarrow> \<not> collinear3 (v2 a) (v2 b) (v2 c)"
  using f_prop2 f_prop0 unfolding collinear3_def cross3_def v2_def by auto
lemma f_prop4: "sortedStrict [a,b,c] \<longrightarrow> cup3 (v2 a) (v2 b) (v2 c)" 
  using f_prop0 strict_sorted_iff unfolding cup3_def
  by (smt (verit, ccfv_threshold) distinct_length_2_or_more mult_eq_0_iff sorted2 zero_less_mult_iff)
lemma f_prop5: "sortedStrict (rev [a,b,c]) \<longrightarrow> cap3 (v2 a) (v2 b) (v2 c)"
  using f_prop4 f_prop3 exactly_one_true
  by (smt (verit, best) append.simps(1,2) cup3_def distinct_rev f_prop0 rev.simps(2) singleton_rev_conv sorted2 strict_sorted_iff zero_less_mult_iff)
lemma f_prop6: "sortedStrict S \<longrightarrow> gpos (v2 ` set S)"
  by (smt (verit, ccfv_SIG) collinear3_def distinct_length_2_or_more f_prop0 gpos_def image_iff mult_eq_0_iff)
lemma f_prop7: "(a :: real) > 0 \<longrightarrow> ((a < b) \<longrightarrow> (a*a < b*b))" by (simp add: mult_strict_mono)
lemma f_prop8: "((a > 0 \<and> (b::real) > 0) \<longrightarrow> (a*a < b*b) \<longrightarrow> (a < b))" by (metis antisym_conv3 f_prop7 order_less_asym')
lemma f_prop9: "sortedStrict[a,b] \<longleftrightarrow> sortedStrict[v2 a, v2 b]" using f_prop7 v2_def strict_sorted_iff
  by (metis (lifting) distinct_length_2_or_more less_prod_simp linorder_not_less not_less_iff_gr_or_eq sorted2
      sorted_wrt1)
lemma f_prop10: "sortedStrict [a,b,c] \<longleftrightarrow> sdistinct[v2 a, v2 b, v2 c]" using f_prop9
  by (smt (verit, best) distinct_length_2_or_more distinct_map fst_conv less_prod_simp linorder_not_less list.simps(8,9) sorted2 strict_sorted_iff v2_def)
lemma f_prop11: "sortedStrict L \<longrightarrow> sdistinct (map v2 L)" 
  by (smt (verit, del_insts) fst_conv imageE less_prod_simp list.set_map nless_le sorted_wrt_map_mono strict_sorted_iff v2_def)
lemma f_prop12: "sdistinct (map v2 L) \<Longrightarrow> cup (length (map v2 L)) (map v2 L)"
proof(induction L)
  case (Cons a L)
  then show ?case
  proof(cases "length (map v2 (a#L)) \<le> 2")
    case False
    then obtain x y z rest where aL: "a#L = x#y#z#rest"
      by (metis One_nat_def Suc_1 Suc_le_length_iff le_SucE length_Cons length_map nle_le)
    hence "sdistinct [v2 x,v2 y,v2 z]" 
      using Cons.prems by auto
    hence "cup3 (v2 x) (v2 y) (v2 z)" using f_prop4 f_prop10 by presburger
    then show ?thesis using Cons aL cup_def by force
  qed(metis lcheck_len2_T Cons(2) cup_def)
qed(simp add: cup_def)

thm card_le_inj

lemma real_set_ex: "\<exists>(S:: real set). card S = n"
  using infinite_UNIV_char_0 infinite_arbitrarily_large by blast

lemma genpos_ex:
  "\<exists>S. gpos S \<and> card S  = n \<and> (\<exists>Sr :: real set. S = (v2 ` Sr)) \<and> sdistinct(sorted_list_of_set S)"
proof-
  obtain X  where rset: "card (X :: real set) = n" using real_set_ex by blast
  hence 1:"card (v2 ` X) = n"  by (metis card_image f_prop1 inj_onI)
  have "gpos (v2 ` X)" using f_prop3 gpos_def
    by (smt (verit, best) distinct_length_2_or_more distinct_singleton image_iff)
  thus ?thesis using 1 rset f_prop10
    by (metis card_image distinct_map f_prop11 f_prop6 list.set_map
        sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set.length_sorted_key_list_of_set
        sorted_list_of_set.sorted_sorted_key_list_of_set
        sorted_list_of_set.strict_sorted_key_list_of_set)
qed

lemma sdistinct_subl:
  fixes   X Y :: "R2 list"
  assumes "sublist X Y" and "sdistinct Y"
  shows   "sdistinct X"
proof
  have "distinct (map fst Y)" using assms(2) by simp
  thus "distinct (map fst X)" sorry
next
  show "sorted X" using assms
  by (metis sorted_wrt_append sublist_def)
qed

lemma sdistinct_sub:
  fixes   A B :: "R2 set"
  assumes "A \<subseteq> B" and "sdistinct(sorted_list_of_set B)"
  shows   "sdistinct(sorted_list_of_set A)"
proof
  have "sublist (sorted_list_of_set A) (sorted_list_of_set B)" using assms(1) sorry
  thus "distinct (map fst (sorted_list_of_set A))" using sdistinct_subl assms(2) by simp
qed(simp)

lemma xyz:
  assumes "min_conv 3 k = k" and S_asm: "card S = Suc k" and S_gp: "general_pos S" and "sdistinct(sorted_list_of_set S)"
  shows "\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap 3 xs \<or> cup (Suc k) xs)"
  using assms
proof-
  obtain x xs where x_xs:"S = set (x#xs)" "sdistinct (x#xs)" "length (x#xs) = card S"
    using extract_cap_cup S_asm assms list.exhaust list.size(3) nat.simps(3)
    by (metis  card.infinite sorted_list_of_set.sorted_key_list_of_set_unique)
  
  have x_Min:"x = Min S" using x_xs
    by (metis S_asm card.empty card.infinite card_distinct list.inject old.nat.distinct(2) sorted_list_of_set.idem_if_sorted_distinct
        sorted_list_of_set_nonempty)

  have "length xs = k" using S_asm x_xs by auto
  hence sminus_x:"card (S - {x}) = k" using S_asm by (simp add: card.insert_remove x_xs(1))
  moreover have gp_sminus_x:"general_pos (S - {x})" using x_xs(1) S_gp general_pos_subs by blast
  text \<open>Using induction hypothesis obtain the cap of size 3 or cup of size k from the set S - {min(S)}.\<close>
  ultimately obtain zs where zs:"set zs \<subseteq> S - {x}" "(cap 3 zs \<or> cup k zs)"
    unfolding min_conv_def using assms extract_cap_cup x_xs
    by (metis (no_types, lifting) List.finite_set
        distinct.simps(2) empty_not_insert list.simps(15,9) sorted_list_of_set.sorted_sorted_key_list_of_set sorted_list_of_set_nonempty x_Min)
  have "\<exists>cc. set cc \<subseteq> S \<and> (cap 3 cc \<or> cup (Suc k) cc)"
  proof(cases "cap 3 zs")
    case True
    then show ?thesis using zs(1,2) by auto
  next
    case False
    hence F1:"cup k zs" using zs by simp
    hence F2:"length zs = k" unfolding cup_def by argo
    hence F0:"length (x#zs) = Suc k" using x_Min by auto
    have  F4:"set (x#zs) \<subseteq> S" using x_xs(1) zs(1) by auto
    have  F3:"sdistinct (x#zs)" using zs x_Min x_xs 
      by (metis (no_types, lifting) Diff_insert_absorb F0 F1 F4 assms(2) card.infinite card_subset_eq cup_def distinct_card distinct_map distinct_singleton insert_absorb
          length_0_conv list.set(2) set_empty2 sminus_x sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set_nonempty)
    then show ?thesis
    proof(cases "cup (Suc k) (x#zs)")
      case True
      then show ?thesis using x_xs(1) zs(1)
        by (metis Diff_empty insert_subset list.set_intros(1) list.simps(15) subset_Diff_insert)
    next
      case False
      hence "\<exists>a b c. (sublist [a,b,c] (x#zs)) \<and> \<not> cup3 a b c"
        using F0 F3 get_cap_from_bad_cup by presburger
      then obtain b1 b2 b3 where bcup:"sublist [b1,b2,b3] (x#zs)" "\<not> cup3 b1 b2 b3" by blast
      have fb1:"b1 \<in> S \<and> b2 \<in> S \<and> b3 \<in> S" 
        by (meson F4 bcup list.set_intros(1,2) set_mono_sublist subset_code(1))
      have fb2:"sdistinct [b1, b2, b3]" using bcup(1) F3 sdistinct_subl
        by presburger
(*         by (metis distinct_map strict_sorted_iff)
 *)      
      have fb3:"cross3 b1 b3 b2 \<noteq> 0" using S_gp fb1 cross3_commutation_23 fb2 genpos_cross0 by (metis distinct_map)
      have fb4:"length [b1, b2, b3] = 3" using fb2 by simp
      have     "cap3 b1 b2 b3" using fb3 bcup(2) cap3_def cup3_def not_less_iff_gr_or_eq
        by (metis cross3_commutation_23)
      hence "cap 3 [b1, b2, b3]" unfolding cap_def using fb2 fb4 by auto 
      thus ?thesis by (meson F4 bcup(1) dual_order.trans fb2 set_mono_sublist)
    qed
  qed
  thus ?thesis
    using cap_def cup_def by auto
qed

lemma abc:
  assumes "min_conv 3 k = k"
  shows "\<forall>S. (card S \<ge> Suc k) \<and> general_pos S \<and> 
              sdistinct(sorted_list_of_set S)
              \<longrightarrow> (\<exists>xs. (set xs \<subseteq> S) \<and> sdistinct xs \<and> (cap 3 xs \<or> cup (Suc k) xs))"
  using xyz assms sdistinct_sub general_pos_subs
  by (smt (verit, ccfv_threshold) dual_order.trans ex_card)

lemma inf_subset_bounds:
  assumes "X \<noteq> {}" and "(X :: nat set) \<subseteq> (Y :: nat set)"
  shows "Inf Y \<le> Inf X"
  by (simp add: assms(1,2) cInf_superset_mono)

lemma inf_upper:
  "x \<in> (S::nat set) \<longrightarrow> Inf S \<le> x"
  by (simp add: wellorder_Inf_le1)

lemma min_conv_num_out:
  assumes "\<exists>S.  card S \<ge> n \<and> general_pos S \<and> 
                sdistinct(sorted_list_of_set S) \<and> 
                (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  shows "min_conv k l \<noteq> n"
proof
  assume "min_conv k l = n"
  hence "\<forall>S . (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs))"
    by (smt (verit, del_insts) Inf_nat_def1 mem_Collect_eq min_conv_def non_empty_cup_cap)
  thus False
    using assms by blast
qed

lemma min_conv_lower:
  assumes "\<exists>S.  card S \<ge> n \<and> general_pos S \<and> 
                sdistinct(sorted_list_of_set S) \<and> 
                (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  shows "min_conv k l > n"
proof-
  obtain S where "card S \<ge> n" "general_pos S" 
          "sdistinct(sorted_list_of_set S)" 
          "\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs)"
    using assms by blast
  hence "\<forall>t. t \<le> n \<longrightarrow> min_conv k l \<noteq> t" using min_conv_num_out by (metis le_trans)
  thus ?thesis using min_conv_def not_le_imp_less by blast
qed

lemma min_conv_3_k_bnd:
  shows "min_conv 3 (Suc k) > k"
(*     and "\<exists>S. (card S = min_conv 3 (Suc k) - 1 \<and> general_pos S \<and> 
        sdistinct (sorted_list_of_set S)) \<and> 
        (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not> (cap 3 xs \<or> cup (Suc k) xs))"
 *)
proof-
  have "\<exists>S. (card S \<ge> k \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<and> (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap 3 xs \<or> cup (Suc k) xs))"
  proof-
    obtain L where Trp:"length (L :: real list) = k" "sortedStrict L" using real_set_ex set2list
      by (metis sorted_list_of_set.length_sorted_key_list_of_set
          sorted_list_of_set.strict_sorted_key_list_of_set)
    define V2L where v2lp:"V2L = map v2 L"
    hence v2l_k:  "length V2L = k" using Trp by force
    hence v2l_ss: "sdistinct V2L" using Trp(2) v2lp f_prop11 by simp
    hence         "cup k V2L" using f_prop4 v2lp v2l_k f_prop12 by blast
    have v2l_gp:  "general_pos (set V2L)" using f_prop6 Trp(2)f_prop11 by (simp add: gpos_generalpos v2lp)
    have v2l_ssgp:"sdistinct(sorted_list_of_set (set V2L))" using v2l_ss
      by (simp add: distinct_map)
    have  "(\<forall>xs. (set xs \<subseteq> set V2L) \<longrightarrow> \<not>(cap 3 xs \<or> cup (Suc k) xs))"
    proof-
      {
        fix xs
        assume xsp:"set xs \<subseteq> set V2L"
        hence "length xs > k \<Longrightarrow> \<not>sdistinct xs" using v2l_k
          by (metis List.finite_set card_mono distinct_card distinct_map linorder_not_less v2l_ss)
        hence 1:"\<not> cup (Suc k) xs" using cup_def by force
        have "\<not> cap 3 xs"
        proof(cases "length xs = 3 \<and> sdistinct xs")
          case True
          hence "length xs = 3" by simp
          then obtain a b c where xs3: "xs = [a,b,c]" using xsp
            by (smt (verit, best) List.finite_set True distinct.simps(2) distinct_map length_0_conv length_Cons
                nat.inject nat.simps(3) numeral_3_eq_3 set_empty sorted_list_of_set.idem_if_sorted_distinct
                sorted_list_of_set.sorted_sorted_key_list_of_set sorted_list_of_set_nonempty)
          then obtain u v w where uvw: "a = v2 u" "b = v2 v" "c = v2 w" using xsp v2lp by auto
          hence "sdistinct[v2 u, v2 v, v2 w]" using xsp xs3 True by simp
          hence "cup3 a b c" using f_prop4 uvw f_prop10 by presburger
          thus "\<not>(cap 3 xs)" using True exactly_one_true cap_def xs3 by (metis list_check.simps(4))
          text\<open>When the length xs \<noteq> 3 then xs can not be a 3-cap from definition trivially.\<close>
        qed(auto simp add: cap_def) 
        hence "set xs \<subseteq> set V2L \<and> sdistinct xs \<longrightarrow> \<not> (cap 3 xs \<or> cup (Suc k) xs)" using 1
          by blast
      }
      thus ?thesis
        by (simp add: cap_def cup_def)
    qed
    hence "(\<forall>xs. (set xs \<subseteq> set V2L) \<longrightarrow> \<not>(cap 3 xs \<or> cup (Suc k) xs))" by simp
    thus ?thesis using v2l_gp Trp(1) v2l_ss v2l_k
      by (metis distinct_card distinct_map dual_order.refl v2l_ssgp)
    qed
  thus ?thesis using min_conv_lower by simp
qed

theorem min_conv_base:
  "min_conv 3 k = k"
proof(induction k)
  case 0
  have "cap 0 []" by (simp add: cap_def) 
  thus ?case unfolding min_conv_def using lcheck_len2_T 
    by (smt (verit, ccfv_SIG) cup_def distinct.simps(1) empty_subsetI inf_upper le_zero_eq list.simps(8) list.size(3) list_check.simps(1) mem_Collect_eq set_empty2
        sorted_wrt.simps(1))
next
  case (Suc k)
  hence "min_conv 3 (Suc k) \<le> Suc k" 
    using min_conv_def[of "3" "Suc k"] inf_upper abc by auto
  moreover have "min_conv 3 (Suc k) \<ge> Suc k"  using Suc_leI min_conv_3_k_bnd
    by presburger
  ultimately show ?case by simp
qed


end