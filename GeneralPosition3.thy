theory GeneralPosition3
  imports Definitions Prelims

begin
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

(*work with a simpler definition of general position in 2 dimensions.*)
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

end