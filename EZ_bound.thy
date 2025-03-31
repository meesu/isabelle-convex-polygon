theory EZ_bound
imports Four_Convex Definitions
begin

(*** start of Theorem 2.2 Andrew Suk ***)

thm strict_sorted_iff

thm finite_sorted_distinct_unique

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

lemma  card_of_s:
  assumes "set xs \<subseteq> S" "cap k xs" "distinct xs" "finite S"
  shows "card S \<ge> k"
  using assms(4,1,2,3) 
  by (metis cap_def card_mono distinct_card)

theorem non_empty_cup_cap:
  fixes k l
  shows "{} \<noteq> {(n::nat). 
                (\<forall>S . card S \<ge> n \<and> general_pos S \<longrightarrow> 
                  (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs)))}"
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

(* To show in a lemma if j < k, and the set of points created by a k-cap does not contain
a 3-cup*)
(*

lemma assumes "finite S" "gen_pos S"
  shows "\<exists> xs. set xs = S \<and> length xs = card S \<and> cap (card k *)


lemma extract_cap_cup:
    assumes "min_conv k l = n"
        and "card S = n" "general_pos S"
      shows "\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap k xs \<or> cup l xs)"
  using assms non_empty_cup_cap min_conv_def
  by (smt (verit, del_insts) Inf_nat_def1 mem_Collect_eq verit_comp_simplify1(2))

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

(* lemma noname *)
lemma 
  assumes "cup k (y#z#ws)" and "x < y"
      and "\<not> cup (Suc k) (x#y#z#ws)"
    shows "(cross3 x y z) \<le> 0"
  using assms unfolding cup_def list_check.simps cup3_def
proof-
  have "sortedStrict (x#y#z#ws)" using assms(1,2) unfolding cup_def by fastforce
  moreover have "length (x#y#z#ws) = Suc k" 
    using assms(1) cup_def by force
  ultimately have 1:"\<not>list_check cup3 (x#y#z#ws)" using assms(3) unfolding cup_def
    by presburger
  then show ?thesis unfolding list_check.simps(4) unfolding cup3_def
    using assms(1) unfolding cup_def cup3_def  by argo
qed

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

lemma get_cup_from_bad_cap:
  assumes "sortedStrict P" and "\<not> cap (length P) P"
  shows "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cap3 a b c"
proof-
  from assms have "\<not> list_check cap3 P" using cap_def by simp
  then show ?thesis using assms
  proof(induction P)
    case Nil
    then show ?case using cap_def by auto
  next
    case (Cons a P)
    then show ?case
    proof(cases "length P \<le> 2")
      case True
      hence "cap (length P) P"  
        using list_check.simps assms(1) Cons.IH Cons.prems(2,3) cap_def sublist_length_le by force
      then show ?thesis using Cons
      proof(cases "length P = 2")
        case True
        then obtain x y where "P = [x,y]"
          by (metis (no_types, lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
       
        then show ?thesis
          by (metis Cons.prems(1) \<open>cap (length P) P\<close> cap_def list_check.simps(4)
              sublist_order.order_refl)  
      next
        case False
        hence "length P < 2"
          using True nat_less_le by blast
        then have False using Suc_length_conv strict_sorted_iff list.inject list_check.elims(1) Cons(2,3)
          by (smt (verit, best) distinct_length_2_or_more length_0_conv less_2_cases_iff neq_Nil_conv)
        then show ?thesis by argo
      qed
    next
      case False
      hence "\<exists>u v rest. P = (u#v#rest)"
        by (metis One_nat_def Suc_1 bot_nat_0.extremum le_add1 length_Cons list.exhaust list.size(3)
            plus_1_eq_Suc)
      then obtain u v rest where uvrest: "P = (u#v#rest)" by blast
      hence "\<not> cap3 a u v \<or> \<not> list_check cap3 P"
        using Cons.prems(1) by auto
      then show ?thesis
      proof
        assume "\<not> cap3 a u v"
        thus "\<exists>aa b c. sublist [aa, b, c] (a # P) \<and> \<not> cap3 aa b c" using uvrest
          by (metis append_Cons append_Nil sublist_append_rightI)
      next
        assume "\<not> list_check cap3 P"
        thus "\<exists>aa b c. sublist [aa, b, c] (a # P) \<and> \<not> cap3 aa b c" using uvrest Cons.prems(2,3)
          by (metis Cons_eq_appendI cap_def strict_sorted_iff distinct_length_2_or_more 
              sorted2 sublist_def Cons.IH)
      qed
    qed
  qed
qed

lemma get_cap_from_bad_cup:
  assumes "sortedStrict P" and "\<not> cup (length P) P"
  shows "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cup3 a b c"
proof-
  from assms have "\<not> list_check cup3 P" using cup_def by simp
  then show ?thesis using assms
  proof(induction P)
    case Nil
    then show ?case using cup_def by auto
  next
    case (Cons a P)
    then show ?case
    proof(cases "length P \<le> 2")
      case True
      hence 1: "cup (length P) P"  
        using list_check.simps assms(1) Cons.IH Cons.prems(2,3) cup_def sublist_length_le by force
      then show ?thesis using Cons
      proof(cases "length P = 2")
        case True
        then obtain x y where "P = [x,y]"
          by (metis (no_types, lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
       
        then show ?thesis
          by (metis Cons.prems(1) 1 cup_def list_check.simps(4)
              sublist_order.order_refl)  
      next
        case False
        hence "length P < 2"
          using True nat_less_le by blast
        then have False using Suc_length_conv strict_sorted_iff list.inject list_check.elims(1) Cons(2,3)
          by (smt (verit, best) distinct_length_2_or_more length_0_conv less_2_cases_iff neq_Nil_conv)
        then show ?thesis by argo
      qed
    next
      case False
      hence "\<exists>u v rest. P = (u#v#rest)"
        by (metis One_nat_def Suc_1 bot_nat_0.extremum le_add1 length_Cons list.exhaust list.size(3)
            plus_1_eq_Suc)
      then obtain u v rest where uvrest: "P = (u#v#rest)" by blast
      hence "\<not> cup3 a u v \<or> \<not> list_check cup3 P"
        using Cons.prems(1) by auto
      then show ?thesis
      proof
        assume "\<not> cup3 a u v"
        thus "\<exists>aa b c. sublist [aa, b, c] (a # P) \<and> \<not> cup3 aa b c" using uvrest
          by (metis append_Cons append_Nil sublist_append_rightI)
      next
        assume "\<not> list_check cup3 P"
        thus "\<exists>aa b c. sublist [aa, b, c] (a # P) \<and> \<not> cup3 aa b c" using uvrest Cons.prems(2,3)
          by (metis Cons_eq_appendI cup_def strict_sorted_iff distinct_length_2_or_more 
              sorted2 sublist_def Cons.IH)
      qed
    qed
  qed
qed

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
lemma gpos_equiv_def:
  "gpos S \<longleftrightarrow> general_pos S" 
proof
  show "gpos S \<Longrightarrow> general_pos S" 
    unfolding gpos_def general_pos_def using coll_is_affDep distinct_is_triple nsubset_def
    by (smt (verit, ccfv_threshold) card_3_iff mem_Collect_eq)
next
  show "general_pos S \<Longrightarrow> gpos S"
    unfolding gpos_def general_pos_def using coll_is_affDep distinct_is_triple by metis
qed

lemma real_set_ex: "\<exists>(S:: real set). card S = (n::nat)"
  using infinite_UNIV_char_0 infinite_arbitrarily_large by blast

definition f :: "real \<Rightarrow> R2" where "f \<equiv> \<lambda>a. (a, a * a)"
lemma f_prop1: "\<forall>x y. x \<noteq> y \<longleftrightarrow> f x \<noteq> f y"                  using f_def fst_conv by metis
lemma f_prop2: "distinct[a,b,c] \<longrightarrow> distinct[f a, f b, f c]" using f_prop1 by auto

lemma f_prop3: 
  assumes "distinct [a,b,c]"
  shows   "\<not> collinear3 (f a) (f b) (f c)"
proof
  have 1:"distinct [f a, f b, f c]" using assms f_prop2 by auto
  assume 2:"collinear3 (f a) (f b) (f c)"
  hence "(b-a) * (c*c - b*b) - (c-b) * (b*b - a*a) = 0"  
    unfolding collinear3_def cross3_def f_def by simp
  hence "(b - a) * (c - a) * (b - c) = 0" by argo
  thus False using assms 1 2 by simp
qed

thm card_le_inj

lemma genpos_ex:
  "\<exists>S. gpos S \<and> card S = n"
proof-
  obtain X  where rset: "card (X :: real set) = n" using real_set_ex by blast
  hence 1:"card (f ` X) = n"  by (metis card_image f_prop1 inj_onI)
  have "gpos (f ` X)" using f_prop3 gpos_def
    by (smt (verit, best) distinct_length_2_or_more distinct_singleton image_iff)
  thus ?thesis using 1 by blast
qed

theorem "min_conv 3 k = k"
  unfolding min_conv_def
proof(induction k)
  case 0
  have "cap 0 []" by (simp add: cap_def) 
  thus ?case using 0 cup_def
    by (smt (verit, ccfv_threshold) empty_subsetI le_zero_eq list.size(3) list_check.simps(1)
        mem_Collect_eq sorted_wrt.simps(1) wellorder_Inf_le1 empty_set)
next
  case (Suc k)
  obtain S where S_asm:"card S = Suc k" and S_gp:"general_pos S" using genpos_ex gpos_equiv_def by blast
  then obtain x xs where x_xs:"S = set (x#xs)" "sortedStrict (x#xs)" "length (x#xs) = card S" 
    using extract_cap_cup S_asm list.exhaust list.size(3) nat.simps(3)
    by (metis card.infinite sorted_list_of_set.sorted_key_list_of_set_unique)
  have x_Min:"x = Min S" using x_xs(1,2)
    by (metis List.finite_set list.discI list.inject set_empty2
        sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set_nonempty strict_sorted_iff)
  have "length xs = k" using S_asm x_xs by auto
  moreover have sminus_x:"card (S - {x}) = k" using S_asm by (simp add: card.insert_remove x_xs(1))
  moreover have gp_sminus_x:"general_pos (S - {x})" using x_xs(1) S_gp general_pos_subs by blast
  text \<open>Using induction hypothesis obtain the cup or cap of size k from the set S - {min(S)}.\<close>
  ultimately obtain zs
    where zs:"set zs \<subseteq> S - {x}" "sortedStrict zs" "(cap 3 zs \<or> cup k zs)"
    using extract_cap_cup[of "3" "k" "k" "S - {x}"] Suc min_conv_def strict_sorted_iff by auto
(*
To Prove
Inf {n. \<forall>S. n \<le> card S \<and> general_pos S \<longrightarrow> 
    (\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap 3 xs \<or> cup (Suc k) xs))} = Suc k
*)
  have "\<exists>cc. set cc \<subseteq> S \<and> sortedStrict cc \<and> (cap 3 cc \<or> cup (Suc k) cc)"
  proof(cases "cap 3 zs")
    case True
    then show ?thesis using zs(1,2) by auto
  next
    case False
    hence F1:"cup k zs" using zs by simp
    hence F2:"length zs = k" unfolding cup_def by argo
    hence F0:"length (x#zs) = Suc k" using x_Min by auto
    have  F4:"set (x#zs) \<subseteq> S" using x_xs(1) zs(1) by auto
    have  F3:"sortedStrict (x#zs)" using zs(1,2) x_Min x_xs(1,2) by fastforce
    then show ?thesis
    proof(cases "cup (Suc k) (x#zs)")
      case True
      then show ?thesis using F3 x_xs(1) zs(1)
        by (metis Diff_empty insert_subset list.set_intros(1) list.simps(15) subset_Diff_insert)
    next
      case False
      hence "\<exists>a b c. (sublist [a,b,c] (x#zs)) \<and> \<not> cup3 a b c"
        using F0 F3 get_cap_from_bad_cup by presburger
      then obtain b1 b2 b3 where bcup:"sublist [b1,b2,b3] (x#zs)" "\<not> cup3 b1 b2 b3" by blast
      have fb1:"b1 \<in> S \<and> b2 \<in> S \<and> b3 \<in> S" 
        by (meson F4 bcup list.set_intros(1,2) set_mono_sublist subset_code(1))
      have fb2:"sortedStrict [b1, b2, b3]" using bcup F3 sublist_def sorted_wrt_append by metis
      have fb3:"cross3 b1 b3 b2 \<noteq> 0" using S_gp fb1 cross3_commutation_23 fb2 genpos_cross0 
          strict_sorted_iff by blast
      have fb4:"length [b1, b2, b3] = 3" using fb2 by simp
      have     "cap3 b1 b2 b3" using fb3 bcup(2) cap3_def cup3_def not_less_iff_gr_or_eq
        by (metis cross3_commutation_23)
      hence "cap 3 [b1, b2, b3]" unfolding cap_def using fb2 fb4 by auto 
      thus ?thesis by (meson F4 bcup(1) dual_order.trans fb2 set_mono_sublist)
    qed
  qed
  hence "Suc k = card S \<and> general_pos S \<longrightarrow> 
        (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap 3 xs \<or> cup (Suc k) xs))" by blast
  have "min_conv 3 (Suc k) > k \<Longrightarrow> (\<exists>S. k = card S \<and> general_pos S \<longrightarrow> 
        \<not> (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap 3 xs \<or> cup (Suc k) xs)))" sorry
  then show ?case sorry
qed

end