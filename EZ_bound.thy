theory EZ_bound
imports Four_Convex
begin


(*** start of Theorem 2.2 Andrew Suk ***)

definition nsubset::"'a set \<Rightarrow> nat \<Rightarrow> ('a set) set" (infix "~" 76)
  where
"nsubset S k = {X. X \<subseteq> S \<and>  card X = k}"


(*** defs gen-position, k-cup, l-cup ***)
definition general_pos::"((real\<times>real) set) \<Rightarrow> bool" where
"general_pos S \<equiv>  (\<forall> P3 \<in> S~3. \<not> affine_dependent P3)"

(*to be deleted - begin*)
definition lex_eq :: "(real\<times>real) \<Rightarrow> (real\<times>real) \<Rightarrow> bool" where
"lex_eq p1 p2 \<equiv> fst p1 \<le> fst p2"

definition lex :: "(real\<times>real) \<Rightarrow> (real\<times>real) \<Rightarrow> bool" where
"lex p1 p2 \<equiv> fst p1 < fst p2"
(*to be deleted - end*)

type_synonym R2 = "real \<times> real"

definition cross3 :: "R2 \<Rightarrow> R2 \<Rightarrow> R2 \<Rightarrow> real" where
"cross3 a b c \<equiv> (fst b - fst a) * (snd c - snd a) - (fst c - fst a) * (snd b - snd a)"

definition cup3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"cup3 a b c \<equiv>  cross3 a c b < 0"

definition cap3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"cap3 a b c \<equiv>  cross3 a c b > 0"

definition collinear3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"collinear3 a b c \<equiv> cross3 a b c = 0"

(* observation: \<not> collinear3 a b c = general_pos_2D {a,b,c} *)

fun list_check :: "(_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> _ list \<Rightarrow> bool" where
  "list_check f [] = True"
| "list_check f (a#[]) = True"
| "list_check f (a#b#[]) = (a \<noteq> b)"
| "list_check f (a#b#c#rest) = (f a b c \<and> list_check f (b#c#rest))"

definition cap::"nat \<Rightarrow> (real\<times>real) list \<Rightarrow> bool" where
"cap k L \<equiv> (k = length L) \<and> (sorted L) \<and> (list_check cap3 L)"

definition cup :: "nat \<Rightarrow> (real \<times> real) list \<Rightarrow> bool" where
"cup k L \<equiv> (k = length L) \<and> (sorted L) \<and> (list_check cup3 L)"

(* definition of minimum number of points containing an l-cup or k-cap *)
(* distinctness is taken care of by the fact that cap or cup needs to have distinct points*)
(*distinctness *)
definition min_conv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"min_conv k l = (Inf {n . (\<forall>S . card S \<ge> n \<and> general_pos S 
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))})"

lemma cross3_commutation_12: "cross3 x y z = 0 \<longrightarrow> cross3 y x z = 0"
  unfolding cross3_def by argo

lemma cross3_commutation_23: "cross3 x y z = 0 \<longrightarrow> cross3 x z y = 0"
  unfolding cross3_def by argo

lemma cap_reduct:
  assumes "cap (k+1) (a#xs)"
  shows "cap k xs"
  using assms unfolding cap_def 

  using add_left_cancel length_Cons list.distinct(1) list.inject list_check.elims(2) by fastforce

lemma  card_of_s:
  assumes "set xs \<subseteq> S" "cap k xs" "distinct xs" "finite S"
  shows "card S \<ge> k"
  using assms(4,1,2,3) 
  by (metis cap_def card_mono distinct_card)

theorem non_empty_cup_cap:
  fixes k l
  shows "{(n::nat) . (\<forall>S . card S \<ge> n \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))} \<noteq> {}"
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

lemma fixes S
  assumes "finite S"
  shows "\<exists>xs.  length xs = card S \<and> set xs = S \<and> sorted xs"
  by (metis assms finite_sorted_distinct_unique sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set.sorted_key_list_of_set_unique)
lemma fixes S
  assumes "finite S"
  shows "\<exists>xs.  length xs = card S \<and> set xs = S \<and> sorted xs"
  by (metis assms finite_sorted_distinct_unique sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set.sorted_key_list_of_set_unique)

(* To show in a lemma if j < k, and the set of points created by a k-cap does not contain
a 3-cup*)
(*

lemma assumes "finite S" "gen_pos S"
  shows "\<exists> xs. set xs = S \<and> length xs = card S \<and> cap (card k *)


lemma extract_cap_cup:
    assumes "min_conv k l = n"
      and "card S = n" "general_pos S"
    shows "\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap k xs \<or> cup l xs)" using min_conv_def assms
proof-
  have s_1:"card S \<ge> n \<and> general_pos S" using assms by simp
  hence "card S \<in> {m.  (\<forall>S . card S \<ge> m \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))}"
    using assms(1) unfolding min_conv_def 
  proof -
    assume a1: "Inf {n. \<forall>S. n \<le> card S \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs))} = n"
    have "{} \<noteq> {n. \<forall>r. n \<le> card r \<and> general_pos r \<longrightarrow> (\<exists>ps. set ps \<subseteq> r \<and> sorted ps \<and> (cap k ps \<or> cup l ps))}"
      using non_empty_cup_cap by blast
    then show ?thesis
      using a1 by (smt (z3) Inf_nat_def1 assms(2))
  qed
  hence "(\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap k xs \<or> cup l xs))"
    using assms(1) s_1 unfolding min_conv_def by simp
  thus ?thesis by argo
qed

lemma general_pos_subs: assumes "X \<subseteq> Y" and "general_pos Y"
  shows "general_pos X" 
proof(rule ccontr)
  assume "\<not>general_pos X"
  then obtain S where S:"S \<in> X~ 3" "affine_dependent S" unfolding general_pos_def by blast
  have "S \<in> Y~3" using assms(1) unfolding nsubset_def 
    by (smt (verit) S mem_Collect_eq nsubset_def order_trans)  
  thus False using S(2) assms(2) unfolding general_pos_def by simp 
qed

lemma assumes "cup k (y#z#ws)" and "x \<le> y"
          and "\<not> cup (Suc k) (x#y#z#ws)"
        shows "(cross3 x z y) \<ge> 0"
  using assms unfolding cup_def list_check.simps cup3_def 
proof-
  have "sorted (x#y#z#ws)" using assms(1,2) unfolding cup_def by fastforce
  moreover have "length (x#y#z#ws) = Suc k" 
    using assms(1) cup_def by force
  ultimately have 1:"\<not>list_check cup3 (x#y#z#ws)" using assms(3) unfolding cup_def
    by presburger
  then show ?thesis unfolding list_check.simps(4) unfolding cup3_def
    using assms(1) unfolding cup_def cup3_def by argo
qed

lemma affine_comb_affine_dep:
  assumes "(u :: real) \<ge> 0" and "x = (1 - u) *\<^sub>R y + u *\<^sub>R (z :: R2)" and "distinct [x, y, z]"
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
  thus ?thesis unfolding cross3_def using 1 2 3 by simp
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
  assumes "(y1 - x1) * (z2 - x2) - (z1 - x1) * (y2 - x2) = 0" 
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
  thus ?thesis using cross_affine_dependent_aux1 cross3_def assms(1,2) surjective_pairing by metis
next
  case False
  then show ?thesis
  proof(cases "snd y = snd x")
    case True
    then show ?thesis 
      using cross_affine_dependent_aux1[of "snd y" "snd x" "fst z" "fst x" "snd z" "fst y"] assms(1,2)
        cross3_def surjective_pairing cross_affine_dep_aux3[of "(prod.swap ` {x, y, z})"] prod.swap_def
      by (smt (verit) distinct_length_2_or_more distinct_singleton fst_conv image_empty image_insert mult_eq_0_iff snd_conv)
  next
    case False
    assume a1: "fst y \<noteq> fst x"
    define "u" where u_def: "u = (fst z - fst x) / (fst y - fst x)"
    then have z1: "fst z = fst x - u * fst x + u * fst y" using "False" a1
      by (simp add: nonzero_eq_divide_eq right_diff_distrib)
    have "u = (snd z - snd x) / (snd y - snd x)" using u_def assms a1
      by (simp add: False cross3_def frac_eq_eq mult.commute)
    then have "snd z = snd x - u * snd x + u * snd y" using "False" a1
      by (simp add: nonzero_eq_divide_eq right_diff_distrib)
    then have "z = (1 - u) *\<^sub>R x + u *\<^sub>R y" using assms a1 False z1
      by (metis (mono_tags, lifting) add.commute add_left_cancel diff_add_cancel fst_diff
          fst_scaleR pair_scal real_scaleR_def scaleR_left.diff scaleR_one snd_diff snd_scaleR)
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
  using affinedep_cases assms cross3_commutation_12 cross3_commutation_23 in_hull3_iscollinear 
  by blast

lemma genpos_cross0:
  assumes "general_pos S" and "x \<in> S" and "y \<in> S" and "z \<in> S" and "distinct [x, y, z]"
  shows "cross3 x y z \<noteq> 0"
  using assms nsubset_def general_pos_def cross_affine_dependent
  by (smt (verit, del_insts) add.right_neutral add_Suc_right distinct_card empty_set 
      empty_subsetI insert_subset list.simps(15) list.size(3,4) mem_Collect_eq numeral_3_eq_3)
(*
definition min_conv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"min_conv k l = (Inf {n . (\<forall>S . card S \<ge> n \<and> general_pos S 
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))})"
*)

(*
min_conv 3 k = 
Inf {n. \<forall>S. n \<le> card S \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap 3 xs \<or> cup k xs))}
*)

lemma cross3_non0_distinct: "cross3 a b c \<noteq> 0 \<longrightarrow> distinct [a,b,c]" unfolding cross3_def by auto

lemma cup_cap_cross_non0:
  assumes "cup k A \<or> cap l A"
  shows   "\<forall>i j k. distinct [i,j,k] \<longrightarrow> cross3 (A!i) (A!j) (A!k) \<noteq> 0"
(*bounds for i j k ? *)
  sorry

lemma cup_cap_distinct:
  assumes "cup k A \<or> cap l A"
  shows   "distinct A" using assms cup_cap_cross_non0 cross3_non0_distinct sorry

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
  fix S::"(real \<times> real) set"
  assume S_asm:"card S = Suc k"
  assume S_gp:"general_pos S"
  then obtain x xs where x_xs:"S = set (x#xs)" "sorted (x#xs)" "length (x#xs) = card S" 
    by (metis (no_types, opaque_lifting) S_asm sorted_list_of_set.sorted_sorted_key_list_of_set
        sorted_list_of_set.sorted_key_list_of_set_unique card.infinite length_Suc_conv nat.simps(3))
  have x_Min:"x = Min S" using x_xs using x_xs(2) by (simp add: Min_insert2)
  have "length xs = k" using S_asm x_xs by auto
  moreover have sminus_x:"card (S - {x}) = k" using S_asm by (simp add: card.insert_remove x_xs(1))
  moreover have gp_sminus_x:"general_pos (S - {x})" using x_xs(1) S_gp general_pos_subs by blast
  text \<open>Using induction hypothesis obtain the cup or cap of size k from the set S - {min(S)}.\<close>
  ultimately obtain zs where  zs:"set zs \<subseteq> S - {x}" "(cap 3 zs \<or> cup k zs)" "sorted zs"
    using extract_cap_cup[of "3" "k" "k" "S - {x}"] Suc min_conv_def by auto
  hence d_zs: "distinct zs" using cup_cap_distinct by auto
(*
To Prove
Inf {n. \<forall>S. n \<le> card S \<and> general_pos S \<longrightarrow> 
    (\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap 3 xs \<or> cup (Suc k) xs))} = Suc k
*)
  have "\<exists>cc. set cc \<subseteq> S \<and> sorted cc \<and> (cap 3 cc \<or> cup (Suc k) cc)"
  proof(cases "cap 3 zs")
    case True
    then show ?thesis using zs(1,3) by auto
  next
    case False
    hence F1:"cup k zs" using zs(2) by simp
    hence F2:"length zs = k" unfolding cup_def by argo
    have  F3:"sorted (x#zs)" using zs(1,3) x_Min x_xs(1,2) by fastforce
    then show ?thesis
    proof(cases "cup (Suc k) (x#zs)")
      case True
      then show ?thesis using F3 x_xs(1) zs(1)
        by (metis Diff_empty insert_subset list.set_intros(1) list.simps(15) subset_Diff_insert)
    next
      case False
(* TODO - cant derive distinctness, clash of --set,list and distinctness--
  1. better definitions only in terms of lists or
  2. derive distinctness using current definitions
  --- lists allow repeated points -- which is more realistic?
*)
      hence "\<exists>b1 b2 b3. \<not> cup3 b1 b2 b3 \<and> sorted [b1,b2,b3] \<and> {b1, b2, b3} \<subseteq> set (x#zs) \<and> distinct[b1,b2,b3]"
        using cup3_def zs d_zs sorry
      then obtain b1 b2 b3 where b_cup:"\<not> cup3 b1 b2 b3" "sorted [b1,b2,b3]" "{b1, b2, b3} \<subseteq> set (x#zs)"
        by blast
      have fb1:"b1 \<in> S \<and> b2 \<in> S \<and> b3 \<in> S" using b_cup(3) x_xs(1) zs(1) by auto
      have fb2:"distinct [b1, b2, b3]" using cross3_non0_distinct fb1 genpos_cross0 S_gp zs
      have fb3:"cross3 b1 b3 b2 \<noteq> 0" using S_gp
        using cross3_commutation_23 genpos_cross0 fb2 fb1 by blast
      hence "cap 3 [b1, b2, b3]" using cap_def b_cup fb2 unfolding cup3_def cap3_def by auto 
      then show ?thesis using b_cup(2) fb1 by force
    qed
  qed
  thus ?case sorry
qed

end
(* steps above: 
1, Show that every k-1 cap does not contain a 3-cup
2, Use that to show that if its a j-cap, where j<k, it does not contain a 3-cup
3. also show that the cap in question needs to have at least k element set. 
4. Thus value of S needs to be at least k*)

(*

  then have "cap 3 zs \<or> cup (Suc k) (x#zs)"
  proof(cases "cap 3 zs")
    case False
    hence F1:"cup k zs" using zs(2) by simp
    hence F2:"length zs = k" unfolding cup_def by argo
    have  F3:"sorted (x#zs)" using zs(1,3) x_Min x_xs(1,2) by fastforce
    then show ?thesis
    proof(cases "cup (Suc k) (x#zs)")
      case False
      then obtain b1 b2 b3 where b_cup:"\<not> cup3 b1 b2 b3" "sorted [b1,b2,b3]"
        by (metis add.right_neutral add_diff_cancel_left' cross3_def cup3_def order.refl 
            order_less_irrefl sorted2_simps(2) sorted_wrt2_simps(1))
      have fb1:"b1 \<in> S" "b2 \<in> S" "b3 \<in> S" sorry
      have fb2:"distinct [b1, b2, b3]" sorry
      have fb3:"cross3 b1 b3 b2 \<noteq> 0" using S_gp
        using cross3_commutation_23 genpos_cross0 fb2 fb1 by blast
      hence "cap 3 [b1, b2, b3]" using cap_def b_cup fb2 unfolding cup3_def cap3_def by auto 
      then show ?thesis sorry
    qed (argo)
  qed (argo)
  thus ?case sorry


  obtain n where "n =min_conv 3 k"
    unfolding min_conv_def using non_empty_cup_cap 
    by blast
   {fix S
    assume asm:"card S = k \<and> general_pos S"
    have "\<exists>xs. set xs \<subseteq> S \<and> (cap k xs \<or> cup 3 xs)"
    proof-
      have "\<exists> xs. length xs = k \<and> set xs = S \<and>  sorted_wrt (\<le>) xs"
        using asm unfolding le_x_def sorry
      show ?thesis  sorry
    qed   }
  show ?thesis sorry
qed
*)

(*** Theorem 2.2: Let f(k, ℓ) be the smallest integer N such that any N-element planar point
set in the plane in general position contains a k-cup or an ℓ-cap. Then f(k, l) = 1 + choose(k+l-4, k-2).
***)



(* relevant equivalent lemma for above is convex_hull_finite*)
(*from above, we can write another lemma to extract*)

(* try to instantiate R^2 in this*)
