theory SomeLemmas
imports MinConv

begin

(*
lemma cross3_mid_below:
  (*The lemma tells you that the if a b c form a cup, then b lies below the
  line joining a and c.  More precisely, if p is the point on ac such that
  fst p = fst b, then snd p \<ge> snd b*)
  assumes "cup3 a b c"
  shows "(fst c - fst a) * snd b 
              \<le> (snd c - snd a) * (fst b - fst c) + snd c * (fst c - fst a)"
  using assms unfolding cup3_def cross3_def
  by argo
*)

lemma cup_abc_cup_bcd_implies_cup_acd:
  assumes "cup3 a b c"
  and     "cup3 b c d"
  and     "sdistinct [a,b,c,d]"
shows   "cup3 a c d"
  using assms unfolding cup3_def
  by (smt (verit) cup3_def cup3_slope distinct_length_2_or_more list.simps(9)
      order.trans slope_cup3 slope_trans(2) sorted2 sorted_wrt1)

lemma cup4Impliescup3Last:
  assumes  "cup 4 [a,b,c,d]"
  shows "cup3 a c d"
proof-
  have cup_abc: "cup3 a b c" using assms unfolding cup_def by simp
  have cup_bcd: "cup3 b c d" using assms unfolding cup_def by simp
  show ?thesis using cup_abc_cup_bcd_implies_cup_acd cup_abc cup_bcd 
    unfolding cup3_def cross3_def 
    using assms cup_def by blast
qed

(*
lemma cup4_last_above:
  (*The lemma tells you that the if a b c d form a cup, then d lies above the
  line joining a and c.  More precisely, if p is the point on ac such that
  fst p = fst d, then snd p \<le> snd d*)
  assumes "cup 4 [a,b,c,d]"
  shows "(fst c - fst a)* snd d 
          \<ge> (snd c - snd a) * (fst d - fst c) + snd c * (fst c - fst a)"
proof-
  have cup_acd: "cup3 a c d" using assms cup4Impliescup3Last by simp
  show ?thesis using assms cup_acd unfolding cup3_def cross3_def by argo
qed
*)

definition halfspace_pos :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real \<times> real) set" where
"halfspace_pos p q \<equiv> 
   let (x1, y1) = p;
       (x2, y2) = q;
       dpq = sqrt((x2-x1)^2 + (y2-y1)^2);
       v = ((y1 - y2)/dpq, (x2 - x1)/dpq);
       D = (x2*y1 - x1*y2)/dpq
   in {s. inner v s \<ge> D}"

definition halfspace_neg :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real \<times> real) set" where
"halfspace_neg p q \<equiv> 
   let (x1, y1) = p;
       (x2, y2) = q;
       dpq = sqrt((x2-x1)^2 + (y2-y1)^2);
       v = ((y1 - y2)/dpq, (x2 - x1)/dpq);
       D = (x2*y1 - x1*y2)/dpq
   in {s. inner v s \<le> D}"


lemma a_c_belongs_halfspace_a_c: 
  assumes "a \<noteq> c"
  shows "a \<in> halfspace_pos a c"
  and "c \<in> halfspace_pos a c"
proof-
  define x1 where "x1 \<equiv> fst a"
  define y1 where "y1 \<equiv> snd a"
  define x2 where "x2 \<equiv> fst c"
  define y2 where "y2 \<equiv> snd c"
  define dpq where "dpq \<equiv> sqrt ((x2 - x1)^2 + (y2 - y1)^2)"
  define v where "v \<equiv> ((y1 - y2) / dpq, (x2 - x1) / dpq)"
  define D where "D \<equiv> (x2 * y1 - x1 * y2)/ dpq"
  hence dpqNE0: "dpq > 0" unfolding dpq_def x1_def x2_def y2_def y1_def 
    using assms
    by (metis add_less_same_cancel1 add_less_same_cancel2 eq_iff_diff_eq_0
        linorder_neqE_linordered_idom not_sum_power2_lt_zero power2_less_0 prod.exhaust_sel
        real_sqrt_eq_zero_cancel_iff real_sqrt_lt_0_iff zero_less_power2)

  have s_1: "fst v = (snd a - snd c) / dpq" using v_def y1_def x1_def x2_def y2_def by simp
  have s_2: "snd v = (fst c - fst a) / dpq" using v_def y1_def x1_def x2_def y2_def by simp 
  have s_3: "v \<bullet> a = D" using s_1 s_2 unfolding inner_prod_def D_def x1_def x2_def y1_def y2_def
    by (smt (verit, del_insts) diff_diff_eq2 diff_divide_distrib diff_eq_diff_eq distrib_left
        divide_divide_eq_right group_cancel.sub1 inner_commute inner_real_def times_divide_eq_left
        times_divide_eq_right x1_def y2_def)
  have s_4: "v \<bullet> c = D" using s_1 s_2  unfolding inner_prod_def D_def x1_def x2_def y1_def y2_def
    by (smt (verit, ccfv_SIG) add.assoc add.commute add_diff_cancel_left' add_diff_eq
        cancel_comm_monoid_add_class.diff_cancel diff_diff_eq diff_diff_eq2 diff_divide_distrib
        diff_eq_eq diff_zero distrib_right divide_divide_eq_left divide_divide_eq_right fst_swap
        inner_commute inner_real_def minus_diff_eq mult_minus_left mult_minus_right power2_eq_square
        real_divide_square_eq ring_class.ring_distribs(1) times_divide_eq_left times_divide_eq_right
        uminus_add_conv_diff x1_def x2_def y1_def y2_def)
  show  "a \<in> halfspace_pos a c" using s_3 unfolding halfspace_pos_def
    by (smt (verit) D_def dpq_def mem_Collect_eq split_beta v_def x1_def x2_def y1_def y2_def)
  show "c \<in> halfspace_pos a c" using s_4 s_3 unfolding halfspace_pos_def
    by (metis (mono_tags, lifting)  \<open>a \<in> halfspace_pos a c\<close> dpq_def halfspace_pos_def
        mem_Collect_eq split_beta v_def x1_def x2_def y1_def y2_def)
qed

lemma halfspace_pos_convex: "convex (halfspace_pos a c)"
proof -
  let ?x1 = "fst a"
  let ?y1 = "snd a"
  let ?x2 = "fst c"
  let ?y2 = "snd c"
  let ?dpq = "sqrt ((?x2 - ?x1)^2 + (?y2 - ?y1)^2)"
  let ?D = "(?x2 * ?y1 - ?x1 * ?y2) / ?dpq"
  let ?v = "((?y1 - ?y2)/?dpq, (?x2 - ?x1)/?dpq)"
  have "halfspace_pos a c = {x. ?D \<le> inner x ?v}"
    unfolding halfspace_pos_def by (metis (no_types, lifting) Collect_cong inner_commute split_beta)
  then show ?thesis
    by (metis (no_types, lifting) ext convex_halfspace_ge halfspace_pos_def split_beta)
qed

lemma cup4_last_halfspace_pos:
  assumes "cup 4 [a,b,c,d]"
  shows "d \<in> halfspace_pos a c"
proof-
  define x1 where "x1 \<equiv> fst a"
  define y1 where "y1 \<equiv> snd a"
  define x2 where "x2 \<equiv> fst c"
  define y2 where "y2 \<equiv> snd c"
  define dpq where "dpq \<equiv> sqrt ((x2 - x1)^2 + (y2 - y1)^2)"
  define v where "v \<equiv> ((y1 - y2) / dpq, (x2 - x1) / dpq)"
  define D where "D \<equiv> (x2 * y1 - x1 * y2)/ dpq"
  have "distinct [a,b,c,d]" using assms unfolding cup_def by auto
  hence dpqNE0: "dpq > 0" unfolding dpq_def x1_def x2_def y2_def y1_def 
    by (smt (verit) distinct_length_2_or_more prod.exhaust_sel real_less_rsqrt
        sum_power2_gt_zero_iff)
  have cup_acd: "cup3 a c d" using assms cup4Impliescup3Last by simp
  have inner_d1: "d \<bullet> v = (fst d * ((y1 - y2) / dpq)) + (snd d * (x2 - x1) / dpq)"
      by (simp add: inner_prod_def v_def)
  have inner_d2: "d \<bullet> v = (fst d * ((snd a - snd c) / dpq)) + (snd d * (fst c - fst a) / dpq)"
    by (simp add: inner_prod_def v_def x1_def x2_def y1_def y2_def)
  have inner_d3: "d \<bullet> v = (fst d * (snd a - snd c) + snd d * (fst c - fst a)) / dpq"
    by (simp add: add_divide_distrib inner_d2)
  have 1: "fst d * (snd a - snd c) + snd d * (fst c - fst a) > fst c * snd a - snd c * fst a"
      by (smt (verit, ccfv_threshold) cross3_def cup3_def cup_acd left_diff_distrib
          mult.commute mult_diff_mult)
  have 4: "v \<bullet> d \<ge> D" using cup_acd inner_d3 dpqNE0
      unfolding D_def x1_def x2_def y1_def y2_def cup3_def cross3_def
      by (metis "1" divide_strict_right_mono inner_commute mult.commute nless_le)
  show ?thesis using 4 unfolding halfspace_pos_def
      by (metis (mono_tags, lifting) D_def dpq_def mem_Collect_eq split_beta v_def x1_def x2_def y1_def
          y2_def) 
qed

lemma convex_hull_subset_halfspace: 
  assumes "cup 4 [a,b,c,d]"
  assumes "b \<in> convex hull {a,c,d}"
  shows "convex hull {a,b,c,d}\<subseteq> halfspace_pos a c"
proof-
  have s_1:"a \<noteq> c" using assms(1) unfolding cup_def by fastforce
  thus ?thesis using assms(2) a_c_belongs_halfspace_a_c[OF s_1]  cup4_last_halfspace_pos[OF assms(1)]
    by (smt (verit, del_insts) bot_least convex_hull_eq convex_hull_subset halfspace_pos_convex
        hull_subset insert_subset list.set(1,2) subset_antisym)
qed

lemma bNotInhalfspace_pos:
  assumes "cup 4 [a,b,c,d]"
  shows "b \<notin> halfspace_pos a c"
proof-
  define x1 where "x1 \<equiv> fst a"
  define y1 where "y1 \<equiv> snd a"
  define x2 where "x2 \<equiv> fst c"
  define y2 where "y2 \<equiv> snd c"
  define dpq where "dpq \<equiv> sqrt ((x2 - x1)^2 + (y2 - y1)^2)"
  define v where "v \<equiv> ((y1 - y2) / dpq, (x2 - x1) / dpq)"
  define D where "D \<equiv> (x2 * y1 - x1 * y2)/ dpq"

  have cup_abc: "cup3 a b c" using assms unfolding cup_def by auto
  have 1: "fst v = (snd a - snd c) / dpq" using v_def y1_def x1_def x2_def y2_def by simp
  have 2: "snd v = (fst c - fst a) / dpq" using v_def y1_def x1_def x2_def y2_def by simp 
  have "distinct [a,b,c,d]" using assms unfolding cup_def by auto
  hence dpqGT0: "dpq > 0" unfolding dpq_def x1_def x2_def y2_def y1_def 
    by (smt (verit) distinct_length_2_or_more prod.exhaust_sel real_less_rsqrt
        sum_power2_gt_zero_iff)
  have 3: "fst v \<bullet> fst b + snd v \<bullet> snd b = ((snd a - snd c) *  fst b + (fst c - fst a) * snd b)/dpq"
    using 1 2 by (simp add: add_divide_distrib)
  have 4: "(snd a - snd c) *  fst b + (fst c - fst a) * snd b < fst c * snd a - fst a * snd c"
    using cup_abc unfolding cup3_def cross3_def by argo
  have 5: "v \<bullet> b < D" using 1 2 3 4 dpqGT0 
    by (simp add: D_def divide_strict_right_mono inner_prod_def x1_def x2_def y1_def y2_def)
  show ?thesis using 5 
    by (smt (verit) D_def dpq_def halfspace_pos_def mem_Collect_eq split_beta v_def x1_def x2_def
        y1_def y2_def)      
qed

lemma bNotInCHacd:
  assumes "cup 4 [a,b,c,d]"
  shows "b \<notin> convex hull {a,c,d}"
proof(rule ccontr)
  assume " \<not> b \<notin> convex hull {a, c, d}"
  hence "b \<in> convex hull {a, c, d}" by simp
  hence "b \<in> halfspace_pos a c" using convex_hull_subset_halfspace[OF assms] 
    by (simp add: halfspace_pos_convex subset_hull)
  moreover have "b \<notin> halfspace_pos a c" using bNotInhalfspace_pos[OF assms] .
  ultimately show False by blast
qed

(*We will now similarly show that c does not belong to the convex hull {a,b,d} *)

lemma cup_abc_cup_bcd_implies_cup_abd:
  assumes "cup3 a b c"
  and     "cup3 b c d"
  and     "sdistinct [a,b,c,d]"
shows   "cup3 a b d"
  using assms unfolding cup3_def
  by (smt (verit, del_insts) cup3_def cup3_slope distinct_length_2_or_more list.simps(9) order.trans
      slope_cup3 slope_trans(1) sorted2 sorted_wrt1)

lemma cup4Impliescup3abd:
  assumes  "cup 4 [a,b,c,d]"
  shows "cup3 a b d"
proof-
  have cup_abc: "cup3 a b c" using assms unfolding cup_def by simp
  have cup_bcd: "cup3 b c d" using assms unfolding cup_def by simp
  show ?thesis using cup_abc_cup_bcd_implies_cup_abd cup_abc cup_bcd 
    unfolding cup3_def cross3_def 
    using assms cup_def by blast
qed

lemma cup4_first_halfspace_pos:
  assumes "cup 4 [a,b,c,d]"
  shows "a \<in> halfspace_pos b d"
proof-
  define x1 where "x1 \<equiv> fst b"
  define y1 where "y1 \<equiv> snd b"
  define x2 where "x2 \<equiv> fst d"
  define y2 where "y2 \<equiv> snd d"
  define dpq where "dpq \<equiv> sqrt ((x2 - x1)^2 + (y2 - y1)^2)"
  define v where "v \<equiv> ((y1 - y2) / dpq, (x2 - x1) / dpq)"
  define D where "D \<equiv> (x2 * y1 - x1 * y2)/ dpq"
  have "distinct [a,b,c,d]" using assms unfolding cup_def by auto
  hence dpqNE0: "dpq > 0" unfolding dpq_def x1_def x2_def y2_def y1_def 
    by (smt (verit) distinct_length_2_or_more prod.exhaust_sel real_less_rsqrt
        sum_power2_gt_zero_iff)
  have cup_abd: "cup3 a b d" using assms cup4Impliescup3abd by simp
  have inner_d1: "a \<bullet> v = (fst a * ((y1 - y2) / dpq)) + (snd a * (x2 - x1) / dpq)"
      by (simp add: inner_prod_def v_def)
  have inner_d2: "a \<bullet> v = (fst a * ((snd b - snd d) / dpq)) + (snd a * (fst d - fst b) / dpq)"
    by (simp add: inner_prod_def v_def x1_def x2_def y1_def y2_def)
  have inner_d3: "a \<bullet> v = (fst a * (snd b - snd d) + snd a * (fst d - fst b)) / dpq"
    by (simp add: add_divide_distrib inner_d2)
  have 1: "fst a * (snd b - snd d) + snd a * (fst d - fst b) > fst d * snd b - snd d * fst b"
    by (smt (verit, del_insts) cross3_def cup3_def cup_abd left_diff_distrib mult.commute
        right_diff_distrib')
  have 4: "v \<bullet> a \<ge> D" using cup_acd inner_d3 dpqNE0
      unfolding D_def x1_def x2_def y1_def y2_def cup3_def cross3_def
      by (metis "1" divide_right_mono dpqNE0 inner_commute inner_d3 mult.commute nless_le)
  show ?thesis using 4 unfolding halfspace_pos_def
      by (metis (mono_tags, lifting) D_def dpq_def mem_Collect_eq split_beta v_def x1_def x2_def y1_def
          y2_def) 
qed

lemma convex_hull_subset_halfspace2: 
  assumes "cup 4 [a,b,c,d]"
  assumes "c \<in> convex hull {a,b,d}"
  shows "convex hull {a,b,c,d}\<subseteq> halfspace_pos b d"
proof-
  have s_1:"b \<noteq> d" using assms(1) unfolding cup_def by fastforce
  thus ?thesis using assms(2) a_c_belongs_halfspace_a_c[OF s_1]  cup4_last_halfspace_pos[OF assms(1)]
    by (metis SomeLemmas.halfspace_pos_convex assms(1) cup4_first_halfspace_pos hull_redundant
        insert_commute insert_subsetI less_by_empty subset_hull)
qed

lemma cNotInhalfspace_pos_bd:
  assumes "cup 4 [a,b,c,d]"
  shows "c \<notin> halfspace_pos b d"
proof-
  define x1 where "x1 \<equiv> fst b"
  define y1 where "y1 \<equiv> snd b"
  define x2 where "x2 \<equiv> fst d"
  define y2 where "y2 \<equiv> snd d"
  define dpq where "dpq \<equiv> sqrt ((x2 - x1)^2 + (y2 - y1)^2)"
  define v where "v \<equiv> ((y1 - y2) / dpq, (x2 - x1) / dpq)"
  define D where "D \<equiv> (x2 * y1 - x1 * y2)/ dpq"

  have cup_bcd: "cup3 b c d" using assms unfolding cup_def by auto
  have 1: "fst v = (snd b - snd d) / dpq" using v_def y1_def x1_def x2_def y2_def by simp
  have 2: "snd v = (fst d - fst b) / dpq" using v_def y1_def x1_def x2_def y2_def by simp 
  have "distinct [a,b,c,d]" using assms unfolding cup_def by auto
  hence dpqGT0: "dpq > 0" unfolding dpq_def x1_def x2_def y2_def y1_def 
    by (smt (verit) distinct_length_2_or_more prod.exhaust_sel real_less_rsqrt
        sum_power2_gt_zero_iff)
  have 3: "fst v \<bullet> fst c + snd v \<bullet> snd c = ((snd b - snd d) *  fst c + (fst d - fst b) * snd c)/dpq"
    using 1 2 by (simp add: add_divide_distrib)
  have 4: "(snd b - snd d) *  fst c + (fst d - fst b) * snd c < fst d * snd b - fst b * snd d"
    using cup_bcd unfolding cup3_def cross3_def by argo
  have 5: "v \<bullet> c < D" using 1 2 3 4 dpqGT0 
    by (simp add: D_def divide_strict_right_mono inner_prod_def x1_def x2_def y1_def y2_def)
  show ?thesis using 5 
    by (smt (verit) D_def dpq_def halfspace_pos_def mem_Collect_eq split_beta v_def x1_def x2_def
        y1_def y2_def)      
qed

lemma cNotInCHabd:
  assumes "cup 4 [a,b,c,d]"
  shows "c \<notin> convex hull {a,b,d}"
proof(rule ccontr)
  assume " \<not> c \<notin> convex hull {a, b, d}"
  hence "c \<in> convex hull {a, b, d}" by simp
  hence "c \<in> halfspace_pos b d" using convex_hull_subset_halfspace2[OF assms] 
    by (simp add: hull_inc in_mono)
  moreover have "c \<notin> halfspace_pos b d" using cNotInhalfspace_pos_bd[OF assms] .
  ultimately show False by blast
qed

end