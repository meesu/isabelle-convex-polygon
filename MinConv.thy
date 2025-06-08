theory MinConv
imports EZ_bound SlopeCapCup Invariants

begin

lemma cap_endpoint_subset:
  assumes "l\<ge>2" 
    and   "Y = {Min (set xs) | xs. set xs \<subseteq> X \<and> sdistinct xs \<and> cup (l - 1) (xs)}"
  shows   "Y \<subseteq> X"
proof  
  fix x
  assume asm: "x \<in> Y"
  then obtain xs where xsp: "x = Min (set xs)" "set xs \<subseteq> X" "cup (l-1) (xs)" 
    using assms by blast
  hence 1:  "set xs \<noteq> {}" using assms unfolding cup_def by fastforce
  hence     "finite (set xs)" using xsp(3) cup_def assms(1) by fastforce
  thus      "x\<in>X" using 1 xsp Min_in asm by fastforce
qed

lemma min_conv_lower_bnd:
  assumes "k\<ge>3" and "l\<ge>3"
    and   "min_conv_set (k-1) l \<noteq> {}"
    and   "min_conv_set k (l-1) \<noteq> {}"
  shows   "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1"    (is "?a \<le> ?b") 
          "min_conv_set k l \<noteq> {}" 
  using inf_upper
proof
  show gg:"?b \<in> {n. \<forall>S . (card S = n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs))}"  
   (is "?b \<in> {n. \<forall>S. ?GSET n S \<longrightarrow> (\<exists>xs. ?SS xs S \<and> ?CUPCAP k xs l)}")

  proof
    text\<open>We show that any point set with size min_conv (k-1) l + min_conv k (l-1) - 1 contains a k-cap or an l-cup.\<close>
    show "\<forall>S. card S = ?b \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) 
              \<longrightarrow> (\<exists>xs. (set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs)))"
    proof-
      {
        fix X
        assume asm: "?b = card X" "general_pos X" "sdistinct(sorted_list_of_set X)"
        hence   A1: "?b \<le> card X" by simp
        have X_fin:"finite X" using assms(1,2,3) asm(1) min_conv_min
          by (smt (verit) add_leE le_add_diff_inverse card.infinite diff_is_0_eq min_def not_less_eq_eq numeral_3_eq_3 plus_1_eq_Suc)

        define Y where ys: "Y = {Min (set xs) | xs. set xs \<subseteq> X \<and> sdistinct xs \<and> cup (l - 1) xs}"
        hence ysx:  "Y\<subseteq>X" using cap_endpoint_subset using asm assms by auto
        hence ygen: "general_pos Y" using asm(2) general_pos_subs by presburger
        have Y_fin: "finite Y" using X_fin rev_finite_subset ysx by blast

        have "\<exists>xs. ?SS xs X \<and> ?CUPCAP k xs l"
        proof(cases "\<exists>xs. ?SS xs X \<and> (cap k xs \<or> cup l xs)")
          case True
          then show ?thesis
            using cap_def cup_def by auto
        next
          case outerFalse:False
          then show ?thesis
          proof(cases "card (X-Y) \<ge> min_conv k (l-1)")
     
            case True
            have xy1: "general_pos (X-Y)" using general_pos_subs ysx asm(2) by blast
            have XmY_fin: "finite (X-Y)" using X_fin by blast
            text\<open>The following is not possible as X-Y can not have a (l-1)-cup as their left points have been put in Y.\<close>
            hence "\<exists>xs. set xs \<subseteq> (X-Y)\<and> sdistinct xs \<and> cup (l-1) xs"
              using outerFalse True genpos_ex gpos_generalpos min_conv_num_out sdistinct_sub X_fin asm(3) xy1 assms(4)
              by (smt (verit, del_insts) Diff_subset dual_order.trans)
            then obtain lcs where lcs: "set lcs \<subseteq> (X-Y)" "cup (l-1) lcs"  by blast
            hence C1: "Min (set lcs) \<in> (X-Y)"
              by (smt (verit, ccfv_SIG) List.finite_set Min_in One_nat_def assms(2) cup_def diff_Suc_Suc diff_less_mono in_mono less_Suc_eq less_nat_zero_code list.size(3) numeral_3_eq_3 set_empty2)
            have  C2: "Min (set lcs) \<in> Y"
              using lcs ys cup_def by auto
            show ?thesis using C1 C2 by simp
         
          next

            case False
            hence 2:"min_conv (k) (l-1) \<ge> card (X - Y) + 1" by simp

            have Y_sd:"sdistinct(sorted_list_of_set Y)"
              using asm(3) sdistinct_sub ysx X_fin
              by presburger

            have    "card (X - Y) = card X - card Y" using ysx card_def 2 asm(1)
              by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.commute card.infinite card_Diff_subset diff_0_eq_0 diff_Suc_1 diff_is_0_eq double_diff finite_Diff le_antisym subset_refl trans_le_add2)
            hence   "card Y \<ge> min_conv (k-1) l" using 2 asm(1) by linarith

            hence 3:"\<exists>xs. set xs \<subseteq> Y \<and> sdistinct xs \<and> (cap (k-1) xs)"
              using ygen outerFalse genpos_ex gpos_generalpos ysx min_conv_num_out sdistinct_sub X_fin Y_sd extract_cap_cup assms(2,3)
              by (metis (full_types) dual_order.trans)

(*  Y gets a (k-1) cap, say kap, in this case. Since each point of Y is a starting point of an (l-1) cup,
    get the (l-1) cup starting at last point in kcs. Now, the union of these two contains either an l-cup or a k-cap.          
 *)

            then obtain kap where kap: "set kap \<subseteq> Y" "(cap (k-1) kap)" by blast
                (* get (l-1) cup in X starting at kap.last *)
            hence k0:"sdistinct kap" "sorted kap" "distinct (map fst kap)" using cap_def by simp+
            have k1:"length kap = k-1" using kap cap_def by auto
            hence k2:"kap!(k-2) \<in> Y" using kap
              by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD add_leE assms(1) lessI nth_mem numeral_3_eq_3 plus_1_eq_Suc subset_iff)
            then obtain lup where lup:"kap!(k-2) = Min (set lup)" "set lup \<subseteq> X" "cup (l - 1) (lup)"   
              using ys by auto
            hence lup_sd:"sdistinct lup" using cup_def by simp
            have k3:"Min (set lup) = lup!0" using assms(2) k0(2) lup
              by (metis List.finite_set One_nat_def add_leE card.empty cup_def distinct_card distinct_map le_add_diff_inverse nth_Cons_0 numeral_3_eq_3 numeral_le_one_iff
                  plus_1_eq_Suc semiring_norm(70) sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set_nonempty)
            have k7:"lup!1 \<in> X" using lup assms(2) cup_def
              by (metis One_nat_def Suc_le_eq less_diff_conv nth_mem numeral_3_eq_3
                  plus_1_eq_Suc subsetD)
            (* try changing k-2 = Suc(k-3) to make it faster? *)
            have k4:"(kap!(k-3)) < (kap!(k-2))" using assms kap cap_def k0(2)
              by (metis (no_types, lifting) One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD add_leE distinct_map lessI numeral_3_eq_3 plus_1_eq_Suc sorted_wrt_nth_less
                  strict_sorted_iff)
            have k5:"(kap!(k-2)) < (lup!1)" using assms lup cup_def k0(2)
              by (metis One_nat_def Suc_le_lessD distinct_map k3 lessI less_diff_conv numeral_3_eq_3 plus_1_eq_Suc sorted_wrt_nth_less strict_sorted_iff)
            hence k61:"sorted [(kap!(k-3)),(kap!(k-2)),(lup!1)]" using lup kap asm 
              by (meson k4 nless_le sorted1 sorted2)
            have aa1:"distinct [(kap!(k-3)),(kap!(k-2)),(lup!1)]" using k4 k5 by auto
            have k62:"distinct (map fst [(kap!(k-3)),(kap!(k-2)),(lup!1)])"
            proof-
              have "{(kap!(k-3)),(kap!(k-2)),(lup!1)} \<subseteq> X"
                using assms(1) k1 k7 kap(1) ysx by force
              thus ?thesis using k61 aa1 asm(3) list.simps(15) sdistinct_sub X_fin
                by (metis empty_set
                    sorted_list_of_set.idem_if_sorted_distinct)

            qed
            hence "sdistinct [(kap!(k-3)),(kap!(k-2)),(lup!1)]" using k61 by simp
            hence k_noncoll:"\<not> collinear3 (kap!(k-3)) (kap!(k-2)) (lup!1)" using aa1
              by (smt (verit, best) Suc_diff_le Suc_eq_plus1 Suc_le_eq asm(2) assms(1) diff_Suc_Suc diff_diff_left
                  diff_le_self diff_zero gpos_def gpos_generalpos k1 k2 k7 kap(1) nth_mem numeral_3_eq_3 subset_iff
                  ysx)

            thus ?thesis
            proof(cases "cap3 (kap!(k-3)) (kap!(k-2)) (lup!1)")

              case True
              hence k8:"cap k (kap@[lup!1])" using kap cap_def
              proof-

                have k_rev: "rev ( (lup!1) # ( rev kap ) ) = (kap@[lup!1])" by force
                have k_lup_len: "length (kap@[lup!1]) = k" using k1 k5
                  using assms(1) by fastforce
                have kl_s:"sortedStrict (kap@[lup!1])"
                  using k1 k3 lup(1) k5 kap(2) assms append_last_sortedStrict
                  by (metis Suc_1 diff_diff_left diff_is_0_eq distinct_map k0(1) k_lup_len last_conv_nth list.size(3) plus_1_eq_Suc sorted_wrt01 strict_sorted_iff)
                have kl_inX: "set (kap@[lup!1]) \<subseteq> X"
                  using k7 kap(1) ysx by auto
                hence k29:"sdistinct (kap@[lup!1])"
                  using kl_s asm(3) sdistinct_sub X_fin
                  by (metis
                      sorted_list_of_set.idem_if_sorted_distinct
                      strict_sorted_iff)
                thus ?thesis 
                  using k29 k_lup_len True cap_def extend_cap_cup k_rev kap
                  by (metis (no_types, lifting) One_nat_def Suc_1 diff_diff_left distinct_map numeral_3_eq_3 plus_1_eq_Suc strict_sorted_iff)
              qed
              have "set kap \<subseteq> X" using kap(1) ysx by blast
              hence "set (kap@[lup!1]) \<subseteq> X" using k7 by force 
              then show ?thesis using k1 assms(1) cap_def lup kap ysx order_trans k8 by blast
            next
              case False
              hence k9:"cup l (kap!(k-3)#lup)"
              proof-
                have k_kap_len: "length (kap!(k-3)#lup) = l" using k4 lup(1) k3 lup cup_def
                  using assms(2) by auto
                have k_kap_d: "sortedStrict (kap!(k-3)#lup)"
                  by (metis (no_types, lifting) append_first_sortedStrict cup_def diff_is_0_eq distinct_map k3 k4
                      k_kap_len list.sel(1) list.size(3) lup(1,3) nth_Cons_0 sorted_wrt.elims(2) sorted_wrt01
                      strict_sorted_iff)
                have k_kap_inX: "set (kap!(k-3)#lup) \<subseteq> X"
                  using assms(1) asm(3) cap_def kap(1,2) lup(2) ysx by force
                hence "sdistinct (kap!(k-3)#lup)" using k_kap_d asm(3) sdistinct_sub X_fin
                  by (metis
                      sorted_list_of_set.idem_if_sorted_distinct
                      strict_sorted_iff)
                thus ?thesis using False k_noncoll cup_def list_check.simps exactly_one_true k3 k4 k_kap_len lup
                  by (smt (verit) diff_is_0_eq' verit_comp_simplify1(1) nth_Cons_numeral numeral_One le_numeral_extra(4) list_check.elims(1) nth_Cons_0)
              qed
              have "set (kap!(k-3)#lup) \<subseteq> X" 
                using kap(1) ysx assms(1) k1 lup(2) by force
              then show ?thesis using cup_def k9 
                by blast
            qed
          qed
        qed
      } 
      thus ?thesis by presburger  
    qed
  qed
  thus "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1"
    using min_conv_def inf_upper min_conv_leImpe min_conv_set_def by force
  show "min_conv_set k l \<noteq> {}" using gg min_conv_set_def min_conv_set_alt_def by blast
qed

thm min_conv_lower[of "a-1" "a" "b"]

lemma min_conv_lower_bnd_Suc:
  assumes "min_conv_set (k+2) (Suc(l+2)) \<noteq> {}"
    and   "min_conv_set (Suc(k+2)) (l+2) \<noteq> {}"

  shows   "min_conv (Suc(k+2)) (Suc(l+2)) 
        \<le> min_conv (k + 2) (Suc(l+2)) + min_conv (Suc(k+2)) (l + 2) - 1"
          "min_conv_set (Suc(k+2)) (Suc(l+2)) \<noteq> {}" 
  using min_conv_lower_bnd(1,2) assms(1,2)
  by (metis (no_types, lifting) 
      One_nat_def Suc_1 add_Suc_right diff_Suc_1 le_add2 numeral_3_eq_3, simp)

(* some lemmas for min_conv_upper_bnd *)

lemma sorted_union:
  fixes   S1 S2 :: "R2 set"
  assumes "finite S1" and "finite S2" and "\<forall>x\<in>S1. \<forall>y\<in>S2. fst x < fst y"
    and   "sdistinct(sorted_list_of_set S1)" and "sdistinct(sorted_list_of_set S2)"
  shows   "sorted_list_of_set (S1\<union>S2) = (sorted_list_of_set S1) @ (sorted_list_of_set S2)
        \<and> sdistinct(sorted_list_of_set (S1\<union>S2))"
  using assms
proof(induction "sorted_list_of_set S1" arbitrary: S1)
  case Nil
  then show ?case
    using sorted_list_of_set.set_sorted_key_list_of_set
    by force
next
  case (Cons a x)
  hence 1:"a = Min S1"
    using sorted_list_of_set_nonempty by fastforce

  obtain S1a where S1a:"S1a = S1 - {a}" using Cons(2) by blast
  hence 2:"x = sorted_list_of_set S1a" using Cons(2,3) sorted_list_of_set_nonempty
    by fastforce

  have 3: "sdistinct (sorted_list_of_set S1a)" using S1a Cons.prems(1,4) sdistinct_sub
    by (meson  Diff_subset)
  hence 4:"sorted_list_of_set (S1a\<union>S2) = (sorted_list_of_set S1a) @ (sorted_list_of_set S2)"
          "sdistinct (sorted_list_of_set (S1a\<union>S2))"
    using Cons S1a "2" by blast+

  have 6:"sorted_list_of_set (S1) = a # sorted_list_of_set(S1a)" using Cons(2) 2 by simp
  hence 5:"a#sorted_list_of_set (S1a\<union>S2) = a#(sorted_list_of_set S1a) @ (sorted_list_of_set S2)"
    using 4 by blast

  have 7:"\<forall>b\<in>S1a. fst a < fst b" using 1 Cons.prems(1,4) S1a assms(4) 6
    by (smt (verit, ccfv_SIG) Min_le list.simps(15,15,9)
        distinct.simps(2) insert_Diff_single insert_absorb
        insert_iff insert_iff less_eq_prod_def list.set_map
        sorted_list_of_set.set_sorted_key_list_of_set)

  hence 8:"\<forall>b\<in>S2. fst a < fst b" using assms(1,2,3) 
    by (metis Cons.hyps(2) Cons.prems(1,3) insertI1 list.simps(15)
        sorted_list_of_set.set_sorted_key_list_of_set) 
  hence 9:"\<forall>b\<in>(S1a\<union>S2). fst a < fst b" using 7 8 assms(3) by fastforce
  hence "\<forall>b\<in>(S1a\<union>S2). a \<le> b" 
    by (meson "7" UnE 8 less_eq_prod_def)
  hence 10:"a#sorted_list_of_set (S1a\<union>S2) = sorted_list_of_set (S1\<union>S2)"
    by (smt (verit, del_insts) "1" "4" Cons.prems(1,3) 6
        Diff_insert_absorb Min_in Min_le S1a Un_iff
        append_Cons assms(2) empty_not_insert finite_Diff
        finite_Un finite_has_minimal insert_absorb
        list.simps(15) set_append
        sorted_list_of_set.set_sorted_key_list_of_set
        sorted_list_of_set_nonempty)
  hence 11:"sorted_list_of_set (S1\<union>S2) = (sorted_list_of_set S1) @ (sorted_list_of_set S2)"
    using 5 6 by simp

  have "fst a \<notin> (fst `(S1a \<union> S2))" using 9
    by (metis imageE order_less_irrefl)
  hence "sdistinct(sorted_list_of_set (S1\<union>S2))" 
    using Cons.prems(1) S1a "10" "3" "4" "9" distinct_def assms(2)
    by (smt (verit, ccfv_SIG) sorted_list_of_set.sorted_sorted_key_list_of_set set_append
        distinct.simps(2) finite_Diff list.set_map list.simps(9) sorted_list_of_set.set_sorted_key_list_of_set)

  then show ?case using 11 by simp
qed

lemma general_pos_union:
  assumes "general_pos S1" 
      and "general_pos S2"
      and "\<forall>x\<in>S1. \<forall>y\<in>S2. fst x < fst y"
      and "\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2. x < y \<longrightarrow> slope x y < slope y z"
      and "\<forall>a\<in>S1. \<forall>b\<in>S2. \<forall>c\<in>S2. b < c \<longrightarrow> slope a b > slope b c"
      and "sdistinct (sorted_list_of_set S1)"
      and "sdistinct (sorted_list_of_set S2)"
      and "finite (S1\<union>S2)"
    shows "general_pos (S1 \<union> S2)"
proof-
  have gp12:  "gpos S1" "gpos S2" using assms(1,2) gpos_generalpos by simp+
  have gpint: "S1 \<inter> S2 = {}" using assms(3) by blast
  have sd: "sdistinct (sorted_list_of_set (S1\<union>S2))" using assms(3,6,7) sorted_union
    by (metis infinite_Un sorted_list_of_set.fold_insort_key.infinite)
  have "gpos (S1\<union>S2)" unfolding gpos_def
  proof(rule+)
    fix a b c
    assume  asm:"a \<in> S1 \<union> S2" "b \<in> S1 \<union> S2" "c \<in> S1 \<union> S2" 
                "distinct [a, b, c]" "collinear3 a b c"
    text \<open>This gives us 3!*2^3 = 48 cases to verify, we reduce it to 4 cases.\<close>
    then obtain u v w where uvw:"u<v" "v<w" "{u,v,w} = {a,b,c}"
      by (metis (full_types) distinct_length_2_or_more insert_commute linorder_less_linear)
    hence 0:"u < w" by simp
    hence 1:"sorted_list_of_set {a,b,c} = [u,v,w]" using uvw
      by (metis distinct_length_2_or_more distinct_singleton empty_set nless_le
          list.simps(15) sorted1 sorted2 sorted_list_of_set.idem_if_sorted_distinct)
    hence 2:"distinct (map fst [u,v,w])" using uvw sdistinct_sub asm(1,2,3) assms(8) sd
      by (metis bot.extremum insert_subset)
    hence 3:"sdistinct [u,v,w]" using uvw(1,2) by fastforce

    have 4: "collinear3 a b c = collinear3 u v w"
      by (metis asm(4,5) coll_is_affDep collinear3_def cross_affine_dependent_conv uvw(3))
    have 5: "S1\<inter>S2 = {}" using assms(3) by blast
    have 6: "u \<in> S1\<union>S2" "v \<in> S1 \<union> S2" "w \<in> S1 \<union> S2"
      by (metis asm(1,2,3,4) distinct_is_triple uvw(3))+

    show False
    proof(cases "v \<in> S1")
      case True
      have C1:"u \<in> S1" using 5 6(1) uvw(1) assms(3)
        by (metis True Un_iff not_less_iff_gr_or_eq prod_less_def)
      have C3:"w\<in>S1 \<Longrightarrow> False" using 4 asm True C1 "2" assms(1) distinctFst_distinct
        by (meson collinear3_def genpos_cross0)
      have "w\<in>S2 \<Longrightarrow> False" using 4 asm True C1 assms(4)
        by (metis "3" collinear3_def cup3_def order_less_irrefl slope_cup3 uvw(1))
      then show ?thesis using C3
        by (metis UnE asm(1,2,3,4) distinct_is_triple uvw(3))     
    next
      case False
      hence C1:"v \<in> S2" using 6(2) 5 by fast
      hence "w \<in> S2" using uvw assms(3) 5 6(3)
        by (meson Un_iff not_less_iff_gr_or_eq prod_less_def)
      then show ?thesis
        by (smt (verit, ccfv_SIG) "3" "4" "6"(1) UnE C1 asm(5) assms(2,5)
            collinear3_def distinctFst_distinct exactly_one_true genpos_cross0
            slope_cap3 uvw(2))
    qed    
  qed
  thus "general_pos (S1\<union>S2)" using gpos_generalpos by simp
qed

lemma min_conv_upper_bnd:
  assumes "min_conv_set (k+2) (Suc(l+2)) \<noteq> {}"
    and   "min_conv_set (Suc(k+2)) (l+2) \<noteq> {}"
    and   "min_conv_set (Suc(k+2)) (Suc(l+2)) \<noteq> {}" 

  shows   "min_conv (Suc (k+2)) (Suc (l+2)) 
        > (min_conv (k+2) (Suc (l+2)) - 1) 
        + (min_conv (Suc (k+2)) (l+2) - 1)"
proof-
  have "min_conv (k + 2) (Suc (l + 2)) > min_conv (k + 2) (Suc (l + 2)) - 1"
    using assms(1) min_conv_min add.assoc add_diff_inverse_nat le_add1 by fastforce
  then obtain S2t where S2t: "card S2t = min_conv (k + 2) (Suc (l + 2)) - 1" 
    "general_pos S2t"  "sdistinct(sorted_list_of_set S2t)"
    "\<forall>xs. set xs \<subseteq> S2t \<and> (sdistinct xs) \<longrightarrow> \<not>(cap (k+2) xs \<or> cup (Suc (l+2)) xs)"
    by (meson min_conv_lower_imp1o)
  hence S2tf: "finite S2t" using assms(1) min_conv_min min_conv_lower
    by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_diff_1 add_2_eq_Suc' card.infinite le_add2 min_def not_less_eq_eq)
  have S2td: "distinct (map fst (sorted_list_of_set S2t))" using S2t
    by meson
  have S2t1:"card S2t \<ge> 1" using S2t(1) assms(1) min_conv_min
    by (smt (verit, best) Suc_1 le_add1 le_add2 min_def
        le_add_diff_inverse nle_le not_less_eq_eq plus_1_eq_Suc)

  have "min_conv (Suc (k + 2)) (l + 2) > min_conv (Suc (k + 2)) (l + 2) - 1"
    using assms(2) min_conv_min add.assoc add_diff_inverse_nat le_add1 by fastforce
  then obtain S1 where S1: "card S1 = min_conv (Suc (k + 2)) (l + 2) - 1" 
    "general_pos S1" "sdistinct(sorted_list_of_set S1)"
    "\<forall>xs. set xs \<subseteq> S1 \<and> (sdistinct xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (l+2) xs)"
    by (meson min_conv_lower_imp1o)
  hence S1f: "finite S1" using assms(2)
    by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_diff_1 add_2_eq_Suc' card.infinite le_add2 min_conv_lower min_conv_min min_def not_less_eq_eq)
  have S11:"card S1 \<ge> 1" using S1(1) assms(2)
    by (smt (verit, best) Suc_1 le_add1 le_add2 min_conv_min min_def
        le_add_diff_inverse nle_le not_less_eq_eq plus_1_eq_Suc)
  have S1d: "distinct (map fst (sorted_list_of_set S1))" using S1
    by meson
      (* find t using which S2t can be translated while satisfying the conditions *)

(* show that S2 has no big cups or caps using the lemma translated_set *)
(* make sure the chosen t allows for the following conditions *)
  obtain t S2 where S2_prop: "S2 = (\<lambda>p. p + t) ` S2t"
    "\<forall>x\<in>S1. \<forall>y\<in>S2. fst x < fst y"
    "\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2. x < y \<longrightarrow> slope x y < slope y z"
    "\<forall>a\<in>S1. \<forall>b\<in>S2. \<forall>c\<in>S2. b < c \<longrightarrow> slope a b > slope b c"
    using shift_set_above S1(3) S1f S2t(3) S2tf S2t1 S1d S2td S11
    by (smt (verit, best))

  have cupExtendS1FromS2: "\<forall>x\<in>S1. \<forall>y\<in>S1. \<forall>z\<in>S2. (sdistinct [x,y,z] \<longrightarrow> cup3 x y z)" 
    using slope_cup3 S2_prop
    by (metis distinct_length_2_or_more distinct_map order_le_imp_less_or_eq sorted2)
  have capExtendS2FromS1: "\<forall>a\<in>S1. \<forall>b\<in>S2. \<forall>c\<in>S2. (sdistinct[a,b,c] \<longrightarrow> cap3 a b c)" 
    using slope_cap3 S2_prop
    by (metis distinct_length_2_or_more distinct_map order_le_imp_less_or_eq sorted2)

  have S2:"card S2 = min_conv (k + 2) (Suc (l + 2)) - 1" 
    "general_pos S2"     "sdistinct(sorted_list_of_set S2)"
    "\<forall>xs. set xs \<subseteq> S2 \<and> (sdistinct xs) \<longrightarrow> \<not>(cap (k+2) xs \<or> cup (Suc(l+2)) xs)"
    using translated_set[of "S2t" _  ] S2t S2_prop(1) by blast+

  have f12_1:"S1 \<inter> S2 = {}" using S2_prop(2) by fast
  hence f12_2:"card (S1\<union>S2) = card S1 + card S2" using S1(1) S2(1) S1f S2tf S2_prop(1)
    by (metis card_Un_disjoint finite_imageI)
  hence f12_3:"sorted_list_of_set (S1\<union>S2) = (sorted_list_of_set S1) @ (sorted_list_of_set S2)"
    "sdistinct (sorted_list_of_set (S1 \<union> S2))"
    using S2_prop(2) S2(3) S1(3) S1f S2tf sorted_union S2_prop(1)
    by (metis finite_imageI)+
  hence f12_0: "general_pos (S1\<union>S2)" 
    using S2_prop general_pos_union S1(2,3) S2(2,3) S1f S2tf by simp

  have gg:"\<forall>xs. set xs \<subseteq> (S1\<union>S2)\<and>(sdistinct xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (Suc (l+2)) xs)"
  proof(rule+)
    fix xs
    assume asm:"set xs \<subseteq> S1 \<union> S2 \<and> sdistinct xs" "cap (Suc (k + 2)) xs \<or> cup (Suc (l + 2)) xs"
    define XS1 where "XS1 = S1 \<inter> set xs"
    define XS2 where "XS2 = S2 \<inter> set xs"
    define xs1 where "xs1 = sorted_list_of_set XS1"
    define xs2 where "xs2 = sorted_list_of_set XS2"

    have xs1p1:"set xs1 \<subseteq> S1" using xs1_def XS1_def by fastforce
    have xs1p2:"sdistinct xs1" using xs1_def XS1_def S1(3) sdistinct_sub S1f
      by (meson Int_lower1 finite_imageI)

    have xs2p1:"set xs2 \<subseteq> S2" using xs2_def XS2_def by fastforce
    have xs2p2:"sdistinct xs2" using xs2_def XS2_def sdistinct_sub S2(3) S2_prop(1) S2tf
      by (metis Int_lower1 finite_imageI)

    have "XS1 \<inter> XS2 = {}" using f12_1 asm XS1_def XS2_def by auto
    hence xs_cat: "xs = xs1 @ xs2" 
      using xs1_def xs2_def S2_prop(2) XS1_def XS2_def asm(1) S1f f12_3 xs1p2 xs2p2
        S2_prop(1) S2tf
      by (smt (verit, best) Int_Un_distrib2 Int_iff Un_Int_eq(1)
          distinct_append distinct_map finite_Int
          finite_imageI set_append sorted_append
          sorted_distinct_set_unique
          sorted_list_of_set.set_sorted_key_list_of_set
          subset_Un_eq)
    hence xs_len: "length xs = length xs1 + length xs2" by simp

    text\<open>The sets xs1 and xs2 satisfy the properties \<not>(cap (k+2) xs1 \<or> cup (Suc (l+2)) xs1) and 
          \<not>(cap (Suc (k+2)) xs2 \<or> cup (l+2) xs2)\<close>
    have xs1p3:"\<not>(cap (Suc(k+2)) xs1 \<or> cup (l+2) xs1)" using S1(4) xs1p1 xs1p2 by simp
    have xs2p3:"\<not>(cap (k+2) xs2 \<or> cup (Suc(l+2)) xs2)" using S2(4) xs2p1 xs2p2 by simp

    have xs1_len_ne_0: "length xs1 \<noteq> 0"
    proof(rule ccontr)
      assume xs1asm:"\<not>length xs1 \<noteq> 0"
      hence C1:"cap (Suc (k+2)) xs \<Longrightarrow> cap (Suc (k+2)) xs2" 
        using xs_cat by fastforce
      have C2: "cap (Suc (k+2)) xs2 \<Longrightarrow> cap (k+2) (tl xs2)"
        by (metis Suc_eq_plus1 cap_reduct length_0_conv
            list.collapse xs1asm xs1p3)

      have C3:"sdistinct (tl xs2)" using xs2p2 sdistinct_subl by blast
      have C4:"set (tl xs2) \<subseteq> S2" using xs2p1
        by (metis list.sel(2) list.set_sel(2) subset_code(1))
      have C5:"cap (k+2) (tl xs2) \<Longrightarrow> False" using S2(4) C3 C4 by blast

      have "length xs1 = 0" using xs1asm by simp
      hence xs2lexs:"length xs2 = length xs" using xs_len by simp

      have "cup (Suc (l+2)) xs \<Longrightarrow> False" using xs2p3 xs_cat xs1asm by auto
      thus False using C1 C2 C5 asm(2) by blast
    qed

    have xs2_len_ne_0: "length xs2 \<noteq> 0"
    proof(rule ccontr)
      assume xs2asm: "\<not>length xs2 \<noteq> 0"
      hence C1:"cap (Suc (k+2)) xs \<Longrightarrow> False" using xs_cat xs1p3 by auto

      have "length xs2 = 0" using xs2asm by simp
      hence xs2lexs:"length xs1 = length xs" using xs_len by simp
      have C2: "cup (Suc (l+2)) xs \<Longrightarrow> cup (Suc (l+2)) xs1" using xs2asm xs_cat by auto
      have C3: "cup (Suc (l+2)) xs1 \<Longrightarrow> cup (l+2) (tl xs1)"
        by (metis cup_def cup_sub_cup diff_Suc_1 length_tl
            sublist_imp_subseq sublist_tl)

      have C4:"sdistinct (tl xs1)" using xs1p2 sdistinct_subl by blast
      have C5:"set (tl xs1) \<subseteq> S1" using xs1p1
        by (metis list.sel(2) list.set_sel(2) subset_code(1))

      have "cup (l+2) (tl xs1) \<Longrightarrow> False" using S1(4) C4 C5 by blast
      thus False using C2 C3 C1 asm(2) by blast
    qed

    have xs2_len1: "cup (Suc (l + 2)) xs \<Longrightarrow> length xs2 = 1"
    proof(rule ccontr)
      assume asmF:"cup (Suc (l + 2)) xs" "length xs2 \<noteq> 1"
      have F1:"length xs1 \<ge> 1" "length xs2 \<ge> 2" 
        using xs1_len_ne_0 xs2_len_ne_0 asmF(2) by linarith+

      then obtain l2 prexs1 where l1l2:"xs1 = prexs1 @ [l2]"
        by (metis One_nat_def not_less_eq_eq rev_exhaust list.size(3) nle_le)

      have F3:"l2 = xs!(length xs1 - 1)" using F1(1) xs_cat l1l2
        by (simp add: nth_append_right)
      have F7:"l2 \<in> S1" using l1l2 xs1p1 by auto

      obtain l3 l4 sufxs2 where l3l4:"xs2 = l3#l4#sufxs2" using F1(2)
        by (metis One_nat_def Suc_1 Suc_le_length_iff)
      hence F4:"l3 = xs!(length xs1)"          by (simp add: xs_cat)
      have F41: "xs = prexs1 @ [l2,l3,l4] @ sufxs2" using l3l4 l1l2 xs_cat
        by auto
      hence F42:"sublist [l2, l3, l4] xs" by fast
      have F62: "sdistinct [l2, l3, l4]" using F42 asm(1) sdistinct_subl by fastforce
      have F8:"l3 \<in> S2 \<and> l4 \<in> S2" using l3l4 xs2p1 XS2_def xs2_def by simp
      have F10: "cap3 l2 l3 l4" using F62 F7 F8 capExtendS2FromS1 by blast

      have "cup 3 [l2,l3,l4]" using cup_sub_cup F42 asmF sublist_imp_subseq
        by (smt (verit, ccfv_threshold) cup_def length_Cons list.size(3) numeral_3_eq_3)

      thus False using asmF(1) F10 exactly_one_true cup_def
        by (metis list_check.simps(4))
    qed

    have xs1_len1: "cap (Suc (k + 2)) xs \<Longrightarrow> length xs1 = 1"
    proof(rule ccontr)
      assume asmF: "cap (Suc (k + 2)) xs" "\<not> length xs1 = 1"
      have F1:"length xs2 \<ge> 1" "length xs1 \<ge> 2"
        using xs1_len_ne_0 xs2_len_ne_0 asmF(2) by linarith+

      then obtain l1 l2 prexs1 where l1l2:"xs1 = prexs1 @ [l1,l2]"
        by (metis One_nat_def append.assoc append_Cons
            append_Nil asmF(2) length_Cons list.size(3)
            rev_exhaust xs1_len_ne_0)

      have F2:"l1 = xs!(length xs1 - 2)" using F1(1) xs_cat l1l2 by simp
      have F3:"l2 = xs!(length xs1 - 1)" using F1(1) xs_cat l1l2
        by (simp add: nth_append_right)
      have F7:"l1 \<in> S1 \<and> l2 \<in> S1" using l1l2 xs1p1 by auto

      obtain l3 sufxs2 where l3l4:"xs2 = l3#sufxs2"
        by (metis length_0_conv list.exhaust xs2_len_ne_0)

      hence F4:"l3 = xs!(length xs1)"          by (simp add: xs_cat)
      have F41: "xs = prexs1 @ [l1,l2,l3] @ sufxs2" using l3l4 l1l2 xs_cat
        by auto
      hence F42:"sublist [l1, l2, l3] xs" by fast
      hence F61:"sdistinct [l1, l2, l3]" using asm(1) sdistinct_subl by fastforce
      have F8:"l3 \<in> S2" using l3l4 xs2p1 XS2_def xs2_def by simp
      have F9:  "cup3 l1 l2 l3" using F61 F7 F8 cupExtendS1FromS2 by blast

      have F11: "cap 3 [l1, l2, l3]" 
        using cap_sub_cap F42 cap_def sublist_imp_subseq asmF(1)
        by (smt (verit, del_insts) length_Cons list.size(3) numeral_3_eq_3)

      thus False using F9 exactly_one_true cap_def
        by (metis list_check.simps(4))
    qed

    have FF2:"cup (Suc (l + 2)) xs \<Longrightarrow> False" 
      using xs_len xs2_len1 xs1p3 cup_sub_cup xs_cat cup_def
      by (metis Suc_eq_plus1 subseq_rev_drop_many nat.inject subseq_order.order_refl)

    have FF1:"cap (Suc (k + 2)) xs \<Longrightarrow> False"
      using xs_len xs1_len1 xs2p3 cap_sub_cap xs_cat cap_def
      by (metis list_emb_append2 old.nat.inject plus_1_eq_Suc subseq_order.order_refl)

    show False using FF1 FF2 asm(2) by auto

  qed
  have asmf:"min_conv_set (Suc (k + 2)) (Suc (l + 2)) \<noteq> {}"
    using assms(1) assms(2) min_conv_lower_bnd(2) by auto
  then have "min_conv (k + 2) (Suc (l + 2)) - 1 + (min_conv (Suc (k + 2)) (l + 2) - 1)
             < min_conv (Suc (k + 2)) (Suc (l + 2))" 
    using S1(1) S2(1) add.commute f12_0 f12_2 min_conv_lower[of "Suc (k+2)" "Suc (l+2)"] min_conv_set_alt_def assms gg f12_3(2)
    by (metis (lifting))
  thus ?thesis using asmf by simp
qed

(* assume points are distinct in x coords
-- 
Note that we have already observed this to be the case when k or l is 3.
We proceed by induction. Suppose that we have a set A of (k+l-5 choose k-3)
points with no (k − 1)-cup and no l-cap, and a set B of (k+l-5 choose k-2) 
points with no k-cup and no (l − 1)-cap. Translate these sets so that the 
following conditions are satisfied:
(i) every point of B has greater first coordinate than the first coordinates of
points of A,
(ii) the slope of any line connecting a point of A to a point of B is greater than
the slope of any line connecting two points of A or two points of B.
Let X = A \<union> B be the resulting configuration. Any cup in X that contains
elements of both A and B may have only one element of B. It follows that X
contains no k-cup. We similarly see that X contains no l-cap.
--
*)

lemma min_conv_k_l_eq:
  "min_conv (Suc (k+2)) (Suc (l+2)) = min_conv (k+2) (Suc (l+2)) + min_conv (Suc (k+2)) (l+2) - 1 
 \<and> min_conv_set (Suc (k+2)) (Suc (l+2)) \<noteq> {}"
proof(induction "k+l" arbitrary: k l)
  case 0
  then show ?case using min_conv_arg_swap min_conv_base numeral_3_eq_3 by fastforce
next
  case (Suc x)
  then show ?case
  proof(cases "k=0 \<or> l=0")
    case True
    have 1: "min_conv (k + 2) (Suc (l + 2)) + (min_conv (Suc (k + 2)) (l + 2) - 1)
           = min_conv (Suc (k + 2)) (Suc (l + 2))" 
      using True min_conv_2(1) min_conv_arg_swap min_conv_base 
      by (metis add_2_eq_Suc' add_Suc_shift diff_Suc_1 le_add1 numeral_3_eq_3 plus_nat.add_0)
    have 2: "min_conv_set 3 (Suc (l + 2)) \<noteq> {}" using min_conv_base by simp
    have 3: "min_conv_set (Suc (k + 2)) 3 \<noteq> {}"
      using min_conv_base min_conv_sets_eq min_conv_set_def by simp
    thus ?thesis using 1 2 3 True numeral_3_eq_3 min_conv_2(1) min_conv_arg_swap min_conv_base
      by (smt (z3) One_nat_def Suc_eq_plus1 add.commute diff_Suc_1 le_add2 nat_1_add_1
          nat_arith.suc1)
  next
    case False
    hence FC1:"k\<ge>1"  "l\<ge>1" by simp+
    have F1:"(k)+(l-1) = x" using FC1 Suc by simp
    have S1:"min_conv_set (Suc (k + 2)) (l + 2) \<noteq> {}" using Suc F1
      by (metis FC1(2) add_2_eq_Suc' le_add_diff_inverse plus_1_eq_Suc)
    have F2:"(k-1) + l = x" using FC1 Suc by simp
    have S2:"min_conv_set (k + 2) (Suc (l + 2)) \<noteq> {}" using Suc F2
      by (metis FC1(1) add_2_eq_Suc' le_add_diff_inverse plus_1_eq_Suc)

    have LT:  "min_conv (Suc (k + 2)) (Suc (l + 2))
            \<le> min_conv (k + 2) (Suc (l + 2)) + min_conv (Suc (k + 2)) (l + 2) - 1"
              "min_conv_set (Suc (k + 2)) (Suc (l + 2)) \<noteq> {}"
      using min_conv_lower_bnd_Suc S1 S2 by simp+
    have GT:  "min_conv (Suc (k + 2)) (Suc (l + 2))
            > min_conv (k + 2) (Suc (l + 2)) - 1 + (min_conv (Suc (k + 2)) (l + 2) - 1)"
      using LT(2) S1 S2 min_conv_upper_bnd by simp
    show ?thesis using LT GT by linarith
  qed 
qed

lemma min_conv_bin:
  "min_conv (k+3) (l+3) = ((k + l + 2) choose (k + 1)) + 1"
proof(induction "k+l" arbitrary: l k)
  case (Suc x)
  then show ?case
  proof(cases "k = 0")
    case False
    have 1:"k\<ge>1" using False by simp
    show ?thesis
    proof(cases "l = 0")
      case True
      hence "min_conv (k + 3) (l + 3) = k + 3" 
        using min_conv_arg_swap min_conv_base[of "k+3"] by simp
      moreover have "(k + l + 2 choose k + 1) + 1 = k + 3" using True binomial_Suc_n by simp
      ultimately show ?thesis using min_conv_base by simp
    next
      case False
      hence 2:"l\<ge>1" by simp
      have    "x = (k-1) + l" using 1 Suc by linarith
      hence 3:"min_conv (k + 2) (l + 3) = (k + l + 1 choose k) + 1" using Suc by fastforce
      have    "x = k + (l-1)" using 2 Suc by linarith
      hence   "min_conv (k + 3) (l + 2) = (k + l + 1 choose k + 1) + 1" using Suc by fastforce
      hence   "min_conv (k+3) (l+3) = (k + l + 1 choose k) + (k + l + 1 choose k + 1) + 1"
        using 3 min_conv_k_l_eq
        by (simp add: numeral_3_eq_3)
      then show ?thesis using binomial_Suc_Suc by simp
    qed
  qed(simp add: min_conv_base)
qed(simp add: min_conv_base)

text \<open>We prove that cups and caps form a convex polygon.\<close>

lemma cup_genpos:
  assumes "cup (length xs) xs"
  shows   "general_pos (set xs)"
proof-
  have "gpos (set xs)" unfolding gpos_def
  proof(rule+)
    fix a b c
    assume asm:"a \<in> set xs" "b \<in> set xs" "c \<in> set xs" "distinct [a,b,c]" "collinear3 a b c"
    then obtain u v w where uvw:"[u,v,w] = sorted_list_of_set {a,b,c}"
      by (smt (verit, best) distinct_length_2_or_more
          empty_set insert_commute linorder_not_less
          list.simps(15) order_less_imp_le sorted1 sorted2
          sorted_list_of_set.idem_if_sorted_distinct)
    have 1:"subseq [u,v,w] xs" using assms asm uvw
      by (metis (no_types, lifting) bot.extremum cup_def distinctFst_distinct insert_subset
          subseq_sorted_subset)
    hence 2:"sdistinct [u,v,w]" using assms uvw
      by (simp add: cup_def sdistinct_subseq)
    hence "\<not>collinear3 u v w" using assms 1 slope_cup3 collinear3_def cup_is_slopeinc_subseq
      by (metis cup3_def order_less_le)
    then show False 
      using 2 asm(4,5) uvw
      by (metis coll_is_affDep sorted_list_of_set.set_sorted_key_list_of_set strict_sorted_iff
          finite.emptyI finite.insertI list.set(1) list.simps(15) sdistinct_sortedStrict)
  qed
  thus ?thesis using gpos_generalpos by simp
qed

(*Divakaran's part begins here*)
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
  have 4: "v \<bullet> a \<ge> D" using cup_abd inner_d3 dpqNE0
      unfolding D_def x1_def x2_def y1_def y2_def cup3_def cross3_def
      by (metis "1" divide_right_mono dpqNE0 inner_commute inner_d3 mult.commute nless_le)
  show ?thesis using 4 unfolding halfspace_pos_def
    by (metis (mono_tags, lifting) D_def dpq_def mem_Collect_eq split_beta v_def x1_def 
        x2_def y1_def y2_def) 
qed

lemma convex_hull_subset_halfspace2: 
  assumes "cup 4 [a,b,c,d]"
  assumes "c \<in> convex hull {a,b,d}"
  shows "convex hull {a,b,c,d}\<subseteq> halfspace_pos b d"
proof-
  have s_1:"b \<noteq> d" using assms(1) unfolding cup_def by fastforce
  thus ?thesis using assms(2) a_c_belongs_halfspace_a_c[OF s_1]  
      cup4_last_halfspace_pos[OF assms(1)]
    by (metis halfspace_pos_convex assms(1) cup4_first_halfspace_pos hull_redundant
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

(*Divakaran's part ends here*)

lemma cup_poly:
  assumes "cup (length xs) xs"
  shows   "convex_poly (length xs) xs"
proof(rule ccontr)
  assume asm:"\<not>convex_poly (length xs) xs"
  have 0:"sdistinct xs" using assms cup_def by simp
  have 1:"subseq ys xs \<Longrightarrow> length ys = card (set ys)" for ys
    by (metis assms cup_def distinct_card distinct_map sdistinct_subseq)
  have 2:"sorted xs" using 0 by simp
  have "\<not>convex_pos (set xs)" using asm by simp
  then obtain Y where Y: "Y \<subseteq> (set xs)" "card Y \<le> 4" "\<not>convex_pos Y" using fourconvex by meson
  define ys where ys:"ys = sorted_list_of_set Y"
  hence 23: "distinct ys" by simp
  hence 3:"sdistinct ys" using 0
    by (metis Y(1) distinct_map sdistinct_subseq subseq_sorted_subset ys) 
  hence 34:"sorted_wrt (<) ys"
    using sdistinct_sortedStrict by blast
  hence 4:"subseq ys xs" using Y(1) 0 2 subseq_sorted_subset distinct_map ys by blast
  have 5:"affine_dependent Y" using Y(2,3) affine_hull_convex_hull hull_inc
    by (metis affine_dependent_def convex_pos_def)

  show False
    text \<open>Since one of the points is contained within the triangle formed by other three: it forms a cap with some two of these points.\<close>
  proof(cases "card Y = 4")
    case True
    have num_4:"4 = Suc (Suc (Suc (Suc 0)))" using numeral_3_eq_3 by simp
    have "length (sorted_list_of_set Y) = 4"
      using True by simp
    then obtain a b c d where abcd: "a#b#c#d#Nil = sorted_list_of_set Y"
      using num_4 length_Suc_conv Suc_length_conv length_0_conv by smt
    hence y_set: "Y = {a,b,c,d}"
      by (metis List.finite_set Y(1) infinite_super
          list.set(1) list.simps(15)
          sorted_list_of_set.set_sorted_key_list_of_set)
    hence y_fin: "\<forall>e\<in>Y. finite (Y-{e})" by blast
    have ys_abcd:"ys = [a,b,c,d]" using abcd ys by argo
    hence y_a:"\<forall>e\<in>Y. card (Y-{e}) = 3" using True 23 Y(1) num_4 ys
      by (metis add_diff_cancel_left' card_Diff_singleton numeral_3_eq_3 plus_1_eq_Suc)
    hence y_a_len:"\<forall>e\<in>Y. length (sorted_list_of_set (Y-{e})) = 3" by simp
    have y_sub_ind:"\<forall>e\<in>Y. \<not>affine_dependent (Y-{e})" 
      using general_pos_subs genpos_cross0 assms general_pos_def y_a
        cross_affine_dependent_conv cup_genpos Y(1) nsubset_def
      by (metis (mono_tags, lifting) Diff_subset mem_Collect_eq)
    hence y_sub_tri:"\<forall>e\<in>Y. convex_pos (Y-{e})"
      by (metis affine_dependent_def affine_hull_convex_hull convex_pos_def hull_inc)
    have coeffs:"\<forall>e\<in>Y. e \<in> convex hull (Y-{e}) \<longrightarrow>
          (\<exists>u. (sum u (Y-{e}) = 1) \<and> (\<forall>x\<in>(Y-{e}). 0 < u x) \<and> sum (\<lambda>x. u x *\<^sub>R x) (Y-{e}) = e)"
    proof(rule, rule)
      fix e
      assume asm:"e \<in> Y" "e \<in> convex hull (Y - {e})"
      then obtain u where uy: "(sum u (Y-{e}) = 1)" "(\<forall>x\<in>(Y-{e}). 0 \<le> u x)" 
                              "sum (\<lambda>x. u x *\<^sub>R x) (Y-{e}) = e" 
        using convex_hull_finite y_fin mem_Collect_eq
        by (smt (verit, best))
      have "e \<in> convex hull (Y-{x, e})" if asm:"x \<in> (Y-{e}) \<and> u x = 0" for x
      proof-
        have 1:"sum u (Y - {x, e}) = 1"
          using uy asm
          by (smt (verit, ccfv_SIG) DiffD2 Diff_insert
              List.finite_set Y(1) finite.emptyI finite_Diff2
              finite_insert insertI1 insert_Diff rev_finite_subset
              sum.insert)
        have 2:"(\<forall>x\<in>Y - {x, e}. 0 \<le> u x) \<and> (\<Sum>z\<in>Y - {x, e}. u z *\<^sub>R z) = e"
        proof(rule)
          show "\<forall>x\<in>Y - {x, e}. 0 \<le> u x" using uy by blast
          have "(\<Sum>z\<in>Y - {x, e}. u z *\<^sub>R z) + (u x *\<^sub>R x) = e" 
            using uy add.commute asm
            by (metis (no_types, lifting) Diff_insert2
                insert_absorb insert_commute sum.infinite
                sum.insert_remove zero_neq_one)
          thus "(\<Sum>z\<in>Y - {x, e}. u z *\<^sub>R z) = e" using asm by simp
        qed
        hence "e \<in> {y. \<exists>u. (\<forall>x\<in>Y-{x,e}. 0 \<le> u x) \<and> sum u (Y-{x,e}) = 1 \<and> (\<Sum>x\<in>Y-{x,e}. u x *\<^sub>R x) = y}"
          using "1" by blast
        thus ?thesis using convex_hull_finite Y(1) finite_subset
          by (smt (verit, del_insts) mem_Collect_eq
              sum.infinite)
      qed

      hence "x \<in> (Y-{e}) \<and> u x = 0 \<Longrightarrow> False" for x
        using y_sub_ind Diff_insert2 Diff_insert_absorb convex_pos_def asm y_sub_tri
              hull_redundant_eq insert_absorb insert_commute mk_disjoint_insert asm
        by (smt (verit, best))

      thus "(\<exists>u. (sum u (Y-{e}) = 1) \<and> (\<forall>x\<in>(Y-{e}). 0 < u x) \<and> sum (\<lambda>x. u x *\<^sub>R x) (Y-{e}) = e)"
        by (metis (lifting) antisym_conv2 uy(1,2,3))
    qed

    have "e\<in>{a,b,c,d} \<Longrightarrow> e \<notin> convex hull (Y-{e})" for e
    proof-
      have ca:"\<not> a \<in> convex hull (Y-{a})"
      proof(rule ccontr)
        assume "\<not> a \<notin> convex hull (Y - {a})"
        hence "a\<in>convex hull (Y-{a})" by simp
        then obtain u where uY: "(\<forall>x\<in>(Y-{a}). 0 < u x)" "sum u (Y-{a}) = 1"
                                "sum (\<lambda>x. u x *\<^sub>R x) (Y-{a}) = a"
          using coeffs Y(1) y_set by auto
        then have c_sum:"u b + u c + u d = 1" using y_set coeffs
          by (smt (verit, best) "23" Diff_insert_absorb abcd
              distinct.simps(2) empty_set finite.emptyI
              finite_insert list.simps(15) sum.empty sum.insert ys)
        have fst_a_min:"fst a < fst b" "fst a < fst c" "fst a < fst d" using ys_abcd "3"
          by (smt (verit)  distinct_length_2_or_more
              less_eq_prod_def list.simps(9) sorted2)+
        have "fst a = sum (\<lambda>x. u x * (fst x)) (Y-{a})" using uY
          by (metis (mono_tags, lifting) fst_scaleR fst_sum
              real_scaleR_def sum.cong)
        also have "... = u b * (fst b) + u c * (fst c) + u d * (fst d)"
          using uY
          by (smt (verit) "23" Diff_insert_absorb abcd
              distinct.simps(2) empty_set finite.emptyI
              finite_insert list.simps(15) sum.empty sum.insert
              y_set ys)
        also have " ... >  u b * (fst a) + u c * (fst a) + u d * (fst a)" 
          using fst_a_min "23" uY(1) y_set ys_abcd
          by (smt (verit, best) DiffI insert_absorb insert_iff
              insert_not_empty mult_less_cancel_left_pos)
        ultimately show False
          by (metis c_sum distrib_left
              mult.commute mult.right_neutral
              order_less_irrefl)
      qed
      have cb:"\<not> b \<in> convex hull (Y-{b})"
      proof(rule ccontr)
        assume asm:"\<not> b \<notin> convex hull (Y - {b})"
        hence "b\<in>convex hull (Y-{b})" by simp
             have y_d: "Y-{b} = {a,c,d}" using y_set "23" ys_abcd by auto
        have cup_ls:"cup 4 [a,b,c,d]" 
          by (metis "4" \<open>length (sorted_list_of_set Y) = 4\<close> abcd assms cup_sub_cup ys_abcd)
        show False using bNotInCHacd[OF cup_ls] asm y_d by auto
      qed
      have cc:"\<not> c \<in> convex hull (Y-{c})" 
      proof(rule ccontr)
        assume asm:"\<not> c \<notin> convex hull (Y - {c})"
        hence "c\<in>convex hull (Y-{c})" by simp
        have y_d: "Y-{c} = {a,b,d}" using y_set "23" ys_abcd by auto
        have cup_ls:"cup 4 [a,b,c,d]" 
          by (metis "4" \<open>length (sorted_list_of_set Y) = 4\<close> abcd assms cup_sub_cup ys_abcd)
        show False using cNotInCHabd[OF cup_ls] asm y_d by auto
      qed
      have cd:"\<not> d \<in> convex hull (Y-{d})"
      proof(rule ccontr)
        assume "\<not> d \<notin> convex hull (Y - {d})"
        hence "d\<in>convex hull (Y-{d})" by simp
        then obtain u where uY: "(\<forall>x\<in>(Y-{d}). 0 < u x)" "sum u (Y-{d}) = 1"
                                "sum (\<lambda>x. u x *\<^sub>R x) (Y-{d}) = d"
          using coeffs Y(1) y_set by auto
        then have c_sum:" u a + u b + u c = 1" using y_set coeffs
          by (smt (z3) "23" Diff_insert_absorb abcd
              distinct.simps(2) empty_set finite.emptyI
              finite_insert insertCI insert_absorb insert_commute
              list.simps(15) sum.empty sum.insert ys)
        have y_d: "Y-{d} = {a,b,c}" using y_set "23" ys_abcd by auto
        have fst_a_min:"fst d > fst a" "fst d > fst b" "fst d > fst c" using ys_abcd "3"
          by (smt (verit)  distinct_length_2_or_more less_eq_prod_def list.simps(9) sorted2)+
      
        have "fst d = sum (\<lambda>x. u x * (fst x)) (Y-{d})" using uY
          by (metis (mono_tags, lifting) fst_scaleR fst_sum real_scaleR_def sum.cong)

        also have "... = u a * (fst a) + u b * (fst b) + u c * (fst c)"
          using uY(3) y_d "23" abcd ys
          by (smt (verit, ccfv_threshold) distinct.simps(2) empty_set finite.emptyI
              finite_insert insert_iff list.simps(15) sum.empty sum.insert)

        also have " ... <  u a * (fst d) + u b * (fst d) + u c * (fst d)" 
          using fst_a_min "23" uY(1) y_set ys_abcd
          by (smt (verit, best) DiffI insert_absorb insert_iff
              insert_not_empty mult_less_cancel_left_pos)

        ultimately show False using c_sum
          by (metis distrib_left mult.commute mult.right_neutral order_less_irrefl)
      qed

      show ?thesis using ca cb cc cd Y(3) convex_pos_def y_set
        by (smt (verit, ccfv_SIG) hull_redundant_eq insertE insert_Diff singletonD)
    qed
    then show ?thesis using Y(3) convex_pos_def y_set
      by (metis hull_inc)
  next
    case False
    hence y_3:"card Y \<le> 3"
      using Y(2) by linarith
    then show ?thesis
    proof(cases "card Y = 3")
      case True
      hence "\<not>affine_dependent Y" using general_pos_subs genpos_cross0 assms general_pos_def cross_affine_dependent_conv cup_genpos Y(1) nsubset_def
        by (metis (mono_tags, lifting) mem_Collect_eq)
      thus ?thesis using 5 by simp 
    next
      case False
      hence y_2:"card Y \<le> 2" using y_3 by simp
      have C0:"card Y = 0 \<Longrightarrow> False" 
        using affine_independent_0 "5" Y(1) finite_subset by fastforce
      have C1:"card Y = 1 \<Longrightarrow> False" 
        using affine_independent_1 by (metis "5" card_1_singletonE)
      have    "card Y = 2 \<Longrightarrow> False" 
        using "5" affine_independent_2 by (metis card_2_iff)
      thus ?thesis using y_2 C0 C1 
        by fastforce 
    qed
  qed
qed

lemma cap_poly:
  assumes "cap (length xs) xs"
  shows   "convex_poly (length xs) xs"
  using cup_poly cap_orig_refl_rev[of "length xs" "xs"] length_neg
  by (metis assms convex_pos_list_refl implm_rev_reflect_inv length_rev set_rev)

lemma min_conv_set_non_empty:
  "min_conv_set n n \<noteq> {}"
proof(cases "n \<le> 2")
  case True
  then show ?thesis using min_conv_0 min_conv_1 min_conv_2
    by (metis One_nat_def Suc_1 bot_nat_0.extremum_uniqueI le_SucE)
next
  case False
  hence "n\<ge>3" by simp
  then show ?thesis using min_conv_k_l_eq
    by (metis One_nat_def Suc_1 add_Suc_right le_add_diff_inverse2 numeral_3_eq_3)
qed

lemma EZ_min_conv:"EZ n \<le> min_conv n n"
proof-
  have "cap a xs \<or> cup a xs \<longrightarrow> convex_poly a xs" for a xs 
    using cup_poly cap_poly cap_def cup_def by presburger
  hence "min_conv_set n n \<subseteq>
    {N :: nat. (\<forall>S :: R2 set. (card S \<ge> N \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
               \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> convex_poly n xs))}" (is "_ \<subseteq> ?EZXS n")
    by (smt (verit) mem_Collect_eq min_conv_num_out_set subset_eq)
  thus "EZ n \<le> min_conv n n"
    using EZ_def inf_subset_bounds min_conv_def min_conv_set_def min_conv_set_non_empty
    by fastforce
qed

(*
lemma min_conv_bin:
  "min_conv (k+3) (l+3) = ((k + l + 2) choose (k + 1)) + 1"*)

lemma EZ_bound_final:
      assumes "n \<ge> 3" 
      shows "EZ n \<le> ((( 2*n -4 ) choose (n - 2)) + 1)"
  using assms min_conv_bin[of "n-3" "n-3"]  EZ_min_conv[of n] 
  by (smt (verit, ccfv_SIG) One_nat_def Suc_1 Suc_eq_plus1 add_mult_distrib2 diff_Suc_numeral
      eq_numeral_Suc le_add_diff_inverse2 mult_2 numeral_3_eq_3 numeral_Bit0_eq_double
      ordered_cancel_comm_monoid_diff_class.add_diff_assoc plus_1_eq_Suc right_diff_distrib') 
end


