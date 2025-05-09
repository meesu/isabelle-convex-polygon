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
shows "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1"
            (is "?a \<le> ?b") 
  using inf_upper
proof
  show "?b \<in> {n. \<forall>S . (card S = n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
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
        have X_fin:"finite X"
          by (smt (verit) add_leE asm(1)
              assms(1,2) card.infinite
              diff_is_0_eq
              le_add_diff_inverse
              min_conv_min min_def
              not_less_eq_eq
              numeral_3_eq_3
              plus_1_eq_Suc)
        define Y where ys: "Y = {Min (set xs) | xs. set xs \<subseteq> X \<and> sdistinct xs \<and> cup (l - 1) xs}"
        hence ysx:  "Y\<subseteq>X" using cap_endpoint_subset using asm assms by auto
        hence ygen: "general_pos Y" using asm(2) general_pos_subs by presburger
        have Y_fin: "finite Y"
          using X_fin rev_finite_subset
            ysx by blast

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
              using outerFalse True genpos_ex gpos_generalpos min_conv_num_out sdistinct_sub X_fin asm(3) xy1
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
              using ygen outerFalse genpos_ex gpos_generalpos ysx min_conv_num_out sdistinct_sub X_fin Y_sd
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
                  by (smt (verit)  diff_is_0_eq' verit_comp_simplify1(1) nth_Cons_numeral numeral_One
                      le_numeral_extra(4) list_check.elims(1) nth_Cons_0)
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
  thus ?thesis 
    using min_conv_def inf_upper min_conv_leImpe
    by force
qed

thm min_conv_lower[of "a-1" "a" "b"]

lemma min_conv_upper_bnd:
  shows "min_conv (Suc (k+2)) (Suc (l+2)) > 
        (min_conv (k+2) (Suc (l+2)) - 1) + (min_conv (Suc (k+2)) (l+2) - 1)"
        (is "?P a b > ?n1 + ?n2")
proof(induction "k+l" arbitrary: k l)
  case 0
  then show ?case using "0" min_conv_arg_swap min_conv_base numeral_3_eq_3 by fastforce
next
  case (Suc x)
  then show ?case 
  proof(cases "k=0 \<or> l=0")
    case True
    then show ?thesis using min_conv_2 min_conv_arg_swap
      by (metis (no_types, opaque_lifting) One_nat_def Suc_1 Suc_eq_plus1 add_Suc_shift diff_Suc_1'
          diff_diff_cancel le_add2 less_one min_conv_base numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(3)
          zero_less_diff)
  next
    case False
    hence FC1:"k\<ge>1"  "l\<ge>1" by simp+
    have F1:"(k)+(l-1) = x" using FC1 Suc by simp
    have F2:"(k-1) + l = x" using FC1 Suc by simp

    have "min_conv (k + 2) (Suc (l + 2)) > min_conv (k + 2) (Suc (l + 2)) - 1"
      by (smt (verit) F2 FC1(1) Suc.hyps(1) add_2_eq_Suc' add_diff_inverse_nat bot_nat_0.extremum_strict diff_le_self diff_less_Suc less_one nless_le
          plus_1_eq_Suc)
    then obtain S2t where S2t: "card S2t = min_conv (k + 2) (Suc (l + 2)) - 1" 
      "general_pos S2t"  "sdistinct(sorted_list_of_set S2t)"
      "\<forall>xs. set xs \<subseteq> S2t \<and> (sdistinct xs) \<longrightarrow> \<not>(cap (k+2) xs \<or> cup (Suc (l+2)) xs)"
      by (meson min_conv_lower_imp1o)
    hence S2tf: "finite S2t"
      by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_diff_1 add_2_eq_Suc' card.infinite le_add2 min_conv_lower min_conv_min min_def not_less_eq_eq)
    have S2td: "distinct (map fst (sorted_list_of_set S2t))" using S2t
      by meson
    have S2t1:"card S2t \<ge> 1" using S2t(1)
      by (smt (verit, best) Suc_1 le_add1 le_add2 min_conv_min min_def
          le_add_diff_inverse nle_le not_less_eq_eq plus_1_eq_Suc)

    have "min_conv (Suc (k + 2)) (l + 2) > min_conv (Suc (k + 2)) (l + 2) - 1"
      by (smt (verit) F1 FC1(2) Nat.add_diff_assoc2 Suc.hyps(1) Suc_diff_1 add_Suc_right diff_is_0_eq' nat_le_linear neq0_conv not_less_eq
          zero_less_diff)
    then obtain S1 where S1: "card S1 = min_conv (Suc (k + 2)) (l + 2) - 1" 
      "general_pos S1" "sdistinct(sorted_list_of_set S1)"
      "\<forall>xs. set xs \<subseteq> S1 \<and> (sdistinct xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (l+2) xs)"
      by (meson min_conv_lower_imp1o)
    hence S1f: "finite S1"
      by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_diff_1 add_2_eq_Suc' card.infinite le_add2 min_conv_lower min_conv_min min_def not_less_eq_eq)
    have S11:"card S1 \<ge> 1" using S1(1)
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

    have f12_0: "general_pos (S1\<union>S2)" sorry (* use S2_prop *)
    have f12_1:"S1 \<inter> S2 = {}" using S2_prop(2) by fast
    hence f12_2:"card (S1\<union>S2) = card S1 + card S2" using S1(1) S2(1) S1f S2tf S2_prop(1)
      by (metis card_Un_disjoint finite_imageI)
    hence f12_3:"sorted_list_of_set (S1\<union>S2) = (sorted_list_of_set S1) @ (sorted_list_of_set S2)"      
      using S2_prop(2) S2(3) S1(3) S1f S2tf sorry
    hence f12_4:"sdistinct (sorted_list_of_set (S1 \<union> S2))" using S2(3) S1(3) S2_prop(2) f12_1 sorry

    have "\<forall>xs. set xs \<subseteq> (S1\<union>S2) \<and> (sdistinct xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (Suc (l+2)) xs)"
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
        using xs1_def xs2_def S2_prop(2) XS1_def XS2_def asm(1) S1f f12_3 f12_4 xs1p2 xs2p2
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
    then show ?thesis
      by (metis S1(1) S2(1) add.commute f12_0 f12_2 f12_4 min_conv_lower)
  qed
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

lemma min_conv_equality:
  "min_conv (Suc (k+2)) (Suc (l+2)) = min_conv (k+2) (Suc (l+2)) + min_conv (Suc (k+2)) (l+2) - 1"
proof-

  have 1:"min_conv (Suc (k+2)) (Suc (l+2)) \<le> min_conv (k+2) (Suc (l+2)) + min_conv (Suc (k+2)) (l+2) - 1" using min_conv_lower_bnd 
    by (metis One_nat_def Suc_1 Suc_eq_numeral diff_Suc_1 le_numeral_Suc le_numeral_extra(4) numeral_3_eq_3 trans_le_add2)
  have 2:"min_conv (k+2) (Suc (l+2)) \<ge> 1"
    by (metis "1" Suc_eq_plus1 diff_0_eq_0 less_Suc_eq linorder_not_less min_conv_upper_bnd(1) nat_arith.rule0 not_add_less2 plus_nat.add_0)
  hence 3:"min_conv (Suc (k+2)) (l+2) \<ge> 1"
    by (metis "1" One_nat_def add_lessD1 diff_0_eq_0 diff_Suc_diff_eq1 linorder_not_less min_conv_upper_bnd(1) not_less_eq_eq)
  have "(min_conv (k+2) (Suc (l+2)) - 1) + (min_conv (Suc (k+2)) (l+2) - 1)
        = min_conv (k+2) (Suc (l+2)) + min_conv (Suc (k+2)) (l+2) - 2"
    using 2 3 by auto
  hence "min_conv (Suc (k+2)) (Suc (l+2)) \<ge> min_conv (k+2) (Suc (l+2)) + min_conv (Suc (k+2)) (l+2) - 1" using min_conv_upper_bnd
    by (smt (verit, del_insts) Suc_1 add.commute add_diff_inverse_nat diff_Suc_Suc less_Suc_eq_le less_diff_conv2 less_imp_diff_less less_or_eq_imp_le plus_1_eq_Suc trans_less_add1)

  thus ?thesis using 1 by simp
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
        using 3 min_conv_equality
        by (simp add: numeral_3_eq_3)
      then show ?thesis using binomial_Suc_Suc by simp
    qed
  qed(simp add: min_conv_base)
qed(simp add: min_conv_base)


end

(* 

      have xs12_len1: "length xs1 \<le> 1 \<or> length xs2 \<le> 1"
      proof(rule ccontr)
        assume asmF:"\<not> (length xs1 \<le> 1 \<or> length xs2 \<le> 1)"
        hence F1:"length xs1 \<ge> 2"  "length xs2 \<ge> 2"  by simp+

        then obtain l1 l2 prexs1 where l1l2:"xs1 = prexs1 @ [l1,l2]"
          by (metis One_nat_def append.assoc asmF not_less_eq_eq rev_exhaust
              append_Cons append_Nil length_Cons list.size(3) nle_le)

        have F2:"l1 = xs!(length xs1 - 2)" using F1(1) xs_cat l1l2 by simp
        have F3:"l2 = xs!(length xs1 - 1)" using F1(1) xs_cat l1l2
          by (simp add: nth_append_right)
        have F7:"l1 \<in> S1 \<and> l2 \<in> S1" using l1l2 xs1p1 by auto

        obtain l3 l4 sufxs2 where l3l4:"xs2 = l3#l4#sufxs2"
          by (metis One_nat_def Suc_eq_plus1 asmF dual_order.refl le_add1 list.size(3,4) neq_Nil_conv)

        hence F4:"l3 = xs!(length xs1)"          by (simp add: xs_cat)
        have F41: "xs = prexs1 @ [l1,l2,l3,l4] @ sufxs2" using l3l4 l1l2 xs_cat
          by auto
(*         have F5:"length xs1 - 2 < length xs1 - 1" "length xs1 - 1 < length xs1" 
                "length xs1 < length xs1 + 1"     "length xs1 + 1 < length xs"
          using F1 xs_cat by auto
 *)
        hence F42:"sublist [l1, l2, l3, l4] xs" by fast
        hence F43: "sublist [l1, l2, l3] xs"
          by (metis append_Cons self_append_conv2
              sublist_append_rightI
              sublist_order.dual_order.trans)
        have F44: "sublist [l2, l3, l4] xs"
          by (meson F42 sublist_Cons_right
              sublist_order.dual_order.refl
              sublist_order.dual_order.trans)
        hence F61:"sdistinct [l1, l2, l3]" using F43 asm(1) sdistinct_subl by fastforce
        have F62: "sdistinct [l2, l3, l4]" using F44 asm(1) sdistinct_subl by fastforce
        have F8:"l3 \<in> S2 \<and> l4 \<in> S2" using l3l4 xs2p1 XS2_def xs2_def by simp
        have F9:  "cup3 l1 l2 l3" using F61 F7 F8 cupExtendS1FromS2 by blast
        have F10: "cap3 l2 l3 l4" using F62 F7 F8 capExtendS2FromS1 by blast

        have F11: "cap (Suc (k + 2)) xs \<Longrightarrow> cap3 l1 l2 l3" using F43 cap_sub_cap sorry
        have F12: "cup (Suc (l + 2)) xs \<Longrightarrow> cup3 l2 l3 l4" using F44 cup_sub_cup sorry
        show False using asm(2) F9 F10 F11 F12 exactly_one_true by blast
      qed


 *)