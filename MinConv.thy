theory MinConv
  imports EZ_bound

begin
lemma min_conv_arg_swap:
  "min_conv k l = min_conv l k"
  unfolding min_conv_def sorry

thm min_conv_base

thm inf_upper

lemma append_first_sortedStrict:
  assumes "sortedStrict (B :: R2 list)" and "(b :: R2) < hd B"
  shows  "sortedStrict (b#B)"
proof-
  have 1: "sorted B" "distinct B" using assms strict_sorted_iff by auto
  have 2: "sorted (b#B)" using assms(2) 1(1)
    by (metis list.sel(1) neq_Nil_conv nless_le sorted1 sorted2)
  have 3: "distinct (b#B)" using assms(2) 1 2
    by (metis (no_types, lifting) distinct.simps(2) list.sel(1) list.set_cases nless_le not_less_iff_gr_or_eq
        sorted_simps(2))
  show ?thesis using 2 3 strict_sorted_iff by blast
qed

(* ALERT: the assumption values are not well defined in isabelle *)
lemma "\<lbrakk>sortedStrict ([]); (1,2::real) < (hd ([]))\<rbrakk> \<Longrightarrow> sortedStrict [(1,2)]" by simp

value "sortedStrict(Nil)"

lemma append_last_sortedStrict:
  assumes "sortedStrict B" and "last (B :: R2 list) < (b :: R2)" and "B\<noteq>[]"
  shows   "sortedStrict (B@[b])"
proof-
  have 1: "sorted B" "distinct B" using assms strict_sorted_iff by auto
  have 2: "sorted (B@[b])" using assms(2) 1 sorry
  have 3: "distinct (B@[b])" using 1(2) assms(2,3)
  proof(induction B)
    case Nil
    then show ?case by simp
  next
    case (Cons a B)
    have 31: "distinct B" using Cons(2) by auto
    have 32: "B\<noteq>[] \<Longrightarrow> (last B = last (a#B))"
    proof(induction B)
      case Nil
      then show ?case by simp
    next
      case (Cons a B)
      then show ?case sorry
    qed
    then show ?case sorry
  qed
  show ?thesis using 2 3 strict_sorted_iff by blast
qed

lemma cap_endpoint_subset:
  assumes "l\<ge>2" 
    and   "Y = {Min (set xs) | xs. set xs \<subseteq> X \<and> sortedStrict xs \<and> cup (l - 1) (xs)}"
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

lemma min_conv_rec:
  assumes "k\<ge>3" and "l\<ge>3"
  shows "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1" 
  (is "?a \<le> ?b") using inf_upper
proof
  show "?b \<in> {n. \<forall>S . (card S = n \<and> general_pos S)
                \<longrightarrow> (\<exists>xs. (set xs \<subseteq> S \<and> sortedStrict xs) \<and> (cap k xs \<or> cup l xs))}"
  (is "?b \<in> {n. \<forall>S. ?GSET n S \<longrightarrow> (\<exists>xs. ?SS xs S \<and> ?CUPCAP k xs l)}")
  proof
    show "\<forall>S. card S = ?b \<and> general_pos S \<longrightarrow> (\<exists>xs. (set xs \<subseteq> S \<and> sortedStrict xs) \<and> (cap k xs \<or> cup l xs))"
    proof-
    {
      fix X
      assume asm: "?b = card X" "general_pos X"
      hence   A1: "?b \<le> card X" by simp
      define Y where ys: "Y = {Min (set xs) | xs. set xs \<subseteq> X \<and> sortedStrict xs \<and> cup (l - 1) (xs)}"
      hence ysx: "Y\<subseteq>X" using cap_endpoint_subset using asm assms by auto
      hence ygen: "general_pos Y" using asm(2) general_pos_subs by presburger
      
      have "\<exists>xs. ?SS xs X \<and> ?CUPCAP k xs l"
      proof(cases "\<exists>xs. ?SS xs X \<and> (cap k xs \<or> cup l xs)")
        case outerFalse:False
        then show ?thesis
        proof(cases "card (X-Y) \<ge> min_conv k (l-1)")
          case True
          have xy1: "general_pos (X-Y)" using general_pos_subs ysx asm(2) by blast
(* the following is not possible as X-Y can not have a (l-1) cup as their left points have been put in Y *)
          hence "\<exists>xs. set xs \<subseteq> (X-Y) \<and> sortedStrict xs \<and> cup (l-1) xs"
            using outerFalse True extract_cap_cup[of "k" "l-1" _ "X - Y"] min_conv_num_out
            by (smt (verit, best) Diff_subset dual_order.trans)
          then obtain lcs where lcs: "set lcs \<subseteq> (X-Y)" "sortedStrict lcs" "cup (l-1) lcs" by blast
          hence C1: "Min (set lcs) \<in> (X-Y)"
            by (smt (verit, ccfv_SIG) List.finite_set Min_in One_nat_def assms(2) cup_def diff_Suc_Suc diff_less_mono in_mono less_Suc_eq less_nat_zero_code list.size(3) numeral_3_eq_3 set_empty2)
          have  C2: "Min (set lcs) \<in> Y"
            using lcs(1,2,3) ys by blast
          show ?thesis using C1 C2 by simp
        next
          case False 
          hence 2:"min_conv (k) (l-1) \<ge> card (X - Y) + 1" by simp
          have    "card (X - Y) = card X - (card Y)" using ysx card_def 2 asm(1)
            by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.commute card.infinite card_Diff_subset diff_0_eq_0 diff_Suc_1 diff_is_0_eq double_diff finite_Diff le_antisym subset_refl trans_le_add2)
          hence   "card Y \<ge> min_conv (k-1) (l)" using 2 asm(1) by linarith
          hence 3:"\<exists>xs. set xs \<subseteq> Y \<and> sortedStrict xs \<and> (cap (k-1) xs)"
            using ygen outerFalse extract_cap_cup[of "k-1" "l" _ "Y"] ysx min_conv_num_out
            by (metis order_trans)

(*  Y gets a (k-1) cap, say kap, in this case. Since each point of Y is a starting point of an (l-1) cup,
    get the (l-1) cup starting at last point in kcs. Now, the union of these two contains either an l-cup or a k-cap.          
 *)

          then obtain kap where kap: "set kap \<subseteq> Y" "sortedStrict kap" "(cap (k-1) kap)" by blast
          (* get (l-1) cup in X starting at kap.last *)
          hence k1:"length kap = k-1" unfolding cap_def by auto
          hence k2:"kap!(k-2) \<in> Y" using kap
            by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD add_leE assms(1) lessI nth_mem numeral_3_eq_3 plus_1_eq_Suc subset_iff)
          then obtain lup where lup:"kap!(k-2) = Min (set lup)" "set lup \<subseteq> X" "sortedStrict lup" "cup (l - 1) (lup)" using ys by auto
          hence k3:"Min (set lup) = lup!0" using lup(1,3,4) assms(2)
            by (metis (no_types, lifting) List.finite_set One_nat_def Suc_diff_Suc
                Suc_le_lessD Suc_lessD Zero_neq_Suc card.empty cup_def nth_Cons_0
                numeral_3_eq_3 sorted_list_of_set.sorted_key_list_of_set_unique
                sorted_list_of_set_nonempty strict_sorted_equal)
          have k7:"lup!1 \<in> X" using lup(2,4) assms(2) cup_def
            by (metis One_nat_def Suc_le_eq less_diff_conv nth_mem numeral_3_eq_3
                plus_1_eq_Suc subsetD)
          have k4:"(kap!(k-3)) < (kap!(k-2))" using assms(1) kap(2,3) cap_def
            by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD add_leE lessI
                numeral_3_eq_3 plus_1_eq_Suc sorted_wrt_iff_nth_less)
          have k5:"(kap!(k-2)) < (lup!1)" using assms lup cup_def
            by (metis One_nat_def Suc_1 Suc_le_lessD add_diff_cancel_left' diff_less_mono
                k3 numeral_3_eq_3 numeral_One one_le_numeral plus_1_eq_Suc
                sorted_wrt_nth_less)
          hence k6:"sortedStrict [(kap!(k-3)),(kap!(k-2)),(lup!1)]" using k4 k5 by simp
          hence "\<not> collinear3 (kap!(k-3)) (kap!(k-2)) (lup!1)" 
            using k3 lup(1,2) kap(1) ysx asm(2) genpos_cross0[of "X"] collinear3_def strict_sorted_iff
            by (metis (no_types, lifting) ext One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD
                Suc_lessD add_diff_cancel_left' assms(1,2) cup_def diff_less_mono in_mono k1
                lessI lup(4) nth_mem numeral_3_eq_3 one_le_numeral plus_1_eq_Suc)
          thus ?thesis
          proof(cases "cap3 (kap!(k-3)) (kap!(k-2)) (lup!1)")
            case True
            hence k8:"cap k (kap@[lup!1])" using k6 kap(2,3) cap_def
            proof-
              have "rev ( (lup!1) # ( rev kap ) ) = (kap@[lup!1])" by force
              have "length (kap@[lup!1]) = k" using k1 k5
                using assms(1) by fastforce
              hence k29:"sortedStrict ( kap@[lup!1] )" 
                using k1 k3 lup(1) k5 kap(2) assms sorry
              thus ?thesis using k29 True sorry
            qed
            have "set kap \<subseteq> X" using kap(1) ysx by blast
            hence "set (kap@[lup!1]) \<subseteq> X" using k7 by force 
            then show ?thesis using k1 k6 assms(1) cap_def lup kap ysx order_trans k8 by blast
          next
            case False
            hence k9:"cup l (kap!(k-3)#lup)"
            proof-
              have "length (kap!(k-3)#lup) = l" using k4 lup(1) k3 lup(4) cup_def
                using assms(2) by auto
              hence "sortedStrict (kap!(k-3)#lup)" using k4 lup(1) k1 k3 kap(2) assms(2) k6 strict_sorted_iff
                by (metis (no_types, lifting) ext List.finite_set Min.coboundedI One_nat_def
                    Suc_le_lessD add_diff_cancel_left' cup_def diff_less_mono distinct.simps(2)
                    empty_set k6 le_add1 linorder_not_le lup(4) nth_mem numeral_3_eq_3
                    plus_1_eq_Suc sorted2 sorted_list_of_set.idem_if_sorted_distinct
                    sorted_list_of_set_nonempty strict_sorted_iff)
              show ?thesis using False sorry
            qed
            have "set (kap!(k-3)#lup) \<subseteq> X" 
              using kap(1) ysx assms(1) k1 lup(2) by force
            then show ?thesis using cup_def k9 
              by blast
          qed
        qed
      qed(blast)
    }  
    thus ?thesis by presburger  
  qed
qed
  thus ?thesis 
    by (smt (verit, ccfv_threshold) inf_upper ex_card general_pos_subs min_conv_def mem_Collect_eq order_trans)
qed

lemma min_conv_bin:
  shows "min_conv (k+3) (l+3) \<le> ((k + l + 2) choose (k + 1)) + 1"
proof(induction "k+l" arbitrary: l k)
  case (Suc x)
  then show ?case
  proof(cases "k = 0")
    case False
    have 1:"k\<ge>1" using False by simp
    show ?thesis
    proof(cases "l = 0")
      case True
      hence "min_conv (k + 3) (l + 3) = k + 3" using min_conv_arg_swap min_conv_base[of "k+3"] by simp
      moreover have "(k + l + 2 choose k + 1) + 1 = k + 3" using True binomial_Suc_n by simp
      ultimately show ?thesis using min_conv_base by simp
    next
      case False
      hence 2:"l\<ge>1" by simp
      have    "x = (k-1) + l" using 1 Suc by linarith
      hence 3:"min_conv (k + 2) (l + 3) \<le> (k + l + 1 choose k) + 1" using Suc by fastforce
      have    "x = k + (l-1)" using 2 Suc by linarith
      hence   "min_conv (k + 3) (l + 2) \<le> (k + l + 1 choose k + 1) + 1" using Suc by fastforce
      hence   "min_conv (k+3) (l+3) \<le> (k + l + 1 choose k) + (k + l + 1 choose k + 1) + 1"
        using 3 min_conv_rec[of "k+3" "l+3"] by simp
      then show ?thesis using binomial_Suc_Suc by simp
    qed
  qed(simp add: min_conv_base)
qed(simp add: min_conv_base)

end