theory SlopeCapCup
  imports Definitions Prelims Invariants

begin

(* slope properties *)

lemma slope_cross3:
  assumes "sdistinct [a,b,c]"
  shows   "cross3 a b c  = (fst b - fst a) * (fst c - fst b) * (slope b c - slope a b)"
proof-
  have 1:"fst a \<noteq> fst b" "fst b \<noteq> fst c" using assms(1) by simp+
  have "cross3 a b c = (fst b - fst a) * (snd c - snd b) - (fst c - fst b) * (snd b - snd a)" using cross3_def by blast
  also have "... = (fst b - fst a) * (fst c - fst b) * (slope b c - slope a b)" using 1 assms unfolding slope_def by (simp add: diff_frac_eq mult.commute)
  ultimately show ?thesis
    by presburger
qed

lemma cup3_slope:
  assumes "sdistinct [x,y,z]" "cup3 x y z"
  shows   "slope x y < slope y z"
  using assms
  by (smt (verit) cup3_def less_eq_prod_def mult_less_0_iff
      slope_cross3 sorted2 zero_less_mult_iff)

lemma cap3_slope:
  assumes "sdistinct [x,y,z]" "cap3 x y z"
  shows   "slope x y > slope y z"
  using assms
  by (smt (verit) cap3_def less_eq_prod_def mult_less_0_iff
      slope_cross3 sorted2 zero_less_mult_iff)

lemma slope_cup3:
  assumes "sdistinct [x,y,z]" "slope x y < slope y z"
  shows   "cup3 x y z" using slope_cross3 assms(1,2) cup3_def
  by (smt (verit, del_insts) distinct_length_2_or_more less_eq_prod_def list.simps(9) sorted2 zero_less_mult_iff)

lemma slope_cap3:
  assumes "sdistinct [x,y,z]" "slope x y > slope y z"
  shows   "cap3 x y z"
proof-
  have 1:"fst x \<noteq> fst y" "fst y \<noteq> fst z" using assms(1) by simp+
  have "0 > slope y z - slope x y" using assms(2) by simp
  hence "0 > (fst y - fst x) * (fst z - fst y) * (slope y z - slope x y)"
    by (metis "1"(1,2) assms(1) diff_gt_0_iff_gt less_eq_prod_def linorder_neqE_linordered_idom
        mult_less_cancel_right_disj mult_zero_left nle_le sorted2)
  thus ?thesis
    using 1 assms(2) cup3_def cross3_def[of "x" "y" "z"] slope_def[of "x" "y"] slope_def[of "y" "z"]
    by (smt (verit, best) cap3_def diff_frac_eq divide_cancel_right mult.commute
        nonzero_mult_div_cancel_left right_minus_eq)
qed

lemma slope_coll3:
  assumes "sdistinct [x,y,z]" "slope x y = slope y z"
  shows   "collinear3 x y z" using slope_cup3 slope_cap3 exactly_one_true
  by (smt (verit, del_insts) assms(1,2) collinear3_def cross3_def diff_frac_eq
      distinct_length_2_or_more divide_cancel_right list.simps(9) mult.commute mult_eq_0_iff
      slope_def)

lemma slopeinc_is_cup:
  assumes "sdistinct xs" "\<forall>x y z. subseq [x,y,z] xs \<longrightarrow> slope x y < slope y z"
  shows   "cup (length xs) xs"
proof-
  have "sublist [x, y, z] xs  \<longrightarrow> sdistinct[x, y, z]"
    using assms(1) sdistinct_subl by blast
  hence "sublist[x, y, z] xs \<longrightarrow> cup3 x y z" using slope_cup3 assms(2) by blast
  hence "list_check cup3 xs" using assms(1,2) bad3_from_bad sdistinct_subl slope_cup3
    by (metis sublist_imp_subseq)
  thus "cup (length xs) xs" using assms cup_def by simp
qed

lemma list_check_cup3_slope:
  assumes "sdistinct xs" "list_check cup3 xs"
  shows   "\<And>i. i < length xs - 2 \<longrightarrow> slope (xs!i) (xs!(i+1)) < slope (xs!(i+1)) (xs!(i+2))"
  using assms
proof(induction xs)
  case (Cons a xs)
  show ?case
  proof(cases "length (a#xs) \<ge> 3")
    case True
    have "sdistinct xs" using Cons(2) by simp
    also have "list_check cup3 xs" using Cons(3)
      using list_check.elims(3) by fastforce
    ultimately have 
      "\<And>i. i < length xs - 2 \<longrightarrow> 
      slope (xs ! i) (xs ! (i + 1)) < slope (xs ! (i + 1)) (xs ! (i + 2))" 
      using Cons(1) by simp
    hence 1:"\<And>i. i <length xs - 2 \<longrightarrow> 
      slope ((a#xs) ! (i+1)) ((a#xs) ! (i+2)) < slope ((a#xs) ! (i+2)) ((a#xs) ! (i + 3))" 
      by simp
    (* hence by change of vars j \<rightarrow> i+1 *)
    hence 2:"\<And>j i. j \<ge> 1 \<and> j < 1 + length (xs) - 2 \<and> j = i+1 \<longrightarrow> 
      slope ((a#xs) ! j) ((a#xs) ! (j + 1)) < slope ((a#xs) ! (j + 1)) ((a#xs) ! (j + 2))"
      by fastforce
    hence 3:"\<And>j. j \<ge> 1 \<and> j < length (a#xs) - 2 \<longrightarrow> 
      slope ((a#xs) ! j) ((a#xs) ! (j + 1)) < slope ((a#xs) ! (j + 1)) ((a#xs) ! (j + 2))"
      by (metis Suc_eq_plus1 length_Cons nat_le_iff_add
          plus_1_eq_Suc)
    hence 7:"sdistinct [(a#xs)!0, (a#xs)!1, (a#xs)!2]" using Cons(2) True ind_seq_subseq
      by (metis Suc_1 Suc_le_eq diff_Suc_1 diff_is_0_eq le_add2
          nless_le numeral_3_eq_3 plus_1_eq_Suc)
    hence "cup3 ((a#xs)!0) ((a#xs)!1) ((a#xs)!2)" using Cons(3)
      by (smt (verit, ccfv_SIG) One_nat_def Suc_1 Suc_eq_plus1
          True diff_Suc_1 diff_add_0 diff_is_0_eq list.size(3,4)
          list_check.elims(2) not_less_eq_eq nth_Cons_0
          nth_Cons_Suc numeral_3_eq_3) 
    hence "slope ((a#xs) ! 0) ((a#xs) ! (1)) < slope ((a#xs) ! (1)) ((a#xs) ! (2))"
      using Cons(3) cup3_slope 7 by simp

    then show ?thesis using 1 2 3
      by (metis One_nat_def Suc_eq_plus1 add_2_eq_Suc' bot_nat_0.extremum_unique
          length_Cons not_less_eq_eq nth_Cons_Suc plus_1_eq_Suc)
  qed(auto)
qed(simp)

lemma farey_prop1:
  fixes n1 n2 d1 d2 :: real
  assumes "d1 > 0" and "d2 > 0" and "n1 / d1 < n2 / d2"
  shows "n1 / d1 < (n1+n2) / (d1+d2)"
proof-
  have "n1 * d2 < d1 * n2" using assms
    by (smt (verit) divide_pos_pos frac_le_eq mult.commute mult_le_0_iff)
  hence "n1 * d2 + n1 * d1 < d1 * n2 + d1 * n1" by simp
  hence "n1 * (d1 + d2) < d1 * (n1 + n2)" by argo
  thus ?thesis
    by (smt (verit, best) assms(1,2) divide_pos_pos frac_le_eq mult.commute mult_le_0_iff)
qed

lemma farey_prop2:
  fixes n1 n2 d1 d2 :: real
  assumes "d1 > 0" and "d2 > 0" and "n1 / d1 < n2 / d2"
  shows "(n1+n2) / (d1+d2) < n2 / d2"
  by (smt (verit, best) assms(1,2,3) divide_minus_left farey_prop1)

lemma farey_pos_coeff:
  fixes \<beta> n1 n2 d1 d2 :: real
  assumes "\<beta> \<ge> 0" "d1 > 0" and "d2 > 0" and "n1 / d1 < n2 / d2"
  shows "n1 / d1 \<le> (n1 + \<beta>*n2) / (d1 + \<beta>*d2)" "(n1 + \<beta>*n2) / (d1 + \<beta>*d2) < n2/d2"
  using farey_prop1 farey_prop2 nle_le assms
  by (metis add.right_neutral mult_divide_mult_cancel_left_if mult_pos_pos
      mult_zero_left order.strict_iff_order)+

lemma farey_neg_coeff1:
  fixes \<beta> n1 n2 d1 d2 :: real
  assumes "0 < d1 + \<beta>*d2" "\<beta> < 0" "d1 > 0" and "d2 > 0" and "n1 / d1 < n2 / d2"
  shows "(n1 + \<beta>*n2) / (d1 + \<beta>*d2) < n1 / d1"
  sorry

lemma farey_neg_coeff2:
  fixes \<beta> n1 n2 d1 d2 :: real
  assumes "d1 + \<beta>*d2 < 0" "d1 > 0" and "d2 > 0" and "n1 / d1 < n2 / d2"
  shows "(n1 + \<beta>*n2) / (d1 + \<beta>*d2) > n2 / d2"
  sorry


(* need this prop for proof below *)
lemma slope_trans:
  assumes "sdistinct [a,b,c]" 
    and   "slope a b < slope b c"
  shows   "slope a b < slope a c" 
                      "slope a c < slope b c" 
  using assms farey_prop2 farey_prop1
  unfolding slope_def 
  by (smt (verit) distinct_length_2_or_more less_eq_prod_def list.simps(9) sorted2)+

lemma slope_trans_fwd:
  assumes "cup (length xs) xs" and "i+1 < j \<and> j < length xs"
  shows   "slope (xs!i) (xs!(j-1)) < slope (xs!(j-1)) (xs!j)"
  using assms(2)
proof(induction "j-i" arbitrary: j)
  case 0
  then show ?case by simp
next
  case (Suc x)
  hence F1:"x = (j-1) - i" by simp
  then show ?case
  proof(cases "i+3 \<le> j")
    case True
    hence F2:"i + 1 < (j-1) \<and> (j-1) < length xs" using Suc(3) by linarith
    hence F3:"slope (xs ! i) (xs ! (j - 2)) < slope (xs ! (j - 2)) (xs ! (j-1))" 
      using F1 Suc(1) by (metis Suc_1 diff_diff_left plus_1_eq_Suc)
    have "sdistinct [xs!i, xs!(j-2), xs!(j-1)]" using assms(1) F2 cup_def ind_seq_subseq
      by (metis (no_types, lifting) Suc_1 Suc_diff_Suc add_leE diff_diff_left less_diff_conv
          less_eq_Suc_le linorder_not_less plus_1_eq_Suc)
    hence F4:"slope (xs ! i) (xs ! (j - 1)) < slope (xs ! (j - 2)) (xs ! (j-1))"
      using slope_trans F3 by blast
    moreover have "...  <  slope (xs ! (j - 1)) (xs ! j)"
      by (smt (verit, ccfv_threshold) Suc.prems Suc_eq_plus1
          add_2_eq_Suc' assms(1) cup_def diff_Suc_1 diff_is_0_eq
          less_diff_conv less_natE list_check_cup3_slope nless_le
          plus_1_eq_Suc verit_comp_simplify1(3))
    finally show ?thesis by simp
  next
    case False
    then show ?thesis
      using Suc.prems assms(1) cup_def list_check_cup3_slope
      by (smt (verit, ccfv_SIG) Suc_1 add.commute add_Suc_right diff_zero less_Suc_eq 
          less_diff_conv not_less_eq numeral_3_eq_3 plus_1_eq_Suc verit_comp_simplify1(3))
  qed
qed

lemma slope_trans_bkd:
  assumes "cup (length xs) xs" and "j+1 < k \<and> k < length xs"
  shows   "slope (xs!j) (xs!(j+1)) < slope (xs!j) (xs!k)"
  using assms(2)
proof(induction "k-j" arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc x)
  hence F1:"x = (k-1) - j" by simp
  then show ?case
  proof(cases "j+3 \<le> k")
    case True
    hence F2:"j + 1 < (k-1) \<and> (k-1) < length xs" using Suc(3) by linarith
    have F4:"sdistinct [xs!j, xs!(k-1), xs!k]" 
      using assms(1) F2 cup_def ind_seq_subseq
      by (metis (no_types, opaque_lifting) Suc.prems Suc_pred' nless_le
          bot_nat_0.extremum_strict less_diff_conv not_less_eq_eq lessI)
    hence F3:"slope (xs ! j) (xs ! (j + 1)) < slope (xs ! j) (xs ! (k-1))"
      using F1 F2 by (metis diff_diff_left plus_1_eq_Suc Suc(1))
    have F5:"slope (xs ! j) (xs ! (k-1)) < slope (xs!(k-1)) (xs!(k))"
      using Suc.prems assms(1) slope_trans_fwd by blast
    thus ?thesis using F3 F4 slope_trans(1)
      by (meson dual_order.strict_trans)
  next
    case False
    hence "j+2 = k"
      using Suc.prems by linarith
    then show ?thesis
      using Suc.prems assms(1) cup_def slope_trans(1) slope_trans_fwd
      by (smt (verit, ccfv_threshold) Suc_1 add_Suc add_Suc_shift diff_Suc_numeral
          diff_zero ind_seq_subseq less_add_one numeral_One pred_numeral_simps(1))
  qed
qed


theorem cup_is_slopeinc:
  assumes "cup (length xs) xs" and "i < j \<and> j < k \<and> k < length xs"
  shows   "slope (xs!i) (xs!j) < slope (xs!j) (xs!k)"
proof-
  have 1:"0 < j" "j+1 < length xs" using assms(2) by simp+
  hence 2:"slope (xs!(j-1)) (xs!j) < slope (xs!j) (xs!(j+1))"
    by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1 add.commute assms(1) diff_add_inverse less_add_one plus_nat.add_0 slope_trans_fwd)
  have 3:"i+1 < j \<Longrightarrow> slope (xs!i) (xs!(j-1)) < slope (xs!(j-1)) (xs!j)" 
    using assms slope_trans_fwd by simp
  have 4:"i+1 = j \<Longrightarrow> ?thesis" using "2" assms slope_trans_bkd
    by (smt (verit, ccfv_threshold) Suc_eq_plus1 Suc_lessI add_diff_cancel_right')
  have 5:"j+1 < k \<Longrightarrow> slope (xs!j) (xs!(j+1)) < slope (xs!j) (xs!k)" 
    using assms slope_trans_bkd by simp
  have   "j+1 = k \<Longrightarrow> ?thesis"
    using assms(1,2) slope_trans_fwd by fastforce
  thus ?thesis using 3 4 5 slope_trans_fwd assms Suc_eq_plus1
    by (smt (verit, best) add_diff_cancel_right' less_trans_Suc linorder_neqE_nat not_less_eq)
qed

corollary cup_is_slopeinc_subseq:
  assumes "cup (length xs) xs" and "subseq [a,b,c] xs"
  shows   "slope a b < slope b c"
  using subseq_index3 cup_is_slopeinc
  by (metis assms(1,2))

lemma cup_sub_cup:
  assumes "cup (length xs) xs" and "subseq ys xs"
  shows   "cup (length ys) ys"
proof-
  have 1:"sdistinct ys" using sdistinct_subseq assms cup_def by simp
  have "\<And>a b c. sublist [a,b,c] ys \<Longrightarrow> slope a b < slope b c"
  proof-
    fix a b c 
    assume "sublist [a,b,c] ys"
    hence  "subseq [a,b,c] xs"
      using assms(2) subseq_order.dual_order.trans by blast
    thus "slope a b < slope b c" using assms(1) cup_is_slopeinc subseq_index3
      by metis
  qed
  thus ?thesis using 1 slopeinc_is_cup get_cap_from_bad_cup sdistinct_subl slope_cup3
    by meson
qed

(* 
-- not needed till min_conv_binomial equality --

theorem cap_is_slopedec:
  assumes "cap (length xs) xs" 
      and "i < j \<and> j < k \<and> k < length xs"
    shows "slope (xs!i) (xs!j) > slope (xs!j) (xs!k)"
  (* proof same as cup_is_slopeinc with similar prerequisite lemmas by cap \<longleftrightarrow> cup *)
  sorry
 *)

lemma slopedec_is_cap:
  assumes "sdistinct xs" 
      and "\<forall>x y z. subseq [x,y,z] xs \<longrightarrow> slope x y > slope y z"
    shows   "cap (length xs) xs"
  using assms
  by (metis get_cup_from_bad_cap sdistinct_subl slope_cap3 sublist_imp_subseq)


lemma cap_sub_cap:
  assumes "cap (length xs) xs" and "subseq ys xs"
  shows   "cap (length ys) ys"
  by (metis assms(1,2) cap_orig_refl_rev cup_sub_cup length_neg length_rev subseq_map subseq_rev)

end


