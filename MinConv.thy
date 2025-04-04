theory MinConv
  imports EZ_bound

begin
lemma min_conv_arg_swap:
  "min_conv k l = min_conv l k"
  unfolding min_conv_def sorry

thm min_conv_base

lemma min_conv_rec:
  "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1" sorry

thm binomial_Suc_Suc

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
      then show ?thesis using min_conv_base min_conv_arg_swap
        by (metis Suc_eq_plus1 add_0 add_2_eq_Suc' add_Suc_right binomial_Suc_n dual_order.refl numeral_3_eq_3)
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