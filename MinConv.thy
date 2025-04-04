theory MinConv
  imports EZ_bound

begin
lemma min_conv_arg_swap:
  "min_conv k l = min_conv l k"
  unfolding min_conv_def sorry

thm min_conv_base


(*
Suppose that X contains f(k − 1, l) + f(k,l − 1) − 1 points. Let Y be the set
of left endpoints of (k − 1)-cups of X. If X \ Y contains f(k − 1, l) points, then it
contains an l-cap. Otherwise, Y contains f(k,l−1) points. Suppose that Y contains
an (l −1)-cap {(xi1 , yi1 ),(xi2 , yi2 ),... ,(xil−1 , yil−1 )}. Let {(xj1 , yj1 ),(xj2 , yj2 ),... ,
(xjk−1 , yjk−1 )} be a (k − 1)-cup with il−1 = j1. A quick sketch then shows that
either (xil−2 , yil−2 ) can be added to the (k − 1)-cup to create a k-cup or (xj2 , yj2 )
can be added to the (l − 1)-cap to create an l-cap.
*)
lemma min_conv_rec:
  "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1"
proof-
  obtain X where xo: "general_pos X" "card X = min_conv (k - 1) l + min_conv k (l - 1) - 1" 
    using genpos_ex gpos_generalpos by blast
  define Y where yo: "Y = {Min xs | xs. xs \<subseteq> X \<and> cup (k-1) (sorted_list_of_set xs)}"
  have ysx: "Y\<subseteq>X" using xo yo sorry
  show ?thesis
  proof(cases "card (X-Y) \<ge> min_conv (k-1) l")
    case True
    then show ?thesis sorry (* show existence of l-cap in X\Y *)
  next
    case False
    hence "card Y \<ge> min_conv k (l-1)" using xo(2) ysx sorry 
    then show ?thesis sorry (* show existence of l-cap *)
  qed
qed

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