theory Cups_to_Convex
imports Main EZ_bound
begin

lemma points_sorted_xsorted:
  assumes "sorted_wrt (<) (ps::(real \<times> real) list)" 
  shows "sorted (map fst ps)"
  using assms
  by (smt (verit, best) length_map less_eq_prod_def nth_map order_le_less_trans sorted_iff_nth_mono strict_sorted_imp_sorted)

value "cup3 (-1,1) (-0.5,-0.5) (0,-1)"
value "cup3 (-0.5,-0.5) (0,-1) (0,0)"
value "cup3 (-1,1) (-0.5,-0.5) (0,-1)"

value "cap3 (-1,-1) (-1,0) (0,0)"
value "cap3 (-1,0) (0,0) (1,-1)"
value "cap3 (-1,-1) (0,0) (1,-1)"
value "cap3 (-1,-1) (-1,0) (1,-1)"

value "cap3 (-1,-1) (-0.5,0) (0,0)"
value "cap3 (-0.5,0) (0,0) (1,-1)"
value "cap3 (-1,-1) (0,0) (1,-1)"
value "cap3 (-1,-1) (-0.5,0) (1,-1)"

lemma cap_step1:
  assumes "cap3 p1 p2 p3" "cap3 p2 p3 p4" "sorted_wrt (<) [p1,p2,p3,p4]"
  shows "(fst p1 < fst p2 \<and> fst p2 < fst p3 \<and> fst p3 < fst p4) \<or>
         (fst p1 = fst p2 \<and> fst p2 < fst p3 \<and> fst p3 < fst p4) \<or>
         (fst p1 < fst p2 \<and> fst p2 = fst p3 \<and> fst p3 < fst p4) \<or>
         (fst p1 < fst p2 \<and> fst p2 < fst p3 \<and> fst p3 = fst p4)"
  using assms unfolding cap3_def cross3_def 
  by (smt (verit, best) less_eq_prod_def mult_left_mono sorted2 strict_sorted_imp_sorted)

lemma cap_step2:
  assumes "cap3 p1 p2 p3" "cap3 p2 p3 p4" "(fst p1 = fst p2 \<and> fst p2 < fst p3 \<and> fst p3 < fst p4)"
  shows "cap3 p1 p3 p4"
  by (smt (verit) assms(1) assms(2) assms(3) cap3_def cross3_def mult_diff_mult mult_left_mono)

lemma cap_step3:
  assumes "cap3 p1 p2 p3" "cap3 p2 p3 p4" "(fst p1 < fst p2 \<and> fst p2 = fst p3 \<and> fst p3 < fst p4)"
  shows "cap3 p1 p3 p4"
  by (smt (verit) assms(1) assms(2) assms(3) cap3_def cross3_def mult_diff_mult mult_less_cancel_right_disj)

lemma cap_step4:
  assumes "cap3 p1 p2 p3" "cap3 p2 p3 p4" "(fst p1 < fst p2 \<and> fst p2 < fst p3 \<and> fst p3 = fst p4)"
  shows "cap3 p1 p3 p4"
  using assms(2) assms(3) cap3_def cross3_def by auto

lemma cap_step5:
  assumes "cap3 p1 p2 p3" "cap3 p2 p3 p4" "(fst p1 < fst p2 \<and> fst p2 < fst p3 \<and> fst p3 < fst p4)"
  shows "cap3 p1 p3 p4" 
proof- 
  have "(snd p2 - snd p1)/(fst p2 - fst p1) > (snd p3 - snd p1)/(fst p3 - fst p1)"
    by (smt (verit, del_insts) assms(1) assms(3) cap3_def cross3_def divide_neg_pos frac_less_eq mult.commute zero_less_mult_iff) 
  moreover have "(snd p3 - snd p2)/(fst p3 - fst p2) > (snd p4 - snd p2)/(fst p4 - fst p2)"
    by (smt (verit) assms(2) assms(3) cap3_def cross3_def divide_neg_pos frac_less_eq mult.commute zero_less_mult_iff)
  ultimately have "(snd p3 - snd p1)/(fst p3 - fst p1) > (snd p4 - snd p1)/(fst p4 - fst p1)"
    

lemma cross_sum: 
  assumes "sorted_wrt (<) [p1,p2,p3,p4]" "cross3 p1 p3 p2 > 0" "cross3 p2 p4 p3 > 0"
  shows "cross3 p1 p4 p3 > 0"

  
  

lemma cap_step1:
  assumes "cup3 p1 p2 p3" "cup3 p2 p3 p4" "sorted_wrt (<) [p1,p2,p3,p4]"
  shows "cup3 p1 p3 p4"
  using assms unfolding cap3_def cross3_def 
proof-
  have xsorted: "fst p1 \<le> fst p2 \<and> fst p2 \<le> fst p3 \<and> fst p3 \<le> fst p4"
    using points_sorted_xsorted[OF assms(3)] by simp
  have "(fst p4 - fst p1)*(snd p3 - snd p1) < (fst p3 - fst p1)*(snd p4 - snd p1)"
  proof-
    have "(fst p4 - fst p1)*(snd p3 - snd p1) - (fst p3 - fst p1)*(snd p4 - snd p1) = 
          (fst p4 - fst p2)*(snd p3 - snd p1) + (fst p2 - fst p1)*(snd p3 - snd p1) 
          - (fst p3 - fst p1)*(snd p4 - snd p1)"
      by argo
    moreover have "... = (fst p4 - fst p2)*(snd p3 - snd p1) + (fst p2 - fst p1)*(snd p3 - snd p1) 
          - (fst p3 - fst p2)*(snd p4 - snd p1) - (fst p2 - fst p1)*(snd p4 - snd p1)"
      by argo
    moreover have "... = (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p4 - fst p2)*(snd p3 - snd p1) -
          (fst p3 - fst p2)*(snd p4 - snd p1)"
      by argo
    moreover have  "... = (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p4 - fst p2)*(snd p3 - snd p2)
          + (fst p4 - fst p2)*(snd p2 - snd p1)  -(fst p3 - fst p2)*(snd p4 - snd p1)"
      by argo
    moreover have  "... < (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p3 - fst p2)*(snd p4 - snd p2)
          + (fst p4 - fst p2)*(snd p2 - snd p1)  -(fst p3 - fst p2)*(snd p4 - snd p1)"
      using assms(2) cross3_def cup3_def by auto
    moreover have "... = (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p3 - fst p2)*(snd p1 - snd p2)
          + (fst p4 - fst p2)*(snd p2 - snd p1)"
      by argo
    
    
    
    
    have 1: "(fst p4 * snd p3) - (fst p4 * snd p2) - (fst p2 * snd p3) + (fst p2 * snd p2) <
          (fst p3 * snd p4) - fst p3 * snd p2 - fst p2 * snd p4 + fst p2 * snd p2" 
      by (smt (verit, ccfv_SIG) assms(2) cross3_def cup3_def mult_diff_mult)
    have 2: "(fst p3 * snd p2) - (fst p3 * snd p1) - (fst p1 * snd p2) + (fst p1 * snd p1) <
          (fst p2 * snd p3) - (fst p2 * snd p1) - (fst p1 * snd p3) + (fst p1 * snd p1)"
      by (smt (verit, ccfv_SIG) assms(1) cross3_def cup3_def mult_diff_mult)
    have 3: "(fst p4 - fst p1)*(snd p3 - snd p1) - (fst p3 - fst p1)*(snd p4 - snd p1) = 
          (fst p4 - fst p2)*(snd p3 - snd p1) + (fst p2 - fst p1)*(snd p3 - snd p1) 
          - (fst p3 - fst p1)*(snd p4 - snd p1)"
      by argo
    have 4: "... = (fst p4 - fst p2)*(snd p3 - snd p1) + (fst p2 - fst p1)*(snd p3 - snd p1) 
          - (fst p3 - fst p2)*(snd p4 - snd p1) - (fst p2 - fst p1)*(snd p4 - snd p1)"
      by argo
    have "... = (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p4 - fst p2)*(snd p3 - snd p1) -
          (fst p3 - fst p2)*(snd p4 - snd p1)"
      by argo
    have  "... = (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p4 - fst p2)*(snd p3 - snd p2)
          + (fst p4 - fst p2)*(snd p2 - snd p1)  -(fst p3 - fst p2)*(snd p4 - snd p1)"
      by argo
    have  "... < (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p3 - fst p2)*(snd p4 - snd p2)
          + (fst p4 - fst p2)*(snd p2 - snd p1)  -(fst p3 - fst p2)*(snd p4 - snd p1)"
      using assms(2) cross3_def cup3_def by auto
    have "... = (fst p2 - fst p1)*(snd p3 - snd p4) + (fst p3 - fst p2)*(snd p1 - snd p2)
          + (fst p4 - fst p2)*(snd p2 - snd p1)"
      by argo
    
          
    show ?thesis
      using xsorted 1 2 
      
(fst p3 - fst p2)*(snd p4 - snd p1) - (fst p3 - fst p2)*(snd p4 - snd p1)


lemma cap_step1:
  assumes "cap3 p1 p2 p3" "cap3 p2 p3 p4" "sorted (p1#p2#p3#p4#[])"
  shows "cap3 p1 p3 p4"
  (*using assms points_sorted_xsorted[OF assms(3)]
  unfolding cap3_def cross3_def*)
proof-
  have xsorted: "fst p1 \<le> fst p2 \<and> fst p1 \<le> fst p3 \<and> fst p1 \<le> fst p4 \<and> fst p2 \<le> fst p3 \<and> fst p2 \<le> 
    fst p4 \<and> fst p3 \<le> fst p4" using points_sorted_xsorted[OF assms(3)] by force
  have ysorted: "snd p2 > snd p3 \<and> snd p3 > snd p4" sledgehammer
  have "(fst p3 - fst p1)*(snd p4 - snd p1) > (fst p4 - fst p1)*(snd p3 - snd p1)"
  proof- 
    have "(fst p3 * snd p4) - (fst p3 * snd p2) - (fst p2 * snd p4) + (fst p2 * snd p2) < 
          (fst p4 * snd p3) - fst p4 * snd p2 - fst p2 * snd p3 + fst p2 * snd p2" 
      using assms(2)
      unfolding cap3_def cross3_def 
      by argo
    have 


lemma cap_step2:
  assumes "cap3 p1 p2 p3" "cap3 p1 p3 p4" "sorted (p1#p2#p3#p4#[])"
  shows "cap3 p1 p2 p4"
  sorry



  

lemma assumes "distinct ys" "sorted ys" "4 = length ys" "set ys \<subseteq> set xs" "cap n xs" 
  shows "cap 4 ys"
proof- 
  have "list_check cap3 ys" by try0 

(*the following lemma proves that if a list of points is an n-cap, then they are 
convex position, that is form the corner points of a convex hull*)
lemma fixes n
  assumes "cap n xs"
  shows "convex_pos (set xs)"
proof(induction xs)
  case Nil
  then show ?case unfolding convex_pos_def by simp
next
  case (Cons a xs)
  then show ?case sorry
qed

(*following lemma is needed for proving the bound*)
lemma fixes n
  shows "((2*n - 4) choose (n - 2)) + 1 \<le> 4^n"
proof(induction n)
  case 0
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed

end
