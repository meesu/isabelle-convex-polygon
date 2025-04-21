theory MinConv
imports EZ_bound

begin

abbreviation
  "reflect \<equiv> (\<lambda> p. -(p :: R2))" 

lemma gpos_neg:
  assumes "gpos S"
  shows   "gpos (reflect ` S)"
proof-
  {
    fix a b c
    assume asm: "a\<in>S" "b\<in>S" "c\<in>S" "distinct [a,b,c]"
    hence 1:"\<not> collinear3 (a) (b) (c)"    using gpos_def assms asm by simp
    have  2:  "distinct [-a, -b, -c]"     using asm by simp
    have  3:"\<not>collinear3 (-a) (-b) (-c)"  using 1 unfolding collinear3_def cross3_def
      by (simp add: mult.commute vector_space_over_itself.scale_right_diff_distrib)
    have "distinct [-a, -b, -c] \<longrightarrow> \<not>collinear3 (-a) (-b) (-c)" using 2 3 by simp
  }
  thus ?thesis unfolding gpos_def by simp
qed

corollary general_pos_neg:
  "general_pos S \<longrightarrow> general_pos (reflect ` S)" 
  using gpos_generalpos gpos_neg  by blast

corollary general_pos_neg_neg:
  "general_pos (reflect ` S) \<longrightarrow> general_pos S" using general_pos_neg  
  by (metis (no_types, opaque_lifting) general_pos_subs minus_equation_iff
    rev_image_eqI subset_eq)

lemma card_neg:
  "(card S = n) = (card (reflect ` (S :: R2 set)) = n)" using card_def
  by (simp add: card_image)

lemma neg_neg:
  "reflect \<circ> reflect = id" by simp

lemma rev_reflect:
  "rev \<circ> (map reflect) = (map reflect) \<circ> rev"
   by (simp add: comp_def rev_map)

lemma rev_reflect_inv:
  "(rev \<circ> (map reflect)) \<circ> (rev \<circ> (map reflect)) = (id :: R2 list \<Rightarrow> R2 list)"
  using rev_reflect neg_neg
  by (metis List.map.comp comp_assoc comp_id list.map_id0 rev_involution)

lemma implm_rev_reflect_inv:"rev (map reflect (rev (map reflect xs))) = xs"
proof(induction xs)
  case (Cons a xs)
  have "rev (map reflect (a # xs)) = (rev (map reflect xs))@[reflect a]"
    by simp
  also have "map reflect ((rev (map reflect xs))@[reflect a])
         = (map reflect (rev (map reflect xs)))@ [a]"
    by simp
  also have "rev ((map reflect (rev (map reflect xs)))@[a]) = [a]@(rev (map reflect (rev (map reflect xs))))"
    by simp
  ultimately show ?case using Cons by simp
qed(simp)
lemma distinct_neg:
"distinct xs = distinct (rev (map reflect (xs :: R2 list)))"
by (simp add: distinct_map)

lemma sorted_neg:
  "sorted xs = sorted (rev (map reflect (xs :: R2 list)))"
  (is "?P xs = ?Q xs")
proof
  assume asm:"?P xs"
  hence 1:"sorted_wrt (\<ge>) (rev xs)"
    by (simp add: sorted_wrt_rev)
  have Fact:"\<forall>x y. x \<le> y \<longrightarrow> reflect x \<ge> reflect y" by simp
  hence 2:"sorted_wrt (\<ge>) (map reflect xs)"
    by (metis asm sorted_wrt_map_mono)
  thus "?Q xs" using asm 1 sorted_wrt_rev
    by blast
next
  have Fact:"\<forall>x y. reflect x \<ge> reflect y \<longrightarrow> x \<le> y " by simp
  assume asm:"?Q xs"
  thus "?P xs" using sorted_wrt_rev sorted_wrt_map_mono Fact
    by (smt (verit, ccfv_SIG) sorted_wrt_map sorted_wrt_mono_rel)
qed

lemma sortedstrict_neg:
  "sortedStrict xs = sortedStrict (rev (map reflect (xs :: R2 list)))" 
  using distinct_neg sorted_neg strict_sorted_iff by blast

lemma orig_refl_rev:
  "cap3 x y z = cup3 (-z) (-y) (-x)"
  unfolding cap3_def cup3_def cross3_def by fastforce

lemma list_cap_tail: 
  assumes "list_check cap3 (xs@[c,b])"
    and "cross3  c b a < 0"
  shows "list_check cap3 (xs@[c,b,a])"
  using assms
proof(induction xs)
  case Nil
  hence "distinct [c,b,a]" using cross3_def 
    using cross3_non0_distinct not_less_iff_gr_or_eq by blast
  hence "list_check cap3 [b,a]" unfolding list_check.simps(3) by simp
  then show ?case using list_check.simps(4)[of "cap3" c b a "[]"] unfolding cap3_def
    by (metis append_Nil assms(2))
next
  case (Cons x xs)
  hence Cons1:" list_check cap3 ((x # xs) @ [c, b])" by argo
  have cross3: "cross3 c b a < 0" using Cons by argo
  have "list_check cap3 (xs@[c,b])" using Cons(2) list_check.simps 
    using list_check.elims(3) by fastforce 
  hence s1:"list_check cap3 (xs@[c,b,a])" using Cons by argo
  then show ?case
  proof(cases xs)
    case Nil
    hence "cross3 x c b < 0" using Cons(2) list_check.simps(4)[of cap3 x c b "[]"]
      unfolding cap3_def 
      by (metis (no_types, lifting) append_eq_Cons_conv) 
    then show ?thesis using Nil list_check.simps(4) 
      by (metis s1 append_Cons append_Nil cap3_def) 
  next
    case (Cons y ys)
    hence xs_is:"xs = y#ys" by argo
    then show ?thesis 
    proof(cases ys)
      case Nil
      hence "cap3 x y c" using Cons Cons1 by simp
      then show ?thesis using Cons Cons1 cross3 unfolding cap3_def 
        by (metis \<open>list_check cap3 (xs @ [c, b, a])\<close> append_Cons append_Nil
            list_check.simps(3,4) local.Nil) 
    next
      case (Cons z zs)
      hence "cap3 x y z" using xs_is Cons Cons1 by simp
      then show ?thesis using xs_is Cons s1 by auto
    qed
  qed
qed

lemma list_cup_tail: 
  assumes "list_check cup3 (xs@[c,b])"
    and "cross3  c b a > 0"
  shows "list_check cup3 (xs@[c,b,a])"
  using assms
proof(induction xs)
  case Nil
  hence "distinct [c,b,a]" using cross3_def 
    using cross3_non0_distinct not_less_iff_gr_or_eq 
    by (metis assms(2)) 
  hence "list_check cup3 [b,a]" unfolding list_check.simps(3) by simp
  then show ?case using list_check.simps(4)[of "cup3" c b a "[]"] unfolding cup3_def
    by (metis append.left_neutral assms(2))
next
  case (Cons x xs)
  hence Cons1:" list_check cup3 ((x # xs) @ [c, b])"  by argo
  have cross3: "cross3 c b a > 0" using Cons by argo
  have "list_check cup3 (xs@[c,b])" using Cons(2) list_check.simps 
    using list_check.elims(3) by fastforce 
  hence s1:"list_check cup3 (xs@[c,b,a])" using Cons by argo
  then show ?case
  proof(cases xs)
    case Nil
    hence "cross3 x c b > 0" using Cons(2) list_check.simps(4)[of cup3 x c b "[]"]
      unfolding cup3_def 
      by (metis (no_types, lifting) append_eq_Cons_conv) 
    then show ?thesis using Nil list_check.simps(4) 
      by (metis s1 append_Cons append_Nil cup3_def) 
  next
    case (Cons y ys)
    hence xs_is:"xs = y#ys" by argo
    then show ?thesis 
    proof(cases ys)
      case Nil
      hence "cup3 x y c" using Cons Cons1 by simp
      then show ?thesis using Cons Cons1 cross3 unfolding cap3_def 
        by (metis s1 append_Cons append_Nil list_check.simps(4) local.Nil) 
    next
      case (Cons z zs)
      hence "cup3 x y z" using xs_is Cons Cons1 by simp
      then show ?thesis using xs_is Cons s1 by auto
    qed
  qed
qed

lemma list_check_cup3_imp_cap3:
  assumes "list_check cup3 xs"
  shows "list_check cap3 (rev (map reflect xs))" using assms
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have lcc:"list_check cup3 (a # xs)" using Cons by argo
  then show ?case
  proof(cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b ys)
    hence b_ys: "xs = b#ys" by argo
    then show ?thesis
    proof(cases ys)
      case Nil
      have "a \<noteq> b" using  lcc unfolding Nil Cons lcc list_check.simps .
      then show ?thesis unfolding Nil Cons lcc list_check.simps by simp
    next
      case (Cons c zs)
      have 1:"(rev (map reflect (a # b # c # zs))) 
                = (rev (map reflect zs))@([reflect c, reflect b, reflect a])"
        by simp
      have "cross3 a b c > 0" using lcc unfolding Cons b_ys lcc 
        by (meson cup3_def list_check.simps(4)) 
      hence "cross3 (reflect c) (reflect b) (reflect a) < 0" 
        by (simp add: cross3_def)  

      then show ?thesis unfolding lcc  implm_rev_reflect_inv 
        unfolding b_ys   Cons using 
          list_cap_tail[of "(rev (map reflect zs))" "reflect c" "reflect b" "reflect a"]
             1 
        by (metis Cons.IH Cons.prems Cons_eq_append_conv b_ys list.simps(9) list_check.simps(4)
            local.Cons rev.simps(2) rev_append rev_swap)   
    qed
  qed
qed


lemma list_check_cap3_imp_cup3:
  assumes "list_check cap3 xs"
  shows "list_check cup3 (rev (map reflect xs))" using assms
 using assms
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have lcc:"list_check cap3 (a # xs)" using Cons by argo
  then show ?case
  proof(cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b ys)
    hence b_ys: "xs = b#ys" by argo
    then show ?thesis
    proof(cases ys)
      case Nil
      have "a \<noteq> b" using  lcc unfolding Nil Cons lcc list_check.simps .
      then show ?thesis unfolding Nil Cons lcc list_check.simps by simp
    next
      case (Cons c zs)
      have 1:"(rev (map reflect (a # b # c # zs))) 
                = (rev (map reflect zs))@([reflect c, reflect b, reflect a])"
        by simp
      have "cross3 a b c < 0" using lcc unfolding Cons b_ys lcc 
        by (meson cap3_def list_check.simps(4))
      hence "cross3 (reflect c) (reflect b) (reflect a) > 0" 
        by (simp add: cross3_def)  
      then show ?thesis unfolding lcc  implm_rev_reflect_inv 
        unfolding b_ys   Cons using 
          list_cap_tail[of "(rev (map reflect zs))" "reflect c" "reflect b" "reflect a"]
             1 
        by (smt (verit, ccfv_threshold) Cons.IH Cons.prems(1) append.assoc append_Cons append_Nil
            b_ys list.simps(9) list_check.simps(4) list_cup_tail local.Cons rev.simps(2))
    qed
  qed
qed

lemma cap_orig_refl_rev:
  "cap k xs = cup k (rev (map reflect (xs::R2 list)))"
proof(induction xs arbitrary: k)
  case Nil
  then show ?case unfolding cap_def cup_def 
    by simp
next
  case (Cons a xs)
  { assume asm:"cap k (a # xs)"
    hence "sortedStrict (a#xs)" unfolding cap_def by argo
    hence 1:"sortedStrict (rev (map reflect (a # xs)))" using sortedstrict_neg by fast
    have 2:"length (rev (map reflect (a # xs))) = k" using asm unfolding cap_def
      by auto
    also have "list_check cap3 (a#xs)" using asm unfolding cap_def by argo
    hence "list_check cup3 (rev (map reflect (a#xs)))" 
      using list_check_cap3_imp_cup3 by blast
    hence "cup k  (rev (map reflect (a#xs)))" 
      using 1 2 asm unfolding cup_def cap_def by argo} note rs = this
  then have s1:"cap k (a#xs) \<longrightarrow> cup k (rev (map reflect (a#xs)))" by argo
  have "cup k (rev (map reflect (a#xs))) \<longrightarrow> (cap k  (a#xs))"
  proof
    assume asm:"cup k (rev (map reflect (a#xs)))"
    hence "sortedStrict (rev (map reflect (a#xs)))" unfolding cup_def by argo
    hence 1:"sortedStrict (a # xs)" using sortedstrict_neg by fast
    have 2:"length (a # xs) = k" using asm unfolding cup_def
      by auto
    also have 3:"list_check cup3 (rev (map reflect (a#xs)))"
      using asm unfolding cup_def by argo
    hence "list_check cap3  (a#xs)" 
    proof-
      have "list_check cap3 (rev (map reflect (rev (map reflect (a#xs)))))"
        using list_check_cup3_imp_cap3[OF 3] .
      also have "(rev (map reflect (rev (map reflect (a#xs))))) = a#xs"
        using implm_rev_reflect_inv[of "a#xs"] .
      ultimately show ?thesis by argo
    qed
    thus "cap k  (a#xs)" 
      using 1 2 asm unfolding cup_def cap_def by argo 
  qed
  then show ?case using s1 by argo
qed

(*
{n :: nat. (\<forall>S . (card S \<ge> n \<and> general_pos S)
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs)))
*)
lemma min_conv_sets_eq:
  assumes rmr:"rmr \<equiv> (\<lambda> xs. (rev (map reflect xs)))"
    shows "{n :: nat. (\<forall>S :: R2 set . (card S \<ge> n \<and> general_pos S)
                  \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs)))}
         = {n :: nat. (\<forall>S :: R2 set . (card S \<ge> n \<and> general_pos S)
                  \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap l xs \<or> cup k xs)))}"
 (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix x 
    assume x_in:"x \<in> ?P"
    have "\<forall>S :: R2 set. (card (S) \<ge> x \<and> general_pos (S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> (reflect ` S) \<and> (sortedStrict xs) \<and> (cap l xs \<or> cup k xs))"
      by (smt (verit, best) cap_def cap_orig_refl_rev cup_def general_pos_neg_neg id_apply image_mono image_set mem_Collect_eq o_def rev_reflect_inv set_rev x_in)
    hence "\<forall>S :: R2 set. (card S \<ge> x \<and> general_pos S)
                 \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap l xs \<or> cup k xs))" 
      using card_neg general_pos_neg neg_neg
      by (metis id_apply image_comp image_id) (* takes long *)
    thus "x \<in> ?Q" by blast
  qed
next
  show "?Q \<subseteq> ?P"
  proof
    fix x
    assume x_in:"x \<in> ?Q"
    have "\<forall>S :: R2 set. (card (S) \<ge> x \<and> general_pos (S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> (reflect ` S) \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs))"
      by (smt (verit, best) cap_def cap_orig_refl_rev cup_def general_pos_neg_neg id_apply image_mono image_set mem_Collect_eq o_def rev_reflect_inv set_rev x_in)
    hence "\<forall>S :: R2 set. (card S \<ge> x \<and> general_pos S)
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs))" 
      using card_neg general_pos_neg neg_neg
      by (metis id_apply image_comp image_id) (* takes long *)    
    thus "x \<in> ?P" by blast
  qed
qed

lemma min_conv_arg_swap: "min_conv k l = min_conv l k"
  unfolding min_conv_def using min_conv_sets_eq by simp
  
lemma extend_cap_cup:
  assumes "sortedStrict (B@[b])" and "list_check cc (B :: R2 list)" and "cc (B!(length B-2)) (B!(length B-1)) b"
  shows   "list_check cc (B@[b])"
using assms
proof(induction B)
  case (Cons a B)
  show ?case
  proof(cases "length B = 0")
    case True
    then show ?thesis using Cons(2) by simp
  next
    case cF:False
    then show ?thesis
    proof(cases "length B = 1")
      case True
      then obtain x where "B = [x]"
        by (metis One_nat_def Suc_length_conv length_0_conv)
      then show ?thesis using Cons(2) True 
        using Cons.prems(3) by auto
    next
      case False
      then have blen: "length B \<ge> 2" using cF by linarith
      have 1:"sortedStrict (B @ [b])" using Cons by simp
      have 2:"list_check cc B" using Cons
        by (smt (verit) list_check.elims(1) list_check.simps(4))
      have 3:"cc (B ! (length B - 2)) (B ! (length B - 1)) b" using blen Cons.prems
        by (metis Suc_1 cF diff_Suc_1 diff_Suc_eq_diff_pred length_Cons less_eq_Suc_le nth_Cons' order_less_irrefl
            zero_less_diff)
      have 4:"list_check cc (B @ [b])" using 3 1 2  Cons.IH by blast
      obtain c1 c2 crest where cp: "B = c1#c2#crest" using blen
      by (metis Suc_1 Suc_le_length_iff list.size(3) neq_Nil_conv not_one_le_zero)
      hence 5:"cc a c1 c2" using Cons.prems(2) list_check.simps(4)[of "cc"] by simp
      have "list_check cc (c1#c2#crest@[b])" using cp 4 by simp
      then show ?thesis using list_check.simps(4)[of "cc" "a" "c1" "c2" "crest@[b]"] 5 cp by auto
    qed
  qed
qed(simp)

lemma append_first_sortedStrict:
  assumes "sorted_wrt (<) (B :: R2 list)" and "(b :: R2) < (hd B)"
  shows  "sorted_wrt (<) (b#B)"
proof-
  have 1: "sorted B" "distinct B" using assms strict_sorted_iff by auto
  have 2: "sorted (b#B)" using assms(2) 1(1)
    by (metis list.sel(1) neq_Nil_conv nless_le sorted1 sorted2)
  have 3: "distinct (b#B)" using assms(2) 1 2
    by (metis (no_types, lifting) distinct.simps(2) list.sel(1) list.set_cases nless_le not_less_iff_gr_or_eq
        sorted_simps(2))
  show ?thesis using 2 3 strict_sorted_iff by blast
qed

lemma sorted_wrt_reverse_append:
  assumes "sorted_wrt (>) (B :: R2 list)" and "(b :: R2) > (hd B)"
  shows  "sorted_wrt (>) (b#B)"
proof-
  have 1: "distinct B" using assms
    using distinct_rev sorted_wrt_rev strict_sorted_iff by blast
  have 2: "sorted_wrt (>)  (b#B)" using assms(2) 1
    using assms(1) distinct_rev sorted_wrt_rev strict_sorted_iff 
    by (smt (verit, best) list.sel(1) nless_le order_less_le_trans set_ConsD sorted_wrt.elims(2) sorted_wrt.simps(2)
        sorted_wrt1)
  have 3: "distinct (b#B)" using assms 1 2 
    by (metis "1" assms(1,2) distinct.simps(2) distinct_singleton list.sel(1) not_less_iff_gr_or_eq set_ConsD
        sorted_wrt.elims(2))
    show ?thesis using 2 3 strict_sorted_iff by blast
qed

lemma append_last_sortedStrict:
  assumes "sorted_wrt (<) (B :: R2 list)" 
      and "(b :: R2) > (last B)"
  shows   "sorted_wrt (<) (B@[b])"
proof- 
  have 1:"sorted_wrt (>) (rev B)" using sorted_wrt_rev[of "(<)"] using assms(1) by force
  have 2:"b > hd (rev B)"
    by (simp add: assms(2) hd_rev)
  have 3:"B@[b] = rev (b#(rev B))" using rev_def by simp
  show ?thesis using sorted_wrt_rev 1 2 3 assms sorted_wrt_reverse_append
    by metis
qed

(* ALERT: the assumption values are not well defined in isabelle
lemma "\<lbrakk>sortedStrict ([]); (1,2::real) < (hd ([]))\<rbrakk> \<Longrightarrow> sortedStrict [(1,2)]" by simp
value "sortedStrict(Nil)"
*)

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

lemma min_conv_lower_bnd:
assumes "k\<ge>3" and "l\<ge>3"
shows "min_conv k l \<le> min_conv (k - 1) l + min_conv k (l - 1) - 1"
            (is "?a \<le> ?b") 
  using inf_upper
  
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
        hence ysx:  "Y\<subseteq>X" using cap_endpoint_subset using asm assms by auto
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
            (* try changing k-2 = Suc(k-3) to make it faster? *)
            have k4:"(kap!(k-3)) < (kap!(k-2))" using assms(1) kap(2,3) cap_def
              by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD add_leE lessI
                  numeral_3_eq_3 plus_1_eq_Suc sorted_wrt_iff_nth_less)
            have k5:"(kap!(k-2)) < (lup!1)" using assms lup cup_def
              by (metis One_nat_def Suc_1 Suc_le_lessD add_diff_cancel_left' diff_less_mono
                  k3 numeral_3_eq_3 numeral_One one_le_numeral plus_1_eq_Suc
                  sorted_wrt_nth_less)
            hence k6:"sortedStrict [(kap!(k-3)),(kap!(k-2)),(lup!1)]" using k4 k5 by simp

            hence k_noncoll:"\<not> collinear3 (kap!(k-3)) (kap!(k-2)) (lup!1)" 
              by (metis (full_types) asm(2) assms(1) collinear3_def diff_less_mono2 dual_order.trans genpos_cross0 k1 k2 k7 kap(1) linorder_not_less nth_mem numeral_le_one_iff semiring_norm(70) strict_sorted_iff subsetD ysx)

            thus ?thesis
            proof(cases "cap3 (kap!(k-3)) (kap!(k-2)) (lup!1)")

              case True
              hence k8:"cap k (kap@[lup!1])" using kap(2,3) cap_def
              proof-

                have k_rev: "rev ( (lup!1) # ( rev kap ) ) = (kap@[lup!1])" by force
                have k_lup_len: "length (kap@[lup!1]) = k" using k1 k5
                  using assms(1) by fastforce
                hence k29:"sortedStrict (kap@[lup!1] )" 
                  using k1 k3 lup(1) k5 kap(2) assms append_last_sortedStrict
                  by (metis Suc_1 append_Nil diff_Suc_eq_diff_pred last_conv_nth sorted_wrt1)
                thus ?thesis 
                  using k29 k_lup_len True cap_def extend_cap_cup k_rev kap(3)
                  by (metis (no_types, lifting) One_nat_def Suc_1 diff_diff_left numeral_3_eq_3 plus_1_eq_Suc)
              qed
              have "set kap \<subseteq> X" using kap(1) ysx by blast
              hence "set (kap@[lup!1]) \<subseteq> X" using k7 by force 
              then show ?thesis using k1 assms(1) cap_def lup kap ysx order_trans k8 by blast
            next
              case False
              hence k9:"cup l (kap!(k-3)#lup)"
              proof-
                have k_kap_len: "length (kap!(k-3)#lup) = l" using k4 lup(1) k3 lup(4) cup_def
                  using assms(2) by auto
                have "sortedStrict (kap!(k-3)#lup)" using k4 lup(1,3) k3 assms(1,2) append_first_sortedStrict
                  by (metis hd_conv_nth sorted_wrt1) 
                thus ?thesis using False k_noncoll cup_def list_check.simps exactly_one_true k3 k4 k_kap_len lup(1,4)
                  by (smt (verit)  diff_is_0_eq' verit_comp_simplify1(1) nth_Cons_numeral numeral_One
                      le_numeral_extra(4) list_check.elims(1) nth_Cons_0)
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

lemma distinctFst_distinct:
  "distinct (map fst xs) \<longrightarrow> distinct xs"
  by (simp add: distinct_map)

value "sortedStrict [(1,2)::R2, (1,3)]"
value "sdistinct [(1,2)::R2, (1,3)]"
value "sdistinct [(1,2), (2,3)]"

lemma sdistinct_sortedStrict:
  assumes "sdistinct xs"
  shows   "sortedStrict xs" 
  using assms distinctFst_distinct strict_sorted_iff by auto

lemma distinct_fst_translated:
  fixes   L :: "R2 list" and t :: R2
  assumes "distinct (map fst L)" and "tr \<equiv> (\<lambda>p. p + t)"
  shows   "distinct (map fst (map tr L))"
  using assms
proof(induction L)
  case (Cons a L)
  have "distinct (map fst L)"
    using Cons.hyps(2) by auto
  hence "distinct (map fst (map tr L))" using Cons.hyps by simp
  have F1:"fst a \<notin> set (map fst L)" "distinct (map fst L)" using Cons.hyps(2) by auto
  have "fst (a+t) \<notin> set (map fst (map tr L))"
  proof
    assume asm: "fst (a + t) \<in> set (map fst (map tr L))"
    then obtain x :: R2 where xp:"fst (x+t)\<in>set(map fst(map tr L))" "fst (x+t)=fst(a+t)" by force
    hence "fst x = fst a" by simp
    hence "fst (a+t) \<in> set(map fst(map tr L))" using xp(1) by simp
    hence "fst a \<in> set(map fst L)"
      by (smt (verit, ccfv_threshold) assms(2) fst_add imageE image_eqI list.set_map)
    thus False using F1(1) by simp
  qed
  then show ?case using Cons.hyps by simp
qed(simp)

lemma prod_addright_le:
  fixes   a s t :: R2 
  assumes "a \<le> s"
  shows   "a + t \<le> s + t"
proof(cases "fst a < fst s")
  case True
  hence "fst (a + t) < fst (s + t)" by simp
  then show ?thesis
    by (smt (verit, best) assms fst_add prod_le_def snd_add)
next
  case False
  hence I8:"fst a = fst s" using assms
    by (simp add: prod_le_def)
  hence "snd a \<le> snd s" using assms prod_le_def False by blast
  hence "snd (a + t) \<le> snd (s + t)" by simp
  then show ?thesis
    by (auto simp add: I8 less_eq_prod_def)
qed

lemma bij_tr:
  "bij (\<lambda> p. p + (t::R2))"
  by (simp add: bij_plus_right)

lemma map_sorted_list_set:
  fixes t :: R2
  shows "map (\<lambda> p. p + t) (sorted_list_of_set S) = sorted_list_of_set ((\<lambda> p. p + t) ` S)"
proof(induction "sorted_list_of_set S" arbitrary: S)
  case Nil
  then show ?case using bij_tr
    by (metis (no_types, lifting) bij_def card_seteq card_vimage_inj dual_order.refl empty_subsetI top.extremum inj_vimage_image_eq list.simps(8) sorted_list_of_set.fold_insort_key.infinite
        sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set.sorted_key_list_of_set_empty)
next
  case (Cons a x)
  hence I1:"x  = sorted_list_of_set (S - {a})"
    by (metis list.inject neq_Nil_conv sorted_list_of_set.fold_insort_key.infinite
        sorted_list_of_set.sorted_key_list_of_set_eq_Nil_iff sorted_list_of_set_nonempty)
  hence I2:"map (\<lambda> p. p + t) (sorted_list_of_set (S-{a})) = 
            sorted_list_of_set ((\<lambda> p. p + t) ` (S-{a}))" using Cons.hyps(1,2) by presburger
  have I4: "a = Min S"
    by (metis Cons.hyps(2) list.inject neq_Nil_conv sorted_list_of_set.fold_insort_key.infinite
        sorted_list_of_set.sorted_key_list_of_set_empty sorted_list_of_set_nonempty)
  hence "a \<in> S"
    by (metis Cons.hyps(2) Diff_insert_absorb I1 insert_Diff1 not_Cons_self2 singleton_iff)
  hence I5:"a + t \<in> (\<lambda>s. s + t) ` S" by simp
  have I6:"\<forall>s\<in>S. a\<le>s" using I4
    by (metis Cons.hyps(2) Min.coboundedI neq_Nil_conv
        sorted_list_of_set.fold_insort_key.infinite)
  hence "\<forall>s\<in>S. a + t \<le> s + t" using prod_addright_le by simp
  hence "\<forall>s\<in>((\<lambda>s. s + t) ` S). a + t \<le> s" by simp
  hence I3:"a + t = Min ((\<lambda> p. p + t) ` S)" using I5
    by (metis Cons.hyps(2) I1 Min_eqI finite_imageI infinite_remove not_Cons_self
        sorted_list_of_set.fold_insort_key.infinite)
  then show ?case
    by (smt (z3) Cons.hyps(2) Diff_empty Diff_insert0 Diff_insert_absorb I2 add_right_cancel
        empty_not_insert finite_imageI insert_absorb list.inject list.set(1,2) list.set_map
        list.simps(8,9) sorted_list_of_set.fold_insort_key.infinite
        sorted_list_of_set.set_sorted_key_list_of_set sorted_list_of_set_nonempty)
qed

lemma translated_cross3:
  shows "cross3 a b c = cross3 (a+t) (b+t) (c+t)"
  unfolding cross3_def by simp

lemma translated_cup:
  assumes "cup k xs"
  shows   "cup k (map (\<lambda>p. p + t) xs)" using assms
proof(induction xs arbitrary: k)
  case (Cons a xs)
  hence "cup (k-1) xs" using cup_reduct
    by (metis Suc_eq_plus1 Suc_pred' bot_nat_0.not_eq_extremum cup_def length_0_conv
        neq_Nil_conv)
  hence F1:"cup (k-1) (map (\<lambda>p. p + t) xs)" 
    using Cons.IH by blast
  then show ?case
  proof(cases "length (a#xs) \<le> 2")
    case True
    then show ?thesis
      by (metis (no_types, lifting) Cons.prems add_right_cancel cup_def lcheck_len2_T length_map nless_le prod_addright_le sorted_wrt_map_mono strict_sorted_iff)
  next
    case False
    hence "length (a#xs) \<ge> 3" by simp
    hence "\<exists>a u v rest. (a#xs) = (a#u#v#rest)"
      by (metis One_nat_def Suc_eq_plus1 list.size(3,4) neq_Nil_conv nle_le not_less_eq_eq
          numeral_3_eq_3)
    then obtain u v rest where xsp: "xs = u#v#rest" by blast
    hence "cup3 a u v" "list_check cup3 (u#v#rest)"
      using assms cup_def Cons.prems by auto
    hence F2:"cup3 (a+t) (u+t) (v+t)" using translated_cross3
      by (metis cup3_def)
    have "list_check cup3 (map (\<lambda>p. p+t) (u#v#rest))"
      using F1 cup_def xsp by blast
    then show ?thesis using F2
      by (smt (verit, best) Cons.prems add_right_imp_eq cup_def length_map list.simps(9)
          list_check.simps(4) nless_le prod_addright_le sorted_wrt_map_mono xsp)
  qed
qed(simp)

lemma translated_cup_eq:
  "\<And>t. cup k xs = cup k (map (\<lambda>p. p + t) xs)"
proof
  define ys where ysp: "ys \<equiv> map (\<lambda>p. p - t) xs"
  have "cup k ys \<Longrightarrow> cup k (map (\<lambda>p. p + t) ys)" using translated_cup by simp
  hence "cup k (map (\<lambda>p. p - t) xs) \<Longrightarrow> cup k xs"
    by (simp add: o_def ysp)
  thus "\<And>t. cup k (map (\<lambda>p. p + t) xs) \<Longrightarrow> cup k xs"
  proof -
    fix ta :: "real \<times> real"
    assume a1: "cup k (map (\<lambda>p. p + ta) xs)"
    have "\<forall>ps. map ((+) (reflect ta)) (map (\<lambda>p. p + ta) ps) = ps"
      by (simp add: o_def)
    then show "cup k xs"
      using a1 by (metis (lifting) add.commute map_ext translated_cup)
  qed
qed(simp add:translated_cup)

lemma translated_cap:
  assumes "cap k xs"
  shows   "cap k (map (\<lambda>p. p + t) xs)" using assms
proof(induction xs arbitrary: k)
  case (Cons a xs)
  hence "cap (k-1) xs" using cap_reduct
    by (metis Suc_eq_plus1 Suc_pred' bot_nat_0.not_eq_extremum cap_def length_0_conv
        neq_Nil_conv)
  hence F1:"cap (k-1) (map (\<lambda>p. p + t) xs)" 
    using Cons.IH by blast
  then show ?case
  proof(cases "length (a#xs) \<le> 2")
    case True
    then show ?thesis
      by (metis (no_types, lifting) Cons.prems add_right_cancel cap_def lcheck_len2_T length_map nless_le prod_addright_le sorted_wrt_map_mono strict_sorted_iff)
  next
    case False
    hence "length (a#xs) \<ge> 3" by simp
    hence "\<exists>a u v rest. (a#xs) = (a#u#v#rest)"
      by (metis One_nat_def Suc_eq_plus1 list.size(3,4) neq_Nil_conv nle_le not_less_eq_eq
          numeral_3_eq_3)
    then obtain u v rest where xsp: "xs = u#v#rest" by blast
    hence "cap3 a u v" "list_check cap3 (u#v#rest)"
      using assms cap_def Cons.prems by auto
    hence F2:"cap3 (a+t) (u+t) (v+t)" using translated_cross3
      by (metis cap3_def)
    have "list_check cap3 (map (\<lambda>p. p+t) (u#v#rest))"
      using F1 cap_def xsp by blast
    then show ?thesis using F2
      by (smt (verit, best) Cons.prems add_right_imp_eq cap_def length_map list.simps(9)
          list_check.simps(4) nless_le prod_addright_le sorted_wrt_map_mono xsp)
  qed
qed(simp)

lemma translated_cap_eq:
  "\<And>t. cap k xs = cap k (map (\<lambda>p. p + t) xs)"
proof
  define ys where ysp: "ys \<equiv> map (\<lambda>p. p - t) xs"
  have "cap k ys \<Longrightarrow> cap k (map (\<lambda>p. p + t) ys)" using translated_cap by simp
  hence "cap k (map (\<lambda>p. p + (-t)) xs) \<Longrightarrow> cap k xs"
    by (simp add: o_def ysp)
  thus "\<And>t. cap k (map (\<lambda>p. p + t) xs) \<Longrightarrow> cap k xs"
    (* the Isar proof below was found using sledgehammer *)
  proof -
    fix ta :: "real \<times> real"
    assume a1: "cap k (map (\<lambda>p. p + ta) xs)"
    have "\<forall>ps. map (\<lambda>p. p + reflect ta) (map (\<lambda>p. p + ta) ps) = ps"
      by (simp add: comp_def)
    then show "cap k xs"
      using a1 by (metis (no_types) translated_cap)
  qed
qed(simp add:translated_cap)


lemma translated_set:
  fixes   t :: R2
  
  assumes "card S = n"
      and "general_pos S"
      and "sdistinct(sorted_list_of_set S)"
      and "\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs)" 
      and "St = (\<lambda> p. p + t) ` S"   
    
    shows "card St = n" and "general_pos St" and "sdistinct(sorted_list_of_set St)"
      and "\<forall>xs. set xs \<subseteq> St \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs)"
proof-
  show "card St = n" using bij_tr bij_def assms(1,5)
    by (metis card_vimage_inj inj_vimage_image_eq top.extremum)

  have "gpos St"
  proof-
    have 3:"gpos S"
      using assms(2) gpos_generalpos by auto
    {
      fix a b c
      assume asm:"a\<in>S" "b\<in>S" "c\<in>S" "distinct [a,b,c]"
      hence 4:"\<not>collinear3 a b c" using 3 unfolding gpos_def by simp
      have 5:"distinct [a + t, b + t, c + t]" using asm(4) by auto
      have "\<not>collinear3 (a + t) (b + t) (c + t)" 
        using 4 unfolding collinear3_def cross3_def by simp
      then have "distinct [a + t, b + t, c + t] \<longrightarrow> \<not>collinear3 (a + t) (b + t) (c + t)"
        using 5 by simp
    }
    thus ?thesis using 3 unfolding gpos_def
      by (simp add: assms(5))
  qed
  thus "general_pos St" using gpos_generalpos by simp

  have 6:"distinct (map fst (sorted_list_of_set S))" using assms(3) by simp
  have 8:"distinct (map fst (map (\<lambda> p. p + t) (sorted_list_of_set S)))" 
    using 6 distinct_fst_translated by blast
  hence "distinct (map fst (sorted_list_of_set ((\<lambda> p. p + t) ` S)))" 
    using map_sorted_list_set 8 by simp
  thus "sdistinct(sorted_list_of_set St)" using assms(3, 5) by simp

  have "\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict (map (\<lambda> p. p + t) xs)) \<longrightarrow> 
        \<not>(cap k (map (\<lambda> p. p + t) xs) \<or> cup l (map (\<lambda> p. p + t) xs))" 
    using translated_cup_eq translated_cap_eq
    by (meson assms(4) cap_def cup_def)
  hence 9:"\<forall>xs. \<forall>ys. set xs \<subseteq> S \<and> (ys = map (\<lambda>p. p+t) xs) \<and> (sortedStrict ys) 
        \<longrightarrow> \<not>(cap k ys \<or> cup l ys)" by blast
  hence "\<forall>xs. \<forall>ys. set ys \<subseteq> ((\<lambda>p. p+t) ` S) \<and> (ys = map (\<lambda>p. p+t) xs) \<and> (sortedStrict ys) 
        \<longrightarrow> \<not>(cap k ys \<or> cup l ys)"
    by (simp add: image_iff image_subset_iff subsetI)
  thus "\<forall>xs. set xs \<subseteq> St \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs)"
    using assms(5) 9
    by (metis (no_types, lifting) diff_add_cancel ex_map_conv)
qed

lemma min_conv_lower_sdistinct:
  assumes "\<exists>S. (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<and> (\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  shows "min_conv k l > n"
  using assms min_conv_lower by blast

lemma min_conv_lower_imp:
  assumes "min_conv k l > n"
  shows   "\<exists>S. (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<and> (\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  oops
(* proof-
  have "\<exists>S. (card S \<ge> n \<and> general_pos S)
                \<and> (\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
    using assms unfolding min_conv_def
    by (smt (verit, ccfv_SIG) inf_upper mem_Collect_eq order.strict_iff_not)
  then obtain S where Sp: "(card S \<ge> n \<and> general_pos S)" 
                          "\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap k xs \<or> cup l xs)"
    by blast
(* rotate S slightly to make sure no x coord is same ? *)
  thus ?thesis sorry
qed
 *)
thm min_conv_lower[of "n" "Suc (k+2)" "Suc (l+2)"]

lemma min_conv_least:
  assumes "a \<ge> 1" and "b \<ge> a"
    shows "a \<le> min_conv a b"
proof-
  have "a - 1 \<notin> {n. \<forall>S. n = card S \<and> general_pos S \<longrightarrow> 
               (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap a xs \<or> cup b xs))}"
  proof-
    {
      assume asm:"a - 1 \<in> {n. \<forall>S. n = card S \<and> general_pos S \<longrightarrow>
               (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap a xs \<or> cup b xs))}"
      fix S
      have F1: "a-1 = card S \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and>
               (cap a xs \<or> cup b xs))" 
        using asm by simp
      have F2: "\<forall>xs. (a-1 = card S \<and> set xs \<subseteq> S \<and> sortedStrict xs \<longrightarrow> \<not>(cap a xs \<or> cup b xs))"
      proof
        fix xs
        {
          assume "a - 1 = card S \<and> set xs \<subseteq> S \<and> sortedStrict xs"
          hence asmd: "a - 1 = card S" "set xs \<subseteq> S" "sortedStrict xs" by auto
          hence "card (set xs) \<le> a-1"
            by (smt (verit, del_insts) Orderings.order_eq_iff asm assms(1,2) cap_def card.empty card.infinite le_add_diff_inverse card_mono cup_def empty_subsetI general_pos_subs genpos_ex gpos_generalpos list.size(3) mem_Collect_eq nat.simps(3) plus_1_eq_Suc set_empty2) 
          hence "length xs \<le> a-1" using asmd(2,3)
            by (metis distinct_card strict_sorted_iff)
          hence "\<not>(cap a xs \<or> cup b xs)"  
            using assms(1,2) cap_def cup_def by auto
        }
        thus "a - 1 = card S \<and> set xs \<subseteq> S \<and> sortedStrict xs \<longrightarrow> \<not> (cap a xs \<or> cup b xs)" by simp
      qed
      {
        assume A1:"a-1 = card S \<and> general_pos S"
        hence A2: "a-1 = card S" "general_pos S" by auto
        hence "(\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap a xs \<or> cup b xs))" using F1 by simp
        then obtain xs where xspp:"set xs \<subseteq> S" "sortedStrict xs" "(cap a xs \<or> cup b xs)" by blast
        hence "\<not>(cap a xs \<or> cup b xs)" using F2 A2(1) by simp
        hence False using xspp(3) by simp
      }
    }
    thus "a - 1 \<notin> {n. \<forall>S. n = card S \<and> general_pos S \<longrightarrow> 
               (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap a xs \<or> cup b xs))}"
      by (metis genpos_ex gpos_generalpos)
  qed
  thus "a \<le> min_conv a b"
    using cap_def min_conv_lower by fastforce
qed

theorem min_conv_min:
  assumes "a \<ge> 1" and "b \<ge> 1"
    shows "min a b \<le> min_conv a b"
  using min_conv_least assms(1,2) min_conv_arg_swap 
  by (metis min_le_iff_disj nat_le_linear)

lemma min_conv_1:
  assumes "k\<ge>1"
  shows "min_conv 1 k = 1"
proof-
  have 1:"min_conv 1 k \<ge> 1" using assms min_conv_min[of "1" "k"] by simp
  have "min_conv 1 k \<le> 1"
  proof-
    {
      fix S
      assume asm:"card S = 1" "general_pos S"
      have "(\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap 1 xs \<or> cup k xs))"
      proof-
        obtain p where p1p2: "S = {p}" using asm using card_1_singletonE by blast
        have 1:"set [p] \<subseteq> S \<and> sortedStrict [p]" using p1p2 by auto
        have 2: "cap 1 [p]" using p1p2 by (simp add: cap_def)
        thus ?thesis using 1 2 by blast
      qed
    }
    hence "\<forall>S. 1 \<le> card S \<and> general_pos S \<longrightarrow>
                (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap 1 xs \<or> cup k xs))"
      by (meson ex_card general_pos_subs order.trans)
    thus ?thesis unfolding min_conv_def by (simp add: inf_upper)
  qed
  thus ?thesis using 1 by simp
qed

lemma min_conv_2:
  assumes "k\<ge>2"  
  shows "min_conv 2 k = 2"
proof-
  have 1:"min_conv 2 k \<ge> 2" using assms min_conv_min[of "2" "k"] by simp
  have "min_conv 2 k \<le> 2"
  proof-
    {
      fix S
      assume asm:"card S = 2" "general_pos S"
      have "(\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap 2 xs \<or> cup k xs))"
      proof-
        obtain p1 p2 where p1p2: "S = {p1, p2}" "p1 < p2" using asm
          by (metis antisym_conv3 card_2_iff insert_commute)
        have 1:"set [p1,p2] \<subseteq> S \<and> sortedStrict [p1,p2]"
          using p1p2(1,2) by auto
        have 2: "cap 2 [p1,p2]" using p1p2(2)
          by (simp add: cap_def)
        thus ?thesis using 1 2 by blast
      qed
    }
    hence "\<forall>S. 2 \<le> card S \<and> general_pos S \<longrightarrow>
                (\<exists>xs. set xs \<subseteq> S \<and> sortedStrict xs \<and> (cap 2 xs \<or> cup k xs))"
      by (meson ex_card general_pos_subs order.trans)
    thus ?thesis unfolding min_conv_def
      by (simp add: inf_upper)
  qed
  thus ?thesis using 1 by simp
qed

lemma min_conv_upper_bnd:
  shows "min_conv (Suc (k+2)) (Suc (l+2)) > 
        (min_conv (k+2) (Suc (l+2)) - 1) + (min_conv (Suc (k+2)) (l+2) - 1)"
        (is "?P a b > ?n1 + ?n2")
    and "\<exists>S. (card S = min_conv (Suc (k+2)) (Suc (l+2)) - 1
          \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
          \<and> (\<forall>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (Suc (l+2)) xs))"
proof(induction "k+l" arbitrary: k l)
  case 0
  {
    case 1
    then show ?case
      using "0" min_conv_arg_swap min_conv_base numeral_3_eq_3 by fastforce
  next
    case 2
    hence 21:"k=0" "l=0" using "0" by auto
    hence 22:"min_conv (Suc (k + 2)) (Suc (l + 2)) - 1 = 2" using min_conv_base
      by (simp add: numeral_3_eq_3)
    define PS2 where ps2: "PS2 = {(0,1), (1,2)::R2}"
    have F1_PS2: "card PS2 = 2" using ps2 by force
    have "gpos PS2" by (simp add: gpos_def ps2)
    hence F2_PS2: "general_pos PS2" using gpos_generalpos by simp
    have F3_PS2: "sdistinct(sorted_list_of_set PS2)" by (simp add: ps2)
    have "\<forall>xs. set xs \<subseteq> PS2 \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (Suc (l+2)) xs)" using F1_PS2 ps2 21 22
      by (metis (no_types, lifting) add_eq_if add_le_same_cancel2 card_mono card_of_s cup_def
          distinct_card finite.intros(1) finite_insert leD plus_1_eq_Suc strict_sorted_iff
          zero_less_one)
    then show ?case using 22 F1_PS2 F2_PS2 F3_PS2 by force
  }
next
  case (Suc x)
  {
    case 1
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

      have "\<exists>S. (card S =
         min_conv (k + 2) (Suc (l + 2)) - 1 \<and>
         general_pos S \<and>
         sdistinct (sorted_list_of_set S)) \<and>
        (\<forall>xs. set xs \<subseteq> S \<and> sortedStrict xs \<longrightarrow>
              \<not> (cap (k + 2) xs \<or>
                  cup (Suc (l + 2)) xs))" using Suc F2
        by (metis (no_types, opaque_lifting) FC1(1) add_2_eq_Suc' le_add_diff_inverse
            plus_1_eq_Suc)
      then obtain S1 where 
        S1p: "card S1 = min_conv (k + 2) (Suc (l + 2)) - 1" 
             "general_pos S1"  "sdistinct(sorted_list_of_set S1)"
             "\<forall>xs. set xs \<subseteq> S1 \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap (k+2) xs \<or> cup (Suc (l+2)) xs)"
        by blast

      have "\<exists>S. (card S =
         min_conv (Suc (k + 2)) (l + 2) - 1 \<and>
         general_pos S \<and>
         sdistinct (sorted_list_of_set S)) \<and>
        (\<forall>xs. set xs \<subseteq> S \<and> sortedStrict xs \<longrightarrow>
              \<not> (cap (Suc (k + 2)) xs \<or>
                  cup (l + 2) xs))" using Suc F1
        by (metis add_2_eq_Suc' add_Suc_right add_diff_cancel_left')
      then obtain S2t where 
        S2tp: "card S2t = min_conv (Suc (k + 2)) (l + 2) - 1" 
              "general_pos S2t" "sdistinct(sorted_list_of_set S2t)"
              "\<forall>xs. set xs \<subseteq> S2t \<and> (sortedStrict xs) \<longrightarrow> \<not>(cap (Suc (k+2)) xs \<or> cup (l+2) xs)"
        by blast
(* find t using which S2t can be translated while satisfying the conditions *)
      fix t define S2 where "S2 = (\<lambda>p. p + t) ` S2t"
(* show that S2 has no big cups or caps using the lemma translated_set *)

(* make sure the chosen t allows for the following conditions *)
      have set2higher:      "\<forall>x\<in>S1. \<forall>y\<in>S2. fst x < fst y" sorry
      have bigslopeacross1: "\<forall>x\<in>S1. \<forall>y\<in>S1. \<forall>z\<in>S2. ((x < y) \<longrightarrow> cup3 x y z)" sorry
      have bigslopeacross2: "\<forall>b\<in>S2. \<forall>c\<in>S2. \<forall>a\<in>S1. ((b < c) \<longrightarrow> cap3 a b c)" sorry
      then show ?thesis sorry
    qed
    case 2
    then show ?case sorry
  }
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