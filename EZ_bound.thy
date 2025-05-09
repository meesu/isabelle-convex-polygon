theory EZ_bound
imports Four_Convex Definitions Prelims GeneralPosition3 Invariants
begin

(*** start of Theorem 2.2 Andrew Suk ***)


lemma min_conv_leImpe:
  shows "Inf (min_conv_set k l)
        =
        Inf {n. \<forall>S . (card S = n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs))}"  
  by (smt (verit) min_conv_set_def Collect_cong add.commute add_diff_cancel_left' card.infinite diff_is_0_eq' dual_order.trans ex_card general_pos_subs le_add_diff_inverse linorder_not_less nless_le
      sdistinct_sub)

lemma min_conv_lower_imp1o:
  assumes "n < min_conv k l"
  shows   "\<exists>S. (card S = n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<and> (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  using assms inf_upper min_conv_def min_conv_leImpe min_conv_set_def
  by (smt (verit, del_insts) linorder_not_less mem_Collect_eq sorted_list_of_set.sorted_sorted_key_list_of_set)

lemma min_conv_num_out_set:
  assumes "\<exists>S.         card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<and> 
                (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  shows   "n \<notin> min_conv_set k l"
  unfolding min_conv_set_def using assms by blast

theorem non_empty_cup_cap:
  fixes k l
  shows "{} \<noteq> {n :: nat. (\<forall>S :: R2 set. (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs)))}"
  sorry


lemma extract_cap_cup:
    assumes "min_conv k l = n"
        and "card (S :: R2 set) = n" 
        and "general_pos S"
        and "sdistinct(sorted_list_of_set S)"
      shows "\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs)"
  using assms Inf_nat_def1 mem_Collect_eq min_conv_def
  by (smt (verit, best) linorder_not_less nless_le non_empty_cup_cap)

lemma min_conv_num_out:
  assumes "min_conv_set k l \<noteq> {}"
    and   "\<exists>S.  card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<and> 
                (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  shows "min_conv k l \<noteq> n"
  using assms min_conv_def min_conv_num_out_set min_conv_set_def
  by (metis (lifting) Inf_nat_def1)

lemma min_conv_lower:
  assumes "min_conv_set k l \<noteq> {}"
    and   "\<exists>S.  card S = n \<and> general_pos S \<and> 
                sdistinct(sorted_list_of_set S) \<and> 
                (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
  shows "min_conv k l > n"
proof-
  obtain S where "card S \<ge> n" "general_pos S" 
          "sdistinct(sorted_list_of_set S)" 
          "\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs)"
    using assms by blast
  hence "\<forall>t. t \<le> n \<longrightarrow> min_conv k l \<noteq> t" using min_conv_num_out assms by metis
  thus ?thesis using min_conv_def not_le_imp_less by blast
qed

lemma min_conv_least:
  assumes "a \<ge> 1" and "b \<ge> a"
  shows "a \<le> min_conv a b"
proof-
  have "a - 1 \<notin> {n. \<forall>S. n = card S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<longrightarrow> 
               (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap a xs \<or> cup b xs))}"
  proof-
    {
      assume asm:"a - 1 \<in> {n. \<forall>S. n = card S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<longrightarrow>
               (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap a xs \<or> cup b xs))}"
      fix S
      have F1: "a-1 = card S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap a xs \<or> cup b xs))" 
        using asm by simp
      have F2: "\<forall>xs. (a-1 = card S \<and> set xs \<subseteq> S \<and> general_pos(S) \<and> sdistinct(sorted_list_of_set S) \<longrightarrow> \<not>(cap a xs \<or> cup b xs))"
      proof
        fix xs
        {
          assume a1:"a - 1 = card S" "set xs \<subseteq> S" "sdistinct(sorted_list_of_set S)"
          hence asmd: "a - 1 = card S" "set xs \<subseteq> S" using a1 by auto
          hence a2:"length xs > a-1 \<Longrightarrow> \<not>sdistinct xs" using a1 
            by (smt (verit, ccfv_threshold) Orderings.order_eq_iff asm assms(1,2) cap_def card.infinite
                card_mono cup_def empty_subsetI general_pos_subs genpos_ex gpos_generalpos le_add_diff_inverse
                length_0_conv linorder_not_less mem_Collect_eq nat.distinct(1) plus_1_eq_Suc
                sdistinct_sortedStrict set_empty2 sorted_list_of_set.idem_if_sorted_distinct
                sorted_list_of_set.length_sorted_key_list_of_set strict_sorted_iff)
          hence "\<not>(cap a xs \<or> cup b xs)"  
            using assms(1,2) a2 cap_def cup_def by force
        }
        thus "a - 1 = card S \<and> set xs \<subseteq> S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) 
              \<longrightarrow> \<not> (cap a xs \<or> cup b xs)" by simp
      qed
      {
        assume A1:"a-1 = card S" "general_pos S" "sdistinct(sorted_list_of_set S)"
        hence "(\<exists>xs. set xs \<subseteq> S  \<and> sdistinct xs \<and> (cap a xs \<or> cup b xs))" using F1 by simp
        then obtain xs where xspp:"set xs \<subseteq> S" "(cap a xs \<or> cup b xs)" by blast
        hence "\<not>(cap a xs \<or> cup b xs)" using F2 A1 by simp
        hence False using xspp by simp
      }
    }
    thus "a - 1 \<notin> {n. \<forall>S. n = card S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<longrightarrow> 
               (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap a xs \<or> cup b xs))}"
      by (metis (no_types, lifting) genpos_ex gpos_generalpos)
  qed
  thus "a \<le> min_conv a b"
    using cap_def min_conv_lower sledgehammer
qed

theorem min_conv_min:
  assumes "a \<ge> 1" and "b \<ge> 1"
    shows "min a b \<le> min_conv a b"
  using min_conv_least assms(1,2) min_conv_arg_swap 
  by (metis min_le_iff_disj nat_le_linear)


(* lemma min_conv_finiteS:
    assumes "min_conv (k+1) (l+1) \<ge> card (S :: R2 set)"
    shows   "finite S"
proof-
  have 1:"min_conv (k+1) (l+1) = card (T :: R2 set) \<longrightarrow> finite T"
    by (metis One_nat_def Suc_eq_plus1 Suc_le_mono card.infinite linorder_not_less min_Suc_Suc 
        min_conv_min zero_le zero_less_Suc)
  fix T
  assume asm:"min_conv (k+1) (l+1) = card (T :: R2 set)"
  hence 2:"finite T" using 1
    by (metis Suc_eq_plus1 card.infinite le_add2 linorder_not_less min_Suc_Suc min_conv_min zero_less_Suc)
  have "card S \<le> card T" using asm assms by simp
  hence "finite S" using 2 assms(2) sorry
qed
 *)


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
    hence "\<forall>S. 1 \<le> card S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<longrightarrow>
                (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap 1 xs \<or> cup k xs))"
      by (meson cap_def cup_def general_pos_subs obtain_subset_with_card_n
          subset_trans)
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
      assume asm:"card S = 2" "general_pos S" "sdistinct(sorted_list_of_set S)"
      have S_fin: "finite S" by (metis asm(1) card.infinite zero_neq_numeral)
      have "(\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap 2 xs \<or> cup k xs))"
      proof-
        obtain p1 p2 where p1p2: "S = {p1, p2}" "p1 < p2"
          by (metis asm(1) card_2_iff insert_commute linorder_less_linear)
        hence 1:"set [p1,p2] \<subseteq> S \<and> sorted [p1,p2] \<and> sdistinct [p1,p2]"
          by (metis One_nat_def Suc_1 asm(1,3) card_distinct dual_order.refl empty_set
              length_Cons list.simps(15) list.size(3) nless_le sorted1 sorted2
              sorted_list_of_set.idem_if_sorted_distinct)
        hence 2: "cap 2 [p1,p2]" using p1p2(2)
          by (simp add: cap_def)
        thus ?thesis using 1 2 by blast
      qed
    }
    hence "\<forall>S. 2 \<le> card S \<and> general_pos S \<and> sdistinct(sorted_list_of_set S) \<longrightarrow>
                (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap 2 xs \<or> cup k xs))"
      by (smt (verit, ccfv_threshold)
          card.infinite ex_card
          general_pos_subs
          less_le_not_le less_one
          order.trans
          sdistinct_sub)
      thus ?thesis unfolding min_conv_def
      by (simp add: inf_upper)
  qed
  thus ?thesis using 1 by simp
qed

lemma xyz:
  assumes "min_conv 3 k = k"  and S_asm:  "card S = Suc k" and 
    S_gp: "general_pos S"     and         "sdistinct(sorted_list_of_set S)"
  shows "\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap 3 xs \<or> cup (Suc k) xs)"
  using assms
proof-
  obtain x xs where x_xs:"S = set (x#xs)" "sdistinct (x#xs)" "length (x#xs) = card S"
    using genpos_ex S_asm assms list.exhaust list.size(3) nat.simps(3)
    by (metis  card.infinite sorted_list_of_set.sorted_key_list_of_set_unique)
  
  have x_Min:"x = Min S" using x_xs
    by (metis S_asm card.empty card.infinite card_distinct list.inject old.nat.distinct(2) sorted_list_of_set.idem_if_sorted_distinct
        sorted_list_of_set_nonempty)

  have "length xs = k" using S_asm x_xs by auto
  hence sminus_x:"card (S - {x}) = k" using S_asm by (simp add: card.insert_remove x_xs(1))
  moreover have gp_sminus_x:"general_pos (S - {x})" using x_xs(1) S_gp general_pos_subs by blast
  text \<open>Using induction hypothesis obtain the cap of size 3 or cup of size k from the set S - {min(S)}.\<close>
  ultimately obtain zs where zs:"set zs \<subseteq> S - {x}" "(cap 3 zs \<or> cup k zs)"
    unfolding min_conv_def 
    using assms genpos_ex gpos_generalpos x_xs sdistinct_sub gp_sminus_x
    by (metis Diff_subset List.finite_set extract_cap_cup)
  have "\<exists>cc. set cc \<subseteq> S \<and> (cap 3 cc \<or> cup (Suc k) cc)"
  proof(cases "cap 3 zs")
    case True
    then show ?thesis using zs(1,2) by auto
  next
    case False
    hence F1:"cup k zs" using zs by simp
    hence F2:"length zs = k" unfolding cup_def by argo
    hence F0:"length (x#zs) = Suc k" using x_Min by auto
    have  F4:"set (x#zs) \<subseteq> S" using x_xs(1) zs(1) by auto
    have  F3:"sdistinct (x#zs)" using zs x_Min x_xs 
      by (metis (no_types, lifting) Diff_insert_absorb F0 F1 F4 assms(2) card.infinite card_subset_eq cup_def distinct_card distinct_map distinct_singleton insert_absorb
          length_0_conv list.set(2) set_empty2 sminus_x sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set_nonempty)
    then show ?thesis
    proof(cases "cup (Suc k) (x#zs)")
      case True
      then show ?thesis using x_xs(1) zs(1)
        by (metis Diff_empty insert_subset list.set_intros(1) list.simps(15) subset_Diff_insert)
    next
      case False
      hence "\<exists>a b c. (sublist [a,b,c] (x#zs)) \<and> \<not> cup3 a b c"
        using F0 F3 get_cap_from_bad_cup by presburger
      then obtain b1 b2 b3 where bcup:"sublist [b1,b2,b3] (x#zs)" "\<not> cup3 b1 b2 b3" by blast
      have fb1:"b1 \<in> S \<and> b2 \<in> S \<and> b3 \<in> S" 
        by (meson F4 bcup list.set_intros(1,2) set_mono_sublist subset_code(1))
      have fb2:"sdistinct [b1, b2, b3]" using bcup(1) F3 sdistinct_subl
        by presburger
(*         by (metis distinct_map strict_sorted_iff)
 *)      
      have fb3:"cross3 b1 b3 b2 \<noteq> 0" using S_gp fb1 cross3_commutation_23 fb2 genpos_cross0 by (metis distinct_map)
      have fb4:"length [b1, b2, b3] = 3" using fb2 by simp
      have     "cap3 b1 b2 b3" using fb3 bcup(2) cap3_def cup3_def not_less_iff_gr_or_eq
        by (metis cross3_commutation_23)
      hence "cap 3 [b1, b2, b3]" unfolding cap_def using fb2 fb4 by auto 
      thus ?thesis by (meson F4 bcup(1) dual_order.trans fb2 set_mono_sublist)
    qed
  qed
  thus ?thesis
    using cap_def cup_def by auto
qed

lemma abc:
  assumes "min_conv 3 k = k"
  shows "\<forall>S. (card S \<ge> Suc k) \<and> general_pos S \<and> 
              sdistinct(sorted_list_of_set S)
              \<longrightarrow> (\<exists>xs. (set xs \<subseteq> S) \<and> sdistinct xs \<and> (cap 3 xs \<or> cup (Suc k) xs))"
  using xyz assms sdistinct_sub general_pos_subs
  by (smt (verit, ccfv_SIG)
      Suc_le_D card.infinite
      ex_card nat.distinct(1)
      subset_trans)


lemma min_conv_3_k_bnd:
  shows "min_conv 3 (Suc k) > k"
proof-
  have "\<exists>S. (card S = k \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<and> (\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap 3 xs \<or> cup (Suc k) xs))"
  proof-
    obtain L where Trp:"length (L :: real list) = k" "sortedStrict L" using real_set_ex set2list
      by (metis sorted_list_of_set.length_sorted_key_list_of_set
          sorted_list_of_set.strict_sorted_key_list_of_set)
    define V2L where v2lp:"V2L = map v2 L"
    hence v2l_k:  "length V2L = k" using Trp by force
    hence v2l_ss: "sdistinct V2L" using Trp(2) v2lp f_prop11 by simp
    hence         "cup k V2L" using f_prop4 v2lp v2l_k f_prop12 by blast
    have v2l_gp:  "general_pos (set V2L)" using f_prop6 Trp(2)f_prop11 
      by (simp add: gpos_generalpos v2lp)
    have v2l_ssgp:"sdistinct(sorted_list_of_set (set V2L))" using v2l_ss
      by (simp add: distinct_map)
    have  "(\<forall>xs. (set xs \<subseteq> set V2L) \<longrightarrow> \<not>(cap 3 xs \<or> cup (Suc k) xs))"
    proof-
      {
        fix xs
        assume xsp:"set xs \<subseteq> set V2L"
        hence "length xs > k \<Longrightarrow> \<not>sdistinct xs" using v2l_k
          by (metis List.finite_set card_mono distinct_card distinct_map linorder_not_less v2l_ss)
        hence 1:"\<not> cup (Suc k) xs" using cup_def by force
        have "\<not> cap 3 xs"
        proof(cases "length xs = 3 \<and> sdistinct xs")
          case True
          hence "length xs = 3" by simp
          then obtain a b c where xs3: "xs = [a,b,c]" using xsp
            by (smt (verit, best) List.finite_set True distinct.simps(2) distinct_map length_0_conv length_Cons
                nat.inject nat.simps(3) numeral_3_eq_3 set_empty sorted_list_of_set.idem_if_sorted_distinct
                sorted_list_of_set.sorted_sorted_key_list_of_set sorted_list_of_set_nonempty)
          then obtain u v w where uvw: "a = v2 u" "b = v2 v" "c = v2 w" using xsp v2lp by auto
          hence "sdistinct[v2 u, v2 v, v2 w]" using xsp xs3 True by simp
          hence "cup3 a b c" using f_prop4 uvw f_prop10 by presburger
          thus "\<not>(cap 3 xs)" using True exactly_one_true cap_def xs3 by (metis list_check.simps(4))
          text\<open>When the length xs \<noteq> 3 then xs can not be a 3-cap from definition trivially.\<close>
        qed(auto simp add: cap_def) 
        hence "set xs \<subseteq> set V2L \<and> sdistinct xs \<longrightarrow> \<not> (cap 3 xs \<or> cup (Suc k) xs)" using 1
          by blast
      }
      thus ?thesis
        by (simp add: cap_def cup_def)
    qed
    hence "(\<forall>xs. (set xs \<subseteq> set V2L) \<longrightarrow> \<not>(cap 3 xs \<or> cup (Suc k) xs))" by simp
    thus ?thesis using v2l_gp Trp(1) v2l_ss v2l_k
      by (metis distinct_card distinct_map v2l_ssgp)
    qed
  thus ?thesis using min_conv_lower by simp
qed

theorem min_conv_base:
  "min_conv 3 k = k"
proof(induction k)
  case 0
  have "cap 0 []" by (simp add: cap_def) 
  thus ?case unfolding min_conv_def using lcheck_len2_T 
    by (smt (verit, ccfv_SIG) cup_def distinct.simps(1) empty_subsetI inf_upper le_zero_eq list.simps(8) list.size(3) list_check.simps(1) mem_Collect_eq set_empty2
        sorted_wrt.simps(1))
next
  case (Suc k)
  hence "min_conv 3 (Suc k) \<le> Suc k" 
    using min_conv_def[of "3" "Suc k"] inf_upper abc by auto
  moreover have "min_conv 3 (Suc k) \<ge> Suc k"  using Suc_leI min_conv_3_k_bnd
    by presburger
  ultimately show ?case by simp
qed


end