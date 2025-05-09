theory Invariants
  imports Definitions GeneralPosition3

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

value "map uminus [1,2,3::real]"

lemma sdistinct_rev_map_refl1:
  assumes "sdistinct L"
  shows   "sdistinct (rev (map reflect L))"
proof-
  have 1:"distinct (map fst L)" using assms by simp
  have 2:"distinct (map reflect L)" using assms
    by (simp add: distinct_map)
  hence "distinct (map fst (map reflect L))" using assms 1 2
    by (metis (no_types, lifting) ext comp_def distinct_map fst_uminus inj_uminus list.map_comp)
  thus "sdistinct (rev (map reflect L))" using assms
    by (metis distinct_map distinct_rev set_rev sorted_neg)
qed

lemma sdistinct_rev_map_refl:
  "sdistinct L \<longleftrightarrow> sdistinct (rev (map reflect L))"
  using sdistinct_rev_map_refl1
  by (metis implm_rev_reflect_inv)

lemma sdistinct_refl_set:
  "sdistinct(sorted_list_of_set S) \<longleftrightarrow> sdistinct (sorted_list_of_set (reflect ` S))"
  using sdistinct_rev_map_refl
proof -
  have "0 = card S \<longrightarrow> sdistinct (sorted_list_of_set S) = sdistinct (sorted_list_of_set (reflect ` S)) \<or> distinct (map fst (sorted_list_of_set (reflect ` S))) \<and> distinct (map fst (sorted_list_of_set S))"
    by (metis bot_nat_0.extremum card_neg card_seteq empty_subsetI sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.sorted_key_list_of_set_empty)
  then show ?thesis
    by (metis (no_types) card.infinite card_neg distinct_map list.set_map sdistinct_rev_map_refl set_rev sorted_list_of_set.distinct_sorted_key_list_of_set sorted_list_of_set.set_sorted_key_list_of_set sorted_list_of_set.sorted_sorted_key_list_of_set sortedstrict_neg strict_sorted_iff)
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
    hence "sdistinct (a#xs)" unfolding cap_def by argo
    hence 1:"sdistinct (rev (map reflect (a # xs)))" using sdistinct_rev_map_refl by blast
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
    hence "sdistinct (rev (map reflect (a#xs)))" unfolding cup_def by argo
    hence 1:"sdistinct (a # xs)" using sdistinct_rev_map_refl by blast
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

lemma min_conv_sets_eq:
    shows "{n :: nat. (\<forall>S :: R2 set. (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs)))}
         = {n :: nat. (\<forall>S :: R2 set. (card S \<ge> n \<and> general_pos S \<and> sdistinct(sorted_list_of_set S))
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap l xs \<or> cup k xs)))}"
 (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix x 
    assume x_in:"x \<in> ?P"
    have  "\<forall>S :: R2 set. card S \<ge> x \<and> general_pos S \<and> sdistinct(sorted_list_of_set S)
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> (reflect ` S) \<and> sdistinct xs \<and> (cap l xs \<or> cup k xs))"
      by (smt (verit, best) cap_def cap_orig_refl_rev cup_def general_pos_neg_neg id_apply image_mono image_set mem_Collect_eq o_def rev_reflect_inv set_rev x_in)
    hence "\<forall>S :: R2 set. card S \<ge> x \<and> general_pos S \<and> sdistinct(sorted_list_of_set S)
                 \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap l xs \<or> cup k xs))" 
      using card_neg general_pos_neg neg_neg sdistinct_refl_set
      by (metis (no_types, lifting) eq_id_iff image_comp image_ident)
    thus "x \<in> ?Q" by blast
  qed
next
  show "?Q \<subseteq> ?P"
  proof
    fix x
    assume x_in:"x \<in> ?Q"
    have "\<forall>S :: R2 set. card S \<ge> x \<and> general_pos S \<and> sdistinct(sorted_list_of_set S)
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> (reflect ` S) \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs))"
      by (smt (verit, best) cap_def cap_orig_refl_rev cup_def general_pos_neg_neg id_apply image_mono image_set mem_Collect_eq o_def rev_reflect_inv set_rev x_in)
    hence "\<forall>S :: R2 set. card S \<ge> x \<and> general_pos S \<and> sdistinct(sorted_list_of_set S)
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> sdistinct xs \<and> (cap k xs \<or> cup l xs))" 
      using card_neg general_pos_neg neg_neg sdistinct_refl_set
      by (metis (no_types, lifting) eq_id_iff image_comp image_ident)
      thus "x \<in> ?P" by blast
  qed
qed

lemma min_conv_arg_swap: "min_conv k l = min_conv l k"
  unfolding min_conv_def using min_conv_sets_eq by simp


(* translation invariants *)
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

lemma translated_sdistinct:
  assumes "sdistinct L"
  shows   "sdistinct (map (\<lambda>p. p+t) L)" using assms distinct_fst_translated
  by (metis prod_addright_le sorted_wrt_map_mono) 

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
  have F2: "length (a#xs) = k" using Cons(2) cup_def by simp
  hence F3: "length (map (\<lambda>p. p + t) (a#xs)) = k" by simp
  have F4: "sdistinct (map (\<lambda>p. p + t) (a#xs))" using translated_sdistinct Cons(2) cup_def
    by blast
  then show ?case
  proof(cases "length (map (\<lambda>p. p+t) (a#xs)) \<le> 2")
    case True
    then show ?thesis using F3 lcheck_len2_T
      using F4 cup_def by blast
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
      using F3 F4 cup_def list.simps(9) list_check.simps(4) xsp by force
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
  have F2: "length (a#xs) = k" using Cons(2) cap_def by simp
  hence F3: "length (map (\<lambda>p. p + t) (a#xs)) = k" by simp
  have F4: "sdistinct (map (\<lambda>p. p + t) (a#xs))" using translated_sdistinct Cons(2) cap_def
    by blast
  then show ?case
  proof(cases "length (map (\<lambda>p. p+t) (a#xs)) \<le> 2")
    case True
    then show ?thesis using F3 lcheck_len2_T
      using F4 cap_def by blast
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
      using F3 F4 cap_def list.simps(9) list_check.simps(4) xsp by force
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
      and "\<forall>xs. set xs \<subseteq> S \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs)" 
      and "St = (\<lambda> p. p + t) ` S"   
    
    shows "card St = n \<and> general_pos St \<and> sdistinct(sorted_list_of_set St) \<and>
           (\<forall>xs. set xs \<subseteq> St \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs))"
proof-
  have P1:"card St = n" using bij_tr bij_def assms(1,5)
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
  hence P2:"general_pos St" using gpos_generalpos by simp

  have 6:"distinct (map fst (sorted_list_of_set S))" using assms(3) by simp
  have 8:"distinct (map fst (map (\<lambda> p. p + t) (sorted_list_of_set S)))" 
    using 6 distinct_fst_translated by blast
  hence "distinct (map fst (sorted_list_of_set ((\<lambda> p. p + t) ` S)))" 
    using map_sorted_list_set 8 by simp
  hence P3:"sdistinct(sorted_list_of_set St)" using assms(3, 5) by simp

  have "\<forall>xs. set xs \<subseteq> S \<longrightarrow> 
        \<not>(cap k (map (\<lambda> p. p + t) xs) \<or> cup l (map (\<lambda> p. p + t) xs))" 
    using translated_cup_eq translated_cap_eq
    by (meson assms(4) cap_def cup_def)
  hence 9:"\<forall>xs. \<forall>ys. set xs \<subseteq> S \<and> (ys = map (\<lambda>p. p+t) xs) 
        \<longrightarrow> \<not>(cap k ys \<or> cup l ys)" by blast
  hence "\<forall>xs. \<forall>ys. set ys \<subseteq> ((\<lambda>p. p+t) ` S) \<and> (ys = map (\<lambda>p. p+t) xs) 
        \<longrightarrow> \<not>(cap k ys \<or> cup l ys)"
    by (simp add: image_iff image_subset_iff subsetI)
  hence "\<forall>xs. set xs \<subseteq> St \<and> sdistinct xs \<longrightarrow> \<not>(cap k xs \<or> cup l xs)"
    using assms(5) 9
    by (metis (no_types, lifting) diff_add_cancel ex_map_conv)
  thus ?thesis using P1 P2 P3 by simp
qed


lemma shift_set_above_c2:
  fixes S1 S2 :: "R2 set"

  assumes "distinct (map fst (sorted_list_of_set S1))" 
      and "finite S1"
      and "card S1 \<ge> 2"

      and "distinct (map fst (sorted_list_of_set S2))"
      and "finite S2"
      and "card S2 \<ge> 2"

    shows "\<exists>t. \<exists>S2t.
              ( S2t = (\<lambda>p. p + t) ` S2 \<and>
               (\<forall>x\<in>S1. \<forall>y\<in>S2t. fst x < fst y) \<and>
               (\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2t.  x < y \<longrightarrow> slope x y < slope y z) \<and>
               (\<forall>a\<in>S1. \<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope a b > slope b c) )"
proof-
  define s1_minx where "s1_minx = Min (fst ` S1)"
  define s1_maxx where "s1_maxx = Max (fst ` S1)"
  define s1_maxy where "s1_maxy = Max (snd ` S1)"

  define s2_miny where "s2_miny = Min (snd ` S2)"
  define s2_minx where "s2_minx = Min (fst ` S2)"
  define s2_maxx where "s2_maxx = Max (fst ` S2)"
  define w1      where "w1   = s1_maxx - s1_minx"
  define w2      where "w2   = s2_maxx - s2_minx"

  define S1pr where "S1pr = {(u,v)|u v. u \<in> S1 \<and> v \<in> S1 \<and> u < v}"
  define S2pr where "S2pr = {(u,v)|u v. u \<in> S2 \<and> v \<in> S2 \<and> u < v}"

  have s1pr_fin: "finite S1pr" using assms(2) S1pr_def finite_set_pr by fast
  have s2pr_fin: "finite S2pr" using assms(5) S2pr_def finite_set_pr by fast
  have s1pr_ne:   "S1pr \<noteq> {}" using assms(1,3) dst_set_card2_ne S1pr_def by blast
  have s2pr_ne:   "S2pr \<noteq> {}" using assms(4,6) dst_set_card2_ne S2pr_def by blast

  have w1_pos  : "w1 \<ge> 0" using w1_def assms(2,3) s1_maxx_def s1_minx_def width_non_zero
    by (metis card.empty finite_imageI image_is_empty not_numeral_le_zero)
  have w2_pos  : "w2 \<ge> 0" using w2_def assms(5,6) s2_maxx_def s2_minx_def width_non_zero
    by (metis card.empty finite_imageI image_is_empty not_numeral_le_zero)

  text \<open>\<close>
  define tx where "tx = -s2_minx + s1_maxx + 1"
  define ty1 where
    "ty1 = max s1_maxy (MAX (a,b) \<in> S1pr. snd b + (slope a b) * ((s1_maxx + 1) + w2 - fst b))"
  define ty2 where 
    "ty2 =  max s1_maxy 
      (MAX (b,c) \<in> S2pr. s1_maxy + s2_miny - snd b + (slope (b+(tx,0)) (c+(tx,0)))*(fst b+tx-s1_minx))"

  define ty where "ty = max ty1 ty2"
  define t where "t = (-s2_minx + s1_maxx + 1, -s2_miny + ty + 1)"
  define S2t where "S2t = (\<lambda>p. p + t) ` S2"   (is "_ = ?tr ` _")

  text \<open>Properties of max function follow.\<close>
  have m1: "ty \<ge> ty1" "ty \<ge> ty2" using ty_def by simp+

  text \<open>The result r1 below is obtained by translating all the points of S2 along the x-axis
        after the point in S1 with highest x-coordinate.\<close>
  have f1r1:"\<forall>x\<in>S1. fst x < s1_maxx + 1" using s1_maxx_def
    by (smt (verit, best) Max_ge assms(2) finite_imageI image_eqI)
  have f2r1:"\<forall>y\<in>S2t. s1_maxx + 1 \<le> fst y" using s2_minx_def S2t_def t_def
    using assms(5) by auto
  hence r1:"(\<forall>x\<in>S1. \<forall>y\<in>S2t. fst x < fst y)" using f1r1 f2r1 by fastforce

  text \<open>We chose ty1 in such a way that the lower right corner of bounding box of S2 is above all
        the lines passing through point pairs in S1.\<close>
  have f0r2:"\<forall>a\<in>S1. \<forall>b\<in>S1. a < b \<longrightarrow> slope a b < slope b (s1_maxx+1 + w2, ty1+1)"
  proof(rule+)
    fix a b assume asm:"a \<in> S1" "b \<in> S1" "a < b"
    have f2:"(a,b) \<in> S1pr" using asm S1pr_def by blast
    have "ty1 \<ge> (MAX (a,b) \<in> S1pr. snd b + (slope a b) * (s1_maxx + 1 + w2 - fst b))"
      using ty1_def by argo
    hence "ty1 + 1 > snd b + ((slope a b) * (s1_maxx + 1 + w2 - fst b))"
      using f2 s1pr_ne s1pr_fin Max_ge finite_imageI pair_imageI
      by (smt (verit, best))
    hence "slope a b < (ty1 + 1 - snd b) / (s1_maxx + 1 + w2 - fst b)"
     using f1r1 asm divide_diff_eq_iff divide_pos_pos s1_maxx_def w2_pos by smt
    thus "slope a b < slope b (s1_maxx+1 + w2, ty1+1)" using slope_def
      by simp
  qed

  text \<open>We show that the slope of any point y in S1 to the lower left corner of bounding box of S2t is at most the slope to any other point in S2t.\<close>
  have "\<forall>y\<in>S1. \<forall>z\<in>S2t. y < z \<longrightarrow> slope y (s1_maxx+1 + w2, ty1+1) \<le> slope y z"
  proof(rule+)
    fix y z assume asm:"y \<in> S1" "z\<in>S2t" "y<z"
    then obtain z2 
      where z2: "z2 \<in> S2" "z = (\<lambda>p. p + t) z2"
      using S2t_def t_def by blast
 
    have fx:"snd (?tr z2) \<ge> ty + 1" using s2_miny_def asm ty_def t_def z2(1) assms(5)
      by simp
    moreover have "... \<ge> s1_maxy" using m1(1) ty1_def calculation by linarith
    moreover have "... \<ge> snd y" using asm(1) assms(2) s1_maxy_def
      by (smt (verit) Max_ge calculation(2) finite_imageI imageI)
    ultimately have 0:"snd (?tr z2) - snd y \<ge> 0" using ty1_def by argo

    have 1:"snd (?tr z2) - snd y  \<ge> ty1 + 1 - snd y" 
      using fx assms s2_miny_def z2(1) t_def m1(1) by argo
    have 2:"fst (?tr z2) - fst y \<le> s1_maxx+1+w2 - fst y"
      by (simp add: assms s2_maxx_def z2(1) w2_def t_def)
    have 3: "(fst (?tr z2) - fst y) > 0" using asm(1,2) r1 z2(2) by fastforce
    show "slope y (s1_maxx + 1 + w2, ty1 + 1) \<le> slope y z" 
      using 0 1 2 3 slope_def slope_div_ord
      by (metis frac_le fst_eqD snd_eqD z2(2))
  qed
  hence r2:"\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2t. x < y \<longrightarrow> slope x y < slope y z"
    using f0r2 r1 by (smt (verit, best) prod_less_def)

  text \<open>We now apply the bounding box technique on S1. We make sure the upper left corner of bounding box of S1 is below the max slope in S2 after shifting.\<close>
  have f0r3:"\<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope (s1_minx, s1_maxy) b > slope b c"
  proof(rule+)
    fix b c assume asm:"b \<in> S2t" "c \<in> S2t" "b < c"
    then obtain b2 c2 where b2c2: "b2\<in>S2" "b = b2 + t" "c2\<in>S2" "c = c2 + t"
      using S2t_def by blast
    have f2:"(b2,c2) \<in> S2pr" using asm S2pr_def by (metis (mono_tags, lifting) b2c2(1,2,3,4) linorder_not_less mem_Collect_eq prod_addright_le)
    have f3:"slope b c = slope (b2+(tx,0)) (c2+(tx,0))" by (simp add: b2c2(2,4) slope_def)
    have "ty \<ge> 
      (MAX (b,c) \<in> S2pr. s1_maxy + s2_miny - snd b +(slope (b+(tx,0)) (c+(tx,0)))*(fst b+tx-s1_minx))" 
      using ty_def ty2_def f2 m1 by fastforce
    hence "ty \<ge> s1_maxy + s2_miny - snd b2 + (slope (b2+(tx,0)) (c2+(tx,0)))*(fst b2 + tx-s1_minx)"
      using f2 s2pr_fin s2pr_ne by auto
    hence "ty + 1 > s1_maxy + s2_miny - snd b2 + (slope (b2+(tx,0)) (c2+(tx,0)))*(fst b2+tx-s1_minx)"
      by linarith
    hence "slope b c < (snd b - s1_maxy) / (fst b - s1_minx)" 
      using f3 asm(1) b2c2(2) f2r1 less_divide_eq t_def tx_def w1_def w1_pos by fastforce
    thus "slope (s1_minx, s1_maxy) b > slope b c" using slope_def by simp
  qed

  text \<open>Next we show that the slope across sets S1 and S2t is at least the slope of upper left corner to any point in the set S2t.\<close>
  have "\<forall>a\<in>S1. \<forall>b\<in>S2t. a < b \<longrightarrow> slope a b \<ge> slope (s1_minx, s1_maxy) b"
  proof(rule+)
    fix a b assume asm:"a \<in> S1" "b\<in>S2t" "a<b"
    then obtain b2 where b2: "b2 \<in> S2" "b = ?tr b2" using S2t_def t_def by blast
 
    have fx:"snd b \<ge> ty + 1" using s2_miny_def t_def b2 assms(5) by simp
    moreover have "... \<ge> s1_maxy" using m1(1) ty1_def calculation by linarith
    ultimately have 0:"snd b - s1_maxy \<ge> 0" by argo

    have 1:"snd b - snd a  \<ge> snd b - (s1_maxy)"
      using fx assms s2_miny_def b2(1) t_def m1(1)
      by (smt (verit, del_insts) Max.coboundedI asm(1)
          finite_imageI imageI s1_maxy_def)
    have 2:"fst b - fst a \<le> fst b - (s1_minx)"  by (simp add: asm(1) assms(2) s1_minx_def)
    have 3: "(fst b - fst a) > 0"               by (simp add: asm(1,2) r1)
    show "slope a b \<ge> slope (s1_minx, s1_maxy) b" using 0 1 2 3
      by (simp add: b2(2) frac_le slope_def)
  qed
  hence "\<forall>a\<in>S1. \<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope a b > slope b c"
    using S2t_def f0r3
    by (metis order_less_le_trans prod_less_def r1)
  then show ?thesis using r1 r2 S2t_def t_def by auto
qed

lemma shift_set_above:
  fixes S1 S2 :: "R2 set"

  assumes "distinct (map fst (sorted_list_of_set S1))" 
      and "finite S1"
      and "card S1 \<ge> 1"

      and "distinct (map fst (sorted_list_of_set S2))"
      and "finite S2"
      and "card S2 \<ge> 1"

    shows "\<exists>t. \<exists>S2t.
              ( S2t = (\<lambda>p. p + t) ` S2 \<and>
               (\<forall>x\<in>S1. \<forall>y\<in>S2t. fst x < fst y) \<and>
               (\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2t.  x < y \<longrightarrow> slope x y < slope y z) \<and>
               (\<forall>a\<in>S1. \<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope a b > slope b c) )"
proof(cases "card S1 = 1 \<or> card S2 = 1")
  case Tout:True
  then show ?thesis
  proof(cases "card S1 \<noteq> 1")
    case True
    hence s2_c1:"card S2 = 1" using Tout by simp
    have s1_c2:"card S1 \<ge> 2" using assms(3) True by simp
    then obtain p2 where p2:"S2 = {p2}"
      using card_1_singletonE s2_c1 by blast

    define tx where "tx = Max (fst ` S1) + 1"
    define S1pr where "S1pr = {(u,v)|u v. u \<in> S1 \<and> v \<in> S1 \<and> u<v}"
    then obtain s1 s2 where "s1\<in>S1" "s2\<in>S1" "s1<s2" using assms s1_c2
      by (meson card_2_iff' ex_card linorder_less_linear subset_iff)
    hence "(s1, s2) \<in> S1pr" using S1pr_def by blast
    hence S1pr_nonE:"S1pr \<noteq> {}" by force
    have S1pr_fin:"finite S1pr" using S1pr_def assms(2) finite_set_pr by blast

    define ty where ty:
      "ty=(MAX (a,b) \<in> S1pr. snd b + (slope a b) * (tx - fst b)) + 1"
    define S2t where "S2t = (\<lambda>p. p + (-fst p2 + tx, -snd p2 + ty)) ` S2"
    
    have f1:"(\<forall>x\<in>S1. fst x < Max (fst ` S1) + 1)"
      by (smt (verit, best) Max_ge assms finite_imageI image_eqI)
    hence r1:"(\<forall>x\<in>S1. \<forall>y\<in>S2t. fst x < fst y)" using tx_def S2t_def p2 by auto
    
    have "\<forall>a\<in>S1. \<forall>b\<in>S1. a < b \<longrightarrow> slope a b < slope b (tx, ty)"
    proof(rule+)
      fix a b assume asm:"a \<in> S1" "b \<in> S1" "a < b"
      have f2:"(a,b) \<in> S1pr" using asm S1pr_def by blast
       have "ty-1=(MAX (a,b) \<in> S1pr. snd b + (slope a b) * (tx - fst b))"
        using ty by argo
      hence "ty - 1 \<ge> (snd b + (slope a b) * (tx - fst b))"
        using f2 S1pr_nonE S1pr_fin
        by (metis (no_types, lifting) Max_ge finite_imageI
            pair_imageI)
      hence "slope a b < (ty - snd b) / (tx - fst b)"
        by (smt (verit, ccfv_threshold) f1 asm(2) divide_diff_eq_iff divide_pos_pos tx_def)
      thus "slope a b < slope b (tx, ty)" using slope_def
        by simp
    qed
    hence r2:"\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2t. x < y \<longrightarrow> slope x y < slope y z"
      by (smt (verit, del_insts) S2t_def add_Pair imageE p2
          prod.collapse singletonD)
    have "\<forall>a\<in>S1. \<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope a b > slope b c"
      using S2t_def p2 by blast
    then show ?thesis using r1 r2 S2t_def by auto
  next
    case False
    then show ?thesis
    proof(cases "card S2 = 1") (* and card S1 = 1 *)
      case True
      then obtain s1 s2 where s1s2: "S1 = {s1}" "S2 = {s2}" using False
        by (meson card_1_singletonE)
      define S2t where "S2t = (\<lambda>p. p + (-fst s2 + fst s1 + 1, 0)) ` S2"
      have r1: "(\<forall>x\<in>S1. \<forall>y\<in>S2t. fst x < fst y)"
        by (simp add: S2t_def s1s2(1,2))
      have "(\<forall>x\<in>S1. \<forall>y\<in>S1. \<forall>z\<in>S2t. x < y \<longrightarrow> slope x y < slope y z) \<and>
            (\<forall>a\<in>S1. \<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope b c < slope a b)" 
        using s1s2 S2t_def by blast
      then show ?thesis using r1
        using S2t_def by auto
    next
      case False
      hence s2_c2: "card S2 \<ge> 2" using assms(6) by linarith
      have  s1_c1: "card S1 = 1" using False Tout by blast
      then obtain s1x s1y where s1: "S1 = {(s1x, s1y)}"
        using card_1_singletonE by (metis surj_pair)

      define s2_miny where "s2_miny = Min (snd ` S2)"
      define s2_minx where "s2_minx = Min (fst ` S2)"
      define S2pr where "S2pr = {(u,v)|u v. u \<in> S2 \<and> v \<in> S2 \<and> u < v}"

      have s2pr_fin: "finite S2pr" using assms(5) S2pr_def finite_set_pr by fast
      have s2pr_ne:   "S2pr \<noteq> {}" using assms(4,6) dst_set_card2_ne S2pr_def s2_c2 by presburger

      define tx where "tx = -s2_minx + s1x + 1"
      define ty2 where 
        "ty2 =  max s1y 
      (MAX (b,c) \<in> S2pr. s1y + s2_miny - snd b + (slope (b+(tx,0)) (c+(tx,0)))*(fst b+tx-s1x))"

      define t where "t = (-s2_minx + s1x + 1, -s2_miny + ty2 + 1)"
      define S2t where "S2t = (\<lambda>p. p + t) ` S2"   (is "_ = ?tr ` _")

      have f1r1:"\<forall>x\<in>S1. fst x < s1x + 1" using s1 by simp
      have f2r1:"\<forall>y\<in>S2t. s1x + 1 \<le> fst y" using s2_minx_def S2t_def t_def
        using assms(5) by auto
      hence r1:"(\<forall>x\<in>S1. \<forall>y\<in>S2t. fst x < fst y)" using f1r1 f2r1 by fastforce

      have "\<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope (s1x, s1y) b > slope b c"
      proof(rule+)
        fix b c assume asm:"b \<in> S2t" "c \<in> S2t" "b < c"
        then obtain b2 c2 where b2c2: "b2\<in>S2" "b = b2 + t" "c2\<in>S2" "c = c2 + t"
          using S2t_def by blast
        have f2:"(b2,c2) \<in> S2pr" using asm S2pr_def by (metis (mono_tags, lifting) b2c2(1,2,3,4) linorder_not_less mem_Collect_eq prod_addright_le)
        have f3:"slope b c = slope (b2+(tx,0)) (c2+(tx,0))" by (simp add: b2c2(2,4) slope_def)
        have "ty2 \<ge> 
          (MAX (b,c) \<in> S2pr. s1y + s2_miny - snd b +(slope (b+(tx,0)) (c+(tx,0)))*(fst b+tx-s1x))" 
          using ty2_def by fastforce
        hence "ty2 + 1 > s1y + s2_miny - snd b2 + slope b c * (fst b2+tx-s1x)"
          using f3 f2 s2pr_fin s2pr_ne by auto
        hence "slope b c < (snd b2 - s2_miny + ty2 + 1 - s1y) / (fst b2 + tx - s1x)"
          using asm(1) b2c2(2) f2r1 less_divide_eq t_def tx_def
          by fastforce
        thus "slope (s1x, s1y) b > slope b c" using slope_def t_def S2t_def
          by (smt (verit, best) b2c2(2) fst_add fst_conv snd_add
              snd_eqD tx_def)
      qed
      hence r3:"\<forall>a\<in>S1. \<forall>b\<in>S2t. \<forall>c\<in>S2t. b < c \<longrightarrow> slope a b > slope b c"
        using s1 by blast
      have r2: "\<forall>x\<in>S1.\<forall>y\<in> S1. \<forall>z\<in>S2t.  x < y \<longrightarrow> slope x y < slope y z" using s1 by blast
      show ?thesis using S2t_def r1 r2 r3 t_def
        by auto
    qed
  qed
next
  case False
  hence "card S1 \<ge> 2" "card S2 \<ge> 2"
    using assms(3,6) by fastforce+
  then show ?thesis using shift_set_above_c2 assms by presburger
qed


end