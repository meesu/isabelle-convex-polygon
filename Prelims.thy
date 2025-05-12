theory Prelims
  imports Definitions

begin

lemma subseq_rev:
  "subseq xs ys \<Longrightarrow> subseq (rev xs) (rev ys)"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case sorry
qed

lemma inf_subset_bounds:
  assumes "X \<noteq> {}" and "(X :: nat set) \<subseteq> (Y :: nat set)"
  shows "Inf Y \<le> Inf X"
  by (simp add: assms(1,2) cInf_superset_mono)

lemma inf_upper:
  "x \<in> (S::nat set) \<longrightarrow> Inf S \<le> x"
  by (simp add: wellorder_Inf_le1)

lemma dst_set_card2_ne:
  fixes   S :: "R2 set"
  assumes "card S \<ge> 2"
  shows   "{(u,v)|u v. u \<in> S \<and> v \<in> S \<and> u < v}  \<noteq>  {}" 
          (is "?Spr \<noteq> {}")
proof-
  obtain s1 s2 where "s1\<in>S" "s2\<in>S" "s1<s2" using assms
    by (meson card_2_iff' ex_card linorder_less_linear subset_iff)
  hence "(s1, s2) \<in> ?Spr" by blast
  thus "?Spr \<noteq> {}" by force
qed

lemma width_non_zero:
  fixes S :: "real set"
  assumes "S \<noteq> {}" and "finite S"
  shows   "Max S - Min S \<ge> 0"
  using assms Min_in by fastforce

lemma slope_div_ord:
  fixes n1 n2 d1 d2 :: real
  assumes "n1 \<le> n2" and "n1 > 0"
      and "d1 \<ge> d2" and "d2 > 0"
  shows   "n1 / d1 \<le> n2 / d2" 
  using assms by (simp add: divide_mono)

lemma finite_set_pr:
  assumes "finite S"
  shows   "finite {(u,v)|u v. u \<in> S \<and> v \<in> S \<and> u < v}"
          (is "finite ?Spr")
proof-
  have "finite (S\<times>S)" using assms by blast
  moreover have "?Spr \<subseteq> S\<times>S" by blast
  ultimately show ?thesis by (meson rev_finite_subset)
qed


(* ALERT: the assumption values are not well defined in isabelle
lemma "\<lbrakk>sortedStrict ([]); (1,2::real) < (hd ([]))\<rbrakk> \<Longrightarrow> sortedStrict [(1,2)]" by simp
value "sortedStrict(Nil)"
*)

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


lemma ind_seq_subseq:
  assumes "a < b" "b < c" "c < length xs" and "sdistinct xs"
  shows   "sdistinct [xs!a, xs!b, xs!c]"
proof
  show "distinct (map fst [xs ! a, xs ! b, xs ! c])" using assms(1,2,3,4)
    by (smt (verit, ccfv_threshold) distinct_singleton dual_order.trans nth_map
        le_eq_less_or_eq distinct_conv_nth distinct_length_2_or_more list.simps(8,9)
        length_map verit_comp_simplify1(3))
next
  show "sorted [xs ! a, xs ! b, xs ! c]"
    by (meson assms(1,2,3,4) less_or_eq_imp_le order.strict_trans1 sorted1 sorted2 sorted_nth_mono)
qed

lemma subseq_index:
  fixes xs :: "R2 list"
  assumes "subseq ys xs"
  shows "\<exists> idx. 
    set idx \<subseteq> {..<length xs} \<and> 
    ys = map (\<lambda> id. xs!id) idx \<and>
    length idx = length ys \<and>
    sorted_wrt (<) idx"
  using assms
proof(induction ys arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  hence "subseq ys xs" by (metis subseq_Cons')
  obtain xsp xss where a_xs:"xs = xsp@a#xss" "subseq ys xss" using Cons(2) list_emb_ConsD
    by (metis (full_types, opaque_lifting))
  have "xs = (xsp@[a])@xss" using a_xs(1) by simp
  hence id_tr:"\<forall>z < length xss. xss!z = xs!(1 + length xsp + z)" using a_xs(1)
    by (metis add_Suc_shift nth_Cons_Suc nth_append_length_plus plus_1_eq_Suc)

  then obtain idx where idx:
          "set idx \<subseteq> {..<length xss}"
          "ys = map ((!) xss) idx"
          "length idx = length ys"
          "sorted_wrt (<) idx"
    using Cons.IH a_xs by blast

  define idxsa where idxsa: "idxsa = (map (\<lambda>n. 1 + length xsp + n) idx)"
  have idxsa_s:"set idxsa \<subseteq> {..<(1 + length xsp + length xss)}" 
    using idxsa a_xs(1) idx(1) by auto
  have    "sorted_wrt (<) idxsa" using idx(4) idxsa by (simp add: sorted_wrt_iff_nth_less)
  hence 4:"sorted_wrt (<) ((length xsp)#idxsa)" using idxsa by simp 
  hence ys_idxs: "ys = map ((!) xs) idxsa"
    using idx(2) idxsa by (simp add: a_xs(1) nth_append)
  hence aind:"xs!length xsp = a" using a_xs by simp
  hence 2:"(a#ys) = map ((!) xs) ((length xsp)#idxsa)" using ys_idxs by simp
  have  3:"length (a#ys) = length ((length xsp)#idxsa)" using idx(3) idxsa by simp
  have 1:"set ((length xsp)#idxsa) \<subseteq> {..<length xs}"  using idxsa_s a_xs(1) by auto
  then show ?case using 1 2 3 4 by metis
qed

lemma subseq_index3:
  fixes xs :: "R2 list"
  assumes "subseq [a,b,c] xs"
  shows   "\<exists> i j k. i<j \<and> j<k \<and> k<length xs \<and> a = xs!i \<and> b = xs!j \<and> c = xs!k"
proof-
  obtain idx where idx:
    "set idx \<subseteq> {..<length xs}" 
    "[a,b,c] = map (\<lambda> id. xs!id) idx" 
    "sorted_wrt (<) idx" 
    "length idx = 3"
    using assms subseq_index
    by (metis length_Cons list.size(3) numeral_3_eq_3)
  obtain a b c where ijk: "idx = Cons a (Cons b (Cons c Nil))" 
    using idx(4) numeral_3_eq_3 length_0_conv Suc_length_conv length_Suc_conv by smt
  hence 1:"c < length xs" using idx ijk
    by (meson lessThan_iff list.set_intros(1) set_subset_Cons subset_code(1))
  thus ?thesis using idx(2,3) "1" ijk by auto
qed

lemma sdistinct_subseq:
  fixes   xs ys :: "R2 list"
  assumes "subseq xs ys" and "sdistinct ys"
  shows   "sdistinct xs"
  using assms
proof(induction ys)
  case (list_emb_Nil ys)
  then show ?case by simp
next
  case (list_emb_Cons xs ys y)
  then show ?case by simp
next
  case (list_emb_Cons2 x y xs ys)
  hence F1: "sdistinct xs" by simp
  then show ?case
  proof
    assume asm: "distinct (map fst xs)" "sorted xs"
    have "fst x \<notin> set (map fst ys)"
      using list_emb_Cons2.hyps(1)
        list_emb_Cons2.prems
      by auto
    hence "fst x \<notin> set (map fst xs)"
      by (metis (full_types, opaque_lifting)
          list_emb_Cons2.hyps(2)
          list_emb_set
          subseq_map)
    hence 1:"distinct (map fst (x#xs))"
      by (simp add: asm(1))
    have "((\<forall>y \<in> set ys. x\<le>y) \<and> sorted ys)"
      using list_emb_Cons2.hyps(1)
        list_emb_Cons2.prems
        sorted_simps(2)
      by blast
    hence "((\<forall>y \<in> set xs. x\<le>y) \<and> sorted xs)"
      using asm(2)
        list_emb_Cons2.hyps(2)
        list_emb_set
      by fastforce
    hence "sorted (x#xs)"
      by simp
    thus ?thesis using 1 by simp
  qed
qed


corollary sdistinct_subl:
  fixes   X Y :: "R2 list"
  assumes "sublist X Y" and "sdistinct Y"
  shows   "sdistinct X"
  using assms sdistinct_subseq by blast

lemma sdistinct_sub:
  fixes   A B :: "R2 set"
  assumes "finite B" and "A \<subseteq> B" and "sdistinct(sorted_list_of_set B)"
  shows   "sdistinct(sorted_list_of_set A)"
proof-
  have "subseq (sorted_list_of_set A) (sorted_list_of_set B)" using assms(1,2)
  proof(induction "sorted_list_of_set B" arbitrary: A B)
    case Nil
    hence "B = {}"
      by (metis sorted_list_of_set.sorted_key_list_of_set_eq_Nil_iff)
    hence "A = {}" using Nil by simp
    then show ?case by simp
  next
    case (Cons a x)
    define Ba where "Ba \<equiv> B - {a}"
    hence 1:"x = sorted_list_of_set(Ba)" using Cons(2,3,4)
      by (metis remove1.simps(2) sorted_list_of_set.sorted_key_list_of_set_remove)
    have 2: "finite Ba" using Cons(3) Ba_def by blast
    hence 3: "A - {a} \<subseteq> Ba" using Ba_def Cons(4) by blast
    hence 4:"a \<in> A \<Longrightarrow> subseq (sorted_list_of_set (A-{a})) (sorted_list_of_set Ba)"
      using Cons 1 2 by simp
    have 5:"a \<in> A \<Longrightarrow> a#(sorted_list_of_set (A-{a})) = sorted_list_of_set A"
      by (smt (verit, best) Cons.hyps(2) Cons.prems(1,2) Min_in Min_le empty_iff finite_has_minimal2 
          finite_subset list.inject sorted_list_of_set_nonempty subset_iff)

    hence 6:"a \<in> A \<Longrightarrow> subseq (sorted_list_of_set A) (sorted_list_of_set B)"
      by (metis "1" "4" Cons.hyps(2) subseq_Cons2)
    have "a\<notin>A \<Longrightarrow> ?case" using Cons "1" "2" "3"
      by (metis Diff_empty Diff_insert0 list_emb_Cons)
    thus ?case using "6" by auto
  qed
  thus "sdistinct ((sorted_list_of_set A))" 
    using sdistinct_subseq assms by simp
qed


(* cross cup etc *)
lemma ex_equiv_minconv:
  " (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs)) \<longrightarrow>
    (\<exists>xs. (set xs \<subseteq> S \<and> (sortedStrict xs)) \<longrightarrow> (cap k xs \<or> cup l xs))"
  by blast

lemma cross3_commutation_12[simp]: "cross3 x y z = 0 \<longrightarrow> cross3 y x z = 0"
  unfolding cross3_def by argo

lemma cross3_commutation_23[simp]: "cross3 x y z = 0 \<longrightarrow> cross3 x z y = 0"
  unfolding cross3_def by argo

lemma cross3_non0_distinct: "cross3 a b c \<noteq> 0 \<longrightarrow> distinct [a,b,c]" 
  unfolding cross3_def 
  by (metis cross3_commutation_23 cross3_def diff_self distinct_length_2_or_more
      distinct_singleton mult_zero_left mult_zero_right) 

lemma cap_reduct:
  assumes "cap (k+1) (a#xs)"
  shows "cap k xs"
  using assms add_left_cancel length_Cons list.distinct(1) list.inject list_check.elims(2)
  unfolding cap_def by fastforce

lemma cup_reduct:
  assumes "cup (k+1) (a#xs)"
  shows "cup k xs"
  using assms add_left_cancel length_Cons list.distinct(1) list.inject list_check.elims(2)
  unfolding cup_def by fastforce

lemma  card_of_s:
  assumes "set xs \<subseteq> S" "cap k xs" "distinct xs" "finite S"
  shows "card S \<ge> k"
  by (metis assms cap_def card_mono distinct_card)

lemma assumes "(X::nat set) \<noteq> {}" 
        shows "\<exists>S \<in> X. Inf X = S"
  using assms 
  by (simp add: Inf_nat_def1)

lemma fixes S
      assumes "finite S"
      shows "\<exists>xs.  length xs = card S \<and> set xs = S"
  using assms 
  by (metis distinct_card finite_distinct_list)

lemma set2list:
  assumes "finite (S :: R2 set)"
  shows   "\<exists>!xs. set xs = S \<and> sortedStrict xs \<and> distinct xs \<and> length xs = card S"
  using finite_sorted_distinct_unique[of "S"] strict_sorted_iff distinct_card assms
  by metis

lemma exactly_one_true:
  assumes "A = collinear3 a b c" and "B = cap3 a b c" and "C = cup3 a b c"
  shows "(A \<or> B \<or> C) \<and> ((\<not>A \<and> \<not>B) \<or> (\<not>B \<and> \<not>C) \<or> (\<not>C \<and> \<not>A))"
  using assms unfolding collinear3_def cap3_def cup3_def by linarith

lemma lcheck_len2_T:
  assumes "length P \<le> 2" and "sdistinct P" shows "list_check f P"
proof(cases "length P = 2")
  case True
  hence "\<exists>x y. P=[x,y] \<and> sdistinct [x,y]" using assms(2)
    by (metis (no_types, lifting) One_nat_def Suc_1  length_0_conv length_Suc_conv)
  then show ?thesis using list_check.simps(3) by fastforce
next
  case False
  hence "(P = []) \<or> (\<exists>x. P=[x])"
    by (metis assms(1) length_0_conv length_Suc_conv less_2_cases_iff nat_less_le)
  then show ?thesis by fastforce
qed

lemma bad3_from_bad:
  assumes "sdistinct P" and "\<not> list_check cc P"
  shows   "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cc a b c"
  using assms
proof(induction "length P" arbitrary: P)
  case (Suc x)
  then show ?case
  proof(cases "length P \<le> 2")
    case False
    hence "\<exists>a u v rest. P = (a#u#v#rest)" using Suc(2) Suc.prems(2) assms(1) list.size(3)
      by (metis One_nat_def Suc_1 bot_nat_0.extremum length_Cons list.exhaust not_less_eq_eq)
    then obtain a u v rest where aP: "P = (a#u#v#rest)" by blast
    hence "\<not> cc a u v \<or> \<not> list_check cc (u#v#rest)" using Suc by simp
    then show ?thesis
    proof
      assume "\<not> cc a u v"
      thus "\<exists>a b c. sublist [a, b, c] P \<and> \<not> cc a b c" using aP
        by (metis append_Cons append_Nil sublist_append_rightI)
    next
      assume "\<not> list_check cc (u#v#rest)"
      moreover have "length (u#v#rest) = x" using aP Suc(2) by simp
      moreover have "sdistinct (u#v#rest)" using Suc(3) aP by simp
      ultimately have "\<exists>a b c. sublist [a, b, c] (u#v#rest) \<and> \<not> cc a b c" using Suc(1) by blast
      thus "\<exists>a b c. sublist [a, b, c] P \<and> \<not> cc a b c" using aP Suc by (meson sublist_Cons_right)
    qed
  qed(metis lcheck_len2_T)
qed(auto)

lemma get_cup_from_bad_cap:
  assumes "sdistinct P" and "\<not> cap (length P) P"
  shows "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cap3 a b c"
  using bad3_from_bad assms(1,2) cap_def
  by blast

lemma get_cap_from_bad_cup:
  assumes "sdistinct P" and "\<not> cup (length P) P"
  shows "\<exists>a b c. (sublist [a,b,c] P) \<and> \<not> cup3 a b c"
  using bad3_from_bad assms(1,2) cup_def strict_sorted_iff by blast

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

end