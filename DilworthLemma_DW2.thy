theory DilworthLemma_DW2 imports Main HOL.Complete_Partial_Order HOL.Relation HOL.Order_Relation
begin

context order
begin

(*Reference Paper: https://arxiv.org/pdf/1703.06133
*)


(*Pre-Req Definitions*)
abbreviation chain:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"chain ord S \<equiv> Complete_Partial_Order.chain ord S"

definition chain_on :: "'a set \<Rightarrow>  ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"(chain_on A ord S) \<longleftrightarrow>(partial_order_on A (relation_of ord A)) 
                                    \<and> (S \<subseteq> A) \<and> (chain ord S)"

definition antichain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"antichain ord S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. (ord x y \<or> ord y x) \<longrightarrow> x = y)"

definition antichain_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"(antichain_on A ord S) \<longleftrightarrow> (partial_order_on A (relation_of ord A))
                                     \<and> (S \<subseteq> A) \<and> (antichain ord S)"

definition largest_antichain_on:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"(largest_antichain_on P ord lac \<longleftrightarrow> (antichain_on P ord lac \<and> 
(\<forall> ac. antichain_on P ord ac \<longrightarrow> card ac \<le> card lac)))"



definition is_maximal:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_maximal S ord a \<longleftrightarrow>  (\<forall> x \<in> S . (ord a x \<longrightarrow> a = x))"               

definition is_minimal:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_minimal S ord a \<longleftrightarrow>  (\<forall> x \<in> S . ( ord x a \<longrightarrow> a = x))"

definition chain_cover_on:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> bool" where
"chain_cover_on S r cv \<longleftrightarrow> (\<Union> cv = S) \<and> (\<forall> x \<in> cv . chain_on S r x)"

definition antichain_cover_on:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> bool" where
"antichain_cover_on S r cv \<longleftrightarrow> (\<Union> cv = S) \<and> (\<forall> x \<in> cv . antichain_on S r x)"

definition smallest_chain_cover_on:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> bool" where
"smallest_chain_cover_on S r cv \<equiv> (chain_cover_on S r cv \<and> (\<forall> cv2. chain_cover_on S r cv2 \<longrightarrow> card cv \<le> card cv2))"


fun max_card where
"max_card S = Max (card ` S)"

fun min_card where
"min_card S = Min (card ` S)"

definition max_card_elem where
"max_card_elem S \<equiv> (SOME x . x \<in> S \<and> card x = max_card S)"

definition min_card_elem where
"min_card_elem S \<equiv> (SOME x . x \<in> S \<and> card x = min_card S)"


definition height::"'a set \<Rightarrow> nat \<Rightarrow> bool" where
"height S h \<longleftrightarrow> (partial_order_on S (relation_of (\<le>) S)) 
                    \<and> (\<nexists> x . (chain_on S (\<le>) x \<and> card x > h))
                    \<and> (\<exists> y . (chain_on S (\<le>) y \<and> card y = h))"

definition width:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
"width S ord w \<longleftrightarrow> (partial_order_on S (relation_of (\<le>) S))
                   \<and> (\<nexists> x. (antichain_on S (\<le>) x \<and> card x > w))
                   \<and> (\<exists> y . (antichain_on S (\<le>) y \<and> card y = w))"


definition maximals_set:: "'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>'a set " where
"maximals_set P ord = {x . x \<in> P \<and> is_maximal P ord x}"

definition minimals_set:: "'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>'a set " where
"minimals_set P ord = {x . x \<in> P \<and> is_minimal P ord x}"


definition p_plus :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"p_plus P ord AC = {x. x \<in> P \<and> (\<exists> y \<in> AC. ord y x)}"

definition p_minus :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"p_minus P ord AC = {x. x \<in> P \<and> (\<exists> y \<in> AC. ord x y)}"


value "(p_plus { {(1::nat)}, {2}, {1,2}, {2,3}, {1,3}, {1,3,4}, {1,2,3,4}, {1,3,5}, {1,2,3,5} } (\<subseteq>) {{1,2}, {2,3}, {1,3,4}, {1,3,5}}) \<union> (p_minus { {(1::nat)}, {2}, {1,2}, {2,3}, {1,3}, {1,3,4}, {1,2,3,4}, {1,3,5}, {1,2,3,5} } (\<subseteq>) {{1,2}, {2,3}, {1,3,4}, {1,3,5}})"


(*Theorem Statement
 In any poset, the maximum size of an antichain is equal
to the minimum number of chains in any chain cover. In other words, if cp
represents the size of a smallest chain cover of P, then width(P) = cp *)


(*Shows \<lbrakk>chain X; antichain Y; |X \<inter> Y| = 0\<rbrakk> \<Longrightarrow> X \<inter> Y = {}*)

lemma inter_nInf: assumes a1: "Complete_Partial_Order.chain (\<le>) X" 
                      and a2: "antichain (\<le>) Y"
                      and asmInf: "card (X \<inter> Y) = 0"
                    shows "X \<inter> Y = {}"
proof (rule ccontr)
  assume "X \<inter> Y \<noteq> {}"
  then obtain a b where 1:"a \<in> (X \<inter> Y)" "b \<in> (X \<inter> Y)" using asmInf by blast
  then have in_chain: "a \<in> X \<and> b \<in> X" using 1 by simp
  then have 3: "(a \<le> b) \<or> (b \<le> a)" using chain_def a1 by metis
  have in_antichain: "a \<in> Y \<and> b \<in> Y" using 1 by blast
  then have "a = b" using antichain_def a2 3 by metis
  then have "\<forall> a \<in> (X \<inter> Y). \<forall> b \<in> (X \<inter> Y). a = b" using 1 a1 a2
    by (metis IntD1 IntD2 antichain_def chain_def)
  then have "card (X \<inter> Y) = 1" using 1 a1 a2 card_def
    by (smt (verit, best) all_not_in_conv asmInf card_0_eq card_le_Suc0_iff_eq finite_if_finite_subsets_card_bdd subset_eq subset_iff)
  then have False using asmInf by presburger
  then show False .
qed

(*Shows \<lbrakk>chain X; antichain Y; X Y \<subseteq> S\<rbrakk> \<Longrightarrow> (|X \<inter> Y| = 1 \<or> X \<inter> Y = {})*)

lemma chain_antichain_inter: assumes a1: "Complete_Partial_Order.chain (\<le>) X" 
                                 and a2: "antichain (\<le>) Y"
                                 and a3: "X \<subseteq> S \<and> Y \<subseteq> S"
                               shows "(card (X \<inter> Y) = 1) \<or> ((X \<inter> Y) = {})"
proof (cases "card (X \<inter> Y) \<ge> 1")
  case True
  then obtain a b where 1:"a \<in> (X \<inter> Y)" "b \<in> (X \<inter> Y)"
    by (metis card_1_singletonE insert_subset obtain_subset_with_card_n)
  then have "a \<in> X \<and> b \<in> X" using 1 by blast
  then have 3: "(a \<le> b) \<or> (b \<le> a)" using chain_def a1 by metis
  have "a \<in> Y \<and> b \<in> Y" using 1 by blast
  then have "a = b" using a2 antichain_def 3 by metis
  then have "\<forall> a \<in> (X \<inter> Y). \<forall> b \<in> (X \<inter> Y). a = b" using 1 a1 a2
    by (metis IntD1 IntD2 antichain_def chainE)
  then have "card (X \<inter> Y) = 1" using 1 a1 a2
    by (metis One_nat_def True card.infinite card_le_Suc0_iff_eq order_class.order_antisym zero_less_one_class.zero_le_one)
  then show ?thesis by presburger
next
  case False
  then have "card (X \<inter> Y) < 1" by linarith
  then have "card (X \<inter> Y) = 0" by blast
  then have "X \<inter> Y = {}" using assms inter_nInf by blast
  then show ?thesis by force
qed

(*Shows \<lbrakk>chain X; antichain Y; X Y \<subseteq> S\<rbrakk> \<Longrightarrow> (|X \<inter> Y| = 1 \<or> X \<inter> Y = {})*)

lemma chain_antichain_card:
  assumes "X \<subseteq> S \<and> Y \<subseteq> S"
  and "chain (\<le>) X \<and> antichain (\<le>) Y"
  shows "card (X \<inter> Y) \<le> 1"
proof-
  have P1: "\<forall> x \<in> (X \<inter> Y). \<forall> y \<in> (X \<inter> Y). x = y" 
  proof-
    have "\<forall>x\<in>X. \<forall>y\<in>X. (x \<le> y) \<or> (y \<le> x)" using assms(2) chain_def by metis
    moreover have "\<forall>x\<in>Y. \<forall>y\<in>Y. (x \<le> y) \<or> (y \<le> x) \<longrightarrow> x = y" using assms(2) antichain_def by metis 
    then show ?thesis using calculation by fastforce
  qed
  then show ?thesis 
  proof(cases "card (X \<inter> Y) = 0") (*doesn't prove (X \<inter> Y) isn't infinite*)
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis using P1 assms
      by (simp add: card_eq_0_iff card_le_Suc0_iff_eq)
  qed
qed

(*2. If S is finite, there exists a finite chain-decomposition of S*)

definition chain_decomposition 
  where  
"chain_decomposition S X \<equiv> ((\<forall>x \<in> X. x \<subseteq> S) \<and> (\<forall>x \<in> X. chain_on S (\<le>) x) \<and> (\<Union> X = S) 
\<and> (\<forall> x \<in> X. \<forall> y \<in> X. x \<noteq> y \<longrightarrow> (x \<inter> y = {})))"

lemma po_restr: assumes "partial_order_on B r" 
                    and "A \<subseteq> B" 
                  shows "partial_order_on A (r \<inter> (A \<times> A))"
  using assms unfolding partial_order_on_def preorder_on_def antisym_def refl_on_def trans_def
  by (metis (no_types, lifting) IntD1 IntD2 IntI Int_lower2 inf.orderE mem_Sigma_iff)

lemma eq_restr: "(Restr (relation_of (\<le>) (insert a A)) A) = (relation_of (\<le>) A)" 
  (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix z
    assume "z \<in> ?P"
    then obtain x y where tuple: "(x, y) = z" using relation_of_def by blast
    then have 1: "(x, y) \<in> ((relation_of (\<le>) (insert a A)) \<inter> (A \<times> A))" 
      using relation_of_def
      using \<open>z \<in> Restr (relation_of (\<le>) (insert a A)) A\<close> by blast
    then have 2: "(x, y) \<in> (relation_of (\<le>) (insert a A))" by simp
    then have 3: "(x, y) \<in> (A \<times> A)" using 1 by simp
    then have "(x, y) \<in> (A \<times> A) \<and> (x \<le> y)" using relation_of_def 2
      by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    then have "(x, y) \<in> (relation_of (\<le>) A)" using relation_of_def by blast
    then show "z \<in> ?Q" using tuple by fast
  qed
next
  show "?Q \<subseteq> ?P"
  proof
    fix z
    assume asm1: "z \<in> ?Q"
    then obtain x y where tuple: "(x, y) = z" by (metis prod.collapse)
    then have 0: "(x, y) \<in> (A \<times> A) \<and> (x \<le> y)" using asm1 relation_of_def
      by (metis (mono_tags, lifting) case_prod_conv mem_Collect_eq)
    then have 1: "(x, y) \<in> (A \<times> A)" by fast
    have rel: "x \<le> y" using 0 by blast
    have "(A \<times> A) \<subseteq> ((insert a A) \<times> (insert a A))" by blast
    then have "(x, y) \<in> ((insert a A) \<times> (insert a A))" using 1 by blast
    then have "(x, y) \<in> (relation_of (\<le>) (insert a A))" using rel relation_of_def by blast
    then have "(x, y) \<in> ((relation_of (\<le>) (insert a A)) \<inter> (A \<times> A))" using 1 by fast
    then show "z \<in> ?P" using tuple by fast
  qed
qed

(*Proof by induction*)

lemma exists_cd: assumes a1: "finite S" 
                     and a2: "partial_order_on S (relation_of (\<le>) S)" 
                   shows "\<exists> X. chain_decomposition S X" 
   using assms
proof(induction rule: finite.induct)
  case emptyI
  then show ?case using assms
    by (metis Sup_empty chain_decomposition_def empty_iff)
next
  case (insertI A a)
  show ?case using assms
  proof (cases "a \<in> A")
    case True
    then have 1: "(insert a A) = A" by fast
    then have "\<exists> X. chain_decomposition A X" using insertI by simp
    then show ?thesis using 1 by auto
  next
    case False
    have subset_a: "{a} \<subseteq> (insert a A)" by simp
    have chain_a: "Complete_Partial_Order.chain (\<le>) {a}" 
      using chain_singleton chain_def by fastforce
    have subset_A: "A \<subseteq> (insert a A)" by blast
    have partial_a: "partial_order_on A ((relation_of (\<le>) (insert a A)) \<inter> (A \<times> A))"
      using po_restr[OF insertI(3) subset_A] .
    then have chain_on_A: "chain_on (insert a A) (\<le>) {a}" using chain_a partial_a
      by (simp add: chain_on_def insertI.prems)
    obtain X where chain_set: "chain_decomposition A X" 
      using insertI partial_a eq_restr by metis
    have chains_X: "\<forall> x \<in> (insert {a} X). chain_on (insert a A) (\<le>) x" 
      using subset_A chain_set chain_on_def chain_decomposition_def chain_on_A by auto
    have subsets_X: "\<forall> x \<in> (insert {a} X). x \<subseteq> (insert a A)" 
      using chain_set chain_decomposition_def subset_a by fast
    have null_inter_X: "\<forall> x \<in> X. \<forall> y \<in> X. x \<noteq> y \<longrightarrow> x \<inter> y = {}"
      using chain_set chain_decomposition_def by metis
    have "{a} \<notin> X" using False chain_set chain_decomposition_def by fastforce
    then have null_inter_a: "\<forall> x \<in> X. {a} \<inter> x = {}"
      by (metis False UnionI chain_decomposition_def chain_set inf_bot_left insert_disjoint(2))
    then have null_inter: "\<forall> x \<in> (insert {a} X). \<forall> y \<in> (insert {a} X). x \<noteq> y \<longrightarrow> x \<inter> y = {}" 
      using null_inter_X by simp
    have union: "\<Union> (insert {a} X) = (insert a A)" using chain_set
      by (metis Union_insert chain_decomposition_def insert_is_Un)
    have "chain_decomposition (insert a A) (insert {a} X)"
      using chain_decomposition_def subsets_X chains_X union null_inter by blast
    then show ?thesis by blast
  qed
qed

(*Shows that the chain decomposition of a set is a chain cover*)

lemma cd_cv: assumes "chain_decomposition P X"
               shows "chain_cover_on P (\<le>) X"
proof-
  have 1: "\<Union> X = P" using assms chain_decomposition_def by simp
  have 2: "\<forall>x \<in> X. chain_on P (\<le>) x" using assms chain_decomposition_def by simp
  show ?thesis using 1 2 chain_cover_on_def by simp
qed

(*Shows that for any finite partially ordered set, there exists a chain cover on that set*)

lemma exists_cv: assumes "finite P"
                     and "partial_order_on P (relation_of (\<le>) P)"
                   shows "\<exists> cv. chain_cover_on P (\<le>) cv"
proof-
  show ?thesis using assms exists_cd cd_cv by blast
qed

(*Shows \<lbrakk>antichain ac; chain cover cv\<rbrakk> \<Longrightarrow> \<forall> ac elems. \<exists> chain \<in> cv. a \<in> c*)

lemma elem_ac_in_c: assumes a1: "antichain_on P (\<le>) ac" 
                        and "chain_cover_on P (\<le>) cv"
                      shows "\<forall> a \<in> ac. \<exists> c \<in> cv. a \<in> c"
proof-
  have "\<Union> cv = P" using assms(2) chain_cover_on_def by simp
  then have "ac \<subseteq> \<Union> cv" using a1 antichain_on_def by simp
  then show "\<forall> a \<in> ac. \<exists> c \<in> cv. a \<in> c" by blast
qed

(*Shows that for a function that maps every element of an antichain to
the chain it belongs to in a chain cover, the co-domain of the function \<subseteq> of the chain cover*)

lemma f_image: fixes f :: "'a \<Rightarrow> 'a set"
             assumes a1: "(antichain_on P (\<le>) ac)"
                 and a2: "(chain_cover_on P (\<le>) cv)"
                 and a3: "\<forall>a \<in> ac. \<exists> c \<in> cv. a \<in> c \<and> f a = c"
               shows "(f ` ac) \<subseteq> cv"
proof
  have 1: "\<forall>a \<in> ac. \<exists> c \<in> cv. a \<in> c" using elem_ac_in_c a1 a2 by presburger
  fix y
  assume "y \<in> (f ` ac)"
  then obtain x where "f x = y" " x \<in> ac" using a1 a2 by auto
  then have "x \<in> y" using a3 by blast
  then show "y \<in> cv" using a3 using \<open>f x = y\<close> \<open>x \<in> ac\<close> by blast
qed


(*1. Size of an antichain \<le> Size of a chain cover*)
lemma DW1: assumes a1: "(antichain_on P (\<le>) ac)"
               and a2: "(chain_cover_on P (\<le>) cv)"
               and "finite P"
             shows "card ac \<le> card cv"
proof (rule ccontr)
  assume a_contr: "\<not> card ac \<le> card cv"
  then have 1: "card cv < card ac" by simp
  have finite_cv: "finite cv" using assms(3) a2 chain_cover_on_def
    by (simp add: finite_UnionD)
  have 2: "\<forall> a \<in> ac. \<exists> c \<in> cv. a \<in> c" using a1 a2 elem_ac_in_c by simp
  then obtain f where f_def: "\<forall>a \<in> ac. \<exists> c \<in> cv. a \<in> c \<and> f a = c" by metis
  then have "(f ` ac) \<subseteq> cv" using f_image assms by blast
  then have 3: "card (f ` ac) \<le> card cv" using f_def finite_cv card_mono by metis
  then have "card (f ` ac) < card ac" using 1 by auto
  then have "\<not> inj_on f ac" using pigeonhole by blast
  then obtain a b where p1: "f a = f b" "a \<noteq> b" "a \<in> ac" "b \<in> ac" 
    using inj_def f_def by (meson inj_on_def)
  then have antichain_elem: "a \<in> ac \<and> b \<in> ac" using f_def by blast
  then have "\<exists> c \<in> cv. f a = c \<and> f b = c" using f_def 2 1 \<open>f ` ac \<subseteq> cv\<close> p1(1) by auto
  then have chain_elem: "\<exists> c \<in> cv. a \<in> c \<and> b \<in> c" using f_def p1(1) p1(3) p1(4) by blast
  then have "a \<le> b \<or> b \<le> a" using chain_elem chain_cover_on_def chain_on_def 
    by (metis a2 chainE)
  then have "a = b" using antichain_elem a1 antichain_on_def antichain_def by auto
  then show False using p1(2) by blast
qed

(*Shows that the maximal set on P is a subset of P*)

lemma max_subset: "maximals_set P (\<le>) \<subseteq> P"
proof-
  show ?thesis using maximals_set_def by simp
qed

(*Shows that the minimal set on P is a subset of P*)

lemma min_subset: "minimals_set P (\<le>) \<subseteq> P"
proof-
  show ?thesis using minimals_set_def by simp
qed

(*Shows that the maximal set is an antichain*)

lemma maxset_ac: "antichain (\<le>) (maximals_set P (\<le>))" (is "antichain (\<le>) ?ms")
proof-
  have "\<forall> x \<in> ?ms. \<forall> y \<in> ?ms. (x \<le> y) \<or> (y \<le> x) \<longrightarrow> x = y" 
    unfolding maximals_set_def using is_maximal_def by fastforce
  then have "antichain (\<le>) ?ms" using antichain_def by simp
  then show ?thesis .
qed

(*Shows that the minimal set is an antichain*)

lemma minset_ac: "antichain (\<le>) (minimals_set P (\<le>))" (is "antichain (\<le>) ?ms")
proof-
  have "\<forall> x \<in> ?ms. \<forall> y \<in> ?ms. (x \<le> y) \<or> (y \<le> x) \<longrightarrow> x = y"
    unfolding minimals_set_def using is_minimal_def by fastforce
  then have "antichain (\<le>) ?ms" using antichain_def by presburger
  then show ?thesis .
qed


(*Shows that the null set is both an antichain and a chain cover"*)

lemma antichain_null: "antichain (\<le>) {}"
proof-
  show ?thesis using antichain_def by simp
qed

lemma chain_cover_null: assumes "P = {}" shows "chain_cover_on P (\<le>) {}"
proof-
  show ?thesis using chain_cover_on_def
    by (simp add: assms)
qed


(*Shows that for any arbitrary x \<notin> the largest antichain of a set, 
\<exists> y in the antichain such that x R y \<or> y R x*)

lemma x_not_in_ac_rel: assumes "largest_antichain_on P (\<le>) ac"
                           and "x \<in> P" 
                           and "x \<notin> ac"
                           and "finite P"
                         shows "\<exists> y \<in> ac. (x \<le> y) \<or> (y \<le> x)"
proof (rule ccontr)
  assume "\<not> (\<exists>y\<in>ac. x \<le> y \<or> y \<le> x)"
  then have 1: "\<forall> y \<in> ac. (\<not>(x \<le> y) \<and> \<not>(y \<le> x))" by simp
  then have 2: "\<forall> y \<in> ac. x \<noteq> y" by auto
  then obtain S where S_def: "S = {x} \<union> ac" by blast
  then have S_fin: "finite S" 
    using assms(4) assms(1) assms(2) largest_antichain_on_def antichain_on_def
    by (meson Un_least bot.extremum insert_subset rev_finite_subset)
  have S_on_P: "antichain_on P (\<le>) S" 
    using S_def largest_antichain_on_def antichain_on_def assms(1) assms(2) 1 2 antichain_def 
    by auto
  then have "ac \<subset> S" using S_def assms(3) by auto
  then have "card ac < card S" using psubset_card_mono S_fin by blast
  then show False using assms(1) largest_antichain_on_def S_on_P by fastforce
qed


(*Shows that for any subset Q of the poset P, if the minimal set of P is a subset of Q, 
then it is a subset of the minimal set of Q aswell*)

lemma minset_subset_minset: assumes "partial_order_on P (relation_of (\<le>) P)"
                                and "finite P"
                                and "Q \<subseteq> P"
                                and "minimals_set P (\<le>) \<subseteq> Q"
                              shows "minimals_set P (\<le>) \<subseteq> minimals_set Q (\<le>)" 
                                (is "?mp \<subseteq> ?mq")
proof
  fix x
  assume asm1: "x \<in> ?mp"
  then have 1: "is_minimal P (\<le>) x" unfolding minimals_set_def by simp
  have 2: "x \<in> Q" using asm1 assms(4) by auto
  have partial_Q: "partial_order_on Q (relation_of (\<le>) Q)" 
    using assms(1) assms(3) partial_order_on_def
    by (simp add: partial_order_on_relation_ofI)
  have "\<forall> q \<in> Q. q \<in> P" using assms(3) by blast
  then have "is_minimal Q (\<le>) x" using is_minimal_def 1 partial_Q by simp
  then have "x \<in> ?mq" using minimals_set_def 2 by simp
  then show "x \<in> ?mq" .
qed

(*Shows that for any subset Q of the poset P, if the maximal set of P is a subset of Q, 
then it is a subset of the maximal set of Q aswell*)

lemma maxset_subset_maxset: assumes "partial_order_on P (relation_of (\<le>) P)"
                                and "finite P"
                                and "Q \<subseteq> P"
                                and "maximals_set P (\<le>) \<subseteq> Q"
                              shows "maximals_set P (\<le>) \<subseteq> maximals_set Q (\<le>)" 
                                (is "?mp \<subseteq> ?mq")
proof
  fix x
  assume asm1: "x \<in> ?mp"
  then have 1: "is_maximal P (\<le>) x" unfolding maximals_set_def by simp
  have 2: "x \<in> Q" using asm1 assms(4) by auto
  have partial_Q: "partial_order_on Q (relation_of (\<le>) Q)" 
    using assms(1) assms(3) partial_order_on_def
    by (simp add: partial_order_on_relation_ofI)
  have "\<forall> q \<in> Q. q \<in> P" using assms(3) by blast
  then have "is_maximal Q (\<le>) x" using is_maximal_def 1 partial_Q by simp
  then have "x \<in> ?mq" using maximals_set_def 2 by simp
  then show "x \<in> ?mq" .
qed


(*Shows that if the minimal set \<noteq> the largest antichain on a set, then
\<exists> a \<in> the minimal set such that a \<notin> the largest antichain*)

(*Awaiting Proof*)


(*Shows that if P \<noteq> {}, the minimal set of P \<noteq> {}*)

lemma non_empty_minset: assumes "partial_order_on P (relation_of (\<le>) P)"
                            and "finite P"
                            and "P \<noteq> {}"
                          shows "minimals_set P (\<le>) \<noteq> {}"
proof-
  have "\<exists> x \<in> P. is_minimal P (\<le>) x" using assms(1) unfolding is_minimal_def
    by (simp add: assms(2) assms(3) local.finite_has_minimal)
  then show ?thesis unfolding minimals_set_def by auto
qed

(*Shows that if P \<noteq> {}, the maximal set of P \<noteq> {}*)

lemma non_empty_maxset: assumes "partial_order_on P (relation_of (\<le>) P)"
                            and "finite P"
                            and "P \<noteq> {}"
                          shows "maximals_set P (\<le>) \<noteq> {}"
proof-
  have "\<exists> x \<in> P. is_maximal P (\<le>) x" using assms(1) unfolding is_maximal_def
    by (simp add: assms(2) assms(3) local.finite_has_maximal)
  then show ?thesis unfolding maximals_set_def by auto
qed


(*Shows that \<forall> m \<in> the minimal set, \<exists> a chain \<in> the chain cover
such that m \<in> c*)

lemma elem_minset_in_chain: assumes "partial_order_on P (relation_of (\<le>) P)"
                                and "finite P"
                                and "chain_cover_on P (\<le>) cv"
                              shows "\<forall> a \<in> minimals_set P (\<le>). \<exists> c \<in> cv. a \<in> c" 
                                (is "\<forall> a \<in> ?min. \<exists> c \<in> cv. a \<in> c")
proof-
  have "antichain_on P (\<le>) ?min" 
    using assms(1) minset_ac min_subset unfolding antichain_on_def by simp
  then show ?thesis using assms(3) elem_ac_in_c by simp
qed

(*Shows that \<forall> m \<in> the maximal set, \<exists> a chain \<in> the chain cover
such that m \<in> c*)

lemma elem_maxset_in_chain: assumes "partial_order_on P (relation_of (\<le>) P)"
                                and "finite P"
                                and "chain_cover_on P (\<le>) cv"
                              shows "\<forall> a \<in> maximals_set P (\<le>). \<exists> c \<in> cv. a \<in> c" 
                                (is "\<forall> a \<in> ?max. \<exists> c \<in> cv. a \<in> c")
proof-
  have "antichain_on P (\<le>) ?max" 
    using assms(1) maxset_ac max_subset unfolding antichain_on_def by simp
  then show ?thesis using assms(3) elem_ac_in_c by simp
qed

lemma card_ac_cv_eq: assumes "partial_order_on P (relation_of (\<le>) P)"
                         and "finite P"
                         and "chain_cover_on P (\<le>) cv"
                         and "antichain_on P (\<le>) ac"
                         and "card cv = card ac"
                       shows "\<forall> c \<in> cv. \<exists> a \<in> ac. a \<in> c"
proof (rule ccontr)
  assume "\<not> (\<forall>c\<in>cv. \<exists>a\<in>ac. a \<in> c)"
  then obtain c where "c \<in> cv" "\<forall> a \<in> ac. a \<notin> c" by blast
  then have "\<forall> a \<in> ac. a \<in> \<Union> (cv - {c})" (is "\<forall> a \<in> ac. a \<in> ?cv_c")
    using assms(3) assms(4) unfolding chain_cover_on_def antichain_on_def by blast
  then have 1: "ac \<subseteq> ?cv_c" by blast
  have 2: "partial_order_on ?cv_c (relation_of (\<le>) ?cv_c)" 
    using assms(1) assms(3) partial_order_on_def
    by (simp add: partial_order_on_relation_ofI)
  then have ac_on_cv_v: "antichain_on ?cv_c (\<le>) ac" 
    using 1 assms(4) antichain_on_def unfolding antichain_on_def by blast
  have 3: "\<forall> a \<in> (cv - {c}). a \<subseteq> ?cv_c" by auto
  have 4: "\<forall> a \<in> (cv - {c}). chain (\<le>) a" using assms(3) 
    unfolding chain_cover_on_def chain_on_def by simp
  have 5: "\<forall> a \<in> (cv - {c}). chain_on ?cv_c (\<le>) a" using chain_on_def 2 3 4 by simp
  have "\<Union> (cv - {c}) = ?cv_c" by simp
  then have cv_on_cv_v: "chain_cover_on ?cv_c (\<le>) (cv - {c})" 
    using 5 chain_cover_on_def by simp
  have "card (cv - {c}) < card cv"
    by (metis \<open>c \<in> cv\<close> assms(2) assms(3) card_Diff1_less chain_cover_on_def finite_UnionD)
  then have "card (cv - {c}) < card ac" using assms(5) by simp
  then show False using ac_on_cv_v cv_on_cv_v DW1 assms(2)
    by (metis Diff_insert_absorb Diff_subset Set.set_insert Union_mono assms(3) assms(5) card_Diff1_less_iff card_seteq chain_cover_on_def rev_finite_subset)
qed


(*Shows that if an element m from the minimal set is in a chain, it is less than or equal to
all elements in the chain*)

lemma e_minset_lesseq_e_chain: assumes "chain_on P (\<le>) c" 
                                   and "m \<in> (minimals_set P (\<le>))" 
                                   and "m \<in> c"
                                 shows "\<forall> a \<in> c. m \<le> a"
proof-
  have 1: "c \<subseteq> P" using assms(1) unfolding chain_on_def by simp
  have 2: "is_minimal P (\<le>) m" using assms(2) unfolding minimals_set_def by blast
  then have "is_minimal c (\<le>) m" using 1 unfolding is_minimal_def
    by (simp add: in_mono partial_order_on_relation_ofI)
  then have 3: "\<forall> a \<in> c. (a \<le> m) \<longrightarrow> a = m" unfolding is_minimal_def by auto
  have "\<forall> a \<in> c. \<forall> b \<in> c. (a \<le> b) \<or> (b \<le> a)" using assms(1) 
    unfolding chain_on_def chain_def by blast
  then have "\<forall> a \<in> c. m \<le> a" using 3 assms(3) by blast
  then show ?thesis .
qed

(*Shows that if an element m from the maximal set is in a chain, it is greater than or equal to
all elements in the chain*)

lemma e_chain_lesseq_e_maxset: assumes "chain_on P (\<le>) c" 
                                   and "m \<in> (maximals_set P (\<le>))" 
                                   and "m \<in> c"
                                 shows "\<forall> a \<in> c. a \<le> m"
proof-
  have 1: "c \<subseteq> P" using assms(1) unfolding chain_on_def by simp
  have 2: "is_maximal P (\<le>) m" using assms(2) unfolding maximals_set_def by blast
  then have "is_maximal c (\<le>) m" using 1 unfolding is_maximal_def
    by (simp add: in_mono partial_order_on_relation_ofI)
  then have 3: "\<forall> a \<in> c. (m \<le> a) \<longrightarrow> a = m" unfolding is_maximal_def by auto
  have "\<forall> a \<in> c. \<forall> b \<in> c. (a \<le> b) \<or> (b \<le> a)" using assms(1) 
    unfolding chain_on_def chain_def by blast
  then have "\<forall> a \<in> c. a \<le> m" using 3 assms(3) by blast
  then show ?thesis .
qed
(*
lemma sub0: assumes "finite P"
               and "partial_order_on P (relation_of (\<le>) P)"
               and "x \<notin> P"
             shows "minimals_set (P \<union> {x}) (\<le>) 
                         = minimals_set P (\<le>) - {y \<in> P. y \<ge> x} \<union> {x}
                    \<or> minimals_set (P \<union> {x}) (\<le>) = minimals_set P (\<le>) "
proof(cases "\<exists>y \<in> minimals_set P (\<le>). y \<le> x")
  case True
  then obtain y where y:"y \<in> minimals_set P (\<le>)" "y \<le> x" by fast
  then have "y \<in> P" using minimals_set_def by blast
  hence y_x_ineq:"y < x" using y(2) assms(3) 
    using local.le_less by auto
  have "minimals_set (P \<union> {x}) (\<le>) = minimals_set P (\<le>)"
(* using assms
     minimals_set_def unfolding is_minimal_def*)
   proof
     show "minimals_set (P \<union> {x}) (\<le>) \<subseteq> minimals_set P (\<le>)"
     proof
       fix z
       assume asm:"z \<in> minimals_set (P \<union> {x}) (\<le>)"
       hence "\<forall>xa\<in> P \<union> {x}. xa \<le> z \<longrightarrow> z = xa" using minimals_set_def unfolding is_minimal_def 
         by simp
       hence loc:"\<forall>xa\<in> P. xa \<le> z \<longrightarrow> z = xa" using minimals_set_def unfolding is_minimal_def 
         by simp
       have "z \<noteq> x" using asm y_x_ineq unfolding minimals_set_def is_minimal_def
         using \<open>y \<in> P\<close> y(2) by blast
       thus "z \<in> minimals_set P (\<le>)" using asm loc unfolding minimals_set_def is_minimal_def
         by blast  case True
     qed
   next      
     show  "minimals_set P (\<le>) \<subseteq> minimals_set (P \<union> {x}) (\<le>)"
     proof
      fix z
      assume asm:"z \<in> minimals_set P (\<le>)"
      show "z \<in> minimals_set (P \<union> {x}) (\<le>)" using y
        unfolding minimals_set_def is_minimal_def 
        by (smt (verit, best) Un_insert_right asm empty_iff insert_iff is_minimal_def local.atLeastAtMost_iff local.atLeastatMost_empty local.dual_order.not_eq_order_implies_strict local.dual_order.trans mem_Collect_eq minimals_set_def sup_bot.right_neutral)
    qed
  qed
  then show ?thesis by argo
  next
   case False
   hence x_minP:"\<forall>y \<in> minimals_set P (\<le>). \<not> y \<le> x" by auto   
   have "minimals_set (P \<union> {x}) (\<le>) = minimals_set P (\<le>) - {y \<in> P. x \<le> y} \<union> {x}"
   proof
     show "minimals_set (P \<union> {x}) (\<le>) \<subseteq> minimals_set P (\<le>) - {y \<in> P. x \<le> y} \<union> {x}"
     proof
       fix z
       assume asm:"z \<in> minimals_set (P \<union> {x}) (\<le>)"
       hence asm_d:"\<forall>xa\<in>P \<union> {x}. xa \<le> z \<longrightarrow> z = xa" unfolding minimals_set_def is_minimal_def by blast  
       show "z \<in> minimals_set P (\<le>) - {y \<in> P. x \<le> y} \<union> {x}" using False assms
       proof(cases "z = x")
         case True
         hence "x \<in>  minimals_set P (\<le>) \<union> {x}"
           by auto
         moreover have "x \<notin> {y \<in> P. x \<le> y}" using assms(3) by blast 
         then show ?thesis using True by simp
       next
         case False
         hence z_in_p:"z \<in> P" using asm 
           by (metis UnE equals0D insertE min_subset subset_eq)
         hence z_in_min:"z \<in> minimals_set P (\<le>)" using asm_d unfolding minimals_set_def
            is_minimal_def by blast
         have "z \<notin> {y \<in> P. x \<le> y}"
         proof(rule ccontr)
           assume "\<not> z \<notin> {y \<in> P. x \<le> y}"
           hence "x \<le> z" by blast
           hence "\<not> (\<forall>xa \<in> P \<union> {x}. xa \<le> z \<longrightarrow> z = xa)" using False by fast
           hence "z \<notin> minimals_set (P \<union> {x}) (\<le>)" unfolding minimals_set_def
               is_minimal_def by blast
           thus False using asm by argo
         qed
         then show ?thesis using z_in_min by blast  
       qed
     qed
   next 
    show "minimals_set P (\<le>) - {y \<in> P. x \<le> y} \<union> {x} \<subseteq> minimals_set (P \<union> {x}) (\<le>)"
    proof
      fix z
      assume asm:"z \<in> minimals_set P (\<le>) - {y \<in> P. x \<le> y} \<union> {x}"
      show " z \<in> minimals_set (P \<union> {x}) (\<le>)" (* unfolding minimals_set_def
         is_minimal_def *)
      proof(cases "z = x")
        case True
        have "\<forall>y \<in> P \<union> {x}. y \<le> x \<longrightarrow> y = x" sorry
      next
        case False
        then show ?thesis sorry
      qed
    qed
  qed
 lemma sub: assumes "finite P"
               and "partial_order_on P (relation_of (\<le>) P)"
             shows "\<forall> p \<in> P. \<exists> m \<in> minimals_set P (\<le>). m \<le> p" 
               (is "\<forall> p \<in> P. \<exists> m \<in> ?min. m \<le> p") using assms then show "minimals_set (P \<union> {x}) (\<le>) = minimals_set P (\<le>) - {y \<in> P. x \<le> y} \<union> {x} \<or>
    minimals_set (P \<union> {x}) (\<le>) = minimals_set P (\<le>)" by argo
qed
*)


lemma assumes "finite P"
          and "partial_order_on P (relation_of (\<le>) P)"
          and "xs \<subseteq> P"
          and "\<forall> x \<in> xs. \<forall> y \<in> xs. x \<le> y \<or> y \<le> x"
        shows "\<exists> z \<in> xs. \<forall> x \<in> xs. z \<ge> x"
  by sorry
lemma DW2_critical: assumes "partial_order_on P (relation_of (\<le>) P)"
                        and "largest_antichain_on P (\<le>) lac"
                        and "finite P"
                      shows "lac \<noteq> minimals_set P (\<le>) \<longrightarrow> (\<exists> x \<in> minimals_set P (\<le>). x \<notin> lac)" 
                        (is " lac \<noteq> ?min \<longrightarrow> (\<exists> x \<in> ?min. x \<notin> lac)")
  by sorry

lemma sub: assumes "finite P"
               and "partial_order_on P (relation_of (\<le>) P)"
             shows "\<forall> p \<in> P. \<exists> m \<in> minimals_set P (\<le>). m \<le> p" 
               (is "\<forall> p \<in> P. \<exists> m \<in> ?min. m \<le> p") 
proof
  fix p
  assume asm:"p \<in> P"
  obtain m where m: "m \<in> P"  "m \<le> p" "\<forall>a \<in> P. a \<le> m \<longrightarrow> a = m"
    using finite_has_minimal2[OF assms(1) asm] by metis 
  hence "m \<in> minimals_set P (\<le>)"
    unfolding minimals_set_def is_minimal_def by blast
  then show " \<exists> m \<in> minimals_set P (\<le>). m \<le> p" using m by fast
qed

(*

(*assumes partial order on p, largest antichian on ac, finite P, shows, \<exists> x \<in> minimals_set of P. x \<notin> lac*)
lemma DW2_critical: assumes "partial_order_on P (relation_of (\<le>) P)"
                        and "largest_antichain_on P (\<le>) lac"
                        and "finite P"
                      shows "lac \<noteq> minimals_set P (\<le>) \<longrightarrow> (\<exists> x \<in> minimals_set P (\<le>). x \<notin> lac)" 
                        (is " lac \<noteq> ?min \<longrightarrow> (\<exists> x \<in> ?min. x \<notin> lac)")
proof (rule ccontr)
  (*have "\<not> ((?min \<subseteq> lac ) \<and> (lac \<subseteq> ?min))" using assms(3) by simp
  then have "(\<not> (?min \<subseteq> lac)) \<or> (\<not> (lac \<subseteq> ?min))" by blast*)
  assume asm1: "\<not> (lac \<noteq> minimals_set P (\<le>) \<longrightarrow> (\<exists>x\<in>minimals_set P (\<le>). x \<notin> lac))"
  then have 0: "lac \<noteq> ?min \<and> (\<forall> x \<in> ?min. x \<in> lac)" by simp
  then have lac_not_min: "lac \<noteq> ?min" by presburger
  then have lac_not_min2: "(\<not> lac \<subseteq> ?min) \<or> (\<not> ?min \<subseteq> lac)" by fast
  have other_asm: "\<forall> x \<in> ?min. x \<in> lac" using 0 by meson
  then have min_sub_lac: "?min \<subseteq> lac" by blast
  then have 1: "\<not> lac \<subseteq> ?min" using lac_not_min2 0 by fast
  have "\<not> ?min \<subseteq> lac"
  proof(rule ccontr)
    assume  "?min \<subseteq> lac"
    have min_under_lac: "?min \<subset> lac" using 1 by (simp add: min_sub_lac psubsetI)
    then obtain elem_lac where elem_lac_def: "elem_lac \<in> lac \<and> elem_lac \<notin> ?min" by auto
    then have elem_lac_in_P: "elem_lac \<in> P" using  largest_antichain_on_def
      by (meson antichain_on_def assms(2) subsetD)
    then have "\<not> is_minimal P (\<le>) elem_lac" using elem_lac_def is_minimal_def 
      unfolding minimals_set_def by simp
    then obtain z where z_def: "z \<in> P" "z \<le> elem_lac" "z \<noteq> elem_lac" using is_minimal_def assms(1) 
      using antichain_on_def assms(2) largest_antichain_on_def by auto
    then have "\<exists> m \<in> ?min. m \<le> z" using z_def  minimals_set_def is_minimal_def 
   proof(cases "is_minimal P (\<le>) z")
      case True
      then have "z \<in> ?min" using minimals_set_def z_def(1) by simp
      then have "\<exists> m \<in> ?min. m = z" by simp
      then show ?thesis by blast
    next
      case False
      then show ?thesis using assms sorry
    qed
    have "\<forall> x \<in> P. \<exists> m \<in> ?min. m \<le> x" using is_minimal_def assms unfolding minimals_set_def sorry
    then have "\<exists> m \<in> ?min. m \<le> elem_lac" using elem_lac_def is_minimal_def antichain_on_def
      unfolding minimals_set_def largest_antichain_on_def sorry
    (*contradiction comes from 
m can't be elem_lac, and so there is a distinct member of minimals set that is related to elem lac. 
elem lac is in lac  and so is m (since m is in min) but this is an antichain*)
    show False sorry
  qed
  show False sorry
qed



*)

(*2. There is a chain cover of size equal to width(P)*)

lemma DW2: assumes asm1: "largest_antichain_on P (\<le>) lac"
               and asm2: "m = card lac" 
               and asm3: "finite P"
             shows "\<exists> cv. (chain_cover_on P (\<le>) cv) \<and> (card cv = m)"
  using assms
proof (induction "card P" arbitrary: P rule: less_induct)
  case less
  let ?max = "maximals_set P (\<le>)"
  let ?min = "minimals_set P (\<le>)"
  show ?case
  proof (cases "lac \<noteq> ?max \<and> lac \<noteq> ?min")
    case True
    have partial_P: "partial_order_on P (relation_of (\<le>) P)" using assms partial_order_on_def
      using antichain_on_def largest_antichain_on_def less.prems(1) by presburger
    then have lac_in_P: "lac \<subseteq> P" 
      using asm1 antichain_on_def largest_antichain_on_def less.prems(1) by presburger
    let ?p_plus = "p_plus P (\<le>) lac"
    let ?p_min = "p_minus P (\<le>) lac"
    have 1: "lac \<subseteq> ?p_plus" unfolding p_plus_def
    proof
      fix x
      assume a1: "x \<in> lac"
      then have a2: "x \<in> P"
        using asm1 largest_antichain_on_def antichain_on_def less.prems(1) by blast
      then have "x \<le> x" using antichain_def by auto
      then show "x \<in> {x \<in> P. \<exists> y \<in> lac. y \<le> x}" using a1 a2 by auto
    qed
    have 2: "lac \<subseteq> ?p_min" unfolding p_minus_def
    proof
      fix x
      assume a1: "x \<in> lac"
      then have a2: "x \<in> P" 
        using asm1 largest_antichain_on_def antichain_on_def less.prems(1) by blast
      then have "x \<le> x" using antichain_def by auto
      then show "x \<in> {x \<in> P. \<exists> y \<in> lac. x \<le> y}" using a1 a2 by auto
    qed
    have lac_subset: "lac \<subseteq> (?p_plus \<inter> ?p_min)" using 1 2 by simp
    have subset_lac: "(?p_plus \<inter> ?p_min) \<subseteq> lac"
    proof
      fix x
      assume "x \<in> (?p_plus \<inter> ?p_min)"
      then obtain a b where antichain_elems: "a \<in> lac" "b \<in> lac" "a \<le> x" "x \<le> b" 
        using p_plus_def p_minus_def by auto
      then have "a \<le> b" by simp
      then have "a = b" 
        using antichain_elems(1) antichain_elems(2) 
          asm1 largest_antichain_on_def antichain_on_def antichain_def by metis
      then have "(a \<le> x) \<and> (x \<le> a)" using antichain_elems(3) antichain_elems(4) by blast
      then have "x = a" by fastforce
      then have "x \<in> lac" using antichain_elems(1) by simp
      then show "x \<in> lac" .
    qed
    then have lac_pset_eq: "lac = (?p_plus \<inter> ?p_min)" using lac_subset by simp
    have P_PP_PM: "(?p_plus \<union> ?p_min) = P"
    proof
      show "(?p_plus \<union> ?p_min) \<subseteq> P"
      proof
        fix x
        assume "x \<in> (?p_plus \<union> ?p_min)"
        then have "x \<in> ?p_plus \<or> x \<in> ?p_min" by simp
        then have "x \<in> P" using p_plus_def p_minus_def by auto
        then show "x \<in> P" .
      qed
    next
      show "P \<subseteq> (?p_plus \<union> ?p_min)"
      proof
        fix x
        assume x_in: "x \<in> P"
        then have "x \<in> lac \<or> x \<notin> lac" by simp
        then have "x \<in> (?p_plus \<union> ?p_min)"
        proof (cases "x \<in> lac")
          case True
          then show ?thesis using lac_subset by blast
        next
          case False
          then obtain y where "y \<in> lac" "(x \<le> y) \<or> (y \<le> x)" 
            using asm1 False x_in x_not_in_ac_rel asm3 less.prems(3) less.prems(1) by blast
          then have "(x \<in> ?p_plus) \<or> (x \<in> ?p_min)" 
            unfolding p_plus_def p_minus_def using x_in by auto
          then show ?thesis by simp
        qed
        then show "x \<in> p_plus P (\<le>) lac \<union> p_minus P (\<le>) lac" by simp
      qed
    qed
    obtain a where a_def: "a \<in> ?min" "a \<notin> lac" using asm1 True asm3
      using less.prems(1) less.prems(3) sorry
    then have "\<forall> x \<in> lac. \<not> (x \<le> a)" 
      unfolding minimals_set_def is_minimal_def using partial_P lac_in_P by auto
    then have a_not_in_PP: "a \<notin> ?p_plus" using p_plus_def by simp
    have "a \<in> P" using a_def min_subset by auto
    then have ppl: "card ?p_plus < card P" using P_PP_PM a_not_in_PP
      by (metis Un_upper1 card_mono card_subset_eq less.prems(3) order_le_imp_less_or_eq)
    have p_plus_subset: "?p_plus \<subseteq> P" using p_plus_def by simp
    have antichain_lac: "antichain (\<le>) lac" 
      using assms(1) unfolding largest_antichain_on_def antichain_on_def by simp
    have partial_PP: "partial_order_on ?p_plus (relation_of (\<le>) ?p_plus)" 
      using partial_P p_plus_subset partial_order_on_def
      by (smt (verit, best) local.antisym_conv local.le_less local.order_trans partial_order_on_relation_ofI)
    then have lac_on_PP: "antichain_on ?p_plus (\<le>) lac" 
      using antichain_on_def 1 antichain_lac by simp
    have card_ac_on_P: "\<forall> ac. antichain_on P (\<le>) ac \<longrightarrow> card ac \<le> card lac"
      using asm1 largest_antichain_on_def less.prems(1) by auto
    then have "\<forall> ac. antichain_on ?p_plus (\<le>) ac \<longrightarrow> card ac \<le> card lac"
      using p_plus_subset antichain_on_def largest_antichain_on_def
      by (meson partial_P preorder_class.order_trans)
    then have "largest_antichain_on ?p_plus (\<le>) lac" 
      using lac_on_PP unfolding largest_antichain_on_def by simp
    then have cv_PP: "\<exists>cv. chain_cover_on ?p_plus (\<le>) cv \<and> card cv = m" using less ppl
      by (metis P_PP_PM finite_Un)
    then obtain cvPP where cvPP_def: "chain_cover_on ?p_plus (\<le>) cvPP" "card cvPP = m" by blast
    obtain b where b_def: "b \<in> ?max" "b \<notin> lac" sorry
    then have "\<forall> x \<in> lac. \<not> (b \<le> x)" 
      unfolding maximals_set_def is_maximal_def using partial_P lac_in_P by auto
    then have b_not_in_PM: "b \<notin> ?p_min" using p_minus_def by simp
    have "b \<in> P" using b_def max_subset by auto
    then have pml: "card ?p_min < card P" using max_subset b_not_in_PM
      by (metis P_PP_PM Un_upper2 card_mono card_subset_eq less.prems(3) nat_less_le)
    have "partial_order_on ?p_min (relation_of (\<le>) ?p_min)"
      by (simp add: partial_order_on_relation_ofI)
    then have lac_on_PM: "antichain_on ?p_min (\<le>) lac" 
      using 2 antichain_lac antichain_on_def by simp
    then have "\<forall> ac. antichain_on ?p_min (\<le>) ac \<longrightarrow> card ac \<le> card lac"
      using card_ac_on_P P_PP_PM antichain_on_def largest_antichain_on_def
      by (metis partial_P sup.coboundedI2)
    then have "largest_antichain_on ?p_min (\<le>) lac" 
      using lac_on_PM unfolding largest_antichain_on_def by simp
    then have cv_PM: "\<exists>cv. chain_cover_on ?p_min (\<le>) cv \<and> card cv = m" using less pml
      by (metis P_PP_PM finite_Un)
    then obtain cvPM where cvPM_def: "chain_cover_on ?p_min (\<le>) cvPM" "card cvPM = m" by blast
    have lac_minPP: "lac = minimals_set ?p_plus (\<le>)" (is "lac = ?msPP")
    proof
      show "lac \<subseteq> minimals_set ?p_plus (\<le>)"
      proof
        fix x
        assume asm1: "x \<in> lac"
        then have x_in_PP: "x \<in> ?p_plus" using 1 by auto
        obtain y where y_def: "y \<in> ?p_plus" "y \<le> x"
          using 1 asm1 by blast
        then obtain a where a_def: "a \<in> lac" "a \<le> y" using p_plus_def by auto
        then have I: "a \<le> x" using y_def(2) by simp
        then have II: "a = x" using asm1 a_def(1) antichain_lac unfolding antichain_def by simp
        then have III: "y = x" using y_def(2) a_def(2) by simp
        have "\<forall> p \<in> ?p_plus. (p \<le> x) \<longrightarrow> p = x" using asm1 y_def a_def I II III assms(1) largest_antichain_on_def sorry
        then have "is_minimal ?p_plus (\<le>) x" using is_minimal_def partial_PP by auto
        then show "x \<in> minimals_set ?p_plus (\<le>)" 
          using x_in_PP unfolding minimals_set_def by auto
      qed
    next
      show "minimals_set ?p_plus (\<le>) \<subseteq> lac"
      proof
        fix x
        assume asm2: "x \<in> minimals_set ?p_plus (\<le>)"
        then have I: "\<forall> a \<in> ?p_plus. (a \<le> x) \<longrightarrow> a = x" 
          unfolding minimals_set_def is_minimal_def by blast
        have "x \<in> ?p_plus" using asm2 min_subset by auto
        then obtain y where y_def: "y \<in> lac" "y \<le> x" using p_plus_def by auto
        then have "y \<in> ?p_plus" using 1 by auto
        then have "y = x" using y_def(2) I by simp
        then show "x \<in> lac" using y_def(1) by simp
      qed
    qed
    then have card_msPP: "card ?msPP = m" using asm2 by simp
    then have "\<forall> a \<in> ?msPP. \<exists> c \<in> cvPP. a \<in> c" 
      using cvPP_def(1) partial_PP asm3 p_plus_subset elem_minset_in_chain elem_ac_in_c 
        \<open>lac = minimals_set (p_plus P (\<le>) lac) (\<le>)\<close> lac_on_PP by presburger
    then have "\<forall> c \<in> cvPP. \<exists> m \<in> ?msPP. m \<in> c" using cvPP_def card_msPP minset_ac card_ac_cv_eq
      by (metis P_PP_PM antichain_on_def finite_Un lac_minPP lac_on_PP less.prems(3))
    then have "\<forall> c \<in> cvPP. \<exists> m \<in> ?msPP. (\<forall> a \<in> c. m \<le> a)" using e_minset_lesseq_e_chain
      by (meson chain_cover_on_def cvPP_def(1))
    then have "\<forall> c \<in> cvPP. \<exists> x \<in> lac. (\<forall> a \<in> c. x \<le> a)" using lac_minPP by simp
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

(*
P = { {1}, {2}, {1,2}, {2,3}, {1,3}, {1,3,4}, {1,2,3,4}, {1,3,5}, {1,2,3,5} } rel = \<subseteq>
ac1 = {{1}, {2}}
ac2 = {{1,2}, {2,3}, {1,3}} *
ac3 = {{1,3,4}, {1,3,5}}
ac4 = {{1,2,3,4},{1,2,3,5}}
ac5 = {{1,3,4},{1,2,3,5}}
ac6 = {{1,3,4}, {1,2,3,5}}
ac7 = {{2,3},{1,3,4},{1,3,5}} *
ac8 = {{1,2}, {2,3}, {1,3,4}, {1,3,5}}

c1 = { {1}, {1,2}, {1,2,3,4} }
c2 = { {1}, {1,2}, {1,2,3,5} }
c3 = { {1}, {1,3}, {1,3,4}, {1,2,3,4} }
c4 = { {1}, {1,3}, {1,3,5}, {1,2,3,5} }
c5 = { {2}, {2,3}, {1,2,3,4} }
c6 = { {2}, {2,3}, {1,2,3,5} }

card lac = 4
max_s = {{1,2,3,4}, {1,2,3,5}}
min_s = {{1},{2}}
*)

(*
  case 0
  then have "card P \<le> 0" using card by simp
  then have 1: "P = {}" using asm1 asm2 by simp
  then have 2: "antichain_on P (\<le>) lac" using asm1 largest_antichain_on_def by simp
  then have "antichain (\<le>) lac" using antichain_on_def by auto
  then have null_anti: "lac = {}" using 1 2
    using elem_ac_in_c chain_cover_null by auto
  have "chain_cover_on P (\<le>) {}" using 1 chain_cover_null by simp
  then show ?case using null_anti by auto
next
  case (Suc n)
  then show ?case sorry
qed
*)

(*Dilworth's Lemma (statement above) *)
lemma Dilworth: assumes asm1: "largest_antichain_on P (\<le>) lac" and "finite P" and "card P \<le> n"
  shows "\<exists> cv. (smallest_chain_cover_on P (\<le>) cv) \<and> (card cv = card lac)"
  using assms
proof-
  show ?thesis using DW1 DW2 asm1 largest_antichain_on_def
    by (metis assms(2) smallest_chain_cover_on_def)
qed

end