theory Catdeory
  imports Main
          "~~/src/HOL/Library/Product_Lexorder"
          "~~/src/HOL/Analysis/Cartesian_Euclidean_Space"
begin

(*check for the proof- cross_affine_dependent*)
lemma "5 + 3 = 8"
  by simp


lemma "(1::real, 2) \<le> (2, 2)"
  by simp

lemma assumes "p \<in> convex hull {a, b}"
  shows "\<exists>\<mu>. \<exists> n.( \<mu> \<ge> 0 \<and> n \<ge> 0 \<and> (\<mu> + n = 1) \<and> (\<mu>  *\<^sub>R a + n  *\<^sub>R b = p))"
  using assms 
  by (metis diff_add_cancel diff_ge_0_iff_ge in_segment(1) segment_convex_hull)

(* note from above: definition of closed segment*)

(*
lemma convex_sum:
  fixes C :: "'a::real_vector set"
  assumes "finite S"
    and "convex C"
    and a: "(\<Sum> i \<in> S. a i) = 1" "\<And>i. i \<in> S \<Longrightarrow> a i \<ge> 0"
    and C: "\<And>i. i \<in> S \<Longrightarrow> y i \<in> C"
  shows "(\<Sum> j \<in> S. a j *\<^sub>R y j) \<in> C"
  using \<open>finite S\<close> a C
proof (induction arbitrary: a set: finite)
  case empty
  then show ?case by simp
next
  case (insert i S) 
  then have "0 \<le> sum a S"
    by (simp add: sum_nonneg)
  have "a i *\<^sub>R y i + (\<Sum>j\<in>S. a j *\<^sub>R y j) \<in> C"
  proof (cases "sum a S = 0")
    case True with insert show ?thesis
      by (simp add: sum_nonneg_eq_0_iff)
  next
    case False
    with \<open>0 \<le> sum a S\<close> have "0 < sum a S"
      by simp
    then have "(\<Sum>j\<in>S. (a j / sum a S) *\<^sub>R y j) \<in> C"
      using insert
      by (simp add: insert.IH flip: sum_divide_distrib)
    with \<open>convex C\<close> insert \<open>0 \<le> sum a S\<close> 
    have "a i *\<^sub>R y i + sum a S *\<^sub>R (\<Sum>j\<in>S. (a j / sum a S) *\<^sub>R y j) \<in> C"
      by (simp add: convex_def)
    then show ?thesis
      by (simp add: scaleR_sum_right False)
  qed
  then show ?case using \<open>finite S\<close> and \<open>i \<notin> S\<close>
    by simp
qed

lemma convex:
  "convex S \<longleftrightarrow> 
    (\<forall>(k::nat) u x. (\<forall>i. 1\<le>i \<and> i\<le>k \<longrightarrow> 0 \<le> u i \<and> x i \<in>S) \<and> (sum u {1..k} = 1)
      \<longrightarrow> sum (\<lambda>i. u i *\<^sub>R x i) {1..k} \<in> S)"  
  (is "?lhs = ?rhs")
proof*)

(*above two theorems show distinct formulations of convex set as equivalent*)


(*from above theorems extract a more amenable form for this result*)

definition nsubset::"'a set \<Rightarrow> nat \<Rightarrow> ('a set) set" (infix "~" 76)
  where
"nsubset S k = {X. X \<subseteq> S \<and>  card X = k}"


(*the function takes a set and outputs a set of all the convex combinations of elements*)
(*each convex combination is associated to function from elements of the set to [0,1], 
which gives the respective coefficients*)

definition convex_combin
  where
"convex_combin S \<equiv> {(\<Sum> j \<in> S. a j *\<^sub>R j) | a. (sum a S = 1) \<and> (\<forall>i \<in> S. a i \<ge> 0)}"


(*vertex of a convex-point, if you subtract any one point from S, 
it is not equal to convex hull of the whole thing*)

definition convex_pos::"('a::euclidean_space set) \<Rightarrow> bool"
  where
"convex_pos S \<equiv>  (\<forall> s \<in> S. convex hull S \<noteq> convex hull (S - {s}))"

lemma convex_pos_inherit': 
  assumes "convex_pos S"
  shows "\<forall> A \<subseteq> S. convex_pos (S - A)"
  unfolding convex_pos_def
proof(rule ccontr)
  assume "\<not> (\<forall>A\<subseteq>S. \<forall>s\<in>S - A. convex hull (S - A) \<noteq> convex hull (S - A - {s}))"
  then obtain A s where es:"A\<subseteq>S" "s\<in>S-A" "convex hull (S-A) = convex hull (S-A-{s})" 
    by blast
  hence "convex hull S = convex hull (S-{s})"
    by (smt (verit, ccfv_SIG) Diff_mono Diff_subset hull_inc hull_mono hull_redundant insert_Diff insert_mono rel_interior_empty rel_interior_subset subset_iff)
  thus False using assms convex_pos_def es(2) by blast
qed


lemma convex_pos_inherit0: 
  assumes "convex_pos S"
  shows "\<forall> e \<in> S. convex_pos (S - {e})"
  unfolding convex_pos_def
proof(rule ccontr)
  assume "\<not> (\<forall>e\<in>S. \<forall>s\<in>S - {e}. convex hull (S - {e}) \<noteq> convex hull (S - {e} - {s}))"
  then obtain e s where es:"e\<in>S" "s\<in>S-{e}" "convex hull (S-{e}) = convex hull (S-{e}-{s})" 
    by blast
  hence "convex hull S = convex hull (S-{s})"
    by (metis Diff_insert hull_insert insert_Diff_single insert_absorb insert_commute member_remove remove_def)
  thus False using assms convex_pos_def es(2) by blast
qed

lemma convex_pos_inherit: 
  assumes "convex_pos S"
  shows "\<forall> X \<subseteq> S. convex_pos X"
proof(rule ccontr)
  assume "\<not> (\<forall> X \<subseteq> S. convex_pos X)"
  then obtain X where X:"X \<subseteq> S" "\<not> (convex_pos X)" by auto
  then obtain x where x:"x \<in> X" "convex hull X = convex hull (X - {x})"
    unfolding convex_pos_def by blast
  then have "x \<in> convex hull (X - {x})" 
    by (metis hull_inc)
  then have "x \<in> convex hull ((X - {x}) \<union> (S - X))" 
    by (meson hull_mono in_mono sup.cobounded1)
  moreover have "((X - {x}) \<union> (S - X)) = (S - {x})" 
    using X(1) x(1) by fast
  ultimately have "x \<in>  convex hull (S - {x})" by simp
  hence "convex hull S = convex hull (S - {x})" using x(1) X(1) 
    by (metis hull_redundant in_mono insert_Diff)
  thus False using x(1) X(1) assms 
    using convex_pos_def by auto
qed

(*if every subset of S of cardinality four is in a convex position, 
then S is in a convex position

theorem caratheodory:
  "convex hull p =
    {x::'a::euclidean_space. \<exists>S. finite S \<and> S \<subseteq> p \<and> card S \<le> DIM('a) + 1 
                             \<and> x \<in> convex hull S}"*)

lemma four_convex:
  assumes "\<forall>X \<subseteq> (S::(real \<times> real) set). card X \<le> 4 \<longrightarrow> convex_pos X"
  shows "convex_pos S"
proof(rule ccontr)
  assume asm:"\<not> convex_pos S"
  then obtain p where p:"p \<in> S" "convex hull S = convex hull (S - {p})"
    using asm unfolding convex_pos_def by blast
  then have "p \<in> convex hull (S - {p})"
    using hull_inc by fastforce
  then obtain T where t:"finite T" "T \<subseteq> S - {p}" "card T \<le> DIM(real\<times>real) + 1" "p\<in>convex hull T" 
    using caratheodory[of "S-{p}"] by blast
  hence c1:"\<not> convex_pos (T\<union>{p})" unfolding convex_pos_def
    by (simp add: hull_insert insert_absorb subset_Diff_insert)
  have c2:"card (T\<union>{p}) \<le> 4" using t
    by (simp add: subset_Diff_insert)
  have "T\<union>{p} \<subseteq> S" using t(2) p(1) by auto
  thus False using c1 c2
    by (simp add: assms)
qed

lemma convex_four:
  assumes "convex_pos S"
  shows "\<forall>X \<subseteq> (S::(real \<times> real) set). card X \<le> 4 \<longrightarrow> convex_pos X"
  using assms convex_pos_inherit by auto

theorem fourConvexfour:
"convex_pos S = (\<forall>X \<subseteq> (S::(real \<times> real) set). card X \<le> 4 \<longrightarrow> convex_pos X)"
  using convex_four four_convex by blast

(*** end of lemma 2.1 Andrew Suk ***)

(*** start of Theorem 2.2 Andrew Suk ***)

(*** defs gen-position, k-cup, l-cup ***)
definition general_pos::"((real\<times>real) set) \<Rightarrow> bool" where
"general_pos S \<equiv>  (\<forall> P3 \<in> S~3. \<not> affine_dependent P3)"

definition lex_eq :: "(real\<times>real) \<Rightarrow> (real\<times>real) \<Rightarrow> bool" where
"lex_eq p1 p2 \<equiv> fst p1 \<le> fst p2"

definition lex :: "(real\<times>real) \<Rightarrow> (real\<times>real) \<Rightarrow> bool" where
"lex p1 p2 \<equiv> fst p1 < fst p2"

type_synonym real_plane = "real \<times> real"



definition cross3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> real" where
"cross3 a b c \<equiv> (snd b - snd a) * (fst c - fst b) - (snd c - snd b) * (fst b - fst a)"

definition cup3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"cup3 a b c \<equiv>  cross3 a b c < 0"

definition cap3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"cap3 a b c \<equiv>  cross3 a b c > 0"

definition collinear3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"collinear3 a b c \<equiv> cross3 a b c = 0"

(* observation: \<not> collinear3 a b c = general_pos_2D {a,b,c} *)

fun list_check :: "(_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> _ list \<Rightarrow> bool" where
  "list_check f [] = True"
| "list_check f (a#[]) = True"
| "list_check f (a#b#[]) = True"
| "list_check f (a#b#c#rest) = (f a b c \<and> list_check f (b#c#rest))"

definition cap::"nat \<Rightarrow> (real\<times>real) list \<Rightarrow> bool" where
"cap k L \<equiv> (k = length L) \<and> (sorted L) \<and> (list_check cap3 L)"

definition cup :: "nat \<Rightarrow> (real \<times> real) list \<Rightarrow> bool" where
"cup k L \<equiv> (k = length L) \<and> (sorted L) \<and> (list_check cup3 L)"

(* definition of minimum number of points containing an l-cup or k-cap *)
definition min_conv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"min_conv k l = (Inf {n . (\<forall>S . card S \<ge> n \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))})"

lemma cap_reduct:
  assumes "cap (k+1) (a#xs)"
  shows "cap k xs"
  using assms unfolding cap_def 
  using add_left_cancel length_Cons list.distinct(1) list.inject list_check.elims(2) by fastforce

lemma assumes "set xs \<subseteq> S" "cap k xs" "distinct xs" "finite S"
  shows "card S \<ge> k"
  using assms(4,1,2,3) 
  by (metis cap_def card_mono distinct_card)




theorem non_empty_cup_cap:
  fixes S
  assumes "finite S"
  shows "{(n::nat) . (\<forall>S . card S \<ge> n \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))} \<noteq> {}"
  sorry

lemma assumes "(X::nat set) \<noteq> {}" 
        shows "\<exists>S \<in> X. Inf X = S"
  using assms 
  by (simp add: Inf_nat_def1)

lemma fixes S
      assumes "finite S"
      shows "\<exists>xs.  length xs = card S \<and> set xs = S"
  using assms 
  by (metis distinct_card finite_distinct_list)

lemma fixes S
  assumes "finite S"
  shows "\<exists>xs.  length xs = card S \<and> set xs = S \<and> sorted xs"
  by (metis assms finite_sorted_distinct_unique sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set.sorted_key_list_of_set_unique)
lemma fixes S
  assumes "finite S"
  shows "\<exists>xs.  length xs = card S \<and> set xs = S \<and> sorted xs"
  by (metis assms finite_sorted_distinct_unique sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set.sorted_key_list_of_set_unique)

(* To show in a lemma if j < k, and the set of points created by a k-cap does not contain
a 3-cup*)
(*

lemma assumes "finite S" "gen_pos S"
  shows "\<exists> xs. set xs = S \<and> length xs = card S \<and> cap (card k *)


lemma assumes "sorted (xs::(real \<times> real) list)" and "sorted ys" 
      and "length xs = length ys"
      and "set xs = set ys"
    shows "xs = ys"
  using assms 
proof(induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
   obtain z zs where z_zs:"ys = z#zs" using Cons(2,4) 
     by (metis Cons.prems(2) length_0_conv sorted_wrt.elims(2))
   then have "z = Min {y . y \<in> set ys}"
     by (metis Collect_mem_eq Cons.prems(2) List.finite_set Min.coboundedI Min_in emptyE list.set_intros(1) nle_le set_ConsD sorted_simps(2)) 
   moreover have "x = Min {y. y \<in> set ys}" using assms(1)
     by (metis Cons.prems(1) Cons.prems(2) Cons.prems(4) List.finite_set Min_insert2 calculation list.simps(15) sorted_simps(2) z_zs)
   ultimately have "x = z" by argo
   hence "set xs = set zs" using Cons(5) unfolding z_zs sorry 
   then have "xs = zs"  sorry
  then show ?case sorry
qed

lemma extract_cap_cup:
    assumes "min_conv k l = n"
      and "card S = n" "general_pos S"
    shows "\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap k xs \<or> cup l xs)" using min_conv_def assms
proof-
  have s_1:"card S \<ge> n \<and> general_pos S" using assms by simp
  hence "card S \<in> {m.  (\<forall>S . card S \<ge> m \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs)))}"
    using assms(1) unfolding min_conv_def 
  proof -
    assume a1: "Inf {n. \<forall>S. n \<le> card S \<and> general_pos S \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sorted xs) \<and> (cap k xs \<or> cup l xs))} = n"
    have "{} \<noteq> {n. \<forall>r. n \<le> card r \<and> general_pos r \<longrightarrow> (\<exists>ps. set ps \<subseteq> r \<and> sorted ps \<and> (cap k ps \<or> cup l ps))}"
      using non_empty_cup_cap by blast
    then show ?thesis
      using a1 by (smt (z3) Inf_nat_def1 assms(2))
  qed
  hence "(\<exists>xs. set xs \<subseteq> S \<and> sorted xs \<and> (cap k xs \<or> cup l xs))"
    using assms(1) s_1 unfolding min_conv_def by simp
  thus ?thesis by argo
qed

lemma general_pos_subs: assumes "X \<subseteq> Y" and "general_pos Y"
  shows "general_pos X" 
proof(rule ccontr)
  assume "\<not>general_pos X"
  then obtain S where S:"S \<in> X~ 3" "affine_dependent S" unfolding general_pos_def by blast
  have "S \<in> Y~3" using assms(1) unfolding nsubset_def 
    by (smt (verit) \<open>S \<in> X ~ 3\<close> mem_Collect_eq nsubset_def order_trans)  
  thus False using S(2) assms(2) unfolding general_pos_def by simp 
qed


lemma assumes "cup k (y#z#ws)" and "x \<le> y"
          and "\<not> cup (Suc k) (x#y#z#ws)"
        shows "(cross3 x y z) \<ge> 0"  
  using assms unfolding cup_def list_check.simps cup3_def 
proof-
  have "sorted (x#y#z#ws)" using assms(1,2) unfolding cup_def by fastforce
  moreover have "length (x#y#z#ws) = Suc k" 
    using assms(1) cup_def by force
  ultimately have 1:"\<not>list_check cup3 (x#y#z#ws)" using assms(3) unfolding cup_def
    by presburger
  then show ?thesis unfolding list_check.simps(4) unfolding cup3_def
    using assms(1) unfolding cup_def cup3_def by argo
qed

  (*this tells us that if cross product of three elements is 0 then they are 
affine dependent*)
lemma cross_affine_dependent:assumes "cross3 a b c = 0"
  shows "affine_dependent {a, b, c}"
proof-
  have reln:"(snd b - snd a)*(fst c - fst b) = (snd c - snd b)*(fst b - fst a)" 
    using assms unfolding cross3_def by simp
  hence eqn1:"(snd b - snd a)* fst c = (snd c - snd a)*(fst b) + (snd b - snd c)*fst a"
    by argo
  from reln have eq2:"(fst b - fst a)* snd c = (fst c - fst a)* snd b - (fst c - fst b)* snd a"
    by argo
  hence "\<exists> u v. u + v = 1 \<and> fst c =  u * (fst b) + v * fst a"
  proof(cases "snd b - snd a = 0")
    case True

    then show ?thesis sorry
  next
    case False
    hence "fst c = ((snd c - snd a)/(snd b - snd a))*(fst b) + ((snd b - snd c)/(snd b - snd a))*fst a"
      by (metis (no_types, opaque_lifting) add.right_cancel diff_add_cancel diff_divide_eq_iff eqn1 mult.commute times_divide_eq_right)
    moreover have "((snd c - snd a)/(snd b - snd a)) +  ((snd b - snd c)/(snd b - snd a)) = 1"
      using False 
      by (metis add.commute add_diff_eq add_divide_distrib diff_add_cancel divide_self_if)
    ultimately show ?thesis 
      by (smt (verit))
  qed
  show ?thesis sorry
qed
(* (b2 - a2)*(c1 - b1) = (c2 - b2)*(b1 - a1)*)
(*( u(a1,a2) + (1-u)(b1,b2) = (c1,c2)*)
(* (b2-a2)/(b1-a1) = (c2-b2)/(c1-b1)*)
(* slope of a-b is same as slope of b-c *)
(* 
  have "
  unfolding affine_dependent_def affine_def hull_def*)
lemma assumes "general_pos S"
  shows "\<forall>x \<in> S. \<forall> y \<in> S. \<forall>z \<in> S. cross3 x y z = 0"
  sorry
theorem "min_conv 3 k = k"
proof(induction k)
  case 0
  then show ?case sorry
next
  case (Suc k)
  {fix S::"(real \<times> real) set"
    assume S_asm:"card S = Suc k"
    assume S_gp:"general_pos S"        
   then obtain x xs where x_xs:"S = set (x#xs)" "sorted (x#xs)" "length (x#xs) = card S"
     using S_asm by (metis One_nat_def Suc_le_length_iff card.infinite le_add1 nat.simps(3) plus_1_eq_Suc sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set.set_sorted_key_list_of_set sorted_list_of_set.sorted_sorted_key_list_of_set)
   have x_Min:"x = Min S" using x_xs 
     by (simp add: Min_insert2)
   hence "length xs = k" using S_asm x_xs by auto
   moreover have sminus_x:"card (S - {x}) = k" using S_asm 
     by (simp add: card.insert_remove x_xs(1))
   moreover have gp_sminus_x:"general_pos (S - {x})" using x_xs(1) S_gp general_pos_subs by blast
   ultimately obtain zs where  zs:"set zs \<subseteq> S - {x}" "(cap 3 zs \<or> cup k zs)" "sorted zs"
     using extract_cap_cup[OF Suc(1) sminus_x gp_sminus_x] by blast
   then have "cap 3 zs \<or> cup (Suc k) (x#zs)"
   proof(cases "cap 3 zs")
     case False
     hence F1:"cup k zs" using zs(2) by simp
     hence F2:"length zs = k" unfolding cup_def by argo
     hence F3:"sorted (x#zs)" using zs x_Min 
       by (metis (no_types, opaque_lifting) Diff_empty in_mono set_ConsD sorted_wrt.simps(2) subset_Diff_insert x_xs(1) x_xs(2))
     then show ?thesis
     proof(cases "cup (Suc k) (x#zs)")
       case False
       then obtain z1 z2 z3 zs0 where "zs = z1#z2#zs0" unfolding cup_def
         using F2 F3 list_check.simps(2,3) 
         by (metis length_Cons remdups_adj.cases)
       (* prove that if xs is a cup and x#xs is not a cup, first three elements are not a cup*)
       then show ?thesis sorry
     qed (argo)
   qed (argo)
  then show ?case sorry
qed

  obtain n where "n =min_conv 3 k"
    unfolding min_conv_def using non_empty_cup_cap 
    by blast

  (* steps above: 
  1, Show that every k-1 cap does not contain a 3-cup
2, Use that to show that if its a j-cap, where j<k, it does not contain a 3-cup
3. also show that the cap in question needs to have atleat k element set. 
4. Thus value of S needs to be atleast k*)

   {fix S
    assume asm:"card S = k \<and> general_pos S"
    have "\<exists>xs. set xs \<subseteq> S \<and> (cap k xs \<or> cup 3 xs)"
    proof-
      have "\<exists> xs. length xs = k \<and> set xs = S \<and>  sorted_wrt le_x xs"
        using asm unfolding le_x_def sorry
      show ?thesis  sorry
    qed   }
  show ?thesis sorry
qed



(*** Theorem 2.2: Let f(k, ℓ) be the smallest integer N such that any N-element planar point
set in the plane in general position contains a k-cup or an ℓ-cap. Then f(k, l) = 1 + choose(k+l-4, k-2).
***)

lemma 
  assumes "finite S"
  shows "convex hull S = convex_combin S"
  unfolding convex_combin_def using assms convex 
  using convex_hull_finite by fastforce


lemma  "\<forall> (x::'a::real_vector). 0 *\<^sub>R x = 0" by simp

(*
theorem caratheodory:
  "convex hull p =
    {x::'a::euclidean_space. \<exists>S. finite S \<and> S \<subseteq> p \<and> card S \<le> DIM('a) + 1 
                             \<and> x \<in> convex hull S}"*)

lemma assumes "(X::'a::real_vector set) \<subseteq> Y" "finite Y" "finite X"
  shows "convex_combin X \<subseteq> convex_combin Y"
proof
  fix x
  assume x:"x \<in> convex_combin X"
  obtain a where a:"x = (\<Sum> j \<in> X . a j *\<^sub>R j)" "sum a X = 1" "\<forall> i \<in> X. a i \<ge> 0" 
    unfolding convex_combin_def 
    by (smt (verit, ccfv_SIG) convex_combin_def mem_Collect_eq x)
  define b where "b = (\<lambda> s. if (s \<in> X) then a s else 0)"
  hence "sum b Y = 1" using a(2) assms
    by (metis (no_types, lifting) DiffD2 sum.mono_neutral_cong_right)
  hence "\<forall> i \<in> Y. b i \<ge> 0" unfolding b_def using a(3) assms(1) 
    using a(3) by auto
  hence "x = (\<Sum> j \<in> Y . b j *\<^sub>R j)" 
  proof-
    have "(\<Sum> j \<in> Y . b j *\<^sub>R j) = (\<Sum> j \<in> (Y - X) . b j *\<^sub>R j) + (\<Sum> j \<in> X . b j *\<^sub>R j)"
      by (simp add: assms(1) assms(2) sum.subset_diff)
    moreover have " \<forall> j \<in> (Y - X) . b j = 0"
      unfolding b_def using assms 
      by simp
    hence " \<forall> j \<in> (Y - X) . b j *\<^sub>R j = 0" 
    show ?thesis sorry
  qed
  show "x \<in> convex_combin Y" sorry
qed

lemma caratheodery:
     fixes C :: "'a::real_vector set"
      assumes "finite S"
       and "dim C = n"
     shows "convex hull S = \<Union> {convex_combin X| X. X \<in> S~(n+1)}"
proof-
  show ?thesis by  sorry
qed



(* relevant equivalent lemma for above is convex_hull_finite*)
(*from above, we can write another lemma to extract*)

(* try to instantiate R^2 in this*)
