theory Definitions
  imports Main          
          "~~/src/HOL/Library/Product_Lexorder"
          "~~/src/HOL/Analysis/Cartesian_Euclidean_Space"
          "HOL-Library.Sublist"

begin

abbreviation
  "sortedStrict \<equiv> sorted_wrt (<)"

definition nsubset::"'a set \<Rightarrow> nat \<Rightarrow> ('a set) set" (infix "~" 76)
  where
"nsubset S k = {X. X \<subseteq> S \<and>  card X = k}"

(*** defs gen-position, k-cup, l-cup ***)
definition general_pos::"((real\<times>real) set) \<Rightarrow> bool" where
"general_pos S \<equiv>  (\<forall> P3 \<in> S~3. \<not> affine_dependent P3)"

(*we define a set of points to be in a convex position if none of the points 
belong to the convex hull of the rest*)
(*a set of points in a convex position can be thought of as the minimal specification set
of a convex hull*)
definition convex_pos::"('a::euclidean_space set) \<Rightarrow> bool"
  where
"convex_pos S \<equiv>  (\<forall> s \<in> S. convex hull S \<noteq> convex hull (S - {s}))"

type_synonym R2 = "real \<times> real"

definition cross3 :: "R2 \<Rightarrow> R2 \<Rightarrow> R2 \<Rightarrow> real" where
"cross3 a b c \<equiv> (fst b - fst a) * (snd c - snd b) - (fst c - fst b) * (snd b - snd a)"

definition cup3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"cup3 a b c \<equiv>  cross3 a c b < 0"

definition cap3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"cap3 a b c \<equiv>  cross3 a c b > 0"

definition collinear3 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" where
"collinear3 a b c \<equiv> cross3 a c b = 0"

(* observation: \<not> collinear3 a b c = general_pos_2D {a,b,c} *)

fun list_check :: "(_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> _ list \<Rightarrow> bool" where
  "list_check f [] = True"
| "list_check f (a#[]) = True"
| "list_check f (a#b#[]) = (a \<noteq> b)"
| "list_check f (a#b#c#rest) = (f a b c \<and> list_check f (b#c#rest))"

definition cap::"nat \<Rightarrow> (real\<times>real) list \<Rightarrow> bool" where
"cap k L \<equiv> (k = length L) \<and> (sortedStrict L) \<and> (list_check cap3 L)"

definition cup :: "nat \<Rightarrow> (real \<times> real) list \<Rightarrow> bool" where
"cup k L \<equiv> (k = length L) \<and> (sortedStrict L) \<and> (list_check cup3 L)"

(* definition of minimum number of points containing an l-cup or k-cap *)
(* distinctness is taken care of by the fact that cap or cup needs to have distinct points*)
(*distinctness *)
definition min_conv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"min_conv k l = (Inf {n . (\<forall>S . card S \<ge> n \<and> general_pos S 
                \<longrightarrow> (\<exists>xs. set xs \<subseteq> S \<and> (sortedStrict xs) \<and> (cap k xs \<or> cup l xs)))})"

end