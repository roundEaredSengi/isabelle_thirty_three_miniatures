chapter \<open>Auxiliary Results\<close>

theory Util
  imports Thirty_Three_Miniatures_Root

begin

section \<open>Auxiliary Lemmas about the gf2 Type\<close>

lemma mod2_0_1_id:
  fixes 
    x :: nat
  assumes 
    "x \<in> {0, 1}"
  shows
    "x = x mod 2"
  using assms
  by fastforce

lemma abs_gf2_homom_mod2: "Abs_gf2 (x mod 2) + Abs_gf2 (y mod 2) = Abs_gf2 ((x + y) mod 2)"
proof (cases "even x")
  case x_even: True
  then have x_zero: "Abs_gf2 (x mod 2) = 0" using zero_gf2_def by simp
  then show ?thesis
  proof (cases "even y")
    case y_even: True
    then have "Abs_gf2 (y mod 2) = 0" using zero_gf2_def by simp
    moreover have "Abs_gf2 ((x+y) mod 2) = 0" using  x_even y_even zero_gf2_def by simp
    ultimately show ?thesis using x_zero by algebra
  next
    case y_odd: False
    then have "(y mod 2) = 1" by presburger
    then have "Abs_gf2 (y mod 2) = 1"  using one_gf2_def by argo
    moreover have "(x+y) mod 2 = 1" using x_even y_odd by presburger
    then have "Abs_gf2 ((x+y) mod 2) = 1" using one_gf2_def by simp
    ultimately show ?thesis using x_zero by algebra
  qed  
next
  case x_odd: False
  then have "x mod 2 = 1" by presburger
  then have x_one: "Abs_gf2 (x mod 2) = 1" using one_gf2_def by simp
  then show ?thesis
  proof (cases "even y")
    case y_even: True
    then have "Abs_gf2 (y mod 2) = 0" using zero_gf2_def by simp
    moreover have "(x+y) mod 2 = 1" using x_odd y_even by presburger
    then have "Abs_gf2 ((x+y) mod 2) = 1" using one_gf2_def by simp
    ultimately show ?thesis using x_one by algebra
  next
    case y_odd: False
    then have "(y mod 2) = 1" by presburger
    then have "Abs_gf2 (y mod 2) = 1"  using one_gf2_def by argo
    moreover have "(x+y) mod 2 = 0" using x_odd y_odd by presburger
    then have "Abs_gf2 ((x+y) mod 2) = 0" using zero_gf2_def by simp
    moreover have "(1::gf2) + 1 = 0" unfolding plus_gf2_def zero_gf2_def by simp
    ultimately show ?thesis using x_one by argo 
  qed
qed

lemma sum_mod_2_gf2:
  fixes 
    f :: "'x \<Rightarrow> nat" and
    X :: "'x set"
  assumes
    "\<forall>x. f x \<in> {0, 1}" 
  shows
    "finite X \<Longrightarrow> Abs_gf2 ((sum f X) mod 2) = sum (Abs_gf2 \<circ> f) X"
proof (induction "card X" arbitrary: X)
  case 0
  hence "sum f X = 0"
    by simp
  moreover have "sum (Abs_gf2 \<circ> f) X = 0"
    using "0.prems" "0.hyps"
    by simp
  ultimately show ?case
    using zero_gf2_def 
    by presburger
next
  case (Suc x)
  hence "card X > 0"
    by simp
  then obtain a :: 'x where "a \<in> X"
    by (rule Multisets_Extras.elem_exists_non_empty_set)
  hence "card (X-{a}) = x"
    using Suc.hyps
    by simp
  hence ind_hyp:
    "Abs_gf2 (sum f (X-{a}) mod 2) = sum (Abs_gf2 \<circ> f) (X-{a})"
    using Suc.hyps Suc.prems
    by blast
  have "(sum f X mod 2) = ((f a + sum f (X-{a})) mod 2)"
    by (metis \<open>a \<in> X\<close> Suc.prems sum.remove)
  then have "Abs_gf2 (sum f X mod 2) = Abs_gf2 (f a mod 2) + (Abs_gf2 (sum f (X-{a}) mod 2))" using abs_gf2_homom_mod2 by presburger
  moreover  have "\<dots> = Abs_gf2 (f a mod 2) + (sum (Abs_gf2 \<circ> f) (X - {a}))" using ind_hyp by argo
  moreover  have "\<dots> = Abs_gf2 (f a) + (sum (Abs_gf2 \<circ> f) (X - {a}))" using assms mod2_0_1_id by presburger
  moreover  have "\<dots> = (Abs_gf2 \<circ> f) a + (sum (Abs_gf2 \<circ> f) (X - {a}))" by simp
  moreover  have "\<dots> = sum (Abs_gf2 \<circ> f) X" using \<open>a \<in> X\<close> Suc.prems sum.remove by metis
  ultimately show ?case by argo
qed

section \<open>Rewriting a Set Cardinalities\<close>

lemma set_card: 
  fixes 
    X :: "'x set" and
    \<phi> :: "'x \<Rightarrow> bool"
  shows
    "finite X \<Longrightarrow> card {x | x. x \<in> X \<and> \<phi> x} = sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X"
proof (induction "card X" arbitrary: X)
  case 0
  hence "X = {}"
    by simp
  hence "{x | x. x \<in> X \<and> \<phi> x} = {}"
    by blast
  hence "card {x | x. x \<in> X \<and> \<phi> x} = 0"
    by (metis card.empty)
  moreover have "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X = 0"
    using \<open>X = {}\<close>
    by simp
  ultimately show ?case
    using "0.hyps" "0.prems"
    by simp
next
  case (Suc x)
  hence "card X > 0"
    by simp
  then obtain a :: 'x where "a \<in> X"
    by (rule Multisets_Extras.elem_exists_non_empty_set)
  have "x = card X - 1"
    using Suc.hyps
    by simp
  hence "x = card (X-{a})"
    using \<open>a \<in> X\<close>
    by simp
  hence card_minus_a:
    "card {x |x. x \<in> X-{a} \<and> \<phi> x} = (\<Sum>x\<in>X-{a}. if \<phi> x then 1::nat else 0)"
    using Suc.hyps Suc.prems
    by blast
  have 
    "{x |x. x \<in> X \<and> \<phi> x} = {x |x. x \<in> X-{a} \<and> \<phi> x} \<union> (if (\<phi> a) then {a} else {})"
    using \<open>a \<in> X\<close>
    by auto
  moreover have "{x |x. x \<in> X-{a} \<and> \<phi> x} \<inter> (if (\<phi> a) then {a} else {}) = {}"
    by simp
  moreover have "finite {x |x. x \<in> X-{a} \<and> \<phi> x}"
    using Suc.prems
    by simp
  moreover have "finite (if (\<phi> a) then {a} else {})"
    by simp
  ultimately have
    "card {x |x. x \<in> X \<and> \<phi> x} = card {x |x. x \<in> X-{a} \<and> \<phi> x} + card (if (\<phi> a) then {a} else {})"
    using card_Un_Int 
    by simp
  hence
    "card {x |x. x \<in> X \<and> \<phi> x} = 
      (\<Sum>x\<in>X - {a}. if \<phi> x then 1 else 0) + (if (\<phi> a) then 1::nat else 0)"
    using card_minus_a
    by simp
  moreover have 
    "(\<Sum>x\<in>X - {a}. if \<phi> x then 1 else 0) =
      (\<Sum>x\<in>X. if \<phi> x then 1 else 0) - (if \<phi> a then 1::nat else 0)"
    using sum_diff1[of X "\<lambda>x. if (\<phi> x) then 1::nat else 0" a] Suc.prems \<open>a \<in> X\<close>
    by (meson sum_diff1_nat)
  ultimately show ?case
    by (metis (no_types, lifting) Suc.prems \<open>a \<in> X\<close> add.commute sum.remove)
qed

section \<open>Finite Sums in Monoids\<close>

text \<open>
  Technical rewriting lemma:

  Forming the finite sum over two summands, when addition commutes, is the same as adding the two 
  summands in arbitrary order. (This can be generalized to any finite number of summands.)
\<close>

lemma (in abelian_monoid) finsum_2_elts[simp]:
  fixes
    x :: 'x and y :: 'x and f :: "'x \<Rightarrow> 'a"
  assumes
    "x \<noteq> y" and
    "f \<in> {x,y} \<rightarrow> carrier G"
  shows
    "(\<Oplus>\<^bsub>G\<^esub>v\<in>{x,y}. f v) = f x \<oplus>\<^bsub>G\<^esub> f y"
proof -
  have "{x,y} = insert y {x}"
    using assms
    by blast
  hence "(\<Oplus>\<^bsub>G\<^esub>v\<in>{x,y}. f v) = finsum G f (insert x {y})"
    by simp
  (* TODO why does "also" fail? *)
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> finsum G f {y}"
    using finsum_insert[of "{y}" x f] assms
    by simp
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> (f y \<oplus>\<^bsub>G\<^esub> finsum G f {})"
    using finsum_insert[of "{}" y f] assms
    by simp
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> (f y \<oplus>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub>)"
    using finsum_empty[of f]
    by metis
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> f y"
    using assms
    by simp
  ultimately show ?thesis
    by simp
qed

end