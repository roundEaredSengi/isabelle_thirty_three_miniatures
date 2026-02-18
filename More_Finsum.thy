theory More_Finsum
  imports Thirty_Three_Miniatures_Root

begin

thm abelian_monoid.finsum_insert

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

lemma (in abelian_monoid) finsum_eq: 
  (* TODO should hold in general but induction would fail without commutativity? *)
  fixes 
    f :: "'x \<Rightarrow> 'a" and g :: "'x \<Rightarrow> 'a" and X :: "'x set"
  assumes
    "\<forall>x \<in> X. f x = g x" and "f \<in> X \<rightarrow> carrier G" and "g \<in> X \<rightarrow> carrier G"
  shows
    "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. f v) = (\<Oplus>\<^bsub>G\<^esub>v\<in>X. g v)"
proof (cases "finite X")
  case True
  then show ?thesis
    using assms
  proof (induction "card X" arbitrary: X f g)
    case 0
    hence "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. f v) = \<one>\<^bsub>add_monoid G\<^esub>"
      unfolding finsum_def finprod_def
      using foldD_empty[of "\<one>\<^bsub>add_monoid G\<^esub>" "carrier (add_monoid G)" "(\<otimes>\<^bsub>add_monoid G\<^esub>) \<circ> f"] assms
      by simp
    moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. g v) = \<one>\<^bsub>add_monoid G\<^esub>"
      unfolding finsum_def finprod_def 
      using 0 assms foldD_empty[of "\<one>\<^bsub>add_monoid G\<^esub>" "carrier (add_monoid G)" "(\<otimes>\<^bsub>add_monoid G\<^esub>) \<circ> g"]
      by simp
    ultimately show ?case 
      by simp
  next
    case (Suc n)
    hence "X \<noteq> {}" by auto
    then obtain x :: 'x where "x \<in> X" by blast
    have func_f: "f \<in> X - {x} \<rightarrow> carrier G"
      using Suc
      unfolding Pi_def
      by simp
    have func_g: "g \<in> X - {x} \<rightarrow> carrier G"
      using Suc
      unfolding Pi_def
      by simp
    have elt_f: "f x \<in> carrier G"
      using Suc \<open>x \<in> X\<close>
      unfolding Pi_def
      by simp
    have elt_g: "g x \<in> carrier G"
      using Suc \<open>x \<in> X\<close>
      unfolding Pi_def
      by simp
    from \<open>x \<in> X\<close> have "card (X - {x}) = n"
      using Suc
      by simp
    moreover have fin: "finite (X - {x})" using Suc by simp
    ultimately have "(\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). f v) = (\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). g v)" 
      using Suc
      by blast
    moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). f v) = f x \<oplus>\<^bsub>G\<^esub> (\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). f v)"
      using finsum_insert[of "X - {x}" x f, OF fin _ func_f elt_f]
      by simp
    moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). g v) = g x \<oplus>\<^bsub>G\<^esub> (\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). g v)"
      using finsum_insert[of "X - {x}" x g, OF fin _ func_g elt_g]
      by simp
    moreover have "f x = g x"
      using \<open>x \<in> X\<close> Suc
      by blast
    ultimately have "(\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). f v) = (\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). g v)"
      by simp
    moreover have "insert x (X - {x}) = X"
      using \<open>x \<in> X\<close>
      by blast
    ultimately show ?case by simp
  qed
next
  case False
  hence "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. f v) = \<one>\<^bsub>add_monoid G\<^esub>"
    unfolding finsum_def finprod_def
    by simp
  moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. g v) = \<one>\<^bsub>add_monoid G\<^esub>"
    using False
    unfolding finsum_def finprod_def
    by simp
  ultimately show ?thesis
    by simp
qed

end