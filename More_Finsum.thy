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

end