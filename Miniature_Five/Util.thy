theory Util
  imports "../Thirty_Three_Miniatures_Root"
begin

lemma distinct_elems_card[simp]:
  assumes
    "card S > 1 \<or> \<not>finite S"
  shows
    "\<exists> a \<in> S . \<exists> b \<in> S . a \<noteq> b"
proof (cases "finite S")
  case finite: True
  show ?thesis proof -
    have card: "card S > 1" using finite assms by satx

    obtain x where "x \<in> S" using assms by fastforce

    then have "card (S - {x}) > 0" using card by auto

    then have "\<exists> b \<in> S . x \<noteq> b" proof -
      obtain y where "y \<in> (S - {x})"
        using \<open>card (S - {x}) > 0\<close> by (rule elem_exists_non_empty_set)
      then have "x \<noteq> y \<and> y \<in> S" by blast
      then show ?thesis by metis
    qed
    then show ?thesis using \<open>x \<in> S\<close> by metis
  qed
next
  case infinite: False
  then show ?thesis
    by (metis ID.set_finite finite_subset singleton_iff subsetI)
qed

lemma lists_of_finite_set:
  fixes
    n::nat
  assumes
    "finite (S::'a set)"
  shows
    "finite { l. length l = n \<and> set l \<subseteq> S}"
proof(induction n)
  case (Suc n)
  then have "{xs::'a list. length xs = Suc n \<and> set xs \<subseteq> S} = (\<Union>x \<in> S. (#) x ` {xs. length xs = n \<and>  set xs \<subseteq> S})"
    using length_Suc_conv by (auto simp: length_Suc_conv)
  then show ?case using Suc assms by simp
qed simp

lemma map_finite:
  assumes
    "finite S"
  shows
    "finite {f x | x . x \<in> S \<and> P x}"
  using assms by simp

lemma distinct_vec_diff_index[simp]:
  assumes
    "dim_vec x = dim_vec y"          
    "x \<noteq> y"
  shows
    "\<exists>i \<in> {0..<dim_vec x} . x$i \<noteq> y$i"
  using assms by auto


lemmas (in vectorspace) additive_inverse = local.module.M.r_neg
lemmas (in vectorspace) additive_inverse_closed = local.module.M.add.inv_closed

lemma (in vectorspace) subspace_inverse_equal:
  assumes
    "subspace K W V"
    "x \<in> W"
  shows
    "\<ominus>\<^bsub>V\<^esub> x = \<ominus>\<^bsub>vs W\<^esub> x"
proof -
  let ?WS = "vs W"
  let ?WSA = "(add_monoid ?WS)"                

  have "x \<in> carrier V"
    using assms
    unfolding subspace_def
    using submodule.subset
    by auto
  then have "x \<in> carrier (add_monoid V)"
    by auto

  have "Units ?WSA = W"
    using subspace_is_vs[OF assms(1)] carrier_vs_is_self[of W]
    using vectorspace_def[of K ?WS]  module_def abelian_group_def abelian_group_axioms_def[of ?WS]
    using comm_group_def
    using group.Units_eq[of ?WSA]
    by auto
  then have "x \<in> Units ?WSA" using assms by presburger

  let ?u = "\<ominus>\<^bsub>V\<^esub> x"
  let ?v = "\<ominus>\<^bsub>?WS\<^esub> x"

  have "\<zero>\<^bsub>V\<^esub> = \<zero>\<^bsub>?WS\<^esub>" by simp
  also have "\<dots> = x \<oplus>\<^bsub>?WS\<^esub> ?v"
    using vectorspace.additive_inverse subspace_is_vs carrier_vs_is_self assms
    by metis
  also have "\<dots> = x \<oplus>\<^bsub>V\<^esub> ?v" by simp
  moreover have "?v \<in> carrier ?WS"
    using assms subspace_is_vs carrier_vs_is_self vectorspace.additive_inverse_closed
    by metis
  then have "?v \<in> carrier V"
    using assms subspace_def submodule.subset
    by fastforce
  moreover from calculation have "?v \<oplus>\<^bsub>V\<^esub> x = \<zero>\<^bsub>V\<^esub>"
    using M.a_comm[OF \<open>x \<in> carrier V\<close>] by presburger
  ultimately show "?u = ?v"
    using M.add.inv_unique'[OF \<open>x \<in> carrier V\<close> \<open>?v \<in> carrier V\<close>]
    unfolding a_inv_def
    by argo
qed

lemma (in vectorspace) eq_equiv_diff_zero:
  assumes
    "u \<in> carrier V"
    "v \<in> carrier V"
    "u \<noteq> v"
  shows
    "(u \<ominus>\<^bsub>V\<^esub> v) \<noteq> \<zero>\<^bsub>V\<^esub>"
proof (rule ccontr)
  assume "\<not> u \<ominus>\<^bsub>V\<^esub> v \<noteq> \<zero>\<^bsub>V\<^esub>"
  then have eq_z: "u \<oplus>\<^bsub>V\<^esub> (\<ominus>\<^bsub>V\<^esub> v) = \<zero>\<^bsub>V\<^esub>" unfolding a_minus_def by simp
  then have "inv\<^bsub>add_monoid V\<^esub> (\<ominus>\<^bsub>V\<^esub> v) = u"
    using M.add.inv_equality[OF eq_z] assms additive_inverse_closed
    by simp
  then have "inv\<^bsub>add_monoid V\<^esub> (inv\<^bsub>add_monoid V\<^esub> v) = u" using a_inv_def by metis
  then have "v = u"
    using M.add.inv_inv assms
    by simp
  then show "False" using assms by presburger
qed

lemma (in vectorspace) subtraction_closed:
  assumes
    "u \<in> carrier V"
    "v \<in> carrier V"
  shows
    "u \<ominus>\<^bsub>V\<^esub> v \<in> carrier V"
  unfolding a_minus_def
  using assms M.add.inv_closed assms R.a_closed
  by simp 

end