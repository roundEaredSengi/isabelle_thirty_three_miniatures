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

end