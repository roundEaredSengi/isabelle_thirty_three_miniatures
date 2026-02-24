theory CarriersetMatrix
  imports "../Thirty_Three_Miniatures_Root"
begin

hide_const (open) Matrix.scalar_prod
hide_const (open) Matrix.mult_mat_vec

definition (in field) scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a" (infix \<open>\<bullet>\<close> 70)
  where "v \<bullet> w \<equiv> (\<Oplus>i \<in> {0 ..< dim_vec w}. (v $ i) \<otimes> (w $ i))"

lemma (in field) scalar_prod_closed:
  assumes
    "dim_vec v = dim_vec w"
    "set\<^sub>v v \<subseteq> carrier R"
    "set\<^sub>v w \<subseteq> carrier R"
  shows
    "scalar_prod v w \<in> carrier R"
proof -
  have "(\<lambda>i. (v $ i) \<otimes> (w $ i)) \<in> {0..<dim_vec w} \<rightarrow> carrier R"
  proof
    fix x
    assume x: "x \<in> {0..<dim_vec w}"
    from x assms have "v$x \<in> carrier R" using vec_set_def by fastforce
    moreover from x assms have "w$x \<in> carrier R" using vec_set_def by force
    ultimately show "(v $ x) \<otimes> (w $ x) \<in> carrier R" by simp
  qed
  then show ?thesis
    unfolding scalar_prod_def
    using finsum_closed
    by simp
qed

lemma (in field) scalar_prod_sym:
  assumes
    "dim_vec w = dim_vec v"
    "vec_set v \<subseteq> carrier R"
    "vec_set w \<subseteq> carrier R"
  shows
    "scalar_prod v w = scalar_prod w v"
proof -
  have swap_func: "(\<lambda>i. (w $ i) \<otimes> (v $ i)) \<in> {0..<dim_vec w} \<rightarrow> carrier R"
  proof
    fix x
    assume x_b: "x \<in> {0..<dim_vec w}"
    then have "w $ x \<in> carrier R"
      using assms vec_set_def by force
    moreover have "v $ x \<in> carrier R"
      using assms vec_set_def x_b
      by fastforce
    ultimately show "w $ x \<otimes> v $ x \<in> carrier R"
      by algebra
  qed
  have swap_equiv: "\<And>i. i \<in> {0..<dim_vec w} \<Longrightarrow> (w $ i) \<otimes> (v $ i) = (v $ i) \<otimes> (w $ i)" 
  proof -
 fix i
    assume x_b: "i \<in> {0..<dim_vec w}"
    then have "w $ i \<in> carrier R"
      using assms vec_set_def by force
    moreover have "v $ i \<in> carrier R"
      using assms vec_set_def x_b
      by fastforce
    ultimately show "w $ i \<otimes> v $ i = v$i \<otimes> w$i"
      by algebra
  qed

  have "scalar_prod v w = (\<Oplus>i \<in> {0 ..< dim_vec w}. (v $ i) \<otimes> (w $ i))"
    using scalar_prod_def by presburger
  also have "\<dots> = (\<Oplus>i \<in> {0 ..< dim_vec w}. (w $ i) \<otimes> (v $ i))"
    using finsum_cong'[OF _ swap_func, of "{0..<dim_vec w}" "\<lambda>i. v$i \<otimes> w$i"]
    using swap_equiv
    by presburger
  also have "\<dots> = (\<Oplus>i \<in> {0 ..< dim_vec v}. (w $ i) \<otimes> (v $ i))"
    using assms
    by presburger
  also have "\<dots> = scalar_prod w v"
    using scalar_prod_def by presburger
  finally show ?thesis .
qed

definition (in field) mult_mat_vec :: "'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl \<open>*\<^sub>v\<close> 70)
  where "mult_mat_vec A v \<equiv> vec (dim_row A) (\<lambda> i. row A i \<bullet> v)"

end