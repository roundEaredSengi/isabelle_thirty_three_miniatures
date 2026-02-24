theory CarriersetMatrix
  imports "../Thirty_Three_Miniatures_Root"
begin

hide_const (open) Matrix.scalar_prod
hide_const (open) Matrix.mult_mat_vec

definition (in field) scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a" (infix \<open>\<bullet>\<close> 70)
  where "v \<bullet> w \<equiv> (\<Oplus>i \<in> {0 ..< dim_vec w}. (v $ i) \<otimes> (w $ i))"

lemma (in field) scalar_prod_closed:
  assumes
    "set\<^sub>v v \<subseteq> carrier R"
    "set\<^sub>v w \<subseteq> carrier R"
  shows
    "scalar_prod v w \<in> carrier R"
  sorry

lemma (in field) scalar_prod_sym: "scalar_prod v w = scalar_prod w v"
proof -
  have "scalar_prod v w = (\<Oplus>i \<in> {0 ..< dim_vec w}. (v $ i) \<otimes> (w $ i))"

definition (in field) mult_mat_vec :: "'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl \<open>*\<^sub>v\<close> 70)
  where "mult_mat_vec A v \<equiv> vec (dim_row A) (\<lambda> i. row A i \<bullet> v)"

end