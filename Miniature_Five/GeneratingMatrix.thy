theory GeneratingMatrix
  imports "LinearCode"
   Jordan_Normal_Form.VS_Connect
   CarriersetMatrix
begin

hide_const (open) Matrix.scalar_prod
hide_const (open) Matrix.mult_mat_vec

definition (in linear_code) generating_matrix:: "'a mat \<Rightarrow> bool"
  where "generating_matrix G \<equiv>
      dim_row G = (vectorspace.dim F CS)
      \<and> dim_col G = n
      \<and> vectorspace.basis F CS (set (rows G))"

text \<open>The reference now claims that every linear code has a generating matrix
in standard form (where the left side of the matrix is $I_k$). This does not make sense
(consider the linear code of all vectors $0v \<in> A^(n+1), v \<in> A^n) and is refuted
by \<^cite>\<open>\<open>Example 4.5.11\<close> in Ling_Xing_2004\<close>\<close>

definition (in linear_code) parity_check_matrix:: "'a mat \<Rightarrow> bool"
  where "parity_check_matrix G \<equiv> let
    orthogonal_generating_matrix = linear_code.generating_matrix F orthogonal_carrier n 
  in
    orthogonal_generating_matrix G"


lemma (in linear_code) orthogonal_linear_code:
  shows
    "linear_code F orthogonal_carrier n"
(*proof -
  have "induced_subspace F orthogonal_carrier n" sorry

  moreover have "code (carrier F) n orthogonal_carrier"
  proof (standard, unfold orthogonal_carrier_def, simp add: finite_alphabet assms, auto)
    assume "\<not> Suc 0 < card {v. dim_vec v = n \<and> set\<^sub>v v \<subseteq> E \<and> (\<forall>x\<in>C. local.orthogonal v x)}"
    then have "card {v. dim_vec v = n \<and> set\<^sub>v v \<subseteq> E \<and> (\<forall>x\<in>C. local.orthogonal v x)} \<le> 1"
      by linarith
    

  ultimately show ?thesis using linear_code_def by metis
qed*) sorry

lemma (in linear_code) parity_check:
  assumes
    "parity_check_matrix P"
    "v \<in> C"
    "i < dim_row P"
  shows
    "(field.mult_mat_vec F P v) $ i = \<zero>\<^bsub>F\<^esub>"
proof -

  let ?prod = "field.mult_mat_vec F P v"

  have "?prod $ i = field.scalar_prod F (row P i) v"
    using assms
    unfolding field.mult_mat_vec_def[OF field_F]
    by simp
  moreover have "linear_code F orthogonal_carrier n" sorry
  then have "vectorspace.basis F (W\<lparr>carrier := orthogonal_carrier\<rparr>) (set (rows P))"
    using assms
    unfolding parity_check_matrix_def
    unfolding Let_def
    using linear_code.generating_matrix_def
    using orthogonal_linear_code
    by metis
  then have "set (rows P) \<subseteq> orthogonal_carrier"
    using orthogonal_linear_code linear_code.code_space
    using vectorspace.basis_def by fastforce
  then have "rows P ! i \<in> orthogonal_carrier"
    using assms length_rows[of P] nth_mem subset_eq by metis
  then have "row P i \<in> orthogonal_carrier" using assms by simp
  then have "induced_vs.orthogonal F (row P i) v"
    using assms
    using orthogonal_carrier_def by auto
  then have "field.scalar_prod F (row P i) v = \<zero>\<^bsub>F\<^esub>"
    unfolding orthogonal_def
    by satx
  ultimately show "?prod $ i = \<zero>\<^bsub>F\<^esub>" by presburger
qed

end