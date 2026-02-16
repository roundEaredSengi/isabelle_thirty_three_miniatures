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
    orthogonal_carrier = induced_subspace.orthogonal_carrier F C n;
    orthogonal_generating_matrix = linear_code.generating_matrix F orthogonal_carrier n 
  in
    orthogonal_generating_matrix G"


lemma (in linear_code) orthogonal_linear_code:
  "linear_code F (induced_subspace.orthogonal_carrier F C n) n"
  sorry

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
  moreover have "row P i = rows P ! i" using assms by simp
  then have "row P i \<in> set (rows P)" using assms nth_mem length_rows[of P] by metis
  then have "row P i \<in> induced_subspace.orthogonal_carrier F C n"
    using assms
    unfolding parity_check_matrix_def
    unfolding Let_def
    unfolding linear_code.generating_matrix_def[OF orthogonal_linear_code, of P]
    using vectorspace.basis_def
    by (metis (no_types, lifting) ext linear_code.code_space orthogonal_linear_code subset_code(1)
        vectorspace.carrier_vs_is_self vs)
  then have "induced_vs.orthogonal F (row P i) v"
    using assms
    using orthogonal_carrier_def by auto
  then have "field.scalar_prod F (row P i) v = \<zero>\<^bsub>F\<^esub>"
    unfolding orthogonal_def
    by satx
    ultimately show "?prod $ i = \<zero>\<^bsub>F\<^esub>" by presburger
qed

end