theory GeneratingMatrix
  imports "LinearCode"
   Jordan_Normal_Form.VS_Connect
   CarriersetMatrix
begin

section \<open>Generating and Parity Check Matrix of a Linear Code\<close>

hide_const (open) Matrix.scalar_prod
hide_const (open) Matrix.mult_mat_vec

definition (in linear_code) generating_matrix:: "'a mat \<Rightarrow> bool"
  where "generating_matrix G \<equiv>
      dim_row G = (vectorspace.dim F CS)
      \<and> dim_col G = n
      \<and> vectorspace.basis F CS (set (rows G))"

lemma (in linear_code) generating_matrix_exists:
  "\<exists>G :: 'a mat. generating_matrix G"
proof -
  interpret space: vectorspace F CS
    by (rule local.code_space)
  have "\<exists>B. finite B \<and> space.basis B"
    using space.finite_basis_exists[OF code_fin_dim]
    by blast
  then obtain B :: "'a vec set" where "space.basis B" and "finite B"
    by blast
  hence "B \<subseteq> carrier CS"
    unfolding space.basis_def
    by satx
  moreover have "carrier CS \<subseteq> V"
    sorry
  ultimately have dim_col: "\<forall>b \<in> B. dim_vec b = n"
    by blast
  have "card B = vectorspace.dim F CS"
    using \<open>space.basis B\<close> \<open>finite B\<close>
    using space.dim_basis[of B]
    by simp
  (* TODO: define matrix ?G with rows = vectors of B *)
  thus "Ex generating_matrix"
    sorry
qed

text \<open>The reference now claims that every linear code has a generating matrix
in standard form (where the left side of the matrix is $I_k$). This does not make sense
(consider the linear code of all vectors $0v \<in> A^(n+1), v \<in> A^n) and is refuted
by \<^cite>\<open>\<open>Example 4.5.11\<close> in Ling_Xing_2004\<close>\<close>

definition (in linear_code) parity_check_matrix:: "'a mat \<Rightarrow> bool"
  where "parity_check_matrix G \<equiv> let
    orthogonal_generating_matrix = linear_code.generating_matrix F orthogonal_carrier n 
  in
    orthogonal_generating_matrix G"

subsection \<open>Generating Matrix as a Linear Map\<close>

locale linear_code_generator = code: linear_code +
  fixes G :: "'a mat"
  assumes gen: "code.generating_matrix G"
begin

definition m :: nat where "m \<equiv> dim_row G"

abbreviation RS where "RS \<equiv> induced_vs.VS F m"

fun generator_hom :: "'a vec \<Rightarrow> 'a vec" where
  "generator_hom v = field.mult_mat_vec F G v"

interpretation row_induced: induced_vs F m
  by (rule local.code.induced_vs_axioms)

interpretation lin_map: 
  linear_map F code.VS "induced_vs.VS F m" generator_hom
proof (unfold linear_map_def, safe)
  show "vectorspace F code.VS"
    by (rule local.code.vectorspace_VS)
next
  show "vectorspace F RS"
    by (rule local.row_induced.vectorspace_VS)
next
  show "mod_hom F code.VS RS generator_hom"
    sorry
qed

subsection \<open>Code as the Image of the Generating Matrix\<close>

lemma code_img_gen: "code.CS = RS\<lparr>carrier:=lin_map.imT\<rparr>"
  sorry

subsection \<open>Orthogonal Carrier as the Kernel of the Generating Matrix\<close>

lemma orthogonal_kernel:
  "code.orthogonal_carrier = lin_map.kerT"
proof (unfold lin_map.ker_def, simp, safe)
  fix v :: "'a vec"
  assume 
    dim: "n = dim_vec v" and 
    vec: "set\<^sub>v v \<subseteq> code.E" and 
    orth: "Ball C (code.orthogonal v)"
  have "set (rows G) \<subseteq> carrier (lin_map.V.vs C)"
    using gen 
          vectorspace.basis_def[of F "lin_map.V.vs C" "set (rows G)", OF code.code_space]
    unfolding code.generating_matrix_def
    by satx
  moreover have "... = C"
    by (rule local.lin_map.V.carrier_vs_is_self)
  ultimately have "\<forall>i \<in> {0..<dim_row G}. row G i \<in> C"
    using rows_def[of G]
    by auto
  hence "\<forall>i \<in> {0..<dim_row G}. field.scalar_prod F (row G i) v = \<zero>\<^bsub>F\<^esub>"
    using orth field.scalar_prod_sym[of F, OF lin_map.field_axioms]
    unfolding code.orthogonal_def
    by metis
  hence "lin_map.mult_mat_vec G v = vec m (\<lambda>i. \<zero>\<^bsub>F\<^esub>)"
    unfolding lin_map.mult_mat_vec_def m_def
    by auto
  moreover have "induced_vs F"
    using m_def code.induced_subspace_axioms
    unfolding induced_subspace_def
    by satx
  ultimately show "lin_map.mult_mat_vec G v = induced_vs.zero_vec F m"
    using induced_vs.zero_vec_def[of F m] m_def code.induced_subspace_axioms
    by metis
next
  fix v :: "'a vec" and w :: "'a vec"
  assume 
    in_C: "w \<in> C" and
    dim: "n = dim_vec v" and 
    vec: "set\<^sub>v v \<subseteq> code.E" and 
    in_ker: "lin_map.mult_mat_vec G v = row_induced.zero_vec"
  show "row_induced.orthogonal v w"
    sorry
qed

lemma orthogonal_dim_ker:
  "vectorspace.dim F (code.VS\<lparr>carrier:=code.orthogonal_carrier\<rparr>) = 
    vectorspace.dim F (code.VS\<lparr>carrier:=lin_map.kerT\<rparr>)"
  using orthogonal_kernel
  by simp

subsection \<open>Dimensions of the Orthogonal Carrier and the Code\<close>

lemma orthogonal_dim_img:
  "vectorspace.dim F (code.VS\<lparr>carrier:=code.orthogonal_carrier\<rparr>) = 
    n - vectorspace.dim F code.CS"
proof -
  have "vectorspace.dim F (code.VS\<lparr>carrier:=code.orthogonal_carrier\<rparr>) =
    lin_map.V.dim - vectorspace.dim F (lin_map.W.vs lin_map.imT)"
    using lin_map.rank_nullity_main[OF code.fin_dim] orthogonal_kernel
    by presburger
  moreover have "lin_map.V.dim = n"
    using code.induced_dim_n
    by satx
  moreover have "RS\<lparr>carrier:=lin_map.imT\<rparr> = (lin_map.W.vs lin_map.imT)"
    by simp
  ultimately show ?thesis
    using code_img_gen
    by simp
qed

end

subsection \<open>Orthogonal Carrier is also a Linear Code\<close>

lemma (in linear_code) orthogonal_linear_code:
    "linear_code F orthogonal_carrier n"
proof (unfold linear_code_def linear_code_axioms_def, safe)
  show "induced_subspace F orthogonal_carrier n"     
    by (rule local.ind.orthogonal_subspace)
next
  have "orthogonal_carrier \<subseteq> words" by auto
  have "finite orthogonal_carrier" using finite by fastforce
  show "code E n orthogonal_carrier"
  proof (standard, simp add: finite_alphabet, safe)
    assume "\<not> 1 < card orthogonal_carrier" and "finite orthogonal_carrier"
    then have card: "card orthogonal_carrier \<le> 1"
      by linarith
    moreover have "zero_vec \<in> orthogonal_carrier"
      using zero_orthogonal zero_vec_in_v words_subs by auto
    then have "{zero_vec} \<subseteq> orthogonal_carrier" by simp
    then have "card {zero_vec} \<le> card orthogonal_carrier"
      using \<open>finite orthogonal_carrier\<close> card_mono
      by blast
    ultimately have trivial: "{zero_vec} = orthogonal_carrier"
      using \<open>{zero_vec} \<subseteq> orthogonal_carrier\<close> \<open>finite orthogonal_carrier\<close>
      by (simp add: card_subset_eq)
    interpret orth_ind_space: induced_subspace F orthogonal_carrier n
      by (rule local.ind.orthogonal_subspace)
    interpret orth_vec_space: vectorspace F orth_ind_space.subspace_obj
      by (rule local.orth_ind_space.sub_vs)
    from generating_matrix_exists obtain G :: "'a mat" where "generating_matrix G"
      by meson
    then interpret g_hom: linear_code_generator F C n G
      sorry
    have "orth_vec_space.dim = n - vectorspace.dim F CS"  
      using g_hom.orthogonal_dim_img
      by satx
    also have "... > 0"
      using code_dim
      by presburger
    finally have "orth_vec_space.dim > 0"
      by simp
    moreover have "vectorspace.dim F (VS\<lparr>carrier:={zero_vec}\<rparr>) = 0"
      using induced_subspace.dim_zero[of F "{zero_vec}" n F]
      sorry
    ultimately show "False"
      using trivial
      by simp
  qed
next
  assume "orthogonal_carrier = {v. dim_vec v = n \<and> set\<^sub>v v \<subseteq> E}"
  show "False"
    sorry
qed

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
  interpret orth_lin: linear_code F orthogonal_carrier n
    using orthogonal_linear_code
    by blast
  have "vectorspace.basis F (W\<lparr>carrier := orthogonal_carrier\<rparr>) (set (rows P))"
    using assms
    unfolding parity_check_matrix_def
    unfolding Let_def
    using orth_lin.generating_matrix_def
    using orth_lin.orthogonal_linear_code
    by algebra
  then have "set (rows P) \<subseteq> orthogonal_carrier"
    using orth_lin.linear_code_axioms orth_lin.code_space
    using vectorspace.basis_def[of F "W\<lparr>carrier := orthogonal_carrier\<rparr>"]
    by simp
  moreover have "rows P ! i \<in> set (rows P)"
    using assms rows_def[of P]
    by simp
  ultimately have "rows P ! i \<in> orthogonal_carrier"
    by blast
  then have "row P i \<in> orthogonal_carrier" using assms by simp
  then have "induced_vs.orthogonal F (row P i) v"
    using assms
    by auto
  then have "field.scalar_prod F (row P i) v = \<zero>\<^bsub>F\<^esub>"
    unfolding orthogonal_def
    by satx
  moreover have "field.scalar_prod F (row P i) v = ?prod $ i"
    using field.mult_mat_vec_def[of F P v] linear_code_axioms assms
    unfolding linear_code_def induced_subspace_def induced_vs_def
    by simp
  ultimately show "?prod $ i = \<zero>\<^bsub>F\<^esub>"
    by simp
qed

end