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
    using words_subs
    by simp
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
  have "vectorspace.basis F code.CS (set (rows G))"
    using gen
    unfolding code.generating_matrix_def 
    by blast
  hence "w \<in> module.span F code.CS (set (rows G))"
    using \<open>w \<in> C\<close> vectorspace.basis_def[of F code.CS "set (rows G)", OF local.code.code_space] 
    by simp
  moreover have "finite (set (rows G))"
    by simp
  moreover have "set (rows G) \<subseteq> carrier code.CS"
    using gen
    unfolding code.generating_matrix_def
    using vectorspace.basis_def[of F "lin_map.V.vs C" "set (rows G)"] code.sub_vs
    by satx
  ultimately have 
    "w \<in> {module.lincomb code.CS a (set (rows G)) | a. a \<in> (set (rows G) \<rightarrow> carrier F)}"
    using code.sub_vs
    unfolding vectorspace_def
    using module.finite_span[of F code.CS "set (rows G)"] 
    by algebra
  hence 
    "\<exists>\<alpha>. \<alpha> \<in> set (rows G) \<rightarrow> carrier F \<and> w = module.lincomb code.CS \<alpha> (set (rows G))"
    using code.sub_vs
    unfolding vectorspace_def
    using module.span_def[of F code.CS "set (rows G)"]
    by auto
  then obtain \<alpha> :: "'a vec \<Rightarrow> 'a" where 
    "\<alpha> \<in> set (rows G) \<rightarrow> row_induced.E" and 
    lin_comb: "w = module.lincomb code.CS \<alpha> (set (rows G))"
    by auto
  have "\<forall>b \<in> set (rows G). \<exists>j \<in> {0..<m}. b = row G j"
    unfolding rows_def m_def
    by auto
  moreover have 
    "\<forall>j \<in> {0..<m}. vec (dim_row G) (\<lambda>i. lin_map.scalar_prod (row G i) v) $ j = 
      lin_map.scalar_prod (row G j) v"
    unfolding m_def
    by simp
  ultimately have "\<forall>b \<in> set (rows G). \<exists>j \<in> {0..<m}. 
    vec (dim_row G) (\<lambda>i. lin_map.scalar_prod (row G i) v) $ j = lin_map.scalar_prod b v"
    by metis
  moreover have 
    "\<forall>j \<in> {0..<m}. vec (dim_row G) (\<lambda>i. lin_map.scalar_prod (row G i) v) $ j = 
      row_induced.zero_vec $ j"
    using lin_map.mult_mat_vec_def[of G v] in_ker
    by metis
  moreover have "\<forall>j \<in> {0..<m}. row_induced.zero_vec $ j = \<zero>\<^bsub>F\<^esub>"
    unfolding row_induced.zero_vec_def
    by simp
  ultimately have "\<forall>b \<in> set (rows G). lin_map.scalar_prod b v = \<zero>\<^bsub>F\<^esub>"
    by simp
  hence "lin_map.scalar_prod w v = \<zero>\<^bsub>F\<^esub>"
    using lin_comb
    sorry
  thus "row_induced.orthogonal v w"
    unfolding row_induced.orthogonal_def
    using lin_map.scalar_prod_sym
    by metis
qed

lemma orthogonal_dim_ker:
  "vectorspace.dim F (code.VS\<lparr>carrier:=code.orthogonal_carrier\<rparr>) = 
    vectorspace.dim F (code.VS\<lparr>carrier:=lin_map.kerT\<rparr>)"
  using orthogonal_kernel
  by simp

subsection \<open>Dimensions of the Orthogonal Carrier and the Code\<close>

lemma gen_dim: "n > m"
proof -
  have "m = vectorspace.dim F code.CS"
    unfolding m_def
    using gen
    unfolding code.generating_matrix_def
    by satx
  thus ?thesis
    using code.code_dim
    by metis
qed

lemma orthogonal_dim_lower_bound:
  "vectorspace.dim F (code.VS\<lparr>carrier:=code.orthogonal_carrier\<rparr>) \<ge> n - m"
proof -
  have "vectorspace.dim F (code.VS\<lparr>carrier:=code.orthogonal_carrier\<rparr>) =
    lin_map.V.dim - vectorspace.dim F (lin_map.W.vs lin_map.imT)"
    using lin_map.rank_nullity_main[OF code.fin_dim] orthogonal_kernel
    by presburger
  moreover have "lin_map.V.dim = n"
    using code.induced_dim_n
    by satx
  moreover have "vectorspace.dim F (lin_map.W.vs lin_map.imT) \<le> m"
    using lin_map.imT_is_subspace m_def row_induced.induced_dim_n subspace.dim_le 
    by fastforce
  ultimately show ?thesis
    by presburger
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
  show code: "code E n orthogonal_carrier"
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
      unfolding linear_code_generator_def linear_code_generator_axioms_def
      using linear_code_axioms
      by satx
    have "orth_vec_space.dim \<ge> n - g_hom.m"  
      using g_hom.orthogonal_dim_lower_bound
      by satx
    moreover have "n - g_hom.m > 0"
      using g_hom.gen_dim
      by presburger
    ultimately have "orth_vec_space.dim > 0"
      by simp
    moreover have "vectorspace.dim F (VS\<lparr>carrier:={zero_vec}\<rparr>) = 0"
      by (rule local.ind.dim_zero)
    ultimately show "False"
      using trivial
      by simp
  qed
next
  assume eq_carr: "orthogonal_carrier = {v. dim_vec v = n \<and> set\<^sub>v v \<subseteq> E}"
  have "card C > 1"
    using code.code_axioms
    unfolding code_def
    by simp
  hence "\<exists>a\<in>C. \<exists>b\<in>C. a \<noteq> b"
    using distinct_elems_card[of C]
    by blast
  hence "\<not> (\<exists>w. \<forall>v \<in> C. v = w)"
    by metis
  hence "\<not> (\<forall>v \<in> C. v = \<zero>\<^bsub>VS\<^esub>)"
    by presburger
  then obtain v :: "'a vec" where "v \<noteq> \<zero>\<^bsub>VS\<^esub>" and "v \<in> C" and "dim_vec v = n"
    using words_subs
    by auto
  hence "\<exists>i \<in> {0..<n}. v $ i \<noteq> \<zero>\<^bsub>F\<^esub>"
    using eq_vecI[of v "\<zero>\<^bsub>VS\<^esub>"] kn.zero_vec_def
    by auto
  then obtain i :: nat where "v $ i \<noteq> \<zero>\<^bsub>F\<^esub>" and "i \<in> {0..<n}"
    by metis
  then have "standard_basis_vec i \<in> standard_basis_n"
    unfolding ind.kn.standard_basis_n_def
    by simp
  then have "standard_basis_vec i \<in> V"
    unfolding standard_basis_vec_def
    using induced_basis_n vectorspace.basis_def[of F VS standard_basis_n, OF ind.kn.vectorspace_VS] 
    by auto
  hence "standard_basis_vec i \<in> orthogonal_carrier"
    using eq_carr
    by metis
  hence "field.scalar_prod F (standard_basis_vec i) v  = \<zero>\<^bsub>F\<^esub>"
    using \<open>v \<in> C\<close>
    unfolding orthogonal_def
    by simp
  moreover have "field.scalar_prod F (standard_basis_vec i) v = v $ i"
    unfolding standard_basis_vec_def
    sorry
  ultimately show "False"
    using \<open>v $ i \<noteq> \<zero>\<^bsub>F\<^esub>\<close> 
    by argo
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