theory MoreVectorspace
  imports InducedVectorspace

begin

lemma (in subspace) dim_le: "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) \<le> vectorspace.dim K V" 
  using vectorspace.dim_li_is_basis
  sorry

lemma (in subspace) dim_eq_imp_space_eq: 
  "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = vectorspace.dim K V \<Longrightarrow> carrier V = W"
  sorry

lemma (in subspace) fin_sub_dim:
  assumes "vectorspace.fin_dim K V"
  shows "vectorspace.fin_dim K (V\<lparr>carrier:=W\<rparr>)"
proof -

  note module = module.submodule_is_module[OF submodule.module[OF submod] vectorspace.is_module[OF vs subspace_axioms]]

  have "\<exists>B. vectorspace.basis K (V\<lparr>carrier:=W\<rparr>) B" sorry
  then obtain B where "vectorspace.basis K (V\<lparr>carrier:=W\<rparr>) B"
    by presburger
  then have basis:
    "(module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B) \<and>
     (module.gen_set K (V\<lparr>carrier:=W\<rparr>) B) \<and>
     (B \<subseteq> carrier (V\<lparr>carrier:=W\<rparr>))"
    using vectorspace.basis_def[OF vectorspace.subspace_is_vs[OF vs subspace_axioms], of B]
    by satx
  then have "B \<subseteq> carrier V"
    using submodule.subset[OF submod]
    by auto
  moreover have "module.lin_indpt K V B" using basis unfolding module.lin_dep_def[OF module]
    by (metis basis module.carrier_vs_is_self module.span_li_not_depend(2) submod vectorspace_def vs)
  ultimately have "finite B"
    using vectorspace.fin_dim_li_fin[OF vs] assms
    by presburger
  then show ?thesis
    using basis subspace_axioms vectorspace.fin_dim_def vectorspace.subspace_is_vs vs
    by blast
qed


lemma (in vectorspace) trivial_space:
  "subspace K {\<zero>\<^bsub>V\<^esub>} V"
proof (unfold subspace_def, safe)
  show "vectorspace K V"
    by (rule local.vectorspace_axioms)
next
  have "module K V" using vectorspace_axioms vectorspace_def by metis
  then show "LinearCombinations.submodule K {\<zero>\<^bsub>V\<^esub>} V"
    by (unfold submodule_def, safe, simp_all)
qed

lemma (in vectorspace) trivial_space_dim_zero:
  "vectorspace.dim K (V\<lparr>carrier:={\<zero>\<^bsub>V\<^esub>}\<rparr>) = 0"
proof -
  interpret zero_space: vectorspace K "V\<lparr>carrier:={\<zero>\<^bsub>V\<^esub>}\<rparr>"
    using trivial_space
    by (rule subspace_is_vs)
  have "zero_space.basis {}" proof (unfold zero_space.basis_def, safe, simp_all)
    assume "zero_space.lin_dep {}"
    then obtain A a v where
      "finite A"
      "A \<subseteq> {}"
      "a \<in> A \<rightarrow> carrier K"
      "zero_space.lincomb a A = \<zero>\<^bsub>vs {\<zero>\<^bsub>V\<^esub>}\<^esub>"
      "v \<in> A"
      "a v \<noteq> \<zero>\<^bsub>K\<^esub>"
      unfolding zero_space.lin_dep_def[of "{}"]
      by blast

    from \<open>A \<subseteq> {}\<close> have "A = {}" by simp
    then show False using \<open>v \<in> A\<close> by simp
  next
    fix x
    assume "x \<in> zero_space.span {}"
    then obtain a where "zero_space.lincomb a {} = x"
      unfolding zero_space.span_def[of "{}"]
      by simp
    then show "x = \<zero>\<^bsub>V\<^esub>"
      unfolding zero_space.lincomb_def
      by simp
  next
    have "zero_space.span {} = {zero_space.lincomb a {} | a. True}"
      unfolding zero_space.span_def[of "{}"]
      by simp
    also have "\<dots> = {\<zero>\<^bsub>V\<^esub> | a. True}"
      by auto
    ultimately show "\<zero>\<^bsub>V\<^esub> \<in> zero_space.span {}"
      by auto
  qed
  thus ?thesis
    using zero_space.dim_basis
    by fastforce
qed
    
lemma (in induced_subspace) dim_zero:
  "vectorspace.dim K (VS\<lparr>carrier:={zero_vec}\<rparr>) = 0"
proof -
  interpret vec_space: vectorspace K "induced_vs.VS K n"
    by (rule local.kn.vectorspace_VS)
  have "\<zero>\<^bsub>induced_vs.VS K n\<^esub> = zero_vec"
    by simp
  thus ?thesis
    using vec_space.trivial_space_dim_zero
    by presburger
qed

end