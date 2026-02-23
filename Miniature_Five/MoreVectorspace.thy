theory MoreVectorspace
  imports InducedVectorspace

begin

lemma (in subspace) dim_le: "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) \<le> vectorspace.dim K V" 
  using vectorspace.dim_li_is_basis
  sorry

lemma (in subspace) dim_eq_imp_space_eq: 
  assumes "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = vectorspace.dim K V"
  shows "carrier V = W"
  sorry

lemma (in subspace) lin_indpt_sub_imp_lin_indpt_parent:
  fixes X :: "'c set"
  assumes "X \<subseteq> W" and "module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) X"
  shows "module.lin_indpt K V X"
proof (rule ccontr, simp)
  assume dep: "module.lin_dep K V X"
  interpret mod: Module.module K V
    using vectorspace_def vs 
    by blast
  interpret sub_mod: Module.module K "V\<lparr>carrier := W\<rparr>"
    using submod module.submodule_is_module submodule.module 
    by blast
  from dep have "mod.lin_dep X"
    by satx
  then have "\<exists>A a v. 
    (finite A \<and> A \<subseteq> X \<and> (a \<in> (A\<rightarrow>carrier K)) \<and> (mod.lincomb a A = \<zero>\<^bsub>V\<^esub>) \<and> (v\<in>A) \<and> (a v \<noteq> \<zero>\<^bsub>K\<^esub>))"
    unfolding mod.lin_dep_def
    by metis
  then obtain A :: "'c set" and a :: "'c \<Rightarrow> 'a" and v :: 'c where
    "finite A" and "A \<subseteq> X" and "a \<in> (A\<rightarrow>carrier K)" and 
    "v \<in> A" and "a v \<noteq> \<zero>\<^bsub>K\<^esub>" and zero: "mod.lincomb a A = \<zero>\<^bsub>V\<^esub>" 
    by blast
  have eq_map: "(\<lambda>v. a v \<odot>\<^bsub>mod.md W\<^esub> v) = (\<lambda>v. a v \<odot> v)"
    by simp
  have "sub_mod.lincomb a A = (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot>\<^bsub>mod.md W\<^esub> v)"
    unfolding sub_mod.lincomb_def
    by simp
  also from eq_map have "(\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot>\<^bsub>mod.md W\<^esub> v) = (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot> v)"
    by metis
  also have "... = (\<Oplus>v\<in>A. a v \<odot> v)"
    sorry
  also have "... = mod.lincomb a A"
    unfolding mod.lincomb_def
    by simp
  finally have "sub_mod.lincomb a A = mod.lincomb a A"
    by simp
  then have "sub_mod.lincomb a A = \<zero>\<^bsub>V\<lparr>carrier := W\<rparr>\<^esub>"
    using zero
    by simp
  hence "sub_mod.lin_dep X"
    unfolding sub_mod.lin_dep_def
    using \<open>finite A\<close> \<open>A \<subseteq> X\<close> \<open>a \<in> (A\<rightarrow>carrier K)\<close> \<open>v \<in> A\<close> \<open>a v \<noteq> \<zero>\<^bsub>K\<^esub>\<close>
    by metis
  thus "False"
    using assms
    by satx
qed

lemma (in subspace) subspace_lin_indpt_card_bounded:
  fixes X :: "'c set"
  assumes "X \<subseteq> W" and "vectorspace.fin_dim K V" and "module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) X"
  shows "card X \<le> vectorspace.dim K V" and "finite X"
proof -
  have lind: "module.lin_indpt K V X"
    using assms lin_indpt_sub_imp_lin_indpt_parent[of X]
    by satx
  moreover have in_carr: "X \<subseteq> carrier V"
    using assms order_trans submod submodule.subset
    by metis
  ultimately show "card X \<le> vectorspace.dim K V"
    using vectorspace.li_le_dim[of K V X] assms vs
    by blast
  show "finite X"
    using assms in_carr lind vectorspace.li_le_dim vs 
    by blast
qed

lemma (in subspace) max_lin_indpt_subset:
  assumes "vectorspace.fin_dim K V"
  defines 
    "P \<equiv> (\<lambda>B. B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B)"
  shows "\<exists>A. finite A \<and> maximal A P"
proof -
  have "\<nexists>A v. A \<subseteq> {} \<and> v \<in> A"
    by simp
  hence "module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) {}"
    using module.lin_dep_def[of K "V\<lparr>carrier:=W\<rparr>" "{}"]
    by (metis module.submodule_is_module submod submodule.module)
  moreover have "{} \<subseteq> W"
    by blast
  ultimately have "P {}"
    unfolding P_def
    by satx
  moreover have "\<And>A. P A \<Longrightarrow> finite A \<and> card A \<le> vectorspace.dim K V"
    using subspace_lin_indpt_card_bounded assms
    unfolding P_def
    by presburger 
  ultimately show ?thesis
    using maximal_exists[of P]
    by metis
qed

lemma (in subspace) add_lin_indpt_vec:
  fixes X :: "'c set" 
  defines 
    "P \<equiv> (\<lambda>B. B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B)"
  assumes "P X" and "\<not> W \<subseteq> module.span K (V\<lparr>carrier:=W\<rparr>) X"
  shows "\<not> maximal X P"
  sorry

lemma (in subspace) subspace_has_basis:
  assumes "vectorspace.fin_dim K V"
  defines 
    "P \<equiv> (\<lambda>B. B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B)"
  shows "\<exists>B. vectorspace.basis K (V\<lparr>carrier:=W\<rparr>) B"
proof -
  have "\<exists>B. finite B \<and> maximal B P"
    using max_lin_indpt_subset assms
    by metis
  then obtain B :: "'c set" where p: "maximal B P" and "finite B"
    by metis
  hence "P B" 
    unfolding maximal_def
    by satx
  hence "B \<subseteq> W"
    unfolding P_def
    by blast
  hence "module.span K (V\<lparr>carrier:=W\<rparr>) B \<subseteq> W"
    by (metis module.span_is_subset module.span_li_not_depend(1) submod submodule.module)
  moreover have "W \<subseteq> module.span K (V\<lparr>carrier:=W\<rparr>) B"
    using p add_lin_indpt_vec[of B] \<open>P B\<close> P_def 
    by fastforce
  ultimately have "module.span K (V\<lparr>carrier:=W\<rparr>) B = W"
    by blast 
  hence "module.gen_set K (V\<lparr>carrier:=W\<rparr>) B"
    by simp
  moreover have "B \<subseteq> carrier (V\<lparr>carrier:=W\<rparr>)"
    using \<open>P B\<close> P_def
    by simp
  moreover have "module.lin_indpt K (V\<lparr>carrier := W\<rparr>) B"
    using \<open>P B\<close> P_def
    by simp
  moreover have "vectorspace K (V\<lparr>carrier := W\<rparr>)"
    by (metis vs subspace_axioms vectorspace.subspace_is_vs)
  ultimately show ?thesis
    using vectorspace.basis_def[of K "V\<lparr>carrier := W\<rparr>" B]
    by metis
qed

(*
3) Lemma: Falls B ein linear unabhängiges subset von U ist und span(B) != U, 
findest du ein u in U so, dass u nicht in span(B) und daher B + {u} linear unabhängig ist
4) Lemma: Das maximale linear unabhängige subset B0 von U aus 2) muss ein generating set sein 
(also eine Basis). span(B0) subset U is klar, U subset span(B0) folgt via Widerspruch: 
Wenns kein generating set wäre könnte man wegen 3) noch mal ein größeres lin. unabh. set bauen, 
Widerspruch zu maximality
*)

lemma (in subspace) fin_sub_dim:
  assumes "vectorspace.fin_dim K V"
  shows "vectorspace.fin_dim K (V\<lparr>carrier:=W\<rparr>)"
proof -

  note module = 
    module.submodule_is_module[OF submodule.module[OF submod] 
    vectorspace.is_module[OF vs subspace_axioms]]

  have "\<exists>B. vectorspace.basis K (V\<lparr>carrier:=W\<rparr>) B" by (rule subspace_has_basis[OF assms])
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