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
  assumes "vectorspace.fin_dim F V"
  shows "vectorspace.fin_dim F (V\<lparr>carrier:=W\<rparr>)"
  sorry

lemma (in vectorspace) trivial_space:
  "subspace K {\<zero>\<^bsub>V\<^esub>} V"
proof (unfold subspace_def, safe)
  show "vectorspace K V"
    by (rule local.vectorspace_axioms)
next
  show "LinearCombinations.submodule K {\<zero>\<^bsub>V\<^esub>} V"
    sorry
qed

lemma (in vectorspace) trivial_space_dim_zero:
  "vectorspace.dim K (V\<lparr>carrier:={\<zero>\<^bsub>V\<^esub>}\<rparr>) = 0"
proof -
  interpret zero_space: vectorspace K "V\<lparr>carrier:={\<zero>\<^bsub>V\<^esub>}\<rparr>"
    using trivial_space
    by (rule subspace_is_vs)
  have "zero_space.basis {}"
    sorry
  thus ?thesis
    sorry
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