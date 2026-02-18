theory InducedVectorspace
  imports "../Thirty_Three_Miniatures_Root" Util CarriersetMatrix
begin

locale induced_vs =
  fixes
    F and
    n :: nat
  assumes
    field_F: "field F"
begin
abbreviation E where "E \<equiv> carrier F"
abbreviation V where "V \<equiv> { v . dim_vec v = n \<and> set\<^sub>v v \<subseteq> E}"

lemma monoid_F: "monoid F" using field_F field_def domain_def cring_def comm_monoid_def by auto
lemma ring_F: "ring F" using field_F field_def domain_def cring_def by auto

definition addition :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "addition u v = vec n (\<lambda>i. (u$i) \<oplus>\<^bsub>F\<^esub> (v$i))"

definition scaling ::  "'a \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "scaling s w = vec n (\<lambda>i. s \<otimes>\<^bsub>F\<^esub> (w$i))"

definition zero_vec where "zero_vec = vec n (\<lambda>i. \<zero>\<^bsub>F\<^esub>)"
lemma zero_vec_in_v: "zero_vec \<in> V"
proof (safe)
  fix x
  assume "x \<in>$ zero_vec"
  then have "x = \<zero>\<^bsub>F\<^esub>" using vec_set_def[of zero_vec] zero_vec_def by auto
  then show "x \<in> E" using ring.ring_simprules(2)[OF ring_F] by presburger
qed (simp add: zero_vec_def)

abbreviation VS where "VS \<equiv> \<lparr> 
  carrier = V,
  mult = undefined,
  one = undefined,
  zero = zero_vec,
  add = addition,
  module.smult = scaling
\<rparr>"

lemma scaling_closed:
  assumes
    "\<alpha> \<in> E"
    "v \<in> V"
  shows
    "scaling \<alpha> v \<in> V"
proof -
  let ?scaled = "(scaling \<alpha> v)"

  have "field F" using induced_vs_def induced_vs_axioms by metis
  then have "domain F" using field_def by blast
  then have mon_F: "monoid F" using domain_def[of F] cring_def comm_monoid_def by metis
  have word_chars_in_A: "\<forall>i \<in> {0..<n}. v$i \<in> E" using assms vec_set_def by fastforce

  have len: "dim_vec ?scaled = n" unfolding scaling_def by simp
  moreover have "\<forall> i\<in>{0..<n}. ?scaled$i = (\<alpha> \<otimes>\<^bsub>F\<^esub> (v$i))" unfolding scaling_def by simp
  then have "\<forall> i\<in>{0..<n}. ?scaled$i \<in> E"
    using word_chars_in_A monoid.m_closed[OF mon_F] assms by metis
  then have "set\<^sub>v ?scaled \<subseteq> E" using vec_set_def[of ?scaled] len by auto
  ultimately show "?scaled \<in> V" by simp
qed

lemma addition_closed:
  assumes
    "u \<in> V"
    "v \<in> V"
  shows
    "addition u v \<in> V"
proof (safe)
  have u_elem: "\<And>i . i \<in> {0..<n} \<Longrightarrow> u$i \<in> E"
    using assms vec_set_def[of u]
    by auto
  have v_elem: "\<And>i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> E"
    using assms vec_set_def[of v]
    by auto

  let ?sum = "(addition u v)"

  show dim: "dim_vec ?sum = n" using addition_def by simp

  fix x
  assume "x \<in> set\<^sub>v ?sum"
  then have "\<exists>i\<in>{0..<n}. x = ?sum$i" using dim vec_set_def[of ?sum] by auto
  then obtain i where i_props: "i \<in> {0..<n}" "x = ?sum$i" by metis
  moreover from this have "?sum$i = u$i \<oplus>\<^bsub>F\<^esub> v$i" using addition_def by simp
  then have "?sum$i \<in> E"
    using i_props assms vec_set_def u_elem v_elem ring.ring_simprules(1)[OF ring_F]
    by presburger
  ultimately show "x \<in> E" by presburger
qed


lemma v_elems[simp]: "\<And> x i . x \<in> V \<Longrightarrow> i\<in>{0..<n} \<Longrightarrow> x$i \<in> E" using vec_set_def by fastforce

lemma addition_assoc:
  assumes
    "u \<in> V"
    "v \<in> V"
    "w \<in> V"
  shows
    "addition (addition u v) w = addition u (addition v w)"
proof -

  have "addition (addition u v) w = vec n (\<lambda>i. ((u$i) \<oplus>\<^bsub>F\<^esub> (v$i)) \<oplus>\<^bsub>F\<^esub> (w$i))"
    unfolding addition_def by auto
  then have "addition (addition u v) w = vec n (\<lambda>i. (u$i) \<oplus>\<^bsub>F\<^esub> ((v$i) \<oplus>\<^bsub>F\<^esub> (w$i)))"
    using ring.ring_simprules(7)[OF ring_F] v_elems assms by auto
  then show ?thesis unfolding addition_def by auto
qed

lemma addition_comm:
  assumes
    "u \<in> V"
    "v \<in> V"
  shows
    "addition u v = addition v u"
  unfolding addition_def using v_elems assms ring.ring_simprules(10)[OF ring_F] by auto

lemma factor_sum_distr:
  assumes
    "\<alpha> \<in> E"
    "\<beta> \<in> E"
    "v \<in> V"
  shows
    "scaling (\<alpha> \<oplus>\<^bsub>F\<^esub> \<beta>) v = addition (scaling \<alpha> v) (scaling \<beta> v)"
proof -
  have "\<And>i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> E"
    using assms vec_set_def by fastforce
  moreover have "scaling (\<alpha> \<oplus>\<^bsub>F\<^esub> \<beta>) v = vec n (\<lambda>i. if i \<in> {0..<n} then (\<alpha> \<oplus>\<^bsub>F\<^esub> \<beta>) \<otimes>\<^bsub>F\<^esub> (v$i) else undefined)"
    unfolding scaling_def assms by auto
  ultimately have "scaling (\<alpha> \<oplus>\<^bsub>F\<^esub> \<beta>) v = vec n (\<lambda>i. if i\<in>{0..<n} then (\<alpha> \<otimes>\<^bsub>F\<^esub> (v$i)) \<oplus>\<^bsub>F\<^esub> (\<beta> \<otimes>\<^bsub>F\<^esub> (v$i)) else undefined)"
    using ring_F ring_def[of F] ring_axioms_def[of F] assms by auto
  then show ?thesis
    using assms scaling_def addition_def by auto
qed


definition induced_inv where "induced_inv v = vec n (\<lambda>i. \<ominus>\<^bsub>F\<^esub> (v$i))"

lemma addition_inv_closed:
  assumes
    "v \<in> V"
  shows
    "induced_inv v \<in> V"
proof (safe)
  show dim: "dim_vec (induced_inv v) = n" using induced_inv_def by simp

  fix x
  assume "x \<in> set\<^sub>v (induced_inv v)"
  then have "\<exists>i. i \<in> {0..<n} \<and> (induced_inv v)$i = x" using dim vec_set_def
    by (metis imageE lessThan_atLeast0)
  then obtain i where i_range: "i \<in> {0..<n}" and "(induced_inv v)$i = x" by metis
  then have "x = \<ominus>\<^bsub>F\<^esub> (v$i)" unfolding induced_inv_def by simp
  moreover have "v$i \<in> E" using vec_set_def assms i_range by simp
  moreover have "group (add_monoid F)"
    using ring_F
    unfolding ring_def abelian_group_def abelian_group_axioms_def comm_group_def
    by satx
  ultimately show "x \<in> E"
    unfolding a_inv_def
    using group.inv_closed
    by fastforce
qed

lemma addition_inv_eq:
  assumes
    "v \<in> V"
  shows
    "addition v (induced_inv v) = zero_vec"
proof -
  have inv_ex: "\<And> \<alpha>. \<alpha>\<in>E \<Longrightarrow> inv\<^bsub>add_monoid F\<^esub> \<alpha> \<in> E"
    using abelian_group.a_inv_closed[OF ring.is_abelian_group[OF ring_F]] a_inv_def by metis

  let ?u = "induced_inv v"

  have dim: "dim_vec ?u = n" unfolding induced_inv_def by simp
  moreover have "\<forall>i\<in>{0..<n}. (v$i) \<in> E" using assms v_elems by auto
  then have "\<forall>i\<in>{0..<n}. inv\<^bsub>add_monoid F\<^esub> (v$i) \<in> E" using inv_ex by auto
  then have "set\<^sub>v ?u \<subseteq> E"
    using vec_set_def[of ?u] dim induced_inv_def
    unfolding a_inv_def
    by auto
  ultimately have elem: "?u \<in> V" by simp
  moreover have "addition v ?u = vec n (\<lambda>i. (v$i) \<oplus>\<^bsub>F\<^esub> (m_inv (add_monoid F) (v$i)))"
    unfolding a_inv_def addition_def induced_inv_def by auto
  then have "addition v ?u = vec n (\<lambda>i. (v$i) \<ominus>\<^bsub>F\<^esub> (v$i))"
    using a_inv_def[of F] a_minus_def[of F] by presburger
  then have "addition v ?u = vec n (\<lambda>i. \<zero>\<^bsub>F\<^esub>)"
    using ring.r_right_minus_eq[OF ring_F] v_elems assms by auto
  then show "addition v ?u = zero_vec" unfolding zero_vec_def .
qed

lemma addition_inv_ex:
  assumes
    "v \<in> V"
  shows
    "\<exists> u \<in> V . addition u v = zero_vec"
proof -

  let ?u = "induced_inv v"

  have "addition v ?u = zero_vec" using addition_inv_eq using assms by blast
  then have "addition ?u v = zero_vec" 
    using addition_comm[OF assms] addition_inv_closed[OF assms]
    by algebra
  then show ?thesis
    using addition_inv_closed[OF assms]
    by auto
qed

lemma vector_sum_distr:
  assumes
    "\<alpha> \<in> E"
    "u \<in> V"
    "v \<in> V"
  shows
    "scaling \<alpha> (addition u v) = addition (scaling \<alpha> u) (scaling \<alpha> v)"
proof -
  have u_elem: "\<And>i . i \<in> {0..<n} \<Longrightarrow> u$i \<in> E"
    using assms vec_set_def[of u]
    by auto
  have v_elem: "\<And>i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> E"
    using assms vec_set_def[of v]
    by auto

  have "scaling \<alpha> (addition u v) = vec n (\<lambda>i. if i \<in> {0..<n} then \<alpha> \<otimes>\<^bsub>F\<^esub> ((addition u v)$i) else undefined)"
    unfolding scaling_def by auto
  then have "scaling \<alpha> (addition u v) = vec n (\<lambda>i. if i \<in> {0..<n} then \<alpha> \<otimes>\<^bsub>F\<^esub> ((u$i) \<oplus>\<^bsub>F\<^esub> (v$i)) else undefined)"
    using addition_def by auto
  then have "scaling \<alpha> (addition u v) = vec n (\<lambda>i. if i\<in>{0..<n} then (\<alpha> \<otimes>\<^bsub>F\<^esub> (u$i)) \<oplus>\<^bsub>F\<^esub> (\<alpha> \<otimes>\<^bsub>F\<^esub> (v$i)) else undefined)"
    using ring_F ring_def[of F] ring_axioms_def[of F] assms u_elem v_elem
    by auto
  then show ?thesis
    unfolding scaling_def addition_def by auto
qed

lemma mult_scale_assoc:
  assumes
    "\<alpha> \<in> E"
    "\<beta> \<in> E"
    "v \<in> V"
  shows "scaling (\<alpha> \<otimes>\<^bsub>F\<^esub> \<beta>) v = scaling \<alpha> (scaling \<beta> v)"
proof -
  have "\<And>i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> E"
    using assms vec_set_def[of v]
    by auto
  moreover have "scaling (\<alpha> \<otimes>\<^bsub>F\<^esub> \<beta>) v = vec n (\<lambda>i. if i \<in> {0..<n} then (\<alpha> \<otimes>\<^bsub>F\<^esub> \<beta>) \<otimes>\<^bsub>F\<^esub> (v$i) else undefined)"
    unfolding scaling_def by auto
  ultimately have "scaling (\<alpha> \<otimes>\<^bsub>F\<^esub> \<beta>) v = vec n (\<lambda>i. if i \<in> {0..<n} then \<alpha> \<otimes>\<^bsub>F\<^esub> (\<beta> \<otimes>\<^bsub>F\<^esub> (v$i)) else undefined)"
    using monoid_F assms monoid.m_assoc[of F] by auto
  then have "scaling (\<alpha> \<otimes>\<^bsub>F\<^esub> \<beta>) v = vec n (\<lambda>i. if i \<in> {0..<n} then \<alpha> \<otimes>\<^bsub>F\<^esub> ((scaling \<beta> v)$i) else undefined)"
    using scaling_def by auto
  then show ?thesis
    using scaling_def by auto
qed

lemma scale_1_id:
  assumes
    "v \<in> V"
  shows
    "scaling \<one>\<^bsub>F\<^esub> v = v"
proof -
  have "\<And>i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> E"
    using assms vec_set_def by fastforce
  moreover have "scaling \<one>\<^bsub>F\<^esub> v = vec n (\<lambda>i. \<one>\<^bsub>F\<^esub> \<otimes>\<^bsub>F\<^esub> (v$i))"
    using scaling_def by simp
  ultimately have "scaling \<one>\<^bsub>F\<^esub> v = vec n (\<lambda>i. (v$i))"
    using monoid.l_one[OF monoid_F] by auto
  then show ?thesis using assms by fastforce
qed

lemma addition_0_id: assumes
  "v \<in> V"
shows
  "addition zero_vec v = v"
proof -
  have "\<And>i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> E"
    using assms v_elems by fastforce
  moreover have "addition zero_vec v = vec n (\<lambda>i. \<zero>\<^bsub>F\<^esub> \<oplus>\<^bsub>F\<^esub> (v$i))"
    unfolding zero_vec_def using addition_def by auto
  ultimately have "addition zero_vec v = vec n (\<lambda>i. (v$i))"
    using assms vec_set_def ring.ring_simprules(8)[OF ring_F] by auto
  then show ?thesis using assms by fastforce
qed

lemma abelian_group_VS: "abelian_group VS" proof
  show "\<And>x y. x \<in> carrier (add_monoid VS) \<Longrightarrow>
           y \<in> carrier (add_monoid VS) \<Longrightarrow>
           x \<otimes>\<^bsub>add_monoid VS\<^esub> y \<in> carrier (add_monoid VS)" using addition_closed by auto
next
  show "\<And>x y z.
       x \<in> carrier (add_monoid VS) \<Longrightarrow>
       y \<in> carrier (add_monoid VS) \<Longrightarrow>
       z \<in> carrier (add_monoid VS) \<Longrightarrow>
       x \<otimes>\<^bsub>add_monoid VS\<^esub> y \<otimes>\<^bsub>add_monoid VS\<^esub> z =
       x \<otimes>\<^bsub>add_monoid VS\<^esub> (y \<otimes>\<^bsub>add_monoid VS\<^esub> z)" using addition_assoc by auto
next
  show "\<one>\<^bsub>add_monoid VS\<^esub> \<in> carrier (add_monoid VS)" using zero_vec_in_v by simp
next
  show "\<And>x. x \<in> carrier (add_monoid VS) \<Longrightarrow> \<one>\<^bsub>add_monoid VS\<^esub> \<otimes>\<^bsub>add_monoid VS\<^esub> x = x"
    using addition_0_id by simp
next
  show "\<And>x. x \<in> carrier (add_monoid VS) \<Longrightarrow> x \<otimes>\<^bsub>add_monoid VS\<^esub> \<one>\<^bsub>add_monoid VS\<^esub> = x"
    using addition_0_id addition_comm
    using zero_vec_in_v by force
next
  show "carrier (add_monoid VS) \<subseteq> Units (add_monoid VS)" proof
    fix v                            
    assume "v \<in> carrier (add_monoid VS)"
    then have "v \<in> V" by simp
    moreover have "\<exists> u\<in>V  . addition u v = zero_vec \<and> addition v u = zero_vec" proof -
      from \<open>v \<in> V\<close> obtain u where "u \<in> V" "addition u v = zero_vec" using addition_inv_ex by blast
      moreover from this have "addition v u = zero_vec" using \<open>v \<in> V\<close> addition_comm by simp
      ultimately show ?thesis by auto
    qed
    ultimately show "v \<in> Units (add_monoid VS)" unfolding Units_def by simp
  qed
qed (simp add: addition_comm zero_vec_in_v)


lemma vectorspace_VS: "vectorspace F VS" proof (unfold vectorspace_def module_def module_axioms_def, simp, safe, goal_cases)
  case 1
  show "field F" using induced_vs_def[of F] induced_vs_axioms by satx
  then show "cring F" using field_def domain_def by metis
next
  case 2
  show "abelian_group VS" using abelian_group_VS .
next
  case (3 a x)
  then show ?case using scaling_closed by auto
next
  case (4 a x xa)
  then show ?case using scaling_closed by auto
next
  case (5 a b x)
  then show ?case using factor_sum_distr by simp
next
  case (6 a x y)
  then show ?case using vector_sum_distr by simp
next
  case (7 a b x)
  then show ?case using mult_scale_assoc by simp
next
  case (8 x)
  then show ?case using scale_1_id by simp
qed

lemma additive_inverse[simp]:
  assumes
    "v \<in> V"
  shows
    "\<ominus>\<^bsub>VS\<^esub> v = induced_inv v"
proof -
  let ?u = "\<ominus>\<^bsub>VS\<^esub> v"
  let ?w = "induced_inv v"

  have "group (add_monoid VS)"
    using vectorspace_VS
    unfolding vectorspace_def module_def abelian_group_def
    unfolding abelian_group_axioms_def comm_group_def
    by satx
  moreover from this have "monoid (add_monoid VS)" unfolding group_def
    by satx
  moreover have "v \<in> carrier VS" using assms by simp
  moreover from calculation have "?u \<oplus>\<^bsub>VS\<^esub> v = \<zero>\<^bsub>VS\<^esub>"
    unfolding a_inv_def
    using group.l_inv[of "add_monoid VS" v]
    by auto
  moreover have "v \<oplus>\<^bsub>VS\<^esub> ?w = \<zero>\<^bsub>VS\<^esub>" 
    using addition_inv_eq assms
    by simp
  moreover from calculation have "?u \<in> carrier VS"
    unfolding a_inv_def
    using group.inv_closed[of "add_monoid VS" v]
    by simp
  moreover have "?w \<in> carrier VS"
    using addition_inv_closed assms
    by auto
  ultimately show ?thesis using monoid.inv_unique[of "add_monoid VS" ?u v ?w] assms by auto
qed


lemma elem_neq_dif_elem_nonzero:
  assumes
    "u \<in> V"
    "v \<in> V"
    "i \<in> {0..<n}"
  shows
    "(u$i \<noteq> v$i) = (\<zero>\<^bsub>VS\<^esub>$i \<noteq> (u \<ominus>\<^bsub>VS\<^esub> v)$i)"
proof
  assume assm: "u$i \<noteq> v$i"

  show "\<zero>\<^bsub>VS\<^esub>$i \<noteq> (u \<ominus>\<^bsub>VS\<^esub> v)$i" proof (rule ccontr)
    assume "\<not> \<zero>\<^bsub>VS\<^esub> $ i \<noteq> (u \<ominus>\<^bsub>VS\<^esub> v) $ i"
    then have "\<zero>\<^bsub>F\<^esub> = (u \<ominus>\<^bsub>VS\<^esub> v) $ i"
      using zero_vec_def assms
      by simp
    also have "\<dots> = u$i \<oplus>\<^bsub>F\<^esub> (\<ominus>\<^bsub>VS\<^esub> v)$i"
      unfolding a_minus_def addition_def
      using assms
      by simp
    also have "\<dots> = u$i \<oplus>\<^bsub>F\<^esub> (\<ominus>\<^bsub>F\<^esub> (v$i))"
      using additive_inverse[OF assms(2)]
      unfolding induced_inv_def
      using assms(3)
      by fastforce
    moreover have a_group: "group (add_monoid F)"
      using ring_F
      unfolding ring_def abelian_group_def abelian_group_axioms_def
      unfolding comm_group_def
      by satx
    moreover have "u$i \<in> E" using assms vec_set_def by simp
    moreover have v_elem: "v$i \<in> E" using assms vec_set_def by simp
    moreover from calculation have "(\<ominus>\<^bsub>F\<^esub> (v$i)) \<in> E"
      using group.inv_closed
      unfolding a_inv_def
      by fastforce
    ultimately have "u$i = \<ominus>\<^bsub>F\<^esub> (\<ominus>\<^bsub>F\<^esub> (v$i))"
      using group.inv_equality[of "add_monoid F" "u$i" "\<ominus>\<^bsub>F\<^esub> (v$i)"]
      unfolding a_inv_def
      by simp
    then have "u$i = v$i"
      using group.inv_inv[OF a_group] v_elem
      unfolding a_inv_def
      by simp
    then show "False" using assm by satx
  qed
next
  assume "\<zero>\<^bsub>VS\<^esub> $ i \<noteq> (u \<ominus>\<^bsub>VS\<^esub> v) $ i"
  then have assm: "\<zero>\<^bsub>F\<^esub> \<noteq> (u \<ominus>\<^bsub>VS\<^esub> v)$i"
    unfolding zero_vec_def
    using assms
    by simp
  
  show "u$i \<noteq> v$i" proof (rule ccontr)
    assume "\<not> u $ i \<noteq> v $ i"
    then have "u$i = v$i" by satx
    moreover have "u$i \<in> E" using assms vec_set_def by simp
    moreover have "v$i \<in> E" using assms vec_set_def by simp
    moreover have a_group: "group (add_monoid F)"
      using ring_F
      unfolding ring_def abelian_group_def abelian_group_axioms_def
      unfolding comm_group_def
      by satx
    ultimately have "\<zero>\<^bsub>F\<^esub> = u$i \<ominus>\<^bsub>F\<^esub> v$i"
      unfolding a_minus_def a_inv_def
      using group.r_inv
      by fastforce
    also have "\<dots> = u$i \<oplus>\<^bsub>F\<^esub> (induced_inv v)$i"
      unfolding induced_inv_def a_minus_def
      using assms additive_inverse
      by auto
    also have "\<dots> = u$i \<oplus>\<^bsub>F\<^esub> (\<ominus>\<^bsub>VS\<^esub> v)$i"
      using additive_inverse assms
      by presburger
    also have "\<dots> = (u \<ominus>\<^bsub>VS\<^esub> v)$i"
      unfolding a_minus_def
      using addition_def assms
      by simp
    finally show "False" using assm by satx
  qed
qed


definition orthogonal where
  "orthogonal u v = (field.scalar_prod F u v = \<zero>\<^bsub>F\<^esub>)"

end

locale induced_subspace = subspace K W "induced_vs.VS K n" + induced_vs K n for K W n
begin

abbreviation "subspace_obj \<equiv> vectorspace.vs VS W"
lemma sub_vs: "vectorspace K subspace_obj"
  using subspace_axioms vectorspace.subspace_is_vs vs by blast

definition orthogonal_carrier where
  "orthogonal_carrier = {v \<in> V . (\<forall>w \<in> W. orthogonal v w)}"

lemma orthogonal_subspace: "subspace K orthogonal_carrier VS"
  sorry

end

end
