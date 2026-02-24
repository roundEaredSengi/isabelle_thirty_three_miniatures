theory MoreVectorspace
  imports InducedVectorspace

begin

section \<open>Additional Lemmas about Vector Spaces\<close>

subsection \<open>Existence of a Subspace Basis\<close>

text \<open>
  We show that a linear subspace U of a finite-dimensional vector space V is also finite-dimensional.
  For this, we prove the existence of a basis of the subspace as follows:

    1) Any subset that is linearly independent in the subspace U is also linear independent in V.
    2) There exists a maximal linearly independent subset of U whose span is contained in U.
    3) For any linearly independent subset of U that does not generate U, 
        we can find a larger linearly independent subset of U by inserting a vector.
    4) The maximal linearly independent subset from 2) must generate 3) because we could otherwise
        find a larger linearly independent subset according to 3), contradicting maximality.

  There is a basis existence theorem "finite_basis_exists" in the AFP entry VectorSpace,
  however, this is only shown for vector spaces that are already known to be finite-dimensional.
\<close>

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
    fin: "finite A" and sub: "A \<subseteq> X" and pi: "a \<in> (A\<rightarrow>carrier K)" and 
    "v \<in> A" and "a v \<noteq> \<zero>\<^bsub>K\<^esub>" and zero: "mod.lincomb a A = \<zero>\<^bsub>V\<^esub>" 
    by blast
  hence "A \<subseteq> carrier V"
    using assms submod
    unfolding LinearCombinations.submodule_def
    by auto
  have eq_map: "(\<lambda>v. a v \<odot>\<^bsub>mod.md W\<^esub> v) = (\<lambda>v. a v \<odot> v)"
    by simp
  have "sub_mod.lincomb a A = (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot>\<^bsub>mod.md W\<^esub> v)"
    unfolding sub_mod.lincomb_def
    by simp
  also from eq_map have "(\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot>\<^bsub>mod.md W\<^esub> v) = (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot> v)"
    by metis
  also have "... = (\<Oplus>v\<in>A. a v \<odot> v)"
    using fin sub pi \<open>A \<subseteq> carrier V\<close>
  proof (induction "card A" arbitrary: A)
    case 0
    hence "(\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot> v) = \<zero>\<^bsub>V\<^esub>"
      by simp 
    moreover have "(\<Oplus>v\<in>A. a v \<odot> v) = \<zero>\<^bsub>V\<^esub>"
      using 0
      by simp
    ultimately show ?case 
      by simp
  next
    case (Suc x)
    hence a_clsd: "\<forall>v \<in> A. a v \<in> carrier K"
      by auto
    hence closed_V: "\<forall>v \<in> A. a v \<odot> v \<in> carrier V"
      using mod.module_axioms \<open>A \<subseteq> carrier V\<close>
      unfolding module_def module_axioms_def
      by auto
    have "A \<subseteq> carrier (mod.md W)"
      using \<open>A \<subseteq> X\<close> \<open>X \<subseteq> W\<close>
      by simp
    hence closed_W: "\<forall>v \<in> A. a v \<odot> v \<in> carrier (mod.md W)"
      using a_clsd sub_mod.module_axioms
      unfolding module_def module_axioms_def
      by auto 
    from Suc have "card A > 0"
      by presburger
    hence "A \<noteq> {}"
      by auto
    then obtain b :: 'c where "b \<in> A"
      by auto
    hence "x = card (A - {b})"
      using Suc
      by simp
    moreover have "finite (A - {b})"
      using \<open>b \<in> A\<close> Suc
      by simp
    moreover have "A - {b} \<subseteq> X"
      using Suc
      by auto
    moreover have "a \<in> A - {b} \<rightarrow> carrier K"
      using Suc
      unfolding Pi_def
      by simp
    ultimately have IH: "(\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A-{b}. a v \<odot> v) = (\<Oplus>v\<in>A-{b}. a v \<odot> v)"
      using Suc
      by blast
    have fin_b: "finite (A - {b})"
      using Suc
      by simp
    moreover have no_elt: "b \<notin> A - {b}"
      by simp
    moreover have "(\<lambda>v. a v \<odot> v) \<in> A - {b} \<rightarrow> carrier (mod.md W)"
      using closed_W
      by simp
    moreover have "a b \<odot> b \<in> carrier (mod.md W)"
      using \<open>b \<in> A\<close> closed_W
      by metis
    moreover have eq_insert: "insert b (A - {b}) = A"
      using \<open>b \<in> A\<close>
      by auto
    ultimately have sub_mod_sum:
      "(\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot> v) = (a b \<odot> b) \<oplus>\<^bsub>mod.md W\<^esub> (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A-{b}. a v \<odot> v)"
      using \<open>b \<in> A\<close> Suc sub_mod.finsum_insert[of "A - {b}" b "\<lambda>v. a v \<odot> v"]
      by metis
    have "(\<lambda>v. a v \<odot> v) \<in> A - {b} \<rightarrow> carrier V"
      using closed_V
      by simp
    moreover have "a b \<odot> b \<in> carrier V"
      using \<open>b \<in> A\<close> closed_V
      by metis
    ultimately have mod_sum: "(\<Oplus>v\<in>A. a v \<odot> v) = (a b \<odot> b) \<oplus>\<^bsub>V\<^esub> (\<Oplus>v\<in>A-{b}. a v \<odot> v)"
      using \<open>b \<in> A\<close> Suc mod.finsum_insert[of "A - {b}" b "\<lambda>v. a v \<odot> v", OF fin_b no_elt] eq_insert
      by metis
    also have "... = (a b \<odot> b) \<oplus>\<^bsub>V\<^esub> (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A-{b}. a v \<odot> v)"
      using IH
      by metis
    also have "... = (a b \<odot> b) \<oplus>\<^bsub>mod.md W\<^esub> (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A-{b}. a v \<odot> v)"
      by simp
    also have "... = (\<Oplus>\<^bsub>mod.md W\<^esub>v\<in>A. a v \<odot> v)"
      using sub_mod_sum
      by simp
    finally show ?case by simp
  qed
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
    "P \<equiv> (\<lambda>B. finite B \<and> B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B)"
  shows "\<exists>A. finite A \<and> maximal A P"
proof -
  have "\<nexists>A v. A \<subseteq> {} \<and> v \<in> A"
    by simp
  hence "module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) {}"
    using module.lin_dep_def[of K "V\<lparr>carrier:=W\<rparr>" "{}"]
    by (metis module.submodule_is_module submod submodule.module)
  moreover have "{} \<subseteq> W"
    by blast
  moreover have "finite {}"
    by simp
  ultimately have "P {}"
    unfolding P_def
    by metis
  moreover have "\<And>A. P A \<Longrightarrow> finite A \<and> card A \<le> vectorspace.dim K V"
    using subspace_lin_indpt_card_bounded assms
    unfolding P_def
    by presburger 
  ultimately show ?thesis
    using maximal_exists[of P]
    by metis
qed

lemma (in module) span_subset:
  fixes X :: "'c set"
  assumes "X \<subseteq> carrier M"
  shows "X \<subseteq> module.span R M X"
proof (safe)
  fix x :: 'c
  assume "x \<in> X"
  let ?a = "\<lambda>y. if (x = y) then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>"
  let ?A = "{x}"
  have "lincomb ?a ?A = (?a x \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> lincomb ?a {}"
    using lincomb_insert[of "{}" ?a x] \<open>x \<in> X\<close> assms
    by auto  
  moreover have "lincomb ?a {} = \<zero>\<^bsub>M\<^esub>"
    by (rule lincomb_empty)
  moreover have "?a x \<odot>\<^bsub>M\<^esub> x = x"
    using \<open>x \<in> X\<close> assms
    by auto
  ultimately have "x = lincomb ?a ?A"
    using \<open>x \<in> X\<close> assms
    by auto
  moreover have "?a \<in> ?A \<rightarrow> carrier R"
    unfolding Pi_def
    by simp
  moreover have "finite ?A"
    by simp
  moreover have "?A \<subseteq> X"
    using \<open>x \<in> X\<close>
    by simp
  ultimately show "x \<in> span X"
    unfolding span_def
    by blast
qed

lemma (in subspace) add_lin_indpt_vec:
  fixes X :: "'c set" 
  defines 
    "P \<equiv> (\<lambda>B. finite B \<and> B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B)"
  assumes "P X" and "\<not> W \<subseteq> module.span K (V\<lparr>carrier:=W\<rparr>) X"
  shows "\<not> maximal X P"
proof -
  have mod: "Module.module K (V\<lparr>carrier := W\<rparr>)"
    by (metis submod module.submodule_is_module submodule.module)
  have "W \<subseteq> carrier V"
    using submod submodule.subset by blast

  have "\<exists>w \<in> W. w \<notin> module.span K (V\<lparr>carrier:=W\<rparr>) X"
    using assms
    by auto
  then obtain w :: 'c where "w \<in> W" and not_span: "w \<notin> module.span K (V\<lparr>carrier:=W\<rparr>) X"
    by blast
  moreover have "X \<subseteq> module.span K (V\<lparr>carrier:=W\<rparr>) X"
    using assms module.span_subset[of K "V\<lparr>carrier:=W\<rparr>" X, OF mod]
    unfolding P_def
    by blast
  ultimately have "w \<notin> X"
    by auto

  have "module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) (X \<union> {w})"
  proof (safe)
    assume ldep: "module.lin_dep K (V\<lparr>carrier := W\<rparr>) (X \<union> {w})"
    have "X \<subseteq> W"
      using assms
      by metis
    from ldep have "\<exists>A a v. 
      (finite A \<and> A \<subseteq> X \<union> {w} \<and> (a \<in> (A\<rightarrow>carrier K)) \<and> 
        (module.lincomb (V\<lparr>carrier:=W\<rparr>) a A = \<zero>\<^bsub>V\<lparr>carrier:=W\<rparr>\<^esub>) \<and> (v \<in> A) \<and> (a v \<noteq> \<zero>\<^bsub>K\<^esub>))"
      using module.lin_dep_def[of K "V\<lparr>carrier := W\<rparr>" "X \<union> {w}", OF mod]
      by satx
    then obtain A :: "'c set" and a :: "'c \<Rightarrow> 'a" and v :: 'c where
      fin: "finite A" and sub: "A \<subseteq> X \<union> {w}" and pi: "a \<in> (A\<rightarrow>carrier K)" and 
      elt: "v \<in> A" and nzero: "a v \<noteq> \<zero>\<^bsub>K\<^esub>" and
      triv: "module.lincomb (V\<lparr>carrier:=W\<rparr>) a A = \<zero>\<^bsub>V\<lparr>carrier:=W\<rparr>\<^esub>"
      by metis

    have "w \<in> A"
    proof (rule ccontr)
      assume "w \<notin> A"
      then have "A \<subseteq> X"
        using \<open>A \<subseteq> X \<union> {w}\<close>
        by auto
      then have "\<exists>A a v. 
        (finite A \<and> A \<subseteq> X \<and> (a \<in> (A\<rightarrow>carrier K)) \<and> 
        (module.lincomb (V\<lparr>carrier:=W\<rparr>) a A = \<zero>\<^bsub>V\<lparr>carrier:=W\<rparr>\<^esub>) \<and> (v \<in> A) \<and> (a v \<noteq> \<zero>\<^bsub>K\<^esub>))"
        using fin pi elt nzero triv
        by metis
      then have "module.lin_dep K (V\<lparr>carrier := W\<rparr>) X"
        using module.lin_dep_def[of K "V\<lparr>carrier := W\<rparr>" X, OF mod]
        by metis
      thus False
        using \<open>P X\<close>
        unfolding P_def
        by satx
    qed
    moreover from this have finw: "finite (A - {w})"
      using fin 
      by simp
    moreover have car_w: "A - {w} \<subseteq> carrier (V\<lparr>carrier := W\<rparr>)"
      using sub \<open>P X\<close>
      unfolding P_def
      by auto
    moreover have "a \<in> A - {w} \<union> {w} \<rightarrow> carrier K"
      using pi \<open>w \<in> A\<close>
      by auto
    moreover have "w \<notin> A - {w}"
      by simp
    moreover have "w \<in> carrier (V\<lparr>carrier := W\<rparr>)"
      using \<open>w \<in> W\<close>
      by simp   
    moreover have "A - {w} \<union> {w} = A"
      using \<open>w \<in> A\<close>
      by auto
    ultimately have 
      "module.lincomb (V\<lparr>carrier:=W\<rparr>) a A = 
        (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w})"
      using module.lincomb_insert[OF mod, of "A - {w}" a w]
      by simp
    hence "\<zero>\<^bsub>V\<lparr>carrier:=W\<rparr>\<^esub> = (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w})"
      using triv
      by metis

    hence lincomb: "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> \<zero>\<^bsub>V\<^esub> = 
      \<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> ((a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}))"
      by simp
    have "a w \<in> carrier K"
      using \<open>w \<in> W\<close> \<open>w \<in> A\<close> pi
      by auto
    hence car_elt: "a w \<odot>\<^bsub>V\<^esub> w \<in> carrier V"
      using vs \<open>w \<in> W\<close>
      unfolding Pi_def vectorspace_def Module.module_def module_axioms_def
      by (meson ring_subset_carrier submod submodule.subset)
    hence car_elt_minus: "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<in> carrier V"
      by (meson vectorspace.additive_inverse_closed vs)
    hence "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> \<zero>\<^bsub>V\<^esub> = \<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w)"  
      using Module.module_def abelian_group.show_r_zero abelian_groupE vectorspace_def vs
      by meson
    hence lincomb2: "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w)= 
      \<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> ((a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}))"
      using lincomb 
      by argo
    moreover have lincomb_carr: 
      "module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}) \<in> carrier V"
      using \<open>W \<subseteq> carrier V\<close> module.lincomb_closed[OF mod, of "A - {w}" a, OF car_w] pi
      unfolding Pi_def
      by auto
    ultimately have 
      "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> ((a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w})) =
        (\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> ((a w \<odot>\<^bsub>V\<^esub> w)) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}))"
      using vs car_elt car_elt_minus
      unfolding vectorspace_def Module.module_def abelian_monoid_def
      by (simp add: abelian_groupE(3))
    hence "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) =
      (\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> ((a w \<odot>\<^bsub>V\<^esub> w)) \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}))"
      using lincomb2
      by metis
    moreover have "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) \<oplus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) = \<zero>\<^bsub>V\<^esub>"
      using car_elt
      by (meson Module.module_def abelian_group.l_neg vectorspace_def vs)
    ultimately have "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) = \<zero>\<^bsub>V\<^esub> \<oplus>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w})"
      by simp
    hence "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) = module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w})"
      using lincomb_carr vs Module.module_def abelian_group.show_l_zero 
            abelian_groupE(2) vectorspace_def
      by metis
    moreover have minus_rewrite: "\<ominus>\<^bsub>V\<^esub> (a w \<odot>\<^bsub>V\<^esub> w) = ((\<ominus>\<^bsub>K\<^esub> a w) \<odot>\<^bsub>V\<^esub> w)"
      using \<open>a w \<in> carrier K\<close> \<open>w \<in> W\<close>
      by (metis module.smult_l_minus ring_subset_carrier submod submodule.module submodule.subset)
    ultimately have lincomb_w: "(\<ominus>\<^bsub>K\<^esub> a w) \<odot>\<^bsub>V\<^esub> w = module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A - {w})"
      by metis
  
    have "\<ominus>\<^bsub>K\<^esub> a w \<noteq> \<zero>\<^bsub>K\<^esub>"
    proof (rule ccontr)
      assume nneq_0: "\<not> \<ominus>\<^bsub>K\<^esub> a w \<noteq> \<zero>\<^bsub>K\<^esub>"
      interpret f: field K
        using vs
        by (rule VectorSpace.vectorspace.axioms(2))
      have "a v \<in> carrier K"
        using pi elt
        by auto
      hence "a v \<oplus>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> a v) = \<zero>\<^bsub>K\<^esub>"
        using group.r_inv[of "add_monoid K" "a v"]
        by algebra
      moreover have "\<ominus>\<^bsub>K\<^esub> a v \<in> carrier K"
        using \<open>a v \<in> carrier K\<close>
        by (rule f.a_inv_closed)
      ultimately have "a v = \<ominus>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> a v)"
        using cring.sum_zero_eq_neg[of K "a v" "\<ominus>\<^bsub>K\<^esub> a v"] f.field_axioms \<open>a v \<in> carrier K\<close>
        unfolding field_def domain_def
        by satx
      moreover have "\<ominus>\<^bsub>K\<^esub> \<zero>\<^bsub>K\<^esub> = \<zero>\<^bsub>K\<^esub>"
        by algebra
      ultimately have "\<ominus>\<^bsub>K\<^esub> a v \<noteq> \<zero>\<^bsub>K\<^esub>"
        using nzero
        by metis
      moreover from nneq_0 have eq_0: "\<ominus>\<^bsub>K\<^esub> a w = \<zero>\<^bsub>K\<^esub>"
        by simp
      ultimately have "w \<noteq> v" 
        by meson
      moreover have "\<forall>v \<in> carrier V. \<zero>\<^bsub>K\<^esub> \<odot>\<^bsub>V\<^esub> v = \<zero>\<^bsub>V\<^esub>"
        using vs module.smult_l_null[of K V]
        unfolding vectorspace_def module_def module_axioms_def
        by simp
      ultimately have "(\<ominus>\<^bsub>K\<^esub> a w) \<odot>\<^bsub>V\<^esub> w = \<zero>\<^bsub>V\<^esub>"
        using \<open>w \<in> W\<close> submod eq_0
        unfolding LinearCombinations.submodule_def
        by auto
      hence "module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}) = \<zero>\<^bsub>V\<^esub>"
        using lincomb_w
        by metis
      moreover have "a \<in> A-{w} \<rightarrow> carrier K"
        using pi
        unfolding Pi_def
        by simp
      moreover have "v \<in> A-{w}"
        using elt \<open>w \<noteq> v\<close>
        by simp
      moreover have "A - {w} \<subseteq> X"
        using sub
        by auto
      ultimately have "\<exists>A a v. 
        (finite A \<and> A \<subseteq> X \<and> (a \<in> (A\<rightarrow>carrier K)) \<and> 
        (module.lincomb (V\<lparr>carrier:=W\<rparr>) a A = \<zero>\<^bsub>V\<lparr>carrier:=W\<rparr>\<^esub>) \<and> (v \<in> A) \<and> (a v \<noteq> \<zero>\<^bsub>K\<^esub>))"
        using finw nzero
        by auto
      hence "module.lin_dep K (V\<lparr>carrier:=W\<rparr>) X"
        using module.lin_dep_def[OF mod]
        by metis
      thus False
        using assms
        unfolding P_def
        by satx
    qed
    moreover have "\<ominus>\<^bsub>K\<^esub> a w \<in> carrier K"
      using \<open>a w \<in> carrier K\<close>                     
      by (meson Module.module_def cring.cring_simprules(3) mod)
    ultimately have "\<ominus>\<^bsub>K\<^esub> a w \<in> Units K"
      using vs unfolding vectorspace_def field_def field_axioms_def
      by simp
    hence "\<exists>x \<in> carrier K. x \<otimes>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> a w) = \<one>\<^bsub>K\<^esub> \<and> (\<ominus>\<^bsub>K\<^esub> a w) \<otimes>\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub>"
      unfolding Units_def
      by simp
    then obtain x :: 'a where x_car: "x \<in> carrier K" and one: "x \<otimes>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> a w) = \<one>\<^bsub>K\<^esub>"
      by blast

    hence "x \<odot>\<^bsub>V\<^esub> ((\<ominus>\<^bsub>K\<^esub> a w) \<odot>\<^bsub>V\<^esub> w) = (x \<otimes>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> a w)) \<odot>\<^bsub>V\<^esub> w"
      using car_elt car_elt_minus \<open>w \<in> W\<close> \<open>\<ominus>\<^bsub>K\<^esub> a w \<in> carrier K\<close> vs submod
      by (metis module.smult_assoc1 ring_subset_carrier submodule.subset vectorspace_def)
    hence "x \<odot>\<^bsub>V\<^esub> ((\<ominus>\<^bsub>K\<^esub> a w) \<odot>\<^bsub>V\<^esub> w) = \<one>\<^bsub>K\<^esub> \<odot>\<^bsub>V\<^esub> w"
      using one
      by metis
    moreover have "\<one>\<^bsub>K\<^esub> \<odot>\<^bsub>V\<^esub> w = w"
      using \<open>w \<in> W\<close> vs submod
      by (meson module.smult_one ring_subset_carrier submodule.subset vectorspace_def)
    ultimately have lincomb_w': "w = x \<odot>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w})"
      using lincomb_w 
      by argo

    have "module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}) \<in> module.span K (V\<lparr>carrier:=W\<rparr>) (A-{w})"
      using module.finite_span[OF mod, of "A - {w}", OF finw car_w] pi
      unfolding Pi_def
      by auto
    hence 
      "x \<odot>\<^bsub>V\<^esub> module.lincomb (V\<lparr>carrier:=W\<rparr>) a (A-{w}) \<in> module.span K (V\<lparr>carrier:=W\<rparr>) (A-{w})"
      using module.span_is_submodule[of K "V\<lparr>carrier:=W\<rparr>" "A-{w}", OF mod car_w] x_car
      unfolding submodule_def module_def
      by simp
  
    hence "w \<in> module.span K (V\<lparr>carrier:=W\<rparr>) (A-{w})"
      using lincomb_w'
      by metis
    moreover have "A - {w} \<subseteq> X"
      using sub
      by auto
    ultimately have "w \<in> module.span K (V\<lparr>carrier:=W\<rparr>) X"
      using module.span_is_monotone[OF mod, of "A-{w}" X]
      by auto
    thus False
      using not_span
      by blast
  qed

  hence "P (X \<union> {w})"
    unfolding P_def
    using \<open>w \<in> W\<close> assms
    by simp
  moreover have "X \<subseteq> X \<union> {w}"
    by auto
  moreover have "X \<noteq> X \<union> {w}"
    using \<open>w \<notin> X\<close>
    by auto
  ultimately have "\<exists>B. X \<subseteq> B \<and> P B \<and> B \<noteq> X"
    by metis
  thus ?thesis
    unfolding maximal_def
    using assms
    by metis
qed
  
lemma (in subspace) subspace_has_basis:
  assumes "vectorspace.fin_dim K V"
  defines 
    "P \<equiv> (\<lambda>B. finite B \<and> B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier:=W\<rparr>) B)"
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

subsection \<open>Dimension of a Linear Subspace\<close>

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

lemma (in subspace) dim_le: 
  assumes "vectorspace.fin_dim K V"
  shows "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) \<le> vectorspace.dim K V" 
  using vectorspace.dim_li_is_basis
  sorry

lemma (in subspace) dim_eq_imp_space_eq: 
  assumes 
    "vectorspace.fin_dim K V" and 
    "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = vectorspace.dim K V"
  shows "carrier V = W"
  sorry

subsection \<open>The Trivial Subspace\<close>

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