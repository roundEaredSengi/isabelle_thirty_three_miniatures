theory LinearCode
  imports "../Thirty_Three_Miniatures_Root" "Code" "InducedVectorspace"
begin

locale linear_code = code +
  fixes
    "F"
    "V"
  assumes
    field_F: "field F" and
    F_carrier: "carrier F = A" and
    C_axioms: "\<And> u v. u \<in> C \<Longrightarrow> v \<in> C \<Longrightarrow> induced_vs.addition F n u v \<in> C"
    "\<And> a v. a \<in> A \<Longrightarrow> v \<in> C \<Longrightarrow> induced_vs.scaling F n a v \<in> C"
    "induced_vs.zero_vec F n \<in> C"
begin

lemma elem_vs: "induced_vs F"
  using
    linear_code_axioms
    linear_code_def[of A n C F]
    linear_code_axioms_def[of A n C F]
    induced_vs_def by blast

definition W: "W = induced_vs.VS F n"
lemma w_vs: "vectorspace F W" using induced_vs.vectorspace_VS elem_vs W by metis

lemma code_subspace: "subspace F C W" unfolding subspace_def using
    w_vs
    induced_vs.vectorspace_VS[OF elem_vs, of n]
    vectorspace_def[of F W]
    words_subs words
    F_carrier
    C_axioms
    elem_vs
  unfolding submodule_def W induced_vs.VS[OF elem_vs]
  by auto

abbreviation "CS" where "CS \<equiv> vectorspace.vs W C"

lemma add_codeword_group: "group (add_monoid CS)"
  using module.submodule_is_module[of F W C] w_vs code_subspace vectorspace_def[of F W]
  using module_def[of F CS] abelian_group_def[of CS] abelian_group_axioms_def[of CS]
  using comm_group_def[of "add_monoid CS"]
  using subspace.submod by blast


lemma abelian_monoid_code: "abelian_monoid CS" 
  using module.submodule_is_module[of F W C] w_vs code_subspace vectorspace_def[of F W]
  using module_def[of F CS] abelian_group_def[of CS]
  using subspace.submod by blast

lemma all_invertible_CS:
  assumes
    "v \<in> C"
  shows
    "v \<in> Units (add_monoid CS)"
  using assms add_codeword_group
    group_def[of "add_monoid CS"] group_axioms_def[of "add_monoid CS"] by fastforce

lemma all_invertible_W:
  assumes
    "v \<in> words"
  shows
    "v \<in> Units (add_monoid W)"
proof -
  have "group (add_monoid W)"
    using w_vs
    using vectorspace_def
    using module_def abelian_group_def abelian_group_axioms_def
    using comm_group_def[of "add_monoid W"]
    by blast
  moreover have "carrier W = words"
    unfolding W induced_vs.VS[OF elem_vs, of n]
    using F_carrier words
    by simp
  ultimately show ?thesis
    using assms
      group_def[of "add_monoid W"] group_axioms_def[of "add_monoid W"] by auto
qed

lemma inv_closed:
  assumes
    "v \<in> C"
  shows
    "\<ominus>\<^bsub>CS\<^esub> v \<in> C"
proof -

  have "v \<in> Units (add_monoid CS)"
    using assms add_codeword_group
      group_def[of "add_monoid CS"] group_axioms_def[of "add_monoid CS"] by fastforce
  then show ?thesis unfolding a_inv_def
    using monoid.Units_inv_closed[of "add_monoid CS" v]
    using group_def[of "add_monoid CS"] add_codeword_group by simp
qed

lemma subtraction_closed:
  assumes
    "u \<in> C"
    "v \<in> C"
  shows
    "u \<ominus>\<^bsub>CS\<^esub> v \<in> C"
  unfolding a_minus_def
  using assms inv_closed[OF assms(2)] abelian_monoid.a_closed[OF abelian_monoid_code]
  by simp 

lemma hamming_distance_subtract:
  assumes
    "u \<in> words"
    "v \<in> words"
  shows
    "hamming_distance u v = hamming_distance \<zero>\<^bsub>W\<^esub> (u \<ominus>\<^bsub>W\<^esub> v)"
proof -
  have per_elem_equiv: "\<And>i. i \<in> {0..<n} \<Longrightarrow> (u$i \<noteq> v$i) = (\<zero>\<^bsub>W\<^esub>$i \<noteq> (u \<ominus>\<^bsub>W\<^esub> v)$i)" sorry

  have sub_word: "word (u \<ominus>\<^bsub>W\<^esub> v)" using subtraction_closed words_subs sorry

  have "\<zero>\<^bsub>W\<^esub> \<in> carrier W" sorry
  have zero_word: "word \<zero>\<^bsub>W\<^esub>" sorry

  have "hamming_distance u v = card {i \<in> {0..<n}. u$i \<noteq> v$i}"
    using assms word hamming_distance_def by presburger
  also have "\<dots> =  card {i \<in> {0..<n}. \<zero>\<^bsub>W\<^esub>$i \<noteq> (u \<ominus>\<^bsub>W\<^esub> v)$i}"
    using per_elem_equiv by meson
  also have "\<dots> = hamming_distance \<zero>\<^bsub>W\<^esub> (u \<ominus>\<^bsub>W\<^esub> v)" using zero_word sub_word hamming_distance_def by presburger
  finally show ?thesis .
qed

lemma "minimum_distance = Min { hamming_distance \<zero>\<^bsub>W\<^esub> w | w . w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}"
proof -
  let ?hammings = "{hamming_distance (fst p) (snd p) |p. p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
  have "?hammings = { hamming_distance \<zero>\<^bsub>W\<^esub> w | w . w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}" proof
    show "{hamming_distance (fst p) (snd p) |p. p \<in> C \<times> C \<and> fst p \<noteq> snd p}
    \<subseteq> {hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}" proof
      fix x
      assume "x \<in> {hamming_distance (fst p) (snd p) |p.
              p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
      then obtain p where p_props: "p \<in> C \<times> C" "fst p \<noteq> snd p" "hamming_distance (fst p) (snd p) = x"
        by blast

      let ?u = "(fst p)"
      let ?v = "(snd p)"

      have "?u \<in> C" using p_props by force
      then have "?u \<in> words" using words_subs by force
      from \<open>?u \<in> C\<close> have "?u \<in> carrier (add_monoid CS)" by simp
      have "?v \<in> C" using p_props by force
      then have "?v \<in> words" using words_subs by force
      from \<open>?v \<in> C\<close> have "?v \<in> carrier (add_monoid CS)" by simp

      have carr: "carrier (add_monoid CS) = C" by simp
      from add_codeword_group have "monoid (add_monoid CS)" using group_def[of "add_monoid CS"] by fast

      have zero_equiv: "\<zero>\<^bsub>CS\<^esub> = \<zero>\<^bsub>W\<^esub>" unfolding W induced_vs.VS[OF elem_vs, of n] by simp
      have add_equiv: "add CS = add W" unfolding W by simp
      have scale_equiv: "module.smult CS = module.smult W" unfolding W by simp
      have "\<And>u. u \<in> C \<Longrightarrow> \<ominus>\<^bsub>CS\<^esub> u = \<ominus>\<^bsub>W\<^esub> u" proof -
        fix u
        assume "u \<in> C"

        have u_elems: "\<And>i. i \<in> {0..<n} \<Longrightarrow> u$i \<in> carrier F"
          using \<open>u \<in> C\<close> words_subs words vec_set_def F_carrier by force

        thm ring.ring_simprules

        have "ring F" using field_F field_def domain_def cring_def by metis
        then have "monoid F" using ring_def by metis

        define v where v_def: "v = vec n (\<lambda>i. \<ominus>\<^bsub>F\<^esub> u$i)"
        then have "v = vec n (\<lambda>i. \<ominus>\<^bsub>F\<^esub> (\<one>\<^bsub>F\<^esub> \<otimes>\<^bsub>F\<^esub> (u$i)))"
          using monoid.l_one[OF \<open>monoid F\<close>] u_elems by auto
        then have "v = vec n (\<lambda>i. (\<ominus>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub>) \<otimes>\<^bsub>F\<^esub> (u$i))"
          using ring.l_minus[OF \<open>ring F\<close> monoid.one_closed[OF \<open>monoid F\<close>]] u_elems
          by auto
        then have "v = (\<ominus>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub>) \<odot>\<^bsub>W\<^esub> (vec n (\<lambda>i. u$i))"
          unfolding W induced_vs.VS[OF elem_vs, of n]
          using induced_vs.scaling_def[OF elem_vs, of n]
          by auto
        moreover have "dim_vec u = n" using \<open>u \<in> C\<close> words words_subs by blast
        ultimately have "v = (\<ominus>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub>) \<odot>\<^bsub>W\<^esub> u" using dim_vec eq_vecI index_vec
          by metis
        moreover have "(\<ominus>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub>) \<in> carrier F"
          using monoid.Units_closed[OF \<open>monoid F\<close>] ring.Units_minus_one_closed[OF \<open>ring F\<close>]
          by presburger
        ultimately have "v \<in> C" using C_axioms(2)[OF _ \<open>u \<in> C\<close>] F_carrier
          unfolding W induced_vs.VS[OF elem_vs, of n]
          by simp

        have "ring F" using field_F field_def domain_def cring_def by metis

        have "u \<oplus>\<^bsub>CS\<^esub> v = vec n (\<lambda>i. u$i \<oplus>\<^bsub>F\<^esub> v$i)"
          unfolding W induced_vs.VS[OF elem_vs, of n]
          using induced_vs.addition_def[OF elem_vs] by simp
        also have "\<dots> = vec n (\<lambda>i. u$i \<oplus>\<^bsub>F\<^esub> (\<ominus>\<^bsub>F\<^esub> u$i))" using v_def by auto
        also have "\<dots> = vec n (\<lambda>i. \<zero>\<^bsub>F\<^esub>)"
          using ring.ring_simprules(16)[OF \<open>ring F\<close>] u_elems by auto
        also have "\<dots> = \<zero>\<^bsub>CS\<^esub>"
          unfolding W induced_vs.VS[OF elem_vs, of n]
          using induced_vs.zero_vec_def[OF elem_vs]
          by simp
        finally have cs_sum: "u \<oplus>\<^bsub>CS\<^esub> v = \<zero>\<^bsub>CS\<^esub>" .
        then have w_sum: "u \<oplus>\<^bsub>W\<^esub> v = \<zero>\<^bsub>W\<^esub>" using zero_equiv add_equiv by argo

        have "v = \<ominus>\<^bsub>CS\<^esub> u" proof -
          have "u \<in> Units (add_monoid CS)"
            using all_invertible_CS[OF \<open>u \<in> C\<close>] .
          moreover define w where w_inv: "w = \<ominus>\<^bsub>CS\<^esub> u"
          then have "w \<oplus>\<^bsub>CS\<^esub> u = \<zero>\<^bsub>CS\<^esub>"
            using monoid.Units_l_inv[OF \<open>monoid (add_monoid CS)\<close> \<open>u \<in> Units (add_monoid CS)\<close>]
            unfolding a_inv_def m_inv_def
            by auto
          moreover from \<open>w = \<ominus>\<^bsub>CS\<^esub> u\<close> have "w \<in> C"
            using monoid.Units_inv_closed[OF \<open>monoid (add_monoid CS)\<close> \<open>u \<in> Units (add_monoid CS)\<close>] a_inv_def[of CS]
            by simp
          ultimately have "v = w"
            using monoid.inv_unique[OF \<open>monoid (add_monoid CS)\<close>, of w u v] cs_sum
            using \<open>u \<in> C\<close> \<open>v \<in> C\<close> by auto
          then show ?thesis using w_inv by presburger
        qed
        moreover have "v = \<ominus>\<^bsub>W\<^esub> u" proof -
          from \<open>u \<in> C\<close> have "u \<in> words" using words_subs by blast
          from \<open>v \<in> C\<close> have "v \<in> words" using words_subs by blast

          have "carrier W = words"
            unfolding W induced_vs.VS[OF elem_vs, of n]
            using words F_carrier
            by simp

          have "monoid (add_monoid W)"
            using w_vs
            using vectorspace_def
            using module_def abelian_group_def abelian_group_axioms_def
            using comm_group_def[of "add_monoid W"] group_def
            by blast

          have "u \<in> Units (add_monoid W)"
            using all_invertible_W[OF \<open>u \<in> words\<close>] .
          moreover define w where w_inv: "w = \<ominus>\<^bsub>W\<^esub> u"
          then have "w \<oplus>\<^bsub>W\<^esub> u = \<zero>\<^bsub>W\<^esub>"
            using monoid.Units_l_inv[OF \<open>monoid (add_monoid W)\<close> \<open>u \<in> Units (add_monoid W)\<close>]
            unfolding a_inv_def m_inv_def
            by auto
          moreover from \<open>w = \<ominus>\<^bsub>W\<^esub> u\<close> have "w \<in> words"
            using monoid.Units_inv_closed[OF \<open>monoid (add_monoid W)\<close> \<open>u \<in> Units (add_monoid W)\<close>]
            using a_inv_def[of W] \<open>carrier W = words\<close>
            by auto
          ultimately have "v = w"
            using monoid.inv_unique[OF \<open>monoid (add_monoid W)\<close>, of w u v] cs_sum
            using \<open>u \<in> words\<close> \<open>v \<in> words\<close> \<open>carrier W = words\<close> by auto
          then show ?thesis using w_inv by presburger
        qed
        ultimately show "\<ominus>\<^bsub>CS\<^esub> u = \<ominus>\<^bsub>W\<^esub> u" by presburger
      qed
      then have minus_equiv: "\<And>u v. u \<in> C \<Longrightarrow> v \<in> C \<Longrightarrow> u \<ominus>\<^bsub>CS\<^esub> v = u \<ominus>\<^bsub>W\<^esub> v"
        unfolding a_minus_def using \<open>add CS = add W\<close> by presburger

      have "?u \<ominus>\<^bsub>CS\<^esub> ?v \<in> C" using subtraction_closed[OF \<open>?u \<in> C\<close> \<open>?v \<in> C\<close>] .
      moreover have "(?u \<ominus>\<^bsub>CS\<^esub> ?v) \<noteq> \<zero>\<^bsub>CS\<^esub>" proof (rule ccontr)
        assume "\<not> ?u \<ominus>\<^bsub>CS\<^esub> ?v \<noteq> \<zero>\<^bsub>CS\<^esub>"
        then have eq_z: "?u \<oplus>\<^bsub>CS\<^esub> (\<ominus>\<^bsub>CS\<^esub> ?v) = \<zero>\<^bsub>CS\<^esub>" unfolding a_minus_def by simp
        then have "inv\<^bsub>add_monoid CS\<^esub> (\<ominus>\<^bsub>CS\<^esub> ?v) = ?u"
          using group.inv_equality[OF
              \<open>group (add_monoid CS)\<close>
              _
              _
              \<open>?u \<in> carrier (add_monoid CS)\<close>
              ]
          using inv_closed[OF \<open>?v \<in> C\<close>]
          unfolding induced_vs.VS[OF elem_vs, of n] W
          by auto
        then have "inv\<^bsub>add_monoid CS\<^esub> (inv\<^bsub>add_monoid CS\<^esub> ?v) = ?u" using a_inv_def by metis
        moreover have "?v \<in> Units (add_monoid CS)" using all_invertible_CS[OF \<open>?v \<in> C\<close>] .
        ultimately have "?v = ?u"
          using monoid.Units_inv_inv[OF \<open>monoid (add_monoid CS)\<close>]
          by algebra
        then show "False" using p_props by presburger
      qed

      moreover from p_props have "x = hamming_distance \<zero>\<^bsub>CS\<^esub> (?u \<ominus>\<^bsub>CS\<^esub> ?v)"
        using words_subs hamming_distance_subtract[OF \<open>?u \<in> words\<close> \<open>?v \<in> words\<close>]
        using \<open>\<zero>\<^bsub>CS\<^esub> = \<zero>\<^bsub>W\<^esub>\<close> minus_equiv by auto
      ultimately have "x \<in> {hamming_distance \<zero>\<^bsub>CS\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>CS\<^esub>}" by blast
      then show "x \<in> {hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}" using \<open>\<zero>\<^bsub>CS\<^esub> = \<zero>\<^bsub>W\<^esub>\<close> by auto
    qed
  next
    show "{hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}
    \<subseteq> {hamming_distance (fst p) (snd p) |p. p \<in> C \<times> C \<and> fst p \<noteq> snd p}" proof
      fix x
      assume "x \<in> {hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}"
      then obtain w where w_props: "w \<in> C" "w \<noteq> \<zero>\<^bsub>W\<^esub>" "hamming_distance w \<zero>\<^bsub>W\<^esub> = x" by auto
      then have "(\<zero>\<^bsub>W\<^esub>, w) \<in> C \<times> C"
        unfolding W induced_vs.VS
        using elem_vs C_axioms induced_vs.VS
        by (simp add: induced_vs.VS)
      then show "x \<in> {hamming_distance (fst p) (snd p) |p. p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
        using w_props
        by auto
    qed
  qed

  then show ?thesis using minimum_distance_def by presburger
qed

end

end