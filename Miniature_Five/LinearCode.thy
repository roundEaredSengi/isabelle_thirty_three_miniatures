theory LinearCode
  imports "../Thirty_Three_Miniatures_Root" "Code" "InducedVectorspace"
begin

locale linear_code = induced_subspace F C n + code "carrier F" n C for F C n
begin


abbreviation "W \<equiv> VS"

abbreviation "CS \<equiv> subspace_obj"
corollary code_space: "vectorspace F CS"
  using sub_vs .

lemma add_codeword_group: "group (add_monoid CS)"
  using module.submodule_is_module[of F W C] vectorspace_def[of F W]
  using module_def[of F CS] abelian_group_def[of CS] abelian_group_axioms_def[of CS]
  using comm_group_def[of "add_monoid CS"]
  using submod vs by blast

lemma abelian_monoid_code: "abelian_monoid CS" 
  using module.submodule_is_module[of F W C] vectorspace_def[of F W]
  using module_def[of F CS] abelian_group_def[of CS]
  using submod vs by blast

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
    using vs
    using vectorspace_def
    using module_def abelian_group_def abelian_group_axioms_def
    using comm_group_def[of "add_monoid W"]
    by blast
  moreover have "carrier W = words"
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

lemma hamming_distance_subtract:
  assumes
    "u \<in> words"
    "v \<in> words"
  shows
    "hamming_distance u v = hamming_distance \<zero>\<^bsub>W\<^esub> (u \<ominus>\<^bsub>W\<^esub> v)"
proof -
  have per_elem_equiv: "\<And>i. i \<in> {0..<n} \<Longrightarrow> (u$i \<noteq> v$i) = (\<zero>\<^bsub>W\<^esub>$i \<noteq> (u \<ominus>\<^bsub>W\<^esub> v)$i)"
    using assms
    using elem_neq_dif_elem_nonzero
    by presburger

  have sub_word: "word (u \<ominus>\<^bsub>W\<^esub> v)"
    using vectorspace.subtraction_closed[OF vs]
    using assms
    by simp

  have "\<zero>\<^bsub>W\<^esub> \<in> C"
    using submod submodule.zero_closed by blast
  then have zero_word: "word \<zero>\<^bsub>W\<^esub>"
    using words_subs
    by blast

  have "hamming_distance u v = card {i \<in> {0..<n}. u$i \<noteq> v$i}"
    using assms hamming_distance_def by presburger
  also have "\<dots> =  card {i \<in> {0..<n}. \<zero>\<^bsub>W\<^esub>$i \<noteq> (u \<ominus>\<^bsub>W\<^esub> v)$i}"
    using per_elem_equiv by meson
  also have "\<dots> = hamming_distance \<zero>\<^bsub>W\<^esub> (u \<ominus>\<^bsub>W\<^esub> v)" using zero_word sub_word hamming_distance_def by presburger
  finally show ?thesis .
qed

lemma linear_min_distance: "minimum_distance = Min { hamming_distance \<zero>\<^bsub>W\<^esub> w | w . w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}"
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
      have "?v \<in> C" using p_props by force
      then have "?v \<in> words" using words_subs by force

      have carr: "carrier (add_monoid CS) = C" by simp
      from add_codeword_group have "monoid (add_monoid CS)" using group_def[of "add_monoid CS"] by fast

      have zero_equiv: "\<zero>\<^bsub>CS\<^esub> = \<zero>\<^bsub>W\<^esub>" by simp
      have add_equiv: "add CS = add W" by simp
      have scale_equiv: "module.smult CS = module.smult W" by simp
      have "\<And>u. u \<in> C \<Longrightarrow> \<ominus>\<^bsub>CS\<^esub> u = \<ominus>\<^bsub>W\<^esub> u"
        using vectorspace.subspace_inverse_equal[OF vs]
        using subspace_axioms by presburger
      then have minus_equiv: "\<And>u v. u \<in> C \<Longrightarrow> v \<in> C \<Longrightarrow> u \<ominus>\<^bsub>CS\<^esub> v = u \<ominus>\<^bsub>W\<^esub> v"
        unfolding a_minus_def using \<open>add CS = add W\<close> by presburger

      have "?u \<ominus>\<^bsub>CS\<^esub> ?v \<in> C"
        using vectorspace.subtraction_closed[OF code_space]
        using \<open>?u \<in> C\<close> \<open>?v \<in> C\<close>
        by simp
      moreover have "(?u \<ominus>\<^bsub>CS\<^esub> ?v) \<noteq> \<zero>\<^bsub>CS\<^esub>" using vectorspace.eq_equiv_diff_zero[OF code_space, of ?u ?v]
        using code_space \<open>?u \<in> C\<close> \<open>?v \<in> C\<close> p_props
        by auto

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
        using vs submod submodule.zero_closed
        by blast
      then show "x \<in> {hamming_distance (fst p) (snd p) |p. p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
        using w_props
        by auto
    qed
  qed

  then show ?thesis using minimum_distance_def by presburger
qed

end

end