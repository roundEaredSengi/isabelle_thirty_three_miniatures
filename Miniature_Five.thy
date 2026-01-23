theory Miniature_Five
  imports Thirty_Three_Miniatures_Root

begin

instantiation gf2 :: equal
begin

definition equal_gf2 :: "gf2 \<Rightarrow> gf2 \<Rightarrow> bool" where
  "equal_gf2 x y = (Rep_gf2 x = Rep_gf2 y)"

instance
  by standard (auto simp: equal_gf2_def Rep_gf2_inject)
end

instantiation vec :: (equal) equal
begin
definition equal_vec :: "('a::equal) vec \<Rightarrow> ('a::equal) vec \<Rightarrow> bool" where
  "equal_vec x y \<equiv> (dim_vec x = dim_vec y) \<and> (\<forall> i \<in> {0..<dim_vec x}. x$i = y$i)"

instance proof
  fix x y :: "'a::equal vec"
  show "equal_class.equal x y = (x = y)" unfolding equal_vec_def by auto
qed
end

lemma distinct_elems_card[simp]:
  assumes
    "card S > 1 \<or> \<not>finite S"
  shows
    "\<exists> a \<in> S . \<exists> b \<in> S . a \<noteq> b"
proof (cases "finite S")
  case finite: True
  show ?thesis proof -
    have card: "card S > 1" using finite assms by satx

    obtain x where "x \<in> S" using assms by fastforce

    then have "card (S - {x}) > 0" using card by auto

    then have "\<exists> b \<in> S . x \<noteq> b" proof -
      obtain y where "y \<in> (S - {x})"
        using \<open>card (S - {x}) > 0\<close> by (rule elem_exists_non_empty_set)
      then have "x \<noteq> y \<and> y \<in> S" by blast
      then show ?thesis by metis
    qed
    then show ?thesis using \<open>x \<in> S\<close> by metis
  qed
next
  case infinite: False
  then show ?thesis
    by (metis ID.set_finite finite_subset singleton_iff subsetI)
qed

lemma distinct_vec_diff_index[simp]:
  assumes
    "dim_vec x = dim_vec y"
    "x \<noteq> y"
  shows
    "\<exists>i \<in> {0..<dim_vec x} . x$i \<noteq> y$i"
  using assms by auto  

lemma lists_of_finite_set:
  fixes
    n::nat
  assumes
    "finite (S::'a set)"
  shows
    "finite { l. length l = n \<and> set l \<subseteq> S}"
proof(induction n)
  case (Suc n)
  then have "{xs::'a list. length xs = Suc n \<and> set xs \<subseteq> S} = (\<Union>x \<in> S. (#) x ` {xs. length xs = n \<and>  set xs \<subseteq> S})"
    using length_Suc_conv by (auto simp: length_Suc_conv)
  then show ?case using Suc assms by simp
qed simp

lemma map_finite:
  assumes
    "finite S"
  shows
    "finite {f x | x . x \<in> S \<and> P x}"
  using assms by simp

lemma elem_in_vec_set:
  assumes
    "i \<in> {0..<dim_vec v}"
  shows
    "v$i \<in> set\<^sub>v v"
  using assms
  by (simp add: vec_set_def)

locale code =
  fixes
    A :: "'a set" and
    n :: nat and
    C :: "'a vec set"
  assumes
    "finite A"
    "card C > 1 \<or> \<not> finite C"
    "C \<subseteq> {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
begin
definition words[simp]: "words = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
definition word[simp]: "word w = (w \<in> words)"

lemma words_subs[simp]: "C \<subseteq> words" using code_def[of A n C] code_axioms by auto

lemma cardA: "card A > 1"
proof -
  obtain u v where uv_props: "u \<in> C" "v \<in> C" "u \<noteq> v"
    using distinct_elems_card code_axioms code_def by metis

  then obtain i where i_prop: "i \<in> {0..<n}" "u$i \<noteq> v$i"
    using code_axioms code_def[of A n C] distinct_vec_diff_index by blast
  then have "u$i \<in> set\<^sub>v u" using vec_set_def words_subs uv_props by fastforce
  moreover have "v$i \<in> set\<^sub>v v" using i_prop vec_set_def words_subs uv_props by fastforce
  ultimately have "u$i \<in> A \<and> v$i \<in> A" using uv_props words_subs words by blast
  then have "{u$i, v$i} \<subseteq> A" by simp
  then have "card {u$i, v$i} \<le> card A" using code_axioms code_def[of A n C] card_mono by metis
  then show ?thesis using i_prop by simp
qed

lemma finite[simp]: "finite C"
proof -
  obtain a b where ab_props: "a \<in> A" "b \<in> A" "a \<noteq> b"
    using cardA
    by (metis One_nat_def card_le_Suc0_iff_eq code_axioms code_def linorder_not_less)

  moreover have "{ list_of_vec w | w . w \<in> C } \<subseteq> { l::'a list . length l = n \<and> set l \<subseteq> A}"
    using code_axioms code_def[of A n C] set_list_of_vec by fastforce
  moreover have "finite { l::'a list . length l = n \<and> set l \<subseteq> A}"
    using lists_of_finite_set[of A] code_axioms code_def[of A n C] by presburger
  ultimately have "finite { list_of_vec w | w . w \<in> C }" 
    using finite_subset map_finite by blast
  then have "finite { vec_of_list l | l . l \<in> { list_of_vec w | w . w \<in> C } }"
    using map_finite by simp
  moreover have "C = { vec_of_list (list_of_vec w) | w . w \<in> C}" by (simp add: vec_list)
  then have "C = { vec_of_list l | l . l \<in> { list_of_vec w | w . w \<in> C } }" by auto
  ultimately show ?thesis by argo
qed

definition hamming_distance :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> nat" where
  "hamming_distance u v = (if word u \<and> word v then card {i \<in> {0..<n} . u$i \<noteq> v$i} else  undefined)"

definition minimum_distance :: "nat" where
  "minimum_distance = Min {hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"

definition corrects_errors :: "nat \<Rightarrow> bool" where
  "corrects_errors t \<equiv> \<forall> w\<in>words. card {v\<in>C . hamming_distance w v \<le> t} \<le> 1"

lemma hamming_symm[simp]: "hamming_distance u v = hamming_distance v u"
proof (cases "word u \<and> word v")
  case True
  then have words: "word u" "word v" using words_subs by auto

  then have "hamming_distance u v = card {i \<in> {0..<n}. u $ i \<noteq> v $ i}"
    using hamming_distance_def by presburger
  also have "\<dots> = card {i \<in> {0..<n}. v $ i \<noteq> u $ i}" by metis
  also have "\<dots> = hamming_distance v u" using words hamming_distance_def by presburger
  finally show ?thesis .
next
  case False
  then show ?thesis using hamming_distance_def by presburger
qed

lemma distances_finite:
  "finite {hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
proof -
  have "finite (C \<times> C)" using finite by blast
  then show ?thesis by (rule map_finite)
qed

lemma distances_nonempty:
  "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p} \<noteq> {}"
proof -

  have dup_subset: "{(x, x) | x . x \<in> C} \<subseteq> C \<times> C" by auto
  have dup_card: "card {(x, x) | x . x \<in> C} = card C"
    by (simp add: Setcompr_eq_image card_image inj_on_convol_ident)

  have "{p \<in> C \<times> C . fst p \<noteq> snd p} = (C \<times> C) - {p \<in> C \<times> C . fst p = snd p}" using code_def by auto
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} = card ((C \<times> C) - {p \<in> C \<times> C . fst p = snd p})" by presburger
  also have "\<dots> = card ((C \<times> C) - {(x, x) | x . x \<in> C})"
    by (metis (no_types, lifting) SigmaE SigmaI split_pairs)
  also have "\<dots> = card (C \<times> C) - card C" using dup_subset dup_card finite card_Diff_subset finite_subset
    by (metis (no_types, lifting) finite_SigmaI)
  also have "\<dots> = (card C) * (card C) - card C"
    by (metis card_cartesian_product)
  also have "\<dots> = (card C - 1) * (card C)"
    by (simp add: diff_mult_distrib)
  finally have "card {p \<in> C \<times> C . fst p \<noteq> snd p} = (card C - 1) * card C" by presburger
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} > (card C - 1) * 1"
    using code_axioms code_def[of A n C] by auto
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} > 0" using code_axioms code_def by auto
  then have "{p \<in> C \<times> C . fst p \<noteq> snd p} \<noteq> {}" by fastforce

  then show ?thesis by blast
qed

lemma word_interpolation:
  assumes
    "u \<in> C" and
    "v \<in> C" and
    "m \<in> {0..hamming_distance u v}"
  shows
    "\<exists> w \<in> words . hamming_distance u w = m \<and> hamming_distance w v = hamming_distance u v - m"
proof -
  let ?d = "hamming_distance u v"
  let ?diff_idx = "{i \<in> {0..<n} . (u $ i) \<noteq> (v $ i)}"
  have diff_card: "card ?diff_idx = ?d"
    using hamming_distance_def[of u v] code_def[of A n C] code_axioms assms by auto

  moreover have "m \<le> card ?diff_idx" using assms diff_card by auto
  moreover have "finite ?diff_idx" by simp
  ultimately obtain D where Diff_prop: "D \<subseteq> ?diff_idx" "card D = m"
    using obtain_subset_with_card_n by meson

  define w where w_def: "w = vec n (\<lambda>i. if i \<in> D then v$i else u$i)"

  have u_elem_A: "\<And> i . i \<in> {0..<n} \<Longrightarrow> u$i \<in> A"
    using elem_in_vec_set code_def[of A n C] code_axioms \<open>u \<in> C\<close> by blast
  have v_elem_A: "\<And> i . i \<in> {0..<n} \<Longrightarrow> v$i \<in> A"
    using elem_in_vec_set code_def[of A n C] code_axioms \<open>v \<in> C\<close> by blast

  have "set\<^sub>v w = {w $ i | i . i \<in> {..<dim_vec w}}"
    using assms vec_set_def Setcompr_eq_image w_def by metis
  moreover have "\<forall> i \<in> {0..<n} . w$i \<in> {v$i, u$i}" using w_def by auto
  then have "\<forall> i \<in> {0..<n} . w$i \<in> A" using u_elem_A v_elem_A by auto
  then have "{w $ i | i . i \<in> {..<n}} \<subseteq> A" by fastforce
  ultimately have "set\<^sub>v w \<subseteq> A" using w_def by simp
  then have is_word: "word w" using word words w_def by auto


  have d_uw: "hamming_distance u w = m" proof -
    have "D \<subseteq> {0..<n}" using someI_ex Diff_prop some_in_eq by fast
    then have "{0..<n} = {0..<n} - D \<union> D" by auto

    then have "{i\<in>{0..<n} . u$i \<noteq> w$i} = {i\<in>({0..<n}-D) . u$i \<noteq> w$i} \<union> {i\<in>D . u$i \<noteq> w$i}"
      by blast
    also have "\<dots> = {i\<in>({0..<n}-D). u$i \<noteq> u$i} \<union> {i \<in> D . u$i \<noteq> w$i}"
      using w_def Diff_prop by auto
    also have "\<dots> = {i \<in> D . u$i \<noteq> w$i}" by blast
    also have "\<dots> = {i \<in> D . u$i \<noteq> v$i}" using w_def Diff_prop by auto
    also have "\<dots> = {i \<in> D . True}" using Diff_prop by blast
    also have "\<dots> = D" by simp
    finally have "card {i\<in>{0..<n} . u$i \<noteq> w$i} = m" using Diff_prop by simp

    moreover have "word u" using code_axioms code_def[of A n C] assms word by auto
    then have "hamming_distance u w = card {i\<in>{0..<n} . u$i \<noteq> w$i}"
      using hamming_distance_def[of u w] is_word by simp

    ultimately show ?thesis using w_def by argo
  qed
  moreover have "hamming_distance w v = ?d - m" proof -
    have "D \<subseteq> {0..<n}" using someI_ex Diff_prop some_in_eq by fast
    then have "{0..<n} = {0..<n} - D \<union> D" by auto

    then have "{i \<in> {0..<n} . w$i \<noteq> v$i} = {i \<in> ({0..<n} - D) . w$i \<noteq> v$i} \<union> {i \<in> D . w$i \<noteq> v$i}"
      by blast
    also have "\<dots> = {i\<in>({0..<n}-D). u$i \<noteq> v$i} \<union> {i \<in> D . w$i \<noteq> v$i}" using w_def Diff_prop by auto
    also have "\<dots> = {i\<in>({0..<n}-D). u$i \<noteq> v$i} \<union> {i \<in> D . v$i \<noteq> v$i}" using w_def Diff_prop by auto
    also have "\<dots> = {i\<in>({0..<n}-D). u$i \<noteq> v$i}" by blast
    also have "\<dots> =  {i \<in> {0..<n} . u$i = v$i \<and> u$i \<noteq> v$i} \<union> {i \<in> (?diff_idx - D) . u$i \<noteq> v$i}"
      using Diff_prop by blast
    also have "\<dots> = {i \<in> (?diff_idx - D) . u$i \<noteq> v$i}" by simp
    also have "\<dots> = ?diff_idx - D" by auto
    finally have "card {i \<in> {0..<n} . (w $ i) \<noteq> (v $ i)} = card (?diff_idx - D)" using Diff_prop by presburger
    moreover have "D \<subseteq> ?diff_idx" using Diff_prop by simp
    moreover have "finite D" using Diff_prop \<open>D \<subseteq> {0..<n}\<close> finite_subset by blast
    ultimately have "card {i \<in> {0..<n} . (w $ i) \<noteq> (v $ i)} = card ?diff_idx - card D"
      using card_Diff_subset by auto
    then have "card {i \<in> {0..<n} . (w $ i) \<noteq> (v $ i)} = ?d - m" using diff_card Diff_prop by auto

    moreover have "word v" using code_axioms code_def[of A n C] assms word by auto
    then have "hamming_distance w v = card {i \<in> {0..<n} . (w $ i) \<noteq> (v $ i)}"
      using hamming_distance_def[of w v] is_word by simp
    ultimately show ?thesis using w_def by argo
  qed
  ultimately have distances: "hamming_distance u w = m \<and> hamming_distance w v = ?d - m" by fast

  have "w \<in> words" using word is_word by presburger

  from this is_word distances show ?thesis by metis 
qed

lemma minimum_distance_bounds:
  assumes
    "u \<in> C" and
    "v \<in> C" and
    "u \<noteq> v"
  shows
    "hamming_distance u v \<ge> minimum_distance"
proof -
  let ?distances = "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
  have "finite (C \<times> C)" by simp
  then have "finite ?distances" using map_finite[of "C \<times> C" "\<lambda>p . hamming_distance (fst p) (snd p)"]
    by presburger
  moreover have "minimum_distance = Min ?distances" using assms minimum_distance_def by presburger
  moreover have "hamming_distance u v \<in> ?distances" using assms by auto
  ultimately show ?thesis by simp
qed

lemma codewords_words[simp]: "w \<in> C \<Longrightarrow> w \<in> words" using code_def[of A n C] code_axioms by auto

lemma hamming_triangle_ineq:
  assumes
    "word u"
    "word v"
    "word w"
  shows
    "hamming_distance u v \<le> hamming_distance u w + hamming_distance w v"
proof -
  have "{i \<in> {0..<n}. u $ i \<noteq> v $ i} = {0..<n} - {i \<in> {0..<n}. u $ i = v $ i}" by blast
  moreover have "{i \<in> {0..<n}. u$i = w$i \<and> w$i = v$i} \<subseteq> {i \<in> {0..<n}. u$i = v$i}" by auto
  then have "{i\<in>{0..<n}. u$i = w$i} \<inter> {i \<in> {0..<n}. w$i = v$i} \<subseteq> {i \<in> {0..<n}. u$i = v$i}"
    by blast
  ultimately have "{i \<in> {0..<n}. u$i \<noteq> v$i} \<subseteq> {0..<n} - ({i \<in> {0..<n}. u$i = w$i} \<inter> {i \<in> {0..<n}. w$i = v$i})"
    by blast
  then have "{i\<in>{0..<n}. u$i \<noteq> v$i} \<subseteq> ({0..<n}-{i \<in> {0..<n}. u$i = w$i}) \<union> ({0..<n}-{i \<in> {0..<n}. w$i = v$i})"
    by blast
  then have "{i\<in>{0..<n}. u$i \<noteq> v$i} \<subseteq> {i\<in>{0..<n}. u$i \<noteq> w$i} \<union> {i\<in>{0..<n}. w$i \<noteq> v$i}"
    by blast
  moreover have "finite {i\<in>{0..<n}. u$i \<noteq> v$i}" by simp
  moreover have "finite ({i\<in>{0..<n}. u$i \<noteq> w$i} \<union> {i\<in>{0..<n}. w$i \<noteq> v$i})" by simp
  ultimately have "card {i\<in>{0..<n}. u$i \<noteq> v$i} \<le> card ({i\<in>{0..<n}. u$i \<noteq> w$i} \<union> {i\<in>{0..<n}. w$i \<noteq> v$i})"
    using card_mono by meson
  then have "card {i\<in>{0..<n}. u$i \<noteq> v$i} \<le> card {i\<in>{0..<n}. u$i \<noteq> w$i} + card {i\<in>{0..<n}. w$i \<noteq> v$i}"
    using card_Un_le le_trans by blast
  then show ?thesis
    using assms hamming_distance_def by presburger
qed

theorem min_distance_ecc:
  fixes
    t :: nat
  shows "corrects_errors t = (minimum_distance \<ge> 2 * t + 1)"
proof
  show "corrects_errors t \<Longrightarrow> (minimum_distance \<ge> 2 * t + 1)" proof (rule ccontr)

    let ?distances = "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"

    assume ecc: "corrects_errors t"
    assume "\<not> (minimum_distance \<ge> 2 * t + 1)"
    then have "minimum_distance < 2 * t + 1" by linarith
    then have dist: "Min ?distances < 2 * t + 1" using minimum_distance_def code_axioms code_def by algebra

    have "finite ?distances" using distances_finite by simp
    moreover have "?distances \<noteq> {}" using distances_nonempty by simp
    ultimately have "Min ?distances \<in> ?distances" using linorder_class.Min_in[OF \<open>finite ?distances\<close> \<open>?distances \<noteq> {}\<close>] by argo

    then have "\<exists> p \<in> {p \<in> C \<times> C . fst p \<noteq> snd p}. hamming_distance (fst p) (snd p) = Min ?distances" by fastforce
    then have "\<exists> p \<in> (C \<times> C) . fst p \<noteq> snd p \<and> hamming_distance (fst p) (snd p) = Min ?distances" by blast
    then have "\<exists> u \<in> C . \<exists> v \<in> C . u \<noteq> v \<and> hamming_distance u v = Min ?distances" by simp
    then obtain u v where "u\<in>C" "v\<in>C" "u\<noteq>v" "hamming_distance u v = Min ?distances" by blast 

    then have "hamming_distance u v < 2 * t + 1" using dist by metis
    then have uv_bound: "hamming_distance u v \<le> 2 * t" using dist by fastforce

    then obtain w where w_bounds:
      "word w"
      "hamming_distance u w = hamming_distance u v div 2"
      "hamming_distance w v = hamming_distance u v - (hamming_distance u v div 2)" 
      using word_interpolation[OF \<open>u\<in>C\<close> \<open>v\<in>C\<close>, of "hamming_distance u v div 2"] by auto

    then have "hamming_distance u w \<le> t" using uv_bound by linarith
    moreover from w_bounds have "hamming_distance w v \<le> t" using uv_bound by linarith

    ultimately have "{u, v} \<subseteq> {x\<in>C . hamming_distance w x \<le> t}"
      using \<open>u \<in> C\<close> \<open>v \<in> C\<close> by auto
    moreover have "finite {x\<in>C . hamming_distance w x \<le> t}" by auto
    ultimately have "card {u, v} \<le> card {x \<in> C. hamming_distance w x \<le> t}" using card_mono by blast
    then have "1 < card {x \<in> C. hamming_distance w x \<le> t}" using \<open>u \<noteq> v\<close> by auto

    moreover have "\<forall>u\<in>words. card {v \<in> C. hamming_distance u v \<le> t} \<le> 1"
      using ecc corrects_errors_def[of t] by algebra

    moreover have "w \<in> words" using \<open>word w\<close> by simp

    ultimately show "False" by fastforce
  qed
next 
  assume distance_min: "minimum_distance \<ge> 2*t + 1"
  moreover have "\<forall> w\<in>words. card {v\<in>C . hamming_distance w v \<le> t} \<le> 1" proof (rule ccontr)
    assume "\<not> (\<forall>w\<in>words. card {v \<in> C. hamming_distance w v \<le> t} \<le> 1)"
    then have "\<exists> w \<in> words . card {v\<in>C . hamming_distance w v \<le> t} > 1" by auto
    then obtain w where "word w" "card {v\<in>C . hamming_distance w v \<le> t} > 1"
      using word by blast
    then obtain u v where uv_props:
      "u \<in> C"
      "v \<in> C"
      "hamming_distance w u \<le> t"
      "hamming_distance w v \<le> t"
      "u \<noteq> v"
      using distinct_elems_card
      by blast
    moreover have "hamming_distance u w \<le> t" 
      using uv_props hamming_symm[of w u] by presburger
    moreover have "word u" using uv_props word codewords_words by presburger
    moreover have "word v" using uv_props word codewords_words by presburger
    ultimately have "hamming_distance u v \<le> t + t"
      using hamming_triangle_ineq[of u v w] \<open>word w\<close> by linarith
    then have "minimum_distance \<le> 2*t" using minimum_distance_bounds uv_props by fastforce
    then show "False" using distance_min by linarith
  qed
  moreover have "corrects_errors t = (\<forall> u\<in>words. card {v\<in>C . hamming_distance u v \<le> t} \<le> 1)" 
    using corrects_errors_def[of t] by presburger
  ultimately show "corrects_errors t" by satx
qed
end

locale elementwise_field_vs = 
  fixes
    F and
    n :: nat
  assumes
    "field F"
begin
abbreviation E where "E \<equiv> carrier F"
abbreviation V where "V \<equiv> { v . dim_vec v = n \<and> set\<^sub>v v \<subseteq> E}"

lemma field_F: "field F" using elementwise_field_vs_axioms elementwise_field_vs_def by auto
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

definition VS: "VS = \<lparr> 
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

  have "field F" using elementwise_field_vs_def elementwise_field_vs_axioms by metis
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

lemma addition_inv:
  assumes
    "v \<in> V"
  shows
    "\<exists> u \<in> V . addition u v = zero_vec"
proof -
  have inv_ex: "\<And> \<alpha>. \<alpha>\<in>E \<Longrightarrow> inv\<^bsub>add_monoid F\<^esub> \<alpha> \<in> E"
    using abelian_group.a_inv_closed[OF ring.is_abelian_group[OF ring_F]] a_inv_def by metis

  define u where "u = vec n (\<lambda>i. inv\<^bsub>add_monoid F\<^esub> (v$i))"

  have dim: "dim_vec u = n" unfolding u_def by simp
  moreover have "\<forall>i\<in>{0..<n}. (v$i) \<in> E" using assms v_elems by auto
  then have "\<forall>i\<in>{0..<n}. inv\<^bsub>add_monoid F\<^esub> (v$i) \<in> E" using inv_ex by auto
  then have "set\<^sub>v u \<subseteq> E" using vec_set_def[of u] dim u_def by auto
  ultimately have elem: "u \<in> V" by simp
  moreover have "addition v u = vec n (\<lambda>i. (v$i) \<oplus>\<^bsub>F\<^esub> (m_inv (add_monoid F) (v$i)))"
    unfolding addition_def u_def by auto
  then have "addition v u = vec n (\<lambda>i. (v$i) \<ominus>\<^bsub>F\<^esub> (v$i))"
    using a_inv_def[of F] a_minus_def[of F] by presburger
  then have "addition v u = vec n (\<lambda>i. \<zero>\<^bsub>F\<^esub>)"
    using ring.r_right_minus_eq[OF ring_F] v_elems assms by auto
  then have "addition v u = zero_vec" unfolding zero_vec_def .
  then have "addition u v = zero_vec" using assms addition_comm elem by algebra
  ultimately show ?thesis by blast
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
           x \<otimes>\<^bsub>add_monoid VS\<^esub> y \<in> carrier (add_monoid VS)" unfolding VS using addition_closed by auto
next
  show "\<And>x y z.
       x \<in> carrier (add_monoid VS) \<Longrightarrow>
       y \<in> carrier (add_monoid VS) \<Longrightarrow>
       z \<in> carrier (add_monoid VS) \<Longrightarrow>
       x \<otimes>\<^bsub>add_monoid VS\<^esub> y \<otimes>\<^bsub>add_monoid VS\<^esub> z =
       x \<otimes>\<^bsub>add_monoid VS\<^esub> (y \<otimes>\<^bsub>add_monoid VS\<^esub> z)" unfolding VS using addition_assoc by auto
next
  show "\<one>\<^bsub>add_monoid VS\<^esub> \<in> carrier (add_monoid VS)" unfolding VS using zero_vec_in_v by simp
next
  show "\<And>x. x \<in> carrier (add_monoid VS) \<Longrightarrow> \<one>\<^bsub>add_monoid VS\<^esub> \<otimes>\<^bsub>add_monoid VS\<^esub> x = x"
    unfolding VS using addition_0_id by simp
next
  show "\<And>x. x \<in> carrier (add_monoid VS) \<Longrightarrow> x \<otimes>\<^bsub>add_monoid VS\<^esub> \<one>\<^bsub>add_monoid VS\<^esub> = x"
    unfolding VS using addition_0_id addition_comm
    using zero_vec_in_v by force
next
  show "\<And>x y. x \<in> carrier (add_monoid VS) \<Longrightarrow>
           y \<in> carrier (add_monoid VS) \<Longrightarrow>
           x \<otimes>\<^bsub>add_monoid VS\<^esub> y = y \<otimes>\<^bsub>add_monoid VS\<^esub> x"
    unfolding VS using addition_comm by simp
next
  show "carrier (add_monoid VS) \<subseteq> Units (add_monoid VS)" proof
    fix v                            
    assume "v \<in> carrier (add_monoid VS)"
    then have "v \<in> V" unfolding VS by simp
    moreover have "\<exists> u\<in>V  . addition u v = zero_vec \<and> addition v u = zero_vec" proof -
      from \<open>v \<in> V\<close> obtain u where "u \<in> V" "addition u v = zero_vec" using addition_inv by blast
      moreover from this have "addition v u = zero_vec" using \<open>v \<in> V\<close> addition_comm by simp
      ultimately show ?thesis by auto
    qed
    ultimately show "v \<in> Units (add_monoid VS)" unfolding VS Units_def by simp
  qed
qed
    

lemma vectorspace_VS: "vectorspace F VS" proof (unfold vectorspace_def module_def module_axioms_def, simp, safe)
  show "field F" using elementwise_field_vs_def[of F] elementwise_field_vs_axioms by satx
  then show "cring F" using field_def domain_def by metis
next
  show "abelian_group VS" using abelian_group_VS .
next
  fix a x
  assume "a \<in> carrier F" "x \<in> carrier VS"
  then show "a \<odot>\<^bsub>VS\<^esub> x \<in> carrier VS" unfolding VS using scaling_closed by auto
next
  fix a b x
  assume "a \<in> carrier F" "b \<in> carrier F" "x \<in> carrier VS"
  moreover from this have "x \<in> V" unfolding VS by simp
  ultimately show "(a \<oplus>\<^bsub>F\<^esub> b) \<odot>\<^bsub>VS\<^esub> x = a \<odot>\<^bsub>VS\<^esub> x \<oplus>\<^bsub>VS\<^esub> b \<odot>\<^bsub>VS\<^esub> x"
    unfolding VS using factor_sum_distr[OF \<open>a \<in> E\<close> \<open>b \<in> E\<close> \<open>x \<in> V\<close>] by simp
next
  fix a x y
  assume assms: "a \<in> E" "x \<in> carrier VS" "y \<in> carrier VS"
  moreover from this have "x \<in> V" unfolding VS by simp
  moreover from assms have "y \<in> V" unfolding VS by simp
  ultimately show "a \<odot>\<^bsub>VS\<^esub> (x \<oplus>\<^bsub>VS\<^esub> y) = a \<odot>\<^bsub>VS\<^esub> x \<oplus>\<^bsub>VS\<^esub> a \<odot>\<^bsub>VS\<^esub> y"
    unfolding VS using vector_sum_distr[OF \<open>a \<in> E\<close> \<open>x \<in> V\<close> \<open>y \<in> V\<close>] by simp
next
  fix a b x
  assume assms: "a \<in> E" "b \<in> E" "x \<in> carrier VS"
  then show "a \<otimes>\<^bsub>F\<^esub> b \<odot>\<^bsub>VS\<^esub> x = a \<odot>\<^bsub>VS\<^esub> (b \<odot>\<^bsub>VS\<^esub> x)"
    unfolding VS using mult_scale_assoc by simp  
next
  fix x
  assume in_carrier: "x \<in> carrier VS"
  then have "x \<in> V" unfolding VS by simp
  then show "\<one>\<^bsub>F\<^esub> \<odot>\<^bsub>VS\<^esub> x = x" unfolding VS using scale_1_id by simp
qed

end

locale linear_code = code +
  fixes
    "F"
    "V"
  assumes
    "field F"
    "carrier F = A"
    "vectorspace F V"
    "carrier V = C"
begin

definition word_addition :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "word_addition u v = vec n (\<lambda>i. (add F) (u$i) (v$i))"

definition word_scaling :: "'a \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "word_scaling s w = vec n (\<lambda>i. (mult F) s (w$i))"

lemma elem_vs: "elementwise_field_vs F"
  using
    linear_code_axioms 
    linear_code_def[of A n C F V]
    linear_code_axioms_def[of A C F V]
    elementwise_field_vs_def by blast

definition W: "W = elementwise_field_vs.VS F n"
lemma "vectorspace F W" using elementwise_field_vs.vectorspace_VS elem_vs W by metis

end

end