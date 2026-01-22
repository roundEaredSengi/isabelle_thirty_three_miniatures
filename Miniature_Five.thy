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

definition W: "W = \<lparr> 
  carrier = words,
  mult = undefined,
  one = undefined,
  zero = vec n (\<lambda>i. zero F),
  add = word_addition,
  module.smult = word_scaling
\<rparr>"

lemma F_field: "field F" using linear_code_def linear_code_axioms_def linear_code_axioms by blast
lemma F_ring: "ring F" using field.is_ring[OF F_field] .
lemma F_monoid: "Group.monoid F" using F_ring ring_def by blast

lemma F_carrier_A[simp]: "carrier F = A" using linear_code_def linear_code_axioms_def linear_code_axioms by metis

lemma word_abelian_group: "abelian_group W" sorry

lemma words_module: "module F W" proof (unfold module_def module_axioms_def, safe)
  show "cring F" using F_field field_def domain_def by metis
next
  show "abelian_group W" using word_abelian_group .
next
  fix a
  assume "a \<in> carrier F"
  then have "a \<in> A" by simp

  fix x
  assume "x \<in> carrier W"
  then have "x \<in> words" unfolding W by simp

  let ?scaled = "((module.smult W) a x)"

  have mon_F: "monoid F" using F_field field_def domain_def cring_def comm_monoid_def by metis
  have word_chars_in_A: "\<forall>i \<in> {0..<n}. x$i \<in> A" using \<open>x \<in> words\<close> words vec_set_def by fastforce

  have len: "dim_vec ?scaled = n" unfolding W word_scaling_def by simp
  moreover have "\<forall> i\<in>{0..<n}. ?scaled$i = ((mult F) a (x$i))" unfolding W word_scaling_def by simp
  then have "\<forall> i\<in>{0..<n}. ?scaled$i \<in> A"
    using F_carrier_A word_chars_in_A monoid.m_closed[OF mon_F  \<open>a \<in> carrier F\<close>] by metis
  then have "set\<^sub>v ?scaled \<subseteq> A" using vec_set_def[of ?scaled] len by auto
  ultimately show "?scaled \<in> carrier W" unfolding W words by simp
next
  fix a b x
  assume in_carriers: "a \<in> carrier F" "b \<in> carrier F" "x \<in> carrier W"

  have "x \<in> words" using in_carriers unfolding W by simp
  from this in_carriers have x_elem_carrier: "\<And>i . i \<in> {0..<n} \<Longrightarrow> x$i \<in> carrier F"
    using F_carrier_A words elem_in_vec_set
    by fast


  from in_carriers have "(a \<oplus>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. if i \<in> {0..<n} then (a \<oplus>\<^bsub>F\<^esub> b) \<otimes>\<^bsub>F\<^esub> (x$i) else undefined)"
    unfolding W word_scaling_def by auto
  then have "(a \<oplus>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. if i\<in>{0..<n} then (a \<otimes>\<^bsub>F\<^esub> (x$i)) \<oplus>\<^bsub>F\<^esub> (b \<otimes>\<^bsub>F\<^esub> (x$i)) else undefined)"
    using F_ring ring_def[of F] ring_axioms_def[of F] in_carriers x_elem_carrier
    by auto
  then show "(a \<oplus>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = a \<odot>\<^bsub>W\<^esub> x \<oplus>\<^bsub>W\<^esub> b \<odot>\<^bsub>W\<^esub> x"
    unfolding W word_scaling_def word_addition_def by auto
next
  fix a x y
  assume in_carriers: "a \<in> carrier F" "x \<in> carrier W" "y \<in> carrier W"

  have "x \<in> words" using in_carriers unfolding W by simp
  from this in_carriers have x_elem_carrier: "\<And>i . i \<in> {0..<n} \<Longrightarrow> x$i \<in> carrier F"
    using F_carrier_A words elem_in_vec_set
    by fast

  have "y \<in> words" using in_carriers unfolding W by simp
  from this in_carriers have y_elem_carrier: "\<And>i . i \<in> {0..<n} \<Longrightarrow> y$i \<in> carrier F"
    using F_carrier_A words elem_in_vec_set
    by fast

  from in_carriers have "a \<odot>\<^bsub>W\<^esub> (x \<oplus>\<^bsub>W\<^esub> y) = vec n (\<lambda>i. if i \<in> {0..<n} then a \<otimes>\<^bsub>F\<^esub> ((x \<oplus>\<^bsub>W\<^esub> y)$i) else undefined)"
    unfolding W word_scaling_def by auto
  then have "a \<odot>\<^bsub>W\<^esub> (x \<oplus>\<^bsub>W\<^esub> y) = vec n (\<lambda>i. if i \<in> {0..<n} then a \<otimes>\<^bsub>F\<^esub> ((x$i) \<oplus>\<^bsub>F\<^esub> (y$i)) else undefined)"
    unfolding W using word_addition_def by auto
  then have "a \<odot>\<^bsub>W\<^esub> (x \<oplus>\<^bsub>W\<^esub> y) = vec n (\<lambda>i. if i\<in>{0..<n} then (a \<otimes>\<^bsub>F\<^esub> (x$i)) \<oplus>\<^bsub>F\<^esub> (a \<otimes>\<^bsub>F\<^esub> (y$i)) else undefined)"
    using F_ring ring_def[of F] ring_axioms_def[of F] in_carriers x_elem_carrier y_elem_carrier
    by auto
  then show "a \<odot>\<^bsub>W\<^esub> (x \<oplus>\<^bsub>W\<^esub> y) = a \<odot>\<^bsub>W\<^esub> x \<oplus>\<^bsub>W\<^esub> a \<odot>\<^bsub>W\<^esub> y"
    unfolding W word_scaling_def word_addition_def by auto
next
  fix a b x
  assume in_carriers: "a \<in> carrier F" "b \<in> carrier F" "x \<in> carrier W"

  have "x \<in> words" using in_carriers unfolding W by simp
  from this in_carriers have x_elem_carrier: "\<And>i . i \<in> {0..<n} \<Longrightarrow> x$i \<in> carrier F"
    using F_carrier_A words elem_in_vec_set
    by fast

  from in_carriers have "(a \<otimes>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. if i \<in> {0..<n} then (a \<otimes>\<^bsub>F\<^esub> b) \<otimes>\<^bsub>F\<^esub> (x$i) else undefined)"
    unfolding W word_scaling_def by auto
  then have "(a \<otimes>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. if i \<in> {0..<n} then a \<otimes>\<^bsub>F\<^esub> (b \<otimes>\<^bsub>F\<^esub> (x$i)) else undefined)"
    using F_monoid x_elem_carrier in_carriers monoid.m_assoc[of F] by auto
  then have "(a \<otimes>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. if i \<in> {0..<n} then a \<otimes>\<^bsub>F\<^esub> ((b \<odot>\<^bsub>W\<^esub> x)$i) else undefined)"
    unfolding W using word_scaling_def by auto
  then show "(a \<otimes>\<^bsub>F\<^esub> b) \<odot>\<^bsub>W\<^esub> x = a \<odot>\<^bsub>W\<^esub> (b \<odot>\<^bsub>W\<^esub> x)"
    unfolding W using word_scaling_def by auto
next
  fix x
  assume in_carrier: "x \<in> carrier W"
  then have "x \<in> words" unfolding W by simp
  then have x_elem_carrier: "\<And>i . i \<in> {0..<n} \<Longrightarrow> x$i \<in> carrier F"
    using F_carrier_A words elem_in_vec_set
    by fast
  moreover have "\<one>\<^bsub>F\<^esub> \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. \<one>\<^bsub>F\<^esub> \<otimes>\<^bsub>F\<^esub> (x$i))"
    unfolding W using word_scaling_def by simp
  ultimately have "\<one>\<^bsub>F\<^esub> \<odot>\<^bsub>W\<^esub> x = vec n (\<lambda>i. (x$i))"
    using monoid.l_one[OF F_monoid] by auto
  then show "\<one>\<^bsub>F\<^esub> \<odot>\<^bsub>W\<^esub> x = x" using \<open>x \<in> words\<close> by fastforce
qed
    


lemma words_vs: "vectorspace F W" using words_module vectorspace_def F_field by blast

end

end