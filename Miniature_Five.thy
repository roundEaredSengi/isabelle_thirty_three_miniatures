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

definition is_code :: "'a vec set \<Rightarrow> bool" where
  "is_code C \<equiv> \<exists> A::'a set . finite A \<and> card A > 1 \<and> (\<exists>! n . n > 0 \<and> C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A})"

lemma code_finite[simp]:
  fixes
    C :: "'a vec set"
  assumes
    "is_code C"
  shows
    "finite C"
proof -
  obtain A where A_prop:
    "finite A"
    "card A > 1"
    "\<exists>! n . n > 0 \<and> C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
    using is_code_def assms by meson
  then obtain a b where ab_props: "a \<in> A" "b \<in> A" "a \<noteq> b"
    by (metis One_nat_def card_le_Suc0_iff_eq less_Suc_eq_le not_less_eq)

  then obtain n where n_prop: "n > 0" "C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
    using A_prop by auto
  then have C_def: "C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
    using is_code_def assms by force

  moreover have "{ list_of_vec w | w . w \<in> C } \<subseteq> { l::'a list . length l = n \<and> set l \<subseteq> A}" using C_def set_list_of_vec by force
  moreover have "finite { l::'a list . length l = n \<and> set l \<subseteq> A}" using lists_of_finite_set A_prop by presburger
  ultimately have "finite { list_of_vec w | w . w \<in> C }" 
    using finite_subset map_finite by fast
  then have "finite { vec_of_list l | l . l \<in> { list_of_vec w | w . w \<in> C } }"
    using map_finite by simp
  moreover have "C = { vec_of_list (list_of_vec w) | w . w \<in> C}" by (simp add: vec_list)
  then have "C = { vec_of_list l | l . l \<in> { list_of_vec w | w . w \<in> C } }" by auto
  ultimately show ?thesis by argo
qed

lemma code_card_min[simp]:
  assumes
    "is_code C"
  shows
    "card C > 1"
proof -
  obtain A where A_prop:
    "finite A"
    "card A > 1"
    "\<exists>! n . n > 0 \<and> C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
    using is_code_def assms by meson
  then obtain a b where ab_props: "a \<in> A" "b \<in> A" "a \<noteq> b"
    by (metis One_nat_def card_le_Suc0_iff_eq less_Suc_eq_le not_less_eq)

  then obtain n where n_prop: "n > 0" "C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
    using A_prop by auto
  then have C_def: "C = {w::'a vec . dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}"
    using is_code_def assms by force

  define x where x_def: "x = vec n (\<lambda>i. a)"
  then have x_len: "dim_vec x = n" by simp
  moreover from x_def have "\<forall> i \<in> {0..<n} . x$i = a" by auto
  then have "\<forall> i \<in> {0..<n} . x$i \<in> A" using ab_props by metis
  then have "set\<^sub>v x \<subseteq> A" using vec_set_def[of x] x_len by auto
  ultimately have "x \<in> C" using is_code_def assms C_def ab_props by blast

  define y where y_def: "y = vec n (\<lambda>i. b)"
  then have y_len: "dim_vec y = n" by simp
  moreover from y_def have "\<forall> i \<in> {0..<n} . y$i = b" by auto
  then have "\<forall> i \<in> {0..<n} . y$i \<in> A" using ab_props by metis
  then have "set\<^sub>v y \<subseteq> A" using vec_set_def[of y] y_len by auto
  ultimately have "y \<in> C" using is_code_def assms C_def ab_props by blast

  have "dim_vec x \<ge> 1" using x_def n_prop by simp
  have "dim_vec y \<ge> 1" using y_def n_prop by simp

  have "a \<noteq> b" using ab_props by simp
  then have "x$0 \<noteq> b" using x_def \<open>dim_vec x \<ge> 1\<close> by simp
  then have "x$0 \<noteq> y$0" using y_def \<open>dim_vec y \<ge> 1\<close> by simp
  then have "x \<noteq> y" by auto

  show ?thesis using \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x \<noteq> y\<close>
    by (metis Miniature_Five.code_finite One_nat_def assms card_le_Suc0_iff_eq less_or_eq_imp_le
        linorder_less_linear)
qed

definition hamming_distance :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> nat" where
  "hamming_distance a b = (if dim_vec a = dim_vec b then card {i \<in> {0..<dim_vec a} . (a $ i) \<noteq> (b $ i)} else  undefined)"

(*value "hamming_distance (vec_of_list [1::gf2,1,1]) (vec_of_list [1::gf2,0,1])" (*Breaks with (equal) vec :: equal instance*)*)

definition minimum_distance :: "'a vec set \<Rightarrow> nat" where
  "minimum_distance C = (if is_code C then Min {hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}  else undefined)"

definition corrects_errors :: "nat \<Rightarrow> 'a vec set \<Rightarrow> bool" where
  "corrects_errors t C \<equiv> if is_code C then \<forall> u\<in>C. card {v\<in>C . hamming_distance u v \<le> t} \<le> 1 else undefined"
  

lemma minimum_distance_bounds:
  fixes
    C :: "('a vec set)" and
    u :: "'a vec" and
    v :: "'a vec"
  assumes
    "is_code C" and
    "u \<in> C" and
    "v \<in> C" and
    "u \<noteq> v"
  shows
    "hamming_distance u v \<ge> minimum_distance C"
proof -
  let ?distances = "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
  have "finite (C \<times> C)" using assms is_code_def by simp
  then have "finite ?distances" using map_finite[of _ "\<lambda>p . hamming_distance (fst p) (snd p)"]
    by presburger
  moreover have "minimum_distance C = Min ?distances" using assms minimum_distance_def by presburger
  moreover have "hamming_distance u v \<in> ?distances" using assms by auto
  ultimately show ?thesis by simp
qed

lemma distances_nonempty:
  assumes
    "is_code C"
  shows
    "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p} \<noteq> {}"
proof -

  have dup_subset: "{(x, x) | x . x \<in> C} \<subseteq> C \<times> C" by auto
  have dup_card: "card {(x, x) | x . x \<in> C} = card C"
    by (simp add: Setcompr_eq_image card_image inj_on_convol_ident)

  have "{p \<in> C \<times> C . fst p \<noteq> snd p} = (C \<times> C) - {p \<in> C \<times> C . fst p = snd p}" using assms is_code_def by auto
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} = card ((C \<times> C) - {p \<in> C \<times> C . fst p = snd p})" by presburger
  also have "\<dots> = card ((C \<times> C) - {(x, x) | x . x \<in> C})"
    by (metis (no_types, lifting) SigmaE SigmaI split_pairs)
  also have "\<dots> = card (C \<times> C) - card C" using dup_subset dup_card assms code_finite card_Diff_subset finite_subset
    by (metis (no_types, lifting) finite_SigmaI)
  also have "\<dots> = (card C) * (card C) - card C"
    by (metis card_cartesian_product)
  also have "\<dots> = (card C - 1) * (card C)"
    by (simp add: diff_mult_distrib)
  finally have "card {p \<in> C \<times> C . fst p \<noteq> snd p} = (card C - 1) * card C" by presburger
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} > (card C - 1) * 1" using assms code_card_min by auto
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} > 0" using assms is_code_def by auto
  then have "{p \<in> C \<times> C . fst p \<noteq> snd p} \<noteq> {}" by fastforce
  
  then show ?thesis by blast
qed

lemma distances_finite:
  assumes
    "is_code C"
  shows
    "finite {hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"
proof -
  let ?distances = "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"

  have "finite (C \<times> C)" using assms code_finite by blast
  then show ?thesis by (rule map_finite)
qed

lemma hamming_symm[simp]:
  assumes
    "is_code C"
    "u \<in> C"
    "v \<in> C"
  shows
    "hamming_distance u v = hamming_distance v u"
proof -
  have "(if True then card {n \<in> {0..<dim_vec u}. v $ n \<noteq> u $ n} else undefined) = (if True then card {n \<in> {0..<dim_vec u}. u $ n \<noteq> v $ n} else undefined)"
    by metis
  then show ?thesis
    by (simp add: hamming_distance_def)
qed

lemma elem_in_vec_set:
  assumes
    "i \<in> {0..<dim_vec v}"
  shows
    "v$i \<in> set\<^sub>v v"
  using assms
  by (simp add: vec_set_def)

lemma hamming_interpol:
  assumes
    "is_code C" and
    "u \<in> C" and
    "v \<in> C" and
    "n \<in> {0..hamming_distance u v}"
  shows
    "\<exists> w \<in> C . hamming_distance u w = n \<and> hamming_distance w v = hamming_distance u v - n"
proof
  obtain A where A_prop: 
    "finite A"
    "card A > 1"
    "(\<exists>!n. n > 0 \<and> C = {w. dim_vec w = n \<and> set\<^sub>v w \<subseteq> A})"
    using assms is_code_def by meson

  define ms where ms_def: "ms = {n. n > 0 \<and> C = {w. dim_vec w = n \<and> set\<^sub>v w \<subseteq> A}}"
  then have ms_nonempty: "ms \<noteq> {}" using A_prop by blast
  define m' where "m' = (SOME m . m \<in> ms)"
  then have "m' \<in> ms" using ms_nonempty assms some_in_eq by metis
  then have m'_prop: "\<forall> x \<in> C . dim_vec x = m'" "m' > 0" using assms is_code_def ms_def by auto

  define m where m_def: "m = dim_vec u"
  then have "m = m'" using m'_prop assms by metis
  then have m_prop: "\<forall> x \<in> C . dim_vec x = m" "m > 0" using m'_prop by auto

  from \<open>m = m'\<close> \<open>m' \<in> ms\<close> have C_def: "C = {w. dim_vec w = m \<and> set\<^sub>v w \<subseteq> A}" using ms_def by simp

  let ?d = "hamming_distance u v"
  let ?diff_idx = "{i \<in> {0..<m} . (u $ i) \<noteq> (v $ i)}"
  have diff_card: "card ?diff_idx = ?d" using hamming_distance_def assms m_prop by auto

  moreover have "n \<le> card ?diff_idx" using assms diff_card by auto
  moreover have "finite ?diff_idx" by simp
  ultimately obtain D where Diff_prop: "D \<subseteq> ?diff_idx" "card D = n" using obtain_subset_with_card_n by meson
  let ?Ds = "{D . D \<subseteq> ?diff_idx \<and> card D = n}"

  have Ds_nonempty: "?Ds \<noteq> {}" using Diff_prop by blast


  define w where w_def: "w = (let D = (SOME D' . D' \<in> ?Ds) in vec m (\<lambda>i. if i \<in> D then v$i else u$i))"

  have u_elem_A: "\<And> i . i \<in> {0..<m} \<Longrightarrow> u$i \<in> A" using m_prop elem_in_vec_set C_def \<open>u \<in> C\<close> by blast
  have v_elem_A: "\<And> i . i \<in> {0..<m} \<Longrightarrow> v$i \<in> A" using m_prop elem_in_vec_set C_def \<open>v \<in> C\<close> by blast

  have "set\<^sub>v w = {w $ i | i . i \<in> {..<dim_vec w}}"
    using assms vec_set_def Setcompr_eq_image w_def by metis
  moreover have "\<forall> i \<in> {0..<m} . w$i \<in> {v$i, u$i}" using w_def by auto
  then have "\<forall> i \<in> {0..<m} . w$i \<in> A" using u_elem_A v_elem_A by auto
  then have "{w $ i | i . i \<in> {..<m}} \<subseteq> A" by fastforce
  ultimately have "set\<^sub>v w \<subseteq> A" using w_def by simp
  then show "w \<in> C" using C_def w_def by auto


  have d_uw: "hamming_distance u w = n" proof -
    define D where D_prop: "D = (SOME D' . D' \<in> ?Ds)"

    have "D \<in> ?Ds" using someI_ex Ds_nonempty some_in_eq D_prop by meson
    then have "D \<subseteq> {0..<m}" using someI_ex Ds_nonempty some_in_eq by blast
    then have "{0..<m} = {0..<m} - D \<union> D" by auto

    then have "{i \<in> {0..<m} . (u $ i) \<noteq> (w $ i)} = {i \<in> ({0..<m} - D) . (u $ i) \<noteq> (w $ i)} \<union> {i \<in> D . (u $ i) \<noteq> (w $ i)}"
      by blast
    also have "\<dots> = {i\<in>({0..<m}-D). u$i \<noteq> u$i} \<union> {i \<in> D . (u $ i) \<noteq> (w $ i)}" using w_def D_prop by auto
    also have "\<dots> = {i \<in> D . (u $ i) \<noteq> (w $ i)}" by blast
    also have "\<dots> = {i \<in> D . (u $ i) \<noteq> (v $ i)}" using w_def D_prop \<open>D \<in> ?Ds\<close> by auto
    also have "\<dots> = {i \<in> D . True}" using \<open>D \<in> ?Ds\<close> by blast
    also have "\<dots> = D" by simp
    finally have "card {i \<in> {0..<m} . (u $ i) \<noteq> (w $ i)} = n" using \<open>D \<in> ?Ds\<close> by simp

    moreover have "hamming_distance u w = card {i \<in> {0..<m} . (u $ i) \<noteq> (w $ i)}"
      using hamming_distance_def assms m_prop w_def by simp

    ultimately show ?thesis using D_prop w_def by argo
  qed
  moreover have "hamming_distance w v = ?d - n" proof -
    define D where D_prop: "D = (SOME D' . D' \<in> ?Ds)"

    have "D \<in> ?Ds" using someI_ex Ds_nonempty some_in_eq D_prop by meson


    have "D \<subseteq> {0..<m}" using someI_ex Ds_nonempty some_in_eq \<open>D \<in> ?Ds\<close> by blast
    then have "{0..<m} = {0..<m} - D \<union> D" by auto

    then have "{i \<in> {0..<m} . (w $ i) \<noteq> (v $ i)} = {i \<in> ({0..<m} - D) . (w $ i) \<noteq> (v $ i)} \<union> {i \<in> D . (w $ i) \<noteq> (v $ i)}"
      by blast
    also have "\<dots> = {i\<in>({0..<m}-D). u$i \<noteq> v$i} \<union> {i \<in> D . w$i \<noteq> v$i}" using w_def D_prop by auto
    also have "\<dots> = {i\<in>({0..<m}-D). u$i \<noteq> v$i} \<union> {i \<in> D . v$i \<noteq> v$i}" using w_def D_prop \<open>D \<in> ?Ds\<close> by auto
    also have "\<dots> = {i\<in>({0..<m}-D). u$i \<noteq> v$i}" by blast
    also have "\<dots> =  {i \<in> {0..<m} . u$i = v$i \<and> u$i \<noteq> v$i} \<union> {i \<in> (?diff_idx - D) . u$i \<noteq> v$i}"
      using \<open>D \<in> ?Ds\<close> by blast
    also have "\<dots> = {i \<in> (?diff_idx - D) . u$i \<noteq> v$i}" by simp
    also have "\<dots> = ?diff_idx - D" by auto
    finally have "card {i \<in> {0..<m} . (w $ i) \<noteq> (v $ i)} = card (?diff_idx - D)" using \<open>D \<in> ?Ds\<close> by presburger
    moreover have "D \<subseteq> ?diff_idx" using \<open>D \<in> ?Ds\<close> by simp
    moreover have "finite D" using \<open>D \<in> ?Ds\<close> \<open>D \<subseteq> {0..<m}\<close> finite_subset by blast
    ultimately have "card {i \<in> {0..<m} . (w $ i) \<noteq> (v $ i)} = card ?diff_idx - card D"
      using card_Diff_subset by auto
    then have "card {i \<in> {0..<m} . (w $ i) \<noteq> (v $ i)} = ?d - n" using diff_card \<open>D \<in> ?Ds\<close> by auto

    moreover have "hamming_distance w v = card {i \<in> {0..<m} . (w $ i) \<noteq> (v $ i)}"
      using hamming_distance_def assms m_prop w_def by simp

    ultimately show ?thesis using D_prop w_def by argo
  qed
  ultimately show "hamming_distance u w = n \<and> hamming_distance w v = ?d - n" by fast

qed
  

theorem min_distance_ecc:
  fixes
    C :: "'a vec set" and
    t :: nat
  assumes "is_code C"
  shows "corrects_errors t C = (minimum_distance C \<ge> 2 * t + 1)"
proof
  show "corrects_errors t C \<Longrightarrow> (minimum_distance C \<ge> 2 * t + 1)" proof (rule ccontr)

    let ?distances = "{hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}"

    assume ecc: "corrects_errors t C"
    assume "\<not> (minimum_distance C \<ge> 2 * t + 1)"
    then have "minimum_distance C < 2 * t + 1" by linarith
    then have dist: "Min ?distances < 2 * t + 1" using minimum_distance_def assms is_code_def by algebra
    
    have "finite ?distances" using distances_finite assms by simp
    moreover have "?distances \<noteq> {}" using distances_nonempty assms by simp
    ultimately have "Min ?distances \<in> ?distances" using linorder_class.Min_in[OF \<open>finite ?distances\<close> \<open>?distances \<noteq> {}\<close>] by argo

    then have "\<exists> p \<in> {p \<in> C \<times> C . fst p \<noteq> snd p}. hamming_distance (fst p) (snd p) = Min ?distances" by fastforce
    then have "\<exists> p \<in> (C \<times> C) . fst p \<noteq> snd p \<and> hamming_distance (fst p) (snd p) = Min ?distances" by blast
    then have "\<exists> u \<in> C . \<exists> v \<in> C . u \<noteq> v \<and> hamming_distance u v = Min ?distances" by simp
    then obtain u v where "u\<in>C" "v\<in>C" "u\<noteq>v" "hamming_distance u v = Min ?distances" by blast 

    then have "hamming_distance u v < 2 * t + 1" using dist by metis
    then have uv_bound: "hamming_distance u v \<le> 2 * t" using dist by fastforce

    then obtain w where w_bounds:
        "w \<in> C"
        "hamming_distance u w = hamming_distance u v div 2"
        "hamming_distance w v = hamming_distance u v - (hamming_distance u v div 2)" 
      using hamming_interpol[OF \<open>is_code C\<close> \<open>u\<in>C\<close> \<open>v\<in>C\<close>, of "hamming_distance u v div 2"] assms by auto

    then have "hamming_distance u w \<le> t" using uv_bound by linarith
    moreover from w_bounds have "hamming_distance w v \<le> t" using uv_bound by linarith

    ultimately have "{u, v} \<subseteq> {x\<in>C . hamming_distance w x \<le> t}" using \<open>u \<in> C\<close> \<open>v \<in> C\<close> \<open>w \<in> C\<close> assms by auto
    moreover have "finite {x\<in>C . hamming_distance w x \<le> t}" using is_code_def assms by auto
    ultimately have "card {u, v} \<le> card {x \<in> C. hamming_distance w x \<le> t}" using card_mono by blast
    then have "1 < card {x \<in> C. hamming_distance w x \<le> t}" using \<open>u \<noteq> v\<close> by auto

    moreover have "\<forall>u\<in>C. card {v \<in> C. hamming_distance u v \<le> t} \<le> 1"
      using ecc corrects_errors_def assms by algebra

    ultimately show "False" using ecc corrects_errors_def \<open>w \<in> C\<close> by auto
  qed
next
  have fini: "finite C" using is_code_def assms by auto 
  assume distance_min: "minimum_distance C \<ge> 2*t + 1"
  moreover have "\<forall> u\<in>C. card {v\<in>C . hamming_distance u v \<le> t} \<le> 1" proof
    fix u
    assume u_elem: "u \<in> C"
    let ?base = "{v \<in> C. local.hamming_distance u v \<le> t}"
    have "\<And> v . v \<in> C \<Longrightarrow> hamming_distance u v \<le> t = (u = v)" proof
      fix v
      assume "u = v"
      then show "hamming_distance u v \<le> t" using hamming_distance_def by simp
    next
      fix v
      assume assms': "v \<in> C" "hamming_distance u v \<le> t"
      show "u = v" proof (rule ccontr)
        assume "u \<noteq> v"
        then have "minimum_distance C \<le> t" using minimum_distance_bounds assms assms' u_elem by fastforce
        then show "False" using distance_min by linarith
      qed
    qed
    then have "?base = {v\<in>C . u = v}" by auto
    also have "\<dots> = {u}" using u_elem by auto
    finally show "card ?base \<le> 1" using u_elem by simp
  qed
  moreover have "corrects_errors t C = (\<forall> u\<in>C. card {v\<in>C . hamming_distance u v \<le> t} \<le> 1)" 
    using assms corrects_errors_def by presburger
  ultimately show "corrects_errors t C" by simp
qed

value "5 div 2::nat"

end