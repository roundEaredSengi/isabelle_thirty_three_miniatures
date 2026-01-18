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

definition is_code :: "'a vec set \<Rightarrow> bool" where
  "is_code C = (finite C \<and> card C > 1 \<and> (\<exists> n . \<forall> w \<in> C . dim_vec w = n))"

definition hamming_distance :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> nat" where
  "hamming_distance a b = (if dim_vec a = dim_vec b then card {i \<in> {0..<dim_vec a} . (a $ i) \<noteq> (b $ i)} else  undefined)"

(*value "hamming_distance (vec_of_list [1::gf2,1,1]) (vec_of_list [1::gf2,0,1])" (*Breaks with (equal) vec :: equal instance*)*)

definition minimum_distance :: "'a vec set \<Rightarrow> nat" where
  "minimum_distance C = (if is_code C then Min {hamming_distance (fst p) (snd p) | p . p \<in> C \<times> C \<and> fst p \<noteq> snd p}  else undefined)"

definition corrects_errors :: "nat \<Rightarrow> 'a vec set \<Rightarrow> bool" where
  "corrects_errors t C \<equiv> if is_code C then \<forall> u\<in>C. card {v\<in>C . hamming_distance u v \<le> t} \<le> 1 else undefined"

lemma map_finite:
  assumes
    "finite S"
  shows
    "finite {f x | x . x \<in> S \<and> P x}"
  using assms by simp
  

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
  have "{p \<in> C \<times> C . fst p \<noteq> snd p} = (C \<times> C) - {p \<in> C \<times> C . fst p = snd p}" using assms is_code_def by auto
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} = card ((C \<times> C) - {p \<in> C \<times> C . fst p = snd p})" by presburger
  also have "\<dots> = card (C \<times> C) - card {p \<in> C \<times> C . fst p = snd p}" using card_Diff_subset assms is_code_def
    by (metis (no_types, lifting) finite_SigmaI mem_Collect_eq rev_finite_subset subsetI)
  also have "\<dots> = card (C \<times> C) - card {(x, x) | x . x \<in> C}"
    by (metis (no_types, lifting) SigmaE SigmaI split_pairs)
  also have "\<dots> = card (C \<times> C) - card C"
    by (simp add: Setcompr_eq_image card_image inj_on_convol_ident)
  also have "\<dots> = (card C) * (card C) - card C"
    by (metis card_cartesian_product)
  also have "\<dots> = (card C - 1) * (card C)"
    by (simp add: diff_mult_distrib)
  finally have "card {p \<in> C \<times> C . fst p \<noteq> snd p} = (card C - 1) * card C" by presburger
  then have "card {p \<in> C \<times> C . fst p \<noteq> snd p} > (card C - 1) * 1" using assms is_code_def by auto
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

  have "finite (C \<times> C)" using assms is_code_def by blast
  then show ?thesis by (rule map_finite)
qed

lemma hamming_symm[simp]:
  assumes
    "is_code C"
    "u \<in> C"
    "v \<in> C"
  shows
    "hamming_distance u v = hamming_distance v u"
  sorry

lemma hamming_interpol:
  assumes
    "is_code C" and
    "u \<in> C" and
    "v \<in> C" and
    "n \<in> {0..hamming_distance u v}"
  shows
    "\<exists> w \<in> C . hamming_distance u w = n \<and> hamming_distance w v = hamming_distance u v - n"
  sorry (* Requires adjustment to is_code to be based on alphabet *)

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