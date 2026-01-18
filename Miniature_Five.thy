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
  "is_code C = (finite C \<and> (\<exists> n . \<forall> w \<in> C . dim_vec w = n))"

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

theorem min_distance_ecc:
  fixes
    C :: "'a vec set" and
    t :: nat
  assumes "is_code C"
  shows "corrects_errors t C = (minimum_distance C \<ge> 2 * t + 1)"
proof
  show "corrects_errors t C \<Longrightarrow> (minimum_distance C \<ge> 2 * t + 1)" proof (rule ccontr)
    assume ecc: "corrects_errors t C"
    assume "\<not> (minimum_distance C \<ge> 2 * t + 1)"
    then have dist: "minimum_distance C < 2 * t + 1" by linarith
    show "False" sorry
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

end