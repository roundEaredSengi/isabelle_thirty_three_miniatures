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
  "is_code C = (\<exists> n . \<forall> w \<in> C . dim_vec w = n)"

definition hamming_distance :: "'a::equal vec \<Rightarrow> 'a::equal vec \<Rightarrow> nat" where
  "hamming_distance a b = (if dim_vec a = dim_vec b then card {i \<in> {0..<dim_vec a} . (a $ i) \<noteq> (b $ i)} else  undefined)"

(*value "hamming_distance (vec_of_list [1::gf2,1,1]) (vec_of_list [1::gf2,0,1])" (*Breaks with (equal) vec :: equal instance*)*)

definition minimum_distance :: "'a::equal vec set \<Rightarrow> nat" where
  "minimum_distance C = (if is_code C then Min {hamming_distance w1 w2 | w1 w2 . w1 \<in> C \<and> w2 \<in> C \<and> w1 \<noteq> w2}  else undefined)"
definition minimum_distance' :: "'a::equal vec set \<Rightarrow> nat set" where
  "minimum_distance' C = (if is_code C then {hamming_distance w1 w2 | w1 w2 . w1 \<in> C \<and> w2 \<in> C}  else undefined)"

definition corrects_errors :: "nat \<Rightarrow> 'a::equal vec set \<Rightarrow> bool" where
  "corrects_errors t C \<equiv> if is_code C then \<forall> u\<in>C. card {v\<in>C . hamming_distance u v \<le> t} \<le> 1 else undefined"

theorem min_distance_ecc:
  assumes "is_code C"
  shows "corrects_errors t C \<equiv> minimum_distance C \<ge> 2 * t + 1"
  sorry

end