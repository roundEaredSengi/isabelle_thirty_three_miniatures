theory Miniature_Five
  imports Thirty_Three_Miniatures_Root "Miniature_Five/Code"

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

end