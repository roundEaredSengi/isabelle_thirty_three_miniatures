theory Miniature_Three
imports Thirty_Three_Miniatures_Root

begin

text \<open>Auxiliary Definitions\<close> 

text \<open>Basic Definitions\<close>

type_synonym 'c club = "'c set"

type_synonym 'c family = "'c set list"

fun card_rule :: "'c family \<Rightarrow> bool" where
  "card_rule \<F> = (\<forall>C \<in> set \<F>. (card C) mod 2 = 1)"

fun intersect_rule :: "'c family \<Rightarrow> bool" where
  "intersect_rule \<F> = (\<forall>C \<in> set \<F>. \<forall>C' \<in> set \<F>. (card (C \<inter> C')) mod 2 = 0)"

fun is_club :: "'c list \<Rightarrow> 'c club \<Rightarrow> bool" where
  "is_club X C = (C \<subseteq> set X)"

text \<open>Oddtown Theorem\<close>

theorem oddtown:
  fixes 
    X :: "'c list" and
    \<F> :: "'c family"
  assumes
    valid: "is_club X ` (set \<F>) = {True}" and
    odd_clubs: "card_rule \<F>" and
    even_ints: "intersect_rule \<F>"
  shows 
    "length \<F> \<le> length X"
proof -
  let ?A = "(transpose_mat (inc_mat_of X \<F>))::(gf2 mat)"
  have dim_A: "?A \<in> carrier_mat (length \<F>) (length X)"
    unfolding inc_mat_of_def
    by simp
  hence dim_AT: "transpose_mat ?A \<in> carrier_mat (length X) (length \<F>)"
    by simp
  with dim_A have rk_A: "rank (length \<F>) ?A \<le> length X"
    using vec_space.rank_le_nc
    by blast
  let ?M = "?A * (transpose_mat ?A)"
  have intersect_card:
    "\<forall>i::nat. \<forall>j::nat. i < length \<F> \<and> j < length \<F> \<longrightarrow> 
      (?M $$ (i, j) = Abs_gf2 ((card (\<F>!i \<inter> \<F>!j)) mod 2))"
    sorry
  moreover have "\<forall>i::nat. i < length \<F> \<longrightarrow> Abs_gf2 (card (\<F>!i) mod 2) = 1"
    using odd_clubs card_rule.simps[of \<F>]
    by (metis nth_mem one_gf2_def)
  ultimately have diag_one:
    "\<forall>i::nat. i < length \<F> \<longrightarrow> (?M $$ (i, i) = 1)"
    by simp
  have 
    "\<forall>i::nat. \<forall>j::nat. i < length \<F> \<and> j < length \<F> \<and> i \<noteq> j \<longrightarrow> 
      Abs_gf2 (card (\<F>!i \<inter> \<F>!j) mod 2) = 0"
    using even_ints intersect_rule.simps[of \<F>]
    by (metis nth_mem zero_gf2_def)
  with intersect_card have off_diag_zero:
    "\<forall>i::nat. \<forall>j::nat. i < length \<F> \<and> j < length \<F> \<and> i \<noteq> j \<longrightarrow> (?M $$ (i, j) = 0)"
    by simp
  have "dim_row ?M = dim_row (one_mat (length \<F>))"
    unfolding dim_row_def
    by (metis carrier_matD(1) dim_A dim_row_def index_mult_mat(2) index_one_mat(2))
  moreover have "dim_col ?M = dim_col (one_mat (length \<F>))"
    unfolding dim_col_def
    by (metis carrier_matD(2) dim_AT dim_col_def index_mult_mat(3) index_one_mat(3))
  ultimately have "?M = one_mat (length \<F>)"
    using diag_one off_diag_zero eq_matI
    by auto
  also have "rank (length \<F>) (one_mat (length \<F>)) = length \<F>"
    by (simp add: vec_space.low_rank_det_zero)
  finally have "rank (length \<F>) ?M = length \<F>"
    by simp
  thus ?thesis
    using vec_space.rank_mat_mul_right[OF dim_A dim_AT] rk_A
    by simp
qed

end