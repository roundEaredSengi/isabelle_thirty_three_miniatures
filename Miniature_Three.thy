chapter \<open>Miniature Three\<close>

theory Miniature_Three
  imports Thirty_Three_Miniatures_Root
          Util

begin

text \<open>
  Miniature 3 employs linear algebra techniques to show a result from extremal set theory,
  namely the "Oddtown Theorem" which states that there are no more than n different clubs
  in a city with n people if each club has an odd number of members and any two clubs intersect
  in an even number of members.
\<close>

section \<open>Auxiliary Definitions\<close> 

text \<open>
  We define a club as an arbitrary set and a "club family" as a list of clubs.
  We decided against defining a family as a set of clubs because defining a matrix based on
  already ordered list entries is easier than defining a matrix based on elements of a set.
\<close>

type_synonym 'c club = "'c set"
type_synonym 'c family = "'c set list"

text \<open>
  The cardinality rule constrains the number of members per club to odd numbers.
  The intersection rule constrains the number of members per club intersection to even numbers.
  Both rules combined define the preconditions of the Oddtown Theorem.
\<close>
fun card_rule :: "'c family \<Rightarrow> bool" where
  "card_rule \<F> = (\<forall>C \<in> set \<F>. (card C) mod 2 = 1)"

fun intersect_rule :: "'c family \<Rightarrow> bool" where
  "intersect_rule \<F> = (\<forall>C \<in> set \<F>. \<forall>C' \<in> set \<F>. C \<noteq> C' \<longrightarrow> (card (C \<inter> C')) mod 2 = 0)"

text \<open>
  Like the club family, we define a village as a list of people, no two of which are identical.
  Requiring distinctness is necessary s.t. the length of a list corresponds to the set cardinality
  of the corresponding set of elements, which we are interested in in the Oddtown theorem.
  
  To check that the predicates are satisfiable, we instantiate them with small examples.
\<close>
fun is_village :: "'c list \<Rightarrow> bool" where
  "is_village X = (\<forall>i < length X. \<forall>j < length X. i \<noteq> j \<longrightarrow> X!i \<noteq> X!j)"

value "is_village [1::nat, 42]"

fun is_club_fam :: "'c list \<Rightarrow> 'c family \<Rightarrow> bool" where
  "is_club_fam X \<F> = (\<forall>i < length \<F>. \<forall>j < length \<F>. \<F>!i \<subseteq> set X \<and> (i \<noteq> j \<longrightarrow> \<F>!i \<noteq> \<F>!j))"

value "is_club_fam [1::nat, 42] [{1::nat}, {42::nat}]"

section \<open>Oddtown Theorem\<close>

text \<open>
  To prove the Oddtown Theorem, we consider the matrix whose columns are the characteristic vectors
  of each club, i.e., a vector whose entries are 1 iff the corresponding citizen is in the club
  and 0 otherwise. The maximum number of clubs satisfying all rules is the maximum number of
  columns in a valid matrix:

    1) We can bound the rank of this matrix by the number n of citizens.
    2) Moreover, using the oddtown rules we can show that multiplying the matrix with its transpose
        yields the identity matrix over \<^latex>\<open>$\mathbb{F}_2^m$\<close> where m is the number of columns.
    3) The rank of the matrix product is further bounded by the rank of the original matrix,
        yielding \<^latex>\<open>m \leq n\<close> as desired. 
\<close>

theorem oddtown:
  fixes 
    X :: "'c list" and
    \<F> :: "'c family"
  assumes
    village: "is_village X" and
    valid: "is_club_fam X \<F>" and
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
  proof (safe)
    fix i :: nat and j :: nat
    assume "i < length \<F>" and "j < length \<F>"
    let ?index_in_inter = "\<lambda>k. (X!k) \<in> (\<F>!i \<inter> \<F>!j)"
    let ?in_inter_ind = "\<lambda>k. if ?index_in_inter(k) then 1 else 0"
    let ?index_range = "{0 ..< length X}"
    let ?inter_indices = "{k | k. k \<in> ?index_range \<and> ?index_in_inter(k)}"
    have valued_0_1:
      "\<forall>k. ?in_inter_ind k \<in> {0::nat, 1}"
      by simp
    have
      "sum ?in_inter_ind ?index_range 
        = card ?inter_indices"
      using set_card[of ?index_range ?index_in_inter]
      by simp
    hence
      "Abs_gf2 (sum ?in_inter_ind ?index_range mod 2)
        = Abs_gf2 (card ?inter_indices mod 2)"
      by simp
    moreover have
      "Abs_gf2 (sum ?in_inter_ind ?index_range mod 2)
        = (sum (Abs_gf2 \<circ> ?in_inter_ind) ?index_range)"
      using sum_mod_2_gf2[of ?in_inter_ind ?index_range] valued_0_1
      by simp
    moreover have 
      "(Abs_gf2 \<circ> ?in_inter_ind)
        = (\<lambda>k. if ?index_in_inter(k) then Abs_gf2 1 else Abs_gf2 0)"
      by auto
    ultimately have
      "(sum (\<lambda>k. if ?index_in_inter(k) then Abs_gf2 1 else Abs_gf2 0) ?index_range)
        = Abs_gf2 (card ?inter_indices mod 2)"
      by metis
    hence sum:
      "(sum (\<lambda>k. if ?index_in_inter(k) then 1::gf2 else 0::gf2) ?index_range)
        = Abs_gf2 (card ?inter_indices mod 2)"
      by (metis one_gf2_def zero_gf2_def)
    have "inj_on (\<lambda>k. X!k) ?index_range"
      unfolding inj_on_def
      using village atLeast0LessThan 
      by auto
    hence "inj_on (\<lambda>k. X!k) ?inter_indices"
      by (simp add: inj_on_def)
    moreover have 
      "(\<lambda>k. X!k) ` ?inter_indices = \<F>!i \<inter> \<F>!j"
    proof (safe)
      fix
        x :: 'c
      assume
        "x \<in> \<F> ! i" and
        "x \<in> \<F> ! j"
      hence "x \<in> set X" 
        using valid \<open>i < length \<F>\<close> \<open>j < length \<F>\<close>
        by auto
      with this obtain k :: nat where "k \<in> ?index_range" and "x = X!k"
        by (metis imageE list.set_map map_nth set_upt)
      thus "x \<in> (!) X ` ?inter_indices"
        using \<open>x \<in> \<F>!i\<close> \<open>x \<in> \<F>!j\<close>
        by simp
    qed
    ultimately have
      "bij_betw (\<lambda>k. X!k) ?inter_indices (\<F>!i \<inter> \<F>!j)"
      unfolding bij_betw_def
      by simp
    hence card:
      "card ?inter_indices = card (\<F>!i \<inter> \<F>!j)"
      by (rule bij_betw_same_card)
    have 
      "\<forall>k \<in> ?index_range. (row ?A i) $ k = (if (X!k) \<in> (\<F>!i) then 1 else 0)"
      unfolding inc_mat_of_def
      by (simp add: \<open>i < length \<F>\<close>)
    moreover have
      "\<forall>k \<in> ?index_range. (col ?A\<^sup>T j) $ k = (row ?A j) $ k"
      by (simp add: \<open>j < length \<F>\<close> inc_mat_dim_col)
    ultimately have 
      "\<forall>k \<in> ?index_range. (row ?A i) $ k * (col ?A\<^sup>T j) $ k 
        = (if (X!k) \<in> (\<F>!i) then 1 else 0) * (if (X!k) \<in> (\<F>!j) then 1 else 0)"
      by (simp add: \<open>j < length \<F>\<close> inc_mat_col_def)
    hence intersect:
      "\<forall>k \<in> ?index_range. (row ?A i) $ k * (col ?A\<^sup>T j) $ k 
        = (if (X!k) \<in> (\<F>!i \<inter> \<F>!j) then 1 else 0)"
      by simp
    have "(?A * ?A\<^sup>T) $$ (i, j) = row ?A i \<bullet> col ?A\<^sup>T j"
      unfolding times_mat_def
      by (simp add: inc_mat_dim_col \<open>i < length \<F>\<close> \<open>j < length \<F>\<close>)
    also have 
      "row ?A i \<bullet> col ?A\<^sup>T j = sum (\<lambda>k. (row ?A i) $ k * (col ?A\<^sup>T j) $ k) {0 ..< dim_vec (row ?A i)}"
      unfolding scalar_prod_def
      by simp
    also have "... = sum (\<lambda>k. (row ?A i) $ k * (col ?A\<^sup>T j) $ k) ?index_range"
      using \<open>i < length \<F>\<close> dim_A
      by simp
    also have "... = sum ?in_inter_ind ?index_range"
      using intersect
      by simp
    also have "... = Abs_gf2 (card ?inter_indices mod 2)"
      using sum
      by simp
    also have "... = Abs_gf2 (card (\<F>!i \<inter> \<F>!j) mod 2)"
      using card
      by argo
    finally show "(?A * ?A\<^sup>T) $$ (i, j) = Abs_gf2 (card (\<F>!i \<inter> \<F>!j) mod 2)"
      by simp
  qed
  moreover have "\<forall>i::nat. i < length \<F> \<longrightarrow> Abs_gf2 (card (\<F>!i) mod 2) = 1"
    using odd_clubs card_rule.simps[of \<F>]
    by (metis nth_mem one_gf2_def)
  ultimately have diag_one:
    "\<forall>i::nat. i < length \<F> \<longrightarrow> (?M $$ (i, i) = 1)"
    by simp
  have 
    "\<forall>i::nat. \<forall>j::nat. i < length \<F> \<and> j < length \<F> \<and> i \<noteq> j \<longrightarrow> 
      Abs_gf2 (card (\<F>!i \<inter> \<F>!j) mod 2) = 0"
    using even_ints intersect_rule.simps[of \<F>] valid nth_mem zero_gf2_def
    by (metis is_club_fam.elims(2))
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