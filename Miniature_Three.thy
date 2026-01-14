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
  "intersect_rule \<F> = (\<forall>C \<in> set \<F>. \<forall>C' \<in> set \<F>. C \<noteq> C' \<longrightarrow> (card (C \<inter> C')) mod 2 = 0)"

(* No two citizens are the same *)
fun is_village :: "'c list \<Rightarrow> bool" where
  "is_village X = (\<forall>i < length X. \<forall>j < length X. (i \<noteq> j \<longrightarrow> X!i \<noteq> X!j))"

(* All clubs consist of citizens and no two clubs are the same *)
fun is_club_fam :: "'c list \<Rightarrow> 'c family \<Rightarrow> bool" where
  "is_club_fam X \<F> = (\<forall>i < length \<F>. \<forall>j < length \<F>. \<F>!i \<subseteq> set X \<and> (i \<noteq> j \<longrightarrow> \<F>!i \<noteq> \<F>!j))"

text \<open>Oddtown Theorem\<close>

lemma mod2_0_1_id:
  fixes 
    x :: nat
  assumes 
    "x \<in> {0, 1}"
  shows
    "x = x mod 2"
  using assms
  by fastforce

lemma abs_gf2_homom_mod2: "Abs_gf2 (x mod 2) + Abs_gf2 (y mod 2) = Abs_gf2 ((x + y) mod 2)"
proof (cases "even x")
  case x_even: True
  then have x_zero: "Abs_gf2 (x mod 2) = 0" using zero_gf2_def by simp
  then show ?thesis
  proof (cases "even y")
    case y_even: True
    then have "Abs_gf2 (y mod 2) = 0" using zero_gf2_def by simp
    moreover have "Abs_gf2 ((x+y) mod 2) = 0" using  x_even y_even zero_gf2_def by simp
    ultimately show ?thesis using x_zero by algebra
  next
    case y_odd: False
    then have "(y mod 2) = 1" by presburger
    then have "Abs_gf2 (y mod 2) = 1"  using one_gf2_def by argo
    moreover have "(x+y) mod 2 = 1" using x_even y_odd by presburger
    then have "Abs_gf2 ((x+y) mod 2) = 1" using one_gf2_def by simp
    ultimately show ?thesis using x_zero by algebra
  qed  
next
  case x_odd: False
  then have "x mod 2 = 1" by presburger
  then have x_one: "Abs_gf2 (x mod 2) = 1" using one_gf2_def by simp
  then show ?thesis
  proof (cases "even y")
    case y_even: True
    then have "Abs_gf2 (y mod 2) = 0" using zero_gf2_def by simp
    moreover have "(x+y) mod 2 = 1" using x_odd y_even by presburger
    then have "Abs_gf2 ((x+y) mod 2) = 1" using one_gf2_def by simp
    ultimately show ?thesis using x_one by algebra
  next
    case y_odd: False
    then have "(y mod 2) = 1" by presburger
    then have "Abs_gf2 (y mod 2) = 1"  using one_gf2_def by argo
    moreover have "(x+y) mod 2 = 0" using x_odd y_odd by presburger
    then have "Abs_gf2 ((x+y) mod 2) = 0" using zero_gf2_def by simp
    moreover have "(1::gf2) + 1 = 0" unfolding plus_gf2_def zero_gf2_def by simp
    ultimately show ?thesis using x_one by argo 
  qed
qed

lemma sum_mod_2_gf2:
  fixes 
    f :: "'x \<Rightarrow> nat" and
    X :: "'x set"
  assumes
    "\<forall>x. f x \<in> {0, 1}" 
  shows
    "finite X \<Longrightarrow> Abs_gf2 ((sum f X) mod 2) = sum (Abs_gf2 \<circ> f) X"
proof (induction "card X" arbitrary: X)
  case 0
  hence "sum f X = 0"
    by simp
  moreover have "sum (Abs_gf2 \<circ> f) X = 0"
    using "0.prems" "0.hyps"
    by simp
  ultimately show ?case
    using zero_gf2_def 
    by presburger
next
  case (Suc x)
  hence "card X > 0"
    by simp
  then obtain a :: 'x where "a \<in> X"
    by (rule Multisets_Extras.elem_exists_non_empty_set)
  hence "card (X-{a}) = x"
    using Suc.hyps
    by simp
  hence ind_hyp:
    "Abs_gf2 (sum f (X-{a}) mod 2) = sum (Abs_gf2 \<circ> f) (X-{a})"
    using Suc.hyps Suc.prems
    by blast
  have "(sum f X mod 2) = ((f a + sum f (X-{a})) mod 2)"
    by (metis \<open>a \<in> X\<close> Suc.prems sum.remove)
  then have "Abs_gf2 (sum f X mod 2) = Abs_gf2 (f a mod 2) + (Abs_gf2 (sum f (X-{a}) mod 2))" using abs_gf2_homom_mod2 by presburger
  moreover  have "\<dots> = Abs_gf2 (f a mod 2) + (sum (Abs_gf2 \<circ> f) (X - {a}))" using ind_hyp by argo
  moreover  have "\<dots> = Abs_gf2 (f a) + (sum (Abs_gf2 \<circ> f) (X - {a}))" using assms mod2_0_1_id by presburger
  moreover  have "\<dots> = (Abs_gf2 \<circ> f) a + (sum (Abs_gf2 \<circ> f) (X - {a}))" by simp
  moreover  have "\<dots> = sum (Abs_gf2 \<circ> f) X" using \<open>a \<in> X\<close> Suc.prems sum.remove by metis
  ultimately show ?case by argo
qed

lemma set_card: 
  fixes 
    X :: "'x set" and
    \<phi> :: "'x \<Rightarrow> bool"
  shows
    "finite X \<Longrightarrow> card {x | x. x \<in> X \<and> \<phi> x} = sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X"
proof (induction "card X" arbitrary: X)
  case 0
  hence "X = {}"
    by simp
  hence "{x | x. x \<in> X \<and> \<phi> x} = {}"
    by blast
  hence "card {x | x. x \<in> X \<and> \<phi> x} = 0"
    by (metis card.empty)
  moreover have "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X = 0"
    using \<open>X = {}\<close>
    by simp
  ultimately show ?case
    using "0.hyps" "0.prems"
    by simp
next
  case (Suc x)
  hence "card X > 0"
    by simp
  then obtain a :: 'x where "a \<in> X"
    by (rule Multisets_Extras.elem_exists_non_empty_set)
  have "x = card X - 1"
    using Suc.hyps
    by simp
  hence "x = card (X-{a})"
    using \<open>a \<in> X\<close>
    by simp
  hence card_minus_a:
    "card {x |x. x \<in> X-{a} \<and> \<phi> x} = (\<Sum>x\<in>X-{a}. if \<phi> x then 1::nat else 0)"
    using Suc.hyps Suc.prems
    by blast
  have 
    "{x |x. x \<in> X \<and> \<phi> x} = {x |x. x \<in> X-{a} \<and> \<phi> x} \<union> (if (\<phi> a) then {a} else {})"
    using \<open>a \<in> X\<close>
    by auto
  moreover have "{x |x. x \<in> X-{a} \<and> \<phi> x} \<inter> (if (\<phi> a) then {a} else {}) = {}"
    by simp
  moreover have "finite {x |x. x \<in> X-{a} \<and> \<phi> x}"
    using Suc.prems
    by simp
  moreover have "finite (if (\<phi> a) then {a} else {})"
    by simp
  ultimately have
    "card {x |x. x \<in> X \<and> \<phi> x} = card {x |x. x \<in> X-{a} \<and> \<phi> x} + card (if (\<phi> a) then {a} else {})"
    using card_Un_Int 
    by simp
  hence
    "card {x |x. x \<in> X \<and> \<phi> x} = 
      (\<Sum>x\<in>X - {a}. if \<phi> x then 1 else 0) + (if (\<phi> a) then 1::nat else 0)"
    using card_minus_a
    by simp
  moreover have 
    "(\<Sum>x\<in>X - {a}. if \<phi> x then 1 else 0) =
      (\<Sum>x\<in>X. if \<phi> x then 1 else 0) - (if \<phi> a then 1::nat else 0)"
    using sum_diff1[of X "\<lambda>x. if (\<phi> x) then 1::nat else 0" a] Suc.prems \<open>a \<in> X\<close>
    by (meson sum_diff1_nat)
  ultimately show ?case
    by (metis (no_types, lifting) Suc.prems \<open>a \<in> X\<close> add.commute sum.remove)
qed

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