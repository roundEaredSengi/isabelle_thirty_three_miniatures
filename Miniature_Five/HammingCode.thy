theory HammingCode
  imports GeneratingMatrix LinearCode CarriersetMatrix
begin

hide_const (open) Matrix.scalar_prod
hide_const (open) Matrix.mult_mat_vec

lemma (in induced_vs) matrix_mul:
  assumes
    "dim_row A = n"
  shows
    "mult_mat_vec A v = (\<Oplus>\<^bsub>VS\<^esub>i \<in> {0..<dim_col A}. v $ i \<otimes>\<^bsub>VS\<^esub> (col A i))"
  sorry

lemma (in field) matrix_mul_idx:
  assumes
    "i \<in> {0..<dim_row A}"
  shows
    "mult_mat_vec A v $ i = (\<Oplus>\<^bsub>R\<^esub>j \<in> {0..<dim_col A}. v $ j \<otimes>\<^bsub>R\<^esub> (col A j $ i))"
  sorry

abbreviation gf2_ring where
  "gf2_ring \<equiv> \<lparr> 
  carrier = UNIV::gf2 set,
  mult = times,
  one = 1::gf2,
  zero = 0::gf2,
  add = plus,
  module.smult = times::gf2 \<Rightarrow> gf2 \<Rightarrow> gf2
\<rparr>"

term "(\<lambda>i. 0)(1 := 2)"

fun nth_gf2_vec:: "nat \<Rightarrow> nat \<Rightarrow> gf2 vec" where
  "nth_gf2_vec 0 n = vec 0 (\<lambda>i. 0)"
| "nth_gf2_vec d 0 = vec d (\<lambda>i. 0)"
| "nth_gf2_vec d n = vec d ((\<lambda>i. nth_gf2_vec (d-1) (n div 2) $ (i - 1))(0 := (if (n mod 2 = 0) then 0 else 1)))"

lemma nth_gf2_vec_len:
  "dim_vec (nth_gf2_vec d n) = d"
proof -
  consider "d = 0" | "d \<noteq> 0" "n = 0" | "d \<noteq> 0" "n \<noteq> 0" by satx
  then show ?thesis proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    then show ?thesis
      by (metis (lifting) dim_vec nth_gf2_vec.elims)
  next
    case 3
    then show ?thesis
      by (metis (lifting) dim_vec nth_gf2_vec.elims)
  qed
qed

lemma nonfirst_vec_nonzero:
    "n > 0 \<Longrightarrow> n < 2^(d+1) \<Longrightarrow> nth_gf2_vec (d + 1) n \<noteq> zero_vec (d+1)"
proof (induction d arbitrary: n)
  case 0
  assume "n < 2^(0+1)"
  then have "n < 2" by simp
  show "nth_gf2_vec (0 + 1) n \<noteq> zero_vec (0 + 1)" proof (rule ccontr)
    assume "\<not> nth_gf2_vec (0 + 1) n \<noteq> zero_vec (0 + 1)"
    then have "nth_gf2_vec 1 n = zero_vec 1" by algebra
    then have "nth_gf2_vec 1 n $ 0 = zero_vec 1 $ 0" by presburger
    then have "nth_gf2_vec 1 n $ 0 = 0" using zero_vec_def[of 1] by simp
    then have "n mod 2 = 0" using 0 nth_gf2_vec.simps(3)[of 0 "n-1"] Nat.lessE by fastforce
    then have "n = 0" using \<open>n < 2\<close> by simp
    then show False using 0 by presburger
  qed
next
  case (Suc d)
  assume "n < 2^(Suc d + 1)"
  then have "n < 2^(d+2)" by simp

  show "nth_gf2_vec (Suc d + 1) n \<noteq> zero_vec (Suc d + 1)" proof (rule ccontr)
    assume "\<not> nth_gf2_vec (Suc d + 1) n \<noteq> zero_vec (Suc d + 1)"
    then have "nth_gf2_vec (d + 2) n = zero_vec (d + 2)" by simp
    then have "\<And>i. i < (d+2) \<Longrightarrow> nth_gf2_vec (d + 2) n $ i = zero_vec (d + 2) $ i" by simp
    then have all_zero: "\<And>i. i < (Suc d+1) \<Longrightarrow> nth_gf2_vec (Suc d + 1) n $ i = 0" by simp

    obtain m where "n = Suc m" using Suc Nat.lessE by metis

    from all_zero have "nth_gf2_vec (d+2) n $ 0 = 0" using zero_vec_def[of 1] by simp
    then have "nth_gf2_vec (Suc (d+1)) (Suc m) $ 0 = 0" using \<open>n = Suc m\<close> by simp
    then have "(if ((Suc m) mod 2 = 0) then 0 else 1) = 0" by auto
    then have "n mod 2 = 0" using \<open>n = Suc m\<close>
      by (metis zero_neq_one)

    from all_zero have "\<And>i. i < (Suc (d+1)) \<Longrightarrow> i > 0 \<Longrightarrow> nth_gf2_vec (Suc (d + 1)) n $ i = 0" by simp
    from all_zero have nonz_idx: "\<And>i. i < (Suc (d+1)) \<Longrightarrow> i > 0 \<Longrightarrow> nth_gf2_vec (Suc (d + 1)) (Suc m) $ i = 0"
      using \<open>n = Suc m\<close> by force
    then have "nth_gf2_vec (Suc (d + 1)) (Suc m) = vec (Suc (d+1)) ((\<lambda>i. nth_gf2_vec (Suc (d+1) -1) ((Suc m) div 2) $ (i - 1))(0 := (if ((Suc m) mod 2 = 0) then 0 else 1)))" by simp
    then have "nth_gf2_vec (Suc (d + 1)) (Suc m) = vec (Suc (d+1)) ((\<lambda>i. nth_gf2_vec (d+1) (n div 2) $ (i - 1))(0 := (if (n mod 2 = 0) then 0 else 1)))"
      using \<open>n = Suc m\<close> by simp
    then have "\<And>i. i < (Suc (d+1)) \<Longrightarrow> i > 0 \<Longrightarrow> nth_gf2_vec (d+1) (n div 2) $ (i - 1) = 0"
      using nonz_idx by simp
    then have "\<And>i. i < (d+1) \<Longrightarrow> nth_gf2_vec (d+1) (n div 2) $ (i) = 0"
      by fastforce
    then have rec_zero: "nth_gf2_vec (d+1) (n div 2) = zero_vec (d+1)"
      using zero_vec_def nth_gf2_vec_len by auto

    have "n div 2 = 0" proof (rule ccontr)
      assume "n div 2 \<noteq> 0"
      then have "n div 2 > 0" by linarith

      have bound: "n div 2 < 2 ^ (d + 1)" using Suc by simp

      show False using Suc.IH[OF \<open>n div 2 > 0\<close> bound] using rec_zero by satx
    qed

    from \<open>n div 2 = 0\<close> \<open>n mod 2 = 0\<close> have "n = 0" by simp
    then show False using Suc by linarith
  qed
qed

abbreviation hamming_parity_columns where
  "hamming_parity_columns d \<equiv> [nth_gf2_vec d i. i \<leftarrow> [1..<2^d]]"
abbreviation hamming_parity_matrix where
  "hamming_parity_matrix d \<equiv> mat_of_cols d (hamming_parity_columns d)"


locale hamming_code = linear_code gf2_ring C "2^n - 1" for n C +
  assumes
    parity: "linear_code.parity_check_matrix gf2_ring C (2^n - 1) (hamming_parity_matrix n)"
begin

abbreviation "m \<equiv> 2^n - 1"
abbreviation "P \<equiv> hamming_parity_matrix n"

lemma par_check:
  assumes
    "v \<in> C"
    "i \<in> {0..<n}"
  shows
    "(field.mult_mat_vec gf2_ring P v) $ i = 0"
proof -
  have "i < n" using assms by auto
  then have "i < dim_row P" using mat_of_cols_carrier(2) by metis
  then show ?thesis using parity_check parity assms(1)
    by simp
qed

lemma finsum_to_sum:
  "(\<Oplus>\<^bsub>gf2_ring\<^esub>i \<in> {0..<j::nat}. f i) = (\<Sum>i\<in>{0..<j}. f i)"
proof -
have comm[simp]: "comm_monoid (add_monoid gf2_ring)"
    using ring_F ring_def abelian_group_def abelian_group_axioms_def comm_group_def
    by blast

  show ?thesis proof (induction j)
    case 0
    have "finsum gf2_ring f {0..<0} = finsum gf2_ring f {}" by simp
    also have "\<dots> = 0" unfolding finsum_def
      using comm comm_monoid.finprod_empty by fastforce
    also have "\<dots> = sum f {0..<0}" by simp
    finally show ?case .
  next
    case (Suc n)
    have "finsum gf2_ring f {0..<Suc n} = finsum gf2_ring f ({0..<n} \<union> {n})"
      by (simp add: set_upt_Suc)
    also have "\<dots> = finsum gf2_ring f {0..<n} + finsum gf2_ring f {n}"
      unfolding finsum_def
      using comm_monoid.finprod_Un_disjoint[of "add_monoid gf2_ring" "{0..<n}" "{n}"] comm
      by simp
    also have "\<dots> = finsum gf2_ring f {0..<n} + (f n) + finsum gf2_ring f {}" unfolding finsum_def
      using comm_monoid.finprod_insert[OF comm, of "{}" n f] by simp
    also have "\<dots> = finsum gf2_ring f {0..<n} + (f n)" unfolding finsum_def
      using comm comm_monoid.finprod_empty by fastforce
    also have "\<dots> = (\<Sum>i \<in> {0..<n}. f i) + f n" using Suc by presburger
    also have "\<dots> = (\<Sum>i \<in> {0..<n + 1}. f i)" by simp
    finally show ?case by simp
  qed
qed

lemma non_zero_places:
  assumes
    "v \<in> C"
    "v \<noteq> \<zero>\<^bsub>CS\<^esub>"
  shows
    "hamming_distance \<zero>\<^bsub>CS\<^esub> v \<ge> 3"
proof (rule ccontr)
  have orth_sum: "\<forall>i \<in> {0..<n}. (\<Sum>j \<in> {0..<m}. v $ j * (nth_gf2_vec n (j+1) $ i)) = 0" proof
    fix i
    assume i_bounds: "i \<in> {0..<n}"

    then have "(\<Oplus>\<^bsub>gf2_ring\<^esub>j \<in> {0..<m}. v $ j * (col P j $ i)) = 0"
      using field.matrix_mul_idx[OF field_F] assms par_check
      by simp
    then have "(\<Sum>j \<in> {0..<m}. v $ j * (col P j $ i)) = 0"
      using finsum_to_sum by algebra
    moreover have "\<And>j. j \<in>{0..<m} \<Longrightarrow> (col P j) = (nth_gf2_vec n (j+1))" proof -
      fix j
      assume "j \<in> {0..<m::nat}"
      then have "j < length (hamming_parity_columns n)"
        by simp
      moreover have "hamming_parity_columns n ! j = nth_gf2_vec n (j+1)"
        using calculation by fastforce
      moreover from calculation have "hamming_parity_columns n ! j \<in> carrier_vec n"
        using nth_gf2_vec_len[of n "j+1"] carrier_vec_def[of n] by auto
      ultimately show "col P j = nth_gf2_vec n (j+1)"
        using col_mat_of_cols[of "j+1" "hamming_parity_columns n" n] by simp
    qed
    then have "\<And>j. j \<in>{0..<m} \<Longrightarrow> (col P j) $i = (nth_gf2_vec n (j+1))$i" by presburger
    ultimately show "(\<Sum>j \<in> {0..<m}. v $ j * (nth_gf2_vec n (j+1) $ i)) = 0"
      using sum.cong by fastforce
  qed

  assume "\<not> 3 \<le> hamming_distance \<zero>\<^bsub>CS\<^esub> v"
  then consider "hamming_distance \<zero>\<^bsub>CS\<^esub> v = 0"
    | "hamming_distance \<zero>\<^bsub>CS\<^esub> v = 1"
    | "hamming_distance \<zero>\<^bsub>CS\<^esub> v = 2"
    by linarith
  then show False
  proof cases
    case 1
    moreover have "\<zero>\<^bsub>CS\<^esub> \<in> C"
      using submodule.zero_closed[of gf2_ring C VS] submod by simp
    ultimately have "\<exists>i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub>$i \<noteq> v$i"
      using words_subs words assms by fastforce
    then have "{i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub>$ i \<noteq> v$ i} \<noteq> {}"
      by blast
    then have "hamming_distance \<zero>\<^bsub>CS\<^esub> v > 0"
      unfolding hamming_distance_def word
      by fastforce
    then show "False" using 1 by linarith
  next
    case 2
    then have card: "card {i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub> $ i \<noteq> v $ i} = 1"
      unfolding hamming_distance_def
      by satx
    then obtain i where i: "\<zero>\<^bsub>CS\<^esub> $ i \<noteq> v $ i" "i \<in> {0..<m}"
      by (metis (mono_tags, lifting) Min_in card.empty distinct_elems_card mem_Collect_eq zero_neq_one)
    then have inz: "v $ i \<noteq> 0" unfolding VS zero_vec_def by auto
    have j_zero: "\<And> j. j \<in> {0..<m} - {i} \<Longrightarrow> 0 = v $ j" proof -
      fix j
      assume j: "j \<in> {0..<m} - {i}"
      have "\<zero>\<^bsub>CS\<^esub> $ j = v $ j" proof (rule ccontr)
        assume "\<zero>\<^bsub>CS\<^esub> $ j \<noteq> v $ j"
        then have "{i, j} \<subseteq> {i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub> $ i \<noteq> v $ i}" using i j by blast
        then have "card {i,j} \<le> 1" using card
          by (metis (lifting) card.infinite card_mono zero_neq_one)
        moreover have "card {i,j} \<ge> 1"
          using j by simp
        ultimately have "card {i,j} = 1" by linarith
        then have "i = j"
          using is_singleton_iff_ex1 by fastforce
        then show False using j by blast
      qed
      then show "0 = v $ j" unfolding VS zero_vec_def using j by auto
    qed

    have "\<forall>k \<in> {0..<n}. (nth_gf2_vec n (i+1) $ k) = 0" proof
      fix k
      assume "k \<in> {0..<n}"
      then have "0 = (\<Sum>j \<in> {0..<m}. v $ j * (nth_gf2_vec n (j+1) $ k))"
        using orth_sum by auto

      also have "\<dots>
               = (\<Sum>j \<in> ({0..<m} - {i}). v $ j * (nth_gf2_vec n (j+1) $ k)) + (v$i * (nth_gf2_vec n (i+1) $ k))"
        using i
        by (simp add: sum.remove)

      also have "\<dots>
               = (\<Sum>j \<in> ({0..<m} - {i}). 0) + (v$i * (nth_gf2_vec n (i+1) $ k))"
        using j_zero by simp

      also have "\<dots> = (v$i * (nth_gf2_vec n (i+1) $ k))" by simp
      finally have "v$i * (nth_gf2_vec n (i+1) $ k) = 0" by presburger
      then show "nth_gf2_vec n (i+1) $ k = 0" using inz by simp
    qed
    then have zero: "nth_gf2_vec n (i+1) = Matrix.zero_vec n" using nth_gf2_vec_len by auto
    
    have "i+1 > 0" by linarith
    moreover have "i+1 < 2^n" using i by simp
    ultimately have False using nonfirst_vec_nonzero[of "i+1" "n-1"] using i
      by (metis add.commute add_diff_inverse_nat bot_nat_0.not_eq_extremum less_one power_0
          zero)

    then show False using zero by satx
  next
    case 3
    then show ?thesis sorry
  qed
qed

lemma min_dist: "minimum_distance \<ge> 3"
proof (rule ccontr)
assume "\<not> minimum_distance \<ge> 3"
  hence "minimum_distance < 3" by simp
  then have "Min {hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>} < 3" 
    using linear_min_distance by presburger
  moreover have "finite {hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}"
    using finite by simp
  moreover have "card C > 1" using code_def code_axioms by fastforce
  then have "\<exists> v \<in> C. v \<noteq> \<zero>\<^bsub>W\<^esub>"
    using distinct_elems_card
    by metis
  then have "{hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>} \<noteq> {}" by blast
  ultimately obtain v where v_props: "hamming_distance \<zero>\<^bsub>W\<^esub> v < 3" "v \<in> C" "v \<noteq> \<zero>\<^bsub>W\<^esub>"
    using Min_in[of "{hamming_distance \<zero>\<^bsub>W\<^esub> w |w. w \<in> C \<and> w \<noteq> \<zero>\<^bsub>W\<^esub>}"] by auto
  moreover have "\<zero>\<^bsub>W\<^esub> = \<zero>\<^bsub>CS\<^esub>" by simp
  ultimately have "hamming_distance \<zero>\<^bsub>W\<^esub> v \<ge> 3" using non_zero_places by fastforce
  then show False using v_props by linarith
qed

lemma "corrects_errors 1"
  using min_dist min_distance_ec
  by presburger

end
  

end