theory HammingCode
  imports GeneratingMatrix LinearCode CarriersetMatrix
begin

hide_const (open) Matrix.scalar_prod
hide_const (open) Matrix.mult_mat_vec

lemma (in field) matrix_mul_idx:
  assumes
    "\<And>i j . i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i,j) \<in> carrier R"
    "\<And>i. i < dim_col A \<Longrightarrow> v $ i \<in> carrier R"
    "i \<in> {0..<dim_row A}"
    "dim_vec v = dim_col A"
  shows
    "mult_mat_vec A v $ i = (\<Oplus>j \<in> {0..<dim_col A}. v $ j \<otimes> (col A j $ i))"
proof -
  have repl_eq: "\<And>j. j \<in> {0..<dim_col A} \<Longrightarrow> row A i $ j \<otimes> v $ j = v $ j \<otimes> col A j $ i"
    unfolding row_def col_def using assms m_comm by simp

  have repl_closed: "\<And>j. j \<in> {0..<dim_col A} \<Longrightarrow> v $ j \<otimes> col A j $ i \<in> carrier R"
    unfolding col_def using m_closed assms by simp


  have "mult_mat_vec A v $ i = vec (dim_row A) (\<lambda> i. row A i \<bullet> v) $ i"
    unfolding mult_mat_vec_def by presburger
  also have "\<dots> = (\<lambda> i. row A i \<bullet> v) i"
    using assms by simp
  also have "\<dots> = row A i \<bullet> v"
    by presburger
  ultimately have "mult_mat_vec A v $ i = (\<Oplus>j\<in>{0..<dim_col A}. row A i $ j \<otimes> v $ j)"
    unfolding scalar_prod_def using assms by presburger
  also have "\<dots> = (\<Oplus>j\<in>{0..<dim_col A}. v $ j \<otimes> col A j $ i)"
    using finsum_cong'[OF _ _ repl_eq, of _ _ "\<lambda>i. i"]
    using repl_eq repl_closed
    by blast
  finally show ?thesis .
qed

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

lemma nth_gf2_vec_first_entry:
  assumes
    "d > 0"
  shows
    "nth_gf2_vec d n $ 0 = (if n mod 2 = 0 then 0 else 1)"
proof -
    have "(nth_gf2_vec d n $ 0) = ((\<lambda>i. nth_gf2_vec (d-1) (n div 2) $ (i - 1))(0 := (if (n mod 2 = 0) then 0 else 1))) 0"
      using assms nth_gf2_vec.simps(2) gr0_conv_Suc
      using assms by force
    then show ?thesis by simp
  qed

lemma nth_gf2_vec_tail:
  assumes
    "d > 0"
    "i \<in> {1..<d}"
  shows
    "nth_gf2_vec d n $ i = nth_gf2_vec (d-1) (n div 2) $ (i-1)"
proof -
  have "nth_gf2_vec d n $ i = vec d ((\<lambda>i. nth_gf2_vec (d-1) (n div 2) $ (i - 1))(0 := (if (n mod 2 = 0) then 0 else 1))) $ i"
    using assms nth_gf2_vec.simps(2)[of "d - 1" n] by simp
  also have "\<dots> = ((\<lambda>i. nth_gf2_vec (d-1) (n div 2) $ (i - 1))(0 := (if (n mod 2 = 0) then 0 else 1))) i"
    using assms by simp
  also have "\<dots> = (\<lambda>i. nth_gf2_vec (d-1) (n div 2) $ (i - 1)) i"
    using assms by auto
  finally show ?thesis by satx
qed

lemma nth_gf2_vec_inj:
  "inj_on (nth_gf2_vec d) {0..<2^d}"
proof (induction d)
  case (Suc d)
  show ?case proof
    fix x::nat and y::nat
    assume bounds: "x \<in> {0..<2^(Suc d)}" "y \<in> {0..<2^(Suc d)}"
    show "nth_gf2_vec (Suc d) x = nth_gf2_vec (Suc d) y \<Longrightarrow> x = y" proof (rule ccontr)
      assume res_eq: "nth_gf2_vec (Suc d) x = nth_gf2_vec (Suc d) y"
      assume "x \<noteq> y"
      then consider "x mod 2 \<noteq> y mod 2" | "x div 2 \<noteq> y div 2"
        by (metis div_mod_decomp)
      then show False proof cases
        case 1
        then show ?thesis using nth_gf2_vec_first_entry[of "Suc d"] res_eq
          by (metis not_mod_2_eq_1_eq_0 zero_less_Suc zero_neq_one)
      next
        case 2
        moreover from res_eq have "\<forall>i \<in> {1..<(Suc d)}. nth_gf2_vec (Suc d) x $ i = nth_gf2_vec (Suc d) y $ i" using nth_gf2_vec_len by metis
        then have "\<forall>i \<in> {1..<(Suc d)}. nth_gf2_vec d (x div 2) $ (i-1) = nth_gf2_vec d (y div 2) $ (i-1)" using nth_gf2_vec_tail[of "Suc d"] by simp
        then have "\<forall>i \<in> {0..<d}. nth_gf2_vec d (x div 2) $ i = nth_gf2_vec d (y div 2) $ i" by force
        then have "nth_gf2_vec d (x div 2) = nth_gf2_vec d (y div 2)" using nth_gf2_vec_len by auto

        then have "x div 2 = y div 2" using Suc.IH bounds unfolding inj_on_def by simp
        ultimately show False by satx
      qed
    qed
  qed
qed simp

lemma nonfirst_vec_nonzero:
  assumes
    "n > 0"
    "n < 2^d"
  shows
    "nth_gf2_vec d n \<noteq> zero_vec d"
proof -
  have "n \<noteq> 0" using assms by simp
  then have "nth_gf2_vec d n \<noteq> nth_gf2_vec d 0"
    using nth_gf2_vec_inj[of d] assms
    unfolding inj_on_def
    by fastforce
  moreover have "nth_gf2_vec d 0 = zero_vec d"  proof (induction d)
    case (Suc d)
    have "\<forall> i \<in> {1..<(Suc d)}. nth_gf2_vec (Suc d) 0 $ i = nth_gf2_vec d 0 $ (i - 1)"
      using nth_gf2_vec_tail by simp
    then have "\<forall> i \<in> {1..<(Suc d)}. nth_gf2_vec (Suc d) 0 $ i = zero_vec d $ (i - 1)"
      using Suc.IH by algebra
    then have "\<forall> i \<in> {1..<(Suc d)}. nth_gf2_vec (Suc d) 0 $ i = 0"
      by fastforce
    moreover have "nth_gf2_vec (Suc d) 0 $ 0 = 0"
      using nth_gf2_vec_first_entry by simp
    ultimately show ?case by auto
  qed auto
  ultimately show ?thesis by metis
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

lemma gf2_exhaust: "x \<in> {0::gf2,1}"
  using Abs_gf2_cases[of x "Abs_gf2 (Rep_gf2 x) \<in> {0,1}"] Rep_gf2_inverse[of x]
  by (metis insert_iff one_gf2_def singleton_iff zero_gf2_def)

lemma non_zero_places:
  assumes
    "v \<in> C"
    "v \<noteq> \<zero>\<^bsub>CS\<^esub>"
  shows
    "hamming_distance \<zero>\<^bsub>CS\<^esub> v \<ge> 3"
proof (rule ccontr)
  have orth_sum: "\<forall>i \<in> {0..<n}. (\<Sum>j \<in> {0..<m}. v $ j * (nth_gf2_vec n (j+1) $ i)) = 0" proof
    fix i

    have aaaa: "\<And>x::gf2. x \<in> E" by simp

    assume i_bounds: "i \<in> {0..<n}"
    then have "(\<Oplus>\<^bsub>gf2_ring\<^esub>j \<in> {0..<dim_col P}. v $ j * (col P j $ i)) = 0"
      using field.matrix_mul_idx[OF field_F, of P]
      using words_subs par_check i_bounds assms
      by fastforce
    then have "(\<Sum>j \<in> {0..<m}. v $ j * (col P j $ i)) = 0"
      using finsum_to_sum by simp
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
    have "\<zero>\<^bsub>CS\<^esub> \<in> C"
      using submodule.zero_closed[of gf2_ring C VS] submod by simp
    then have "dim_vec \<zero>\<^bsub>CS\<^esub> = m" using words_subs by blast
    then have "dim_vec \<zero>\<^bsub>CS\<^esub> = dim_vec v" using assms words_subs by auto
    then have "\<exists>i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub>$i \<noteq> v$i"
      using words_subs assms \<open>v \<noteq> \<zero>\<^bsub>CS\<^esub>\<close> by fastforce
    then have "{i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub>$ i \<noteq> v$ i} \<noteq> {}"
      by blast
    then have "hamming_distance \<zero>\<^bsub>CS\<^esub> v > 0"
      unfolding hamming_distance_def
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
      using nonfirst_vec_nonzero zero by presburger

    then show False using zero by satx
  next
    case 3
    then have "card {i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub> $ i \<noteq> v $ i} = 2"
      unfolding hamming_distance_def
      by satx
    moreover have "{i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub> $ i \<noteq> v $ i} = {i \<in> {0..<m}. v $ i \<noteq> \<zero>\<^bsub>CS\<^esub> $ i}"
      by metis
    then have "{i \<in> {0..<m}. \<zero>\<^bsub>CS\<^esub> $ i \<noteq> v $ i} = {i \<in> {0..<m}. v $ i \<noteq> 0}"
      unfolding VS zero_vec_def
      by fastforce
    ultimately have card: "card {i \<in> {0..<m}. v$i \<noteq> 0} = 2"
      by argo
    then obtain i j where ij: "v $ i \<noteq> 0" "v $ j \<noteq> 0" "i \<in> {0..<m}" "j \<in> {0..<m}" "i \<noteq> j"
      by (smt (verit) card_2_iff' mem_Collect_eq)
    then have "card ({i \<in> {0..<m}. v$i \<noteq> 0} - {i,j}) = 0"
      using card by simp
    then have other_zero: "\<And>k. k \<in> {0..<m} \<Longrightarrow> k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> v$k = 0"
      by auto


    have "\<And>l. l \<in> {0..<n} \<Longrightarrow> nth_gf2_vec n (i+1) $ l = nth_gf2_vec n (j+1) $ l" proof -
      fix l
      assume "l \<in> {0..<n}"
      then have "(\<Sum>k \<in> {0..<m}. v $ k * (nth_gf2_vec n (k+1) $ l)) = 0"
        using orth_sum by simp
      then have "(\<Sum>k \<in> {0..<m} - {i,j}. v $ k * (nth_gf2_vec n (k+1) $ l)) + (\<Sum>k \<in> {i,j}. v $ k * (nth_gf2_vec n (k+1) $ l)) = 0"
        by (metis (lifting) empty_subsetI finite_lessThan ij(3,4) insert_subset lessThan_atLeast0 sum.subset_diff)
      then have "(\<Sum>k \<in> {i,j}. v $ k * (nth_gf2_vec n (k+1) $ l)) = 0"
        using other_zero by auto
      then have "v$i * (nth_gf2_vec n (i+1) $ l) + v$j * (nth_gf2_vec n (j+1) $ l) = 0"
        using ij by auto
      moreover have "v$i = 1" "v$j = 1" using ij gf2_exhaust by auto
      ultimately have "(nth_gf2_vec n (i+1) $ l) + (nth_gf2_vec n (j+1) $ l) = 0" by simp
      then show "(nth_gf2_vec n (i+1) $ l) = (nth_gf2_vec n (j+1) $ l)" using plus_gf2_def minus_gf2_def by simp
    qed
    then have "nth_gf2_vec n (i+1) = nth_gf2_vec n (j+1)"
      using nth_gf2_vec_len
      by auto

    moreover have "i + 1 \<in> {0..<2^n}" "j + 1 \<in> {0..<2^n}" using ij by auto
    ultimately have "i + 1 = j + 1" using nth_gf2_vec_inj[of n] unfolding inj_on_def by metis
    then show False using ij by linarith
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