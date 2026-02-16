theory HammingCode
  imports GeneratingMatrix LinearCode
begin

abbreviation gf2_ring where
  "gf2_ring \<equiv> \<lparr> 
  carrier = UNIV::gf2 set,
  mult = undefined,
  one = 1::gf2,
  zero = 0::gf2,
  add = (\<lambda>x y. x + y),
  module.smult = (\<lambda>x::gf2.\<lambda>y::gf2. x * y)
\<rparr>"

term "(\<lambda>i. 0)(1 := 2)"

fun nth_gf2_vec:: "nat \<Rightarrow> nat \<Rightarrow> gf2 vec" where
  "nth_gf2_vec 0 n = vec 0 (\<lambda>i. 0)"
| "nth_gf2_vec d 0 = vec d (\<lambda>i. 0)"
| "nth_gf2_vec d n = vec d ((\<lambda>i. nth_gf2_vec (d-1) (n div 2) $ (i - 1))(0 := (if (n mod 2 = 0) then 0 else 1)))"


lemma gets_all_vecs: "nth_gf2_vec d ` {0..<2^d} = {v . dim_vec v = d}"
  sorry

lemma gets_all_nonzero_vecs: "nth_gf2_vec d ` {1..<2^d} = {v . dim_vec v = d \<and> v \<noteq> induced_vs.zero_vec gf2_ring d}"
  sorry

abbreviation hamming_parity_matrix where
  "hamming_parity_matrix d \<equiv> mat_of_cols d [nth_gf2_vec d i. i \<leftarrow> [1..<2^d]]"


locale hamming_code = linear_code gf2_ring C "2^n + 1" for n C +
  assumes
    "linear_code.parity_check_matrix gf2_ring C (2^n + 1) (hamming_parity_matrix n)"
begin

abbreviation "m \<equiv> 2^n + 1"

lemma min_dist: "minimum_distance \<ge> 3"
proof (rule ccontr)
assume "\<not> minimum_distance \<ge> 3"
  hence "minimum_distance < 3" by simp
  then consider "minimum_distance = 0" | "minimum_distance = 1" | "minimum_distance = 2"
    by linarith
  thus False
  proof cases
    case 1
    then obtain p where p_prop: "hamming_distance (fst p) (snd p) = 0" "p \<in> C \<times> C" "fst p \<noteq> snd p"
      unfolding minimum_distance_def
      using Min_in[OF distances_finite distances_nonempty]
      by auto
    then have "\<exists>i \<in> {0..<m}. (fst p)$i \<noteq> (snd p)$i"
      using words_subs words p_prop by fastforce
    then have "{i \<in> {0..<m}. (fst p)$ i \<noteq> (snd p)$ i} \<noteq> {}"
      by blast
    then have "hamming_distance (fst p) (snd p) > 0"
      unfolding hamming_distance_def word
      by fastforce
    then show "False" using 1 p_prop by linarith
  next
    case 2
    then show ?thesis sorry
  next
    case 3
    then show ?thesis sorry
  qed
qed

lemma "corrects_errors 1"
  using min_dist min_distance_ec
  by presburger

end
  

end