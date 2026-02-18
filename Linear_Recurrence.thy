theory Linear_Recurrence
  imports "Miniature_Two"

begin


(* 'x::{comm_monoid_add,times,power,minus} into 'x::{idom} *)
(* TODO why is comm_semiring_0 not automatically of sort monoid_mult? *)
locale linrec =
  fixes  
    c :: "nat \<Rightarrow> nat \<Rightarrow> 'x::{idom}" and
    f :: "nat \<Rightarrow> 'x" and 
    k :: nat
  assumes
    finite: "\<forall>m > k. c m = 0"

fun (in linrec) solution :: "(nat \<Rightarrow> 'x) \<Rightarrow> bool" where
  "solution a = (\<forall>n \<ge> k. a n = (\<Sum>i\<in>{1..k}. (c i n) * (a (n-i))) + f n)"

locale linrec_const = rec?: linrec c _ k for c :: "nat \<Rightarrow> nat \<Rightarrow> 'x::{idom}" and k +
  assumes
    order_k: "c k \<noteq> 0" and
    order_gt_0: "k > 0" and
    const: "\<forall>i\<in>{1..k}. \<exists>\<gamma>. c i = (\<lambda>n. \<gamma>)"

sublocale linrec_const \<subseteq> linrec c _ k
  by (rule local.rec.linrec_axioms)

context linrec_const
begin

fun const_c :: "nat \<Rightarrow> 'x" where
  "const_c i = (c i 1)"

function char_coeff :: "nat \<Rightarrow> 'x" where
  "i < k \<Longrightarrow> char_coeff i = - const_c (k - i)" |
  "i = k \<Longrightarrow> char_coeff i = 1" |
  "i > k \<Longrightarrow> char_coeff i = 0"
  by (simp_all, fastforce)
  termination using "termination" by blast

definition char_poly :: "'x poly" where 
  "char_poly = (Abs_poly char_coeff)"

lemma deg_eq_order:
  "degree char_poly = k"
proof (unfold degree_def char_poly_def)
  have coeff: "poly.coeff (Abs_poly char_coeff) = char_coeff"
    using coeff_Abs_poly[of k char_coeff] 
    by simp
  from coeff have "poly.coeff (Abs_poly char_coeff) k \<noteq> 0"
    by simp
  hence "\<forall>n. n < k \<longrightarrow> \<not>(\<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0)"
    by meson
  hence "\<forall>n. (\<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0) \<longrightarrow> k \<le> n"
    using linorder_not_less 
    by blast
  hence "(\<And>n. (\<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0) \<Longrightarrow> k \<le> n)"
    by blast
  moreover from coeff have "\<forall>i>k. poly.coeff (Abs_poly char_coeff) i = 0"
    by simp
  ultimately show "(LEAST n. \<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0) = k"
    using Least_equality[of "\<lambda>n. \<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0" k]
    by blast
qed

fun mult :: "nat \<Rightarrow> 'x \<Rightarrow> 'x" where
  "mult 0 a = 0" |
  "mult (Suc n) a = a + mult n a"

lemma mult_prod:
  fixes a :: 'x and n :: nat
  shows "mult n a = (mult n 1) * a"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "local.mult (Suc n) a = a + mult n a"
    by simp
  also have "... = a + (mult n 1) * a"
    using Suc
    by metis
  also have "... = (1 + mult n 1) * a"
    by (simp add: Rings.ring_distribs(2))
  also have "... = (mult (Suc n) 1) * a"
    by simp
  finally show ?case by simp
qed

function deg_n_char_coeff_derivative :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'x" where
  "n < j \<Longrightarrow> deg_n_char_coeff_derivative n i j = 0" |
  "n = j \<Longrightarrow> deg_n_char_coeff_derivative n i j = mult (n ^ i) 1" |
  "n - j \<ge> 1 \<and> n - j \<le> k \<Longrightarrow> deg_n_char_coeff_derivative n i j = - mult (j ^ i) (const_c (n - j))" |
  "n - j > k \<Longrightarrow> deg_n_char_coeff_derivative n i j = 0"
  by (simp_all, fastforce)
  termination using "termination" by blast

lemma deg_n_helper:
  fixes i :: nat and j :: nat and n :: nat
  assumes "n < i"
  shows "deg_n_char_coeff_derivative n j i = 0"
  using assms
  by (rule deg_n_char_coeff_derivative.simps(1))

fun deg_n_derivative_poly ::  "nat \<Rightarrow> nat \<Rightarrow> 'x poly" where
  "deg_n_derivative_poly n j = Abs_poly (deg_n_char_coeff_derivative n j)"

lemma deg_deg_n_char_coeff_derivative_eq_n:
  fixes n :: nat and j :: nat
  shows
    "degree (deg_n_derivative_poly n j) = n"
proof  (unfold degree_def)
  have coeff: "poly.coeff (Abs_poly char_coeff) = char_coeff"
    using coeff_Abs_poly[of k char_coeff] 
    by simp
  from coeff have "poly.coeff (Abs_poly char_coeff) k \<noteq> 0"
    by simp
  hence "\<forall>n. n < k \<longrightarrow> \<not>(\<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0)"
    by meson
  hence "\<forall>n. (\<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0) \<longrightarrow> k \<le> n"
    using linorder_not_less 
    by blast
  hence "(\<And>n. (\<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0) \<Longrightarrow> k \<le> n)"
    by blast
  moreover from coeff have "\<forall>i>k. poly.coeff (Abs_poly char_coeff) i = 0"
    by simp
  ultimately show "(LEAST n. \<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0) = k"
    using Least_equality[of "\<lambda>n. \<forall>i>n. poly.coeff (Abs_poly char_coeff) i = 0" k]
    by blast
qed


theorem fundamental_solution:
  fixes
    a :: "'x" and s :: nat and i :: nat
  assumes
    "f = (\<lambda>n. 0)" and
    "j < s" and
    (* 
      TODO we need the idom type class only for the multiplicity of polynomial roots, 
      how to avoid the assumption in the locale? 
    *)
    "order a char_poly = s"
  shows
    "solution (\<lambda>n. mult (n ^ j) (a ^ n))"
proof (simp, safe, goal_cases)
  case (1 n)
  let ?poly = "deg_n_derivative_poly n j"
  have "poly ?poly a = 0"
    sorry
  hence "0 = (\<Sum>i\<le>degree ?poly. poly.coeff ?poly i * (a ^ i))"
    using poly_altdef[of ?poly a]
    by simp
  moreover have "degree ?poly = n"
    using deg_deg_n_char_coeff_derivative_eq_n[of n j]
    by simp
  ultimately have "0 = (\<Sum>i\<le>n. poly.coeff ?poly i * (a ^ i))"
    by simp
  also have "... = (\<Sum>i\<in>{0..n}. poly.coeff ?poly i * (a ^ i))"
    using atLeast0AtMost 
    by presburger
  also have "... = (\<Sum>i\<in>{0..n}. deg_n_char_coeff_derivative n j i * (a ^ i))"
    using coeff_Abs_poly[of n "deg_n_char_coeff_derivative n j"] deg_n_helper[of n _ j]
    by simp
  also have 
    "... = deg_n_char_coeff_derivative n j n * (a ^ n) + 
      (\<Sum>i\<in>{0..n}-{n}. deg_n_char_coeff_derivative n j i * (a ^ i))"
    using sum_diff1[of "{0..n}" "\<lambda>i. deg_n_char_coeff_derivative n j i * (a ^ i)" n] 
    by simp
  also have 
    "... = (mult (n ^ j) 1) * (a ^ n) + 
      (\<Sum>i\<in>{0..n}-{n}. deg_n_char_coeff_derivative n j i * (a ^ i))"
    by simp
  also have
    "... = mult (n ^ j) (a ^ n) + 
      (\<Sum>i\<in>{0..n}-{n}. deg_n_char_coeff_derivative n j i * (a ^ i))"
    using mult_prod[of "n ^ j" "a ^ n"]
    by simp
  (* TODOOOOOOOOOOOOOOOOOOOOOOOOOO *)
  finally show
    "mult (n ^ j) (a ^ n) = (\<Sum>i\<in>{Suc 0..k}. c i n * mult ((n - i) ^ j) (a ^ (n - i))) + f n"
    sorry
qed

end

end