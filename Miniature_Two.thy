theory Miniature_Two
imports Thirty_Three_Miniatures_Root

begin

text \<open>
  This is a special case of the more general strategy to solve recurrences by

    1) viewing sequences that satisfy the recurrence as a vector space
    2) finding a simple basis of that vector space 
        (by finding the roots of the recurrence's characteristic polynomial)
    3) writing every other sequence in the vector space as a linear combination of the basis
        (by solving initial value conditions)
  
  Note that the power of this approach lies not so much in proving an already found explicit
  formula (induction should do the trick). Rather, it aids in finding an explicit formula in the
  first place.

  We directly apply this strategy to the Fibonacci recurrence following <TODO: citation>,
  but generalizing the proof strategy for reuse would be a sensible next step.
\<close>

subsection \<open>Basic Definitions\<close>

definition reals :: "real ring" where
  "reals = \<lparr> carrier = (UNIV::real set), mult = (*), one = 1, zero = 0, add = (+) \<rparr>"

subsection \<open>Fibonacci Numbers\<close>

fun fibonacci :: "nat \<Rightarrow> real" where
  "fibonacci 0 = 0" |
  "fibonacci (Suc 0) = 1" |
  "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

subsection \<open>Vector Space of Sequences\<close>

text \<open>
  Our vector space is the space of sequences satisfying the recurrence 
  \<^latex>\<open>a_n = a_{n-1} + a_{n-2}\<close> with arbitrary initial values.
\<close>

type_synonym 'a sequence = "nat \<Rightarrow> 'a"

fun fib_prop :: "real sequence \<Rightarrow> nat \<Rightarrow> bool" where
  "fib_prop f n = (f (Suc (Suc n)) = f n + f (Suc n))"

definition fib_sequences :: "real sequence set" where
  "fib_sequences = {f | f. \<forall>n. fib_prop f n}"

text \<open>Vector addition and scalar multiplication in the sequence space\<close>

fun add_sequences :: "'a::plus sequence \<Rightarrow> 'a sequence \<Rightarrow> 'a sequence" where
  "add_sequences f g = (\<lambda>n. f n + g n)"

fun scale_sequences :: "[real, real sequence] \<Rightarrow> real sequence" where
  "scale_sequences x f = (\<lambda>n. x * (f n))"

text \<open>
  The actual vector space with a carrier, vector addition and scalar multiplication put together.

  To reuse AFP entries, we are required to define vector spaces as modules. Note that modules 
  generally have a multiplication operation, which can be left undefined in a vector space.
\<close>
definition fib_space :: "(real, real sequence) module" where
  "fib_space = 
    \<lparr> carrier = fib_sequences, 
    mult = undefined, 
    one = undefined,
    zero = (\<lambda>n::nat. 0), 
    add = (\<lambda> (f::real sequence) g. (\<lambda>n. (f n) + (g n))),  
    module.smult = scale_sequences \<rparr>"

section \<open>Vector Space Interpretation\<close>

interpretation sequence_group: abelian_group fib_space
proof
  fix 
    f :: "nat \<Rightarrow> real" and g :: "nat \<Rightarrow> real"
  assume
    grp_f: "f \<in> carrier (add_monoid fib_space)" and
    grp_g: "g \<in> carrier (add_monoid fib_space)"
  show "f \<otimes>\<^bsub>add_monoid fib_space\<^esub> g \<in> carrier (add_monoid fib_space)"
  proof (unfold fib_space_def fib_sequences_def, simp, safe)
    fix
      n :: nat
      have "fib_prop f n \<and> fib_prop g n"
        using grp_f grp_g
        unfolding fib_space_def fib_sequences_def All_def
        by simp
      hence "f (Suc (Suc n)) + g (Suc (Suc n)) = f n + f (Suc n) + g n + g (Suc n)"
        using grp_f grp_g
        unfolding fib_space_def fib_sequences_def
        by simp
      also have "... = f n + g n + (f (Suc n) + g (Suc n))"
        by simp
      finally have "f (Suc (Suc n)) + g (Suc (Suc n)) = f n + g n + (f (Suc n) + g (Suc n))"
        by simp
      hence "(\<lambda>n. f n + g n) (Suc (Suc n)) = (\<lambda>n. f n + g n) n + (\<lambda>n. f n + g n) (Suc n)"
        by satx
      thus "fib_prop (\<lambda>n. f n + g n) n"
        by simp
    qed
next
  fix
     f :: "nat \<Rightarrow> real" and g :: "nat \<Rightarrow> real" and h :: "nat \<Rightarrow> real"
  show "f \<otimes>\<^bsub>add_monoid fib_space\<^esub> g \<otimes>\<^bsub>add_monoid fib_space\<^esub> h =
    f \<otimes>\<^bsub>add_monoid fib_space\<^esub> (g \<otimes>\<^bsub>add_monoid fib_space\<^esub> h)"
    unfolding fib_space_def
    by auto
next
  have "\<one>\<^bsub>add_monoid fib_space\<^esub> = (\<lambda>n. 0)" 
    unfolding fib_space_def
    by simp
  moreover have "\<forall>n::nat. (\<lambda>n. 0::real) (Suc (Suc n)) = (\<lambda>n. 0) n + (\<lambda>n. 0) (Suc n)"
    by linarith
  ultimately show "\<one>\<^bsub>add_monoid fib_space\<^esub> \<in> carrier (add_monoid fib_space)"
    unfolding fib_space_def fib_sequences_def All_def
    by auto
next
  fix
     f :: "nat \<Rightarrow> real"
  show "\<one>\<^bsub>add_monoid fib_space\<^esub> \<otimes>\<^bsub>add_monoid fib_space\<^esub> f = f"
    unfolding fib_space_def
    by simp
  show "f \<otimes>\<^bsub>add_monoid fib_space\<^esub> \<one>\<^bsub>add_monoid fib_space\<^esub> = f"
    unfolding fib_space_def
    by simp
next
  fix 
    f :: "nat \<Rightarrow> real" and g :: "nat \<Rightarrow> real"
  show "f \<otimes>\<^bsub>add_monoid fib_space\<^esub> g = g \<otimes>\<^bsub>add_monoid fib_space\<^esub> f"
    unfolding fib_space_def
    by auto
next
  show "carrier (add_monoid fib_space) \<subseteq> Units (add_monoid fib_space)"
  proof (unfold Units_def, simp, safe)
    fix 
      f :: "nat \<Rightarrow> real"
    assume 
      grp_f: "f \<in> carrier fib_space"
    let ?g = "\<lambda>n. -(f n)"
    have "\<forall>n::nat. ?g (Suc (Suc n)) = -(f (Suc (Suc n)))"
      by simp
    moreover have "\<forall>n::nat. -(f (Suc (Suc n))) = -(f n + f (Suc n))"
      using grp_f
      unfolding fib_space_def fib_sequences_def fib_prop.simps
      by simp
    moreover have "\<forall>n::nat. -(f n + f (Suc n)) = -(f n) + -(f (Suc n))"
      by simp
    moreover have "\<forall>n::nat. -(f n) + -(f (Suc n)) = ?g n + ?g (Suc n)"
      by simp
    ultimately have "\<forall>n::nat. ?g (Suc (Suc n)) = ?g n + ?g (Suc n)"
      by metis
    hence "?g \<in> carrier fib_space"
      unfolding fib_space_def fib_sequences_def  fib_prop.simps
      by simp
    moreover have "?g \<oplus>\<^bsub>fib_space\<^esub> f = \<zero>\<^bsub>fib_space\<^esub>"
      unfolding fib_space_def
      by simp
    moreover have "f \<oplus>\<^bsub>fib_space\<^esub> ?g = \<zero>\<^bsub>fib_space\<^esub>"
      unfolding fib_space_def
      by simp
    ultimately show
      "\<exists>g\<in>carrier fib_space. g \<oplus>\<^bsub>fib_space\<^esub> f = \<zero>\<^bsub>fib_space\<^esub> \<and> f \<oplus>\<^bsub>fib_space\<^esub> g = \<zero>\<^bsub>fib_space\<^esub>"
      by blast
  qed
qed
    
interpretation sequence_module: Module.module reals fib_space
proof (unfold module_def module_axioms_def, safe)
    have "field reals" 
      unfolding reals_def
      using class_field
      by metis
    thus "cring reals" 
      unfolding field_def domain_def
      by satx
  next
    show "abelian_group fib_space"
      using sequence_group.abelian_group_axioms
      by blast
  next
    fix
      \<alpha> :: real and
      f :: "nat \<Rightarrow> real"
    assume
      scalar: "\<alpha> \<in> carrier reals" and
      vector: "f \<in> carrier fib_space"
    show "\<alpha> \<odot>\<^bsub>fib_space\<^esub> f \<in> carrier fib_space"
    proof (unfold fib_space_def fib_sequences_def, simp, safe)
      fix
        n :: nat
      have "\<alpha> * f (Suc (Suc n)) = \<alpha> * (f n + f (Suc n))"
        using vector
        unfolding fib_space_def fib_sequences_def fib_prop.simps
        by simp
      also have "... = \<alpha> * (f n) + \<alpha> * (f (Suc n))"
        by argo
      finally have "\<alpha> * f (Suc (Suc n)) = \<alpha> * f n + \<alpha> * f (Suc n)"
        by simp
      thus "fib_prop (\<lambda>n. \<alpha> * f n) n"
        by simp
    qed
  next
    fix
      \<alpha> :: real and \<beta> :: real and f :: "nat \<Rightarrow> real"
    have "(\<alpha> \<oplus>\<^bsub>reals\<^esub> \<beta>) \<odot>\<^bsub>fib_space\<^esub> f = (\<lambda>n. (\<alpha> + \<beta>) * (f n))"
      unfolding reals_def fib_space_def
      by simp
    also have "... = (\<lambda>n. \<alpha> * (f n) + \<beta> * (f n))"
      by (simp add: ring_class.ring_distribs(2))
    also have "... = (\<lambda>n. \<alpha> * (f n)) \<oplus>\<^bsub>fib_space\<^esub> (\<lambda>n. \<beta> * (f n))"
      unfolding fib_space_def
      by simp
    also have "... = \<alpha> \<odot>\<^bsub>fib_space\<^esub> f \<oplus>\<^bsub>fib_space\<^esub> \<beta> \<odot>\<^bsub>fib_space\<^esub> f"
      unfolding fib_space_def
      by simp
    finally show "(\<alpha> \<oplus>\<^bsub>reals\<^esub> \<beta>) \<odot>\<^bsub>fib_space\<^esub> f = \<alpha> \<odot>\<^bsub>fib_space\<^esub> f \<oplus>\<^bsub>fib_space\<^esub> \<beta> \<odot>\<^bsub>fib_space\<^esub> f"
      by simp
  next
    fix
      \<alpha> :: real and f :: "nat \<Rightarrow> real" and g :: "nat \<Rightarrow> real"
    have "\<alpha> \<odot>\<^bsub>fib_space\<^esub> (f \<oplus>\<^bsub>fib_space\<^esub> g) = (\<lambda>n. \<alpha> * (f n + g n))"
      unfolding fib_space_def
      by simp
    also have "... = (\<lambda>n. \<alpha> * (f n) + \<alpha> * (g n))"
      by (simp add: distrib_left)
    also have "... = (\<lambda>n. \<alpha> * (f n)) \<oplus>\<^bsub>fib_space\<^esub> (\<lambda>n. \<alpha> * (g n))"
      unfolding fib_space_def
      by simp
    also have "... = \<alpha> \<odot>\<^bsub>fib_space\<^esub> f \<oplus>\<^bsub>fib_space\<^esub> \<alpha> \<odot>\<^bsub>fib_space\<^esub> g"
      unfolding fib_space_def
      by simp
    finally show 
      "\<alpha> \<odot>\<^bsub>fib_space\<^esub> (f \<oplus>\<^bsub>fib_space\<^esub> g) = \<alpha> \<odot>\<^bsub>fib_space\<^esub> f \<oplus>\<^bsub>fib_space\<^esub> \<alpha> \<odot>\<^bsub>fib_space\<^esub> g"
      by simp
  next
    fix
      \<alpha> :: real and \<beta> :: real and f :: "nat \<Rightarrow> real"
    have "\<alpha> \<otimes>\<^bsub>reals\<^esub> \<beta> \<odot>\<^bsub>fib_space\<^esub> f = (\<lambda>n. \<alpha> * \<beta> * (f n))"
      unfolding reals_def fib_space_def
      by simp
    also have "... = (\<lambda>n. \<alpha> * ((\<beta> \<odot>\<^bsub>fib_space\<^esub> f) n))"
      unfolding fib_space_def
      by auto
    also have "... = \<alpha> \<odot>\<^bsub>fib_space\<^esub> (\<beta> \<odot>\<^bsub>fib_space\<^esub> f)"
      unfolding fib_space_def
      by simp
    finally show "\<alpha> \<otimes>\<^bsub>reals\<^esub> \<beta> \<odot>\<^bsub>fib_space\<^esub> f = \<alpha> \<odot>\<^bsub>fib_space\<^esub> (\<beta> \<odot>\<^bsub>fib_space\<^esub> f)"
      by simp
  next
    fix f :: "nat \<Rightarrow> real"
    show "\<one>\<^bsub>reals\<^esub> \<odot>\<^bsub>fib_space\<^esub> f = f"
      unfolding fib_space_def reals_def
      by simp
  qed

interpretation sequence_space: vectorspace reals fib_space
proof (unfold vectorspace_def, safe)
  show field: "field reals"
    using class_field
    unfolding reals_def
    by blast
  show "Module.module reals fib_space"
    using sequence_module.module_axioms
    by blast
qed

section \<open>Vector Space Basis\<close>

thm abelian_monoid.finsum_insert

text \<open>
  Technical rewriting lemma:

  Forming the finite sum over two summands, when addition commutes, is the same as adding the two 
  summands in arbitrary order. (This can be generalized to any finite number of summands.)
\<close>
lemma (in abelian_monoid) finsum_2_elts[simp]:
  fixes
    x :: 'x and y :: 'x and f :: "'x \<Rightarrow> 'a"
  assumes
    "x \<noteq> y" and
    "f \<in> {x,y} \<rightarrow> carrier G"
  shows
    "(\<Oplus>\<^bsub>G\<^esub>v\<in>{x,y}. f v) = f x \<oplus>\<^bsub>G\<^esub> f y"
proof -
  have "{x,y} = insert y {x}"
    using assms
    by blast
  hence "(\<Oplus>\<^bsub>G\<^esub>v\<in>{x,y}. f v) = finsum G f (insert x {y})"
    by simp
  (* TODO why does "also" fail? *)
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> finsum G f {y}"
    using finsum_insert[of "{y}" x f] assms
    by simp
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> (f y \<oplus>\<^bsub>G\<^esub> finsum G f {})"
    using finsum_insert[of "{}" y f] assms
    by simp
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> (f y \<oplus>\<^bsub>G\<^esub> \<zero>\<^bsub>G\<^esub>)"
    using finsum_empty[of f]
    by metis
  moreover have "... = f x \<oplus>\<^bsub>G\<^esub> f y"
    using assms
    by simp
  ultimately show ?thesis
    by simp
qed

lemma (in abelian_monoid) finsum_eq: 
  (* TODO should hold in general but induction would fail without commutativity? *)
  fixes 
    f :: "'x \<Rightarrow> 'a" and g :: "'x \<Rightarrow> 'a" and X :: "'x set"
  assumes
    "\<forall>x \<in> X. f x = g x" and "f \<in> X \<rightarrow> carrier G" and "g \<in> X \<rightarrow> carrier G"
  shows
    "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. f v) = (\<Oplus>\<^bsub>G\<^esub>v\<in>X. g v)"
proof (cases "finite X")
  case True
  then show ?thesis
    using assms
  proof (induction "card X" arbitrary: X f g)
    case 0
    hence "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. f v) = \<one>\<^bsub>add_monoid G\<^esub>"
      unfolding finsum_def finprod_def
      using foldD_empty[of "\<one>\<^bsub>add_monoid G\<^esub>" "carrier (add_monoid G)" "(\<otimes>\<^bsub>add_monoid G\<^esub>) \<circ> f"] assms
      by simp
    moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. g v) = \<one>\<^bsub>add_monoid G\<^esub>"
      unfolding finsum_def finprod_def 
      using 0 assms foldD_empty[of "\<one>\<^bsub>add_monoid G\<^esub>" "carrier (add_monoid G)" "(\<otimes>\<^bsub>add_monoid G\<^esub>) \<circ> g"]
      by simp
    ultimately show ?case 
      by simp
  next
    case (Suc n)
    hence "X \<noteq> {}" by auto
    then obtain x :: 'x where "x \<in> X" by blast
    have func_f: "f \<in> X - {x} \<rightarrow> carrier G"
      using Suc
      unfolding Pi_def
      by simp
    have func_g: "g \<in> X - {x} \<rightarrow> carrier G"
      using Suc
      unfolding Pi_def
      by simp
    have elt_f: "f x \<in> carrier G"
      using Suc \<open>x \<in> X\<close>
      unfolding Pi_def
      by simp
    have elt_g: "g x \<in> carrier G"
      using Suc \<open>x \<in> X\<close>
      unfolding Pi_def
      by simp
    from \<open>x \<in> X\<close> have "card (X - {x}) = n"
      using Suc
      by simp
    moreover have fin: "finite (X - {x})" using Suc by simp
    ultimately have "(\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). f v) = (\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). g v)" 
      using Suc
      by blast
    moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). f v) = f x \<oplus>\<^bsub>G\<^esub> (\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). f v)"
      using finsum_insert[of "X - {x}" x f, OF fin _ func_f elt_f]
      by simp
    moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). g v) = g x \<oplus>\<^bsub>G\<^esub> (\<Oplus>\<^bsub>G\<^esub>v\<in>(X - {x}). g v)"
      using finsum_insert[of "X - {x}" x g, OF fin _ func_g elt_g]
      by simp
    moreover have "f x = g x"
      using \<open>x \<in> X\<close> Suc
      by blast
    ultimately have "(\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). f v) = (\<Oplus>\<^bsub>G\<^esub>v\<in>insert x (X - {x}). g v)"
      by simp
    moreover have "insert x (X - {x}) = X"
      using \<open>x \<in> X\<close>
      by blast
    ultimately show ?case by simp
  qed
next
  case False
  hence "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. f v) = \<one>\<^bsub>add_monoid G\<^esub>"
    unfolding finsum_def finprod_def
    by simp
  moreover have "(\<Oplus>\<^bsub>G\<^esub>v\<in>X. g v) = \<one>\<^bsub>add_monoid G\<^esub>"
    using False
    unfolding finsum_def finprod_def
    by simp
  ultimately show ?thesis
    by simp
qed

subsection \<open>"Standard" Basis of the Fibonacci Sequence Space\<close>

text\<open>
  We use as standard basis of the Fibonacci sequence vector space the sequences with initial
  values 0 and 1 resp. 1 and 0. For these, it is uncomplicated to show that they form a basis.

  Hence, the dimension of the Fibonacci sequence vector space over the field of reals has 
  dimension 2. Using that, it follows that every other linearly independent set of Fibonacci 
  sequences with cardinality 2 is also a basis.
\<close>

fun seq_10 :: "nat \<Rightarrow> real" where
  "seq_10 0 = 1" |
  "seq_10 (Suc 0) = 0" |
  "seq_10 (Suc (Suc n)) = seq_10 n + seq_10 (Suc n)"

fun seq_01 :: "nat \<Rightarrow> real" where
  "seq_01 0 = 0" |
  "seq_01 (Suc 0) = 1" |
  "seq_01 (Suc (Suc n)) = seq_01 n + seq_01 (Suc n)"

lemma seq_01_10_is_fib_sequence:
  shows
    seq_10: "seq_10 \<in> fib_sequences" and
    seq_01: "seq_01 \<in> fib_sequences" and
    neq: "seq_10 \<noteq> seq_01"
proof (unfold fib_sequences_def All_def, simp_all, goal_cases)
  case 1
  show ?case
    by auto
next
  case 2
  show ?case
    by auto
next
  case 3
  have "seq_10 0 \<noteq> seq_01 0"
    by simp
  thus ?case
    by metis
qed

text \<open>
  An arbitrary Fibonacci sequence f can be written as 
  \<^latex>\<open>f(0) \cdot seq_{10} + f(1) \cdot seq_{01}\<close>.
\<close>
lemma seq_01_10_is_gen_set:
  fixes
    n :: nat and f :: "nat \<Rightarrow> real"
  assumes
    "f \<in> fib_sequences"
  shows
    "f n = f 0 * seq_10 n + f 1 * seq_01 n"
proof (induction n rule: nat_less_induct)
  fix n :: nat
  assume hyp: "\<forall>m < n. f m = f 0 * seq_10 m + f 1 * seq_01 m"
  show "f n = f 0 * seq_10 n + f 1 * seq_01 n"
  proof (cases "n = 0 \<or> n = Suc 0")
    case True
    have "f 0 = f 0 * seq_10 0 + f 1 * seq_01 0"
      by simp
    moreover have "f 1 = f 0 * seq_10 1 + f 1 * seq_01 1"
      by simp
    ultimately show ?thesis 
      using True
      by auto
  next
    case False
    hence "\<exists> m :: nat. n = Suc (Suc m)"
      by presburger
    then obtain m :: nat where "n = Suc (Suc m)" and "m < n" and "Suc m < n"
      by auto
    hence "f n = f (Suc (Suc m))"
      by simp
    also have "... = f m + f (Suc m)"
      using assms
      unfolding fib_sequences_def fib_prop.simps
      by simp
    also have 
      "... = (f 0 * seq_10 m + f 1 * seq_01 m) + (f 0 * seq_10 (Suc m) + f 1 * seq_01 (Suc m))"
      using hyp \<open>m < n\<close> \<open>Suc m < n\<close>
      by presburger
    also have 
      "... = f 0 * (seq_10 m + seq_10 (Suc m)) + f 1 * (seq_01 m + seq_01 (Suc m))"
      by argo
    also have "... = f 0 * (seq_10 (Suc (Suc m))) + f 1 * (seq_01 (Suc (Suc m)))"
      using seq_01_10_is_fib_sequence
      by simp
    finally show ?thesis
      using \<open>n = Suc (Suc m)\<close>
      by simp
  qed
qed

lemma fib_standard_basis_is_lin_indpt: "True" by simp

lemma fib_standard_basis: "sequence_space.basis {seq_10, seq_01}"
proof -
  (* Linear Independence *)
  have subset: "{seq_10, seq_01} \<subseteq> carrier fib_space"
    unfolding fib_space_def
    using seq_01_10_is_fib_sequence
    by simp
  {
    assume "sequence_module.lin_dep {seq_10, seq_01}"
    moreover have "finite {seq_10, seq_01}"
      by blast
    ultimately have "\<exists>\<mu> f. 
      \<mu> \<in> {seq_10, seq_01} \<rightarrow> carrier reals \<and> 
      sequence_module.lincomb \<mu> {seq_10, seq_01} = \<zero>\<^bsub>fib_space\<^esub> \<and> 
      f \<in> {seq_10, seq_01} \<and> \<mu> f \<noteq> \<zero>\<^bsub>reals\<^esub>"
      using sequence_module.finite_lin_dep[of "{seq_10, seq_01}"] subset
      by blast
    then obtain \<mu> :: "(nat \<Rightarrow> real) \<Rightarrow> real" and f :: "nat \<Rightarrow> real" where
      zero: "sequence_module.lincomb \<mu> {seq_10, seq_01} = \<zero>\<^bsub>fib_space\<^esub>" and
      elt: "f \<in> {seq_10, seq_01}" and nontriv: "\<mu> f \<noteq> \<zero>\<^bsub>reals\<^esub>"
      by blast
    let ?mu = "\<lambda>f. \<mu> f \<odot>\<^bsub>fib_space\<^esub> f"
    have eq: "\<forall>f \<in> {seq_10, seq_01}. ?mu f = \<mu> f \<odot>\<^bsub>fib_space\<^esub> f"
      by simp
    moreover have "\<forall>f \<in> {seq_10, seq_01}. \<mu> f \<in> carrier reals"
      unfolding reals_def
      by simp
    ultimately have "\<forall>f \<in> {seq_10, seq_01}. ?mu f \<in> carrier fib_space"
      using sequence_space.vectorspace_axioms subset
      unfolding vectorspace_def module_def module_axioms_def
      by simp
    hence func: "?mu \<in> {seq_10, seq_01} \<rightarrow> carrier fib_space"
      unfolding Pi_def
      by simp
    from zero have "\<zero>\<^bsub>fib_space\<^esub> = (\<Oplus>\<^bsub>fib_space\<^esub>f\<in>{seq_10, seq_01}. \<mu> f \<odot>\<^bsub>fib_space\<^esub> f)"
      unfolding sequence_module.lincomb_def
      by simp
    moreover have "... = (\<Oplus>\<^bsub>fib_space\<^esub>f\<in>{seq_10, seq_01}. ?mu f)"
      using abelian_monoid.finsum_eq[
              of fib_space "{seq_10, seq_01}" _ _, 
              OF sequence_group.abelian_monoid_axioms _ func] func
      by meson
    moreover have "... = \<mu> seq_10 \<odot>\<^bsub>fib_space\<^esub> seq_10 \<oplus>\<^bsub>fib_space\<^esub> \<mu> seq_01 \<odot>\<^bsub>fib_space\<^esub> seq_01"
      using abelian_monoid.finsum_2_elts[
          of fib_space seq_10 seq_01 ?mu, 
          OF sequence_group.abelian_monoid_axioms seq_01_10_is_fib_sequence(3) func]
      by simp
    moreover have "... = (\<lambda>n. \<mu> seq_10 * seq_10 n + \<mu> seq_01 * seq_01 n)"
      unfolding fib_space_def
      by simp
    ultimately have const_0: "(\<lambda>n. 0) = (\<lambda>n. \<mu> seq_10 * seq_10 n + \<mu> seq_01 * seq_01 n)"
      unfolding fib_space_def
      by simp
    hence "0 = (\<lambda>n. \<mu> seq_10 * seq_10 n + \<mu> seq_01 * seq_01 n) 0"
      by meson
    hence fst_0: "0 = \<mu> seq_10"
      by simp
    have "0 = (\<lambda>n. \<mu> seq_10 * seq_10 n + \<mu> seq_01 * seq_01 n) 1"
      using const_0
      by meson
    hence snd_0: "0 = \<mu> seq_01"
      by simp
    moreover have "\<mu> f \<in> {\<mu> seq_10, \<mu> seq_01}"
      using elt
      by blast
    ultimately have "False"
      using fst_0 \<open>\<mu> f \<noteq> \<zero>\<^bsub>reals\<^esub>\<close>
      unfolding reals_def
      by simp
  }
  hence lind: "sequence_module.lin_indpt {seq_10, seq_01}"
    by satx

  (* Generating Set *)
  let ?phi = 
    "\<lambda>f. (\<lambda>g. if g = seq_01 then f 1 else f 0)"
  let ?phi' = 
    "\<lambda>f. (\<lambda>g. if g = seq_01 then f 1 \<odot>\<^bsub>fib_space\<^esub> g else f 0 \<odot>\<^bsub>fib_space\<^esub> g)"
  have "\<forall>f. \<forall>g. ?phi f g \<in> carrier reals"
    unfolding reals_def
    by simp
  hence 
    "\<forall>f. \<forall>g \<in> carrier fib_space. (\<lambda>g. ?phi f g \<odot>\<^bsub>fib_space\<^esub> g) g \<in> carrier fib_space" 
    by blast
  hence func_phi: 
    "\<forall>f. \<forall>g \<in> {seq_10, seq_01}. 
      (\<lambda>g. ?phi f g \<odot>\<^bsub>fib_space\<^esub> g) \<in> {seq_10, seq_01} \<rightarrow> carrier fib_space" 
    unfolding Pi_def
    using subset
    by blast
  moreover have func_eq: 
    "\<forall>f. \<forall>g \<in> {seq_10, seq_01}. ?phi' f g = (\<lambda>g. ?phi f g \<odot>\<^bsub>fib_space\<^esub> g) g"
    by simp
  ultimately have func_phi': 
    "\<forall>f \<in> carrier fib_space. ?phi' f \<in> {seq_10, seq_01} \<rightarrow> carrier fib_space"
    by auto
  have "\<forall>f \<in> carrier fib_space. f = f 0 \<odot>\<^bsub>fib_space\<^esub> seq_10 \<oplus>\<^bsub>fib_space\<^esub> f 1 \<odot>\<^bsub>fib_space\<^esub> seq_01"
    using seq_01_10_is_gen_set
    unfolding fib_space_def
    by simp
  hence "\<forall>f \<in> carrier fib_space. f = 
    (?phi f seq_10) \<odot>\<^bsub>fib_space\<^esub> seq_10 \<oplus>\<^bsub>fib_space\<^esub> (?phi f seq_01) \<odot>\<^bsub>fib_space\<^esub> seq_01"
    using seq_01_10_is_fib_sequence(3)
    by simp
  moreover have 
    "\<forall>f \<in> carrier fib_space.
      (?phi f seq_10) \<odot>\<^bsub>fib_space\<^esub> seq_10 \<oplus>\<^bsub>fib_space\<^esub> (?phi f seq_01) \<odot>\<^bsub>fib_space\<^esub> seq_01
      = (\<Oplus>\<^bsub>fib_space\<^esub>v\<in>{seq_10, seq_01}. ?phi' f v)"
    using func_phi' abelian_monoid.finsum_2_elts[
                of fib_space seq_10 seq_01, 
                OF sequence_group.abelian_monoid_axioms seq_01_10_is_fib_sequence(3)]
    by simp
  moreover have 
    "\<forall>f \<in> carrier fib_space. (\<Oplus>\<^bsub>fib_space\<^esub>g\<in>{seq_10, seq_01}. ?phi' f g)
      = (\<Oplus>\<^bsub>fib_space\<^esub>g\<in>{seq_10, seq_01}. (\<lambda>v. ?phi f v \<odot>\<^bsub>fib_space\<^esub> v) g)"
  proof (safe, goal_cases)
    case (1 f)
    hence
      "(\<lambda>g. ?phi f g \<odot>\<^bsub>fib_space\<^esub> g) \<in> {seq_10, seq_01} \<rightarrow> carrier fib_space"
      using sequence_module.module_axioms seq_01_10_is_fib_sequence func_phi func_phi'
      unfolding module_def module_axioms_def
      by simp
    moreover have "?phi' f \<in> {seq_10, seq_01} \<rightarrow> carrier fib_space"
      using func_phi' 1
      by simp
    ultimately show ?case
      using func_eq 
            abelian_monoid.finsum_eq[
              of fib_space "{seq_10, seq_01}" "?phi' f" "(\<lambda>g. ?phi f g \<odot>\<^bsub>fib_space\<^esub> g)",
              OF sequence_group.abelian_monoid_axioms]
      by simp
  qed
  ultimately have
    "\<forall>f \<in> carrier fib_space. f = sequence_module.lincomb (?phi f) {seq_10, seq_01}"
    unfolding sequence_module.lincomb_def
    by simp
  moreover have "\<forall>f \<in> carrier fib_space. ?phi f \<in> {seq_10, seq_01} \<rightarrow> carrier reals"
    unfolding Pi_def reals_def
    by simp
  ultimately have "\<forall>f \<in> carrier fib_space. f \<in> sequence_module.span {seq_10, seq_01}"
    unfolding sequence_module.span_def
    by blast
  hence "carrier fib_space \<subseteq> sequence_module.span {seq_10, seq_01}"
    by auto
  moreover have "sequence_module.span {seq_10, seq_01} \<subseteq> carrier fib_space"
    using seq_01_10_is_fib_sequence(1,2) sequence_space.vectorspace_axioms 
          sequence_module.span_is_submodule[of "{seq_10, seq_01}", OF subset]
          LinearCombinations.submodule_def
    by meson

  (* Basis *)
  ultimately have "sequence_module.gen_set {seq_10, seq_01}"
    by simp
  moreover have "{seq_10, seq_01} \<subseteq> carrier fib_space"
    unfolding fib_space_def
    using seq_01_10_is_fib_sequence
    by simp
  ultimately show ?thesis
    unfolding sequence_space.basis_def
    using lind
    by blast
qed

theorem fib_dimension: 
  shows
    fin_dim: "sequence_space.fin_dim" and
    dim_2: "sequence_space.dim = 2"
proof -
  have "finite {seq_10, seq_01}"
    by simp
  moreover have "{seq_10, seq_01} \<subseteq> carrier fib_space"
    using fib_standard_basis
    unfolding sequence_space.basis_def
    by satx
  moreover have "sequence_module.gen_set {seq_10, seq_01}"
    using fib_standard_basis
    unfolding sequence_space.basis_def
    by satx
  ultimately show "sequence_space.fin_dim"
    unfolding sequence_space.fin_dim_def
    by blast
next
  have "seq_10 0 \<noteq> seq_01 0"
    by simp
  hence "seq_10 \<noteq> seq_01"
    by metis
  hence "card {seq_10, seq_01} = 2"
    by simp
  moreover have "finite {seq_10, seq_01}"
    by simp
  ultimately show "sequence_space.dim = 2"
    using fib_standard_basis sequence_space.dim_basis
    by metis
qed

subsection \<open>Basis using Roots of the Characteristic Polynomial\<close>

text \<open>
  The roots of the characteristic polynomial of the Fibonacci recurrence are
  \<^latex>\<open>\frac{1 \pm \sqrt{5}}{2}\<close>. Those are linearly independent and thus form a basis of the
  Fibonacci sequence space. The benefit of choosing these sequences is that it is easy to solve 
  them explicitly: The nth element is just ^latex>\<open>(\frac{1 \pm \sqrt{5}}{2})^n\<close>. 
  Thus, expressing any other Fibonacci sequence as a linear combination of this alternative basis
  immediately yields an explicit formula for its elements.
\<close>

definition \<tau>1 :: "nat \<Rightarrow> real" where
  "\<tau>1 n = ((1 + sqrt 5)/2)^n"

definition \<tau>2 :: "nat \<Rightarrow> real" where
  "\<tau>2 n = ((1 - sqrt 5)/2)^n"

lemma tau_simp[simp]:
  shows
    tau1: "((1 + sqrt 5)/2)^2 = ((1 + sqrt 5)/2) + 1" and
    tau2: "((1 - sqrt 5)/2)^2 = ((1 - sqrt 5)/2) + 1" and
    tnt: "\<tau>1 \<noteq> \<tau>2"
proof -
  have "((1 + sqrt 5)/2)^2 = ((1 + sqrt 5)/2) * ((1 + sqrt 5)/2)"
    by (rule power2_eq_square)
  also have "... = ((1 + sqrt 5) * (1 + sqrt 5)/(2 * 2))"
    by linarith
  also have "... = (1 * 1 + 1 * sqrt 5 + sqrt 5 * 1 + sqrt 5 * sqrt 5)/4"
    by argo
  also have "... = (1 + 2 * sqrt 5 + 5)/4"
    by simp
  also have "... = (1 + sqrt 5)/4 + (5 + sqrt 5)/4"
    by argo
  also have "... = (1 + sqrt 5)/4 + (1 + sqrt 5)/4 + 4/4"
    by argo
  also have "... = (1 + sqrt 5)/2 + 1"
    by linarith
  finally show "((1 + sqrt 5) / 2)\<^sup>2 = (1 + sqrt 5) / 2 + 1"
    by simp
next
 have "((1 - sqrt 5)/2)^2 = ((1 - sqrt 5)/2) * ((1 - sqrt 5)/2)"
    by (rule power2_eq_square)
  also have "... = ((1 - sqrt 5) * (1 - sqrt 5)/(2 * 2))"
    by linarith
  also have "... = (1 * 1 - 1 * sqrt 5 - sqrt 5 * 1 + sqrt 5 * sqrt 5)/4"
    by argo
  also have "... = (1 - 2 * sqrt 5 + 5)/4"
    by simp
  also have "... = (1 - sqrt 5)/4 + (5 - sqrt 5)/4"
    by argo
  also have "... = (1 - sqrt 5)/4 + (1 - sqrt 5)/4 + 4/4"
    by argo
  also have "... = (1 - sqrt 5)/2 + 1"
    by linarith
  finally show "((1 - sqrt 5) / 2)\<^sup>2 = (1 - sqrt 5) / 2 + 1"
    by simp
next
  have "\<tau>1 1 \<noteq> \<tau>2 1"
    unfolding \<tau>1_def \<tau>2_def
    by simp
  thus "\<tau>1 \<noteq> \<tau>2"
    by metis
qed

lemma tau_is_fib_sequence:
  shows (* Without the "shows", referencing the lemma only references the first goal? *)
    "\<tau>1 \<in> fib_sequences" and
    "\<tau>2 \<in> fib_sequences"
proof (unfold fib_sequences_def, simp_all, safe)
  fix n :: nat
  have "\<tau>1 (Suc (Suc n)) = ((1 + sqrt 5)/2)^(Suc (Suc n))"
    unfolding \<tau>1_def
    by simp
  also have "... = ((1 + sqrt 5)/2)^n * ((1 + sqrt 5)/2)^2"
    by (metis add_2_eq_Suc' power_add)
  also have "... = ((1 + sqrt 5)/2)^n * ((1 + sqrt 5)/2 + 1)"
    by simp
  also have "... = ((1 + sqrt 5)/2)^n + ((1 + sqrt 5)/2)^n * ((1 + sqrt 5)/2)"
    by argo
  also have "... = \<tau>1 n + ((1 + sqrt 5)/2)^(Suc n)"
    using \<tau>1_def
    by simp
  also have "... = \<tau>1 n + \<tau>1 (Suc n)"
    using \<tau>1_def
    by simp
  finally have "\<tau>1 (Suc (Suc n)) = \<tau>1 n + \<tau>1 (Suc n)"
    by simp
  thus "fib_prop \<tau>1 n"
    by simp
next
  fix n :: nat
  have "\<tau>2 (Suc (Suc n)) = ((1 - sqrt 5)/2)^(Suc (Suc n))"
    unfolding \<tau>2_def
    by simp
  also have "... = ((1 - sqrt 5)/2)^n * ((1 - sqrt 5)/2)^2"
    by (metis add_2_eq_Suc' power_add)
  also have "... = ((1 - sqrt 5)/2)^n * ((1 - sqrt 5)/2 + 1)"
    by simp
  also have "... = ((1 - sqrt 5)/2)^n + ((1 - sqrt 5)/2)^n * ((1 - sqrt 5)/2)"
    by argo
  also have "... = \<tau>2 n + ((1 - sqrt 5)/2)^(Suc n)"
    using \<tau>2_def
    by simp
  also have "... = \<tau>2 n + \<tau>2 (Suc n)"
    using \<tau>2_def
    by simp
  finally have "\<tau>2 (Suc (Suc n)) = \<tau>2 n + \<tau>2 (Suc n)"
    by simp
  thus "fib_prop \<tau>2 n"
    by simp
qed

lemma tau_is_basis: "sequence_space.basis {\<tau>1, \<tau>2}"
proof -
  {
    assume "sequence_module.lin_dep {\<tau>1, \<tau>2}"
    hence
      "\<exists>\<mu> f. \<mu> \<in> ({\<tau>1, \<tau>2} \<rightarrow> carrier reals) 
        \<and> sequence_module.lincomb \<mu> {\<tau>1, \<tau>2} = \<zero>\<^bsub>fib_space\<^esub> 
        \<and> f \<in> {\<tau>1, \<tau>2} \<and> \<mu> f \<noteq> \<zero>\<^bsub>reals\<^esub>"
      using sequence_module.finite_lin_dep[of "{\<tau>1, \<tau>2}"] tau_is_fib_sequence
      unfolding fib_space_def
      by simp
    then obtain \<mu> :: "(nat \<Rightarrow> real) \<Rightarrow> real" and f :: "nat \<Rightarrow> real" where
      "f \<in> {\<tau>1, \<tau>2}" and "\<mu> f \<noteq> \<zero>\<^bsub>reals\<^esub>" and
      lincomb: "sequence_module.lincomb \<mu> {\<tau>1, \<tau>2} = \<zero>\<^bsub>fib_space\<^esub>"
      by blast
    let ?mu = "\<lambda>f. (\<mu> f) \<odot>\<^bsub>fib_space\<^esub> f"
    have "\<forall>f \<in> carrier fib_space. ?mu f \<in> carrier fib_space"
      using sequence_space.vectorspace_axioms
      unfolding fib_space_def vectorspace_def module_def module_axioms_def
      by (simp add: reals_def)
    hence "?mu \<in> {\<tau>1, \<tau>2} \<rightarrow> carrier fib_space"
      using tau_is_fib_sequence
      unfolding fib_space_def
      by simp
    hence "sequence_module.lincomb \<mu> {\<tau>1, \<tau>2} 
      = \<mu> \<tau>1 \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> \<mu> \<tau>2 \<odot>\<^bsub>fib_space\<^esub> \<tau>2"
      unfolding sequence_module.lincomb_def 
      using abelian_monoid.finsum_2_elts[
              of fib_space \<tau>1 \<tau>2 ?mu, OF sequence_group.abelian_monoid_axioms] 
            tnt sequence_group.abelian_monoid_axioms
      by satx
    hence "\<zero>\<^bsub>fib_space\<^esub> = (\<mu> \<tau>1) \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> (\<mu> \<tau>2) \<odot>\<^bsub>fib_space\<^esub> \<tau>2"
      using lincomb
      by simp
    also have "... = (\<lambda>n. (\<mu> \<tau>1) * (\<tau>1 n) + (\<mu> \<tau>2) * (\<tau>2 n))"
      unfolding fib_space_def
      by simp
    finally have "\<zero>\<^bsub>fib_space\<^esub> = (\<lambda>n. (\<mu> \<tau>1) * (\<tau>1 n) + (\<mu> \<tau>2) * (\<tau>2 n))"
      by simp
    hence "\<forall>n :: nat. \<zero>\<^bsub>fib_space\<^esub> n = (\<mu> \<tau>1) * (\<tau>1 n) + (\<mu> \<tau>2) * (\<tau>2 n)"
      by simp
    hence all_0: "\<forall>n :: nat. 0 = (\<mu> \<tau>1) * (\<tau>1 n) + (\<mu> \<tau>2) * (\<tau>2 n)"
      unfolding fib_space_def
      by simp
    hence "0 = (\<mu> \<tau>1) * (\<tau>1 0) + (\<mu> \<tau>2) * (\<tau>2 0)"
      by simp
    also have "... = (\<mu> \<tau>1) + (\<mu> \<tau>2)"
      unfolding \<tau>1_def \<tau>2_def
      by simp
    finally have lgs_0: "\<mu> \<tau>2 = - (\<mu> \<tau>1)"
      by simp
    hence "0 = (\<mu> \<tau>1) * (\<tau>1 1) - (\<mu> \<tau>1) * (\<tau>2 1)"
      using all_0
      by auto
    hence "0 = (\<mu> \<tau>1) * (((1 + sqrt 5)/2) - ((1 - sqrt 5)/2))"
      unfolding \<tau>1_def \<tau>2_def
      by simp
    moreover have "(((1 + sqrt 5)/2) - ((1 - sqrt 5)/2)) \<noteq> 0"
      by simp
    ultimately have "\<mu> \<tau>1 = 0"
      by simp
    moreover with this have "\<mu> \<tau>2 = 0"
      using lgs_0
      by simp
    ultimately have "\<mu> f = 0"
      using \<open>f \<in> {\<tau>1, \<tau>2}\<close>
      by auto
    hence "False"
      using \<open>\<mu> f \<noteq> \<zero>\<^bsub>reals\<^esub>\<close>
      unfolding reals_def
      by simp
  }
  hence lin_indep: "sequence_module.lin_indpt {\<tau>1, \<tau>2}"
    by satx
  moreover have "sequence_space.dim \<le> card {\<tau>1, \<tau>2}"
    using tnt fib_dimension
    by simp
  moreover have "finite {\<tau>1, \<tau>2}"
    by simp
  moreover have "sequence_space.fin_dim"
    using fib_dimension
    by satx
  ultimately show ?thesis
    using sequence_space.dim_li_is_basis[of "{\<tau>1, \<tau>2}"] tau_is_fib_sequence
    unfolding fib_space_def
    by simp
qed

section \<open>Coordinates of the Fibonacci Sequence\<close>

lemma fib_is_fib_sequence: "fibonacci \<in> fib_sequences"
  unfolding fib_sequences_def fib_prop.simps
  by simp

text \<open>
  To find an explicit formula for the Fibonacci numbers, we write it as a linear combination
  of the basis \<^latex>\<open>(\<tau>_1, \<tau>_2)\<close>. To find the scalar factors, we solve initial value conditions.
\<close>
lemma fib_coordinates:           
  "fibonacci = ((1/(sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>1) \<oplus>\<^bsub>fib_space\<^esub> (-(1/(sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>2)"
proof (unfold fib_space_def, simp)
  have fibs: "{\<tau>1, \<tau>2} \<subseteq> carrier fib_space"
    unfolding fib_space_def
    using tau_is_fib_sequence
    by simp
  moreover have "fibonacci \<in> carrier fib_space"
    unfolding fib_space_def
    using fib_is_fib_sequence
    by simp
  ultimately have 
    "\<exists>!\<mu>. \<mu> \<in> {\<tau>1, \<tau>2} \<rightarrow>\<^sub>E carrier reals \<and> sequence_module.lincomb \<mu> {\<tau>1, \<tau>2} = fibonacci"
    using tau_is_basis sequence_space.basis_criterion[of "{\<tau>1, \<tau>2}"]
    by simp
  then obtain \<mu> :: "(nat \<Rightarrow> real) \<Rightarrow> real" where 
    ext: "\<mu> \<in> {\<tau>1, \<tau>2} \<rightarrow>\<^sub>E carrier reals" and
    comb: "sequence_module.lincomb \<mu> {\<tau>1, \<tau>2} = fibonacci"
    unfolding reals_def
    by blast
  hence "fibonacci = (\<Oplus>\<^bsub>fib_space\<^esub>v\<in>{\<tau>1, \<tau>2}. \<mu> v \<odot>\<^bsub>fib_space\<^esub> v)"
    unfolding sequence_module.lincomb_def[of \<mu> "{\<tau>1, \<tau>2}"]
    by simp
  also have 
    "... = (\<mu> \<tau>1) \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> (\<mu> \<tau>2) \<odot>\<^bsub>fib_space\<^esub> \<tau>2" 
    using abelian_monoid.finsum_2_elts[
            of fib_space \<tau>1 \<tau>2 "\<lambda>f. (\<mu> f) \<odot>\<^bsub>fib_space\<^esub> f",
            OF sequence_group.abelian_monoid_axioms] tau_simp ext fibs
    unfolding extensional_funcset_def
    by simp
  finally have fib_lin_comb:
    "fibonacci = (\<mu> \<tau>1) \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> (\<mu> \<tau>2) \<odot>\<^bsub>fib_space\<^esub> \<tau>2"
    by simp
  hence "fibonacci 0 = ((\<mu> \<tau>1) \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> (\<mu> \<tau>2) \<odot>\<^bsub>fib_space\<^esub> \<tau>2) 0"
    by simp
  hence "0 = (\<mu> \<tau>1) * (\<tau>1 0) + (\<mu> \<tau>2) * (\<tau>2 0)"
    unfolding fib_space_def
    by simp
  hence "0 = (\<mu> \<tau>1) + (\<mu> \<tau>2)"
    unfolding \<tau>1_def \<tau>2_def
    by simp
  hence lgs_0: "(\<mu> \<tau>2) = -(\<mu> \<tau>1)"
    by simp
  have "fibonacci 1 = ((\<mu> \<tau>1) \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> (\<mu> \<tau>2) \<odot>\<^bsub>fib_space\<^esub> \<tau>2) 1"
    using fib_lin_comb
    by simp
  hence "1 = (\<mu> \<tau>1) * (\<tau>1 1) + (\<mu> \<tau>2) * (\<tau>2 1)"
    unfolding fib_space_def
    by simp
  hence "1 = (\<mu> \<tau>1) * ((1 + sqrt 5)/2) + (\<mu> \<tau>2) * ((1 - sqrt 5)/2)"
    unfolding \<tau>1_def \<tau>2_def
    by simp
  hence "1 = (\<mu> \<tau>1) * ((1 + sqrt 5)/2) - (\<mu> \<tau>1) * ((1 - sqrt 5)/2)"
    using lgs_0
    by simp
  hence "1 = (\<mu> \<tau>1) * (sqrt 5)"
    by argo
  hence "1 / (sqrt 5) = \<mu> \<tau>1"
    by (metis mult_eq_0_iff nonzero_mult_div_cancel_right numeral_One zero_neq_numeral)
  moreover with this have "\<mu> \<tau>2 = - 1 / (sqrt 5)"
    using lgs_0
    by linarith
  ultimately have 
    "fibonacci = (1 / (sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>1 \<oplus>\<^bsub>fib_space\<^esub> (- 1 / (sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>2"
    using fib_lin_comb
    by simp
  also have "... = (\<lambda>n. (1 / (sqrt 5)) * (\<tau>1 n)) \<oplus>\<^bsub>fib_space\<^esub> (\<lambda>n. (- 1 / (sqrt 5)) * (\<tau>2 n))"
    unfolding fib_space_def
    by simp
  also have "... = (\<lambda>n. (1 / (sqrt 5)) * (\<tau>1 n) + (- 1 / (sqrt 5)) * (\<tau>2 n))"
    unfolding fib_space_def
    by simp
  finally show "fibonacci = (\<lambda>n. \<tau>1 n / sqrt 5 - \<tau>2 n / sqrt 5)"
    by simp
qed

text \<open>
  An explicit formula for the Fibonacci sequence follows from the coordinates w.r.t the basis
  \<^latex>\<open>(\<tau>_1, \<tau>_2)\<close>. Instead of inductively proving the explicit formula, we just rewrite the
  linear combination of the basis vectors.
\<close>
theorem fib_explicit:
  fixes n :: nat
  shows
    "fibonacci n = (1/(sqrt 5)) * (((1 + sqrt 5)/2)^n - ((1 - sqrt 5)/2)^n)"
proof -
  have 
    "fibonacci n = (((1/(sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>1) \<oplus>\<^bsub>fib_space\<^esub> (-(1/(sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>2)) n"
    using fib_coordinates
    by simp
  also have "... = (((1/(sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>1) n) + ((-(1/(sqrt 5)) \<odot>\<^bsub>fib_space\<^esub> \<tau>2) n)"
    unfolding fib_space_def
    by simp
  also have "... = (1/(sqrt 5)) * (\<tau>1 n) + (-(1/(sqrt 5))) * (\<tau>2 n)"
    unfolding fib_space_def
    by simp
  also have "... = (1/(sqrt 5)) * (\<tau>1 n - \<tau>2 n)"
    by argo
  also have "... = (1/(sqrt 5)) * (((1 + sqrt 5)/2)^n - ((1 - sqrt 5)/2)^n)"
    unfolding \<tau>1_def \<tau>2_def
    by presburger
  finally show ?thesis
    by simp
qed

end