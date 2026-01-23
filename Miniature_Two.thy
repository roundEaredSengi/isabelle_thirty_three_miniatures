theory Miniature_Two
imports Thirty_Three_Miniatures_Root

begin

subsection \<open>Basic Definitions\<close>

definition reals :: "real ring" where
  "reals = \<lparr> carrier = (UNIV::real set), mult = (*), one = 1, zero = 0, add = (+) \<rparr>"

subsection \<open>Fibonacci Numbers\<close>

fun fibonacci :: "nat \<Rightarrow> nat" where
  "fibonacci 0 = 0" |
  "fibonacci (Suc 0) = 1" |
  "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

subsection \<open>Vector Space of Sequences\<close>

type_synonym 'a sequence = "nat \<Rightarrow> 'a"

definition fib_sequences :: "real sequence set" where
  "fib_sequences = {f | f :: real sequence. (\<forall>n. f (Suc (Suc n)) = f n + f (Suc n))}"

fun add_sequences :: "'a::plus sequence \<Rightarrow> 'a sequence \<Rightarrow> 'a sequence" where
  "add_sequences f g = (\<lambda>n. f n + g n)"

fun scale_sequences :: "[real, real sequence] \<Rightarrow> real sequence" where
  "scale_sequences x f = (\<lambda>n. x * (f n))"

typ "(real, nat \<Rightarrow> real, 'm) module_scheme"

definition fib_space :: "(real, real sequence) module" where
  "fib_space = 
    \<lparr> carrier = fib_sequences, 
    mult = undefined, 
    one = undefined,
    zero = (\<lambda>n::nat. 0), 
    add = (\<lambda> (f::real sequence) g. (\<lambda>n. (f n) + (g n))),  
    module.smult = scale_sequences \<rparr>"

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
    have "f (Suc (Suc n)) + g (Suc (Suc n)) = f n + f (Suc n) + g n + g (Suc n)"
      using grp_f grp_g
      unfolding fib_space_def fib_sequences_def
      by simp
    also have "... = f n + g n + (f (Suc n) + g (Suc n))"
      by simp
    finally show "f (Suc (Suc n)) + g (Suc (Suc n)) = f n + g n + (f (Suc n) + g (Suc n))"
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
    unfolding fib_space_def fib_sequences_def
    by simp
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
      unfolding fib_space_def fib_sequences_def
      by simp
    moreover have "\<forall>n::nat. -(f n + f (Suc n)) = -(f n) + -(f (Suc n))"
      by simp
    moreover have "\<forall>n::nat. -(f n) + -(f (Suc n)) = ?g n + ?g (Suc n)"
      by simp
    ultimately have "\<forall>n::nat. ?g (Suc (Suc n)) = ?g n + ?g (Suc n)"
      by metis
    hence "?g \<in> carrier fib_space"
      unfolding fib_space_def fib_sequences_def
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
        unfolding fib_space_def fib_sequences_def
        by simp
      also have "... = \<alpha> * (f n) + \<alpha> * (f (Suc n))"
        by argo
      finally show "\<alpha> * f (Suc (Suc n)) = \<alpha> * f n + \<alpha> * f (Suc n)"
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

end