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

interpretation sequence_space: vectorspace reals fib_space
proof (unfold vectorspace_def, safe)
  show "Module.module reals fib_space"
    sorry
next
  show "field reals"
    sorry             
qed

end