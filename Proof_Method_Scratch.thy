theory Proof_Method_Scratch
  imports "HOL-Eisbach.Eisbach"
          "HOL-Eisbach.Eisbach_Tools"
          "Combinatorics_Words.CoWBasic"
          "Miniature_Two"

begin 

method unfold_many_things =
  (
    unfold+
  )

interpretation sequence_space: vectorspace reals fib_space
proof (unfold_many_things)



method root_prover = (
    (unfold insert_iff),
    (elim disjE emptyE)
    )

lemma "u \<in> {x,y} \<Longrightarrow> P u"
  apply(root_prover)
  oops

method dest_conj =
  (match conclusion in "A \<and> B" for A B \<Rightarrow> \<open>cases \<open>A \<and> B\<close>; simp\<close>)

lemma "A \<and> B \<longrightarrow> A"
  apply dest_conj

end