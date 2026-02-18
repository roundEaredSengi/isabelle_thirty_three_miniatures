theory Proof_Method_Scratch
  imports "HOL-Eisbach.Eisbach"
          "HOL-Eisbach.Eisbach_Tools"
          "Combinatorics_Words.CoWBasic"
          "Miniature_Two"
          "Stochastic_Matrices.Eigenspace"

begin 

method split_iff = (rule iffD1, simp, rule iffD2, simp, goal_cases)

lemma "card {x,y} = 1 \<Longrightarrow> x = y"
  by (metis mem_simps(2) mem_simps(1) card_1_singletonE)

lemma test:
  assumes X: 
    "Q \<longrightarrow> P"
    Q
  shows P
  apply (match X in I : "Q \<longrightarrow> P" and I': Q \<Rightarrow> \<open>insert mp [OF I I']\<close>)
  oops

end