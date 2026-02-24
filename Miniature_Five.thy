chapter \<open>Miniature 5\<close>

theory Miniature_Five
  imports Thirty_Three_Miniatures_Root "Miniature_Five/Code"

begin

section \<open>Central Types and Definitions\<close>

text \<open>
  Miniature 5 aims at showing that the (generalized) Hamming Code corrects \<^latex>\<open>$err = 1$\<close>-bit-errors.

  The overall proof strategy is as follows:

    1) Define the Hamming Code as a particular linear code, i.e., a vector space over \<^latex>\<open>$\mathbb{F}_2$\<close>,
        by defining it as the kernel of a matrix (its so-called parity check matrix).
    2) Show that the minimum Hamming distance in this vector space is \<^latex>\<open>$3 > 2 = 2 \cdot err$\<close>.
        To prove this, viewing the Hamming code as the kernel of its parity check matrix is helpful:
        We only need to show that no vector in the matrix kernel has length \<^latex>\<open>$\leq 2$\<close>.
        Since the Hamming distance between any two Hamming code words is the length of their
        difference vector, this shows the claim.

  Since the Hamming Code is just one example of (linear) codes, we tried to keep this formalization
  more abstract to cover potential further use cases.

  The formalization is structured as follows:

    1) Theory "Code" introduces general terminology about codes over arbitrary finite alphabets,
         such as the definition of Hamming distances and error-correcting codes.

         The main lemma of this theory is that a code can correct t errors, iff the minimum
         hamming distance is >= 2t + 1.
    2) Theory "LinearCode" defines linear codes, i.e., codes that form a linear subspace 
        of the (induced, see below) vector space of all words \<^latex>\<open>$\mathbb{K}^n$\<close>.

        The main lemma of this theory is, that for the minimum distance of a linear code,
        it suffices to take the minimum of the hamming_distances from the 0-vector (this
        is sometimes called the hamming weight).
    3) Theory "GeneratingMatrix" introduces the generating and parity check matrix of linear codes.
    4) Theory "HammingCode" defines the generalized Hamming code via its parity check matrix
        and shows that it is 1-bit-error-correcting.

  To define the Hamming code and show claims about linear codes and their orthogonal complements,
  we need more general definitions and results about vector spaces that we did not find in the
  existing HOL and AFP libraries:

    5) Theory "InducedVectorspace" defines vector spaces of the form \<^latex>\<open>$\mathbb{K}^n$\<close> 
        for fields K. 
    6) Theory "CarrierSetMatrix" redefines matrix-vector-multiplication and the scalar product,
        as the definitions available in the AFP require the element type of the base field to 
        be of the `semiring_0` typeclass, which we do not require.
        It then proves some results about these new definitions.
    7) Theory "MoreVectorspace" shows additional claims about vector spaces that we need throughout
        our formalization.
\<close>

instantiation gf2 :: equal
begin

definition equal_gf2 :: "gf2 \<Rightarrow> gf2 \<Rightarrow> bool" where
  "equal_gf2 x y = (Rep_gf2 x = Rep_gf2 y)"

instance
  by standard (auto simp: equal_gf2_def Rep_gf2_inject)
end

instantiation vec :: (equal) equal
begin
definition equal_vec :: "('a::equal) vec \<Rightarrow> ('a::equal) vec \<Rightarrow> bool" where
  "equal_vec x y \<equiv> (dim_vec x = dim_vec y) \<and> (\<forall> i \<in> {0..<dim_vec x}. x$i = y$i)"

instance proof
  fix x y :: "'a::equal vec"
  show "equal_class.equal x y = (x = y)" unfolding equal_vec_def by auto
qed
end

end