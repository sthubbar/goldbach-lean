module

public import LeanLab.Linnik1951.Burst1122RouteWiring
public import LeanLab.Linnik1951.Burst1122GrhTransfer519

/-!
# Linnik 1951 under the generalized Riemann hypothesis

Yu. V. Linnik, Prime numbers and powers of two, Trudy Mat. Inst. Steklov 38, 1951, 152 to 169.
Assuming the generalized Riemann hypothesis for Dirichlet L-functions, there is a constant `K`
such that every sufficiently large even integer is a sum of two primes and at most `K` powers
of two.

`Burst1122RouteWiring` proves `linnik1951_decomposed_of_transfer_b1122` from GRH and one
further hypothesis `hT`, the Mellin transfer estimate stated on page 159 before equation 5.1.
`Burst1122GrhTransfer519` proves that estimate from GRH as `grh_mellin_transfer519_b1122`.
Here the two are combined. The bound for the mixed integral that this route uses carries
`log N` to the power 7 in place of the power 6 printed in display 5.5 on page 160.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- Linnik 1951, the theorem of page 154 in its qualitative form, with the conclusion of
pages 168 and 169: assuming GRH, some `K` makes every sufficiently large even integer a sum
of two primes and at most `K` powers of two, each power at least 2. -/
theorem linnik1951_decomposed_final_b1122 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) :=
  fun hG => linnik1951_decomposed_of_transfer_b1122 hG (Task519.grh_mellin_transfer519_b1122 hG)

end LeanLab.Linnik1951
