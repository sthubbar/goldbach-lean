module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Verifications.PrattCertificates

/-!
The prime `3999999999999999761`, certified by Lucas certificates checked in the kernel, with
its two large auxiliary primes. It is the prime just below `4 · 10^18` used to close the top
of the finite range in `Dudek2014/MaxGap.lean`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014
open Real LeanLab.Verifications.Pratt

/-! ### The prime `3999999999999999761` -/

theorem p777448979 : Nat.Prime 777448979 := pB (by decide +kernel)

theorem p13994081623 : Nat.Prime 13994081623 := by
  refine pratt 13994081623 3 [(2, 1), (3, 2), (777448979, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact p777448979

theorem pBig : Nat.Prime 3999999999999999761 := by
  refine pratt 3999999999999999761 7 [(2, 4), (5, 1), (3572939, 1), (13994081623, 1)]
    (by norm_num) (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_five
  · exact pB (by decide +kernel)
  · exact p13994081623

end LeanLab.KadiriLumley2014
