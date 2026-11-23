module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Verifications.OeSHPTables
public import LeanLab.Verifications.PrattCertificates

/-!
Pratt certificates checked by the kernel, closing the cited primality inputs of
OeSHPTables.lean for P0005's two records.
Method: Lucas' test, Mathlib's `lucas_primality`, with a binary modular power proved equal to
`ZMod` exponentiation; factorizations of p - 1 found by Python, checked by the kernel; prime
factors below 10^7 by trial division with the lab's `primeB`, larger ones recursively.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Verifications.Pratt

theorem prime_nRec_sub' : (OeSHP.nRec - 9781).Prime := by
  exact prime_nRec_sub_literal

theorem pGap_prime_lo : OeSHP.pGap.Prime := by
  exact pGap_prime_lo_literal

theorem pGap_prime_hi : (OeSHP.pGap + 1476).Prime := by
  exact pGap_prime_hi_literal

/-- The least prime of a Goldbach partition of 3325581707333960528 is 9781, no placeholder proof. -/
theorem minGB_nRec' : LeanLab.Verifications.minGB OeSHP.nRec = 9781 := by
  have hex : ∃ p, p.Prime ∧ (OeSHP.nRec - p).Prime := ⟨9781, by norm_num, prime_nRec_sub'⟩
  unfold LeanLab.Verifications.minGB
  rw [dif_pos hex, Nat.find_eq_iff]
  exact ⟨⟨by norm_num, prime_nRec_sub'⟩,
    fun m hm hmp => OeSHP.no_small_partition m hm hmp.1 hmp.2⟩

/-- 1425172824437699411 and 1425172824437700887 are consecutive primes, 1476 apart. -/
theorem gap1476 : OeSHP.pGap.Prime ∧ (OeSHP.pGap + 1476).Prime ∧
    ∀ k, 0 < k → k < 1476 → ¬ (OeSHP.pGap + k).Prime :=
  ⟨pGap_prime_lo, pGap_prime_hi, OeSHP.gap_composite⟩

end LeanLab.Verifications.Pratt
