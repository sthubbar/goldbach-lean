module

public import LeanLab.KanieckiGap.Lemma7
public import LeanLab.Kaniecki1995.Gap

/-!
P0022, page 371. The two bridges between the natural and the real gap function.
Extract of the lab file `LeanLab/KanieckiGap/Decomp127.lean`: only these two lemmas are kept.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KanieckiGap.Decomp127

open Real

/-- LEAF. Page 371, the gap definition. Both lab representations use the same successor. -/
theorem nextPrime_eq (p : ℕ) :
    LeanLab.Kaniecki1995.nextPrime p = KanieckiGap.nextPrime p := by
  rfl

/-- LEAF. Page 371, the gap definition. At a natural argument the two maxima agree. -/
theorem lam_nat_eq (x : ℕ) :
    LeanLab.Kaniecki1995.lam (x : ℝ) = KanieckiGap.lam x := by
  unfold LeanLab.Kaniecki1995.lam KanieckiGap.lam
  rw [Nat.floor_natCast]
  have hc : (x : ℝ) ≤ 7 ↔ x ≤ 7 := by norm_cast
  simp only [hc]
  rfl

end LeanLab.KanieckiGap.Decomp127
