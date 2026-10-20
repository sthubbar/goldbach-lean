module

public import Mathlib
public import LeanLab.Tao2012.SmallRange
public import LeanLab.MinimalPartition.Basic

/-!
Numerical verification papers, statements only, plus how they feed the other papers.
P0005 Oliveira e Silva, Herzog, Pardi 2014, Math. Comp. 83, 2033-2060.
P0006 Helfgott, Platt 2013, arXiv 1305.3062, Exp. Math. 22.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
A `sorry` marks a computation the lab does not redo. The lab's kernel checker reaches 1000.
Prior art, IDEAS I-0001: PNT+ and teorth/IEANTN already formalize the ladder reduction from
even Goldbach to odd Goldbach used by Helfgott and Platt; the lab does not redo it.
-/

@[expose] public section

namespace LeanLab.Verifications
open LeanLab.SchnirelmannConstant LeanLab.Tao2012



/-! ### Links, proved with zero sorry -/

theorem evenGoldbachUpTo_mono {M N : ℕ} (h : EvenGoldbachUpTo N) (hMN : M ≤ N) :
    EvenGoldbachUpTo M := fun n he h4 hn => h n he h4 (hn.trans hMN)

theorem atMost3_of_ternary {n : ℕ} (h : IsTernarySum n) : AtMostPrimes 3 n := by
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := h
  exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)

/-- P0005 gives Tao's Theorem 1.6, Richstein's 4e14, with room to spare. -/
theorem tao_1_6_of_oesilva (h : EvenGoldbachUpTo (4 * 10 ^ 18)) : EvenGoldbachUpTo N0 :=
  evenGoldbachUpTo_mono h (by simp [N0])

/-- P0006 gives the odd Goldbach input to Tao's small range, 1.13e22, with room to spare. -/
theorem oddGoldbach113_of_hp (h : TernaryGoldbachUpTo 8875694145621773516800000000000) :
    OddGoldbachTo113e20 := fun n ho h7 hn => atMost3_of_ternary (h n ho h7 (by omega))

/-- Tao's five primes from Theorem 8.2, Ramaré-Saouter short intervals and the two
verification papers. Zero sorry of its own. -/
theorem tao_five_primes_of (h82 : Theorem8_2) (hRS : RSShortIntervals)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hT : TernaryGoldbachUpTo 8875694145621773516800000000000) :
    ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x :=
  theorem1_4_of' h82 (tao_1_6_of_oesilva hE) hRS (oddGoldbach113_of_hp hT)

/-! ### Earlier verifications, titles and abstracts as catalogued -/





/-- Each later even verification contains the earlier ones. -/
theorem richstein_of_oesilva (h : EvenGoldbachUpTo (4 * 10 ^ 18)) : EvenGoldbachUpTo (4 * 10 ^ 14) :=
  evenGoldbachUpTo_mono h (by norm_num)

theorem dtrs_of_richstein (h : EvenGoldbachUpTo (4 * 10 ^ 14)) : EvenGoldbachUpTo (10 ^ 14) :=
  evenGoldbachUpTo_mono h (by norm_num)

theorem sinisalo_of_dtrs (h : EvenGoldbachUpTo (10 ^ 14)) : EvenGoldbachUpTo (4 * 10 ^ 11) :=
  evenGoldbachUpTo_mono h (by norm_num)

theorem saouter_of_hp (h : TernaryGoldbachUpTo 8875694145621773516800000000000) :
    TernaryGoldbachUpTo (10 ^ 20) := fun n ho h7 hn => h n ho h7 (by omega)

/-! ### Minimal Goldbach partitions, P0042 -/

/-- The least prime `p` with `n - p` prime, for even `n ≥ 4`, given a witness. -/
noncomputable def minGB (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, p.Prime ∧ (n - p).Prime then Nat.find h else 0



/-- P0042 conjecture on probabilistic grounds, OPEN: `p(n) ≪ log² n · log log n`. -/
def GvLtRConjecture : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, Even n → 16 ≤ n → (minGB n : ℝ) ≤ C * Real.log n ^ 2 * Real.log (Real.log n)

/-- The record value in this notation: `minGB 3807404 = 751`, zero sorry. -/
theorem minGB_3807404 : minGB 3807404 = 751 := by
  have hL := LeanLab.MinimalPartition.a_3807404
  have hex : ∃ p, p.Prime ∧ (3807404 - p).Prime := ⟨751, hL.1⟩
  unfold minGB
  rw [dif_pos hex]
  rw [Nat.find_eq_iff]
  refine ⟨hL.1, fun m hm hmp => ?_⟩
  have := hL.2 hmp
  omega

end LeanLab.Verifications
