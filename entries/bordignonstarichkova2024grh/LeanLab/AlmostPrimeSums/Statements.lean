module

public import Mathlib
public import LeanLab.ChenExplicit.Reductions
public import LeanLab.DERZ1997.Statements

/-!
Chen's theorem, its GRH explicit form, and Togashi-Uchiyama's P3 + P3.
P0002 Chen 1973, Sci. Sinica 16: every sufficiently large even integer is a prime plus a
  product of at most two primes.
P0021 Bordignon, Starichkova 2022, arXiv 2211.08844, abstract: assuming GRH every even
  integer larger than exp(exp(15.85)) is a prime plus a number with at most two prime factors.
P0072 Togashi, Uchiyama 1964, J. Fac. Sci. Hokkaido Univ. 18, Main Theorem: every
  sufficiently large even integer is a sum of two integers, each of which has not more than
  three prime factors. Prime factors are read with multiplicity, Mathlib's `Ω`; the paper
  speaks of the total number of prime factors.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.AlmostPrimeSums
open LeanLab.ChenExplicit LeanLab.DERZ1997

/-- Every sufficiently large even integer is `a + b` with `Ω a ≤ 3`, `Ω b ≤ 3`, both nonzero. -/
def TogashiUchiyama : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
    ∃ a b : ℕ, N = a + b ∧ Nat.IsAtMostAlmostPrime 3 a ∧ Nat.IsAtMostAlmostPrime 3 b

/-! ### The papers, cited, as statements -/


/-- P0021 Bordignon-Starichkova 2022, abstract. -/
def bordignonStarichkova_GRH : Prop := GRH → ChenAbove (Real.exp (Real.exp 15.85))


/-! ### Links, fully proved -/

theorem chenAbove_mono {T T' : ℝ} (hT : T ≤ T') (h : ChenAbove T) : ChenAbove T' :=
  fun N he hN => h N he (hT.trans_lt hN)

/-- BJS Theorem 3, already stated in `ChenExplicit`, gives Chen 1973. -/
theorem chen1973_of_BJS3 (h : BJS3) : ∃ T : ℝ, ChenAbove T := ⟨_, chenAbove_of_BJS3 h⟩

/-- The GRH threshold is below the unconditional one of BJS. -/
theorem bs_threshold_lt : Real.exp (Real.exp 15.85) < Real.exp (Real.exp (327 / 10)) :=
  Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by norm_num))

/-- Under GRH, Bordignon-Starichkova gives the BJS conclusion. -/
theorem bjs_conclusion_of_bs (h : GRH → ChenAbove (Real.exp (Real.exp 15.85))) :
    GRH → ChenAbove (Real.exp (Real.exp (327 / 10))) :=
  fun hG => chenAbove_mono bs_threshold_lt.le (h hG)

/-- Chen gives Togashi-Uchiyama: `p` has one prime factor, `m` at most two. -/
theorem togashiUchiyama_of_chen (h : ∃ T : ℝ, ChenAbove T) : TogashiUchiyama := by
  obtain ⟨T, hT⟩ := h
  refine ⟨⌈T⌉₊, fun N he hN => ?_⟩
  have hTN : T < N := (Nat.le_ceil T).trans_lt (by exact_mod_cast hN)
  obtain ⟨p, m, hp, rfl, hm⟩ := hT N he hTN
  refine ⟨p, m, rfl, ⟨hp.ne_zero, ?_⟩, ⟨hm.1, hm.2.trans (by norm_num)⟩⟩
  rw [ArithmeticFunction.cardFactors_apply_prime hp]; norm_num

/-- Togashi-Uchiyama from BJS Theorem 3, fully proved here. -/
theorem togashiUchiyama_of_BJS3 (h : BJS3) : TogashiUchiyama :=
  togashiUchiyama_of_chen (chen1973_of_BJS3 h)

end LeanLab.AlmostPrimeSums
