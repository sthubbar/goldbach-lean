module

public import LeanLab.GoldbachAverage.ZeroSums
public import LeanLab.GoldbachAverage.OddSumPNT

/-!
P0051 D. A. Goldston, A. I. Suriajaya 2021, arXiv 2110.14250v2, On an average Goldbach
representation formula of Fujii: Theorem 1 simplified form, Corollary 2, Theorem 7 first line.
P0053 A. Languasco, A. Zaccagnini 2012, arXiv 1206.0251, A Cesàro average of Goldbach numbers:
Theorem 1, unconditional, k > 1; as printed it is false, see `lz_cesaro_printed`, U-6500.
Both read on arXiv 2026-10-16 by run 20261016T2303Z-22954, unit U-0094.
AI-written Lean code, Claude. Checked only by the Lean kernel. The lab's unproved cited statements of Theorem 1, Corollary 2
and the corrected Cesàro formula are not part of this copy; see PORTING.md.
-/

@[expose] public section

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `e(u) = exp(2πiu)`. -/
def eAdd (u : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * u)

/-- `Ψ(r, α) = Σ_n Λ(n) r^n e(αn)`. -/
def PsiGen (r α : ℝ) : ℂ := ∑' n : ℕ, (Λ n : ℂ) * (r : ℂ) ^ n * eAdd (α * n)

/-- `I(r, α) = Σ_n r^n e(αn)`, from `n = 1` as Goldston-Suriajaya's Λ-free comparison sum. -/
def IGen (r α : ℝ) : ℂ := ∑' n : ℕ, (if n = 0 then 0 else (r : ℂ) ^ n * eAdd (α * n))

/-- `I_N(r, α) = Σ_{n ≤ N} r^n e(αn)`. -/
def IGenN (N : ℕ) (r α : ℝ) : ℂ := ∑ n ∈ Icc 1 N, (r : ℂ) ^ n * eAdd (α * n)

/-- `E(N) = ∫_0^1 (Ψ(r,α) - I(r,α))² I_N(1/r, -α) dα`; the paper notes `0 < r < 1` and the value
does not depend on `r`, since the integral picks out coefficients `n ≤ N`. -/
def EGS (N : ℕ) (r : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, (PsiGen r α - IGen r α) ^ 2 * IGenN N (1 / r) (-α)


/-- `Θ`, the supremum of the real parts of the nontrivial zeros. -/
def Theta : ℝ := sSup (Set.range fun ρ : NontrivialZero => ρ.1.re)


/-- P0051 Theorem 7, first line, unconditional: `Σ_{n ≤ N, n odd} ψ₂(n) = 2 N log N + O(N)`.
PROVED 2026-10-18, run 20261018T0002Z-3485, by `gs_theorem7_odd_proved` in OddSumPNT.lean; was a
cited statement without proof. -/
theorem gs_theorem7_odd : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    |∑ n ∈ (range (N + 1)).filter Odd, G n - 2 * N * Real.log N| ≤ K * N :=
  gs_theorem7_odd_proved

/-- P0053 Theorem 1 AS PRINTED in arXiv 1206.0251v1, unconditional, `k > 1`:
`Σ_{n ≤ N} r_G(n) (1 - n/N)^k / Γ(k+1) = N²/Γ(k+3) - 2 Σ_ρ Γ(ρ)/Γ(ρ+k+2) N^{ρ+1}
 + Σ_{ρ₁} Σ_{ρ₂} Γ(ρ₁)Γ(ρ₂)/Γ(ρ₁+ρ₂+k+1) N^{ρ₁+ρ₂} + O_k(N^{1/2})`; `r_G = G`.
FALSE as printed, author-corrected: Languasco's survey arXiv 1606.00860 §6 says the error term
was "erroneously written as O_k(N^{1/2})" and is `O_k(N)`; the missing term is
`-2 log(2π) N/Γ(k+2)`, from the constant `-ζ'/ζ(0)` that the printed Lemma 1 drops, see
`LZ2012.lemma1_printed_real_false` in LZ2012Lemma1.lean and numerics/lz_cesaro_U6500.out, U-6500.
Kept as a `def`, not asserted; until 2026-10-20 this was the cited, unproved `lz_cesaro`. -/
def lz_cesaro_printed (k : ℝ) : Prop := ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n * (1 - (n : ℝ) / N) ^ k / Real.Gamma (k + 1) : ℝ) : ℂ)
      - (N : ℂ) ^ 2 / (Real.Gamma (k + 3) : ℂ)
      + 2 * zeroSum (fun ρ => Gamma ρ / Gamma (ρ + k + 2) * (N : ℂ) ^ (ρ + 1))
      - zeroSum (fun ρ₁ => zeroSum (fun ρ₂ =>
          Gamma ρ₁ * Gamma ρ₂ / Gamma (ρ₁ + ρ₂ + k + 1) * (N : ℂ) ^ (ρ₁ + ρ₂)))‖
      ≤ K * (N : ℝ) ^ ((1 : ℝ) / 2)


/-! ### Formal consistency with Goldston-Yang Theorem 2 at `k = 1`

Languasco-Zaccagnini need `k > 1`, so this only checks that the shapes agree at `k = 1`; it does
not derive Goldston-Yang from Languasco-Zaccagnini. -/

/-- `Γ(ρ)/Γ(ρ+3) = 1/(ρ(ρ+1)(ρ+2))` for `Re ρ > 0`. -/
theorem gamma_ratio_three (ρ : ℂ) (hρ : 0 < ρ.re) :
    Gamma ρ / Gamma (ρ + 1 + 2) = 1 / (ρ * (ρ + 1) * (ρ + 2)) := by
  have h0 : ρ ≠ 0 := fun h => by simp [h] at hρ
  have h1 : ρ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2 : ρ + 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hG : Gamma ρ ≠ 0 := Gamma_ne_zero_of_re_pos hρ
  have e : ρ + 1 + 2 = ρ + 2 + 1 := by ring
  rw [e, Gamma_add_one _ h2, show ρ + 2 = ρ + 1 + 1 by ring, Gamma_add_one _ h1,
    Gamma_add_one _ h0]
  field_simp

/-- `Γ(4) = 6`, so the `k = 1` main term `N²/Γ(k+3)` is Goldston-Yang's `N²/6`. -/
theorem gamma_four : Real.Gamma (1 + 3) = 6 := by
  rw [show (1 : ℝ) + 3 = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

end LeanLab.GoldbachAverage

