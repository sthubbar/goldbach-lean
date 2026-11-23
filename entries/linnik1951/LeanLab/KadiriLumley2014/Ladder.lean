module

public import LeanLab.KadiriLumley2014.Corollary

/-!
Kadiri and Lumley 2014, Table 2 and Corollary 1.2, arXiv 1407.7902v1 pages 1, 2 and 13.
Journal version INTEGERS 14 A61 pages 2 and 17.
Theorem 1.1 and the verification computations remain cited inputs.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- Binary verification endpoint used in Corollary 1.2. -/
def evenBase : ℕ := 4 * 10 ^ 18

/-- Rounded odd verification endpoint cited just after Corollary 1.2. -/
def oddBase : ℕ := 8875 * 10 ^ 27

/-- Helfgott and Platt, arXiv 1305.3062, Theorem 4.1.
This named input uses the weaker rounded endpoint printed in the paper. -/
def HelfgottPlattBase : Prop := TernaryGoldbachUpTo oddBase

/-- The row inequality alone produces an odd prime and a short even remainder.
The shift by three preserves the strict upper interval endpoint. -/
theorem row_step {x0 Δ : ℝ} (hrow : KLRow x0 Δ)
    (hx0 : (evenBase : ℝ) ≤ x0) (hΔ : 2 ≤ Δ)
    {n : ℕ} (hn : Odd n) (hlo : x0 + 3 < n)
    (hhi : (n : ℝ) < Δ * evenBase) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p + 4 ≤ n ∧ n - p ≤ evenBase + 2 := by
  let x : ℝ := n - 3
  have hx : x0 < x := by dsimp [x]; linarith
  obtain ⟨p, hp, hl, hu⟩ := hrow x hx
  have hΔ0 : 0 < Δ := by linarith
  have hl' : x - x / Δ < p := by
    convert hl using 1; ring
  have hquot : x / Δ < evenBase := by
    apply (div_lt_iff₀ hΔ0).2
    dsimp [x]
    nlinarith
  have hhalf : x / 2 < p := by
    have hxpos : 0 < x := by norm_num [evenBase] at hx0; linarith
    have hquot2 : x / Δ ≤ x / 2 := div_le_div_of_nonneg_left hxpos.le (by norm_num) hΔ
    linarith
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have hx4 : (4 : ℝ) < x := by
      have : (4 : ℝ) ≤ x0 := by norm_num [evenBase] at hx0 ⊢; linarith
      linarith
    norm_num at hhalf
    linarith
  have hpo := hp.odd_of_ne_two hp2
  have hev := Nat.Odd.sub_odd hn hpo
  have hsmall : p + 3 < n := by
    have : (p : ℝ) + 3 < n := by dsimp [x] at hu; linarith
    exact_mod_cast this
  have hgap : n < p + (evenBase + 3) := by
    have : (n : ℝ) < p + (evenBase + 3) := by dsimp [x] at hl'; linarith
    exact_mod_cast this
  refine ⟨p, hp, hpo, ?_, by omega⟩
  obtain ⟨k, hk⟩ := hev
  omega

/-- A single cited Table 2 row gives the stated three prime range,
conditional on the even verification and the certified top partition. -/
theorem ternary_of_row {x0 Δ : ℝ} (hrow : KLRow x0 Δ)
    (hx0 : (evenBase : ℝ) ≤ x0) (hΔ : 2 ≤ Δ)
    (hE : EvenGoldbachUpTo evenBase)
    {n : ℕ} (hn : Odd n) (hlo : x0 + 3 < n)
    (hhi : (n : ℝ) < Δ * evenBase) : IsTernarySum n := by
  obtain ⟨p, hp, hpo, h4, hle⟩ := row_step hrow hx0 hΔ hn hlo hhi
  have hev := Nat.Odd.sub_odd hn hpo
  have h4' : 4 ≤ n - p := by omega
  by_cases htop : n - p ≤ evenBase
  · obtain ⟨q, r, hq, hr, hqr⟩ := hE (n - p) hev h4' htop
    exact ⟨p, q, r, hp, hq, hr, by omega⟩
  · have heq : n - p = evenBase + 2 := by
      obtain ⟨k, hk⟩ := hev
      norm_num [evenBase] at htop hle ⊢
      omega
    have htop' : IsGoldbachSum (evenBase + 2) := goldbach_top
    obtain ⟨q, r, hq, hr, hqr⟩ := htop'
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

end LeanLab.KadiriLumley2014.Task64
