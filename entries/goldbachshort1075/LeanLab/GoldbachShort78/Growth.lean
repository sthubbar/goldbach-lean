module

public import LeanLab.GoldbachShort78.Statements

/-!
Elementary growth bounds for the side conditions of `goldbach_short_b`.
These are consequences of real powers and logarithms, not cited analytic inputs.

AI wrote the Lean code, Codex, OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78

/-- Every sublinear real power is eventually at most any positive multiple of x. -/
theorem eventually_rpow_le_mul {a δ : ℝ} (ha : a < 1) (hδ : 0 < δ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → x ^ a ≤ δ * x := by
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 1 / δ ≤ x ^ (1 - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr ha)).eventually_ge_atTop (1 / δ)
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max A 1, ?_⟩
  intro x hx
  have hxA := le_trans (le_max_left A 1) hx
  have hx1 := le_trans (le_max_right A 1) hx
  have hxpos : 0 < x := by linarith
  have hprod : x ^ a * x ^ (1 - a) = x := by
    rw [← Real.rpow_add hxpos]
    simp
  have hdiv : x ^ a / δ ≤ x := by
    calc
      x ^ a / δ = x ^ a * (1 / δ) := by ring
      _ ≤ x ^ a * x ^ (1 - a) := mul_le_mul_of_nonneg_left (hA x hxA) (by positivity)
      _ = x := hprod
  have := (div_le_iff₀ hδ).mp hdiv
  linarith

/-- All side conditions of goldbach_short_b hold eventually for 0 < a < 1. -/
theorem short_b_side_conditions_eventually {a c x₀ y₀ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x → x₀ ≤ (x : ℝ) ∧ y₀ ≤ (x : ℝ) ^ a ∧
      3 ≤ (x : ℝ) ^ a ∧ 1 < c * a ^ 2 * Real.log x ∧
      2 * ⌈(x : ℝ) ^ a⌉₊ + 3 ≤ x := by
  obtain ⟨A, hA⟩ := eventually_rpow_le_mul ha1 (by norm_num : (0 : ℝ) < 1 / 8)
  have hgrowth : ∀ᶠ x : ℝ in Filter.atTop, max y₀ 3 ≤ x ^ a :=
    (tendsto_rpow_atTop ha0).eventually_ge_atTop (max y₀ 3)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hgrowth
  have hlog : ∀ᶠ x : ℝ in Filter.atTop, 2 / (c * a ^ 2) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (2 / (c * a ^ 2))
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max x₀ (max A (max B (max C 8))), ?_⟩
  intro x hx
  have hx0 : x₀ ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hxA : A ≤ (x : ℝ) := by grind
  have hxB : B ≤ (x : ℝ) := by grind
  have hxC : C ≤ (x : ℝ) := by grind
  have hx8 : (8 : ℝ) ≤ x := by grind
  have hxpos : (0 : ℝ) < x := by linarith
  have hp := hB x hxB
  refine ⟨hx0, le_trans (le_max_left _ _) hp, le_trans (le_max_right _ _) hp, ?_, ?_⟩
  · have hca : 0 < c * a ^ 2 := by positivity
    have := (div_le_iff₀ hca).mp (hC x hxC)
    nlinarith
  · have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hxpos.le a)
    have hsmall := hA x hxA
    have hs : 2 * (⌈(x : ℝ) ^ a⌉₊ : ℝ) + 3 ≤ x := by linarith
    exact_mod_cast hs

/-- `goldbach_short_b` from the two counts, with all elementary side conditions discharged. -/
theorem goldbach_short_b_eventually {a b c x₀ y₀ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc : 0 < c)
    (hW : WindowCount a c x₀) (hA : AlmostAllCount b y₀) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (a * b) := by
  obtain ⟨X, hX⟩ := short_b_side_conditions_eventually (x₀ := x₀) (y₀ := y₀) ha0 ha1 hc
  refine ⟨X, ?_⟩
  intro x hx
  obtain ⟨h0, h1, h2, h3, h4⟩ := hX x hx
  exact goldbach_short_b ha0 hb0 hb1 hc hW hA h0 h1 h2 h3 h4

end LeanLab.GoldbachShort78
