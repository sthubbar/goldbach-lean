module

public import LeanLab.LanguascoPintzZaccagnini2007.Density481

/-!
Jutila 1977, On Linnik's constant, Math. Scand. 41, page 46, Theorem 1, display 1.8,
stated as printed, and the reduction of the P0045 density sentence to it.
P0045 journal page 774, the sentence following display 8.

The density theorem itself stays an explicit hypothesis. Nothing here proves it.
The reduction takes epsilon one half, alpha equal to one minus H over log X and Q equal to P.
The range condition alpha at least four fifths holds once X is at least exp of 5H.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Jutila 1977 page 46, the rectangle `R(α, T)` of the display before 1.3 together with the
index set of `N*(α, T, Q)`: a modulus `q` with `1 ≤ q ≤ Q`, a primitive character modulo `q`
and a zero of its L function with `α ≤ σ ≤ 1` and `|t| ≤ T`. -/
def jutilaRect481 (α T Q : ℝ) : Set (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :=
  {z | 1 ≤ z.1 ∧ (z.1 : ℝ) ≤ Q ∧ z.2.1.IsPrimitive ∧ Lfun481 z.2.1 z.2.2 = 0 ∧
    α ≤ z.2.2.re ∧ z.2.2.re ≤ 1 ∧ |z.2.2.im| ≤ T}

/-- Jutila 1977 page 46, Theorem 1, display 1.8: for `4/5 ≤ α ≤ 1` and `T ≥ 1`,
`N*(α, T, Q) ≪_ε (Q^2 T)^((2 + ε)(1 - α))`, the implied constant depending on `ε` only.
The count is written as the sum of analytic multiplicities over an arbitrary finite set of
distinct modulus, primitive character, zero triples of the rectangle, which is the count
with multiplicity. -/
def JutilaTheorem18_481 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ α T Q : ℝ, 4 / 5 ≤ α → α ≤ 1 → 1 ≤ T →
    ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ z ∈ F, z ∈ jutilaRect481 α T Q) →
      (∑ z ∈ F, (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤
        C * (Q ^ 2 * T) ^ ((2 + ε) * (1 - α))

/-- P0045 journal page 774, the sentence following display 8: the box of display 8 lies in
Jutila's rectangle with `α = 1 - H / log X` and `Q = P`. -/
theorem zeroBox_subset_jutilaRect481 (X : ℕ) (H T P : ℝ) :
    zeroBox481 X H T P ⊆ jutilaRect481 (1 - H / Real.log X) T P := by
  rintro z ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6.le, h7⟩

/-- P0045 journal page 774, the sentence following display 8, derived from Jutila 1977
page 46 display 1.8 at `ε = 1/2`, `α = 1 - H / log X`, `Q = P`: since `T ≤ P ≤ sqrt X` the
base `P^2 T` is at most `X^(3/2)`, so the bound is at most `C exp ((15/4) H) ≤ C exp (4 H)`.
The cutoff `X ≥ exp (5 H)` gives `α ≥ 4/5`. CONDITIONAL ON the cited theorem `h`. -/
theorem jutilaStatement481_of_theorem18 (h : JutilaTheorem18_481) : JutilaStatement481 := by
  obtain ⟨C, hC, hJ⟩ := h (1 / 2) (by norm_num)
  apply jutila_of_rectangle_density481
  refine ⟨C, hC, fun H T hH hT => ?_⟩
  refine ⟨max 2 ⌈Real.exp (5 * H)⌉₊, fun X hX P _ _ F hF => ?_⟩
  have hX2 : 2 ≤ X := le_of_max_le_left hX
  have hXc : ⌈Real.exp (5 * H)⌉₊ ≤ X := le_of_max_le_right hX
  have hXe : Real.exp (5 * H) ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hXc)
  have hlog : 5 * H ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos _) hXe
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log X := by linarith
  have hq0 : 0 ≤ H / Real.log X := div_nonneg (by linarith) hlogpos.le
  have hq1 : H / Real.log X ≤ 1 / 5 := by
    rw [div_le_iff₀ hlogpos]; linarith
  have key := hJ (1 - H / Real.log X) T P (by linarith) (by linarith) hT F
    (fun z hz => zeroBox_subset_jutilaRect481 X H T P (hF z hz))
  have hexp : (2 + 1 / 2 : ℝ) * (1 - (1 - H / Real.log X)) = (5 / 2 : ℝ) * H / Real.log X := by
    ring
  rwa [hexp] at key

end

end LeanLab.LPZ2007

