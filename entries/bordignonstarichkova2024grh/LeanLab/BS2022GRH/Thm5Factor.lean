module

public import LeanLab.BS2022GRH.QG
public import LeanLab.ChenExplicit.TwinCNumeric

/-!
P0021, Bordignon-Starichkova 2022, arXiv 2211.08844 v1, Theorem 5, Section 5.1.
The near-1 factor `1 - 0.62 log X₂ / X₂^{1/16}` and the `c_G(X₂)/log^{A-2} N` term of the
Theorem 5 lower bound, at the Section 5.4 range `N ≥ X₂ ≥ exp(exp 15.85)`, `A = 4`.
Read in Claude in Chrome from arxiv.org/html/2211.08844 on 2026-10-18.
AI-written Lean code, Claude, run 20261018T1903Z-4829, unit U-0968. Checked only by the
Lean kernel. Binary Goldbach is OPEN; Theorem 3 itself stays cited.

Result: the Theorem 5 bracket is at least its main term `M` minus `10⁻⁸`, so these two
pieces cost at most `8 · 10⁻⁸` against the margin `K3 > 0.0015` of `theorem3_main`.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

/-- The main bracket of Theorem 5: `2e^γ log(3-8α)/(4-8α) - ε C₂ 3e^{8α-2}/(4-8α)`. -/
noncomputable def thm5Main (α g ε C₂ : ℝ) : ℝ :=
  2 * g * log (3 - 8 * α) / (4 - 8 * α) - ε * C₂ * 3 * exp (8 * α - 2) / (4 - 8 * α)

/-- `δ = 0.62 log X₂ / X₂^{1/16}` of Theorem 5. -/
noncomputable def thm5Delta (X₂ : ℝ) : ℝ := 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)

/-- The whole factor after `8 U_N N / log² N` in Theorem 5, with `A = 4`, `τ` the twin
prime constant `∏_{p>2} (1 - 1/(p-1)²)` and `cGv = c_G(X₂)`. -/
noncomputable def thm5Bracket (α g ε C₂ τ cGv X₂ N : ℝ) : ℝ :=
  (1 - thm5Delta X₂) * (thm5Main α g ε C₂ -
    1 / 8 * (1 - thm5Delta X₂)⁻¹ * (2 * g * τ)⁻¹ * cGv / log N ^ (4 - 2 : ℕ))

lemma logX2_ge {X₂ : ℝ} (h : exp (exp 15.85) ≤ X₂) : (100000 : ℝ) ≤ log X₂ := by
  have hX : 0 < X₂ := lt_of_lt_of_le (exp_pos _) h
  have h1 : exp 15.85 ≤ log X₂ := (le_log_iff_exp_le hX).2 h
  have h2 := Real.pow_div_factorial_le_exp (x := (15.85 : ℝ)) (by norm_num) 9
  norm_num [Nat.factorial] at h2
  linarith

lemma delta_le {X₂ : ℝ} (h : exp (exp 15.85) ≤ X₂) :
    0 ≤ thm5Delta X₂ ∧ thm5Delta X₂ ≤ 1e-9 := by
  have hX : 0 < X₂ := lt_of_lt_of_le (exp_pos _) h
  have hL := logX2_ge h
  have hr : X₂ ^ (1 / 16 : ℝ) = exp (log X₂ / 16) := by
    rw [rpow_def_of_pos hX]; ring_nf
  set L := log X₂
  unfold thm5Delta
  rw [hr]
  have he := exp_pos (L / 16)
  constructor
  · positivity
  rw [div_le_iff₀ he]
  have h4 := Real.pow_div_factorial_le_exp (x := L / 16) (by positivity) 4
  norm_num [Nat.factorial] at h4
  have hL3 : (100000 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have : (L / 16) ^ 4 / 24 = L * L ^ 3 / 1572864 := by ring
  nlinarith [mul_le_mul_of_nonneg_left hL3 (by linarith : (0:ℝ) ≤ L)]

/-- **Theorem 5 bracket at the Section 5.4 range**: at least the main term minus `10⁻⁸`. -/
theorem thm5Bracket_ge {α g ε C₂ τ cGv X₂ N : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 0.0024548)
    (hg1 : 1.78103 ≤ g) (hg2 : g ≤ 1.781081) (hε : 0 ≤ ε) (hC : 0 ≤ C₂) (hτ : 0.65 ≤ τ)
    (hc : cGv ≤ 0.429) (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    thm5Main α g ε C₂ - 1e-8 ≤ thm5Bracket α g ε C₂ τ cGv X₂ N := by
  obtain ⟨hd0, hd⟩ := delta_le hX
  have hL := logX2_ge hX
  have hX0 : 0 < X₂ := lt_of_lt_of_le (exp_pos _) hX
  have hLN : log X₂ ≤ log N := log_le_log hX0 hN
  set M := thm5Main α g ε C₂
  set δ := thm5Delta X₂
  -- M ≤ 2
  have hM : M ≤ 2 := by
    have hd : (3.98 : ℝ) ≤ 4 - 8 * α := by linarith
    have hl : log (3 - 8 * α) ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (x := 3 - 8 * α) (by linarith); linarith
    have hl0 : 0 ≤ log (3 - 8 * α) := Real.log_nonneg (by linarith)
    have hE : 0 ≤ ε * C₂ * 3 * exp (8 * α - 2) / (4 - 8 * α) := by
      have := exp_pos (8 * α - 2); positivity
    have h1 : 2 * g * log (3 - 8 * α) / (4 - 8 * α) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    simp only [M, thm5Main]; linarith
  -- the c_G term
  set lN := log N
  have hlN : (100000 : ℝ) ≤ lN := le_trans hL hLN
  have hden : (1 : ℝ) ≤ 2 * g * τ := by nlinarith
  have hinv : (2 * g * τ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
  have hinv0 : 0 ≤ (2 * g * τ)⁻¹ := inv_nonneg.2 (by linarith)
  have hsq : (10000000000 : ℝ) ≤ lN ^ (4 - 2 : ℕ) := by
    norm_num; nlinarith
  have hT : 1 / 8 * (2 * g * τ)⁻¹ * cGv / lN ^ (4 - 2 : ℕ) ≤ 1e-9 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : (2 * g * τ)⁻¹ * cGv ≤ (2 * g * τ)⁻¹ * 0.429 := mul_le_mul_of_nonneg_left hc hinv0
    have : (2 * g * τ)⁻¹ * cGv ≤ 0.429 := by nlinarith
    nlinarith
  have hne : 1 - δ ≠ 0 := by linarith
  have expand : thm5Bracket α g ε C₂ τ cGv X₂ N =
      (1 - δ) * M - 1 / 8 * (2 * g * τ)⁻¹ * cGv / lN ^ (4 - 2 : ℕ) := by
    simp only [thm5Bracket, M, δ, lN]
    rw [mul_sub]
    congr 1
    field_simp
    exact mul_div_mul_left _ _ hne
  rw [expand]
  have : δ * M ≤ δ * 2 := mul_le_mul_of_nonneg_left hM hd0
  nlinarith

/-- At the Section 5.4 parameters, with `g = e^γ`, `τ` the twin prime constant and
`c_G(X₂) ≤ 0.429`: the Theorem 5 factor loses at most `10⁻⁸`. -/
theorem thm5Bracket_ge_params {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    thm5Main α0 (exp eulerMascheroniConstant) (1 / 8137) 114 - 1e-8 ≤
      thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114 LeanLab.ChenExplicit.twinC
        (cG X₂) X₂ N := by
  have hX0 : 0 < X₂ := lt_of_lt_of_le (exp_pos _) hX
  have h4 : (4e18 : ℝ) ≤ X₂ := by
    have := logX2_ge hX
    have h := (le_log_iff_exp_le hX0).1 (le_trans (by norm_num) this : (100 : ℝ) ≤ log X₂)
    have h2 := Real.pow_div_factorial_le_exp (x := (100 : ℝ)) (by norm_num) 20
    norm_num [Nat.factorial] at h2
    linarith
  obtain ⟨hg1, hg2⟩ := g_bounds
  have hτ : (0.65 : ℝ) ≤ LeanLab.ChenExplicit.twinC := by
    have := LeanLab.ChenExplicit.twinC_ge_065; norm_num at this ⊢; linarith
  exact thm5Bracket_ge (le_trans (by norm_num) alpha_ge) alpha_le hg1 hg2 (by norm_num)
    (by norm_num) hτ (cG_le_all X₂ h4) hX hN

/-- `theorem3_main` with Theorem 5's exact factor in place of its main term: the margin
stays above `0.0015 - 8·10⁻⁸`. -/
theorem theorem3_main_thm5 {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    (0.0015 - 8e-8 : ℝ) <
      K3 α0 (exp eulerMascheroniConstant) (1 / 8137) 112 114 LeanLab.ChenExplicit.BJS.cbar
      - 8 * thm5Main α0 (exp eulerMascheroniConstant) (1 / 8137) 114
      + 8 * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N := by
  have h1 := theorem3_main
  have h2 := thm5Bracket_ge_params hX hN
  linarith

/-- The first term of `K3` is exactly `8 · thm5Main`. -/
theorem K3_first (α g ε C₁ C₂ cb : ℝ) : K3 α g ε C₁ C₂ cb = 8 * thm5Main α g ε C₂
    - 1 / 2 * (8 * (g / 4 * (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)
      + log (8 / 3) * ε * C₁))
    - 1 / 2 * ((2 * g / (1 / 2 - α) + 3 * ε * C₁) * cb) := by
  unfold K3 thm5Main; ring


end LeanLab.BS2022GRH
