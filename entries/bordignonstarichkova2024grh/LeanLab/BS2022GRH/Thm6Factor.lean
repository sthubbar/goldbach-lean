module

public import LeanLab.BS2022GRH.Thm5Factor

/-!
P0021, Bordignon-Starichkova 2022, arXiv 2211.08844 v1, Theorem 6, Section 5.2.
The near-1 factors and the lower-order terms `l₂ / log^{A-3} N`, `l₃ / log^{A-1} N` of the
Theorem 6 upper bound, at the Section 5.4 range `N ≥ X₂ ≥ exp(exp 15.85)`, `A = 4`.
`l₁, l₂, l₃`, `k_x = 8(1/6 - x)` and `h(s)` read in Claude in Chrome from
arxiv.org/html/2211.08844 on 2026-10-18, Theorem 6 and the sieve statement of Section 2.
AI-written Lean code, Claude, run 20261018T2003Z-9206, unit U-0969. Checked only by the
Lean kernel. Binary Goldbach is OPEN; Theorem 6 itself stays cited.

Result: at `α ≤ 0.0024548`, `k_α ∈ [1, 4/3]` so `e² h(k_α) = 1`, and the whole Theorem 6
bracket is at most its main term, the second piece of `K3`, plus `10⁻⁶`. With the
weight `1/2 · 8` of Section 5.4 this costs at most `4 · 10⁻⁶` against `K3 > 0.0015`.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

/-- `k_x = 8 (1/6 - x)` of Theorem 6. -/
noncomputable def kA (α : ℝ) : ℝ := 8 * (1 / 6 - α)

/-- `h(s)` of the linear sieve statement, Section 2: `e⁻²` on `[1,2]`, `e^{-s}` on `[2,3]`,
`3 s⁻¹ e^{-s}` for `s ≥ 3`. -/
noncomputable def hS (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 / s * exp (-s)

/-- `X^{1/8} / (X^{1/8} - 1)`. -/
noncomputable def rX (X : ℝ) : ℝ := X ^ (1 / 8 : ℝ) / (X ^ (1 / 8 : ℝ) - 1)

/-- The main term of Theorem 6, equal to the second piece of `K3` divided by `4`. -/
noncomputable def thm6Main (α g ε C₁ : ℝ) : ℝ :=
  g / 4 * (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + log (8 / 3) * ε * C₁

/-- `l₁(X₂)` of Theorem 6, as printed. -/
noncomputable def l1T6 (α g ε C₁ X : ℝ) : ℝ :=
  (1 + 3e-7) * (1 + thm5Delta X) * rX X *
    (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)
        + 512 / (kA α * log X ^ 2))
      + (log (8 / 3) + 64 / log X ^ 2) * ε * C₁ * exp 2 * hS (kA α))

/-- `l₂(X₂)` of Theorem 6, `τ` the twin prime constant, `cGv = c_G(X₂)`. -/
noncomputable def l2T6 (g τ cGv X : ℝ) : ℝ :=
  cGv / 8 * (0.55 + 1 / log X) * (2 * g * τ)⁻¹

/-- `l₃(X₂)` of Theorem 6. -/
noncomputable def l3T6 (α g ε C₁ cGv X : ℝ) : ℝ :=
  (1 + thm5Delta X) * (2 * g / kA α + ε * C₁ * exp 2 * hS (kA α)) * cGv

/-- The Theorem 6 bracket `l₁ + l₂ / log^{A-3} N + l₃ / log^{A-1} N` with `A = 4`. -/
noncomputable def thm6Bracket (α g ε C₁ τ cGv X N : ℝ) : ℝ :=
  l1T6 α g ε C₁ X + l2T6 g τ cGv X / log N ^ (4 - 3 : ℕ)
    + l3T6 α g ε C₁ cGv X / log N ^ (4 - 1 : ℕ)

lemma kA_bounds {α : ℝ} (h0 : 0 ≤ α) (h : α ≤ 0.0024548) : 1 ≤ kA α ∧ kA α ≤ 4 / 3 := by
  unfold kA; constructor <;> linarith

lemma e2h_eq {α : ℝ} (h0 : 0 ≤ α) (h : α ≤ 0.0024548) : exp 2 * hS (kA α) = 1 := by
  obtain ⟨_, hk⟩ := kA_bounds h0 h
  unfold hS
  rw [if_pos (show kA α ≤ 2 by linarith), ← exp_add]; norm_num

lemma rX_le {X : ℝ} (h : exp (exp 15.85) ≤ X) : 1 ≤ rX X ∧ rX X ≤ 1 + 1e-9 := by
  have hX : 0 < X := lt_of_lt_of_le (exp_pos _) h
  have hL := logX2_ge h
  have hr : X ^ (1 / 8 : ℝ) = exp (log X / 8) := by
    rw [rpow_def_of_pos hX]; ring_nf
  unfold rX
  rw [hr]
  set L := log X
  have h4 := Real.pow_div_factorial_le_exp (x := L / 8) (by positivity) 4
  norm_num [Nat.factorial] at h4
  have hL4 : (100000 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hY : (2000000000 : ℝ) ≤ exp (L / 8) := by
    have : (L / 8) ^ 4 / 24 = L ^ 4 / 98304 := by ring
    nlinarith
  have hpos : 0 < exp (L / 8) - 1 := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; nlinarith

/-- `0 ≤ thm6Main ≤ 1.71` at the Section 5.4 ranges. -/
lemma thm6Main_bounds {α g ε C₁ : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 0.0024548)
    (hg1 : 1.78103 ≤ g) (hg2 : g ≤ 1.781081) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8137)
    (hC0 : 0 ≤ C₁) (hC : C₁ ≤ 112) : 0 ≤ thm6Main α g ε C₁ ∧ thm6Main α g ε C₁ ≤ 1.71 := by
  unfold thm6Main
  have hl6 := log6_le
  have hl83 := log83_le
  have hlr := logr_le hα0 hα
  have hl6' : (1 : ℝ) ≤ log 6 := by
    have := Real.add_one_le_exp (1 : ℝ)
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hlr0 : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hl830 : 0 ≤ log (8 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hd : 0 < 1 / 2 - α := by linarith
  set B := log 6 + log ((3 - 8 * α) / (3 - 18 * α))
  have hB : B ≤ 1.79176 + 0.024548 / (3 - 18 * 0.0024548) := by simp only [B]; linarith
  have hB0 : 0 ≤ B := by simp only [B]; linarith
  have hεC : ε * C₁ ≤ 112 / 8137 := by nlinarith
  have hεC0 : 0 ≤ ε * C₁ := mul_nonneg hε0 hC0
  have t1 : g / 4 * B / (1 / 2 - α) ≤ 1.69 := by
    rw [div_le_iff₀ hd]; norm_num at hB; nlinarith
  have t2 : log (8 / 3) * ε * C₁ ≤ 0.98083 * (112 / 8137) := by
    rw [mul_assoc]; exact mul_le_mul hl83 hεC hεC0 (by norm_num)
  have t10 : 0 ≤ g / 4 * B / (1 / 2 - α) := by
    apply div_nonneg _ hd.le; nlinarith
  have t20 : 0 ≤ log (8 / 3) * ε * C₁ := by rw [mul_assoc]; positivity
  constructor
  · linarith
  · norm_num at t2 ⊢; linarith

/-- `l₂ ≤ 0.0129` at the Section 5.4 ranges. -/
lemma l2T6_le {g τ cGv X : ℝ} (hg1 : 1.78103 ≤ g) (hτ : 0.65 ≤ τ) (hc : cGv ≤ 0.429)
    (hL : 100000 ≤ log X) : l2T6 g τ cGv X ≤ 0.0129 := by
  have hden : (2.3 : ℝ) ≤ 2 * g * τ := by nlinarith
  have hinv : (2 * g * τ)⁻¹ ≤ 1 / 2.3 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hden
  have hinv0 : 0 ≤ (2 * g * τ)⁻¹ := inv_nonneg.2 (by linarith)
  have hq : 1 / log X ≤ 1 / 100000 := one_div_le_one_div_of_le (by norm_num) hL
  have hq0 : 0 ≤ 1 / log X := by apply div_nonneg <;> linarith
  unfold l2T6
  have hc0 : 0 ≤ (0.55 + 1 / log X) * (2 * g * τ)⁻¹ := by positivity
  have s1 : cGv / 8 * (0.55 + 1 / log X) * (2 * g * τ)⁻¹ ≤
      0.429 / 8 * ((0.55 + 1 / log X) * (2 * g * τ)⁻¹) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) hc0
  have s2 : (0.55 + 1 / log X) * (2 * g * τ)⁻¹ ≤ (0.55 + 1 / 100000) * (1 / 2.3) :=
    mul_le_mul (by linarith) hinv hinv0 (by norm_num)
  have s3 := mul_le_mul_of_nonneg_left s2 (by norm_num : (0:ℝ) ≤ 0.429 / 8)
  have : (0.429 / 8 : ℝ) * ((0.55 + 1 / 100000) * (1 / 2.3)) ≤ 0.0129 := by norm_num
  linarith

/-- `l₃ ≤ 2` at the Section 5.4 ranges. -/
lemma l3T6_le {α g ε C₁ cGv X : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 0.0024548)
    (hg2 : g ≤ 1.781081) (hg0 : 0 ≤ g) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8137)
    (hC0 : 0 ≤ C₁) (hC : C₁ ≤ 112) (hc : cGv ≤ 0.429) (hd0 : 0 ≤ thm5Delta X)
    (hd : thm5Delta X ≤ 1e-9) : l3T6 α g ε C₁ cGv X ≤ 2 := by
  obtain ⟨hk1, hk2⟩ := kA_bounds hα0 hα
  have he2 := e2h_eq hα0 hα
  have e : ε * C₁ * exp 2 * hS (kA α) = ε * C₁ := by
    rw [mul_assoc (ε * C₁), he2, mul_one]
  unfold l3T6
  rw [e]
  set k := kA α
  set δ := thm5Delta X
  have hεC : ε * C₁ ≤ 112 / 8137 := by nlinarith
  have hεC0 : 0 ≤ ε * C₁ := mul_nonneg hε0 hC0
  have hgk : 2 * g / k ≤ 3.6 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hgk0 : 0 ≤ 2 * g / k := div_nonneg (by linarith) (by linarith)
  have hP : 0 ≤ (1 + δ) * (2 * g / k + ε * C₁) := by positivity
  have s1 : (1 + δ) * (2 * g / k + ε * C₁) * cGv ≤ (1 + δ) * (2 * g / k + ε * C₁) * 0.429 :=
    mul_le_mul_of_nonneg_left hc hP
  have s2 : (1 + δ) * (2 * g / k + ε * C₁) ≤ (1 + 1e-9) * (3.6 + 112 / 8137) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have s3 : (1 + δ) * (2 * g / k + ε * C₁) * 0.429 ≤ (1 + 1e-9) * (3.6 + 112 / 8137) * 0.429 :=
    mul_le_mul_of_nonneg_right s2 (by norm_num)
  have : (1 + 1e-9 : ℝ) * (3.6 + 112 / 8137) * 0.429 ≤ 2 := by norm_num
  linarith

/-- `l₁ ≤ thm6Main + 7·10⁻⁷` at the Section 5.4 ranges. -/
lemma l1T6_le {α g ε C₁ X₂ : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 0.0024548)
    (hg1 : 1.78103 ≤ g) (hg2 : g ≤ 1.781081) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8137)
    (hC0 : 0 ≤ C₁) (hC : C₁ ≤ 112) (hX : exp (exp 15.85) ≤ X₂) :
    l1T6 α g ε C₁ X₂ ≤ thm6Main α g ε C₁ + 7e-7 := by
  obtain ⟨hd0, hd⟩ := delta_le hX
  obtain ⟨hr1, hr2⟩ := rX_le hX
  obtain ⟨hk1, hk2⟩ := kA_bounds hα0 hα
  obtain ⟨hM0, hM⟩ := thm6Main_bounds hα0 hα hg1 hg2 hε0 hε hC0 hC
  have he2 := e2h_eq hα0 hα
  have hL := logX2_ge hX
  have hεC : ε * C₁ ≤ 112 / 8137 := by nlinarith
  have hεC0 : 0 ≤ ε * C₁ := mul_nonneg hε0 hC0
  have hI : g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)
        + 512 / (kA α * log X₂ ^ 2))
        + (log (8 / 3) + 64 / log X₂ ^ 2) * ε * C₁ * exp 2 * hS (kA α)
      = thm6Main α g ε C₁ + g / 4 * (512 / (kA α * log X₂ ^ 2))
        + 64 / log X₂ ^ 2 * (ε * C₁) := by
    have : (log (8 / 3) + 64 / log X₂ ^ 2) * ε * C₁ * exp 2 * hS (kA α)
        = (log (8 / 3) + 64 / log X₂ ^ 2) * ε * C₁ * (exp 2 * hS (kA α)) := by ring
    rw [this, he2]
    unfold thm6Main; ring
  have e : l1T6 α g ε C₁ X₂ = (1 + 3e-7) * (1 + thm5Delta X₂) * rX X₂ *
      (thm6Main α g ε C₁ + g / 4 * (512 / (kA α * log X₂ ^ 2))
        + 64 / log X₂ ^ 2 * (ε * C₁)) := by
    unfold l1T6; rw [hI]
  rw [e]
  set L := log X₂
  set M := thm6Main α g ε C₁
  set δ := thm5Delta X₂
  set r := rX X₂
  set k := kA α
  have hL2 : (10000000000 : ℝ) ≤ L ^ 2 := by nlinarith
  have hkL : 10000000000 ≤ k * L ^ 2 := by nlinarith
  have hA : 512 / (k * L ^ 2) ≤ 512 / 10000000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkL
  have hA0 : 0 ≤ 512 / (k * L ^ 2) := div_nonneg (by norm_num) (by linarith)
  have hB : 64 / L ^ 2 ≤ 64 / 10000000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
  have hB0 : 0 ≤ 64 / L ^ 2 := div_nonneg (by norm_num) (by linarith)
  have hE1 : g / 4 * (512 / (k * L ^ 2)) ≤ 1.781081 / 4 * (512 / 10000000000) :=
    mul_le_mul (by linarith) hA hA0 (by norm_num)
  have hE10 : 0 ≤ g / 4 * (512 / (k * L ^ 2)) := mul_nonneg (by linarith) hA0
  have hE2 : 64 / L ^ 2 * (ε * C₁) ≤ 64 / 10000000000 * (112 / 8137) :=
    mul_le_mul hB hεC hεC0 (by norm_num)
  have hE20 : 0 ≤ 64 / L ^ 2 * (ε * C₁) := mul_nonneg hB0 hεC0
  have n1 : (1.781081 / 4 : ℝ) * (512 / 10000000000) + 64 / 10000000000 * (112 / 8137) ≤ 1e-7 := by
    norm_num
  set I := M + g / 4 * (512 / (k * L ^ 2)) + 64 / L ^ 2 * (ε * C₁)
  have hIu : I ≤ M + 1e-7 := by simp only [I]; linarith
  have hI0 : 0 ≤ I := by simp only [I]; linarith
  have h1 : (1 + δ) * r ≤ (1 + 1e-9) * (1 + 1e-9) :=
    mul_le_mul (by linarith) hr2 (by linarith) (by norm_num)
  have h2 : (1 + 3e-7) * ((1 + δ) * r) ≤ (1 + 3e-7) * ((1 + 1e-9) * (1 + 1e-9)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have n2 : (1 + 3e-7 : ℝ) * ((1 + 1e-9) * (1 + 1e-9)) ≤ 1 + 3.1e-7 := by norm_num
  have hF : (1 + 3e-7) * (1 + δ) * r ≤ 1 + 3.1e-7 := by rw [mul_assoc]; linarith
  have hF0 : 0 ≤ (1 + 3e-7) * (1 + δ) * r := by
    apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have h3 : (1 + 3e-7) * (1 + δ) * r * I ≤ (1 + 3.1e-7) * (M + 1e-7) :=
    mul_le_mul hF hIu hI0 (by norm_num)
  have h4 : (1 + 3.1e-7 : ℝ) * (M + 1e-7) ≤ M + 7e-7 := by nlinarith
  linarith

/-- **Theorem 6 bracket at the Section 5.4 range**: at most the main term plus `10⁻⁶`. -/
theorem thm6Bracket_le {α g ε C₁ τ cGv X₂ N : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 0.0024548)
    (hg1 : 1.78103 ≤ g) (hg2 : g ≤ 1.781081) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8137)
    (hC0 : 0 ≤ C₁) (hC : C₁ ≤ 112) (hτ : 0.65 ≤ τ) (hc : cGv ≤ 0.429)
    (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    thm6Bracket α g ε C₁ τ cGv X₂ N ≤ thm6Main α g ε C₁ + 1e-6 := by
  obtain ⟨hd0, hd⟩ := delta_le hX
  have hL := logX2_ge hX
  have hX0 : 0 < X₂ := lt_of_lt_of_le (exp_pos _) hX
  have hlN : (100000 : ℝ) ≤ log N := le_trans hL (log_le_log hX0 hN)
  have h1 := l1T6_le hα0 hα hg1 hg2 hε0 hε hC0 hC hX
  have h2 := l2T6_le hg1 hτ hc hL
  have h3 := l3T6_le hα0 hα hg2 (by linarith) hε0 hε hC0 hC hc hd0 hd
  have hT2 : l2T6 g τ cGv X₂ / log N ^ (4 - 3 : ℕ) ≤ 2e-7 := by
    rw [show (4 - 3 : ℕ) = 1 from rfl, pow_one, div_le_iff₀ (by linarith)]
    nlinarith
  have hT3 : l3T6 α g ε C₁ cGv X₂ / log N ^ (4 - 1 : ℕ) ≤ 1e-8 := by
    have h3' : (1e15 : ℝ) ≤ log N ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hlN 3; norm_num at this ⊢; linarith
    rw [show (4 - 1 : ℕ) = 3 from rfl, div_le_iff₀ (by linarith)]
    nlinarith
  unfold thm6Bracket
  linarith

/-- The second piece of `K3` is exactly `4 · thm6Main`. -/
theorem K3_second (α g ε C₁ C₂ cb : ℝ) : K3 α g ε C₁ C₂ cb = 8 * thm5Main α g ε C₂
    - 4 * thm6Main α g ε C₁
    - 1 / 2 * ((2 * g / (1 / 2 - α) + 3 * ε * C₁) * cb) := by
  unfold K3 thm5Main thm6Main; ring

/-- At the Section 5.4 parameters, with `g = e^γ`, `C₁ = 112`, `τ` the twin prime constant
and `c_G(X₂) ≤ 0.429`: the Theorem 6 bracket exceeds its main term by at most `10⁻⁶`. -/
theorem thm6Bracket_le_params {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112 LeanLab.ChenExplicit.twinC
        (cG X₂) X₂ N ≤ thm6Main α0 (exp eulerMascheroniConstant) (1 / 8137) 112 + 1e-6 := by
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
  exact thm6Bracket_le (le_trans (by norm_num) alpha_ge) alpha_le hg1 hg2 (by norm_num)
    le_rfl (by norm_num) le_rfl hτ (cG_le_all X₂ h4) hX hN

/-- `theorem3_main` with the exact Theorem 5 and Theorem 6 brackets in place of their main
terms, weights `8` and `1/2 · 8` as in `K3`: the margin stays above `0.0015 - 8·10⁻⁸ - 4·10⁻⁶`.
Theorems 5 and 6 themselves, and Theorem 7's term, stay cited. -/
theorem theorem3_main_thm56 {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    (0.0015 - 8e-8 - 4e-6 : ℝ) <
      K3 α0 (exp eulerMascheroniConstant) (1 / 8137) 112 114 LeanLab.ChenExplicit.BJS.cbar
      - 8 * thm5Main α0 (exp eulerMascheroniConstant) (1 / 8137) 114
      + 8 * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
      + 4 * thm6Main α0 (exp eulerMascheroniConstant) (1 / 8137) 112
      - 4 * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N := by
  have h1 := theorem3_main_thm5 hX hN
  have h2 := thm6Bracket_le_params hX hN
  linarith


end LeanLab.BS2022GRH
