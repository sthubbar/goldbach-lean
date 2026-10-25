module

public import LeanLab.DensityGoldbach.U1481Assemble

/-!
Unit U-1484, run 20261022T1302Z-31860. P0047 Alsetri and Shao 2024, Theorem 1.2.

The deterministic half of `ArcClassBound` of U1478Arcs. For `W = z#`, `θ = -r/(WN)`, `0 < r < N`,
levels `P, Q` with `W ≤ Q + 1`: either every `α_k = k/W + θ` is on the lab's minor arcs
`MinorAt P Q`, or one `α_k` is within `1/(q(Q + 1))` of some `a/q`, `q ≤ P`; then
`ρ = a/q - k/W` has every `k'/W + ρ` of denominator at most `W P`, `θ = ρ + β` with
`|β| ≤ 1/(Q + 1)`, and the major arc assembly of U-1481 applies to every `k'` at once. When
`den ρ ∣ W` the window `-1/W < θ < 0` forces `ρ ∈ {0, -1/W}` and `V_period`, or its conjugate,
bounds `V(β)` by `W`.

* `twS_explicit`, PROVED: given any uniform major arc error `E` for moduli `q ≤ W P` and
  `|β| ≤ 1/(Q + 1)`, `‖twS‖ ≤ W Mb + W/φ(W) (X/z + W) + W E`, `Mb` the lab's `minor_sup` bound.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
noncomputable section
namespace LeanLab.DensityGoldbach.U1484

open LeanLab.DensityGoldbach.U1478 LeanLab.DensityGoldbach.U1481

local notation "eL" => LeanLab.PNTPort.LargeSieve.e
local notation "SV" => LeanLab.PNTPort.Vinogradov.S
local notation "VV" => LeanLab.PNTPort.Vinogradov.V

/-- The lab's `minor_sup` bound at length `X`. -/
def Mb (X P Q : ℕ) : ℝ :=
  300 * ((X : ℝ) / Real.sqrt P + (X : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (X * Q)) *
    (1 + Real.log X) ^ 4

lemma Mb_nonneg (X P Q : ℕ) : 0 ≤ Mb X P Q := by
  unfold Mb
  have := Real.log_natCast_nonneg X
  positivity

/-- Trivial bound `‖V(X, β)‖ ≤ X`. -/
theorem norm_V_le (X : ℕ) (β : ℝ) : ‖VV X β‖ ≤ X := by
  unfold LeanLab.PNTPort.Vinogradov.V
  refine (norm_sum_le _ _).trans ?_
  simp [LeanLab.PNTPort.LargeSieve.norm_e]

/-- `‖V(X, -β)‖ = ‖V(X, β)‖`. -/
theorem norm_V_neg (X : ℕ) (β : ℝ) : ‖VV X (-β)‖ = ‖VV X β‖ := by
  have : VV X (-β) = (starRingEnd ℂ) (VV X β) := by
    unfold LeanLab.PNTPort.Vinogradov.V
    rw [map_sum]; refine sum_congr rfl fun n _ => ?_
    rw [mul_neg, LeanLab.PNTPort.LargeSieve.e_neg]
  rw [this, Complex.norm_conj]

/-- **Conjugate period bound**: `‖V(X, 1/W - r/(WN))‖ ≤ W` for `0 < r < N`. -/
theorem V_period_conj {W b N r : ℕ} (hW : 0 < W) (hb : b < W) (hr : 0 < r) (hrN : r < N) :
    ‖VV (Xc W b N) (-((r : ℝ) / (W * N)) + 1 / W)‖ ≤ W := by
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h := V_period (W := W) (b := b) (N := N) (r := N - r) hW hb (by omega) (by omega)
  have he : -((r : ℝ) / (W * N)) + 1 / W = -(-(((N - r : ℕ) : ℝ) / (W * N))) := by
    rw [Nat.cast_sub hrN.le]; field_simp; ring
  rw [he, norm_V_neg]; exact h

/-- **`den ρ ∣ W` forces `ρ ∈ {0, -1/W}`** when `ρ` is within `1/W` of `θ ∈ (-1/W, 0)`. -/
theorem rho_of_dvd {W : ℕ} (hW : 0 < W) {ρ : ℚ} (hd : ρ.den ∣ W) {θ : ℝ}
    (hθ0 : θ < 0) (hθ1 : -(1 / (W : ℝ)) < θ) (hclose : |θ - ρ| ≤ 1 / W) :
    (ρ : ℝ) = 0 ∨ (ρ : ℝ) = -(1 / (W : ℝ)) := by
  obtain ⟨t, ht⟩ := hd
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hden : (ρ.den : ℝ) ≠ 0 := by exact_mod_cast ρ.den_nz
  set m : ℤ := ρ.num * t
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; omega
    exact_mod_cast this
  have hρ : (ρ : ℝ) = m / W := by
    have hm : (m : ℝ) = ρ.num * t := by simp [m]
    rw [Rat.cast_def, hm, ht]
    push_cast
    rw [mul_div_mul_right _ _ ht0]
  rw [hρ] at hclose ⊢
  rw [abs_le] at hclose
  have h1 : (-2 : ℝ) < m := by
    have : -(1 / (W : ℝ)) - 1 / W < (m : ℝ) / W := by linarith [hclose.2]
    rw [lt_div_iff₀ hWr] at this
    have e : (-(1 / (W : ℝ)) - 1 / W) * W = -2 := by field_simp; ring
    linarith
  have h2 : (m : ℝ) < 1 := by
    have : (m : ℝ) / W < 1 / W := by linarith [hclose.1]
    rw [div_lt_div_iff_of_pos_right hWr] at this
    exact this
  have h1' : (-2 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  rcases (show m = 0 ∨ m = -1 by omega) with h | h
  · left; rw [h]; simp
  · right; rw [h]; push_cast; ring

/-- Minor or major: either every `α_k` is minor, or one is close to a fraction of small
denominator. -/
theorem minor_or_major (W P Q : ℕ) (θ : ℝ) :
    (∀ k < W, LeanLab.PNTPort.Vinogradov.MinorAt P Q ((k : ℝ) / W + θ)) ∨
    ∃ k : ℕ, k < W ∧ ∃ a : ℤ, ∃ q : ℕ, 1 ≤ q ∧ q ≤ P ∧
      |(k : ℝ) / W + θ - a / q| ≤ 1 / ((q : ℝ) * (Q + 1)) := by
  by_cases h : ∀ k < W, LeanLab.PNTPort.Vinogradov.MinorAt P Q ((k : ℝ) / W + θ)
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨k, hk, hm⟩ := h
    unfold LeanLab.PNTPort.Vinogradov.MinorAt at hm
    push Not at hm
    obtain ⟨a, q, h1, h2, h3⟩ := hm
    exact ⟨k, hk, a, q, h1, h2, h3⟩

lemma den_divq_dvd' (a : ℤ) (b : ℕ) : ((a : ℚ) / b).den ∣ b := den_divq_dvd a b

/-- The denominators of the shifted fractions. -/
theorem den_shift_le {W P : ℕ} (hW : 0 < W) (k k' : ℕ) (a : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (hqP : q ≤ P) : ((k' : ℚ) / W + ((a : ℚ) / q - (k : ℚ) / W)).den ≤ W * P := by
  have hx : (k' : ℚ) / W + ((a : ℚ) / q - (k : ℚ) / W) =
      ((((k' : ℤ) - k) * q + a * W : ℤ) : ℚ) / ((q * W : ℕ) : ℚ) := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hW0 : (W : ℚ) ≠ 0 := by exact_mod_cast hW.ne'
    push_cast; field_simp; ring
  rw [hx]
  refine (Nat.le_of_dvd (by positivity) (den_divq_dvd' _ _)).trans ?_
  rw [mul_comm]; exact Nat.mul_le_mul_left W hqP

lemma isCoprime_num_den (x : ℚ) : IsCoprime x.num (x.den : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have := x.reduced
  rw [Int.gcd]; simpa using this

/-- **The explicit twisted sum bound**: for `W = z#`, levels `P, Q`, and a uniform major arc
error `E` for moduli `q ≤ W P` and shifts `|β| ≤ 1/(Q + 1)`,
`‖twS‖ ≤ W Mb + W/φ(W) (X/z + W) + W E`. -/
theorem twS_explicit {z b N r P Q : ℕ} (hz1 : 1 ≤ z) (hblt : b < primorial z)
    (hb : Nat.Coprime b (primorial z)) (hr : 0 < r) (hrN : r < N) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hQX : Q ≤ Xc (primorial z) b N) (hWQ : (primorial z : ℝ) ≤ Q + 1) {E : ℝ} (hE0 : 0 ≤ E)
    (hmaj : ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ primorial z * P → IsCoprime a (q : ℤ) →
      ∀ β : ℝ, |β| ≤ 1 / ((Q : ℝ) + 1) →
        ‖SV (Xc (primorial z) b N) (a / q + β) - gμ q * VV (Xc (primorial z) b N) β‖ ≤ E) :
    ‖twS (primorial z) b N r‖ ≤ primorial z * Mb (Xc (primorial z) b N) P Q +
      (primorial z : ℝ) / Nat.totient (primorial z) *
        ((Xc (primorial z) b N : ℝ) / z + primorial z) + primorial z * E := by
  set W := primorial z with hWdef
  set X := Xc W b N with hXdef
  have hW : 0 < W := primorial_pos z
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  have hMb := Mb_nonneg X P Q
  have hMbW : 0 ≤ (W : ℝ) * Mb X P Q := by positivity
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz1
  have hT0 : 0 ≤ (W : ℝ) / Nat.totient W * ((X : ℝ) / z + W) := by positivity
  set θ : ℝ := -((r : ℝ) / (W * N)) with hθdef
  rcases minor_or_major W P Q θ with hmin | ⟨k, hk, a, q, hq1, hqP, hclose⟩
  · -- all minor
    have hmin' : ∀ k < W,
        LeanLab.PNTPort.Vinogradov.MinorAt P Q ((k : ℝ) / W - (r : ℝ) / (W * N)) := by
      intro k hk; have := hmin k hk; rwa [hθdef, ← sub_eq_add_neg] at this
    have h := twS_minor (b := b) (N := N) hP hQ hQX hmin'
    have : ‖twS W b N r‖ ≤ W * Mb X P Q := h
    have : 0 ≤ (W : ℝ) * E := by positivity
    linarith
  · -- one major point
    set ρ : ℚ := (a : ℚ) / q - (k : ℚ) / W with hρdef
    set β : ℝ := θ - ρ with hβdef
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hρr : (ρ : ℝ) = (a : ℝ) / q - (k : ℝ) / W := by rw [hρdef]; push_cast; ring
    have hβ : |β| ≤ 1 / ((Q : ℝ) + 1) := by
      have e : β = (k : ℝ) / W + θ - a / q := by rw [hβdef, hρr]; ring
      rw [e]
      refine hclose.trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hθ : θ = (ρ : ℝ) + β := by rw [hβdef]; ring
    have hE : ∀ k' < W, ‖SV X ((((k' : ℚ) / W + ρ : ℚ) : ℝ) + β) -
        gμ (((k' : ℚ) / W + ρ).den) * VV X β‖ ≤ E := by
      intro k' _
      set x : ℚ := (k' : ℚ) / W + ρ
      have hx : ((x : ℚ) : ℝ) = (x.num : ℝ) / (x.den : ℕ) := by rw [Rat.cast_def]
      rw [hx]
      exact hmaj x.num x.den x.pos (den_shift_le hW k k' a hq1 hqP) (isCoprime_num_den x) β hβ
    have hWQ' : 1 / ((Q : ℝ) + 1) ≤ 1 / W := one_div_le_one_div_of_le hWr hWQ
    by_cases hd : ρ.den ∣ W
    · have hmajor := twS_major (b := b) ρ β hθ hE
      rw [norm_coefSum_dvd (squarefree_primorial z) hb hd] at hmajor
      have hmajor' : ‖twS W b N r‖ ≤ (W : ℝ) / Nat.totient W * ‖VV X β‖ + W * E := hmajor
      have hθ0 : θ < 0 := by
        rw [hθdef]; have : (0 : ℝ) < r := by exact_mod_cast hr
        have : 0 < (r : ℝ) / (W * N) := by positivity
        linarith
      have hθ1 : -(1 / (W : ℝ)) < θ := by
        rw [hθdef, neg_lt_neg_iff, div_lt_div_iff₀ (by positivity) hWr]
        have : (r : ℝ) < N := by exact_mod_cast hrN
        nlinarith
      have hcl : |θ - ρ| ≤ 1 / W := by
        have : θ - ρ = β := by rw [hβdef]
        rw [this]; exact hβ.trans hWQ'
      have hV : ‖VV X β‖ ≤ W := by
        rcases rho_of_dvd hW hd hθ0 hθ1 hcl with h0 | h1
        · have : β = θ := by rw [hβdef, h0, sub_zero]
          rw [this, hθdef]; exact V_period hW hblt hr hrN
        · have : β = -((r : ℝ) / (W * N)) + 1 / W := by rw [hβdef, h1, hθdef]; ring
          rw [this]; exact V_period_conj hW hblt hr hrN
      have h1 : (W : ℝ) / Nat.totient W * ‖VV X β‖ ≤
          (W : ℝ) / Nat.totient W * ((X : ℝ) / z + W) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 0 ≤ (X : ℝ) / z := by positivity
        linarith
      linarith
    · have hmajor := twS_major_not_dvd (b := b) (N := N) hz1 hb ρ hd β (by rw [← hθdef]; exact hθ)
        hE
      have h1 : (W : ℝ) / Nat.totient W / z * ‖VV X β‖ ≤
          (W : ℝ) / Nat.totient W * ((X : ℝ) / z + W) := by
        have hV := norm_V_le X β
        have e : (W : ℝ) / Nat.totient W / z * ‖VV X β‖ =
            (W : ℝ) / Nat.totient W * (‖VV X β‖ / z) := by ring
        rw [e]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : ‖VV X β‖ / z ≤ (X : ℝ) / z := div_le_div_of_nonneg_right hV hzr.le
        linarith
      have hmajor' : ‖twS W b N r‖ ≤ (W : ℝ) / Nat.totient W / z * ‖VV X β‖ + W * E := hmajor
      linarith

end LeanLab.DensityGoldbach.U1484

