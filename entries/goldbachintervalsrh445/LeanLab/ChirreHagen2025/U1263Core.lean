module

public import Mathlib
public import LeanLab.ChirreHagen2025.Lemma24
public import LeanLab.ChirreHagen2025.Lemma26BPT

/-!
P0075 line, T2, unit U-1263, run 20261020T1803Z-21834, 2026-10-20.
Core lemmas for a sharper diagonal bound `Σ |c_γ|² log |γ| ≤ C δ log²(2.0001/δ)`:
Taylor bounds for `cos` to degree 6, the exact size of `|(1+δ)^ρ - 1|²`, pointwise
majorants of `|c_γ|²` on intervals of `|γ|` (using the periodicity of `cos`), and the
interval sums by counts from `BPTN` (Brent-Platt-Trudgian Lemma 1).
CONDITIONAL ON `Lemma26B.BPTN γ` and `Ordinates14 γ` where stated; no other inputs.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.U1263
open Real

/-! ### Taylor bounds for `cos` and `sin` -/

lemma cos_le_four_nonneg {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t
  have hd : ∀ t, HasDerivAt f (-t + t ^ 3 / 6 + sin t) t := by
    intro t
    have := ((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 t).div_const 24)).sub (hasDerivAt_cos t)
    convert this using 1; push_cast; ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      have := sin_ge_sub_cube (le_of_lt ht)
      linarith
  have := hm (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [f] at this
  simp at this
  linarith

lemma cos_le_four (x : ℝ) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  rcases le_total 0 x with hx | hx
  · exact cos_le_four_nonneg hx
  · have := cos_le_four_nonneg (neg_nonneg.mpr hx)
    rw [cos_neg] at this
    have e2 : (-x) ^ 2 = x ^ 2 := by ring
    have e4 : (-x) ^ 4 = x ^ 4 := by ring
    rw [e2, e4] at this; exact this

lemma sin_le_five {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - sin t
  have hd : ∀ t, HasDerivAt f (1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t) t := by
    intro t
    have := ((((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
      ((hasDerivAt_pow 5 t).div_const 120))).sub (hasDerivAt_sin t)
    convert this using 1; push_cast; ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hd t).deriv]
      have := cos_le_four t
      linarith
  have := hm (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [f] at this
  simp at this
  linarith

lemma cos_ge_six_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  let f : ℝ → ℝ := fun t => cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hd : ∀ t, HasDerivAt f (-sin t + (t - t ^ 3 / 6 + t ^ 5 / 120)) t := by
    intro t
    have := (hasDerivAt_cos t).sub ((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 t).div_const 24) |>.sub ((hasDerivAt_pow 6 t).div_const 720))
    convert this using 1; push_cast; ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      have := sin_le_five (le_of_lt ht)
      linarith
  have := hm (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [f] at this
  simp at this
  linarith

/-- `1 - cos x ≤ x²/2 - x⁴/24 + x⁶/720` for every real `x`. -/
lemma one_sub_cos_le (x : ℝ) : 1 - cos x ≤ x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 := by
  rcases le_total 0 x with hx | hx
  · have := cos_ge_six_nonneg hx; linarith
  · have := cos_ge_six_nonneg (neg_nonneg.mpr hx)
    rw [cos_neg] at this
    have e2 : (-x) ^ 2 = x ^ 2 := by ring
    have e4 : (-x) ^ 4 = x ^ 4 := by ring
    have e6 : (-x) ^ 6 = x ^ 6 := by ring
    rw [e2, e4, e6] at this; linarith

/-! ### The size of `c_γ` -/

open Complex in
lemma c_sq_le {ι : Type*} (γ : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ι) (hγ : γ i ≠ 0) :
    ‖SmoothT2.cδ γ δ i‖ ^ 2 ≤
      (δ ^ 2 / 4 + 2 * (1 + δ / 2) * (1 - Real.cos (|γ i| * Real.log (1 + δ)))) / γ i ^ 2 := by
  have ha : (0 : ℝ) < 1 + δ := by linarith
  set l := Real.log (1 + δ) with hl
  set θ := γ i * l with hθ
  set r := Real.exp (l / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ^ 2 = 1 + δ := by
    rw [hr, sq, ← Real.exp_add, show l / 2 + l / 2 = l by ring, hl, Real.exp_log ha]
  have key : ((1 + δ : ℝ) : ℂ) ^ SmoothT2.rho γ i
      = ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), ← ofReal_log ha.le]
    unfold SmoothT2.rho
    have e : ((Real.log (1 + δ) : ℝ) : ℂ) * (1 / 2 + (γ i : ℂ) * I)
        = ((l / 2 : ℝ) : ℂ) + ((θ : ℝ) : ℂ) * I := by
      rw [hθ, hl]; push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  have hnum : ‖((1 + δ : ℝ) : ℂ) ^ SmoothT2.rho γ i - 1‖ ^ 2
      = (r - 1) ^ 2 + 2 * r * (1 - Real.cos θ) := by
    rw [key]
    have e : ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I - 1
        = ((r * Real.cos θ - 1 : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hden : ‖SmoothT2.rho γ i‖ ^ 2 = 1 / 4 + γ i ^ 2 := by
    unfold SmoothT2.rho
    have e : (1 / 2 : ℂ) + (γ i : ℂ) * I = ((1 / 2 : ℝ) : ℂ) + ((γ i : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]; ring
  have hc : ‖SmoothT2.cδ γ δ i‖ ^ 2
      = ((r - 1) ^ 2 + 2 * r * (1 - Real.cos θ)) / (1 / 4 + γ i ^ 2) := by
    unfold SmoothT2.cδ
    rw [norm_div, div_pow, hnum, hden]
  have hr1 : 1 ≤ r := by nlinarith
  have hrd : r - 1 ≤ δ / 2 := by nlinarith
  have hcos : Real.cos θ = Real.cos (|γ i| * l) := by
    rw [← Real.cos_abs θ, hθ, abs_mul, abs_of_nonneg (Real.log_nonneg (by linarith))]
  rw [hc, ← hcos]
  have hg2 : 0 < γ i ^ 2 := by positivity
  have h1c : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hn : (r - 1) ^ 2 + 2 * r * (1 - Real.cos θ)
      ≤ δ ^ 2 / 4 + 2 * (1 + δ / 2) * (1 - Real.cos θ) := by
    have : (r - 1) ^ 2 ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hrd 2
    have : 2 * r * (1 - Real.cos θ) ≤ 2 * (1 + δ / 2) * (1 - Real.cos θ) := by
      apply mul_le_mul_of_nonneg_right _ h1c; linarith
    nlinarith
  have hn0 : 0 ≤ (r - 1) ^ 2 + 2 * r * (1 - Real.cos θ) := by positivity
  calc ((r - 1) ^ 2 + 2 * r * (1 - Real.cos θ)) / (1 / 4 + γ i ^ 2)
      ≤ ((r - 1) ^ 2 + 2 * r * (1 - Real.cos θ)) / γ i ^ 2 :=
        div_le_div_of_nonneg_left hn0 hg2 (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right hn hg2.le

/-! ### Pointwise majorants on intervals of `|γ|` -/

section Pieces
variable {ι : Type*} {γ : ι → ℝ}
open LeanLab.ChirreHagen2025.SmoothT2 (cδ Ordinates14)

lemma log_one_add_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) :
    δ * (1 - 1 / 10 ^ 13) ≤ Real.log (1 + δ) ∧ Real.log (1 + δ) ≤ δ := by
  have ha : 0 < 1 + δ := by linarith
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos ha
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    rw [e] at h
    refine le_trans ?_ h
    rw [le_div_iff₀ ha]
    nlinarith
  · have := Real.log_le_sub_one_of_pos ha; linarith

/-- With `A/δ < |γ| ≤ B/δ`, the phase `t = |γ| log(1+δ)` lies in `(A(1 - 10^-13), B]` and
`t ≤ |γ| δ`. -/
lemma phase_range {δ A B g : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hA : 0 ≤ A)
    (hg1 : A / δ < g) (hg2 : g ≤ B / δ) :
    A * (1 - 1 / 10 ^ 13) < g * Real.log (1 + δ) ∧ g * Real.log (1 + δ) ≤ B ∧
      g * Real.log (1 + δ) ≤ g * δ := by
  obtain ⟨h1, h2⟩ := log_one_add_bounds hδ hδ1
  have hg0 : 0 < g := lt_of_le_of_lt (div_nonneg hA hδ.le) hg1
  have hgA : A < g * δ := by rwa [div_lt_iff₀ hδ] at hg1
  have hgB : g * δ ≤ B := by rwa [le_div_iff₀ hδ] at hg2
  have h3 : g * Real.log (1 + δ) ≤ g * δ := mul_le_mul_of_nonneg_left h2 hg0.le
  refine ⟨?_, by linarith, h3⟩
  have : g * (δ * (1 - 1 / 10 ^ 13)) ≤ g * Real.log (1 + δ) := mul_le_mul_of_nonneg_left h1 hg0.le
  have hc : (0 : ℝ) < 1 - 1 / 10 ^ 13 := by norm_num
  nlinarith

/-- The raw majorant: `|c|² ≤ Q δ²` when `1 - cos t ≤ u` on the phase range. -/
lemma pt_raw {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (h14 : Ordinates14 γ)
    (A B Q u : ℝ) (hA : 1 ≤ A)
    (hu : ∀ t, A * (1 - 1 / 10 ^ 13) < t → t ≤ B → 1 - Real.cos t ≤ u)
    (hQ : (1 / 10 ^ 26 + 2 * (1 + 1 / 10 ^ 13) * u) / A ^ 2 ≤ Q) :
    ∀ i, A / δ < |γ i| → |γ i| ≤ B / δ → ‖cδ γ δ i‖ ^ 2 ≤ Q * δ ^ 2 := by
  intro i hg1 hg2
  have hγ : γ i ≠ 0 := by intro h; have := h14 i; rw [h, abs_zero] at this; norm_num at this
  obtain ⟨t1, t2, _⟩ := phase_range hδ hδ1 (by linarith) hg1 hg2
  have hc := c_sq_le γ hδ i hγ
  have hu' := hu _ t1 t2
  have h1c : 0 ≤ 1 - Real.cos (|γ i| * Real.log (1 + δ)) := by
    linarith [Real.cos_le_one (|γ i| * Real.log (1 + δ))]
  have hu0 : 0 ≤ u := le_trans h1c hu'
  have hδ2 : δ ^ 2 / 4 ≤ 1 / 10 ^ 26 := by
    have : δ ^ 2 ≤ (1 / 10 ^ 13) ^ 2 := pow_le_pow_left₀ hδ.le hδ1 2
    nlinarith
  have hn : δ ^ 2 / 4 + 2 * (1 + δ / 2) * (1 - Real.cos (|γ i| * Real.log (1 + δ)))
      ≤ 1 / 10 ^ 26 + 2 * (1 + 1 / 10 ^ 13) * u := by
    have : 2 * (1 + δ / 2) * (1 - Real.cos (|γ i| * Real.log (1 + δ)))
        ≤ 2 * (1 + 1 / 10 ^ 13) * u := by
      apply mul_le_mul (by linarith) hu' h1c (by norm_num)
    linarith
  have hgA : A < |γ i| * δ := by rwa [div_lt_iff₀ hδ] at hg1
  have hA0 : 0 < A := by linarith
  have hg2' : A ^ 2 < (|γ i| * δ) ^ 2 := pow_lt_pow_left₀ hgA hA0.le (by norm_num)
  have hgi : 0 < γ i ^ 2 := by positivity
  have hsq : γ i ^ 2 = |γ i| ^ 2 := (sq_abs _).symm
  have hn0 : 0 ≤ 1 / 10 ^ 26 + 2 * (1 + 1 / 10 ^ 13) * u := by positivity
  calc ‖cδ γ δ i‖ ^ 2 ≤ _ := hc
    _ ≤ (1 / 10 ^ 26 + 2 * (1 + 1 / 10 ^ 13) * u) / γ i ^ 2 :=
        div_le_div_of_nonneg_right hn hgi.le
    _ ≤ (1 / 10 ^ 26 + 2 * (1 + 1 / 10 ^ 13) * u) / A ^ 2 * δ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hgi (by positivity)]
        rw [hsq]
        have : A ^ 2 ≤ |γ i| ^ 2 * δ ^ 2 := by rw [← mul_pow]; exact hg2'.le
        have := mul_le_mul_of_nonneg_left this hn0
        linarith
    _ ≤ Q * δ ^ 2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

/-- The normalized majorant near the origin, from `1 - cos t ≤ t²/2 - t⁴/24 + t⁶/720`. -/
lemma pt_norm {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (h14 : Ordinates14 γ)
    (A B lo Q : ℝ) (hA : 1 ≤ A) (hlo0 : 0 ≤ lo) (hlo : lo ≤ A * (1 - 1 / 10 ^ 13))
    (hQ : 2 * (1 + 1 / 10 ^ 13) * (1 / 2 - lo ^ 2 / 24 + B ^ 4 / 720) + 1 / 10 ^ 26 ≤ Q) :
    ∀ i, A / δ < |γ i| → |γ i| ≤ B / δ → ‖cδ γ δ i‖ ^ 2 ≤ Q * δ ^ 2 := by
  intro i hg1 hg2
  have hγ : γ i ≠ 0 := by intro h; have := h14 i; rw [h, abs_zero] at this; norm_num at this
  set g := |γ i| with hgdef
  set t := g * Real.log (1 + δ) with htdef
  obtain ⟨t1, t2, t3⟩ := phase_range hδ hδ1 (by linarith) hg1 hg2
  rw [← htdef] at t1 t2 t3
  have hc := c_sq_le γ hδ i hγ
  rw [← hgdef, ← htdef] at hc
  have hg14 : 14 ≤ g := h14 i
  have ht0 : 0 ≤ t := by linarith
  have hlot : lo ≤ t := by linarith
  set n := 1 / 2 - lo ^ 2 / 24 + B ^ 4 / 720 with hn
  have hbr : 1 / 2 - t ^ 2 / 24 + t ^ 4 / 720 ≤ n := by
    have a1 : lo ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hlo0 hlot 2
    have a2 : t ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ ht0 t2 4
    rw [hn]; linarith
  have hbr0 : 0 < 1 / 2 - t ^ 2 / 24 + t ^ 4 / 720 := by nlinarith [sq_nonneg (t ^ 2 - 30)]
  have hcos : 1 - Real.cos t ≤ t ^ 2 * n := by
    have := one_sub_cos_le t
    have : t ^ 2 * (1 / 2 - t ^ 2 / 24 + t ^ 4 / 720) ≤ t ^ 2 * n :=
      mul_le_mul_of_nonneg_left hbr (sq_nonneg t)
    nlinarith
  have hn0 : 0 ≤ n := by linarith
  have hgi : 0 < γ i ^ 2 := by positivity
  have hsq : γ i ^ 2 = g ^ 2 := (sq_abs _).symm
  have hg0 : 0 < g := by linarith
  have ht2 : t ^ 2 ≤ g ^ 2 * δ ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ ht0 t3 2
  have hgbig : 10 ^ 13 ≤ g := by
    have : A / δ ≥ 1 / (1 / 10 ^ 13) := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hδ]; nlinarith
    have e : (1 : ℝ) / (1 / 10 ^ 13) = 10 ^ 13 := by norm_num
    linarith
  have hg26 : 10 ^ 26 ≤ g ^ 2 := by nlinarith
  rw [hsq] at hc
  have h1c : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
  have hdd : 1 + δ / 2 ≤ 1 + 1 / 10 ^ 13 := by linarith
  calc ‖cδ γ δ i‖ ^ 2 ≤ (δ ^ 2 / 4 + 2 * (1 + δ / 2) * (1 - Real.cos t)) / g ^ 2 := hc
    _ = δ ^ 2 / 4 / g ^ 2 + 2 * (1 + δ / 2) * ((1 - Real.cos t) / g ^ 2) := by ring
    _ ≤ δ ^ 2 * (1 / 10 ^ 26) + 2 * (1 + 1 / 10 ^ 13) * (δ ^ 2 * n) := by
        gcongr
        · rw [div_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg δ]
        · rw [div_le_iff₀ (by positivity)]
          calc 1 - Real.cos t ≤ t ^ 2 * n := hcos
            _ ≤ g ^ 2 * δ ^ 2 * n := mul_le_mul_of_nonneg_right ht2 hn0
            _ = δ ^ 2 * n * g ^ 2 := by ring
    _ = (2 * (1 + 1 / 10 ^ 13) * n + 1 / 10 ^ 26) * δ ^ 2 := by ring
    _ ≤ Q * δ ^ 2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

/-- `1 - cos t ≤ 2`. -/
lemma hu_two (A B : ℝ) : ∀ t, A * (1 - 1 / 10 ^ 13) < t → t ≤ B → 1 - Real.cos t ≤ 2 :=
  fun t _ _ => by linarith [Real.neg_one_le_cos t]

/-- The shifted Taylor majorant: `1 - cos t = 1 - cos (t - 2πk)`. -/
lemma hu_poly (A B : ℝ) (k : ℕ) (plo phi : ℝ) (hplo : 0 ≤ plo)
    (hcase : (0 ≤ A * (1 - 1 / 10 ^ 13) - 2 * k * 3.141593 ∧
        plo ≤ A * (1 - 1 / 10 ^ 13) - 2 * k * 3.141593 ∧ B - 2 * k * 3.141592 ≤ phi) ∨
      (B - 2 * k * 3.141592 ≤ 0 ∧ plo ≤ -(B - 2 * k * 3.141592) ∧
        -(A * (1 - 1 / 10 ^ 13) - 2 * k * 3.141593) ≤ phi) ∨
      (plo = 0 ∧ -phi ≤ A * (1 - 1 / 10 ^ 13) - 2 * k * 3.141593 ∧
        B - 2 * k * 3.141592 ≤ phi)) :
    ∀ t, A * (1 - 1 / 10 ^ 13) < t → t ≤ B →
      1 - Real.cos t ≤ phi ^ 2 / 2 - plo ^ 4 / 24 + phi ^ 6 / 720 := by
  intro t ht1 ht2
  set φ := t - k * (2 * π) with hφ
  have hcos : Real.cos t = Real.cos φ := (Real.cos_sub_nat_mul_two_pi t k).symm
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp1 : A * (1 - 1 / 10 ^ 13) - 2 * k * 3.141593 < φ := by
    have := Real.pi_lt_d6
    have : k * (2 * π) ≤ 2 * k * 3.141593 := by nlinarith
    linarith
  have hp2 : φ ≤ B - 2 * k * 3.141592 := by
    have := Real.pi_gt_d6
    have : 2 * k * 3.141592 ≤ k * (2 * π) := by nlinarith
    linarith
  have hab : plo ≤ |φ| ∧ |φ| ≤ phi := by
    rcases hcase with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [abs_of_nonneg (by linarith)]; constructor <;> linarith
    · rw [abs_of_nonpos (by linarith)]; constructor <;> linarith
    · constructor
      · rw [h0]; exact abs_nonneg _
      · rw [abs_le]; constructor <;> linarith
  obtain ⟨hl, hh⟩ := hab
  have e2 : φ ^ 2 = |φ| ^ 2 := (sq_abs φ).symm
  have e4 : φ ^ 4 = |φ| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
  have e6 : φ ^ 6 = |φ| ^ 6 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, pow_mul, sq_abs]
  have a2 : |φ| ^ 2 ≤ phi ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have a4 : plo ^ 4 ≤ |φ| ^ 4 := pow_le_pow_left₀ hplo hl 4
  have a6 : |φ| ^ 6 ≤ phi ^ 6 := pow_le_pow_left₀ (abs_nonneg _) hh 6
  have := one_sub_cos_le φ
  rw [hcos]
  linarith

end Pieces

/-! ### Sums over intervals by counts -/

section Sums
variable {ι : Type*} {γ : ι → ℝ}
open LeanLab.ChirreHagen2025.SmoothT2 (cδ Ordinates14)
open LeanLab.ChirreHagen2025.Lemma26B (BPTN Mt Rt M_diff R_sum c_lower part1 part2 log_1e13)

lemma log_le_dyadic (B : ℝ) (j : ℕ) (hB : 0 < B) :
    Real.log B ≤ j * 0.6931471808 + (B / 2 ^ j - 1) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have e : B = 2 ^ j * (B / 2 ^ j) := by field_simp
  have hq : 0 < B / 2 ^ j := div_pos hB h2
  rw [e, Real.log_mul h2.ne' hq.ne', Real.log_pow, ← e]
  have := Real.log_two_lt_d9
  have := Real.log_le_sub_one_of_pos hq
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

lemma Lam_ge {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) : 29.8 ≤ Real.log (1 / δ) := by
  have h : (10 : ℝ) ^ 13 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; linarith
  exact log_1e13.trans (Real.log_le_log (by positivity) h)

lemma log_div_delta {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    Real.log (B / δ) = Real.log B + Real.log (1 / δ) := by
  rw [div_eq_mul_one_div B δ, Real.log_mul hB.ne' (by positivity)]

/-- `δ (log(1/δ) + 5)² ≤ 10^-5` for `δ ≤ 10^-13`. -/
lemma small_E {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) :
    δ * (Real.log (1 / δ) + 5) ^ 2 ≤ 1 / 10 ^ 5 := by
  set T := 1 / δ with hT
  have hT13 : (10 : ℝ) ^ 13 ≤ T := by
    rw [hT, le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; linarith
  have hT0 : 0 < T := by positivity
  set u := T ^ (1 / 4 : ℝ)
  have hu0 : 0 < u := by positivity
  have hu4 : u ^ 4 = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hlog : Real.log T = 4 * Real.log u := by rw [← hu4, Real.log_pow]; norm_num
  have hlu : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
  have hu : (1700 : ℝ) ≤ u := by
    by_contra h; push_neg at h
    have : u ^ 4 < 1700 ^ 4 := by gcongr
    norm_num at this; linarith
  have hlu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hd : δ = 1 / T := by rw [hT]; field_simp
  have key : (Real.log T + 5) ^ 2 ≤ T / 10 ^ 5 := by
    rw [hlog, ← hu4]
    have h1 : 4 * Real.log u + 5 ≤ 5 * u := by linarith
    have h2 : (4 * Real.log u + 5) ^ 2 ≤ (5 * u) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : (5 * u) ^ 2 ≤ u ^ 4 / 10 ^ 5 := by
      have : 25 * 10 ^ 5 ≤ u ^ 2 := by nlinarith
      nlinarith [sq_nonneg u]
    linarith
  rw [hd, one_div_mul_eq_div, div_le_iff₀ hT0]
  linarith

/-- The head: `Σ_{|γ| ≤ 1/δ} |c|² log |γ| ≤ δ log²(1/δ)/π`. -/
lemma head_sum (hN : BPTN γ) (h14 : Ordinates14 γ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 10 ^ 13) (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => |γ i| ≤ 1 / δ), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ 0.31831 * (δ * Real.log (1 / δ) ^ 2) := by
  have hT13 : (10 : ℝ) ^ 13 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; linarith
  have hp := part1 hN hT13 s
  have hlog : ∀ i, 0 ≤ Real.log |γ i| := fun i => Real.log_nonneg (by linarith [h14 i])
  have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ 1 / δ), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ δ ^ 2 * ∑ i ∈ s.filter (fun i => |γ i| ≤ 1 / δ), Real.log |γ i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hlog i)
    exact pow_le_pow_left₀ (norm_nonneg _) (SmoothT2.coef_le_delta hδ γ i) 2
  have hpi := Real.pi_gt_d6
  have h2 : δ ^ 2 * (1 / δ * Real.log (1 / δ) ^ 2 / π) = δ * Real.log (1 / δ) ^ 2 / π := by
    field_simp
  have h3 : δ * Real.log (1 / δ) ^ 2 / π ≤ 0.31831 * (δ * Real.log (1 / δ) ^ 2) := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ δ * Real.log (1 / δ) ^ 2 := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_left hp (sq_nonneg δ)
  linarith

/-- The tail: `Σ_{|γ| > X/δ} |c|² log |γ| ≤ ℓ² · 1.028 δ log²(X/δ)/(π X)`. -/
lemma tail_sum (hN : BPTN γ) (h14 : Ordinates14 γ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 10 ^ 13) (X lamX : ℝ) (hX : 1 ≤ X) (hlX : Real.log X ≤ lamX)
    (hl0 : 0 ≤ lamX) (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => X / δ < |γ i|), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ 0.31831 * 4.00041 * 1.028 / X * (δ * Real.log (1 / δ) ^ 2
        + 2 * lamX * (δ * Real.log (1 / δ)) + lamX ^ 2 * δ) := by
  set T := X / δ with hT
  have hT13 : (10 : ℝ) ^ 13 ≤ T := by
    rw [hT, le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; nlinarith
  have hp := part2 hN hT13 s
  have hf : s.filter (fun i => X / δ < |γ i|) = s.filter (fun i => ¬ |γ i| ≤ T) := by
    apply Finset.filter_congr; intro i _; rw [not_le]
  rw [hf]
  have hlog : ∀ i, 0 ≤ Real.log |γ i| := fun i => Real.log_nonneg (by linarith [h14 i])
  have hl2 : Local36.ell δ ^ 2 ≤ 4.00041 := by
    have hs : √(1 + δ) ≤ 1.0001 := by
      rw [show (1.0001 : ℝ) = √(1.0001 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h0 : 0 ≤ Local36.ell δ := by unfold Local36.ell; positivity
    have : Local36.ell δ ≤ 2.0001 := by unfold Local36.ell; linarith
    nlinarith
  have h1 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ 4.00041 * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), Real.log |γ i| / γ i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hγ : γ i ≠ 0 := by intro h; have := h14 i; rw [h, abs_zero] at this; norm_num at this
    have hc := SmoothT2.coef_le_ell hδ γ i hγ
    have hg : 0 < |γ i| := abs_pos.mpr hγ
    have hc2 : ‖cδ γ δ i‖ ^ 2 ≤ 4.00041 / γ i ^ 2 := by
      calc ‖cδ γ δ i‖ ^ 2 ≤ (Local36.ell δ / |γ i|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
        _ = Local36.ell δ ^ 2 / γ i ^ 2 := by rw [div_pow, sq_abs]
        _ ≤ 4.00041 / γ i ^ 2 := div_le_div_of_nonneg_right hl2 (sq_nonneg _)
    calc ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ 4.00041 / γ i ^ 2 * Real.log |γ i| :=
          mul_le_mul_of_nonneg_right hc2 (hlog i)
      _ = 4.00041 * (Real.log |γ i| / γ i ^ 2) := by ring
  have hLT : Real.log T = Real.log X + Real.log (1 / δ) := log_div_delta hδ (by linarith)
  have hΛ := Lam_ge hδ hδ1
  have hlT0 : 0 ≤ Real.log T := by rw [hLT]; have := Real.log_nonneg hX; linarith
  have hlT : Real.log T ^ 2 ≤ (lamX + Real.log (1 / δ)) ^ 2 :=
    pow_le_pow_left₀ hlT0 (by rw [hLT]; linarith) 2
  have hpi := Real.pi_gt_d6
  have hTe : π * T = π * X / δ := by rw [hT]; ring
  have h2 : 1.028 * Real.log T ^ 2 / (π * T) ≤ 1.028 * (lamX + Real.log (1 / δ)) ^ 2 * δ / (π * X) := by
    rw [hTe, div_div_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_left hlT (show (0 : ℝ) ≤ 1.028 * δ by positivity)
    nlinarith
  have h3 : 1.028 * (lamX + Real.log (1 / δ)) ^ 2 * δ / (π * X)
      ≤ 0.31831 * 1.028 / X * (δ * Real.log (1 / δ) ^ 2
        + 2 * lamX * (δ * Real.log (1 / δ)) + lamX ^ 2 * δ) := by
    have e : δ * Real.log (1 / δ) ^ 2 + 2 * lamX * (δ * Real.log (1 / δ)) + lamX ^ 2 * δ
        = δ * (lamX + Real.log (1 / δ)) ^ 2 := by ring
    rw [e]
    have hX0 : 0 < X := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hq : 0 ≤ δ * (lamX + Real.log (1 / δ)) ^ 2 := by positivity
    have : 0.31831 * 1.028 / X * (δ * (lamX + Real.log (1 / δ)) ^ 2) * (π * X)
        = 0.31831 * π * (1.028 * (lamX + Real.log (1 / δ)) ^ 2 * δ) := by
      field_simp
    rw [this]
    have hq' : 0 ≤ 1.028 * (lamX + Real.log (1 / δ)) ^ 2 * δ := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4.00041 by norm_num)
  have e2 : 0.31831 * 4.00041 * 1.028 / X * (δ * Real.log (1 / δ) ^ 2
        + 2 * lamX * (δ * Real.log (1 / δ)) + lamX ^ 2 * δ)
      = 4.00041 * (0.31831 * 1.028 / X * (δ * Real.log (1 / δ) ^ 2
        + 2 * lamX * (δ * Real.log (1 / δ)) + lamX ^ 2 * δ)) := by ring
  rw [e2]
  nlinarith

/-- One interval `A/δ < |γ| ≤ B/δ`, with `|c|² ≤ Q δ²` there, by counts from `BPTN`. -/
lemma piece_sum (hN : BPTN γ) (h14 : Ordinates14 γ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 10 ^ 13) (A B Q lam : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hlam : Real.log B ≤ lam) (hlam5 : lam ≤ 5) (hQ : 0 ≤ Q)
    (hc : ∀ i, A / δ < |γ i| → |γ i| ≤ B / δ → ‖cδ γ δ i‖ ^ 2 ≤ Q * δ ^ 2) (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => A / δ < |γ i| ∧ |γ i| ≤ B / δ), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ 0.31831 * (Q * (B - A)) * (δ * Real.log (1 / δ) ^ 2
          + (2 * lam - 1.8) * (δ * Real.log (1 / δ)) + (lam ^ 2 - 1.8 * lam) * δ)
        + 2 * Q * (δ ^ 2 * (Real.log (1 / δ) + 5) ^ 2) := by
  set T := A / δ with hT
  set t := B / δ with ht
  set Λ := Real.log (1 / δ) with hΛdef
  have hT13 : (10 : ℝ) ^ 13 ≤ T := by
    rw [hT, le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; nlinarith
  have hTt : T ≤ t := div_le_div_of_nonneg_right hAB hδ.le
  have hΛ := Lam_ge hδ hδ1
  have hB0 : 0 < B := by linarith
  have hlt : Real.log t = Real.log B + Λ := log_div_delta hδ hB0
  have hlB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hlam0 : 0 ≤ lam := le_trans hlB0 hlam
  set S := s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t) with hS
  have hterm : ∀ i ∈ S, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ Q * δ ^ 2 * (Λ + lam) := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    obtain ⟨_, h1, h2⟩ := hi
    have hg0 : 0 < |γ i| := lt_of_le_of_lt (by positivity) h1
    have hlg : Real.log |γ i| ≤ Λ + lam := by
      have := Real.log_le_log hg0 h2; linarith
    have hlg0 : 0 ≤ Real.log |γ i| := Real.log_nonneg (by linarith [h14 i])
    exact mul_le_mul (hc i h1 h2) hlg hlg0 (by positivity)
  have hsum : ∑ i ∈ S, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ (S.card : ℝ) * (Q * δ ^ 2 * (Λ + lam)) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard := hN.2 T t hT13 hTt s
  have hM := M_diff (by linarith) hTt
  have hR := R_sum hT13 hTt
  have hc1 := c_lower
  have hpi := Real.pi_gt_d6
  have hpi0 : 0 < π := Real.pi_pos
  have hdiff : t - T = (B - A) / δ := by rw [ht, hT]; ring
  have hBA : 0 ≤ B - A := by linarith
  have hcount : (S.card : ℝ) ≤ 0.31831 * ((B - A) / δ) * (Λ + lam - 1.8) + 2 * (Λ + lam) := by
    have k1 : (t - T) * (Real.log t - Real.log (2 * π)) ≤ (B - A) / δ * (Λ + lam - 1.8) := by
      rw [hdiff]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hlt]; linarith
    have k2 : 2 * (Mt t - Mt T) ≤ (t - T) * (Real.log t - Real.log (2 * π)) / π := by
      have e2 : (t - T) * (Real.log t - Real.log (2 * π)) / π =
          2 * ((t - T) * (Real.log t - Real.log (2 * π)) / (2 * π)) := by field_simp
      rw [e2]; linarith
    have k3 : (B - A) / δ * (Λ + lam - 1.8) / π ≤ 0.31831 * ((B - A) / δ) * (Λ + lam - 1.8) := by
      rw [div_le_iff₀ hpi0]
      have : 0 ≤ (B - A) / δ * (Λ + lam - 1.8) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    have k4 : (t - T) * (Real.log t - Real.log (2 * π)) / π ≤ (B - A) / δ * (Λ + lam - 1.8) / π :=
      div_le_div_of_nonneg_right k1 hpi0.le
    have hlt' : Real.log t ≤ Λ + lam := by rw [hlt]; linarith
    linarith
  have hfac : 0 ≤ Q * δ ^ 2 * (Λ + lam) := by
    have : 0 ≤ Λ + lam := by linarith
    positivity
  have hfin := mul_le_mul_of_nonneg_right hcount hfac
  have hsq : (Λ + lam) ^ 2 ≤ (Λ + 5) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hE : 2 * Q * (δ ^ 2 * (Λ + lam) ^ 2) ≤ 2 * Q * (δ ^ 2 * (Λ + 5) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg δ)
  have e : (0.31831 * ((B - A) / δ) * (Λ + lam - 1.8) + 2 * (Λ + lam)) * (Q * δ ^ 2 * (Λ + lam))
      = 0.31831 * (Q * (B - A)) * (δ * Λ ^ 2 + (2 * lam - 1.8) * (δ * Λ) + (lam ^ 2 - 1.8 * lam) * δ)
        + 2 * Q * (δ ^ 2 * (Λ + lam) ^ 2) := by
    field_simp; ring
  rw [e] at hfin
  linarith

/-- Splitting the sum. -/
lemma split_head (f : ι → ℝ) (s : Finset ι) (a : ℝ) :
    ∑ i ∈ s, f i = ∑ i ∈ s.filter (fun i => |γ i| ≤ a), f i
      + ∑ i ∈ s.filter (fun i => a < |γ i|), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ a)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr; intro i _; rw [not_le]

lemma split_tail (f : ι → ℝ) (s : Finset ι) {a b : ℝ} (hab : a ≤ b) :
    ∑ i ∈ s.filter (fun i => a < |γ i|), f i
      = ∑ i ∈ s.filter (fun i => a < |γ i| ∧ |γ i| ≤ b), f i
        + ∑ i ∈ s.filter (fun i => b < |γ i|), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun i => a < |γ i|)) (fun i => |γ i| ≤ b),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr; intro i _
  constructor
  · rintro ⟨_, h⟩; exact lt_of_not_ge h
  · intro h; exact ⟨lt_of_le_of_lt hab h, not_le.mpr h⟩

end Sums

end LeanLab.ChirreHagen2025.U1263
