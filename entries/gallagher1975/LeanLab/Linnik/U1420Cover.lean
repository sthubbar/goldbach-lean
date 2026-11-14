module

public import LeanLab.Linnik.U1412Display53

/-!
Li-Liu, arXiv 2610.15784, Section 5, proof of Proposition 5.2: the finite cover `CoverInput λ ρ`
of `U1412Display53`, from displays (47), (48), (49), (52) and compactness, read by WebFetch on
arxiv.org/html/2610.15784, 2026-10-21.

Paper: (47) for z = x + iy with 0 < u = x² + y² < 1,
  ξ = √2 s (x - u)/√(u(1-x)(1-u)),  η = √2 s y/√(u(1-x)(1-u));
(48) V_{ξ,η}(x,y) = s², Φ_{ξ,η}(z) = s √(2u(1-x)/(1-u)) - log cosh s;
(49) s = (1/2) log((1+λ)/(1-λ)), I(λ) = (1+λ)/2 log(1+λ) + (1-λ)/2 log(1-λ) = sλ - log cosh s;
(52) for |z| < 1, z ∈ D_λ iff (1 + r_λ - x)|z|² ≤ r_λ; on |z| = 1 the paper argues directly.

Here: `Il` is I(λ) of (49), `Il_eq` its second form. `pair47` is the computation (48) for the
pair (47), written ξ = c(x-u), η = cy with c = s √(2/(u(1-x)(1-u))), the same numbers.
On the unit circle two further pairs are used: (t(x-1), ty) with V = 0 for z ≠ 1, and (s, 0)
at z = 1. Outside D_λ in the closed disc one has r_λ ≤ (1 + r_λ - x)u, `ge_of_not_mem_Dl`, by the
factorisation β((1 + r - x)x² - r) = (1 - x)(x - β)(βx + r), valid since β² = r(1 + β).
The set K = {|z| ≤ 1, r_λ ≤ (1 + r_λ - x)u} is compact and every point has a pair with Φ > ρ,
so finitely many pairs cover it: `coverInput`. Then `prop52_of_moment46` is display (53)
CONDITIONAL ON `Moment46` only. The paper's hypothesis 0 < ρ is not needed for the cover.

Unit U-1420, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1420Cover

open Set Real MeasureTheory
open LeanLab.Linnik.U1412Display53

/-- (49): `s = (1/2) log((1+λ)/(1-λ))`. -/
noncomputable def sl (l : ℝ) : ℝ := (1 / 2) * Real.log ((1 + l) / (1 - l))

/-- (49): `I(λ) = (1+λ)/2 log(1+λ) + (1-λ)/2 log(1-λ)`. -/
noncomputable def Il (l : ℝ) : ℝ :=
  (1 + l) / 2 * Real.log (1 + l) + (1 - l) / 2 * Real.log (1 - l)

lemma sl_pos {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : 0 < sl l := by
  unfold sl
  have : 1 < (1 + l) / (1 - l) := by rw [one_lt_div (by linarith)]; linarith
  have := Real.log_pos this
  positivity

/-- (49), second form: `I(λ) = sλ - log cosh s`. -/
theorem Il_eq {l : ℝ} (h0 : 0 < l) (h1 : l < 1) :
    Il l = sl l * l - Real.log (Real.cosh (sl l)) := by
  have hm : 0 < 1 - l := by linarith
  have hp : 0 < 1 + l := by linarith
  set s := sl l with hs
  set a := Real.exp s with ha
  have ha0 : 0 < a := Real.exp_pos s
  have ha2 : a ^ 2 = (1 + l) / (1 - l) := by
    rw [ha, ← Real.exp_nat_mul, hs, sl]
    rw [show ((2 : ℕ) : ℝ) * (1 / 2 * Real.log ((1 + l) / (1 - l))) = Real.log ((1 + l) / (1 - l))
      by push_cast; ring]
    exact Real.exp_log (by positivity)
  have hc : Real.cosh s = ((1 - l) * a)⁻¹ := by
    rw [Real.cosh_eq, Real.exp_neg, ← ha]
    field_simp
    rw [ha2]
    field_simp
    ring
  have hlog : Real.log (Real.cosh s) = -(Real.log (1 - l) + s) := by
    rw [hc, Real.log_inv, Real.log_mul hm.ne' ha0.ne', ha, Real.log_exp]
  have hs' : s = (1 / 2) * (Real.log (1 + l) - Real.log (1 - l)) := by
    rw [hs, sl, Real.log_div hp.ne' hm.ne']
  rw [hlog, Il, hs']
  ring

lemma sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- (50): `β_λ² = r_λ (1 + β_λ)`. -/
lemma bl_sq (l : ℝ) : bl l ^ 2 = rl l * bl l + rl l := by
  have hr : 0 ≤ rl l := by unfold rl; positivity
  have hS := Real.sq_sqrt (show 0 ≤ rl l ^ 2 + 4 * rl l by positivity)
  unfold bl
  linear_combination (1 / 4 : ℝ) * hS

lemma bl_pos {l : ℝ} (h0 : 0 < l) : 0 < bl l := by
  have hr : 0 < rl l := by unfold rl; positivity
  unfold bl
  have := Real.sqrt_nonneg (rl l ^ 2 + 4 * rl l)
  linarith

/-- (52) on the closed disc: a point of the closed unit disc outside `D_λ` has
`r_λ ≤ (1 + r_λ - x) u`. -/
theorem ge_of_not_mem_Dl {l : ℝ} (h0 : 0 < l) {z : ℂ} (hz : ‖z‖ ≤ 1) (hD : z ∉ Dl l) :
    rl l ≤ (1 + rl l - z.re) * (z.re ^ 2 + z.im ^ 2) := by
  have hr : 0 < rl l := by unfold rl; positivity
  have hx1 : z.re ≤ 1 := (Complex.re_le_norm z).trans hz
  have hpos : 0 < 1 + rl l - z.re := by linarith
  unfold Dl at hD
  simp only [mem_ofPred_eq, not_and, not_le] at hD
  by_cases hx : z.re ≤ bl l
  · have := hD hx
    rw [div_lt_iff₀ hpos] at this
    linarith
  · push Not at hx
    have hb := bl_pos h0
    have hb2 := bl_sq l
    have hid : bl l * ((1 + rl l - z.re) * z.re ^ 2 - rl l) =
        (1 - z.re) * (z.re - bl l) * (bl l * z.re + rl l) := by
      linear_combination (z.re * (1 - z.re)) * hb2
    have h3 : 0 ≤ (1 - z.re) * (z.re - bl l) * (bl l * z.re + rl l) := by
      have : 0 ≤ bl l * z.re + rl l := by nlinarith
      have : 0 ≤ (1 - z.re) * (z.re - bl l) := mul_nonneg (by linarith) (by linarith)
      positivity
    have h4 : rl l ≤ (1 + rl l - z.re) * z.re ^ 2 := by
      rw [← hid] at h3
      have := (mul_nonneg_iff_of_pos_left hb).1 h3
      linarith
    have h5 : (1 + rl l - z.re) * z.re ^ 2 ≤ (1 + rl l - z.re) * (z.re ^ 2 + z.im ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z.im]) hpos.le
    linarith

/-- (47) and (48): the pair `ξ = c(x-u)`, `η = cy`, `c = s √(2/(u(1-x)(1-u)))` gives
`V = s²` and `ξx + ηy = c u (1-x)`, with `(c u (1-x))² = 2 s² u (1-x)/(1-u)`. -/
theorem pair47 {x y s : ℝ} (_hs : 0 ≤ s) (hu0 : 0 < x ^ 2 + y ^ 2) (hu1 : x ^ 2 + y ^ 2 < 1)
    (hx : x < 1) :
    let u := x ^ 2 + y ^ 2
    let c := s * Real.sqrt (2 / (u * (1 - x) * (1 - u)))
    V (c * (x - u)) (c * y) x y = s ^ 2 ∧
      c * (x - u) * x + c * y * y = c * (u * (1 - x)) ∧
      (c * (u * (1 - x))) ^ 2 = 2 * s ^ 2 * u * (1 - x) / (1 - u) := by
  intro u c
  have hD : 0 < u * (1 - x) * (1 - u) := by
    have : 0 < 1 - x := by linarith
    have : 0 < 1 - u := by simp only [u]; linarith
    positivity
  have hc2 : c ^ 2 = s ^ 2 * (2 / (u * (1 - x) * (1 - u))) := by
    simp only [c]; rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpoly : (1 + x) * (x - u) ^ 2 + 2 * y ^ 2 * (x - u) + (1 - x) * y ^ 2 =
      u * (1 - x) * (1 - u) := by simp only [u]; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold V
    have : ((1 + x) * (c * (x - u)) ^ 2 + 2 * y * (c * (x - u)) * (c * y) +
        (1 - x) * (c * y) ^ 2) / 2 =
        c ^ 2 * ((1 + x) * (x - u) ^ 2 + 2 * y ^ 2 * (x - u) + (1 - x) * y ^ 2) / 2 := by ring
    rw [this, hpoly, hc2]
    have : u ≠ 0 := hu0.ne'
    have : 1 - u ≠ 0 := by simp only [u]; linarith
    have : 1 - x ≠ 0 := by linarith
    field_simp
  · simp only [u]; ring
  · have h1u : (1 - u) ≠ 0 := by simp only [u]; linarith
    rw [mul_pow, hc2]
    field_simp

/-- Every point of `K` has a pair with `Φ > ρ`, for `0 < λ < 1` and `ρ < I(λ)`. -/
theorem exists_pair {l ρ : ℝ} (h0 : 0 < l) (h1 : l < 1) (hρ : ρ < Il l) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hK : rl l ≤ (1 + rl l - z.re) * (z.re ^ 2 + z.im ^ 2)) :
    ∃ p : ℝ × ℝ, ρ < Phi p.1 p.2 z := by
  set x := z.re with hxdef
  set y := z.im with hydef
  have hr : 0 < rl l := by unfold rl; positivity
  have hu1 : x ^ 2 + y ^ 2 ≤ 1 := by
    rw [← sq_norm_eq]; nlinarith [norm_nonneg z]
  have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hs := sl_pos h0 h1
  have hI := Il_eq h0 h1
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · -- interior: the pair (47)
    have hu0 : 0 < x ^ 2 + y ^ 2 := by
      by_contra hc; push Not at hc; nlinarith
    have hx : x < 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
    obtain ⟨hV, hlin, hsq⟩ := pair47 hs.le hu0 hlt hx
    set u := x ^ 2 + y ^ 2 with hu
    set c := sl l * Real.sqrt (2 / (u * (1 - x) * (1 - u))) with hc
    refine ⟨(c * (x - u), c * y), ?_⟩
    have hcnn : 0 ≤ c * (u * (1 - x)) := by
      have : 0 ≤ c := mul_nonneg hs.le (Real.sqrt_nonneg _)
      have : 0 ≤ u * (1 - x) := mul_nonneg hu0.le (by linarith)
      positivity
    -- 2u(1-x) ≥ λ²(1-u) from (52)
    have hkey : l ^ 2 * (1 - u) ≤ 2 * u * (1 - x) := by
      unfold rl at hK; nlinarith
    have hge : sl l * l ≤ c * (u * (1 - x)) := by
      have h1u : 0 < 1 - u := by linarith
      have : (sl l * l) ^ 2 ≤ (c * (u * (1 - x))) ^ 2 := by
        rw [hsq, le_div_iff₀ h1u]
        have := mul_le_mul_of_nonneg_left hkey (sq_nonneg (sl l))
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) hcnn two_ne_zero).1 this
    show ρ < c * (x - u) * z.re + c * y * z.im -
      Real.log (Real.cosh (Real.sqrt (V (c * (x - u)) (c * y) z.re z.im)))
    rw [← hxdef, ← hydef, hV, Real.sqrt_sq hs.le, hlin]
    linarith
  · by_cases hx : x < 1
    · -- unit circle, z ≠ 1: the pair (t(x-1), ty), V = 0
      set t := (|ρ| + 1) / (1 - x) with ht
      refine ⟨(t * (x - 1), t * y), ?_⟩
      have hV : V (t * (x - 1)) (t * y) x y = 0 := by
        unfold V
        have : ((1 + x) * (t * (x - 1)) ^ 2 + 2 * y * (t * (x - 1)) * (t * y) +
            (1 - x) * (t * y) ^ 2) = t ^ 2 * (1 - x) * (1 - (x ^ 2 + y ^ 2)) := by ring
        rw [this, heq]; ring
      show ρ < t * (x - 1) * z.re + t * y * z.im -
        Real.log (Real.cosh (Real.sqrt (V (t * (x - 1)) (t * y) z.re z.im)))
      rw [← hxdef, ← hydef, hV]
      simp only [Real.sqrt_zero, Real.cosh_zero, Real.log_one, sub_zero]
      have : t * (x - 1) * x + t * y * y = t * (1 - x) := by
        have : t * (x - 1) * x + t * y * y = t * ((x ^ 2 + y ^ 2) - x) := by ring
        rw [this, heq]
      rw [this, ht, div_mul_cancel₀ _ (by linarith)]
      linarith [le_abs_self ρ]
    · -- z = 1: the pair (s, 0)
      have hx' : x = 1 := le_antisymm hx1 (not_lt.1 hx)
      have hy : y = 0 := by nlinarith [sq_nonneg y]
      refine ⟨(sl l, 0), ?_⟩
      show ρ < sl l * z.re + 0 * z.im - Real.log (Real.cosh (Real.sqrt (V (sl l) 0 z.re z.im)))
      rw [← hxdef, ← hydef, hx', hy]
      have : V (sl l) 0 1 0 = sl l ^ 2 := by unfold V; ring
      rw [this, Real.sqrt_sq hs.le]
      have : sl l * l < sl l * 1 := mul_lt_mul_of_pos_left h1 hs
      linarith

/-- **The finite cover of the proof of Proposition 5.2, PROVED.** For `0 < λ < 1` and
`ρ < I(λ)`, finitely many pairs `(ξ_j, η_j)` with: every `z` of the closed unit disc outside
`D_λ` has `Φ_{ξ_j,η_j}(z) > ρ` for some `j`. -/
theorem coverInput {l ρ : ℝ} (h0 : 0 < l) (h1 : l < 1) (hρ : ρ < Il l) : CoverInput l ρ := by
  set K : Set ℂ := Metric.closedBall 0 1 ∩
    {z | rl l ≤ (1 + rl l - z.re) * (z.re ^ 2 + z.im ^ 2)} with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const (by fun_prop))
  have hcov : K ⊆ ⋃ p : ℝ × ℝ, {z : ℂ | ρ < Phi p.1 p.2 z} := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz.1
    obtain ⟨p, hp⟩ := exists_pair h0 h1 hρ hz1 hz.2
    exact mem_iUnion.2 ⟨p, hp⟩
  obtain ⟨S, hS⟩ := hKc.elim_finite_subcover (fun p : ℝ × ℝ => {z : ℂ | ρ < Phi p.1 p.2 z})
    (fun p => isOpen_lt continuous_const (continuous_Phi _ _)) hcov
  refine ⟨S, fun z hz hD => ?_⟩
  have hzK : z ∈ K := ⟨by simpa using hz, ge_of_not_mem_Dl h0 hz hD⟩
  have := hS hzK
  simp only [mem_iUnion, mem_ofPred_eq] at this
  obtain ⟨p, hp, h⟩ := this
  exact ⟨p, hp, h⟩

/-- **Proposition 5.2, display (53), CONDITIONAL ON `Moment46` only.** For `0 < λ < 1` and
`ρ < I(λ)` there is `C ≥ 0` with `meas {α ∈ [0,1] : z_L(α) ∉ D_λ} ≤ C e^{-ρL}` for all `L ≥ 1`. -/
theorem prop52_of_moment46 (hM : Moment46) {l ρ : ℝ} (h0 : 0 < l) (h1 : l < 1)
    (hρ : ρ < Il l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ Dl l}).toReal ≤ C * Real.exp (-ρ * L) :=
  prop52 hM (coverInput h0 h1 hρ)

/-- Vacuity: `I(1/2) = (1/4) log(27/16) > 0`, so `0 < ρ < I(λ)` is satisfiable. -/
theorem Il_half_pos : 0 < Il (1 / 2) := by
  have h : Il (1 / 2) = (1 / 4) * Real.log (27 / 16) := by
    rw [Il, show (27 / 16 : ℝ) = (3 / 2) ^ 3 * (1 / 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  rw [h]
  have := Real.log_pos (show (1 : ℝ) < 27 / 16 by norm_num)
  positivity

/-- Vacuity instance in the paper's range: `λ = 1/2`, `ρ = I(1/2)/2`. -/
theorem coverInput_instance : CoverInput (1 / 2) (Il (1 / 2) / 2) :=
  coverInput (by norm_num) (by norm_num) (by linarith [Il_half_pos])

end LeanLab.Linnik.U1420Cover
