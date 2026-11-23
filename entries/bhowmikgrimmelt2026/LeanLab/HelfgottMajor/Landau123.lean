module

public import Mathlib

/-!
# Landau's lemma, P0014 display 4.16

P0014, Helfgott, Major arcs for Goldbach's problem, page 36, display 4.16 cites a lemma of Landau
from Montgomery and Vaughan 2007, Lemma 6.3, which rests on their Lemma 6.2, the derivative form
of the Borel-Carathéodory inequality. This file proves both from Mathlib: the Schwarz lemma, the
Borel-Carathéodory theorem `Complex.borelCaratheodory_zero`, and the existence of primitives on
discs `DifferentiableOn.isExactOn_ball`.

AI wrote this Lean code.

* `disc_automorphism_mapsTo`: the disc automorphism moving 0 to z keeps the disc.
* `halfPlane_cayley_norm_le_one`: the Cayley map of the half plane Re < M has norm at most 1.
* `norm_deriv_le_of_re_lt`: Schwarz-Pick for maps of a disc into a half plane.
* `mv_lemma_6_2`: Montgomery and Vaughan Lemma 6.2, derivative part.
* `exists_log_on_ball`: a zero free holomorphic function on a disc has a holomorphic logarithm.
* `landau_lemma`: display 4.16.
-/

@[expose] public section


open Metric Complex

namespace LeanLab.HelfgottMajor.Landau123

/-- The disc automorphism ζ ↦ R²(ζ + z)/(R² + conj z ζ) maps the open disc of radius R about 0
into itself, and its denominator does not vanish there. Used for the Schwarz-Pick step in the
proof of Montgomery and Vaughan Lemma 6.2, cited at P0014 display 4.16. -/
lemma disc_automorphism_mapsTo {R : ℝ} (hR : 0 < R) {z ζ : ℂ} (hz : ‖z‖ < R) (hζ : ‖ζ‖ < R) :
    (R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ ≠ 0 ∧
      ‖(R : ℂ) ^ 2 * (ζ + z) / ((R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ)‖ < R := by
  have hz2 : z.re ^ 2 + z.im ^ 2 < R ^ 2 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    have : ‖z‖ ^ 2 < R ^ 2 := by gcongr
    nlinarith
  have hζ2 : ζ.re ^ 2 + ζ.im ^ 2 < R ^ 2 := by
    have h := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at h
    have : ‖ζ‖ ^ 2 < R ^ 2 := by gcongr
    nlinarith
  have hprod : 0 < (R ^ 2 - (z.re ^ 2 + z.im ^ 2)) * (R ^ 2 - (ζ.re ^ 2 + ζ.im ^ 2)) :=
    mul_pos (by linarith) (by linarith)
  have hre : ((R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ).re = R ^ 2 + (z.re * ζ.re + z.im * ζ.im) := by
    simp [← Complex.ofReal_pow]
  have him : ((R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ).im = z.re * ζ.im - z.im * ζ.re := by
    simp [← Complex.ofReal_pow]
    ring
  -- the key inequality R² ‖ζ + z‖² < ‖R² + conj z ζ‖²
  have key : R ^ 2 * ‖ζ + z‖ ^ 2 < ‖(R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre, him]
    simp only [Complex.add_re, Complex.add_im]
    nlinarith [hprod]
  have hden : (R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at key
    have : 0 ≤ R ^ 2 * ‖ζ + z‖ ^ 2 := by positivity
    nlinarith
  refine ⟨hden, ?_⟩
  have hdpos : 0 < ‖(R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_lt_iff₀ hdpos, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR]
  have h1 : (R * ‖ζ + z‖) ^ 2 < ‖(R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ‖ ^ 2 := by
    rw [mul_pow]; exact key
  have h2 : R * ‖ζ + z‖ < ‖(R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ‖ :=
    lt_of_pow_lt_pow_left₀ 2 hdpos.le h1
  calc R ^ 2 * ‖ζ + z‖ = R * (R * ‖ζ + z‖) := by ring
    _ < R * ‖(R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ‖ := by gcongr

/-- The Cayley map u ↦ (u − a)/(2M − conj a − u) of the half plane Re < M, which sends a to 0,
takes values of norm at most 1, and its denominator does not vanish. Used for the Schwarz-Pick
step in the proof of Montgomery and Vaughan Lemma 6.2, cited at P0014 display 4.16. -/
lemma halfPlane_cayley_norm_le_one {M : ℝ} {a u : ℂ} (ha : a.re < M) (hu : u.re < M) :
    (2 * M : ℂ) - (starRingEnd ℂ) a - u ≠ 0 ∧
      ‖(u - a) / ((2 * M : ℂ) - (starRingEnd ℂ) a - u)‖ ≤ 1 := by
  have hre : ((2 * M : ℂ) - (starRingEnd ℂ) a - u).re = 2 * M - a.re - u.re := by simp
  have him : ((2 * M : ℂ) - (starRingEnd ℂ) a - u).im = a.im - u.im := by simp
  have hden : (2 * M : ℂ) - (starRingEnd ℂ) a - u ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hre] at this
    simp at this
    linarith
  refine ⟨hden, ?_⟩
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre, him]
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hu)]

/-- Schwarz-Pick for maps of a disc into a half plane: if h is holomorphic on the open disc of
radius R about 0 with Re h < M there, then abs h'(z) ≤ 2 (M − Re h(z)) R / (R² − abs z ²).
This is the step behind Montgomery and Vaughan Lemma 6.2, cited at P0014 display 4.16; it is
proved from the Schwarz lemma after moving z to the centre with a disc automorphism. -/
lemma norm_deriv_le_of_re_lt {h : ℂ → ℂ} {M R : ℝ} (hR : 0 < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (hre : ∀ ζ ∈ ball (0 : ℂ) R, (h ζ).re < M)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ‖deriv h z‖ ≤ 2 * (M - (h z).re) * R / (R ^ 2 - ‖z‖ ^ 2) := by
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  set a := h z with ha
  have haM : a.re < M := hre z hz
  set ψ : ℂ → ℂ := fun ζ => (R : ℂ) ^ 2 * (ζ + z) / ((R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ)
    with hψ
  set D : ℂ := (2 * M : ℂ) - (starRingEnd ℂ) a - a with hD
  set F : ℂ → ℂ := fun ζ => (h (ψ ζ) - a) / ((2 * M : ℂ) - (starRingEnd ℂ) a - h (ψ ζ)) with hF
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hψ0 : ψ 0 = z := by
    simp only [hψ, zero_add, mul_zero, add_zero]
    field_simp
  have hψmem : ∀ ζ ∈ ball (0 : ℂ) R, ψ ζ ∈ ball (0 : ℂ) R := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ ⊢
    exact (disc_automorphism_mapsTo hR hzR hζ).2
  have hψderiv : ∀ ζ ∈ ball (0 : ℂ) R, HasDerivAt ψ
      (((R : ℂ) ^ 2 * 1 * ((R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ) -
        (R : ℂ) ^ 2 * (ζ + z) * ((starRingEnd ℂ) z * 1)) /
        ((R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ) ^ 2) ζ := by
    intro ζ hζ
    have hden := (disc_automorphism_mapsTo hR hzR (mem_ball_zero_iff.mp hζ)).1
    have h1 : HasDerivAt (fun ζ : ℂ => (R : ℂ) ^ 2 * (ζ + z)) ((R : ℂ) ^ 2 * 1) ζ :=
      ((hasDerivAt_id ζ).add_const z).const_mul _
    have h2 : HasDerivAt (fun ζ : ℂ => (R : ℂ) ^ 2 + (starRingEnd ℂ) z * ζ)
        ((starRingEnd ℂ) z * 1) ζ :=
      ((hasDerivAt_id ζ).const_mul _).const_add _
    exact h1.div h2 hden
  have hhderiv : ∀ w ∈ ball (0 : ℂ) R, HasDerivAt h (deriv h w) w := fun w hw =>
    (hh.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hFdiff : DifferentiableOn ℂ F (ball 0 R) := by
    intro ζ hζ
    have hu : HasDerivAt (fun ζ => h (ψ ζ)) _ ζ :=
      (hhderiv (ψ ζ) (hψmem ζ hζ)).comp ζ (hψderiv ζ hζ)
    have hden := (halfPlane_cayley_norm_le_one haM (hre _ (hψmem ζ hζ))).1
    exact ((hu.sub_const a).div (hu.const_sub _) hden).differentiableAt.differentiableWithinAt
  have hF0 : F 0 = 0 := by simp [hF, hψ0, ha]
  have hmaps : Set.MapsTo F (ball 0 R) (closedBall (F 0) 1) := by
    intro ζ hζ
    rw [hF0, mem_closedBall_zero_iff]
    exact (halfPlane_cayley_norm_le_one haM (hre _ (hψmem ζ hζ))).2
  have hschwarz : ‖deriv F 0‖ ≤ 1 / R :=
    Complex.norm_deriv_le_div_of_mapsTo_ball hFdiff hmaps hR
  -- compute deriv F 0
  have hDre : D = ((2 * (M - a.re) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hD]
    ring
  have hDpos : 0 < 2 * (M - a.re) := by linarith
  have hD0 : D ≠ 0 := by
    rw [hDre]; exact_mod_cast hDpos.ne'
  have hzz : (R : ℂ) ^ 2 - z * (starRingEnd ℂ) z = ((R ^ 2 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hgap : 0 < R ^ 2 - ‖z‖ ^ 2 := by
    have : ‖z‖ ^ 2 < R ^ 2 := by gcongr
    linarith
  have hFd : HasDerivAt F (deriv h z * (((R : ℂ) ^ 2 - z * (starRingEnd ℂ) z) / (R : ℂ) ^ 2) / D)
      0 := by
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
    have hu := HasDerivAt.comp (0 : ℂ) (hhderiv (ψ 0) (hψmem 0 h0)) (hψderiv 0 h0)
    have hden := (halfPlane_cayley_norm_le_one haM (hre _ (hψmem 0 h0))).1
    have hd := (hu.sub_const a).div (hu.const_sub ((2 * M : ℂ) - (starRingEnd ℂ) a)) hden
    refine hd.congr_deriv ?_
    have hcomp : (h ∘ ψ) 0 = a := by rw [Function.comp_apply, hψ0]
    simp only [hψ0, hcomp, sub_self, zero_mul, sub_zero, zero_add, mul_zero, add_zero, mul_one]
    rw [← hD]
    field_simp
  rw [hFd.deriv, hzz, hDre, norm_div, norm_mul, norm_div, norm_pow, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hgap, abs_of_pos hDpos, abs_of_pos hR] at hschwarz
  rw [le_div_iff₀ hgap]
  have hR2 : 0 < R ^ 2 := by positivity
  rw [div_le_div_iff₀ hDpos hR] at hschwarz
  have e : ‖deriv h z‖ * ((R ^ 2 - ‖z‖ ^ 2) / R ^ 2) * R =
      ‖deriv h z‖ * (R ^ 2 - ‖z‖ ^ 2) / R := by
    field_simp
  rw [e, one_mul, div_le_iff₀ hR] at hschwarz
  linarith

/-- Montgomery and Vaughan 2007, Lemma 6.2, derivative part, used at P0014 display 4.16:
if h is holomorphic on the open disc of radius R about 0, h(0) = 0 and Re h ≤ M there with
M > 0, then abs h'(z) ≤ 2 M R / (R − abs z)² in the disc. Proved from the Schwarz-Pick bound
`norm_deriv_le_of_re_lt` and Mathlib's Borel-Carathéodory theorem. -/
theorem mv_lemma_6_2 {h : ℂ → ℂ} {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (hre : ∀ ζ ∈ ball (0 : ℂ) R, (h ζ).re ≤ M)
    (h0 : h 0 = 0) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ‖deriv h z‖ ≤ 2 * M * R / (R - ‖z‖) ^ 2 := by
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hgap : 0 < R - ‖z‖ := by linarith
  have hsum : 0 < R + ‖z‖ := by positivity
  have hK : 0 < 2 * R / (R - ‖z‖) ^ 2 := by positivity
  -- it suffices to prove the bound with M + ε for every ε > 0
  suffices hε : ∀ ε > 0, ‖deriv h z‖ ≤ 2 * (M + ε) * R / (R - ‖z‖) ^ 2 by
    by_contra hcon
    rw [not_le] at hcon
    set K := 2 * R / (R - ‖z‖) ^ 2 with hKdef
    have e1 : 2 * M * R / (R - ‖z‖) ^ 2 = K * M := by rw [hKdef]; ring
    rw [e1] at hcon
    have hεpos : 0 < (‖deriv h z‖ - K * M) / (2 * K) := by
      apply div_pos <;> linarith
    have := hε _ hεpos
    have e2 : 2 * (M + (‖deriv h z‖ - K * M) / (2 * K)) * R / (R - ‖z‖) ^ 2 =
        K * M + (‖deriv h z‖ - K * M) / 2 := by
      have : K * ((‖deriv h z‖ - K * M) / (2 * K)) = (‖deriv h z‖ - K * M) / 2 := by
        field_simp
      calc 2 * (M + (‖deriv h z‖ - K * M) / (2 * K)) * R / (R - ‖z‖) ^ 2
          = K * M + K * ((‖deriv h z‖ - K * M) / (2 * K)) := by rw [hKdef]; ring
        _ = _ := by rw [this]
    rw [e2] at this
    linarith
  intro ε hε
  have hM' : 0 < M + ε := by linarith
  have hsp := norm_deriv_le_of_re_lt (M := M + ε) hR hh
    (fun ζ hζ => lt_of_le_of_lt (hre ζ hζ) (by linarith)) hz
  have hbc : ‖h z‖ ≤ 2 * (M + ε) * ‖z‖ / (R - ‖z‖) :=
    Complex.borelCaratheodory_zero hM' hh (fun ζ hζ => (hre ζ hζ).trans (by linarith)) hR hz h0
  have hrez : -(h z).re ≤ 2 * (M + ε) * ‖z‖ / (R - ‖z‖) :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hbc)
  have hfac : R ^ 2 - ‖z‖ ^ 2 = (R - ‖z‖) * (R + ‖z‖) := by ring
  have hgap2 : 0 < R ^ 2 - ‖z‖ ^ 2 := by rw [hfac]; positivity
  refine hsp.trans ?_
  have hnum : M + ε - (h z).re ≤ (M + ε) * (R + ‖z‖) / (R - ‖z‖) := by
    have : (M + ε) * (R + ‖z‖) / (R - ‖z‖) = (M + ε) + 2 * (M + ε) * ‖z‖ / (R - ‖z‖) := by
      field_simp
      ring
    rw [this]
    linarith
  calc 2 * (M + ε - (h z).re) * R / (R ^ 2 - ‖z‖ ^ 2)
      ≤ 2 * ((M + ε) * (R + ‖z‖) / (R - ‖z‖)) * R / (R ^ 2 - ‖z‖ ^ 2) := by gcongr
    _ = 2 * (M + ε) * R / (R - ‖z‖) ^ 2 := by
      rw [hfac]
      field_simp

/-- A holomorphic function without zeros on an open disc has a holomorphic logarithm there,
normalized to vanish at the centre: there is g with g(s0) = 0, g' = f'/f on the disc and
f = f(s0) exp g on the disc. This is the function log(f(z)/f(s0)) in the proof of Montgomery and
Vaughan Lemma 6.3, cited at P0014 display 4.16. -/
lemma exists_log_on_ball {f : ℂ → ℂ} {s0 : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball s0 R)) (hz : ∀ z ∈ ball s0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g s0 = 0 ∧ (∀ z ∈ ball s0 R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball s0 R, f z = f s0 * Complex.exp (g z) := by
  have hdf : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball s0 R) :=
    (hf.deriv isOpen_ball).div hf hz
  obtain ⟨g, hg0, hg⟩ := hdf.isExactOn_ball.with_val_at s0 0
  refine ⟨g, hg0, hg, ?_⟩
  set k : ℂ → ℂ := fun z => f z * Complex.exp (-g z) with hk
  have hkd : ∀ z ∈ ball s0 R, HasDerivAt k 0 z := by
    intro z hzb
    have hfz : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (isOpen_ball.mem_nhds hzb)).hasDerivAt
    have he : HasDerivAt (fun z => Complex.exp (-g z))
        (Complex.exp (-g z) * -(deriv f z / f z)) z := ((hg z hzb).neg).cexp
    have := hfz.mul he
    refine this.congr_deriv ?_
    have := hz z hzb
    field_simp
    ring
  have hkdiff : DifferentiableOn ℂ k (ball s0 R) := fun z hzb =>
    (hkd z hzb).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ ball s0 R, k z = k s0 := fun z hzb =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball s0 R).isPreconnected hkdiff
      (fun w hw => (hkd w hw).deriv) hzb (mem_ball_self hR)
  intro z hzb
  have h1 := hconst z hzb
  simp only [hk, hg0, neg_zero, Complex.exp_zero, mul_one] at h1
  rw [← h1, mul_assoc, ← Complex.exp_add]
  simp

/-- P0014 display 4.16, page 36: the lemma of Landau cited from Montgomery and Vaughan 2007,
Lemma 6.3 with Lemma 6.2. For f entire, zero free and bounded by B on the closed disc of radius
R about s0, abs f'/f at any point of the closed disc of radius r < R about s0 is at most
2R log(B/abs f(s0))/(R − r)². Same statement as `Residue123.landau_lemma`, proved here from
`exists_log_on_ball` and `mv_lemma_6_2`. -/
theorem landau_lemma (f : ℂ → ℂ) (hf : Differentiable ℂ f) (s0 : ℂ) (r R B : ℝ) (hr : 0 < r)
    (hrR : r < R) (hz : ∀ z ∈ Metric.closedBall s0 R, f z ≠ 0)
    (hB : ∀ z ∈ Metric.closedBall s0 R, ‖f z‖ ≤ B) (s : ℂ) (hs : s ∈ Metric.closedBall s0 r) :
    ‖deriv f s / f s‖ ≤ 2 * R * Real.log (B / ‖f s0‖) / (R - r) ^ 2 := by
  have hR : 0 < R := hr.trans hrR
  have hs0 : s0 ∈ closedBall s0 R := mem_closedBall_self hR.le
  have hf0 : 0 < ‖f s0‖ := norm_pos_iff.mpr (hz s0 hs0)
  obtain ⟨g, hg0, hg, hexp⟩ := exists_log_on_ball hR hf.differentiableOn
    (fun z hzb => hz z (ball_subset_closedBall hzb))
  set M := Real.log (B / ‖f s0‖) with hMdef
  set h : ℂ → ℂ := fun ζ => g (s0 + ζ) with hh
  have hmem : ∀ ζ ∈ ball (0 : ℂ) R, s0 + ζ ∈ ball s0 R := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ
    rw [mem_ball, dist_eq_norm]
    simpa using hζ
  have hhd : ∀ ζ ∈ ball (0 : ℂ) R, HasDerivAt h (deriv f (s0 + ζ) / f (s0 + ζ)) ζ := by
    intro ζ hζ
    have := (hg (s0 + ζ) (hmem ζ hζ)).comp_const_add s0 ζ
    exact this
  have hhdiff : DifferentiableOn ℂ h (ball 0 R) := fun ζ hζ =>
    (hhd ζ hζ).differentiableAt.differentiableWithinAt
  have hre : ∀ ζ ∈ ball (0 : ℂ) R, (h ζ).re ≤ M := by
    intro ζ hζ
    have hb := hmem ζ hζ
    have h1 := congrArg norm (hexp _ hb)
    rw [norm_mul, Complex.norm_exp] at h1
    have h2 : ‖f (s0 + ζ)‖ ≤ B := hB _ (ball_subset_closedBall hb)
    have h3 : Real.exp (h ζ).re ≤ B / ‖f s0‖ := by
      rw [le_div_iff₀ hf0, mul_comm]
      rw [← h1]; exact h2
    have := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at this
  have hh0 : h 0 = 0 := by simp [hh, hg0]
  have hsz : s - s0 ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hs
    linarith
  have hsr : ‖s - s0‖ ≤ r := by
    rw [mem_closedBall, dist_eq_norm] at hs
    exact hs
  have hderiv : deriv h (s - s0) = deriv f s / f s := by
    have := (hhd (s - s0) hsz).deriv
    simpa using this
  have hM0 : 0 ≤ M := by
    have := hre 0 (mem_ball_self hR)
    rwa [hh0, Complex.zero_re] at this
  have hRr : 0 < R - r := by linarith
  rcases hM0.eq_or_lt with hMz | hMpos
  · -- M = 0: bound with every ε > 0 in place of M
    rw [← hMz, mul_zero, zero_div]
    by_contra hcon
    rw [not_le] at hcon
    rw [← hderiv] at hcon
    set K := 2 * R / (R - r) ^ 2 with hKdef
    have hK : 0 < K := by positivity
    have hεpos : 0 < ‖deriv h (s - s0)‖ / (2 * K) := by positivity
    have h1 := mv_lemma_6_2 hεpos hR hhdiff
      (fun ζ hζ => (hre ζ hζ).trans (by rw [← hMz]; exact hεpos.le)) hh0 hsz
    have h2 : 2 * (‖deriv h (s - s0)‖ / (2 * K)) * R / (R - ‖s - s0‖) ^ 2 ≤
        2 * (‖deriv h (s - s0)‖ / (2 * K)) * R / (R - r) ^ 2 := by
      gcongr
    have h3 : 2 * (‖deriv h (s - s0)‖ / (2 * K)) * R / (R - r) ^ 2 =
        ‖deriv h (s - s0)‖ / 2 := by
      calc 2 * (‖deriv h (s - s0)‖ / (2 * K)) * R / (R - r) ^ 2
          = K * (‖deriv h (s - s0)‖ / (2 * K)) := by rw [hKdef]; ring
        _ = _ := by field_simp
    linarith
  · have h1 := mv_lemma_6_2 hMpos hR hhdiff hre hh0 hsz
    rw [hderiv] at h1
    refine h1.trans ?_
    have : 2 * M * R / (R - ‖s - s0‖) ^ 2 ≤ 2 * M * R / (R - r) ^ 2 := by
      gcongr
    refine this.trans (le_of_eq ?_)
    ring

end LeanLab.HelfgottMajor.Landau123
