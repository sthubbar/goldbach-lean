module

public import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442
public import LeanLab.Linnik1951.Gamma442
public import LeanLab.Linnik1951.Mellin473
public import LeanLab.Linnik1951.SPLIT_outer_kernel_mass_integrable442

/-!
Split of the abstract outer Mellin kernel estimate `outer_kernel_integrable442`
into four steps plus one assembly.

The estimate is one integrability claim about the absolute value of the outer
Mellin kernel on the shifted line, weighted by the cube of the logarithm. The
kernel factor is a complex power of a fixed nonzero base times the Gamma
function; along the line the Gamma factor decays exponentially in the absolute
imaginary part, and the logarithm weight grows only cubically, so the weighted
kernel is dominated by an exponentially decaying cubic. The split records that
argument in four pieces: the exponential decay of the kernel factor with
constants that may depend on the parameters, the cubic polynomial bound on the
logarithm weight, the integrability of the exponential decay times the cubic,
and the strong measurability of the weighted kernel. The assembly below
combines them through the dominated convergence inequality for the Bochner
integral.

Nothing here changes the statement of `outer_kernel_integrable442`; the theorem
`outer_kernel_integrable442_split` restates it character for character and
proves it from the four leaves without using the original theorem.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of 4: exponential decay of the kernel factor in the variable of
integration. For N at least three and a frequency in the outer interval, the
complex power and the Gamma factor together are dominated by one exponential
with a positive rate, the two constants depending on N, R and the frequency but
not on the integration variable. No logarithm weight and no coefficient
occurs. -/
theorem outer_kernel_decay442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ t : ℝ,
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤
        K * Real.exp (-(δ * |t|)) := by
  let z : ℂ := (1 / (N : ℝ) : ℝ) + (2 * Real.pi * α : ℝ) * Complex.I
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hzre : z.re = 1 / N := by simp [z]
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hzpos
  have ha : 0 ≤ α := (by positivity : (0 : ℝ) ≤ 4 / N).trans hα.1
  have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    positivity)
  have harglt : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (.inl hzpos)
  let d : ℝ := Real.pi / 2 - z.arg
  have hd : 0 < d := by dsimp [d]; linarith
  let rate : ℝ := d / 2
  have hr : 0 < rate := by dsimp [rate]; positivity
  let σ : ℝ := 1 / 2 + 1 / Real.log N
  let A : ℝ := ‖z‖ ^ (-σ) * Real.sqrt (2 * Real.pi)
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hA : 0 < A := by dsimp [A]; positivity
  have hlin : ∀ x : ℝ, 0 ≤ x → 3 + x ≤ (3 + 1 / rate) * Real.exp (rate * x) := by
    intro x hx
    have he : 1 ≤ Real.exp (rate * x) := Real.one_le_exp_iff.mpr (mul_nonneg hr.le hx)
    have hx' : x ≤ Real.exp (rate * x) / rate := by
      rw [le_div_iff₀ hr]
      linarith [Real.add_one_le_exp (rate * x)]
    calc
      3 + x ≤ 3 * Real.exp (rate * x) + Real.exp (rate * x) / rate := by linarith
      _ = (3 + 1 / rate) * Real.exp (rate * x) := by ring
  refine ⟨A * (3 + 1 / rate), rate, by positivity, hr, ?_⟩
  intro t
  have hre : (-(mellinLine1622 N t)).re = -σ := by
    simp only [mellinLine1622, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, σ]
  have him : (-(mellinLine1622 N t)).im = -t := by
    simp only [mellinLine1622, Complex.neg_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      add_zero, zero_add]
  have hpow : ‖z ^ (-(mellinLine1622 N t))‖ ≤ ‖z‖ ^ (-σ) * Real.exp (|t| * z.arg) := by
    have h := Complex.norm_cpow_le z (-(mellinLine1622 N t))
    rw [hre, him, div_eq_mul_inv, ← Real.exp_neg] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg z) _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self t) harg0]
  have hgamma := gamma_mellin_line442 N hN t
  have hprod := mul_le_mul hpow hgamma (norm_nonneg _)
    (by positivity : 0 ≤ ‖z‖ ^ (-σ) * Real.exp (|t| * z.arg))
  have hexp : Real.exp (|t| * z.arg) * Real.exp (-(Real.pi * |t| / 2)) =
      Real.exp (-(d * |t|)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  have hbound : ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤
      A * (3 + |t|) * Real.exp (-(d * |t|)) := by
    rw [norm_mul]
    apply hprod.trans_eq
    calc
      _ = (‖z‖ ^ (-σ) * Real.sqrt (2 * Real.pi)) * (3 + |t|) *
        (Real.exp (|t| * z.arg) * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ = _ := by rw [hexp]
  change ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤ _
  calc
    _ ≤ A * (3 + |t|) * Real.exp (-(d * |t|)) := hbound
    _ ≤ A * ((3 + 1 / rate) * Real.exp (rate * |t|)) * Real.exp (-(d * |t|)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlin _ (abs_nonneg t)) hA.le)
        (Real.exp_pos _).le
    _ = (A * (3 + 1 / rate)) *
        (Real.exp (rate * |t|) * Real.exp (-(d * |t|))) := by ring
    _ = A * (3 + 1 / rate) * Real.exp (-(rate * |t|)) := by
      congr 1
      rw [← Real.exp_add]
      congr 1
      dsimp [rate]
      ring

/-- LEAF. Step 2 of 4: the cube of the logarithm weight is bounded by a cubic
polynomial in the absolute value of the integration variable. The constant
depends on N only, and there is no kernel factor here. -/
theorem log_weight_cubic442 (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ C * (1 + |t|) ^ 3 := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  refine ⟨(Real.log N + 1) ^ 3, by positivity, ?_⟩
  intro t
  have ht : 0 ≤ |t| := abs_nonneg t
  have hp : 0 < |t| + 2 := by positivity
  have hlog : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [mul_nonneg (Nat.cast_nonneg N) ht])
  have hbound : Real.log ((N : ℝ) * (|t| + 2)) ≤ (Real.log N + 1) * (1 + |t|) := by
    rw [Real.log_mul hNp.ne' hp.ne']
    have hi := Real.log_le_sub_one_of_pos hp
    nlinarith [mul_nonneg hL ht]
  calc
    _ ≤ ((Real.log N + 1) * (1 + |t|)) ^ 3 := pow_le_pow_left₀ hlog hbound 3
    _ = _ := by ring

/-- LEAF. Step 3 of 4: for every positive rate the exponential decay times the
cubic polynomial is integrable on the line. This is the model estimate that the
dominating function has to satisfy, and it carries no kernel, no Gamma factor
and no logarithm of N. -/
theorem exp_decay_cubic_integrable442 :
    ∀ δ : ℝ, 0 < δ → Integrable (fun t : ℝ =>
      Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by
  intro δ hδ
  exact exp_decay_cubic_integrable473 δ hδ

/-- LEAF. Step 4 of 4: strong measurability of the log weighted kernel. The base
is a fixed nonzero complex number, the line is continuous in the variable of
integration and the Gamma factor is continuous on the half plane of positive
real part, which is where the shifted line lies. This is the measurability half
of the conclusion, without any bound. -/
theorem outer_kernel_aestronglyMeasurable442 (N : ℕ) (R : ℝ) (α : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ)))
  · exact (outer_kernel_weight_continuous_line442 N hN α).aestronglyMeasurable

/-- Assembly of `outer_kernel_integrable442` from the four leaves. The decay
constants and the polynomial constant of the two bounds multiply into the
dominating exponential times cubic, which is integrable by the model estimate,
and the weighted kernel is measurable, so the dominated convergence inequality
for the Bochner integral gives the conclusion. -/
theorem outer_kernel_integrable442_split (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
    Integrable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  obtain ⟨K, δ, hK, hδ, hdec⟩ := outer_kernel_decay442 N hN R hR α hα
  obtain ⟨C, hC, hlog⟩ := log_weight_cubic442 N hN
  have hint : Integrable (fun t : ℝ =>
      K * C * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3)) :=
    (exp_decay_cubic_integrable442 δ hδ).const_mul (K * C)
  refine hint.mono' (outer_kernel_aestronglyMeasurable442 N R α)
    (Filter.Eventually.of_forall (fun t => ?_))
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    nlinarith [abs_nonneg t]
  have hfnn : (0 : ℝ) ≤
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
    mul_nonneg (norm_nonneg _) (pow_nonneg hlog0 3)
  have hpoly : (0 : ℝ) ≤ (1 + |t|) ^ 3 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  calc
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3
        ≤ ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            (C * (1 + |t|) ^ 3) :=
          mul_le_mul_of_nonneg_left (hlog t) (norm_nonneg _)
    _ = (‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ * C) *
            (1 + |t|) ^ 3 := by ring
    _ ≤ ((K * Real.exp (-(δ * |t|))) * C) * (1 + |t|) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hdec t) hC.le) hpoly
    _ = K * C * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by ring

end LeanLab.Linnik1951
