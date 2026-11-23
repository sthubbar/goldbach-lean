module

public import LeanLab.PNTPort.LargeSieve.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Gallagher's lemma, discrete form

Lab proof, unit U-5758, CLOUD 20261020T0014Z-cloud30. AI wrote this file. Known mathematics,
Gallagher 1970, Invent. Math. 11, Lemma 1, in the discrete form with integer window `L`.
No cited input.

For complex `a n`, `n < N`, and an integer `L ≥ 1`,

  `∫_{|β| ≤ 1/(2L)} ‖∑_{n<N} a n e(nβ)‖² dβ ≤ (π/(2L))² ∑_{m < N + L} ‖∑_{n<N, m-L < n ≤ m} a n‖²`,

that is, with `x = m - L`, the mean square of `S` near `0` is at most `(π/(2L))²` times the sum
over `x` of the squared window sums `∑_{x < n ≤ x + L} a n`.

The proof is the Fejer kernel route on the circle, with no Fourier analysis on `ℝ`:
* `norm_dirichlet_ge`: `‖∑_{j<L} e(jβ)‖ ≥ 2L/π` for `|β| ≤ 1/(2L)`, by
  `|sin(πLβ)| ≥ 2L|β|` and `|sin(πβ)| ≤ π|β|`;
* `mul_dirichlet`: `S(β) · ∑_{j<L} e(jβ) = ∑_m b m e(mβ)`, `b` the window sums;
* `parseval`: `∫_{-1/2}^{1/2} ‖∑_{m<M} b m e(mβ)‖² = ∑_{m<M} ‖b m‖²`.
This is the bridge from short interval mean squares, such as Selberg's under RH, to the
`L²` norm of the exponential sum of `Λ` near `0`, used by Languasco-Perelli 1996, Languasco-
Zaccagnini 2016 Theorem 1 and Bhowmik-Grimmelt 2026 Lemma 5.3.
-/

@[expose] public section


namespace LeanLab.PNTPort.Gallagher

open Complex Finset Real MeasureTheory
open LeanLab.PNTPort.LargeSieve

lemma continuous_e : Continuous e := by
  unfold e; fun_prop

lemma continuous_e_mul (k : ℝ) : Continuous fun β : ℝ => e (k * β) :=
  continuous_e.comp (continuous_const.mul continuous_id)

/-- `‖e θ - 1‖ = 2 |sin(πθ)|`. -/
lemma norm_e_sub_one (θ : ℝ) : ‖e θ - 1‖ = 2 * |Real.sin (π * θ)| := by
  unfold e
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  rw [show 2 * π * θ / 2 = π * θ by ring]

/-- The Dirichlet kernel is large near `0`: `‖∑_{j<L} e(jβ)‖ ≥ 2L/π` for `|β| ≤ 1/(2L)`. -/
theorem norm_dirichlet_ge {L : ℕ} (hL : 0 < L) {β : ℝ} (hβ : |β| ≤ 1 / (2 * L)) :
    2 * L / π ≤ ‖∑ j ∈ range L, e (j * β)‖ := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rcases eq_or_ne β 0 with h0 | h0
  · subst h0
    simp only [mul_zero, e_zero, sum_const, card_range, nsmul_eq_mul, mul_one,
      Complex.norm_natCast]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.two_le_pi]
  · have hb0 : 0 < |β| := abs_pos.mpr h0
    have hhalf : |β| ≤ 1 / 2 := by
      refine hβ.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    -- the denominator `‖e β - 1‖ = 2|sin πβ|`, positive and at most `2π|β|`
    have hden_pos : 0 < ‖e β - 1‖ := by
      rw [norm_e_sub_one]
      have := two_abs_le_abs_sin hhalf
      linarith
    have hden_le : ‖e β - 1‖ ≤ 2 * (π * |β|) := by
      rw [norm_e_sub_one]
      have := Real.abs_sin_le_abs (x := π * β)
      rw [abs_mul, abs_of_pos Real.pi_pos] at this
      linarith
    have hne : e β ≠ 1 := by
      intro h1; rw [h1, sub_self, norm_zero] at hden_pos; exact lt_irrefl _ hden_pos
    -- the numerator `‖e (Lβ) - 1‖ = 2|sin πLβ| ≥ 4L|β|`
    have hLb : |(L : ℝ) * β| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hLr]
      calc (L : ℝ) * |β| ≤ L * (1 / (2 * L)) := mul_le_mul_of_nonneg_left hβ hLr.le
        _ = 1 / 2 := by field_simp
    have hnum : 4 * (L * |β|) ≤ ‖e β ^ L - 1‖ := by
      rw [← e_nat_mul, norm_e_sub_one]
      have := two_abs_le_abs_sin hLb
      rw [abs_mul, abs_of_pos hLr] at this
      rw [show π * (L * β) = π * ((L : ℝ) * β) by ring]
      linarith
    simp_rw [e_nat_mul]
    rw [geom_sum_eq hne, norm_div, le_div_iff₀ hden_pos]
    calc 2 * L / π * ‖e β - 1‖ ≤ 2 * L / π * (2 * (π * |β|)) :=
          mul_le_mul_of_nonneg_left hden_le (by positivity)
      _ = 4 * (L * |β|) := by field_simp; ring
      _ ≤ _ := hnum

/-- The window sum `b m = ∑_{n<N, n ≤ m < n + L} a n`, that is `∑_{m - L < n ≤ m} a n`. -/
noncomputable def win (a : ℕ → ℂ) (N L m : ℕ) : ℂ :=
  ∑ n ∈ (range N).filter (fun n => n ≤ m ∧ m < n + L), a n

/-- `S(β) ∑_{j<L} e(jβ) = ∑_{m < N + L} b m e(mβ)`. -/
theorem mul_dirichlet (a : ℕ → ℂ) (N L : ℕ) (β : ℝ) :
    (∑ n ∈ range N, a n * e (n * β)) * ∑ j ∈ range L, e (j * β)
      = ∑ m ∈ range (N + L), win a N L m * e (m * β) := by
  unfold win
  simp_rw [sum_mul, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  -- `∑_{m < N + L} [n ≤ m < n + L] a n e(mβ) = a n ∑_{j<L} e((n + j)β)`
  have hset : (range (N + L)).filter (fun m => n ≤ m ∧ m < n + L) = Ico n (n + L) := by
    ext m; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [← sum_filter, hset, sum_Ico_eq_sum_range, add_tsub_cancel_left, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_assoc, ← e_add]
  congr 2; push_cast; ring

/-- `∫_{-1/2}^{1/2} e(kβ) dβ = [k = 0]` for an integer `k`. -/
lemma integral_e_int (k : ℤ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), e (k * β) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [e_zero]; norm_num
  · have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Complex.I_ne_zero, this, hk']
    have he : ∀ β : ℝ, e (k * β) = Complex.exp ((2 * Real.pi * Complex.I * k) * β) := by
      intro β; unfold e; congr 1; push_cast; ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * k * ((1 / 2 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * k * ((-(1 / 2) : ℝ) : ℂ)) := by
      have hper : Complex.exp (k * (2 * Real.pi * Complex.I)) = 1 :=
        Complex.exp_int_mul_two_pi_mul_I k
      rw [show 2 * Real.pi * Complex.I * k * ((1 / 2 : ℝ) : ℂ)
          = 2 * Real.pi * Complex.I * k * ((-(1 / 2) : ℝ) : ℂ) + k * (2 * Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_add, hper, mul_one]
    rw [h1, sub_self, zero_div]

/-- Parseval for a finite trigonometric polynomial with frequencies `0, …, M - 1`. -/
theorem parseval (b : ℕ → ℂ) (M : ℕ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ range M, b m * e (m * β)‖ ^ 2
      = ∑ m ∈ range M, ‖b m‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hexp : ∀ β : ℝ, ((‖∑ m ∈ range M, b m * e (m * β)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ range M, ∑ m' ∈ range M,
          b m * (starRingEnd ℂ) (b m') * e (((m : ℤ) - (m' : ℤ) : ℤ) * β) := by
    intro β
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [map_mul, ← e_neg]
    have : e (((m : ℤ) - (m' : ℤ) : ℤ) * β) = e (m * β) * e (-(m' * β)) := by
      rw [← e_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hexp]
  have hint : ∀ (m m' : ℕ), IntervalIntegrable
      (fun β : ℝ => b m * (starRingEnd ℂ) (b m') * e (((m : ℤ) - (m' : ℤ) : ℤ) * β))
      volume (-(1 / 2)) (1 / 2) := fun m m' =>
    (continuous_const.mul (continuous_e_mul _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (f := fun m β => ∑ m' ∈ range M,
      b m * (starRingEnd ℂ) (b m') * e (((m : ℤ) - (m' : ℤ) : ℤ) * β)) fun m _ =>
    (continuous_finsetSum _ fun m' _ =>
      continuous_const.mul (continuous_e_mul _)).intervalIntegrable _ _]
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun m' β =>
      b m * (starRingEnd ℂ) (b m') * e (((m : ℤ) - (m' : ℤ) : ℤ) * β)) fun m' _ => hint m m']
  simp_rw [intervalIntegral.integral_const_mul, integral_e_int]
  rw [sum_eq_single m]
  · simp only [sub_self, if_true, mul_one]
    rw [Complex.mul_conj', Complex.ofReal_pow]
  · intro m' _ hm'
    have : ((m : ℤ) - (m' : ℤ)) ≠ 0 := by
      intro h; apply hm'; omega
    simp [this]
  · intro h; exact absurd hm h

/-- **Gallagher's lemma, discrete form.** For complex `a n`, `n < N`, and an integer `L ≥ 1`,
`∫_{|β| ≤ 1/(2L)} ‖∑_{n<N} a n e(nβ)‖² ≤ (π/(2L))² ∑_{m<N+L} ‖∑_{m-L < n ≤ m} a n‖²`. -/
theorem gallagher (a : ℕ → ℂ) (N L : ℕ) (hL : 0 < L) :
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range N, a n * e (n * β)‖ ^ 2
      ≤ (π / (2 * L)) ^ 2 * ∑ m ∈ range (N + L), ‖win a N L m‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set S : ℝ → ℂ := fun β => ∑ n ∈ range N, a n * e (n * β) with hS
  set D : ℝ → ℂ := fun β => ∑ j ∈ range L, e (j * β) with hD
  have hcS : Continuous S := continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_e_mul _)
  have hcD : Continuous D := continuous_finsetSum _ fun j _ => continuous_e_mul _
  have hδ : (0 : ℝ) < 1 / (2 * L) := by positivity
  have hδh : 1 / (2 * (L : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- pointwise: `‖S‖² ≤ (π/(2L))² ‖S D‖²` on `|β| ≤ 1/(2L)`
  have hpt : ∀ β ∈ Set.Icc (-(1 / (2 * L) : ℝ)) (1 / (2 * L)),
      ‖S β‖ ^ 2 ≤ (π / (2 * L)) ^ 2 * ‖S β * D β‖ ^ 2 := by
    intro β hβ
    have hb : |β| ≤ 1 / (2 * L) := abs_le.mpr ⟨hβ.1, hβ.2⟩
    have hk := norm_dirichlet_ge hL hb
    have h1 : 1 ≤ π / (2 * L) * ‖D β‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hk Real.pi_pos.le
      rw [mul_div_assoc', mul_comm π (2 * (L : ℝ)), mul_div_assoc, div_self Real.pi_ne_zero,
        mul_one] at this
      linarith
    rw [norm_mul, mul_pow, ← mul_assoc, ← mul_pow, mul_comm (π / (2 * L)) ‖S β‖, mul_pow,
      mul_assoc]
    have h2 : 1 ≤ (π / (2 * L)) ^ 2 * ‖D β‖ ^ 2 := by
      rw [← mul_pow]; nlinarith
    nlinarith [sq_nonneg ‖S β‖]
  calc ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖S β‖ ^ 2
      ≤ ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), (π / (2 * L)) ^ 2 * ‖S β * D β‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact ((hcS.norm).pow 2).intervalIntegrable _ _
        · exact (continuous_const.mul (((hcS.mul hcD).norm).pow 2)).intervalIntegrable _ _
        · exact hpt
    _ = (π / (2 * L)) ^ 2 * ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖S β * D β‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (π / (2 * L)) ^ 2 * ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖S β * D β‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hδh
        · exact Filter.Eventually.of_forall fun β => by positivity
        · exact (((hcS.mul hcD).norm).pow 2).intervalIntegrable _ _
    _ = (π / (2 * L)) ^ 2 * ∑ m ∈ range (N + L), ‖win a N L m‖ ^ 2 := by
        congr 1
        simp_rw [hS, hD, mul_dirichlet]
        exact parseval _ _

end LeanLab.PNTPort.Gallagher

