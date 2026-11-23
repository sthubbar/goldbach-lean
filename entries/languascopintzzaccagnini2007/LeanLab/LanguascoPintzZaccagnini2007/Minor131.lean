module

public import LeanLab.LanguascoPintzZaccagnini2007.Fourier131
public import LeanLab.BhowmikGrimmelt2026.Minor84

@[expose] public section

namespace LeanLab.LPZ2007

open Finset Real MeasureTheory


noncomputable section

/-- Match the page 3 prime sum to the existing lab Vaughan and Parseval sum. -/
theorem primeSum_eq_ssum131 (X : ℕ) (α : ℝ) :
    primeSum131 X α = LeanLab.BhowmikGrimmelt2026.Ssum X α := by
  simp only [primeSum131, LeanLab.BhowmikGrimmelt2026.Ssum,
    LeanLab.BhowmikGrimmelt2026.ee, phase131, mul_comm α]

/-- Page 4: the prime sum has period one. -/
theorem primeSum_periodic131 (X : ℕ) : Function.Periodic (primeSum131 X) 1 := by
  intro α
  unfold primeSum131
  apply sum_congr rfl
  intro m _
  congr 1
  unfold phase131
  have he : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) * (α + 1) : ℝ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) * α : ℝ) +
        (m : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Page 4: Parseval for the prime sum on every shifted unit interval. -/
theorem primeSum_parseval131 (X : ℕ) (a : ℝ) :
    (∫ α in a..a + 1, ‖primeSum131 X α‖ ^ 2) =
      ∑ n ∈ Icc 1 X, ArithmeticFunction.vonMangoldt n ^ 2 := by
  have hp : Function.Periodic (fun α => ‖primeSum131 X α‖ ^ 2) 1 := by
    intro α
    change ‖primeSum131 X (α + 1)‖ ^ 2 = ‖primeSum131 X α‖ ^ 2
    rw [primeSum_periodic131 X α]
  rw [hp.intervalIntegral_add_eq a 0]
  simpa only [zero_add, primeSum_eq_ssum131] using
    LeanLab.BhowmikGrimmelt2026.ssum_parseval84 X

/-- Page 4: the weaker elementary Chebyshev bound suffices in place of the PNT. -/
theorem primeSum_energy131 (X : ℕ) (a : ℝ) :
    (∫ α in a..a + 1, ‖primeSum131 X α‖ ^ 2) ≤ 6 * X * Real.log X := by
  rw [primeSum_parseval131]
  exact LeanLab.BhowmikGrimmelt2026.mangoldt_energy84 X

/-- Page 3 arc dissection: an interior point covered by a periodic major arc
is covered by the paper major arcs when Q >= P + 2. -/
theorem periodic_major_imp_major131 {X : ℕ} {P α : ℝ}
    (hX : 0 < X) (hP : 0 < P) (hQ : P + 2 ≤ arcQ131 X P)
    (hα : α ∈ Set.Ioc (1 / arcQ131 X P) (1 + 1 / arcQ131 X P))
    (hm : LeanLab.BhowmikGrimmelt2026.MajorArc X P α) :
    α ∈ majorArcs131 X P := by
  obtain ⟨q, hq, hqP, a, hcop, happ⟩ := hm
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hQ0 : 0 < arcQ131 X P := div_pos hXr hP
  have hradius : P / ((q : ℝ) * X) = 1 / ((q : ℝ) * arcQ131 X P) := by
    unfold arcQ131
    field_simp
  rw [hradius] at happ
  obtain ⟨hl, hu⟩ := abs_le.mp happ
  have he : (1 / ((q : ℝ) * arcQ131 X P)) * ((q : ℝ) * arcQ131 X P) = 1 :=
    one_div_mul_cancel (by positivity)
  have ha_lower : (0 : ℝ) < a := by
    have hlow := mul_lt_mul_of_pos_right hα.1 hQ0
    have hr := mul_le_mul_of_nonneg_right hu ((mul_pos hq0 hQ0).le)
    have hcancel : (1 / arcQ131 X P) * arcQ131 X P = 1 := one_div_mul_cancel hQ0.ne'
    have ha_cancel : ((a : ℝ) / q) * ((q : ℝ) * arcQ131 X P) = a * arcQ131 X P := by field_simp
    rw [sub_mul, ha_cancel, he] at hr
    rw [hcancel] at hlow
    nlinarith
  have ha_upper : (a : ℝ) < q + 1 := by
    have htop := mul_le_mul_of_nonneg_right hα.2 ((mul_pos hq0 hQ0).le)
    have hr := mul_le_mul_of_nonneg_right hl ((mul_pos hq0 hQ0).le)
    have ha_cancel : ((a : ℝ) / q) * ((q : ℝ) * arcQ131 X P) = a * arcQ131 X P := by field_simp
    have hi : (1 / arcQ131 X P) * ((q : ℝ) * arcQ131 X P) = q := by field_simp
    rw [sub_mul, ha_cancel, neg_mul, he] at hr
    rw [add_mul, hi] at htop
    have hgap : (q : ℝ) + 1 < arcQ131 X P := by linarith
    nlinarith
  have han : 0 ≤ a := by exact_mod_cast ha_lower.le
  lift a to ℕ using han
  have ha1 : 1 ≤ a := by exact_mod_cast ha_lower
  have haq : a ≤ q := by
    have ht : a < q + 1 := by exact_mod_cast ha_upper
    omega
  push_cast at hl hu
  refine ⟨q, a, hq, hqP, mem_Icc.mpr ⟨ha1, haq⟩, ?_, ?_⟩
  · exact_mod_cast hcop
  · exact ⟨by linarith, by linarith⟩

/-- Page 3: for all sufficiently large X, every admissible P has Q >= P + 2. -/
theorem admissible_gap_eventually131 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 2 ≤ X ∧ ∀ P : ℝ, AdmissibleP131 X P →
      1 ≤ P ∧ P ≤ X ∧ P + 2 ≤ arcQ131 X P := by
  have ht : Filter.Tendsto (fun X : ℕ => (X : ℝ) ^ ((18 : ℝ) / 100)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 18 / 100)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨X₀, hX₀⟩ := (ht.eventually_ge_atTop 3).exists_forall_of_atTop
  refine ⟨max X₀ 2, fun X hX => ⟨by omega, fun P hP => ?_⟩⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0 : (0 : ℝ) < X := by linarith
  have hu1 : 1 ≤ (X : ℝ) ^ ((41 : ℝ) / 100) := Real.one_le_rpow hX1 (by norm_num)
  have hP1 : 1 ≤ P := (Real.one_le_rpow hX1 (by norm_num : (0 : ℝ) ≤ 2 / 5)).trans hP.1
  have hPX : P ≤ X := hP.2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (by norm_num : (41 : ℝ) / 100 ≤ 1))
  have hprod : (X : ℝ) ^ ((59 : ℝ) / 100) =
      (X : ℝ) ^ ((41 : ℝ) / 100) * (X : ℝ) ^ ((18 : ℝ) / 100) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have h59 : P + 2 ≤ (X : ℝ) ^ ((59 : ℝ) / 100) := by
    rw [hprod]
    have h3 := hX₀ X (by omega)
    have hPu := hP.2
    nlinarith [mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hX0.le ((41 : ℝ) / 100))]
  have hdiv : (X : ℝ) ^ ((59 : ℝ) / 100) = X / (X : ℝ) ^ ((41 : ℝ) / 100) := by
    rw [show (59 : ℝ) / 100 = 1 - 41 / 100 by norm_num, Real.rpow_sub hX0, Real.rpow_one]
  refine ⟨hP1, hPX, h59.trans ?_⟩
  rw [hdiv]
  exact div_le_div_of_nonneg_left hX0.le (by linarith) hP.2

/-- Page 4: the lab Vaughan bound applies to the paper minor arcs in the interval interior. -/
theorem minor_pointwise131 {X : ℕ} {P α : ℝ} (hX : 2 ≤ X)
    (hP : AdmissibleP131 X P) (hQ : P + 2 ≤ arcQ131 X P)
    (hα : α ∈ Set.Ioo (1 / arcQ131 X P) (1 / arcQ131 X P + 1))
    (hm : α ∉ majorArcs131 X P) :
    ‖primeSum131 X α‖ ≤ 97200 * (X : ℝ) ^ ((4 : ℝ) / 5) * Real.log X ^ 4 := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0 : (0 : ℝ) < X := by linarith
  have hP1 : 1 ≤ P := (Real.one_le_rpow hX1 (by norm_num : (0 : ℝ) ≤ 2 / 5)).trans hP.1
  have hPX : P ≤ X := hP.2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (by norm_num : (41 : ℝ) / 100 ≤ 1))
  have hn : ¬ LeanLab.BhowmikGrimmelt2026.MajorArc X P α := by
    intro he
    apply hm
    apply periodic_major_imp_major131 (by omega) (by linarith) hQ _ he
    exact ⟨hα.1, by linarith [hα.2]⟩
  have hv := LeanLab.BhowmikGrimmelt2026.minor_pointwise84 hX hP1 hPX hn
  rw [← primeSum_eq_ssum131] at hv
  have hsqrt : (X : ℝ) ^ ((1 : ℝ) / 5) ≤ Real.sqrt P := by
    rw [Real.sqrt_eq_rpow]
    have hh : ((X : ℝ) ^ ((2 : ℝ) / 5)) ^ ((1 : ℝ) / 2) =
        (X : ℝ) ^ ((1 : ℝ) / 5) := by rw [← Real.rpow_mul hX0.le]; norm_num
    rw [← hh]
    exact Real.rpow_le_rpow (by positivity) hP.1 (by norm_num)
  have hfirst : (X : ℝ) / Real.sqrt P ≤ (X : ℝ) ^ ((4 : ℝ) / 5) := by
    calc (X : ℝ) / Real.sqrt P ≤ X / (X : ℝ) ^ ((1 : ℝ) / 5) :=
          div_le_div_of_nonneg_left hX0.le (by positivity) hsqrt
      _ = (X : ℝ) ^ ((4 : ℝ) / 5) := by
          rw [show (4 : ℝ) / 5 = 1 - 1 / 5 by norm_num, Real.rpow_sub hX0, Real.rpow_one]
  nlinarith [mul_le_mul_of_nonneg_right hfirst (pow_nonneg (Real.log_natCast_nonneg X) 4)]

/-- Page 4: a pointwise bound on S times the full prime energy bounds the minor mean square. -/
theorem minor_energy131 (k X : ℕ) (P B : ℝ) (hL : 0 ≤ Lg X)
    (hB : ∀ α ∈ Set.Ioo (1 / arcQ131 X P) (1 / arcQ131 X P + 1),
      α ∉ majorArcs131 X P → ‖primeSum131 X α‖ ≤ B) :
    ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
      B ^ 2 * Lg X ^ (2 * k) * (6 * X * Real.log X) := by
  let a := 1 / arcQ131 X P
  have he (α : ℝ) : ‖minorIntegrand131 k X P α‖ ^ 2 =
      (majorArcs131 X P)ᶜ.indicator
        (fun α => ‖primeSum131 X α ^ 2 * powerSum131 X α ^ k‖ ^ 2) α := by
    by_cases hm : α ∈ (majorArcs131 X P)ᶜ
    · simp [minorIntegrand131, Set.indicator_of_mem hm]
    · simp [minorIntegrand131, Set.indicator_of_notMem hm]
  have hcont : Continuous (fun α => ‖primeSum131 X α ^ 2 * powerSum131 X α ^ k‖ ^ 2) :=
    (((primeSum_continuous131 X).pow 2).mul ((powerSum_continuous131 X).pow k)).norm.pow 2
  have hint : IntervalIntegrable (fun α => ‖minorIntegrand131 k X P α‖ ^ 2) volume a (a + 1) := by
    simp_rw [he]
    have hi : IntervalIntegrable _ volume a (a + 1) := hcont.intervalIntegrable a (a + 1)
    exact ⟨hi.1.indicator (majorArcs_measurable131 X P).compl,
      hi.2.indicator (majorArcs_measurable131 X P).compl⟩
  have hpt (α : ℝ) (hα : α ∈ Set.Ioo a (a + 1)) :
      ‖minorIntegrand131 k X P α‖ ^ 2 ≤ B ^ 2 * Lg X ^ (2 * k) * ‖primeSum131 X α‖ ^ 2 := by
    rw [he]
    by_cases hm : α ∈ (majorArcs131 X P)ᶜ
    · rw [Set.indicator_of_mem hm]
      have hs := pow_le_pow_left₀ (norm_nonneg _) (hB α hα hm) 2
      have hg := pow_le_pow_left₀ (norm_nonneg _) (powerSum_norm_le131 hL α) (2 * k)
      calc ‖primeSum131 X α ^ 2 * powerSum131 X α ^ k‖ ^ 2
          = ‖primeSum131 X α‖ ^ 2 * ‖primeSum131 X α‖ ^ 2 * ‖powerSum131 X α‖ ^ (2 * k) := by
            rw [norm_mul, norm_pow, norm_pow]; ring
        _ ≤ B ^ 2 * ‖primeSum131 X α‖ ^ 2 * Lg X ^ (2 * k) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) hg (by positivity) (by positivity)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hm]
      positivity
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : a ≤ a + 1) hint
    ((((primeSum_continuous131 X).norm.pow 2).intervalIntegrable a (a + 1)).const_mul
      (B ^ 2 * Lg X ^ (2 * k))) hpt
  rw [intervalIntegral.integral_const_mul] at hi
  exact (minor_bessel131 k X P hL).trans (hi.trans
    (mul_le_mul_of_nonneg_left (primeSum_energy131 X a) (by positivity)))

/-- Page 4 before display 7. The minor mean square bound follows unconditionally
from the proved lab Vaughan bound, Mathlib Parseval and elementary Chebyshev. -/
theorem minor_mean_square_proved131 (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ P : ℝ, AdmissibleP131 X P →
        ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
          K * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k + 9) := by
  obtain ⟨X₀, hX₀⟩ := admissible_gap_eventually131
  refine ⟨6 * 97200 ^ 2, by positivity, X₀, fun X hX P hP => ?_⟩
  obtain ⟨hX2, hpar⟩ := hX₀ X hX
  have hQ := (hpar P hP).2.2
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL : 0 < Lg X := Real.logb_pos (by norm_num) (by exact_mod_cast hX2)
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogL : Real.log X ≤ Lg X := by
    unfold Lg
    rw [Real.logb, le_div_iff₀ hl2]
    have hh : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [mul_nonneg hlog (sub_nonneg.mpr hh)]
  have hm := minor_energy131 k X P
    (97200 * (X : ℝ) ^ ((4 : ℝ) / 5) * Real.log X ^ 4) hL.le
    (fun α hα hminor => minor_pointwise131 hX2 hP hQ hα hminor)
  have hpow : ((X : ℝ) ^ ((4 : ℝ) / 5)) ^ 2 * X = (X : ℝ) ^ ((13 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    have he : ((4 : ℝ) / 5) * (2 : ℕ) = 8 / 5 := by norm_num
    rw [he]
    calc (X : ℝ) ^ ((8 : ℝ) / 5) * X = (X : ℝ) ^ ((8 : ℝ) / 5) * (X : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX0]; norm_num
  calc ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2
      ≤ (97200 * (X : ℝ) ^ ((4 : ℝ) / 5) * Real.log X ^ 4) ^ 2 *
          Lg X ^ (2 * k) * (6 * X * Real.log X) := hm
    _ = (6 * 97200 ^ 2) * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k) * Real.log X ^ 9 := by
          rw [← hpow]
          ring
    _ ≤ (6 * 97200 ^ 2) * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k) * Lg X ^ 9 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hlogL 9) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- P0045 Lemma 6.3 on page 10, with an explicit constant from the proved lab Vaughan bound.
The paper states this with an absolute implied constant. -/
theorem lemma63_proved131 {X q : ℕ} (hX : 2 ≤ X) (hq : 1 ≤ q) (hqX : q ≤ X)
    {a : ℤ} (hcop : Int.gcd a q = 1) {α : ℝ}
    (hα : |α - a / q| < 1 / (q : ℝ) ^ 2) :
    ‖primeSum131 X α‖ ≤ 24300 * ((X : ℝ) / Real.sqrt q +
      Real.sqrt ((X : ℝ) * q) + (X : ℝ) ^ ((4 : ℝ) / 5)) * Real.log X ^ 4 := by
  rw [primeSum_eq_ssum131]
  have h := LeanLab.BhowmikGrimmelt2026.vaughan_small_denominator84 hX hq hcop hα hqX
  convert h using 1; ring

end

end LeanLab.LPZ2007
