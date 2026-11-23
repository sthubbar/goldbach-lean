module

public import LeanLab.BakerHarmanPintz1997.DerivativeTest219
public import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150

/-!
ROUTE for `oscillatory_zero_modes508`, part two: the phase of one zero mode.
A term `n ^ ρ * e(n β)` of the Abel form of display 4.6 of P0029 page 15 is `n ^ Re ρ` times
the unit `e(Im ρ / (2π) * log n + n β)`. Sums of these units over a dyadic block are bounded
by the second derivative test, and far out by the Kusmin Landau first derivative test. Both
tests are the proved lab ports in BakerHarmanPintz1997, PortedVanDerCorput and
DerivativeTest219. The survey itself treats only the smoothed centre β = 0; see the QUESTION
on the sharp route in PROGRESS.md.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput in
/-- The lab character `ee` agrees with the ported character `eK`. -/
theorem ee_eq_eK508 (x : ℝ) : ee x = eK x := by
  unfold ee eK
  congr 1
  push_cast
  ring

open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput in
/-- Negating every phase conjugates the sum, so the norm is unchanged. -/
theorem norm_sum_ee_neg508 (s : Finset ℕ) (f : ℕ → ℝ) :
    ‖∑ n ∈ s, ee (-(f n))‖ = ‖∑ n ∈ s, ee (f n)‖ := by
  have h : ∑ n ∈ s, ee (-(f n)) = (starRingEnd ℂ) (∑ n ∈ s, ee (f n)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ee_eq_eK508, ee_eq_eK508, eK_neg]
  rw [h, Complex.norm_conj]

/-- An interval of naturals starting at `p ≥ 1` as a half open interval. -/
theorem Icc_eq_Ioc_pred508 {p : ℕ} (hp : 1 ≤ p) (q : ℕ) :
    Finset.Icc p q = Finset.Ioc (p - 1) q := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- The first difference of the logarithm lies between `0` and `1 / t`. -/
theorem log_first_diff508 {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.log (t + 1) - Real.log t ∧ Real.log (t + 1) - Real.log t ≤ 1 / t := by
  have h1 : Real.log (t + 1) - Real.log t = Real.log ((t + 1) / t) := by
    rw [Real.log_div (by positivity) ht.ne']
  have h2 : (t + 1) / t = 1 + 1 / t := by field_simp
  have h3 : 0 < 1 / t := by positivity
  rw [h1, h2]
  constructor
  · exact Real.log_nonneg (by linarith)
  · have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / t by linarith)
    linarith

/-- The second difference of the logarithm at `t ≥ 1` has size `1 / (t + 1) ^ 2`. -/
theorem log_second_diff508 {t : ℝ} (ht : 1 ≤ t) :
    1 / (t + 1) ^ 2 ≤ 2 * Real.log (t + 1) - Real.log (t + 2) - Real.log t ∧
      2 * Real.log (t + 1) - Real.log (t + 2) - Real.log t ≤ (4 / 3) / (t + 1) ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hy : 0 < t * (t + 2) / (t + 1) ^ 2 := by positivity
  have h1 : Real.log (t * (t + 2) / (t + 1) ^ 2) =
      Real.log t + Real.log (t + 2) - 2 * Real.log (t + 1) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul ht0.ne' (by positivity),
      Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_le_sub_one_of_pos hy
  have h3 := Real.one_sub_inv_le_log_of_pos hy
  have h4 : t * (t + 2) / (t + 1) ^ 2 - 1 = -(1 / (t + 1) ^ 2) := by
    field_simp
    ring
  have h5 : (t * (t + 2) / (t + 1) ^ 2)⁻¹ - 1 = 1 / (t * (t + 2)) := by
    field_simp
    ring
  have h6 : 1 / (t * (t + 2)) ≤ (4 / 3) / (t + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  constructor
  · linarith
  · linarith

/-- P0029 page 15 display 4.6, one term of the Abel form of a zero mode split into its
modulus and its phase. -/
theorem cpow_twist_phase508 {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) (β : ℝ) :
    (n : ℂ) ^ ρ * ee ((n : ℝ) * β) =
      (((n : ℝ) ^ ρ.re : ℝ) : ℂ) *
        ee (ρ.im / (2 * Real.pi) * Real.log n + (n : ℝ) * β) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h : (n : ℂ) ^ ρ =
      (((n : ℝ) ^ ρ.re : ℝ) : ℂ) * ee (ρ.im / (2 * Real.pi) * Real.log n) := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Real.rpow_def_of_pos hnpos]
    unfold ee
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im ρ]
    push_cast
    field_simp
  rw [h, ee_add150, mul_assoc]

open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput in
/-- The second derivative test for the phase sum when `γ < 0`. -/
theorem log_phase_block_vdc_neg508 {γ β : ℝ} (hγ : γ < 0) {N p q : ℕ} (hN : 1 ≤ N)
    (hp : N ≤ p) (hpq : p ≤ q) (hq : q + 1 ≤ 2 * N) :
    ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤
      9 * Real.sqrt |γ| + 41 * (N : ℝ) / Real.sqrt |γ| := by
  have hp1 : 1 ≤ p := le_trans hN hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hγa : 0 < |γ| := abs_pos.mpr hγ.ne
  have hκ : 0 < |γ| / (2 * Real.pi) := by positivity
  have hγκ : γ / (2 * Real.pi) = -(|γ| / (2 * Real.pi)) := by
    rw [abs_of_neg hγ]; ring
  rw [Icc_eq_Ioc_pred508 hp1]
  simp_rw [ee_eq_eK508]
  have hlam : 0 < |γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2) := by positivity
  have key : ∀ n : ℕ, p - 1 < n → n < q →
      |γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2) ≤
        ((γ / (2 * Real.pi) * Real.log ((n + 1 + 1 : ℕ) : ℝ) + ((n + 1 + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β)) -
        ((γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β)) ∧
      ((γ / (2 * Real.pi) * Real.log ((n + 1 + 1 : ℕ) : ℝ) + ((n + 1 + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β)) -
        ((γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β)) ≤
        16 / 3 * (|γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2)) := by
    intro n h1 h2
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    have hn2 : (n : ℝ) + 1 ≤ 2 * N := by exact_mod_cast (show n + 1 ≤ 2 * N by omega)
    have ht : (1 : ℝ) ≤ n := le_trans hNr hnN
    obtain ⟨h3, h4⟩ := log_second_diff508 ht
    have e : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, e1, hγκ]
    have hD : ((-(|γ| / (2 * Real.pi)) * Real.log ((n : ℝ) + 2) + ((n : ℝ) + 2) * β) -
          (-(|γ| / (2 * Real.pi)) * Real.log ((n : ℝ) + 1) + ((n : ℝ) + 1) * β)) -
        ((-(|γ| / (2 * Real.pi)) * Real.log ((n : ℝ) + 1) + ((n : ℝ) + 1) * β) -
          (-(|γ| / (2 * Real.pi)) * Real.log (n : ℝ) + (n : ℝ) * β)) =
        |γ| / (2 * Real.pi) *
          (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
      ring
    rw [hD]
    have h5 : 1 / (4 * (N : ℝ) ^ 2) ≤ 1 / ((n : ℝ) + 1) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h6 : (4 / 3) / ((n : ℝ) + 1) ^ 2 ≤ (4 / 3) / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have h7 : |γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2) =
        |γ| / (2 * Real.pi) * (1 / (4 * (N : ℝ) ^ 2)) := by ring
    have h8 : 16 / 3 * (|γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2)) =
        |γ| / (2 * Real.pi) * ((4 / 3) / (N : ℝ) ^ 2) := by
      field_simp
      ring
    rw [h8, h7]
    exact ⟨mul_le_mul_of_nonneg_left (h5.trans h3) hκ.le,
      mul_le_mul_of_nonneg_left (h4.trans h6) hκ.le⟩
  have hv := vdC_second_derivative
    (f := fun n : ℕ => γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β)
    (a := p - 1) (b := q) (lam := |γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2)) (c := 16 / 3)
    (by omega) hlam (by norm_num) (fun n h1 h2 => (key n h1 h2).1)
    (fun n h1 h2 => (key n h1 h2).2)
  refine hv.trans ?_
  have hs : 0 < Real.sqrt |γ| := Real.sqrt_pos.mpr hγa
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : Real.sqrt |γ| ^ 2 = |γ| := Real.sq_sqrt hγa.le
  have hr2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hrlo : 64 / 27 ≤ Real.sqrt (2 * Real.pi) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have hrhi : Real.sqrt (2 * Real.pi) ≤ 41 / 16 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hsl : Real.sqrt (|γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2)) =
      Real.sqrt |γ| / (2 * N * Real.sqrt (2 * Real.pi)) := by
    have : |γ| / (2 * Real.pi) / (4 * (N : ℝ) ^ 2) =
        (Real.sqrt |γ| / (2 * N * Real.sqrt (2 * Real.pi))) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, hs2, hr2]
      field_simp
      ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsl]
  have hlen : (q : ℝ) - ((p - 1 : ℕ) : ℝ) ≤ N := by
    have h1 : (q : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hq
    have h2 : (N : ℝ) ≤ p := by exact_mod_cast hp
    rw [Nat.cast_sub hp1]
    push_cast
    linarith
  have hA : 16 / 3 * ((q : ℝ) - ((p - 1 : ℕ) : ℝ)) *
      (Real.sqrt |γ| / (2 * N * Real.sqrt (2 * Real.pi))) ≤
      16 / 3 * (N : ℝ) * (Real.sqrt |γ| / (2 * N * Real.sqrt (2 * Real.pi))) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hA2 : 16 / 3 * (N : ℝ) * (Real.sqrt |γ| / (2 * N * Real.sqrt (2 * Real.pi))) =
      8 / 3 * (Real.sqrt |γ| / Real.sqrt (2 * Real.pi)) := by
    field_simp
    ring
  have hA3 : Real.sqrt |γ| / Real.sqrt (2 * Real.pi) ≤ Real.sqrt |γ| * (27 / 64) := by
    rw [div_le_iff₀ hr]
    nlinarith
  have hB : 1 / (Real.sqrt |γ| / (2 * N * Real.sqrt (2 * Real.pi))) =
      2 * N * Real.sqrt (2 * Real.pi) / Real.sqrt |γ| := by
    rw [one_div_div]
  have hB2 : 8 * (2 * N * Real.sqrt (2 * Real.pi) / Real.sqrt |γ|) ≤
      41 * (N : ℝ) / Real.sqrt |γ| := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith
  rw [hB]
  linarith

/-- P0029 page 15 display 4.6, the phase sum of one zero mode over part of a dyadic
block `[N, 2N - 1]`, by the second derivative test. The second difference of the phase is
`γ / (2π) * log (1 - 1 / (n + 1) ^ 2)`, of size `|γ| / N ^ 2` on the block. -/
theorem log_phase_block_vdc508 {γ β : ℝ} (hγ : γ ≠ 0) {N p q : ℕ} (hN : 1 ≤ N)
    (hp : N ≤ p) (hpq : p ≤ q) (hq : q + 1 ≤ 2 * N) :
    ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤
      9 * Real.sqrt |γ| + 41 * (N : ℝ) / Real.sqrt |γ| := by
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · exact log_phase_block_vdc_neg508 hneg hN hp hpq hq
  · have h := log_phase_block_vdc_neg508 (γ := -γ) (β := -β) (by linarith) hN hp hpq hq
    have e : ∑ n ∈ Finset.Icc p q, ee (-γ / (2 * Real.pi) * Real.log n + (n : ℝ) * -β) =
        ∑ n ∈ Finset.Icc p q, ee (-(γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)) :=
      Finset.sum_congr rfl fun n _ => by congr 1; ring
    rw [e, norm_sum_ee_neg508, abs_neg] at h
    exact h

open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput in
/-- The Kusmin Landau test for the phase sum when `γ ≤ 0`. -/
theorem log_phase_tail_kl_nonpos508 {γ β : ℝ} (hγ0 : γ ≤ 0) (hβ0 : β ≠ 0)
    (hβ : |β| ≤ 1 / 2) {p q : ℕ}
    (hp : 1 ≤ p) (_hpq : p ≤ q) (hγ : |γ| ≤ Real.pi * |β| * p) :
    ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤
      2 / |β| := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hβa : 0 < |β| := abs_pos.mpr hβ0
  have hκ : 0 ≤ |γ| / (2 * Real.pi) := by positivity
  have hγκ : γ / (2 * Real.pi) = -(|γ| / (2 * Real.pi)) := by
    rw [abs_of_nonpos hγ0]; ring
  rw [Icc_eq_Ioc_pred508 hp]
  simp_rw [ee_eq_eK508]
  have hκp : |γ| / (2 * Real.pi) * (1 / (p : ℝ)) ≤ |β| / 2 := by
    have : |γ| / (2 * Real.pi) * (1 / (p : ℝ)) = |γ| / (2 * Real.pi * p) := by
      field_simp
    rw [this, div_le_iff₀ (by positivity)]
    have : |β| / 2 * (2 * Real.pi * p) = Real.pi * |β| * p := by ring
    linarith
  have step : ∀ n : ℕ, p - 1 < n →
      (γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β) ≤ β ∧
      β - |β| / 2 ≤ (γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β) := by
    intro n h1
    have hnp : (p : ℝ) ≤ n := by exact_mod_cast (show p ≤ n by omega)
    have ht : (0 : ℝ) < n := by linarith
    obtain ⟨h3, h4⟩ := log_first_diff508 ht
    have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e1, hγκ]
    have hD : (-(|γ| / (2 * Real.pi)) * Real.log ((n : ℝ) + 1) + ((n : ℝ) + 1) * β) -
          (-(|γ| / (2 * Real.pi)) * Real.log (n : ℝ) + (n : ℝ) * β) =
        β - |γ| / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      ring
    rw [hD]
    have h5 : 1 / (n : ℝ) ≤ 1 / (p : ℝ) := one_div_le_one_div_of_le (by linarith) hnp
    have h6 : |γ| / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ |β| / 2 :=
      (mul_le_mul_of_nonneg_left (h4.trans h5) hκ).trans hκp
    have h7 : 0 ≤ |γ| / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      mul_nonneg hκ h3
    constructor <;> linarith
  have mono : ∀ n : ℕ, p - 1 < n → n < q →
      (γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β) ≤
      (γ / (2 * Real.pi) * Real.log ((n + 2 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) * β) -
          (γ / (2 * Real.pi) * Real.log ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * β) := by
    intro n h1 _
    have hnp : (p : ℝ) ≤ n := by exact_mod_cast (show p ≤ n by omega)
    have ht : (1 : ℝ) ≤ n := by linarith
    obtain ⟨h3, _⟩ := log_second_diff508 ht
    have e : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, e1, hγκ]
    have h4 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ 2 := by positivity
    have h5 : 0 ≤ |γ| / (2 * Real.pi) *
        (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) :=
      mul_nonneg hκ (h4.trans h3)
    linarith
  have hfin : 1 / (|β| / 2) = 2 / |β| := by rw [one_div_div]
  rw [← hfin]
  rcases lt_or_gt_of_ne hβ0 with hneg | hpos
  · have hab : |β| = -β := abs_of_neg hneg
    exact kusmin_landau
      (f := fun n : ℕ => γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β)
      (a := p - 1) (b := q) (δ := |β| / 2) (m := -1) (by positivity) (by linarith)
      (fun n h1 _ => by have := (step n h1).2; push_cast at this ⊢; linarith)
      (fun n h1 _ => by have := (step n h1).1; push_cast at this ⊢; linarith)
      mono
  · have hab : |β| = β := abs_of_pos hpos
    exact kusmin_landau
      (f := fun n : ℕ => γ / (2 * Real.pi) * Real.log (n : ℝ) + (n : ℝ) * β)
      (a := p - 1) (b := q) (δ := |β| / 2) (m := 0) (by positivity) (by linarith)
      (fun n h1 _ => by have := (step n h1).2; push_cast at this ⊢; linarith)
      (fun n h1 _ => by have := (step n h1).1; push_cast at this ⊢; linarith)
      mono

/-- P0029 page 15 display 4.6, the phase sum of one zero mode beyond the stationary
range, by the Kusmin Landau first derivative test. For `n ≥ |γ| / (π |β|)` the first
difference of the phase stays between `β / 2` and `3 β / 2` and is monotone. -/
theorem log_phase_tail_kl508 {γ β : ℝ} (hβ0 : β ≠ 0) (hβ : |β| ≤ 1 / 2) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hγ : |γ| ≤ Real.pi * |β| * p) :
    ‖∑ n ∈ Finset.Icc p q, ee (γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)‖ ≤
      2 / |β| := by
  rcases le_or_gt γ 0 with hneg | hpos
  · exact log_phase_tail_kl_nonpos508 hneg hβ0 hβ hp hpq hγ
  · have h := log_phase_tail_kl_nonpos508 (γ := -γ) (β := -β) (by linarith)
      (neg_ne_zero.mpr hβ0) (by rwa [abs_neg]) hp hpq (by rwa [abs_neg, abs_neg])
    have e : ∑ n ∈ Finset.Icc p q, ee (-γ / (2 * Real.pi) * Real.log n + (n : ℝ) * -β) =
        ∑ n ∈ Finset.Icc p q, ee (-(γ / (2 * Real.pi) * Real.log n + (n : ℝ) * β)) :=
      Finset.sum_congr rfl fun n _ => by congr 1; ring
    rw [e, norm_sum_ee_neg508, abs_neg] at h
    exact h

end LeanLab.BhowmikGrimmelt2026
