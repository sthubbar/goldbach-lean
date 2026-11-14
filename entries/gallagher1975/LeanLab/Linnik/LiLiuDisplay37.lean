module

public import LeanLab.Linnik.LiLiuLemma43Int
public import Mathlib.NumberTheory.Chebyshev

/-!
Li-Liu, arXiv 2610.15784 v1, Section 4, proof of Lemma 4.3, display (37), the central arc input:
  (1/N) ∫_{-T/N}^{T/N} |S(β)|² dβ = ∫_{-T}^{T} |∫_0^1 e(ut) dt|² du + o_T(1) = 1 + O(1/T) + o_T(1),
with S(α) = ∑_{N₁ < p ≤ N} (log p) e(pα), N₁ = N^{1-κ}. Read through WebFetch on
arxiv.org/html/2610.15784, run 20261021T0703Z-4724, unit U-1379. The paper derives (37) from
"the prime number theorem and partial summation, uniformly for |u| ≤ T,
S(u/N)/N = ∫_0^1 e(ut) dt + o_T(1)" and Plancherel.

This file discharges the one-sided form of (37) that `lemma43_lower_conditional` takes, with an
explicit constant and no prime number theorem, through a Fejér kernel:
* `G_eq`, `G_nonneg`, `G_ge`: the Fejér weight G(c) = ∫_{-δ}^{δ} (1 - |β|/δ) cos(cβ) dβ equals
  2(1 - cos cδ)/(δc²), is nonnegative, and is at least 4δ/π² when |cδ| ≤ π;
* `normSq_expand`: |S(β)|² = ∑_m ∑_n a_m a_n cos(2π(m - n)β) for real weights;
* `fejer_lower`: for nonnegative weights on any finite A ⊆ [0, N],
  ∫_{-δ}^{δ} |S|² ≥ (4δ/π²) (∑_A a)² / (⌊2δN⌋ + 1), by blocks of length 1/(2δ) and Cauchy;
* `display37_weak`: with A the primes in (M, N], a = log and δ = T/N,
  ∫_{-T/N}^{T/N} |S|² ≥ (4T/(π²(2T + 1))) (θ(N) - θ(M))²/N, unconditional;
* `lemma43_lower_explicit`: R₁(0) ≥ (4T/(π²(2T + 1))) ((θ(N) - θ(M))/N)² N log(Q + 1),
  unconditional, the lower half of (36) up to a constant factor;
* `Display37`: the paper's (37) as a named Prop, and `lemma43_lower_of_display37`, the lower half
  of (36) at level (I(T) - ε) CONDITIONAL ON it.

Unit U-1379, PC run 20261021T0703Z-4724. AI-written Lean code, Claude. KNOWN mathematics: the
Fejér kernel bound is the standard positive-definite kernel trick. Nothing here is progress on
Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.LiLiuDisplay37

open MeasureTheory Set Real Finset
open LeanLab.Linnik.LiLiuLemma43 LeanLab.Linnik.LiLiuLemma43Int
open LeanLab.PNTPort.LargeSieve

/-! ## The Fejér weight -/

/-- `G δ c = ∫_{-δ}^{δ} (1 - |β|/δ) cos(cβ) dβ`. -/
noncomputable def G (δ c : ℝ) : ℝ := ∫ β in (-δ)..δ, (1 - |β| / δ) * Real.cos (c * β)

lemma half_ne {δ c : ℝ} (hδ : 0 < δ) (hc : c ≠ 0) :
    ∫ β in (0 : ℝ)..δ, (1 - β / δ) * Real.cos (c * β) = (1 - Real.cos (c * δ)) / (δ * c ^ 2) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) δ, HasDerivAt
      (fun β => (1 - β / δ) * (Real.sin (c * β) / c) - Real.cos (c * β) / (δ * c ^ 2))
      ((1 - x / δ) * Real.cos (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun β : ℝ => 1 - β / δ) (-(1 / δ)) x := by
      simpa using ((hasDerivAt_id x).div_const δ).const_sub 1
    have h2 : HasDerivAt (fun β : ℝ => Real.sin (c * β) / c) (Real.cos (c * x) * c / c) x := by
      have := ((hasDerivAt_id x).const_mul c).sin
      simpa using this.div_const c
    have h3 : HasDerivAt (fun β : ℝ => Real.cos (c * β) / (δ * c ^ 2))
        (-Real.sin (c * x) * c / (δ * c ^ 2)) x := by
      have := ((hasDerivAt_id x).const_mul c).cos
      simpa using this.div_const (δ * c ^ 2)
    convert (h1.mul h2).sub h3 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => (1 - x / δ) * Real.cos (c * x)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.sin_zero, zero_div, Real.cos_zero, div_self hδ.ne', sub_self,
    zero_mul, mul_zero, zero_sub]
  field_simp
  ring

lemma half_zero {δ : ℝ} (hδ : 0 < δ) :
    ∫ β in (0 : ℝ)..δ, (1 - β / δ) * Real.cos (0 * β) = δ / 2 := by
  simp only [zero_mul, Real.cos_zero, mul_one]
  have hd : ∀ x ∈ uIcc (0 : ℝ) δ, HasDerivAt (fun β : ℝ => β - β ^ 2 / (2 * δ))
      (1 - x / δ) x := by
    intro x _
    have := (hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).div_const (2 * δ))
    convert this using 1
    · funext β; simp only [Pi.sub_apply, id]
    · norm_num; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => 1 - x / δ).intervalIntegrable _ _)]
  field_simp
  ring

lemma G_eq_two_half {δ c : ℝ} (hδ : 0 < δ) :
    G δ c = 2 * ∫ β in (0 : ℝ)..δ, (1 - β / δ) * Real.cos (c * β) := by
  set f : ℝ → ℝ := fun β => (1 - |β| / δ) * Real.cos (c * β) with hf
  have hfc : Continuous f := by fun_prop
  have heven : ∀ x, f (-x) = f x := by
    intro x; simp [hf, abs_neg, Real.cos_neg, mul_neg]
  have hneg : ∫ β in (-δ)..0, f β = ∫ β in (0 : ℝ)..δ, f β := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := δ) f
    simp only [heven, neg_zero] at this
    exact this.symm
  have hpos : ∫ β in (0 : ℝ)..δ, f β =
      ∫ β in (0 : ℝ)..δ, (1 - β / δ) * Real.cos (c * β) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hδ.le] at hx
    simp [hf, abs_of_nonneg hx.1]
  unfold G
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _), hneg, hpos]
  ring

/-- The Fejér weight in closed form, `c ≠ 0`. -/
theorem G_eq {δ c : ℝ} (hδ : 0 < δ) (hc : c ≠ 0) :
    G δ c = 2 * (1 - Real.cos (c * δ)) / (δ * c ^ 2) := by
  rw [G_eq_two_half hδ, half_ne hδ hc]; ring

theorem G_zero {δ : ℝ} (hδ : 0 < δ) : G δ 0 = δ := by
  rw [G_eq_two_half hδ, half_zero hδ]; ring

theorem G_nonneg {δ : ℝ} (hδ : 0 < δ) (c : ℝ) : 0 ≤ G δ c := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [G_zero hδ]; exact hδ.le
  · rw [G_eq hδ hc]
    have := Real.cos_le_one (c * δ)
    apply div_nonneg (by linarith) (by positivity)

/-- `G δ c ≥ 4δ/π²` once `|cδ| ≤ π`, from `cos x ≤ 1 - 2x²/π²`. -/
theorem G_ge {δ c : ℝ} (hδ : 0 < δ) (hcδ : |c * δ| ≤ π) : 4 * δ / π ^ 2 ≤ G δ c := by
  have hπ : (0 : ℝ) < π ^ 2 := by positivity
  rcases eq_or_ne c 0 with rfl | hc
  · rw [G_zero hδ, div_le_iff₀ hπ]
    have : (4 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith
  · rw [G_eq hδ hc]
    have hcos := Real.cos_le_one_sub_mul_cos_sq hcδ
    have hc2 : 0 < c ^ 2 := by positivity
    rw [div_le_div_iff₀ hπ (by positivity)]
    have : 2 / π ^ 2 * (c * δ) ^ 2 ≤ 1 - Real.cos (c * δ) := by linarith
    have h' : 2 * (c * δ) ^ 2 ≤ π ^ 2 * (1 - Real.cos (c * δ)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at this; linarith
    nlinarith

/-! ## Expanding |S|² -/

lemma e_mul_conj_re (x y : ℝ) :
    (e x * (starRingEnd ℂ) (e y)).re = Real.cos (2 * π * (x - y)) := by
  rw [← e_neg, ← e_add, e]
  rw [show (Complex.I * ((2 * π * (x + -y) : ℝ) : ℂ)) = ((2 * π * (x - y) : ℝ) : ℂ) * Complex.I by
    rw [mul_comm]; congr 2]
  exact Complex.exp_ofReal_mul_I_re _

/-- `|S(β)|² = ∑_m ∑_n a_m a_n cos(2π(m - n)β)` for real weights. -/
theorem normSq_expand (A : Finset ℕ) (a : ℕ → ℝ) (β : ℝ) :
    ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 =
      ∑ m ∈ A, ∑ n ∈ A, a m * a n * Real.cos ((2 * π * ((m : ℝ) - n)) * β) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj]
  unfold SA
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro m _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro n _
  rw [map_mul, Complex.conj_ofReal,
    show (a m : ℂ) * e (m * β) * ((a n : ℂ) * (starRingEnd ℂ) (e (n * β))) =
      ((a m * a n : ℝ) : ℂ) * (e (m * β) * (starRingEnd ℂ) (e (n * β))) by push_cast; ring,
    Complex.re_ofReal_mul, e_mul_conj_re]
  congr 2; ring

/-! ## The Fejér lower bound -/

lemma int_fejer_eq (A : Finset ℕ) (a : ℕ → ℝ) {δ : ℝ} :
    ∫ β in (-δ)..δ, (1 - |β| / δ) * ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 =
      ∑ m ∈ A, ∑ n ∈ A, a m * a n * G δ (2 * π * ((m : ℝ) - n)) := by
  simp_rw [normSq_expand, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro m _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro n _
      unfold G
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext β; ring
    · intro n _; exact (by fun_prop : Continuous fun β : ℝ =>
        (1 - |β| / δ) * (a m * a n * Real.cos (2 * π * ((m : ℝ) - n) * β))).intervalIntegrable _ _
  · intro m _
    exact (continuous_finsetSum _ fun n _ => (by fun_prop : Continuous fun β : ℝ =>
        (1 - |β| / δ) * (a m * a n * Real.cos (2 * π * ((m : ℝ) - n) * β)))).intervalIntegrable _ _

/-- The block index `⌊2δn⌋`. -/
noncomputable def blk (δ : ℝ) (n : ℕ) : ℕ := ⌊2 * δ * n⌋₊

lemma same_blk {δ : ℝ} (hδ : 0 < δ) {m n : ℕ} (h : blk δ m = blk δ n) :
    |2 * π * ((m : ℝ) - n) * δ| ≤ π := by
  unfold blk at h
  have hm0 : 0 ≤ 2 * δ * (m : ℝ) := by positivity
  have hn0 : 0 ≤ 2 * δ * (n : ℝ) := by positivity
  have a1 := Nat.floor_le hm0
  have a2 := Nat.lt_floor_add_one (2 * δ * (m : ℝ))
  have b1 := Nat.floor_le hn0
  have b2 := Nat.lt_floor_add_one (2 * δ * (n : ℝ))
  rw [h] at a1 a2
  have : |2 * δ * (m : ℝ) - 2 * δ * n| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [show 2 * π * ((m : ℝ) - n) * δ = π * (2 * δ * (m : ℝ) - 2 * δ * n) by ring, abs_mul,
    abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- **Fejér lower bound.** For nonnegative weights on a finite `A ⊆ [0, N]` and `δ > 0`:
`∫_{-δ}^{δ} |S|² ≥ (4δ/π²) (∑_A a)² / (⌊2δN⌋ + 1)`. PROVED unconditional. -/
theorem fejer_lower (A : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n ∈ A, 0 ≤ a n) {δ : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hAN : ∀ n ∈ A, n ≤ N) :
    4 * δ / π ^ 2 * (∑ n ∈ A, a n) ^ 2 / ((⌊2 * δ * N⌋₊ : ℝ) + 1) ≤
      ∫ β in (-δ)..δ, ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 := by
  set B := ⌊2 * δ * N⌋₊ + 1 with hB
  set s : ℕ → ℝ := fun j => ∑ n ∈ A.filter (fun n => blk δ n = j), a n with hs
  have hmaps : ∀ n ∈ A, blk δ n ∈ range B := by
    intro n hn
    rw [Finset.mem_range, hB, Nat.lt_add_one_iff]
    apply Nat.floor_le_floor
    have : (n : ℝ) ≤ N := by exact_mod_cast hAN n hn
    nlinarith
  have hsum : ∑ j ∈ range B, s j = ∑ n ∈ A, a n :=
    Finset.sum_fiberwise_of_maps_to hmaps a
  have hsq : ∑ n ∈ A, a n * s (blk δ n) = ∑ j ∈ range B, s j ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl; intro j _
    rw [hs, sq, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro n hn
    rw [(Finset.mem_filter.mp hn).2]
  have hκ : 0 ≤ 4 * δ / π ^ 2 := by positivity
  -- the double sum dominates the block-diagonal part
  have hdbl : 4 * δ / π ^ 2 * ∑ n ∈ A, a n * s (blk δ n) ≤
      ∑ m ∈ A, ∑ n ∈ A, a m * a n * G δ (2 * π * ((m : ℝ) - n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro m hm
    calc 4 * δ / π ^ 2 * (a m * s (blk δ m))
        = ∑ n ∈ A.filter (fun n => blk δ n = blk δ m), a m * a n * (4 * δ / π ^ 2) := by
          rw [hs]; simp only; rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n _; ring
      _ ≤ ∑ n ∈ A.filter (fun n => blk δ n = blk δ m),
            a m * a n * G δ (2 * π * ((m : ℝ) - n)) := by
          apply Finset.sum_le_sum; intro n hn
          rw [Finset.mem_filter] at hn
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ha m hm) (ha n hn.1))
          exact G_ge hδ (same_blk hδ hn.2.symm)
      _ ≤ ∑ n ∈ A, a m * a n * G δ (2 * π * ((m : ℝ) - n)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro n hn _
          exact mul_nonneg (mul_nonneg (ha m hm) (ha n hn)) (G_nonneg hδ _)
  have hcs : (∑ n ∈ A, a n) ^ 2 ≤ (B : ℝ) * ∑ j ∈ range B, s j ^ 2 := by
    rw [← hsum]
    have := sq_sum_le_card_mul_sum_sq (s := range B) (f := s)
    simpa using this
  have hBpos : (0 : ℝ) < B := by positivity
  have hBcast : ((⌊2 * δ * N⌋₊ : ℝ) + 1) = B := by rw [hB]; push_cast; ring
  have hmono : ∫ β in (-δ)..δ, (1 - |β| / δ) * ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 ≤
      ∫ β in (-δ)..δ, ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 := by
    have hc : Continuous fun β => ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 :=
      (SA_continuous A _).norm.pow 2
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact ((by fun_prop : Continuous fun β : ℝ => 1 - |β| / δ).mul hc).intervalIntegrable _ _
    · exact hc.intervalIntegrable _ _
    · intro β hβ
      have h0 : 0 ≤ ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 := by positivity
      have h1 : 0 ≤ |β| / δ := by positivity
      nlinarith
  rw [hBcast, int_fejer_eq] at *
  calc 4 * δ / π ^ 2 * (∑ n ∈ A, a n) ^ 2 / (B : ℝ)
      ≤ 4 * δ / π ^ 2 * ((B : ℝ) * ∑ j ∈ range B, s j ^ 2) / B := by
        apply div_le_div_of_nonneg_right _ hBpos.le
        exact mul_le_mul_of_nonneg_left hcs hκ
    _ = 4 * δ / π ^ 2 * ∑ n ∈ A, a n * s (blk δ n) := by
        rw [hsq]; field_simp
    _ ≤ _ := hdbl
    _ ≤ _ := hmono

/-! ## Display (37), one-sided, for the primes in (M, N] with log weights -/

/-- The primes in `(M, N]`. -/
def primesIn (M N : ℕ) : Finset ℕ := (Finset.Ioc M N).filter Nat.Prime

/-- The log weights, as complex numbers. -/
noncomputable def logw : ℕ → ℂ := fun n => ((Real.log n : ℝ) : ℂ)

lemma sum_primesIn {M N : ℕ} (hMN : M ≤ N) :
    ∑ p ∈ primesIn M N, Real.log p = Chebyshev.theta N - Chebyshev.theta M := by
  rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast, primesIn,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN]
  ring

/-- **Display (37), one-sided, explicit, unconditional.** With `S(β) = ∑_{M < p ≤ N} log p e(pβ)`
and `δ = T/N`: `∫_{-T/N}^{T/N} |S|² ≥ (4T/(π²(2T + 1))) (θ(N) - θ(M))²/N`. -/
theorem display37_weak {M N : ℕ} {T : ℝ} (hT : 0 < T) (hN : 0 < N) (hMN : M ≤ N) :
    4 * T / (π ^ 2 * (2 * T + 1)) * (Chebyshev.theta N - Chebyshev.theta M) ^ 2 / N ≤
      ∫ β in (-(T / N))..(T / N), ‖SA (primesIn M N) logw β‖ ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < T / N := by positivity
  have h := fejer_lower (primesIn M N) (fun n => Real.log n)
    (fun n _ => Real.log_natCast_nonneg n) hδ
    (fun n hn => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2) (N := N)
  rw [sum_primesIn hMN] at h
  refine le_trans ?_ h
  have hfl : (⌊2 * (T / N) * N⌋₊ : ℝ) + 1 ≤ 2 * T + 1 := by
    have : 2 * (T / N) * (N : ℝ) = 2 * T := by field_simp
    rw [this]
    linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)]
  have hpos : (0 : ℝ) < (⌊2 * (T / N) * N⌋₊ : ℝ) + 1 := by positivity
  set D := (Chebyshev.theta N - Chebyshev.theta M) ^ 2
  have hD : 0 ≤ D := by positivity
  rw [show 4 * T / (π ^ 2 * (2 * T + 1)) * D / N = 4 * (T / N) / π ^ 2 * D / (2 * T + 1) by
    field_simp]
  apply div_le_div_of_nonneg_left _ hpos hfl
  positivity

/-- **Lemma 4.3, lower half, explicit constant, PROVED unconditional.** For `Q ≤ M ≤ N`,
`Q T ≤ P`, `Q ≤ P` and `2P² < TN`:
`R₁(0) ≥ (4T/(π²(2T + 1))) ((θ(N) - θ(M))/N)² N log(Q + 1)`. -/
theorem lemma43_lower_explicit {M N Q : ℕ} {P T : ℝ} (hT : 0 < T) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hQM : Q ≤ M) (hMN : M ≤ N) (hQP : (Q : ℝ) ≤ P) (hQT : (Q : ℝ) * T ≤ P)
    (hP : 2 * P ^ 2 < T * N) :
    4 * T / (π ^ 2 * (2 * T + 1)) * ((Chebyshev.theta N - Chebyshev.theta M) / N) ^ 2 * N *
      Real.log ((Q : ℝ) + 1) ≤ R10 (primesIn M N) logw P N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := params_ok hT hNr hQT hP
  have hA : ∀ p ∈ primesIn M N, p.Prime ∧ Q < p := by
    intro p hp
    rw [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, by omega⟩
  have h37 := display37_weak hT hN hMN (M := M)
  have := lemma43_lower_conditional (primesIn M N) logw hA (by positivity) hNr hQ hQP h1 h2
    (c := 4 * T / (π ^ 2 * (2 * T + 1)) * ((Chebyshev.theta N - Chebyshev.theta M) / N) ^ 2)
    (by
      refine le_trans (le_of_eq ?_) h37
      field_simp)
  exact this

/-! ## The paper's (37) as a named Prop, and the lower half of (36) conditional on it -/

/-- `I(T) = ∫_{-T}^{T} |∫_0^1 e(ut) dt|² du`, the right side of (37). -/
noncomputable def I (T : ℝ) : ℝ :=
  ∫ u in (-T)..T, ‖∫ t in (0 : ℝ)..1, e (u * t)‖ ^ 2

/-- **Display (37)** of Li-Liu, exactly: for `N₁ = ⌊N^{1-κ}⌋` and each fixed `T ≥ 1`,
`(1/N) ∫_{-T/N}^{T/N} |S|² → I(T)` as `N → ∞`. -/
def Display37 (κ : ℝ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → Filter.Tendsto
    (fun N : ℕ => (1 / (N : ℝ)) * ∫ β in (-(T / N))..(T / N),
      ‖SA (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw β‖ ^ 2)
    Filter.atTop (nhds (I T))

/-- **Lemma 4.3 lower half, CONDITIONAL ON `Display37 κ`.** For each `T ≥ 1` and `ε > 0`,
eventually in `N`, for every `Q ≤ N₁` meeting the arc conditions,
`R₁(0) ≥ (I(T) - ε) N log(Q + 1)`. -/
theorem lemma43_lower_of_display37 {κ : ℝ} (h : Display37 κ) {T ε : ℝ} (hT : 1 ≤ T)
    (hε : 0 < ε) : ∀ᶠ N : ℕ in Filter.atTop, ∀ (Q : ℕ) (P : ℝ), 1 ≤ Q →
      Q ≤ ⌊(N : ℝ) ^ (1 - κ)⌋₊ → (Q : ℝ) ≤ P → (Q : ℝ) * T ≤ P → 2 * P ^ 2 < T * N →
      (I T - ε) * N * Real.log ((Q : ℝ) + 1) ≤
        R10 (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw P N := by
  have hev := (h T hT).eventually (lt_mem_nhds (show I T - ε < I T by linarith))
  filter_upwards [hev, Filter.eventually_gt_atTop 0] with N hN hN0 Q P hQ hQM hQP hQT hP
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hT0 : 0 < T := by linarith
  obtain ⟨h1, h2⟩ := params_ok hT0 hNr hQT hP
  have hA : ∀ p ∈ primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N, p.Prime ∧ Q < p := by
    intro p hp
    rw [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, by omega⟩
  apply lemma43_lower_conditional _ logw hA (by positivity) hNr hQ hQP h1 h2
  have := hN.le
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hNr] at this
  exact this

/-- Vacuity of `display37_weak` and `lemma43_lower_explicit`: N = 10⁶, M = Q = 100, T = 1,
P = 100 meet every hypothesis. -/
theorem vacuity :
    (0 : ℝ) < 1 ∧ 0 < (10 ^ 6 : ℕ) ∧ 1 ≤ (100 : ℕ) ∧ (100 : ℕ) ≤ 100 ∧ (100 : ℕ) ≤ 10 ^ 6 ∧
      ((100 : ℕ) : ℝ) ≤ 100 ∧ ((100 : ℕ) : ℝ) * 1 ≤ 100 ∧
      2 * (100 : ℝ) ^ 2 < 1 * ((10 ^ 6 : ℕ) : ℝ) := by
  norm_num

end LeanLab.Linnik.LiLiuDisplay37
