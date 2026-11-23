module

public import LeanLab.LZCesaroShort.Lemma7Proof

/-!
# P0058 Lemma 8, proved

Lab proof, unit U-5322, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input. Languasco-Zaccagnini Lemma 8,
`Σ_{n=N-H}^{N+H} (H - |n - N|)(ψ(n) - n) = -S + O(HN)`, from the lab's explicit formula for
`ψ₁(x)/x`: the triangle sum is the second difference of the double partial sums, which differ
from `∫ ψ₁` by `O(HN)` after differencing, and `∫ ψ₁` is given by the explicit formula
integrated term by term. Binary Goldbach is open.
-/

@[expose] public section


open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.LZCesaroShort

/-- `A₁(j) = Σ_{i ≤ j} a(i)`. -/
def A1 (a : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), a i

/-- `A₂(m) = Σ_{j < m} A₁(j)`. -/
def A2 (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ range m, A1 a j

/-- The triangle sum is a second difference. -/
lemma tri_identity (a : ℕ → ℝ) (N : ℕ) : ∀ H : ℕ, H ≤ N →
    ∑ n ∈ Ico (N - H) (N + H + 1), ((H : ℝ) - |(n : ℝ) - N|) * a n =
      A2 a (N + H) - 2 * A2 a N + A2 a (N - H) := by
  intro H
  induction H with
  | zero =>
    intro _
    simp [A2, A1]
    ring
  | succ H ih =>
    intro hH
    have ih' := ih (by omega)
    have e1 : N - (H + 1) + 1 = N - H := by omega
    -- split off the two endpoints, weight 0
    have hlo : N - (H + 1) < N + (H + 1) + 1 := by omega
    rw [sum_eq_sum_Ico_succ_bot hlo, e1, show N + (H + 1) + 1 = (N + H + 1) + 1 by ring,
      sum_Ico_succ_top (by omega)]
    have w1 : ((H + 1 : ℕ) : ℝ) - |((N - (H + 1) : ℕ) : ℝ) - N| = 0 := by
      rw [Nat.cast_sub (by omega)]; push_cast
      rw [show (N : ℝ) - (H + 1) - N = -(H + 1) by ring, abs_neg, abs_of_pos (by positivity)]
      ring
    have w2 : ((H + 1 : ℕ) : ℝ) - |((N + H + 1 : ℕ) : ℝ) - N| = 0 := by
      push_cast
      rw [show (N : ℝ) + H + 1 - N = H + 1 by ring, abs_of_pos (by positivity)]
      ring
    rw [w1, w2, zero_mul, zero_mul, zero_add, add_zero]
    have hmid : ∑ n ∈ Ico (N - H) (N + H + 1), (((H + 1 : ℕ) : ℝ) - |(n : ℝ) - N|) * a n =
        ∑ n ∈ Ico (N - H) (N + H + 1), ((H : ℝ) - |(n : ℝ) - N|) * a n +
          ∑ n ∈ Ico (N - H) (N + H + 1), a n := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro n _; push_cast; ring
    rw [hmid, ih', sum_Ico_eq_sub _ (by omega)]
    have h2 : A2 a (N + (H + 1)) = A2 a (N + H) + ∑ i ∈ range (N + H + 1), a i := by
      rw [show N + (H + 1) = (N + H) + 1 by ring, A2, sum_range_succ]; rfl
    have h3 : A2 a (N - H) = A2 a (N - (H + 1)) + ∑ i ∈ range (N - H), a i := by
      rw [A2, A2, show N - H = (N - (H + 1)) + 1 by omega, sum_range_succ, A1]
    rw [h2, h3]
    ring

/-- `Σ_{i ≤ m} ψ(i) = Σ_{k ≤ m} Λ(k)(m + 1 - k)`. -/
lemma A1_psi (m : ℕ) : A1 (fun i => ψ (i : ℝ)) m = ∑ k ∈ range (m + 1), Λ k * ((m : ℝ) + 1 - k) := by
  induction m with
  | zero => simp [A1, psi_nat]
  | succ m ih =>
    rw [A1, sum_range_succ, ← A1, ih, psi_nat,
      sum_range_succ (fun k => Λ k * (((m + 1 : ℕ) : ℝ) + 1 - k)) (m + 1),
      sum_range_succ (fun k => Λ k) (m + 1)]
    have : ∑ k ∈ range (m + 1), Λ k * (((m + 1 : ℕ) : ℝ) + 1 - k) =
        ∑ k ∈ range (m + 1), Λ k * ((m : ℝ) + 1 - k) + ∑ k ∈ range (m + 1), Λ k := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro k _; push_cast; ring
    rw [this]; push_cast; ring

/-- `A₂(m) = Σ_{k ≤ m} Λ(k)((m - k)²/2 + (m - k)/2)` for `a = ψ`. -/
lemma A2_psi (m : ℕ) : A2 (fun i => ψ (i : ℝ)) m =
    ∑ k ∈ range (m + 1), Λ k * (((m : ℝ) - k) ^ 2 / 2 + ((m : ℝ) - k) / 2) := by
  induction m with
  | zero => simp [A2]
  | succ m ih =>
    rw [A2, sum_range_succ, ← A2, ih, A1_psi,
      sum_range_succ (fun k => Λ k * ((((m + 1 : ℕ) : ℝ) - k) ^ 2 / 2 + (((m + 1 : ℕ) : ℝ) - k) / 2))
        (m + 1)]
    rw [← sum_add_distrib]
    push_cast
    rw [show ((m : ℝ) + 1 - (m + 1)) = 0 by ring]
    simp only [zero_pow two_ne_zero, zero_div, add_zero, mul_zero]
    apply sum_congr rfl; intro k _; ring

/-- `A₂(m) = (m³ - m)/6` for `a(i) = i`. -/
lemma A2_id (m : ℕ) : A2 (fun i => (i : ℝ)) m = ((m : ℝ) ^ 3 - m) / 6 := by
  have h1 : ∀ j : ℕ, A1 (fun i => (i : ℝ)) j = (j : ℝ) * (j + 1) / 2 := by
    intro j
    induction j with
    | zero => simp [A1]
    | succ j ih => rw [A1, sum_range_succ, ← A1, ih]; push_cast; ring
  induction m with
  | zero => simp [A2]
  | succ m ih => rw [A2, sum_range_succ, ← A2, ih, h1]; push_cast; ring

/-- `Σ_{n} (H - |n - N|) n = H² N`. -/
lemma tri_id (N H : ℕ) (hH : H ≤ N) :
    ∑ n ∈ Ico (N - H) (N + H + 1), ((H : ℝ) - |(n : ℝ) - N|) * n = (H : ℝ) ^ 2 * N := by
  rw [tri_identity (fun i => (i : ℝ)) N H hH, A2_id, A2_id, A2_id, Nat.cast_sub hH]
  push_cast; ring

/-- `R(u) = Σ_{k ≤ M} Λ(k) max(0, u - k)`, which is `ψ₁(u)` for `u ≤ M`. -/
def Rg (M : ℕ) (u : ℝ) : ℝ := ∑ k ∈ range (M + 1), Λ k * max 0 (u - k)

/-- `Q(u) = Σ_{k ≤ M} Λ(k) max(0, u - k)²/2`, an antiderivative of `R`. -/
def Qg (M : ℕ) (u : ℝ) : ℝ := ∑ k ∈ range (M + 1), Λ k * (max 0 (u - k) ^ 2 / 2)

lemma A2_psi_eq {m M : ℕ} (hm : m ≤ M) :
    A2 (fun i => ψ (i : ℝ)) m = Qg M m + Rg M m / 2 := by
  rw [A2_psi, Qg, Rg, sum_div, ← sum_add_distrib]
  apply sum_subset_zero_on_sdiff (range_subset_range.mpr (by omega))
  · intro k hk
    rw [mem_sdiff, mem_range, mem_range] at hk
    have : (m : ℝ) - k ≤ 0 := by
      have : (m : ℝ) + 1 ≤ k := by exact_mod_cast not_lt.mp hk.2
      linarith
    rw [max_eq_left this]; ring
  · intro k hk
    rw [mem_range] at hk
    have : 0 ≤ (m : ℝ) - k := by
      have : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp hk
      linarith
    rw [max_eq_right this]; ring

lemma hasDerivAt_sqmax (k u : ℝ) :
    HasDerivAt (fun u : ℝ => max 0 (u - k) ^ 2 / 2) (max 0 (u - k)) u := by
  have hne : ∀ y ≠ k, HasDerivAt (fun u : ℝ => max 0 (u - k) ^ 2 / 2) (max 0 (y - k)) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with h | h
    · have hev : (fun u : ℝ => max 0 (u - k) ^ 2 / 2) =ᶠ[nhds y] fun _ => 0 := by
        filter_upwards [eventually_lt_nhds h] with z hz
        rw [max_eq_left (by linarith)]; ring
      rw [max_eq_left (by linarith)]
      exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    · have hev : (fun u : ℝ => max 0 (u - k) ^ 2 / 2) =ᶠ[nhds y] fun u => (u - k) ^ 2 / 2 := by
        filter_upwards [eventually_gt_nhds h] with z hz
        rw [max_eq_right (by linarith)]
      rw [max_eq_right (by linarith)]
      have : HasDerivAt (fun u : ℝ => (u - k) ^ 2 / 2) ((2 : ℕ) * (y - k) ^ (2 - 1) * 1 / 2) y :=
        (((hasDerivAt_id y).sub_const k).pow 2).div_const 2
      convert this.congr_of_eventuallyEq hev using 1
      push_cast; ring
  by_cases hu : u = k
  · rw [hu]
    exact hasDerivAt_of_hasDerivAt_of_ne hne
      (by fun_prop : Continuous fun u : ℝ => max 0 (u - k) ^ 2 / 2).continuousAt
      (by fun_prop : Continuous fun u : ℝ => max 0 (u - k)).continuousAt
  · exact hne u hu

lemma continuous_Rg (M : ℕ) : Continuous (Rg M) := by
  unfold Rg; fun_prop

lemma integral_Rg (M : ℕ) (a b : ℝ) : ∫ u in a..b, Rg M u = Qg M b - Qg M a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    unfold Qg Rg
    exact HasDerivAt.fun_sum (fun k _ => (hasDerivAt_sqmax k u).const_mul (Λ k))
  · exact (continuous_Rg M).intervalIntegrable a b

/-- `R(u) = u Σ Λ(n) w₁(n/u) = ψ₁(u)` for `0 < u ≤ M`. -/
lemma Rg_eq {M : ℕ} {u : ℝ} (hu0 : 0 < u) (huM : u ≤ M) :
    ((Rg M u : ℝ) : ℂ) = (u : ℂ) * ∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / u) := by
  rw [tsum_w1 hu0, ← ofReal_mul, mul_sum]
  congr 1
  have hfl : ⌊u⌋₊ ≤ M := Nat.floor_le_of_le huM
  rw [Rg]
  symm
  apply sum_subset_zero_on_sdiff (range_subset_range.mpr (by omega))
  · intro k hk
    rw [mem_sdiff, mem_range, mem_range] at hk
    have : u ≤ k := by
      have h1 := Nat.lt_floor_add_one u
      have h2 : ((⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast not_lt.mp hk.2
      push_cast at h2; linarith
    rw [max_eq_left (by linarith)]; ring
  · intro k hk
    rw [mem_range] at hk
    have : (k : ℝ) ≤ u := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hk) (Nat.floor_le hu0.le)
    rw [max_eq_right (by linarith)]
    field_simp

open PNTPort.ExplicitPsi1 in
/-- The zero term of `ψ₁`: `m(ρ) u^{ρ+1}/(ρ(ρ + 1))`. -/
def wterm (u : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ : ℂ) * ((u : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))

open PNTPort.ExplicitPsi1 in
/-- `W(u) = Σ_ρ m(ρ) u^{ρ+1}/(ρ(ρ + 1))`. -/
def Wf (u : ℝ) : ℂ := ∑' ρ : Zall, wterm u ρ

open PNTPort.ExplicitPsi1 in
lemma Zall_re_pos {ρ : ℂ} (h : ρ ∈ Zall) : 0 < ρ.re := by
  rw [Zall_eq] at h; exact h.2.1

open PNTPort.ExplicitPsi1 in
lemma norm_wterm_le {B u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) {ρ : ℂ} (h : ρ ∈ Zall) :
    ‖wterm u ρ‖ ≤ (B + 1) ^ 2 * hw ρ := by
  have hre0 := Zall_re_pos h
  have hre1 := Zall_re_lt h
  have hpow : ‖(u : ℂ) ^ (ρ + 1)‖ ≤ (B + 1) ^ 2 := by
    rcases eq_or_lt_of_le hu0 with h0 | hpos
    · rw [← h0, ofReal_zero, zero_cpow (by intro e; have := congr_arg re e; simp at this; linarith)]
      simp only [norm_zero]; positivity
    · rw [norm_cpow_eq_rpow_re_of_pos hpos]
      have hα : (ρ + 1).re = ρ.re + 1 := by simp
      rw [hα]
      calc u ^ (ρ.re + 1) ≤ (B + 1) ^ (ρ.re + 1) :=
            Real.rpow_le_rpow hu0 (by linarith) (by linarith)
        _ ≤ (B + 1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (B + 1) ^ 2 := by norm_cast
  unfold wterm hw
  rw [norm_mul, norm_div, Complex.norm_natCast]
  calc (analyticOrderNatAt riemannZeta ρ : ℝ) * (‖(u : ℂ) ^ (ρ + 1)‖ / ‖ρ * (ρ + 1)‖)
      = ‖(u : ℂ) ^ (ρ + 1)‖ * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖) := by ring
    _ ≤ (B + 1) ^ 2 * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)

open PNTPort.ExplicitPsi1 in
lemma continuous_wterm {ρ : ℂ} (h : ρ ∈ Zall) : Continuous fun u : ℝ => wterm u ρ := by
  unfold wterm
  have := continuous_ofReal_cpow_const (y := ρ + 1) (by simp; linarith [Zall_re_pos h])
  exact (this.div_const _).const_mul _

open PNTPort.ExplicitPsi1 in
lemma Zall_countable : Zall.Countable := by
  refine (Set.countable_iUnion fun n : ℕ => (zeros_rect_finite 2 n).countable).mono ?_
  intro ρ hρ
  rw [Set.mem_iUnion]
  refine ⟨⌈|ρ.im|⌉₊, ?_, hρ.1⟩
  rw [mem_rect (by norm_num) (by positivity)]
  have hc := Nat.le_ceil |ρ.im|
  exact ⟨⟨hρ.2, by linarith [Zall_re_lt hρ]⟩, abs_le.mp hc⟩

instance : Countable PNTPort.ExplicitPsi1.Zall := Zall_countable.to_subtype

open PNTPort.ExplicitPsi1 in
lemma hasSum_integral_W {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    HasSum (fun ρ : Zall => ∫ u in a..b, wterm u ρ) (∫ u in a..b, Wf u) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun (ρ : Zall) _ => (b + 1) ^ 2 * hw ρ)
  · intro ρ; exact (continuous_wterm ρ.2).aestronglyMeasurable
  · intro ρ
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact norm_wterm_le (by linarith [ht.1]) ht.2 ρ.2
  · exact Filter.Eventually.of_forall fun t _ => summable_hw.mul_left _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact (Summable.of_norm_bounded (summable_hw.mul_left ((b + 1) ^ 2))
      (fun ρ => norm_wterm_le (by linarith [ht.1]) ht.2 ρ.2)).hasSum

open PNTPort.ExplicitPsi1 in
lemma integral_wterm {a b : ℝ} {ρ : ℂ} (h : ρ ∈ Zall) :
    ∫ u in a..b, wterm u ρ = (analyticOrderNatAt riemannZeta ρ : ℂ) *
      (((b : ℂ) ^ (ρ + 2) - (a : ℂ) ^ (ρ + 2)) / (ρ * (ρ + 1) * (ρ + 2))) := by
  unfold wterm
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    integral_cpow (Or.inl (by simp; linarith [Zall_re_pos h]))]
  rw [show ρ + 1 + 1 = ρ + 2 by ring]
  field_simp

open PNTPort.ExplicitPsi1 in
lemma uZ_eq {u : ℝ} (hu : 0 < u) : (u : ℂ) * ∑' ρ : Zall, zterm u ρ = Wf u := by
  rw [Wf, ← tsum_mul_left]
  apply tsum_congr; intro ρ
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  simp only [zterm, wterm]
  rw [cpow_add _ _ hu0, cpow_one]; ring

open PNTPort.ExplicitPsi1 in
/-- `ψ₁(u) = u²/2 - u ζ'(0)/ζ(0) - W(u) + E(u)` with `‖E(u)‖ ≤ K(u + 1)`. -/
lemma psi1_formula : ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℕ) (u : ℝ), 0 < u → u ≤ M →
    ‖((Rg M u : ℝ) : ℂ) - ((u : ℂ) ^ 2 / 2 - u * (deriv riemannZeta 0 / riemannZeta 0) - Wf u)‖
      ≤ K * (u + 1) := by
  obtain ⟨K, hK⟩ := explicit_formula_psi1_bound
  refine ⟨|K|, abs_nonneg K, fun M u hu huM => ?_⟩
  have hb := hK u hu
  have e : ((Rg M u : ℝ) : ℂ) - ((u : ℂ) ^ 2 / 2 - u * (deriv riemannZeta 0 / riemannZeta 0) - Wf u) =
      (u : ℂ) * (∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / u) -
        (u / 2 - deriv riemannZeta 0 / riemannZeta 0 - ∑' ρ : Zall, zterm u ρ)) := by
    rw [Rg_eq hu huM, ← uZ_eq hu]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hr0 : 0 ≤ u ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hu.le _
  have hkey : u * u ^ (-1 / 2 : ℝ) ≤ u + 1 := by
    rcases le_total 1 u with h1 | h1
    · have : u ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
      nlinarith
    · have e2 : u * u ^ (-1 / 2 : ℝ) = u ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hu.le (by norm_num)]; norm_num
      rw [e2]
      have : u ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hu.le h1 (by norm_num)
      linarith
  calc u * ‖_‖ ≤ u * (K * u ^ (-1 / 2 : ℝ)) := by gcongr
    _ ≤ u * (|K| * u ^ (-1 / 2 : ℝ)) := by gcongr; exact le_abs_self K
    _ = |K| * (u * u ^ (-1 / 2 : ℝ)) := by ring
    _ ≤ |K| * (u + 1) := by gcongr

open PNTPort.ExplicitPsi1 in
lemma Wf_continuousOn {B : ℝ} : ContinuousOn Wf (Set.Icc 0 B) := by
  apply continuousOn_tsum (fun ρ => (continuous_wterm ρ.2).continuousOn)
    (summable_hw.mul_left ((B + 1) ^ 2))
  intro ρ u hu
  exact norm_wterm_le hu.1 hu.2 ρ.2

lemma Wf_intervalIntegrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable Wf MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact (Wf_continuousOn (B := b)).mono (Set.Icc_subset_Icc ha le_rfl)

open PNTPort.ExplicitPsi1 in
/-- The second difference of `∫ W` is the zero sum `S` of the paper. -/
lemma I_Wf {N H : ℕ} (hH : H ≤ N) :
    (∫ u in (N : ℝ)..((N : ℝ) + H), Wf u) - ∫ u in ((N : ℝ) - H)..(N : ℝ), Wf u = ZH N H := by
  have hHN : (H : ℝ) ≤ N := by exact_mod_cast hH
  have h1 := hasSum_integral_W (a := (N : ℝ)) (b := (N : ℝ) + H) (by positivity) (by linarith)
  have h2 := hasSum_integral_W (a := (N : ℝ) - H) (b := (N : ℝ)) (by linarith) (by linarith)
  rw [← h1.tsum_eq, ← h2.tsum_eq, ← h1.summable.tsum_sub h2.summable, ZH, zeroSum]
  have e : (∑' ρ : Zall, ((∫ u in (N : ℝ)..((N : ℝ) + H), wterm u ρ) -
      ∫ u in ((N : ℝ) - H)..(N : ℝ), wterm u ρ)) =
      ∑' ρ : NontrivialZero, ((∫ u in (N : ℝ)..((N : ℝ) + H), wterm u ρ.1) -
        ∫ u in ((N : ℝ) - H)..(N : ℝ), wterm u ρ.1) := by
    rw [Zall_eq]; rfl
  rw [e]
  apply tsum_congr; intro ρ
  have hρ : ρ.1 ∈ Zall := by rw [Zall_eq]; exact ρ.2
  rw [integral_wterm hρ, integral_wterm hρ]
  push_cast
  ring

lemma Rg_lip (M : ℕ) (x y : ℝ) : |Rg M x - Rg M y| ≤ |x - y| * ψ (M : ℝ) := by
  rw [Rg, Rg, ← sum_sub_distrib, psi_nat, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  have hl := abs_max_sub_max_le_abs (x - k) (y - k) 0
  rw [show x - k - (y - k) = x - y by ring, max_comm (x - k), max_comm (y - k)] at hl
  calc |Λ k * max 0 (x - k) - Λ k * max 0 (y - k)|
      = Λ k * |max 0 (x - k) - max 0 (y - k)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ Λ k * |x - y| := mul_le_mul_of_nonneg_left hl ArithmeticFunction.vonMangoldt_nonneg
    _ = |x - y| * Λ k := mul_comm _ _

/-- **Languasco-Zaccagnini Lemma 8**, unconditional, now proved. -/
theorem lz_lemma8_proved : Lemma8 := by
  obtain ⟨K₀, hK₀, hF⟩ := psi1_formula
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hd0
  refine ⟨1, ‖d0‖ + 6 * K₀ + 4 * (Real.log 4 + 4), fun N H hN hH2 hHN => ?_⟩
  set M := N + H with hMdef
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hH2r : (2 : ℝ) ≤ H := by exact_mod_cast hH2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) - H with ha
  set c : ℝ := (N : ℝ) + H with hc
  have hMc : ((M : ℕ) : ℝ) = c := by rw [hMdef, hc]; push_cast; ring
  -- the discrete side
  have hT : ∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ (n : ℝ) - n) =
      (Qg M c - 2 * Qg M N + Qg M a) + (Rg M c - 2 * Rg M N + Rg M a) / 2 - (H : ℝ) ^ 2 * N := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    have e : ∑ n ∈ Ico (N - H) (N + H + 1), ((H : ℝ) - |(n : ℝ) - N|) * (ψ (n : ℝ) - n) =
        ∑ n ∈ Ico (N - H) (N + H + 1), ((H : ℝ) - |(n : ℝ) - N|) * (fun i : ℕ => ψ (i : ℝ)) n -
          ∑ n ∈ Ico (N - H) (N + H + 1), ((H : ℝ) - |(n : ℝ) - N|) * n := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro n _; ring
    rw [e, tri_identity _ N H hHN, tri_id N H hHN, A2_psi_eq (le_refl M),
      A2_psi_eq (show N ≤ M by omega), A2_psi_eq (show N - H ≤ M by omega)]
    have e1 : ((N + H : ℕ) : ℝ) = c := by push_cast; ring
    have e2 : ((N - H : ℕ) : ℝ) = a := by rw [Nat.cast_sub hHN]
    rw [show M = N + H from rfl, e1, e2]
    ring
  have hQ : Qg M c - 2 * Qg M N + Qg M a =
      (∫ u in (N : ℝ)..c, Rg M u) - ∫ u in a..(N : ℝ), Rg M u := by
    rw [integral_Rg, integral_Rg]; ring
  -- the analytic side
  set main : ℝ → ℂ := fun u => ((u ^ 2 / 2 : ℝ) : ℂ) - ((u : ℝ) : ℂ) * d0 - Wf u with hmain
  set E1 : ℝ → ℂ := fun u => ((Rg M u : ℝ) : ℂ) - main u with hE1
  have hRint : ∀ α β : ℝ, IntervalIntegrable (fun u => ((Rg M u : ℝ) : ℂ)) MeasureTheory.volume α β :=
    fun α β => (continuous_ofReal.comp (continuous_Rg M)).intervalIntegrable α β
  have hmint : ∀ α β : ℝ, 0 ≤ α → α ≤ β →
      IntervalIntegrable main MeasureTheory.volume α β := by
    intro α β hα hαβ
    refine IntervalIntegrable.sub (IntervalIntegrable.sub ?_ ?_) (Wf_intervalIntegrable hα hαβ)
    · exact (by fun_prop : Continuous fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ)).intervalIntegrable α β
    · exact (by fun_prop : Continuous fun u : ℝ => ((u : ℝ) : ℂ) * d0).intervalIntegrable α β
  have hint_main : ∀ α β : ℝ, 0 ≤ α → α ≤ β → ∫ u in α..β, main u =
      (((β ^ 3 - α ^ 3) / 6 : ℝ) : ℂ) - (((β ^ 2 - α ^ 2) / 2 : ℝ) : ℂ) * d0 -
        ∫ u in α..β, Wf u := by
    intro α β hα hαβ
    rw [hmain, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal]
    · congr 2
      · congr 1
        rw [intervalIntegral.integral_div, integral_pow]; ring
      · congr 1; rw [integral_id]
    · exact (by fun_prop : Continuous fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ)).intervalIntegrable α β
    · exact (by fun_prop : Continuous fun u : ℝ => ((u : ℝ) : ℂ) * d0).intervalIntegrable α β
    · exact IntervalIntegrable.sub
        ((by fun_prop : Continuous fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ)).intervalIntegrable α β)
        ((by fun_prop : Continuous fun u : ℝ => ((u : ℝ) : ℂ) * d0).intervalIntegrable α β)
    · exact Wf_intervalIntegrable hα hαβ
  have hsplitR : ∀ α β : ℝ, 0 ≤ α → α ≤ β →
      (((∫ u in α..β, Rg M u) : ℝ) : ℂ) = (∫ u in α..β, main u) + ∫ u in α..β, E1 u := by
    intro α β hα hαβ
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_add (hmint α β hα hαβ)
      ((hRint α β).sub (hmint α β hα hαβ))]
    congr 1; funext u; simp [hE1]
  have hE1b : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ c → ‖∫ u in α..β, E1 u‖ ≤ K₀ * (c + 1) * (β - α) := by
    intro α β hα hαβ hβc
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := α) (b := β)
      (C := K₀ * (c + 1)) (f := E1) (fun u hu => by
        rw [Set.uIoc_of_le hαβ] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        have huc : u ≤ c := le_trans hu.2 hβc
        have e : E1 u = ((Rg M u : ℝ) : ℂ) - ((u : ℂ) ^ 2 / 2 - u * d0 - Wf u) := by
          simp only [hE1, hmain]; push_cast; ring
        rw [e]
        refine (hF M u hu0 (by rw [hMc]; exact huc)).trans ?_
        gcongr)
    rwa [abs_of_nonneg (by linarith)] at this
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  -- assemble
  have hId : (((∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ (n : ℝ) - n) : ℝ)) : ℂ)
      + ZH N H = -(((H : ℝ) ^ 2 : ℝ) : ℂ) * d0 + ((∫ u in (N : ℝ)..c, E1 u) -
        ∫ u in a..(N : ℝ), E1 u) + (((Rg M c - 2 * Rg M N + Rg M a) / 2 : ℝ) : ℂ) := by
    rw [hT, hQ]
    push_cast
    rw [hsplitR _ _ (by positivity) (by linarith), hsplitR _ _ ha0 (by linarith),
      hint_main _ _ (by positivity) (by linarith), hint_main _ _ ha0 (by linarith),
      ← I_Wf hHN]
    rw [hc, ha]
    push_cast
    ring
  rw [hId]
  have b1 : ‖-(((H : ℝ) ^ 2 : ℝ) : ℂ) * d0‖ ≤ ‖d0‖ * H * N := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (H : ℝ) ^ 2 ≤ H * N := by nlinarith
    nlinarith [norm_nonneg d0]
  have b2 : ‖(∫ u in (N : ℝ)..c, E1 u) - ∫ u in a..(N : ℝ), E1 u‖ ≤ 6 * K₀ * H * N := by
    have i1 := hE1b N c (by positivity) (by linarith) le_rfl
    have i2 := hE1b a N ha0 (by linarith) (by linarith)
    have hc1 : c + 1 ≤ 3 * N := by linarith
    have hK : K₀ * (c + 1) ≤ K₀ * (3 * N) := by gcongr
    calc _ ≤ ‖∫ u in (N : ℝ)..c, E1 u‖ + ‖∫ u in a..(N : ℝ), E1 u‖ := norm_sub_le _ _
      _ ≤ K₀ * (c + 1) * (c - N) + K₀ * (c + 1) * (N - a) := add_le_add i1 i2
      _ = K₀ * (c + 1) * (2 * H) := by rw [hc, ha]; ring
      _ ≤ K₀ * (3 * N) * (2 * H) := by gcongr
      _ = 6 * K₀ * H * N := by ring
  have b3 : ‖((((Rg M c - 2 * Rg M N + Rg M a) / 2 : ℝ)) : ℂ)‖ ≤ 4 * (Real.log 4 + 4) * H * N := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have l1 := Rg_lip M c N
    have l2 := Rg_lip M N a
    have hψ : ψ (M : ℝ) ≤ (Real.log 4 + 4) * (2 * N) := by
      refine (Chebyshev.psi_le_const_mul_self (by positivity)).trans ?_
      rw [hMc]; gcongr; linarith
    have hψ0 : 0 ≤ ψ (M : ℝ) := Chebyshev.psi_nonneg _
    rw [show c - N = H by rw [hc]; ring, abs_of_nonneg (show (0 : ℝ) ≤ H by positivity)] at l1
    rw [show (N : ℝ) - a = H by rw [ha]; ring, abs_of_nonneg (show (0 : ℝ) ≤ H by positivity)] at l2
    have : |Rg M c - 2 * Rg M N + Rg M a| ≤ |Rg M c - Rg M N| + |Rg M N - Rg M a| := by
      rw [show Rg M c - 2 * Rg M N + Rg M a = (Rg M c - Rg M N) - (Rg M N - Rg M a) by ring]
      exact abs_sub _ _
    rw [abs_div, abs_two]
    have hlog : 0 ≤ Real.log 4 + 4 := by positivity
    have : (H : ℝ) * ψ (M : ℝ) ≤ H * ((Real.log 4 + 4) * (2 * N)) := by gcongr
    nlinarith
  calc _ ≤ ‖-(((H : ℝ) ^ 2 : ℝ) : ℂ) * d0‖ +
        ‖(∫ u in (N : ℝ)..c, E1 u) - ∫ u in a..(N : ℝ), E1 u‖ +
        ‖((((Rg M c - 2 * Rg M N + Rg M a) / 2 : ℝ)) : ℂ)‖ := norm_add₃_le
    _ ≤ ‖d0‖ * H * N + 6 * K₀ * H * N + 4 * (Real.log 4 + 4) * H * N := by linarith
    _ = (‖d0‖ + 6 * K₀ + 4 * (Real.log 4 + 4)) * H * N := by ring

end LeanLab.LZCesaroShort

