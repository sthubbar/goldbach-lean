module

public import LeanLab.LZCesaroShort.Sec5Proof

/-!
# von Koch's bound under RH with `log² x`

Lab proof, unit U-5324, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
von Koch 1901, CONDITIONAL ON `RiemannHypothesis`, Mathlib's definition, and nothing else:
`|ψ(x) - x| ≤ C √x log² x` for `x ≥ 3`. The lab's earlier `ZetaZeros.vonKoch_RH` had `log³ x`.
Route: `ψ(x)` is squeezed between difference quotients of `ψ₁` at step `h = √x`; `ψ₁` is the lab's
explicit formula; under RH each zero term of the difference is `≪ min(h √x/|ρ|, x^{3/2}/|ρ|²)`;
the zero sums split at `|ρ| = x`. Binary Goldbach is open.
-/

@[expose] public section


open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.PNTPort.ExplicitPsi1

/-- `F(t) = (log t + 2)/(t - 1)`, a telescoping majorant. -/
def Ftel (t : ℝ) : ℝ := (Real.log t + 2) / (t - 1)

lemma Ftel_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ Ftel t := by
  unfold Ftel
  have : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have : 0 < t - 1 := by linarith
  positivity

/-- `log(p + 1)/p² ≤ F(p) - F(p + 1)` for `p ≥ 2`. -/
lemma tel_real {p : ℝ} (hp2 : 2 ≤ p) :
    Real.log (p + 1) / p ^ 2 ≤ Ftel p - Ftel (p + 1) := by
  set L := Real.log p with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlogn : Real.log (p + 1) ≤ L + 1 / p := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (p + 1) / p by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have : (p + 1) / p - 1 = 1 / p := by field_simp; ring
    linarith
  unfold Ftel
  rw [show p + 1 - 1 = p by ring]
  have hp1 : 0 < p - 1 := by linarith
  have hlog1 : 0 ≤ Real.log (p + 1) := Real.log_nonneg (by linarith)
  have key : (L + 1) / p ^ 2 ≤ (L + 2) / (p - 1) - (Real.log (p + 1) + 2) / p := by
    rw [div_sub_div _ _ hp1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have h1p : p * (1 / p) = 1 := by field_simp
    have hq : 0 ≤ 1 / p := by positivity
    have h2 : (p - 1) * Real.log (p + 1) ≤ (p - 1) * (L + 1 / p) :=
      mul_le_mul_of_nonneg_left hlogn hp1.le
    have hD : L + 1 ≤ (L + 2) * p - (p - 1) * (Real.log (p + 1) + 2) := by nlinarith
    have h3 : (L + 1) * p ^ 2 ≤ ((L + 2) * p - (p - 1) * (Real.log (p + 1) + 2)) * p ^ 2 :=
      mul_le_mul_of_nonneg_right hD (sq_nonneg p)
    nlinarith
  have : Real.log (p + 1) / p ^ 2 ≤ (L + 1) / p ^ 2 := by
    gcongr
    have : 1 / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  linarith

/-- `Σ_{n=a}^{M} log n/(n - 1)² ≤ F(a - 1)` for `a ≥ 3`. -/
lemma sum_log_div_sq_le {a : ℕ} (ha : 3 ≤ a) (M : ℕ) :
    ∑ n ∈ Icc a M, Real.log n / ((n : ℝ) - 1) ^ 2 ≤ Ftel ((a : ℝ) - 1) := by
  have ha1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have h : ∀ k : ℕ, ∑ n ∈ Icc a (a - 1 + k), Real.log n / ((n : ℝ) - 1) ^ 2 ≤
      Ftel ((a : ℝ) - 1) - Ftel (((a - 1 + k : ℕ) : ℝ)) := by
    intro k
    induction k with
    | zero =>
      have : Icc a (a - 1 + 0) = ∅ := by ext x; simp; omega
      rw [this, sum_empty, add_zero, ha1]; simp
    | succ k ih =>
      rw [show a - 1 + (k + 1) = (a - 1 + k) + 1 by ring, sum_Icc_succ_top (by omega)]
      have hp2 : (2 : ℝ) ≤ ((a - 1 + k : ℕ) : ℝ) := by
        have : 2 ≤ a - 1 + k := by omega
        exact_mod_cast this
      have := tel_real hp2
      have e : (((a - 1 + k + 1 : ℕ)) : ℝ) = ((a - 1 + k : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e, show ((a - 1 + k : ℕ) : ℝ) + 1 - 1 = ((a - 1 + k : ℕ) : ℝ) by ring]
      linarith
  rcases Nat.lt_or_ge M a with hM | hM
  · have : Icc a M = ∅ := by ext x; simp; omega
    rw [this, sum_empty]
    exact Ftel_nonneg (by have h3 : (3 : ℝ) ≤ a := (by exact_mod_cast ha); linarith)
  · have := h (M - (a - 1))
    rw [show a - 1 + (M - (a - 1)) = M by omega] at this
    have h0 : 0 ≤ Ftel (M : ℝ) := Ftel_nonneg (by
      have : (3 : ℝ) ≤ M := by exact_mod_cast (le_trans ha hM)
      linarith)
    linarith

/-- **Tail count**: zeros in the strip with `|ρ| > T ≥ 6` have `Σ m(ρ)/|ρ|² ≤ C (log T + 1)/T`. -/
theorem tail_count : ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ T : ℝ, 6 ≤ T → ∀ u : Finset ℂ,
    (∀ ρ ∈ u, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ‖ρ‖) →
    ∑ ρ ∈ u, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 ≤ C2 * (Real.log T + 1) / T := by
  obtain ⟨C, hC, hfib⟩ := fiber_count
  refine ⟨16 * C, by positivity, fun T hT u hu => ?_⟩
  have him : ∀ ρ ∈ u, T - 1 < |ρ.im| := by
    intro ρ hρ
    obtain ⟨_, h0, h1, hT'⟩ := hu ρ hρ
    have := norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos h0] at this
    linarith
  set a := ⌈T - 1⌉₊ with ha
  set M := u.sup (fun ρ => ⌈|ρ.im|⌉₊) with hM
  have hTa1 : T - 1 ≤ a := Nat.le_ceil _
  have hTa2 : (a : ℝ) < T - 1 + 1 := Nat.ceil_lt_add_one (by linarith)
  have ha5 : 5 ≤ a := by
    have : (5 : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hmaps : ∀ ρ ∈ u, ⌈|ρ.im|⌉₊ ∈ Icc a M := by
    intro ρ hρ
    rw [mem_Icc]
    exact ⟨Nat.ceil_mono (him ρ hρ).le, Finset.le_sup (f := fun ρ => ⌈|ρ.im|⌉₊) hρ⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hB : ∀ n ∈ Icc a M, ∑ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n),
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 ≤ 4 * C * (Real.log n / ((n : ℝ) - 1) ^ 2) := by
    intro n hn
    rw [mem_Icc] at hn
    have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast (le_trans ha5 hn.1)
    set v := u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n)
    have hv : ∀ ρ ∈ v, riemannZeta ρ = 0 ∧ (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n := by
      intro ρ hρ
      simp only [v, Finset.mem_filter] at hρ
      have hc := (Nat.ceil_eq_iff (by omega)).mp hρ.2
      rw [Nat.cast_sub (by omega)] at hc
      push_cast at hc
      exact ⟨(hu ρ hρ.1).1, hc⟩
    have hcount := hfib n (by omega) v hv
    have hd : 0 < ((n : ℝ) - 1) ^ 2 := by nlinarith
    calc ∑ ρ ∈ v, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2
        ≤ ∑ ρ ∈ v, (analyticOrderNatAt riemannZeta ρ : ℝ) / ((n : ℝ) - 1) ^ 2 := by
          apply sum_le_sum; intro ρ hρ
          obtain ⟨_, hlo, _⟩ := hv ρ hρ
          apply div_le_div_of_nonneg_left (by positivity) hd
          exact pow_le_pow_left₀ (by linarith) (le_trans hlo.le (abs_im_le_norm ρ)) 2
      _ = (∑ ρ ∈ v, (analyticOrderNatAt riemannZeta ρ : ℝ)) / ((n : ℝ) - 1) ^ 2 := by
          rw [sum_div]
      _ ≤ 4 * C * Real.log n / ((n : ℝ) - 1) ^ 2 := div_le_div_of_nonneg_right hcount hd.le
      _ = 4 * C * (Real.log n / ((n : ℝ) - 1) ^ 2) := by ring
  have hsum := sum_le_sum hB
  rw [← mul_sum] at hsum
  have htel := sum_log_div_sq_le (by omega : 3 ≤ a) M
  have hF : Ftel ((a : ℝ) - 1) ≤ 4 * (Real.log T + 1) / T := by
    unfold Ftel
    have h1 : 0 < (a : ℝ) - 1 := by linarith
    have hlog : Real.log ((a : ℝ) - 1) ≤ Real.log T := Real.log_le_log h1 (by linarith)
    have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hd : T / 2 ≤ (a : ℝ) - 1 - 1 := by linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc _ ≤ 4 * C * ∑ n ∈ Icc a M, Real.log n / ((n : ℝ) - 1) ^ 2 := hsum
    _ ≤ 4 * C * (4 * (Real.log T + 1) / T) := by gcongr; exact htel.trans hF
    _ = 16 * C * (Real.log T + 1) / T := by ring

open LZCesaroShort in
/-- Under RH, `‖W(b) - W(a)‖ ≤ (b - a) √(2x) D₁ (log x + 1)² + (2x)^{3/2} D₂ (log x + 1)/x`
for `0 ≤ a ≤ b ≤ 2x`, `x ≥ 6`. -/
theorem dW_bound (hRH : RiemannHypothesis) : ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
    ∀ x : ℝ, 6 ≤ x → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 2 * x →
    ‖Wf b - Wf a‖ ≤ (b - a) * (2 * x) ^ (1 / 2 : ℝ) * (D1 * (Real.log x + 1) ^ 2) +
      (2 * x) ^ (3 / 2 : ℝ) * (2 * D2 * (Real.log x + 1) / x) := by
  obtain ⟨C1, hC1, hZ1⟩ := zero_sum_inv_bound
  obtain ⟨C2, hC2, hZ2⟩ := tail_count
  refine ⟨C1, C2, hC1, hC2, fun x hx a b ha hab hb => ?_⟩
  have hx0 : 0 < x := by linarith
  have hB1 : (1 : ℝ) ≤ 2 * x := by linarith
  set g : Zall → ℂ := fun ρ => wterm b ρ.1 - wterm a ρ.1 with hg
  have hsa : Summable (fun ρ : Zall => wterm a ρ.1) :=
    Summable.of_norm_bounded (summable_hw.mul_left ((2 * x + 1) ^ 2))
      (fun ρ => norm_wterm_le ha (by linarith) ρ.2)
  have hsb : Summable (fun ρ : Zall => wterm b ρ.1) :=
    Summable.of_norm_bounded (summable_hw.mul_left ((2 * x + 1) ^ 2))
      (fun ρ => norm_wterm_le (by linarith) hb ρ.2)
  have hW : Wf b - Wf a = ∑' ρ : Zall, g ρ := by
    rw [Wf, Wf, ← hsb.tsum_sub hsa]
  have hre : ∀ ρ : Zall, ρ.1.re = 1 / 2 := fun ρ => rh_re hRH ρ.2
  have hρ0 : ∀ ρ : Zall, ρ.1 ≠ 0 := fun ρ h => by have := hre ρ; rw [h] at this; simp at this
  have hρ1 : ∀ ρ : Zall, ρ.1 + 1 ≠ 0 := fun ρ h => by
    have := congr_arg re h; simp [hre ρ] at this; norm_num at this
  -- bound A per zero
  have hA : ∀ ρ : Zall, ‖g ρ‖ ≤ (b - a) * (2 * x) ^ (1 / 2 : ℝ) *
      ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := by
    intro ρ
    have e : g ρ = (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((∫ y in a..b, (y : ℂ) ^ ρ.1) / ρ.1) := by
      simp only [hg, wterm]
      rw [integral_cpow (Or.inl (by rw [hre ρ]; norm_num))]
      have := hρ0 ρ; have := hρ1 ρ
      field_simp
    rw [e, norm_mul, norm_div, Complex.norm_natCast]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := (2 * x) ^ (1 / 2 : ℝ)) (f := fun y : ℝ => (y : ℂ) ^ ρ.1) (fun y hy => by
        rw [Set.uIoc_of_le hab] at hy
        exact norm_cpow_le_of_le (by linarith [hy.1]) (by linarith [hy.2]) hB1
          (by rw [hre ρ]; norm_num) (le_of_eq (hre ρ)))
    rw [abs_of_nonneg (by linarith)] at hint
    have hn : 0 < ‖ρ.1‖ := norm_pos_iff.mpr (hρ0 ρ)
    calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (‖∫ y in a..b, (y : ℂ) ^ ρ.1‖ / ‖ρ.1‖)
        ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * ((2 * x) ^ (1 / 2 : ℝ) * (b - a) / ‖ρ.1‖) := by
          gcongr
      _ = _ := by ring
  -- bound B per zero
  have hBz : ∀ ρ : Zall, ‖g ρ‖ ≤ 2 * (2 * x) ^ (3 / 2 : ℝ) *
      ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := by
    intro ρ
    have hr : (ρ.1 + 1).re = 3 / 2 := by simp [hre ρ]; norm_num
    have b1 := norm_cpow_le_of_le (y := b) (by linarith) hb hB1 (r := ρ.1 + 1) (by rw [hr]; norm_num)
      (le_of_eq hr)
    have b2 := norm_cpow_le_of_le (y := a) ha (by linarith) hB1 (r := ρ.1 + 1) (by rw [hr]; norm_num)
      (le_of_eq hr)
    have hden : ‖ρ.1‖ ^ 2 ≤ ‖ρ.1 * (ρ.1 + 1)‖ := by
      rw [norm_mul, sq]
      have := norm_le_norm_add (ρ := ρ.1) (by rw [hre ρ]; norm_num) (k := 1) zero_le_one
      push_cast at this
      gcongr
    have hn : 0 < ‖ρ.1‖ ^ 2 := by have := norm_pos_iff.mpr (hρ0 ρ); positivity
    simp only [hg, wterm]
    rw [← mul_sub, ← sub_div, norm_mul, norm_div, Complex.norm_natCast]
    have hnum : ‖(b : ℂ) ^ (ρ.1 + 1) - (a : ℂ) ^ (ρ.1 + 1)‖ ≤ 2 * (2 * x) ^ (3 / 2 : ℝ) := by
      have := norm_sub_le ((b : ℂ) ^ (ρ.1 + 1)) ((a : ℂ) ^ (ρ.1 + 1)); linarith
    calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
          (‖(b : ℂ) ^ (ρ.1 + 1) - (a : ℂ) ^ (ρ.1 + 1)‖ / ‖ρ.1 * (ρ.1 + 1)‖)
        ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (2 * (2 * x) ^ (3 / 2 : ℝ) / ‖ρ.1‖ ^ 2) := by
          gcongr
      _ = _ := by ring
  have hgs : Summable (fun ρ : Zall => ‖g ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => ?_)
      ((summable_hw.mul_left ((2 * x + 1) ^ 2)).add (summable_hw.mul_left ((2 * x + 1) ^ 2)))
    exact (norm_sub_le _ _).trans (add_le_add (norm_wterm_le (by linarith) hb ρ.2)
      (norm_wterm_le ha (by linarith) ρ.2))
  rw [hW]
  refine (norm_tsum_le_tsum_norm hgs).trans (Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _) ?_)
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.1‖ ≤ x)]
  apply add_le_add
  · calc ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ x), ‖g ρ‖
        ≤ ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ x), (b - a) * (2 * x) ^ (1 / 2 : ℝ) *
            ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := sum_le_sum fun ρ _ => hA ρ
      _ = (b - a) * (2 * x) ^ (1 / 2 : ℝ) * ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.1‖ ≤ x)).map
            (Function.Embedding.subtype _), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
          rw [Finset.sum_map, Finset.mul_sum]; rfl
      _ ≤ (b - a) * (2 * x) ^ (1 / 2 : ℝ) * ∑ ρ ∈ (zeros_rect_finite 2 x).toFinset,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
          have : 0 ≤ (b - a) * (2 * x) ^ (1 / 2 : ℝ) := by
            have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) (1 / 2 : ℝ)
            nlinarith
          gcongr
          intro ρ hρ
          rw [Finset.mem_map] at hρ
          obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
          rw [Finset.mem_filter] at hρ'u
          rw [Set.Finite.mem_toFinset]
          have hre1 := Zall_re_lt hρ'Z
          have him : |ρ'.im| ≤ x := le_trans (abs_im_le_norm _) hρ'u.2
          refine ⟨(mem_rect (by norm_num) (by linarith)).mpr
            ⟨⟨hρ'Z.2, by simp; linarith⟩, abs_le.mp ?_⟩, hρ'Z.1⟩
          simpa using him
      _ ≤ (b - a) * (2 * x) ^ (1 / 2 : ℝ) * (C1 * (Real.log x + 1) ^ 2) := by
          have : 0 ≤ (b - a) * (2 * x) ^ (1 / 2 : ℝ) := by
            have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) (1 / 2 : ℝ)
            nlinarith
          gcongr; exact hZ1 x (by linarith)
  · calc ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ x), ‖g ρ‖
        ≤ ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ x), 2 * (2 * x) ^ (3 / 2 : ℝ) *
            ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := sum_le_sum fun ρ _ => hBz ρ
      _ = 2 * (2 * x) ^ (3 / 2 : ℝ) * ∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ x)).map
            (Function.Embedding.subtype _), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 := by
          rw [Finset.sum_map, Finset.mul_sum]; rfl
      _ ≤ 2 * (2 * x) ^ (3 / 2 : ℝ) * (C2 * (Real.log x + 1) / x) := by
          gcongr
          apply hZ2 x hx
          intro ρ hρ
          rw [Finset.mem_map] at hρ
          obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
          rw [Finset.mem_filter] at hρ'u
          have h := hρ'Z
          rw [Zall_eq] at h
          exact ⟨h.1, h.2.1, h.2.2, lt_of_not_ge hρ'u.2⟩
      _ = (2 * x) ^ (3 / 2 : ℝ) * (2 * C2 * (Real.log x + 1) / x) := by ring

open LZCesaroShort in
lemma Rg_sub_ge {M : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (haM : a ≤ M) :
    (b - a) * ψ a ≤ Rg M b - Rg M a := by
  rw [Chebyshev.psi_eq_sum_Icc, mul_sum, Rg, Rg, ← sum_sub_distrib]
  have hsub : Icc 0 ⌊a⌋₊ ⊆ range (M + 1) := by
    intro k hk; rw [mem_Icc] at hk; rw [mem_range]
    have := Nat.floor_le_of_le (n := M) haM; omega
  calc ∑ k ∈ Icc 0 ⌊a⌋₊, (b - a) * Λ k
      = ∑ k ∈ Icc 0 ⌊a⌋₊, (Λ k * max 0 (b - k) - Λ k * max 0 (a - k)) := by
        apply sum_congr rfl; intro k hk
        rw [mem_Icc] at hk
        have hk' : (k : ℝ) ≤ a := le_trans (by exact_mod_cast hk.2) (Nat.floor_le ha)
        rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro k _ _
        rw [← mul_sub]
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (sub_nonneg.mpr (max_le_max le_rfl (by linarith)))

open LZCesaroShort in
lemma Rg_sub_le {M : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbM : b ≤ M) :
    Rg M b - Rg M a ≤ (b - a) * ψ b := by
  rw [Chebyshev.psi_eq_sum_Icc, mul_sum, Rg, Rg, ← sum_sub_distrib]
  have hsub : Icc 0 ⌊b⌋₊ ⊆ range (M + 1) := by
    intro k hk; rw [mem_Icc] at hk; rw [mem_range]
    have := Nat.floor_le_of_le (n := M) hbM; omega
  rw [← sum_subset hsub]
  · apply sum_le_sum; intro k _
    rw [← mul_sub, mul_comm (b - a)]
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    have := abs_max_sub_max_le_abs (b - k) (a - k) 0
    rw [show b - k - (a - k) = b - a by ring, max_comm (b - k), max_comm (a - k)] at this
    exact (le_abs_self _).trans (this.trans (le_of_eq (abs_of_nonneg (by linarith))))
  · intro k _ hk
    rw [mem_Icc, not_and_or] at hk
    have hkb : b < k := by
      rcases hk with h | h
      · omega
      · exact (Nat.floor_lt (by linarith)).mp (not_le.mp h)
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

open LZCesaroShort in
/-- `ψ₁(y) = y²/2 - y ζ'(0)/ζ(0) - W(y) + E(y)` with `‖E(y)‖ ≤ K √y`, `0 < y ≤ M`. -/
lemma psi1_sqrt : ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℕ) (y : ℝ), 0 < y → y ≤ M →
    ‖((Rg M y : ℝ) : ℂ) - ((((y ^ 2 / 2 : ℝ)) : ℂ) - y * (deriv riemannZeta 0 / riemannZeta 0) - Wf y)‖
      ≤ K * y ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK⟩ := explicit_formula_psi1_bound
  refine ⟨|K|, abs_nonneg K, fun M y hy hyM => ?_⟩
  have e : ((Rg M y : ℝ) : ℂ) - ((((y ^ 2 / 2 : ℝ)) : ℂ) - y * (deriv riemannZeta 0 / riemannZeta 0) - Wf y) =
      (y : ℂ) * (∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / y) -
        (y / 2 - deriv riemannZeta 0 / riemannZeta 0 - ∑' ρ : Zall, zterm y ρ)) := by
    rw [Rg_eq hy hyM, ← uZ_eq hy]; push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have hyy : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hy.le (by norm_num)]; norm_num
  calc y * ‖_‖ ≤ y * (|K| * y ^ (-1 / 2 : ℝ)) := by
        gcongr; exact (hK y hy).trans (by gcongr; exact le_abs_self K)
    _ = |K| * (y * y ^ (-1 / 2 : ℝ)) := by ring
    _ = |K| * y ^ (1 / 2 : ℝ) := by rw [hyy]

lemma final_arith {h L d D1 D2 K : ℝ} (hh : 1 ≤ h) (hL : 1 ≤ L) (hd : 0 ≤ d) (hD1 : 0 ≤ D1)
    (hD2 : 0 ≤ D2) (hK : 0 ≤ K) :
    h / 2 + (d + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K) ≤
      (1 / 2 + d + 8 * D1 + 12 * D2 + 4 * K) * h * L ^ 2 := by
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hhL : 1 ≤ h * L ^ 2 := by nlinarith
  have e1 : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have e2 : L + 1 ≤ 2 * L ^ 2 := by nlinarith
  have t1 : h / 2 ≤ 1 / 2 * (h * L ^ 2) := by nlinarith
  have t2 : d ≤ d * (h * L ^ 2) := by nlinarith
  have t3 : 2 * h * D1 * (L + 1) ^ 2 ≤ 8 * D1 * (h * L ^ 2) := by
    have : 0 ≤ 2 * h * D1 := by positivity
    nlinarith
  have t4 : 6 * D2 * (L + 1) ≤ 12 * D2 * (h * L ^ 2) := by
    have : L + 1 ≤ 2 * (h * L ^ 2) := by nlinarith
    nlinarith
  have t5 : 4 * K ≤ 4 * K * (h * L ^ 2) := by nlinarith
  calc _ ≤ 1 / 2 * (h * L ^ 2) + (d * (h * L ^ 2) + 8 * D1 * (h * L ^ 2) +
        12 * D2 * (h * L ^ 2) + 4 * K * (h * L ^ 2)) := by linarith
    _ = _ := by ring

open LZCesaroShort in
/-- **von Koch under RH with `log²`**: `|ψ(x) - x| ≤ C √x log² x` for `x ≥ 6`, CONDITIONAL ON RH. -/
theorem vonKoch_RH_log2 (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 6 ≤ x → |ψ x - x| ≤ C * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := psi1_sqrt
  obtain ⟨D1, D2, hD1, hD2, hW⟩ := dW_bound hRH
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hd0
  refine ⟨1 / 2 + ‖d0‖ + 8 * D1 + 12 * D2 + 4 * K, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set h := Real.sqrt x with hh
  have hh0 : 0 < h := Real.sqrt_pos.mpr hx0
  have hhsq : h * h = x := Real.mul_self_sqrt hx0.le
  have hh1 : 2 ≤ h := by
    rw [hh, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hhx : h ≤ x := by nlinarith
  set M := ⌈2 * x⌉₊ with hM
  have h2xM : 2 * x ≤ M := Nat.le_ceil _
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  -- the general difference bound
  have G : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * x →
      |Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2| ≤ (b - a) * ‖d0‖ + ‖Wf b - Wf a‖ +
        K * (b ^ (1 / 2 : ℝ) + a ^ (1 / 2 : ℝ)) := by
    intro a b ha hab hb
    have ea := hK M a ha (by linarith)
    have eb := hK M b (by linarith) (by linarith)
    set Ea := ((Rg M a : ℝ) : ℂ) - ((((a ^ 2 / 2 : ℝ)) : ℂ) - a * d0 - Wf a)
    set Eb := ((Rg M b : ℝ) : ℂ) - ((((b ^ 2 / 2 : ℝ)) : ℂ) - b * d0 - Wf b)
    have e : (((Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2 : ℝ)) : ℂ) =
        -(((b - a : ℝ) : ℂ) * d0) - (Wf b - Wf a) + (Eb - Ea) := by
      simp only [Ea, Eb]; push_cast; ring
    have habs : |Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2| =
        ‖(((Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2 : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [habs, e]
    have n1 : ‖((b - a : ℝ) : ℂ) * d0‖ = (b - a) * ‖d0‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    calc ‖-(((b - a : ℝ) : ℂ) * d0) - (Wf b - Wf a) + (Eb - Ea)‖
        ≤ ‖-(((b - a : ℝ) : ℂ) * d0)‖ + ‖Wf b - Wf a‖ + (‖Eb‖ + ‖Ea‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _)) (norm_sub_le _ _))
      _ ≤ (b - a) * ‖d0‖ + ‖Wf b - Wf a‖ + K * (b ^ (1 / 2 : ℝ) + a ^ (1 / 2 : ℝ)) := by
          rw [norm_neg, n1]
          have : K * a ^ (1 / 2 : ℝ) + K * b ^ (1 / 2 : ℝ) =
              K * (b ^ (1 / 2 : ℝ) + a ^ (1 / 2 : ℝ)) := by ring
          linarith
  -- common size of the error
  have hs2 : (2 * x) ^ (1 / 2 : ℝ) ≤ 2 * h := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), hh]
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg x)
  have hs32 : (2 * x) ^ (3 / 2 : ℝ) ≤ 3 * x * h := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), hh]
    have : Real.sqrt 2 ≤ 3 / 2 := by
      rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsx := Real.sqrt_nonneg x
    have : 2 * x * (Real.sqrt 2 * Real.sqrt x) ≤ 2 * x * (3 / 2 * Real.sqrt x) := by gcongr
    linarith
  have hrp : ∀ y : ℝ, 0 ≤ y → y ≤ 2 * x → y ^ (1 / 2 : ℝ) ≤ 2 * h := fun y hy hyx =>
    (Real.rpow_le_rpow hy hyx (by norm_num)).trans hs2
  -- the zero sum difference over a step `h`
  have hWb : ∀ a b : ℝ, 0 ≤ a → b = a + h → b ≤ 2 * x →
      ‖Wf b - Wf a‖ ≤ h * (2 * h) * (D1 * (L + 1) ^ 2) + 3 * x * h * (2 * D2 * (L + 1) / x) := by
    intro a b ha hb hbx
    refine (hW x hx a b ha (by linarith) hbx).trans ?_
    rw [show b - a = h by linarith]
    have : 0 ≤ D1 * (L + 1) ^ 2 := by positivity
    have : 0 ≤ 2 * D2 * (L + 1) / x := by have : 0 ≤ L := by linarith
                                          positivity
    gcongr
  set Err := h * ‖d0‖ + (h * (2 * h) * (D1 * (L + 1) ^ 2) + 3 * x * h * (2 * D2 * (L + 1) / x)) +
    K * (2 * h + 2 * h) with hErr
  -- upper bound
  have hup : h * ψ x ≤ h * x + h * h / 2 + Err := by
    have g1 := Rg_sub_ge (M := M) (a := x) (b := x + h) hx0.le (by linarith) (by linarith)
    have g2 := G x (x + h) hx0 (by linarith) (by linarith)
    have g3 := hWb x (x + h) hx0.le rfl (by linarith)
    have r1 := hrp (x + h) (by linarith) (by linarith)
    have r2 := hrp x hx0.le (by linarith)
    rw [show x + h - x = h by ring] at g1 g2
    have habs := (abs_le.mp g2).2
    have : K * ((x + h) ^ (1 / 2 : ℝ) + x ^ (1 / 2 : ℝ)) ≤ K * (2 * h + 2 * h) := by gcongr
    have e : ((x + h) ^ 2 - x ^ 2) / 2 = h * x + h * h / 2 := by ring
    rw [e] at habs
    linarith
  -- lower bound
  have hlo : h * x - h * h / 2 - Err ≤ h * ψ x := by
    have g1 := Rg_sub_le (M := M) (a := x - h) (b := x) (by linarith) (by linarith) (by linarith)
    have g2 := G (x - h) x (by nlinarith) (by linarith) (by linarith)
    have g3 := hWb (x - h) x (by linarith) (by ring) (by linarith)
    have r1 := hrp x hx0.le (by linarith)
    have r2 := hrp (x - h) (by linarith) (by linarith)
    rw [show x - (x - h) = h by ring] at g1 g2
    have habs := (abs_le.mp g2).1
    have : K * (x ^ (1 / 2 : ℝ) + (x - h) ^ (1 / 2 : ℝ)) ≤ K * (2 * h + 2 * h) := by gcongr
    have e : (x ^ 2 - (x - h) ^ 2) / 2 = h * x - h * h / 2 := by ring
    rw [e] at habs
    linarith
  -- divide by `h`
  have hErrh : Err = h * (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K) := by
    rw [hErr]; field_simp; ring
  have hfin : |ψ x - x| ≤ h / 2 + (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K) := by
    rw [hErrh] at hup hlo
    rw [abs_le]
    constructor
    · have : h * (x - h / 2 - (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K)) ≤
          h * ψ x := by
        have : h * (x - h / 2 - (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K)) =
            h * x - h * h / 2 - h * (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K) := by
          ring
        linarith
      have := le_of_mul_le_mul_left this hh0
      linarith
    · have : h * ψ x ≤ h * (x + h / 2 + (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 6 * D2 * (L + 1) + 4 * K)) := by
        nlinarith
      have := le_of_mul_le_mul_left this hh0
      linarith
  exact hfin.trans (final_arith (by linarith) hL1 (norm_nonneg _) hD1 hD2 hK0)

end LeanLab.PNTPort.ExplicitPsi1

