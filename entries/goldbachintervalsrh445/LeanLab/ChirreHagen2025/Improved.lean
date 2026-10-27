module

public import Mathlib
public import LeanLab.ChirreHagen2025.Lower

/-!
DISCOVER I-0010, from P0075 Chirre-Hagen 2025. The pairing in Lower.lean needs only
`δ x ≤ h`, not `δ x ≤ h / 2`: primes in `(t, (1+δ) t]` and `(x - t, (1+δ)(x - t)]` sum into
`(x, x + δ x]`. With `δ = h / x` the Section 5 contradiction needs only
`C > 3 · 2.5571 / (1/8 - a³) ≈ 61.37` instead of `6 · 2.5571 / (1/8 - a³) ≈ 122.74`.
So, from the paper's own Theorem 3 under RH and the `4 · 10^18` even check, a Goldbach number
lies in `(x, x + 62 log² x)` for every `x ≥ 2`. Conditional on RH, through Theorem 3 which
stays cited. New to us until a literature search says otherwise; see IDEAS.md I-0010.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The wide form of the lower bound: `δ ≤ h / x` suffices. -/
theorem noGoldbachLower_wide :
    ∀ a x h δ : ℝ, 0 < a → a < 1 → 2 ≤ a * x → 0 < x → 0 < δ → δ * x ≤ h →
    (¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) →
    δ ^ 2 * x ^ 3 / 3 * (1 / 8 - a ^ 3) ≤ JthetaFrom a x δ := by
  intro a x h δ ha ha1 hax hx0 hδ hδx hno
  have hF0 : ∀ y, 0 ≤ F δ y := fun y => sq_nonneg _
  have hJ : JthetaFrom a x δ = ∫ y in a * x..x, F δ y := rfl
  have hax_le : a * x ≤ x := by nlinarith
  rcases le_or_gt (1 / 2) a with hbig | hsmall
  · have h8 : 1 / 8 - a ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hbig 3
      norm_num at this ⊢; linarith
    have : 0 ≤ JthetaFrom a x δ := intervalIntegral.integral_nonneg hax_le (fun y _ => sq_nonneg _)
    have : δ ^ 2 * x ^ 3 / 3 * (1 / 8 - a ^ 3) ≤ 0 := by
      have : 0 ≤ δ ^ 2 * x ^ 3 / 3 := by positivity
      nlinarith
    linarith
  · have hax2 : a * x ≤ x / 2 := by nlinarith
    have hmid : x / 2 ≤ x - a * x := by linarith
    have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
      fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
    have i1 := iF (a * x) (x / 2) (by linarith) hax2
    have i2 := iF (x / 2) (x - a * x) (by linarith) hmid
    have i3 := iF (x - a * x) x (by linarith) (by linarith)
    have i2r : IntervalIntegrable (fun t => F δ (x - t)) MeasureTheory.volume (a * x) (x / 2) := by
      have := (i2.symm).comp_sub_left x
      simpa [sub_sub_cancel, show x - x / 2 = x / 2 by ring] using this
    have hsum : ∫ t in a * x..x / 2, δ ^ 2 * t ^ 2 ≤
        ∫ t in a * x..x / 2, (F δ t + F δ (x - t)) := by
      apply intervalIntegral.integral_mono_on hax2
      · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
      · exact i1.add i2r
      · intro t ht
        exact pointwise hδ hδx (le_trans hax ht.1) ht.2 hno
    rw [intervalIntegral.integral_add i1 i2r, intervalIntegral.integral_comp_sub_left
      (fun y => F δ y) x] at hsum
    have e1 : x - x / 2 = x / 2 := by ring
    rw [e1, intervalIntegral.integral_add_adjacent_intervals i1 i2] at hsum
    have hrest : 0 ≤ ∫ y in x - a * x..x, F δ y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => hF0 y)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3
    have hpow : ∫ t in a * x..x / 2, δ ^ 2 * t ^ 2 = δ ^ 2 * x ^ 3 / 3 * (1 / 8 - a ^ 3) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring
    rw [hpow] at hsum
    rw [hJ, ← hsplit]
    linarith

theorem C2_choice : 3 * 2.5571 / (1 / 8 - (1 / 10 ^ 13 : ℝ) ^ 3) < 61.5 := by norm_num

/-- `61.5 log² x / x ≤ 10^-13` for `x ≥ 1.1 · 10^18`. -/
theorem threshold2 {x : ℝ} (hx : 1.1 * 10 ^ 18 ≤ x) :
    61.5 * Real.log x ^ 2 / x ≤ 1 / 10 ^ 13 := by
  have h := threshold hx
  have hxpos : 0 < x := by linarith
  have e : 61.5 * Real.log x ^ 2 / x = 123 / 122.75 * (122.75 * Real.log x ^ 2 / (2 * x)) := by
    field_simp; ring
  -- the 122.75 threshold has slack: 61.375 · 42² / 1.1e18 < 0.985e-13
  have hb : Real.log x ^ 2 / x ≤ 42 ^ 2 / (1.1 * 10 ^ 18) := by
    have he2 : Real.exp 2 ≤ 1.1 * 10 ^ 18 := by
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr; exact Real.exp_one_lt_d9.le
        _ ≤ 1.1 * 10 ^ 18 := by norm_num
    have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.mpr he2)
      (Set.mem_Ici.mpr (le_trans he2 hx)) hx
    simp only at hanti
    have hx0 : (0 : ℝ) < 1.1 * 10 ^ 18 := by norm_num
    have hl0 : 0 ≤ Real.log x / √x :=
      div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
    have hsq := pow_le_pow_left₀ hl0 hanti 2
    rw [div_pow, div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hx0.le] at hsq
    have hlx0 : 0 ≤ Real.log (1.1 * 10 ^ 18) := Real.log_nonneg (by norm_num)
    have h42 : Real.log (1.1 * 10 ^ 18) ^ 2 ≤ 42 ^ 2 := pow_le_pow_left₀ hlx0 log_x0_le 2
    exact le_trans hsq (div_le_div_of_nonneg_right h42 hx0.le)
  have : 61.5 * Real.log x ^ 2 / x = 61.5 * (Real.log x ^ 2 / x) := by ring
  rw [this]
  calc 61.5 * (Real.log x ^ 2 / x) ≤ 61.5 * (42 ^ 2 / (1.1 * 10 ^ 18)) := by gcongr
    _ ≤ 1 / 10 ^ 13 := by norm_num

/-- The numerical core with `h = 61.5 log² x`, `δ = h / x`. -/
theorem core2 {x : ℝ} (hx : 1.1 * 10 ^ 18 ≤ x) :
    2.5571 * (61.5 * Real.log x ^ 2 / x) *
        Real.log (2.0001 / (61.5 * Real.log x ^ 2 / x)) ^ 2 * x ^ 2
      < (61.5 * Real.log x ^ 2 / x) ^ 2 * x ^ 3 / 3 * (1 / 8 - (1 / 10 ^ 13) ^ 3) := by
  set L := Real.log x with hLdef
  have hL : 41 ≤ L := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set δ := 61.5 * L ^ 2 / x with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 10 ^ 13 := threshold2 hx
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (2.0001 : ℝ) ≤ 61.5 * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hD : 0 < δ * x ^ 2 := by positivity
  have hdx : δ * x = 61.5 * L ^ 2 := by rw [hδ]; field_simp
  have e1 : 2.5571 * δ * u ^ 2 * x ^ 2 = (δ * x ^ 2) * (2.5571 * u ^ 2) := by ring
  have e2 : δ ^ 2 * x ^ 3 / 3 * (1 / 8 - (1 / 10 ^ 13) ^ 3)
      = (δ * x ^ 2) * ((δ * x) / 3 * (1 / 8 - (1 / 10 ^ 13) ^ 3)) := by ring
  rw [e1, e2]
  apply mul_lt_mul_of_pos_left _ hD
  rw [hdx]
  have hL2 : 0 < L ^ 2 := by positivity
  nlinarith

/-- A Goldbach number in `(x, x + 61.5 log² x]` for `x ≥ 1.1 · 10^18`, from Section 5's
upper bound alone; the lower bound is now proved. -/
theorem large2_of (hU : Section5Upper) :
    ∀ x : ℝ, 1.1 * 10 ^ 18 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 61.5 * Real.log x ^ 2 := by
  intro x hx
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := 61.5 * Real.log x ^ 2 with hh
  have hδle : h / x ≤ 1 / 10 ^ 13 := threshold2 hx
  have hδpos : 0 < h / x := by positivity
  have hδx : h / x * x = h := by field_simp
  have hlow := noGoldbachLower_wide (1 / 10 ^ 13) x h (h / x) (by norm_num) (by norm_num)
    (by linarith) hxpos hδpos hδx.le hno
  have hup := hU (1 / 10 ^ 13) x (h / x) le_rfl (by norm_num) (by linarith) hδpos hδle
  have hc := core2 hx
  rw [← hh] at hc
  linarith

/-- I-0010: under RH, via Chirre-Hagen's Theorem 3 and the `4 · 10^18` even check, a Goldbach
number lies in `(x, x + 62 log² x)` for every `x ≥ 2`. -/
theorem goldbach_62
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 62 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · obtain ⟨n, hn, h1, h2⟩ := large2_of (section5Upper_of_RH h3 hRH) x (by linarith)
    exact ⟨n, hn, h1, by nlinarith⟩

end LeanLab.ChirreHagen2025
