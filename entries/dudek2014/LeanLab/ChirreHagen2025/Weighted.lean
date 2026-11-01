module

public import Mathlib
public import LeanLab.ChirreHagen2025.Improved

/-!
T2, unit U-5025, from P0075 Chirre-Hagen 2025 and the lab's I-0010. A weighted Section 5.
Lower.lean and Improved.lean integrate the pairing bound `F t + F (x - t) ≥ δ² t²` against the
constant weight, which forces `δ x > 24 · 2.5571 · L²`. Here the weight is `1` on `[1, x/2]`
and a step version of `((x - u)/u)²` on `[x/2, x]`: on the piece `u ∈ [s_j x, s_{j+1} x]` it is
`v_j = ((1 - s_j)/s_j)²`, so `F t + v_j F (x - t) ≥ δ² t²` still holds for the partner
`t = x - u`, while Abel summation over the scales `s_j x` bounds the weighted integral by
Theorem 3 at each scale. The continuous weight gives the constant `24 (2 log 2 - 1) · 2.5571`,
about `23.71`; the 16 steps used here give `24.82`, so `25 log² x`.
Conditional on RH, through Chirre-Hagen Theorem 3 which stays a hypothesis, and on the
`4 · 10^18` even check. Binary Goldbach is open; this is a conditional short-interval result.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The Abel sum `v₀ G₀ + Σ_{j<N} v_j (G_{j+1} - G_j)`, the integral of a step weight. -/
def abelSum (v G : ℕ → ℝ) (N : ℕ) : ℝ :=
  v 0 * G 0 + ∑ j ∈ Finset.range N, v j * (G (j + 1) - G j)

theorem abelSum_aux (v G B : ℕ → ℝ) (hv : Antitone v)
    (hGB : ∀ j, G j ≤ B j) (N : ℕ) :
    v (N - 1) * (B N - G N) ≤ abelSum v B N - abelSum v G N := by
  induction N with
  | zero => simp [abelSum]; linarith
  | succ n ih =>
    have e : abelSum v B (n + 1) - abelSum v G (n + 1) = abelSum v B n - abelSum v G n
        + v n * ((B (n + 1) - B n) - (G (n + 1) - G n)) := by
      simp only [abelSum, Finset.sum_range_succ]; ring
    rw [e, show n + 1 - 1 = n by omega]
    have h1 : v n ≤ v (n - 1) := hv (by omega)
    have h2 : 0 ≤ B n - G n := by linarith [hGB n]
    have h3 : v n * (B n - G n) ≤ v (n - 1) * (B n - G n) := mul_le_mul_of_nonneg_right h1 h2
    nlinarith

/-- Abel summation is monotone in `G` when the weights are nonnegative and nonincreasing. -/
theorem abelSum_mono (v G B : ℕ → ℝ) (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j)
    (hGB : ∀ j, G j ≤ B j) (N : ℕ) : abelSum v G N ≤ abelSum v B N := by
  have := abelSum_aux v G B hv hGB N
  have : 0 ≤ v (N - 1) * (B N - G N) := mul_nonneg (hv0 _) (by linarith [hGB N])
  linarith

/-- The weights `((1 - s)/s)²`. -/
noncomputable def wt (s : ℝ) : ℝ := ((1 - s) / s) ^ 2

/-- Pointwise on one piece: for `t ∈ [2, (1 - s) x]` with `1/2 ≤ s < 1` and no Goldbach number
in `(x, x + h]`, `δ² t² ≤ F t + wt s · F (x - t)`. -/
theorem pointwise_wt {x h δ t s : ℝ} (hδ : 0 < δ) (hδh : δ * x ≤ h) (ht2 : 2 ≤ t)
    (hs : 1 / 2 ≤ s) (hs1 : s < 1) (hts : t ≤ (1 - s) * x)
    (hno : ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) :
    δ ^ 2 * t ^ 2 ≤ F δ t + wt s * F δ (x - t) := by
  have hF0 : ∀ y, 0 ≤ F δ y := fun y => sq_nonneg _
  have hw0 : 0 ≤ wt s := sq_nonneg _
  have hle : ∀ y : ℝ, 0 ≤ y → y ≤ (1 + δ) * y := fun y hy => by nlinarith
  have hxt : s * x ≤ x - t := by linarith
  have hx0 : 0 < x := by nlinarith
  have hxt2 : 2 ≤ x - t := by nlinarith
  by_cases hS : θ ((1 + δ) * t) = θ t
  · have : F δ t = δ ^ 2 * t ^ 2 := by unfold F; rw [hS]; ring
    have := mul_nonneg hw0 (hF0 (x - t))
    linarith
  · by_cases hS' : θ ((1 + δ) * (x - t)) = θ (x - t)
    · have hFx : F δ (x - t) = δ ^ 2 * (x - t) ^ 2 := by unfold F; rw [hS']; ring
      have hs0 : 0 < s := by linarith
      have hkey : t * s ≤ (1 - s) * (x - t) := by nlinarith
      have hsq : (t * s) ^ 2 ≤ ((1 - s) * (x - t)) ^ 2 :=
        pow_le_pow_left₀ (by nlinarith) hkey 2
      have hw : t ^ 2 ≤ wt s * (x - t) ^ 2 := by
        unfold wt
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have : δ ^ 2 * t ^ 2 ≤ wt s * F δ (x - t) := by
        rw [hFx]; nlinarith [sq_nonneg δ]
      linarith [hF0 t]
    · exfalso
      obtain ⟨p, hp, hp1, hp2⟩ := prime_of_theta_ne (by linarith) (hle t (by linarith)) hS
      obtain ⟨q, hq, hq1, hq2⟩ :=
        prime_of_theta_ne (by linarith) (hle (x - t) (by linarith)) hS'
      have hp2' : p ≠ 2 := by rintro rfl; norm_num at hp1; linarith
      have hq2' : q ≠ 2 := by rintro rfl; norm_num at hq1; linarith
      apply hno
      refine ⟨p + q, ⟨p, q, hp, hq, hp.odd_of_ne_two hp2', hq.odd_of_ne_two hq2', rfl⟩, ?_, ?_⟩
      · push_cast; linarith
      · push_cast; nlinarith

/-- `G_j = ∫_1^{s_j x} F`, the partial integrals at the scales. -/
noncomputable def Gs (δ x : ℝ) (s : ℕ → ℝ) (j : ℕ) : ℝ := ∫ y in (1 : ℝ)..s j * x, F δ y

/-- The weighted lower bound, by induction on the number of pieces. For a nondecreasing
`s` with `s 0 = 1/2`, `s j < 1` and `(1 - s j) x ≥ 2`, and no Goldbach number in `(x, x + h]`
with `δ x ≤ h`:
`δ² ∫_{(1 - s_N) x}^{x/2} t² + ∫_1^{(1 - s_N) x} F ≤ abelSum (wt ∘ s) G N`. -/
theorem weighted_lower {x h δ : ℝ} (s : ℕ → ℝ) (hδ : 0 < δ) (hδh : δ * x ≤ h)
    (hsm : Monotone s) (hs0 : s 0 = 1 / 2) (hs1 : ∀ j, s j < 1) (hs2 : ∀ j, 2 ≤ (1 - s j) * x)
    (hno : ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) (N : ℕ) :
    δ ^ 2 * ((x / 2) ^ 3 - ((1 - s N) * x) ^ 3) / 3 + ∫ y in (1 : ℝ)..(1 - s N) * x, F δ y
      ≤ abelSum (fun j => wt (s j)) (Gs δ x s) N := by
  have hx0 : 0 < x := by
    have := hs2 0; rw [hs0] at this; linarith
  have hhalf : ∀ j, 1 / 2 ≤ s j := fun j => hs0 ▸ hsm (Nat.zero_le j)
  have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
    fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
  induction N with
  | zero =>
    simp only [abelSum, Finset.range_zero, Finset.sum_empty, add_zero, hs0, Gs]
    have : wt (1 / 2) = 1 := by unfold wt; norm_num
    rw [this, one_mul, show (1 - 1 / 2 : ℝ) * x = 1 / 2 * x by ring,
      show x / 2 = 1 / 2 * x by ring]
    simp
  | succ n ih =>
    set a := (1 - s n) * x with ha
    set b := (1 - s (n + 1)) * x with hb
    have hb2 : 2 ≤ b := hs2 (n + 1)
    have hba : b ≤ a := by
      have := hsm (Nat.le_succ n); nlinarith
    have hsn : s n * x ≤ s (n + 1) * x := by
      have := hsm (Nat.le_succ n); nlinarith
    have hsn0 : 0 ≤ s n * x := by nlinarith [hhalf n]
    -- the step of the Abel sum is `wt (s n) ∫_{s_n x}^{s_{n+1} x} F`
    have hstep : abelSum (fun j => wt (s j)) (Gs δ x s) (n + 1)
        = abelSum (fun j => wt (s j)) (Gs δ x s) n
          + wt (s n) * ∫ u in s n * x..s (n + 1) * x, F δ u := by
      simp only [abelSum, Finset.sum_range_succ, Gs]
      rw [intervalIntegral.integral_interval_sub_left (iF 1 _ zero_le_one (by nlinarith [hhalf (n + 1)]))
        (iF 1 _ zero_le_one (by nlinarith [hhalf n]))]
      ring
    -- reflect the piece: `∫_{s_n x}^{s_{n+1} x} F = ∫_b^a F (x - t)`
    have hrefl : ∫ u in s n * x..s (n + 1) * x, F δ u = ∫ t in b..a, F δ (x - t) := by
      rw [intervalIntegral.integral_comp_sub_left (fun y => F δ y) x]
      congr 1 <;> ring
    have i_ba : IntervalIntegrable (F δ) MeasureTheory.volume b a := iF b a (by linarith) hba
    have i_ref : IntervalIntegrable (fun t => F δ (x - t)) MeasureTheory.volume b a := by
      have := (iF (s n * x) (s (n + 1) * x) hsn0 hsn).symm.comp_sub_left x
      have e1 : x - s (n + 1) * x = b := by rw [hb]; ring
      have e2 : x - s n * x = a := by rw [ha]; ring
      simpa [e1, e2] using this
    -- the piece integral of the pairing bound
    have hpiece : δ ^ 2 * (a ^ 3 - b ^ 3) / 3 ≤
        ∫ t in b..a, (F δ t + wt (s n) * F δ (x - t)) := by
      have hpow : ∫ t in b..a, δ ^ 2 * t ^ 2 = δ ^ 2 * (a ^ 3 - b ^ 3) / 3 := by
        rw [intervalIntegral.integral_const_mul, integral_pow]; ring
      rw [← hpow]
      apply intervalIntegral.integral_mono_on hba
      · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
      · exact i_ba.add (i_ref.const_mul _)
      · intro t ht
        exact pointwise_wt hδ hδh (le_trans hb2 ht.1) (hhalf n) (hs1 n) ht.2 hno
    rw [intervalIntegral.integral_add i_ba (i_ref.const_mul _),
      intervalIntegral.integral_const_mul] at hpiece
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (iF 1 b zero_le_one (by linarith)) i_ba
    rw [hstep, hrefl]
    have : δ ^ 2 * ((x / 2) ^ 3 - b ^ 3) / 3
        = δ ^ 2 * ((x / 2) ^ 3 - a ^ 3) / 3 + δ ^ 2 * (a ^ 3 - b ^ 3) / 3 := by ring
    rw [this]
    linarith

/-- The scales used: `s_j = 1/2 + 7 j / 256` for `j ≤ 16`, then constant `15/16`. -/
noncomputable def s16 (j : ℕ) : ℝ := 1 / 2 + 7 * ((min j 16 : ℕ) : ℝ) / 256

theorem s16_mono : Monotone s16 := by
  intro i j hij
  unfold s16
  have : ((min i 16 : ℕ) : ℝ) ≤ ((min j 16 : ℕ) : ℝ) := by exact_mod_cast min_le_min_right 16 hij
  linarith

theorem s16_bounds (j : ℕ) : 1 / 2 ≤ s16 j ∧ s16 j ≤ 15 / 16 := by
  unfold s16
  have h1 : ((min j 16 : ℕ) : ℝ) ≤ 16 := by exact_mod_cast min_le_right j 16
  have h0 : (0 : ℝ) ≤ ((min j 16 : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

theorem wt_antitone : Antitone (fun j => wt (s16 j)) := by
  intro i j hij
  simp only [wt]
  have hi := s16_bounds i
  have hj := s16_bounds j
  have hm := s16_mono hij
  have hpi : 0 < s16 i := by linarith
  have hpj : 0 < s16 j := by linarith
  apply pow_le_pow_left₀ (div_nonneg (by linarith) hpj.le)
  rw [div_le_div_iff₀ hpj hpi]
  nlinarith

/-- The step weight's Abel sum of `u ↦ u²`, the constant `U`, is below `0.4036`;
the continuous weight would give `2 log 2 - 1 ≈ 0.3863`. -/
theorem U16_lt : abelSum (fun j => wt (s16 j)) (fun j => s16 j ^ 2) 16 < 0.4036 := by
  simp only [abelSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, s16, wt]
  norm_num

/-- With `h = 24.9 log² x`, `δ = h / x`, the weighted contradiction for `x ≥ 1.1 · 10^18`. -/
theorem core25 {x : ℝ} (hx : 1.1 * 10 ^ 18 ≤ x) :
    2.5571 * (24.9 * Real.log x ^ 2 / x) *
        Real.log (2.0001 / (24.9 * Real.log x ^ 2 / x)) ^ 2 * x ^ 2 * 0.4036
      < (24.9 * Real.log x ^ 2 / x) ^ 2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3 := by
  set L := Real.log x with hLdef
  have hL : 41 ≤ L := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set δ := 24.9 * L ^ 2 / x with hδ
  have hδpos : 0 < δ := by positivity
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by
    rw [le_div_iff₀ hδpos]
    have : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx
      have : δ ≤ 61.5 * L ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    linarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (2.0001 : ℝ) ≤ 24.9 * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hD : 0 < δ * x ^ 2 := by positivity
  have hdx : δ * x = 24.9 * L ^ 2 := by rw [hδ]; field_simp
  have e1 : 2.5571 * δ * u ^ 2 * x ^ 2 * 0.4036 = (δ * x ^ 2) * (2.5571 * 0.4036 * u ^ 2) := by
    ring
  have e2 : δ ^ 2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3
      = (δ * x ^ 2) * ((δ * x) * (1 / 8 - 1 / 4096) / 3) := by ring
  rw [e1, e2]
  apply mul_lt_mul_of_pos_left _ hD
  rw [hdx]
  have hL2 : 0 < L ^ 2 := by positivity
  nlinarith

/-- A Goldbach number in `(x, x + 24.9 log² x]` for `x ≥ 1.1 · 10^18`, from Theorem 3 at the
17 scales `s_j x`, `x/2 ≤ s_j x ≤ 15x/16`. -/
theorem large25_of
    (h3 : ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2) :
    ∀ x : ℝ, 1.1 * 10 ^ 18 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 24.9 * Real.log x ^ 2 := by
  intro x hx
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := 24.9 * Real.log x ^ 2 with hh
  have hδpos : 0 < h / x := by positivity
  have hδle : h / x ≤ 1 / 10 ^ 13 := by
    have := threshold2 hx
    have : h / x ≤ 61.5 * Real.log x ^ 2 / x := by
      rw [hh]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
    linarith
  have hδx : h / x * x = h := by field_simp
  set δ := h / x with hδ
  set K := 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.log (2.0001 / δ) ^ 2 := sq_nonneg _
    positivity
  -- lower bound
  have hlow := weighted_lower (x := x) (h := h) s16 hδpos hδx.le s16_mono
    (by simp [s16]) (fun j => by linarith [(s16_bounds j).2])
    (fun j => by nlinarith [(s16_bounds j).2]) hno 16
  have hs16 : s16 16 = 15 / 16 := by simp [s16]; norm_num
  rw [hs16] at hlow
  have hF1 : 0 ≤ ∫ y in (1 : ℝ)..(1 - 15 / 16) * x, F δ y :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun y _ => sq_nonneg _)
  -- upper bound, Theorem 3 at each scale
  have hGB : ∀ j, Gs δ x s16 j ≤ x ^ 2 * K * s16 j ^ 2 := by
    intro j
    have hb := s16_bounds j
    have hX : 10 ^ 13 ≤ s16 j * x := by nlinarith
    have := h3 (s16 j * x) δ hX hδpos hδle
    have e : Jtheta (s16 j * x) δ = Gs δ x s16 j := rfl
    rw [e] at this
    calc Gs δ x s16 j ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * (s16 j * x) ^ 2 := this
      _ = x ^ 2 * K * s16 j ^ 2 := by rw [hK]; ring
  have hup := abelSum_mono (fun j => wt (s16 j)) (Gs δ x s16) (fun j => x ^ 2 * K * s16 j ^ 2)
    wt_antitone (fun j => sq_nonneg _) hGB 16
  have hfac : abelSum (fun j => wt (s16 j)) (fun j => x ^ 2 * K * s16 j ^ 2) 16
      = x ^ 2 * K * abelSum (fun j => wt (s16 j)) (fun j => s16 j ^ 2) 16 := by
    simp only [abelSum]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac] at hup
  have hU := U16_lt
  have hxK : 0 ≤ x ^ 2 * K := by positivity
  have hup2 : abelSum (fun j => wt (s16 j)) (Gs δ x s16) 16 ≤ x ^ 2 * K * 0.4036 := by
    have := mul_le_mul_of_nonneg_left hU.le hxK
    linarith
  have hc := core25 hx
  rw [← hh, ← hδ] at hc
  have e16 : (1 - 15 / 16 : ℝ) * x = x / 16 := by ring
  rw [e16] at hlow hF1
  have hKx : x ^ 2 * K * 0.4036 = 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 * 0.4036 := by
    rw [hK]; ring
  linarith

/-- U-5025: under RH, via Chirre-Hagen's Theorem 3 and the `4 · 10^18` even check, a Goldbach
number lies in `(x, x + 25 log² x)` for every `x ≥ 2`. The paper has 123, the lab's I-0010 62. -/
theorem goldbach_25
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 25 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · obtain ⟨n, hn, h1, h2⟩ := large25_of (h3 hRH) x (by linarith)
    exact ⟨n, hn, h1, by nlinarith⟩

end LeanLab.ChirreHagen2025

