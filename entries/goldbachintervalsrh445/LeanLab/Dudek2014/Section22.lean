module

public import Mathlib
public import LeanLab.Dudek2014.Statements
public import LeanLab.Helfgott2013.GammaFine

/-!
P0100 Dudek 2014, arXiv 1402.6417, Sections 2.1 and 2.2: the numeric steps of the proof of
Theorem 2.
- Lemma 4: `|ε(x)| < 2 + 2^{3/2} Σ 1/|ρ|² + (1/2)|log(16/27)| < 12/5`, with
  `Σ 1/|ρ|² = 2 + γ - log 4π` as the paper cites from Davenport; value `2.3923`. MATCHES.
- Section 2.2, page 6: with `h = (2/π) √x log x`, the right side of the last display
  `h - (2/π)(x/√(x-h) + (x+h)^{3/2}/x) log(2x/h) - 1.11 √(x+h) - 3 (x+h)^{1/3}
   + 0.98 √(x-h) - 48/(5h)` is positive for every `x ≥ 65000`. The paper says "using a
  monotonicity argument"; here it is PROVED for every such x by explicit bounds. Python puts the
  zero near x ≈ 5200, so 65000 is safe; value 208.1 at 65000.
- The shift "replacing x + d √x log x with x": from a prime in `(x - h, x + h]` for every
  `x ≥ 65000` to a prime in `(X - (4/π)√X log X, X]` for every `X ≥ 66799`, by the intermediate
  value theorem; the paper's threshold `65000 + (2/π)√65000 log 65000 ≈ 66798.7` is checked.
So `theorem2_large` follows from one cited input, the paper's displayed lower bound for
`Σ_{x-h<p≤x+h} log p`, which the paper derives from RH, Lemma 5, Trudgian's N(T), Skewes'
Lemma 1 (ii) and Schoenfeld's ψ - θ bounds.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Section22
open Real Finset

noncomputable section

/-! ### Lemma 4's constant -/

theorem pi_bounds : (0.6366 : ℝ) ≤ 2 / π ∧ 2 / π ≤ 0.63662 := by
  have h1 := pi_gt_d6; have h2 := pi_lt_d6
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

theorem log_pi_lt : log π < 1.1448 := by
  have h1 := pi_lt_d4
  have he : (3.1416 : ℝ) ≤ exp 1.1448 := by
    have e : exp (1.1448 : ℝ) = exp 1 * exp 0.1448 := by rw [← exp_add]; norm_num
    have h2 := exp_one_gt_d9
    have h3 := sum_le_exp_of_nonneg (x := (0.1448 : ℝ)) (by norm_num) 4
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h3
    norm_num at h3
    rw [e]; nlinarith [exp_pos (0.1448 : ℝ)]
  rw [log_lt_iff_lt_exp (by linarith [pi_gt_three])]; linarith

theorem log_pi_gt : (1.14472 : ℝ) < log π := by
  have h1 := pi_gt_d6
  have he : exp (1.14472 : ℝ) < 3.14159 := by
    have e : exp (1.14472 : ℝ) = exp 1 * exp 0.14472 := by rw [← exp_add]; norm_num
    have h2 := exp_one_lt_d9
    have h3 := Real.exp_bound' (x := (0.14472 : ℝ)) (by norm_num) (by norm_num) (n := 8)
      (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h3
    norm_num at h3
    rw [e]; nlinarith [exp_pos (0.14472 : ℝ), exp_pos (1 : ℝ)]
  rw [lt_log_iff_exp_lt (by linarith [pi_gt_three])]; linarith

/-- **Lemma 4: `2 + 2^{3/2}(2 + γ - log 4π) + (1/2) log(27/16) < 12/5`.** MATCHES, `2.3923`. -/
theorem lemma4_const :
    2 + 2 * √2 * (2 + eulerMascheroniConstant - log (4 * π)) + 1 / 2 * log (27 / 16) <
      (12 / 5 : ℝ) := by
  have hg := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
  have h4 : log (4 * π) = 2 * log 2 + log π := by
    rw [log_mul (by norm_num) (by linarith [pi_gt_three]),
      show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  have hp := log_pi_gt
  have l2 := log_two_gt_d9; have l2' := log_two_lt_d9
  have hs : √2 ≤ 1.41422 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have hS : 2 + eulerMascheroniConstant - log (4 * π) ≤ 0.04622 := by rw [h4]; linarith
  have hS0 : 0 ≤ 2 + eulerMascheroniConstant - log (4 * π) ∨
      2 + eulerMascheroniConstant - log (4 * π) < 0 := le_or_gt _ _
  have h2716 : log (27 / 16 : ℝ) ≤ 0.5233 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 27 / 16 * (16 / 27) * (27 / 16) by norm_num)
    have e : log (27 / 16 : ℝ) = 3 * log 3 - 4 * log 2 := by
      rw [log_div (by norm_num) (by norm_num), show (27 : ℝ) = 3 ^ 3 by norm_num,
        show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow, log_pow]; push_cast; ring
    have h3 : log (3 : ℝ) < 1.0986123 := by
      have e3 : log (3 : ℝ) = log 2 + log (3 / 2) := by
        rw [← log_mul (by norm_num) (by norm_num)]; norm_num
      have := LeanLab.Helfgott2013.GammaFine.log_three_halves_gt
      have h32 := LeanLab.ChenExplicit.Gamma.log_one_add_inv_le_sum (a := (2 : ℝ)) (by norm_num) 6
      simp only [sum_range_succ, sum_range_zero] at h32
      rw [show (1 : ℝ) + (2 : ℝ)⁻¹ = 3 / 2 by norm_num] at h32
      norm_num at h32
      linarith
    rw [e]; linarith
  rcases hS0 with h0 | h0
  · have : 2 * √2 * (2 + eulerMascheroniConstant - log (4 * π)) ≤ 2 * 1.41422 * 0.04622 := by
      apply mul_le_mul (by linarith) hS h0 (by norm_num)
    linarith
  · have : 2 * √2 * (2 + eulerMascheroniConstant - log (4 * π)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
    linarith

/-- The same pieces are at most `2.393`, the constant the lab's `Lemma4` Prop cites. -/
theorem lemma4_const_2393 :
    2 + 2 * √2 * (2 + eulerMascheroniConstant - log (4 * π)) + 1 / 2 * log (27 / 16) <
      (2.393 : ℝ) := by
  have hg := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
  have h4 : log (4 * π) = 2 * log 2 + log π := by
    rw [log_mul (by norm_num) (by linarith [pi_gt_three]),
      show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  have hp := log_pi_gt
  have l2 := log_two_gt_d9; have l2' := log_two_lt_d9
  have hs : √2 ≤ 1.41422 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have hS : 2 + eulerMascheroniConstant - log (4 * π) ≤ 0.04622 := by rw [h4]; linarith
  have hS0 : 0 ≤ 2 + eulerMascheroniConstant - log (4 * π) ∨
      2 + eulerMascheroniConstant - log (4 * π) < 0 := le_or_gt _ _
  have h2716 : log (27 / 16 : ℝ) ≤ 0.5233 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 27 / 16 * (16 / 27) * (27 / 16) by norm_num)
    have e : log (27 / 16 : ℝ) = 3 * log 3 - 4 * log 2 := by
      rw [log_div (by norm_num) (by norm_num), show (27 : ℝ) = 3 ^ 3 by norm_num,
        show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow, log_pow]; push_cast; ring
    have h3 : log (3 : ℝ) < 1.0986123 := by
      have e3 : log (3 : ℝ) = log 2 + log (3 / 2) := by
        rw [← log_mul (by norm_num) (by norm_num)]; norm_num
      have := LeanLab.Helfgott2013.GammaFine.log_three_halves_gt
      have h32 := LeanLab.ChenExplicit.Gamma.log_one_add_inv_le_sum (a := (2 : ℝ)) (by norm_num) 6
      simp only [sum_range_succ, sum_range_zero] at h32
      rw [show (1 : ℝ) + (2 : ℝ)⁻¹ = 3 / 2 by norm_num] at h32
      norm_num at h32
      linarith
    rw [e]; linarith
  rcases hS0 with h0 | h0
  · have : 2 * √2 * (2 + eulerMascheroniConstant - log (4 * π)) ≤ 2 * 1.41422 * 0.04622 := by
      apply mul_le_mul (by linarith) hS h0 (by norm_num)
    linarith
  · have : 2 * √2 * (2 + eulerMascheroniConstant - log (4 * π)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
    linarith

/-! ### Section 2.2: the last display is positive for `x ≥ 65000` -/

/-- `h = (2/π) √x log x`. -/
def hD (x : ℝ) : ℝ := 2 / π * √x * log x

/-- The right side of the last display of Section 2.2, page 6. -/
def rhs (x : ℝ) : ℝ :=
  hD x - 2 / π * (x / √(x - hD x) + (x + hD x) ^ (3 / 2 : ℝ) / x) * log (2 * x / hD x)
    - 1.11 * √(x + hD x) - 3 * (x + hD x) ^ (1 / 3 : ℝ) + 0.98 * √(x - hD x) - 48 / (5 * hD x)

theorem log_65000 : (11.07 : ℝ) ≤ log 65000 := by
  have h := log_le_sub_one_of_pos (show (0 : ℝ) < 65536 / 65000 by norm_num)
  have e : log (65536 / 65000 : ℝ) = 16 * log 2 - log 65000 := by
    rw [log_div (by norm_num) (by norm_num), show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow]
    push_cast; ring
  have := log_two_gt_d9
  linarith

theorem exp_24 : exp (2.4 : ℝ) ≤ 11.07 := by
  have e : exp (2.4 : ℝ) = exp 1 * exp 1 * exp 0.4 := by rw [← exp_add, ← exp_add]; norm_num
  have h1 := exp_one_lt_d9
  have h3 := Real.exp_bound' (x := (0.4 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h3
  norm_num at h3
  rw [e]
  have h0 := exp_pos (1 : ℝ)
  have : exp (1 : ℝ) * exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul h1.le h1.le h0.le (by norm_num)
  nlinarith [exp_pos (0.4 : ℝ)]

/-- `4 (log t)² ≤ 0.9 t` for `t ≥ 254`, from `e^w ≥ 1 + w + w²/2`. -/
theorem log_sq_le {t : ℝ} (ht : 254 ≤ t) : 4 * log t ^ 2 ≤ 0.9 * t := by
  have ht0 : 0 < t := by linarith
  set w := log (t / 254) with hw
  have hw0 : 0 ≤ w := log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have htw : t = 254 * exp w := by rw [hw, exp_log (by positivity)]; field_simp
  have hlt : log t = log 254 + w := by rw [hw, log_div ht0.ne' (by norm_num)]; ring
  have h254 : log (254 : ℝ) ≤ 5.546 := by
    have := log_le_log (by norm_num) (show (254 : ℝ) ≤ 256 by norm_num)
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, log_pow] at this
    have := log_two_lt_d9; push_cast at *; linarith
  have h2540 : 0 ≤ log (254 : ℝ) := log_nonneg (by norm_num)
  have hq := quadratic_le_exp_of_nonneg hw0
  rw [hlt]
  have : (log 254 + w) ^ 2 ≤ (5.546 + w) ^ 2 := by nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
theorem rhs_pos {x : ℝ} (hx : 65000 ≤ x) : 0 < rhs x := by
  have hx0 : 0 < x := by linarith
  set t := √x with htdef
  have ht2 : t ^ 2 = x := sq_sqrt hx0.le
  have ht : 254 ≤ t := by rw [htdef, le_sqrt (by norm_num) hx0.le]; linarith
  have ht0 : 0 < t := by linarith
  set L := log x with hLdef
  have hLt : L = 2 * log t := by rw [hLdef, ← ht2, log_pow]; push_cast; ring
  have hL : 11.07 ≤ L := le_trans log_65000 (log_le_log (by norm_num) hx)
  have hL2 : L ^ 2 ≤ 0.9 * t := by rw [hLt]; nlinarith [log_sq_le ht]
  have hlogL : 2.4 ≤ log L := by
    rw [le_log_iff_exp_le (by linarith)]; linarith [exp_24]
  have hlp := log_pi_lt
  have hlp' := log_pi_gt
  obtain ⟨hc1, hc2⟩ := pi_bounds
  set c := 2 / π with hc
  have hπ0 : 0 < π := pi_pos
  -- u = c L / t, h = u t²
  set u := c * L / t with hu
  have hLt' : L / t ≤ 0.0813 := by
    rw [div_le_iff₀ ht0]; nlinarith
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 0.052 := by
    rw [hu, mul_div_assoc]; nlinarith [div_nonneg (by linarith : (0 : ℝ) ≤ L) ht0.le]
  have hhD : hD x = c * t * L := rfl
  have hh : hD x = u * x := by
    rw [hhD, hu, ← ht2]; field_simp
  have htu : t * u = c * L := by rw [hu]; field_simp
  -- square roots
  have hsm : √(x - hD x) = t * √(1 - u) := by
    rw [hh, show x - u * x = t ^ 2 * (1 - u) by rw [← ht2]; ring,
      sqrt_mul (by positivity), sqrt_sq ht0.le]
  have hsp : √(x + hD x) = t * √(1 + u) := by
    rw [hh, show x + u * x = t ^ 2 * (1 + u) by rw [← ht2]; ring,
      sqrt_mul (by positivity), sqrt_sq ht0.le]
  have hs1 : 1 - u ≤ √(1 - u) := by
    rw [le_sqrt (by linarith) (by linarith)]; nlinarith
  have hs2 : √(1 + u) ≤ 1 + u / 2 := by
    rw [sqrt_le_left (by linarith)]; nlinarith
  have hs2' : 1 ≤ √(1 + u) := by rw [le_sqrt (by norm_num) (by linarith)]; linarith
  -- the bracket P
  have hP1 : x / √(x - hD x) ≤ t * (1 + 1.06 * u) := by
    rw [hsm, ← ht2, div_le_iff₀ (by nlinarith)]
    have k1 : 1 ≤ (1 + 1.06 * u) * (1 - u) := by nlinarith
    have k2 : (1 + 1.06 * u) * (1 - u) ≤ (1 + 1.06 * u) * √(1 - u) :=
      mul_le_mul_of_nonneg_left hs1 (by linarith)
    have k3 := mul_le_mul_of_nonneg_left (k1.trans k2) (sq_nonneg t)
    have e : t * (1 + 1.06 * u) * (t * √(1 - u)) = t ^ 2 * ((1 + 1.06 * u) * √(1 - u)) := by ring
    rw [e]; linarith
  have h32 : (x + hD x) ^ (3 / 2 : ℝ) = (x + hD x) * √(x + hD x) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (by rw [hh]; positivity), rpow_one,
      sqrt_eq_rpow]
  have hP2 : (x + hD x) ^ (3 / 2 : ℝ) / x ≤ t * (1 + 1.53 * u) := by
    rw [h32, hsp, hh, div_le_iff₀ hx0]
    have k1 : (1 + u) * √(1 + u) ≤ (1 + u) * (1 + u / 2) :=
      mul_le_mul_of_nonneg_left hs2 (by linarith)
    have k : (1 + u) * √(1 + u) ≤ 1 + 1.53 * u := by nlinarith
    have e : (x + u * x) * (t * √(1 + u)) = (x * t) * ((1 + u) * √(1 + u)) := by ring
    have e2 : t * (1 + 1.53 * u) * x = (x * t) * (1 + 1.53 * u) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left k (by positivity)
  -- the logarithm A = log(2x/h) = log π + L/2 - log L
  have hA : log (2 * x / hD x) = log π + L / 2 - log L := by
    have e : 2 * x / hD x = π * t / L := by
      rw [hh, hu, hc]; field_simp
    rw [e, log_div (by positivity) (by linarith), log_mul hπ0.ne' ht0.ne']
    rw [hLt]; ring
  have hA0 : 0 ≤ log π + L / 2 - log L := by
    have : log L ≤ L / 2 := by
      have := log_le_sub_one_of_pos (show 0 < L / 4 by linarith)
      rw [log_div (by linarith) (by norm_num)] at this
      have h4 : log 4 ≤ (1.3863 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; have := log_two_lt_d9; push_cast; linarith
      linarith
    linarith
  have hAL : log π + L / 2 - log L ≤ L / 2 := by linarith
  -- assemble
  have hPA : c * (x / √(x - hD x) + (x + hD x) ^ (3 / 2 : ℝ) / x) * log (2 * x / hD x) ≤
      c * t * L - 2 * c * t * (log L - log π) + 0.525 * L ^ 2 := by
    rw [hA]
    have hP : x / √(x - hD x) + (x + hD x) ^ (3 / 2 : ℝ) / x ≤ t * (2 + 2.59 * u) := by
      linarith
    have h1 : c * (x / √(x - hD x) + (x + hD x) ^ (3 / 2 : ℝ) / x) * (log π + L / 2 - log L) ≤
        c * (t * (2 + 2.59 * u)) * (log π + L / 2 - log L) := by
      apply mul_le_mul_of_nonneg_right _ hA0
      exact mul_le_mul_of_nonneg_left hP (by linarith)
    have h2 : c * (t * (2 + 2.59 * u)) * (log π + L / 2 - log L) =
        c * t * L - 2 * c * t * (log L - log π) + 2.59 * c * (t * u) * (log π + L / 2 - log L) := by
      ring
    have h3 : 2.59 * c * (t * u) * (log π + L / 2 - log L) ≤ 0.525 * L ^ 2 := by
      rw [htu]
      have hcc : c * c ≤ 0.40529 := by
        have := mul_le_mul hc2 hc2 (by linarith) (by norm_num); linarith
      have hm : (t * u) * (log π + L / 2 - log L) ≤ c * L * (L / 2) := by
        rw [htu]; exact mul_le_mul_of_nonneg_left hAL (by positivity)
      calc 2.59 * c * (c * L) * (log π + L / 2 - log L)
          = 2.59 * c * ((c * L) * (log π + L / 2 - log L)) := by ring
        _ ≤ 2.59 * c * (c * L * (L / 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hAL (by positivity)
        _ = 1.295 * (c * c) * L ^ 2 := by ring
        _ ≤ 1.295 * 0.40529 * L ^ 2 := by gcongr
        _ ≤ 0.525 * L ^ 2 := by nlinarith [sq_nonneg L]
    linarith
  have hcube : (x + hD x) ^ (1 / 3 : ℝ) ≤ 0.162 * t := by
    have hle : x + hD x ≤ (0.162 * t) ^ (3 : ℕ) := by
      rw [hh, ← ht2]; nlinarith [mul_nonneg ht0.le ht0.le]
    calc (x + hD x) ^ (1 / 3 : ℝ) ≤ ((0.162 * t) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) :=
          rpow_le_rpow (by rw [hh]; positivity) hle (by norm_num)
      _ = 0.162 * t := by
          rw [← rpow_natCast, ← rpow_mul (by positivity)]; norm_num
  have hlast : 48 / (5 * hD x) ≤ 0.006 := by
    rw [hh, div_le_iff₀ (by positivity)]
    have : (1700 : ℝ) ≤ u * x := by
      rw [← hh, hhD]
      have k1 : (0.6366 : ℝ) * 254 ≤ c * t := mul_le_mul hc1 ht (by norm_num) (by linarith)
      have k2 : (0.6366 : ℝ) * 254 * 11.07 ≤ c * t * L :=
        mul_le_mul k1 hL (by norm_num) (by positivity)
      linarith
    nlinarith
  have hmain : 2 * c * t * (log L - log π) ≥ 1.598 * t := by
    have h1 : 1.2552 ≤ log L - log π := by linarith
    have k : (0.6366 : ℝ) * 1.2552 ≤ c * (log L - log π) :=
      mul_le_mul hc1 h1 (by norm_num) (by linarith)
    have k2 := mul_le_mul_of_nonneg_left k ht0.le
    have e : 2 * c * t * (log L - log π) = 2 * (t * (c * (log L - log π))) := by ring
    rw [e]; nlinarith
  have hsq1 : √(x + hD x) ≤ t * (1 + u / 2) := by
    rw [hsp]; exact mul_le_mul_of_nonneg_left hs2 ht0.le
  have hsq2 : t * (1 - u) ≤ √(x - hD x) := by
    rw [hsm]; exact mul_le_mul_of_nonneg_left hs1 ht0.le
  have hLlin : L ≤ 0.0813 * t := by
    have := (div_le_iff₀ ht0).1 hLt'; linarith
  have htu' : t * u ≤ 0.63662 * L := by rw [htu]; nlinarith
  unfold rhs
  rw [← hc]
  nlinarith [hPA, hsq1, hsq2, hcube, hlast, hmain, hL2, hLlin, htu', hhD]

/-! ### From the display to Theorem 2 for `X ≥ 66799` -/

/-- Cited, page 6, derived in the paper from RH, Lemma 5, Trudgian's `N(T)`, Skewes' Lemma 1 (ii)
and Schoenfeld's `ψ - θ` bounds: `Σ_{x-h<p≤x+h} log p > rhs x` for `x ≥ 65000`. -/
def Display22 : Prop :=
  ∀ x : ℝ, 65000 ≤ x →
    rhs x < ∑ p ∈ (Finset.Ioc ⌊x - hD x⌋₊ ⌊x + hD x⌋₊).filter Nat.Prime, Real.log p

theorem hD_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ hD x := by
  unfold hD
  have := pi_pos
  have := log_nonneg hx
  positivity

/-- A prime in `(x - h, x + h]` for every `x ≥ 65000`, CONDITIONAL ON `Display22`. -/
theorem prime_near (hd : Display22) {x : ℝ} (hx : 65000 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x - hD x < p ∧ (p : ℝ) ≤ x + hD x := by
  have h := lt_trans (rhs_pos hx) (hd x hx)
  obtain ⟨p, hp⟩ : ((Finset.Ioc ⌊x - hD x⌋₊ ⌊x + hD x⌋₊).filter Nat.Prime).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    rw [he, Finset.sum_empty] at h
    exact lt_irrefl _ h
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨h1, h2⟩, hpp⟩ := hp
  have hh0 := hD_nonneg (x := x) (by linarith)
  refine ⟨p, hpp, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (x - hD x)
    have : ((⌊x - hD x⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast h1
    push_cast at this
    linarith
  · have := Nat.floor_le (show 0 ≤ x + hD x by linarith)
    have : (p : ℝ) ≤ ⌊x + hD x⌋₊ := by exact_mod_cast h2
    linarith

theorem hD_65000 : 65000 + hD 65000 ≤ 66799 := by
  unfold hD
  obtain ⟨-, hc2⟩ := pi_bounds
  have hs : √(65000 : ℝ) ≤ 254.96 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have hl : log (65000 : ℝ) ≤ 11.0822 := by
    have e : log (65000 : ℝ) = 16 * log 2 - log (1 + (65000 / 536 : ℝ)⁻¹) := by
      rw [show (1 : ℝ) + (65000 / 536 : ℝ)⁻¹ = 65536 / 65000 by norm_num,
        log_div (by norm_num) (by norm_num), show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow]
      push_cast; ring
    have h1 := LeanLab.ChenExplicit.Gamma.log_one_add_inv_ge (a := (65000 / 536 : ℝ))
      (by norm_num)
    have := log_two_lt_d9
    norm_num at h1
    rw [e]; linarith
  have hl0 : 0 ≤ log (65000 : ℝ) := log_nonneg (by norm_num)
  have hs0 : 0 ≤ √(65000 : ℝ) := sqrt_nonneg _
  have : 2 / π * √(65000 : ℝ) * log 65000 ≤ 0.63662 * 254.96 * 11.0822 := by
    apply mul_le_mul (mul_le_mul hc2 hs hs0 (by norm_num)) hl hl0 (by norm_num)
  linarith

/-- **Theorem 2 for `X ≥ 66799`, CONDITIONAL ON `Display22` only**: a prime in
`(X - (4/π) √X log X, X]`. The shift `x ↦ x + h(x)` is onto `[66799, ∞)` by the intermediate
value theorem, and `2 h(x) ≤ (4/π) √X log X` for `x ≤ X`. This is the lab's `theorem2_large`
with RH replaced by the one display it is used for. -/
theorem theorem2_large_of (hd : Display22) {X : ℝ} (hX : 66799 ≤ X) :
    PrimeInDudekInterval X := by
  set g : ℝ → ℝ := fun x => x + hD x with hg
  have hcont : ContinuousOn g (Set.Icc 65000 X) := by
    apply ContinuousOn.add continuousOn_id
    unfold hD
    apply ContinuousOn.mul (continuousOn_const.mul continuous_sqrt.continuousOn)
    exact continuousOn_log.mono (fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; have := hy.1; intro h; linarith)
  have hga : g 65000 ≤ X := by simp only [hg]; linarith [hD_65000]
  have hgb : X ≤ g X := by simp only [hg]; linarith [hD_nonneg (x := X) (by linarith)]
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc (by linarith) hcont ⟨hga, hgb⟩
  simp only [hg] at hgx
  obtain ⟨p, hp, hlo, hhi⟩ := prime_near hd hx.1
  refine ⟨p, hp, ?_, by linarith⟩
  have hxX : x ≤ X := hx.2
  have hmono : 2 * hD x ≤ dudekH X := by
    unfold hD dudekH
    have hπ := pi_pos
    have h1 : √x ≤ √X := sqrt_le_sqrt hxX
    have h2 : log x ≤ log X := log_le_log (by linarith [hx.1]) hxX
    have h3 : 0 ≤ log x := log_nonneg (by linarith [hx.1])
    have h4 : 0 ≤ √x := sqrt_nonneg _
    have : √x * log x ≤ √X * log X := mul_le_mul h1 h2 h3 (sqrt_nonneg _)
    have e1 : 2 * (2 / π * √x * log x) = 4 / π * (√x * log x) := by ring
    have e2 : 4 / π * √X * log X = 4 / π * (√X * log X) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  linarith

end

end LeanLab.Dudek2014.Section22

