module

public import Mathlib
public import LeanLab.ChebyshevExplicit.Psi30Upper

/-!
# Explicit unconditional bounds for `ψ(y) - θ(y)`

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel. Known mathematics.

The lab cites Schoenfeld 1976 Theorem 14 and (5.5) as `Dudek2014.Section22.Schoenfeld`:
`0.98 √y < ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}` for `y ≥ 121`. This file proves, with no cited
input, from Mathlib's Costa Pereira inequality
`ψ(y) - θ(y) ≤ ψ(y^{1/2}) + ψ(y^{1/3}) + ψ(y^{1/5})` and the lab's Chebyshev bounds
`ψ(n) ≤ 1.1062 n + 2 log² n + 160`, `ψ(n) ≥ 0.9212 n - 5 log n`:
* `psi_sub_theta_le_explicit`: `ψ(y) - θ(y) ≤ 1.1062 (√y + y^{1/3} + y^{1/5}) + (361/450) log² y + 480`
  for every `y ≥ 1`;
* `psi_sub_theta_lt_schoenfeld`: the upper half of the cited bound,
  `ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}`, for every `y ≥ 10^8`;
* `psi_sub_theta_lt_125`: `ψ(y) - θ(y) < 1.25 √y` for `y ≥ 10^8`, so the Rosser Schoenfeld 1962
  constant `1.42620` holds there;
* `psi_sub_theta_ge_09`: `ψ(y) - θ(y) ≥ 0.9 √y` for `y ≥ 10^8`.
The lower half with `0.98` is not reachable this way: it needs `θ(t) ≥ 0.98 t - O(t^{2/3})` for all
large `t`, beyond Chebyshev's `0.9212`. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Common.PsiTheta

open Real Chebyshev

/-- `ψ(y) ≤ 1.1062 y + 2 log² y + 160` for real `y ≥ 1`, from `psi_le_11062`. -/
lemma psi_le_real {y : ℝ} (hy : 1 ≤ y) : ψ y ≤ 1.1062 * y + 2 * log y ^ 2 + 160 := by
  rw [psi_eq_psi_coe_floor]
  have h := LeanLab.ChebyshevExplicit.psi_le_11062 ⌊y⌋₊
  have hf : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hf1 : (1 : ℝ) ≤ ⌊y⌋₊ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0; rw [Nat.floor_eq_zero] at h0; linarith)
  have hl : log ⌊y⌋₊ ≤ log y := Real.log_le_log (by linarith) hf
  have hl0 : 0 ≤ log (⌊y⌋₊ : ℝ) := Real.log_nonneg hf1
  have : log (⌊y⌋₊ : ℝ) ^ 2 ≤ log y ^ 2 := by gcongr
  linarith

/-- `log u ≤ u / e` for `u > 0`. -/
lemma log_le_div_e {u : ℝ} (hu : 0 < u) : log u ≤ u / exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu (exp_pos 1))
  rw [Real.log_div hu.ne' (exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- `log y ≤ k log 2` when `y ≤ 2^k`. -/
lemma log_le_of_le_two_pow {y : ℝ} (hy : 0 < y) (k : ℕ) (h : y ≤ 2 ^ k) :
    log y ≤ k * 0.6931471808 := by
  have h1 := Real.log_le_log hy h
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  have : (0 : ℝ) ≤ k := by positivity
  nlinarith

/-- `(y^{1/n})^n = y` for `y ≥ 0`. -/
lemma rpow_inv_pow {y : ℝ} (hy : 0 ≤ y) (n : ℕ) (hn : n ≠ 0) :
    (y ^ ((n : ℝ)⁻¹)) ^ n = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy, inv_mul_cancel₀ (by exact_mod_cast hn),
    Real.rpow_one]

/-- `(y^{1/m})^k = y^{k/m}` for `y ≥ 0`. -/
lemma rpow_inv_pow' {y : ℝ} (hy : 0 ≤ y) (m k : ℕ) :
    (y ^ ((m : ℝ)⁻¹)) ^ k = y ^ ((k : ℝ) / m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; congr 1; ring

/-- **Explicit form for every `y ≥ 1`.**
`ψ(y) - θ(y) ≤ 1.1062 (√y + y^{1/3} + y^{1/5}) + (361/450) log² y + 480`. -/
theorem psi_sub_theta_le_explicit {y : ℝ} (hy : 1 ≤ y) :
    ψ y - θ y ≤ 1.1062 * (√y + y ^ (1 / 3 : ℝ) + y ^ (1 / 5 : ℝ)) +
      361 / 450 * log y ^ 2 + 480 := by
  have hy0 : 0 < y := by linarith
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi y
  have e2 : y ^ (2 : ℝ)⁻¹ = √y := by rw [Real.sqrt_eq_rpow]; norm_num
  have e3 : y ^ (3 : ℝ)⁻¹ = y ^ (1 / 3 : ℝ) := by norm_num
  have e5 : y ^ (5 : ℝ)⁻¹ = y ^ (1 / 5 : ℝ) := by norm_num
  rw [e2, e3, e5] at hCP
  have ha1 : 1 ≤ √y := by rw [Real.le_sqrt (by norm_num) hy0.le]; linarith
  have hb1 : 1 ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy (by norm_num)
  have hc1 : 1 ≤ y ^ (1 / 5 : ℝ) := Real.one_le_rpow hy (by norm_num)
  have pa := psi_le_real ha1
  have pb := psi_le_real hb1
  have pc := psi_le_real hc1
  have la : log √y = log y / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hy0]; ring
  have lb : log (y ^ (1 / 3 : ℝ)) = log y / 3 := by rw [Real.log_rpow hy0]; ring
  have lc : log (y ^ (1 / 5 : ℝ)) = log y / 5 := by rw [Real.log_rpow hy0]; ring
  rw [la] at pa; rw [lb] at pb; rw [lc] at pc
  nlinarith

/-- The arithmetic that closes the upper half once `a = √y`, `b = y^{1/3}`, `c = y^{1/5}`,
`L = log y` are bounded. -/
lemma close_upper {a b c L : ℝ} (h : 0.0038 * a + 1.8938 * b > 1.1062 * c + 361 / 450 * L ^ 2 + 480) :
    1.1062 * (a + b + c) + 361 / 450 * L ^ 2 + 480 < 1.11 * a + 3 * b := by
  linarith

/-- **Upper half of the cited Schoenfeld bound, unconditional, for `y ≥ 10^8`.**
`ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}`. -/
theorem psi_sub_theta_lt_schoenfeld {y : ℝ} (hy : 10 ^ 8 ≤ y) :
    ψ y - θ y < 1.11 * √y + 3 * y ^ (1 / 3 : ℝ) := by
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  refine lt_of_le_of_lt (psi_sub_theta_le_explicit hy1) ?_
  set a := √y with ha
  set b := y ^ (1 / 3 : ℝ) with hb
  set c := y ^ (1 / 5 : ℝ) with hc
  set L := log y with hL
  have ha0 : 0 ≤ a := Real.sqrt_nonneg y
  have hb0 : 0 ≤ b := Real.rpow_nonneg hy0.le _
  have hc0 : 0 ≤ c := Real.rpow_nonneg hy0.le _
  have hL0 : 0 ≤ L := Real.log_nonneg hy1
  have ha2 : a ^ 2 = y := Real.sq_sqrt hy0.le
  have hb3 : b ^ 3 = y := by
    have := rpow_inv_pow hy0.le 3 (by norm_num); rw [hb]; norm_num at this ⊢; exact this
  have hc5 : c ^ 5 = y := by
    have := rpow_inv_pow hy0.le 5 (by norm_num); rw [hc]; norm_num at this ⊢; exact this
  rcases le_or_gt y (3 * 10 ^ 8) with h1 | h1
  · -- `[10^8, 3 · 10^8]`
    have hA : 10 ^ 4 ≤ a := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) ha0 (by nlinarith)
    have hB : 464 ≤ b := le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hb0 (by nlinarith)
    have hC : c ≤ 50 := le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by norm_num) (by nlinarith)
    have hLb : L ≤ 29 * 0.6931471808 := by
      have := log_le_of_le_two_pow hy0 29 (by norm_num; linarith); push_cast at this; linarith
    apply close_upper
    nlinarith
  rcases le_or_gt y (10 ^ 10) with h2 | h2
  · -- `[3 · 10^8, 10^10]`
    have hA : 17320 ≤ a := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) ha0 (by nlinarith)
    have hB : 669 ≤ b := le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hb0 (by nlinarith)
    have hC : c ≤ 100 := le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by norm_num) (by nlinarith)
    have hLb : L ≤ 34 * 0.6931471808 := by
      have := log_le_of_le_two_pow hy0 34 (by norm_num; linarith); push_cast at this; linarith
    apply close_upper
    nlinarith
  · -- `y ≥ 10^10`, with `z = y^{1/12}`, `a = z^6`, `b = z^4`, `c ≤ b`, `L ≤ 12 z / e`
    set z := y ^ ((12 : ℕ) : ℝ)⁻¹ with hz
    have hz0 : 0 < z := Real.rpow_pos_of_pos hy0 _
    have hz12 : z ^ 12 = y := rpow_inv_pow hy0.le 12 (by norm_num)
    have haz : a = z ^ 6 := by
      rw [hz, rpow_inv_pow' hy0.le, ha, Real.sqrt_eq_rpow]; norm_num
    have hbz : b = z ^ 4 := by
      rw [hz, rpow_inv_pow' hy0.le, hb]; norm_num
    have hcb : c ≤ b := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    have hLz : L = 12 * log z := by
      rw [hL, ← hz12, Real.log_pow]; push_cast; ring
    have hlz := log_le_div_e hz0
    have he := Real.exp_one_gt_d9
    have hLz' : L ≤ 4.4151 * z := by
      rw [hLz]
      have h1 : z / exp 1 ≤ z / 2.7182818283 :=
        div_le_div_of_nonneg_left hz0.le (by norm_num) he.le
      have h2 : z / 2.7182818283 ≤ 0.36788 * z := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    have hz68 : 6.8 ≤ z := le_of_pow_le_pow_left₀ (n := 12) (by norm_num) hz0.le (by nlinarith)
    set w := z ^ 2 with hw
    have hw46 : 46.24 ≤ w := by rw [hw]; nlinarith
    have hL2 : L ^ 2 ≤ 19.4932 * w := by rw [hw]; nlinarith
    have h4 : z ^ 4 = w ^ 2 := by rw [hw]; ring
    have h6 : z ^ 6 = w ^ 3 := by rw [hw]; ring
    have : 1.1062 * (a + b + c) + 361 / 450 * L ^ 2 + 480 ≤
        1.1062 * w ^ 3 + 2.2124 * w ^ 2 + 361 / 450 * (19.4932 * w) + 480 := by
      rw [haz, hbz, h4, h6] at *; nlinarith
    have hpos : 1.1062 * w ^ 3 + 2.2124 * w ^ 2 + 361 / 450 * (19.4932 * w) + 480 <
        1.11 * w ^ 3 + 3 * w ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hw46) (sub_nonneg.mpr hw46),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hw46) (sub_nonneg.mpr hw46)) (sub_nonneg.mpr hw46)]
    rw [haz, hbz, h4, h6]
    rw [haz, hbz, h4, h6] at this
    linarith

/-- **`ψ(y) - θ(y) < 1.25 √y` for `y ≥ 10^8`**, unconditional. -/
theorem psi_sub_theta_lt_125 {y : ℝ} (hy : 10 ^ 8 ≤ y) : ψ y - θ y < 1.25 * √y := by
  have hy0 : 0 < y := by linarith
  have h := psi_sub_theta_lt_schoenfeld hy
  set z := y ^ ((6 : ℕ) : ℝ)⁻¹ with hz
  have hz0 : 0 < z := Real.rpow_pos_of_pos hy0 _
  have hz6 : z ^ 6 = y := rpow_inv_pow hy0.le 6 (by norm_num)
  have haz : √y = z ^ 3 := by
    rw [hz, rpow_inv_pow' hy0.le, Real.sqrt_eq_rpow]; norm_num
  have hbz : y ^ (1 / 3 : ℝ) = z ^ 2 := by
    rw [hz, rpow_inv_pow' hy0.le]; norm_num
  have hz21 : 21.5 ≤ z := le_of_pow_le_pow_left₀ (n := 6) (by norm_num) hz0.le (by nlinarith)
  rw [haz, hbz] at h
  rw [haz]
  nlinarith [sq_nonneg z]

/-- The Rosser Schoenfeld 1962 constant on `y ≥ 10^8`: `ψ(y) - θ(y) < 1.42620 √y`. -/
theorem psi_sub_theta_lt_rosser_schoenfeld {y : ℝ} (hy : 10 ^ 8 ≤ y) :
    ψ y - θ y < 1.42620 * √y := by
  have := psi_sub_theta_lt_125 hy
  have : 0 ≤ √y := Real.sqrt_nonneg y
  linarith

/-- `log t ≤ 4 t^{1/4} / e` for `t > 0`. -/
lemma log_le_four_root {t : ℝ} (ht : 0 < t) :
    log t ≤ 4 * t ^ ((4 : ℕ) : ℝ)⁻¹ / exp 1 := by
  have hu : 0 < t ^ ((4 : ℕ) : ℝ)⁻¹ := Real.rpow_pos_of_pos ht _
  have h4 := rpow_inv_pow ht.le 4 (by norm_num)
  have hl : log t = 4 * log (t ^ ((4 : ℕ) : ℝ)⁻¹) := by
    conv_lhs => rw [← h4]
    rw [Real.log_pow]; push_cast; ring
  rw [hl, mul_div_assoc]
  have := log_le_div_e hu
  linarith

/-- **Lower bound, unconditional: `ψ(y) - θ(y) ≥ 0.9 √y` for `y ≥ 10^8`.** -/
theorem psi_sub_theta_ge_09 {y : ℝ} (hy : 10 ^ 8 ≤ y) : 0.9 * √y ≤ ψ y - θ y := by
  have hy0 : 0 < y := by linarith
  have hCP := psi_sub_theta_ge_psi_add_psi_add_psi hy0.le
  have e2 : y ^ (2 : ℝ)⁻¹ = √y := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [e2] at hCP
  have h3 := psi_nonneg (y ^ (3 : ℝ)⁻¹)
  have h7 := psi_nonneg (y ^ (7 : ℝ)⁻¹)
  set t := √y with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg y
  have ht4 : 10 ^ 4 ≤ t := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) ht0
    (by rw [ht, Real.sq_sqrt hy0.le]; linarith)
  set n := ⌊t⌋₊ with hn
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
  have hnt' : t < n + 1 := Nat.lt_floor_add_one t
  have hn30 : 30 ≤ n := by
    have : (30 : ℝ) < n + 1 := by linarith
    have : (29 : ℝ) < n := by linarith
    exact_mod_cast this
  have hpsi := LeanLab.ChebyshevExplicit.psi_ge_09212 n hn30
  rw [← psi_eq_psi_coe_floor] at hpsi
  have hn30' : (30 : ℝ) ≤ n := by exact_mod_cast hn30
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : log n ≤ log t := Real.log_le_log hn0 hnt
  have ht0' : 0 < t := by linarith
  have hl4 := log_le_four_root ht0'
  set u := t ^ ((4 : ℕ) : ℝ)⁻¹ with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht0' _
  have hu4 : u ^ 4 = t := rpow_inv_pow ht0'.le 4 (by norm_num)
  have hu10 : 10 ≤ u := le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hu0.le (by nlinarith)
  have he := Real.exp_one_gt_d9
  have hlu : log t ≤ 1.4716 * u := by
    have : 4 * u / exp 1 ≤ 4 * u / 2.7182818283 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) he.le
    have h2 : 4 * u / 2.7182818283 ≤ 1.4716 * u := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  -- `0.9212 (t - 1) - 5 · 1.4716 u ≥ 0.9 t` since `t = u^4`, `u ≥ 10`
  have key : 0.9 * t ≤ 0.9212 * (t - 1) - 5 * (1.4716 * u) := by
    rw [← hu4]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu10) (sub_nonneg.mpr hu10),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hu10) (sub_nonneg.mpr hu10)) (sub_nonneg.mpr hu10)]
  linarith

end LeanLab.Common.PsiTheta
