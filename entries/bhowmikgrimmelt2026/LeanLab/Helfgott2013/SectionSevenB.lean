module

public import Mathlib
public import LeanLab.Helfgott2013.SectionSeven

/-!
P0001 H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2,
Section 7.3, pages 64 to 69: printed constants of (7.32) to (7.45), the bound for
`∫_{r₀}^{r₁} g(r)/r dr`. Only the arithmetic between displayed numbers is checked; the
values R, z, I₁, cϕ, the bisection results and VNODE-LP integrals are the paper's.

AI-written Lean code, Claude, 2026-10-18, cloud session 20261018T1720Z-cloud5.
Checked only by the Lean kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Helfgott2013
open Real

set_option exponentiation.threshold 5000 in
/-- `log 3 < (4701/2966) log 2`, from `3^2966 < 2^4701`. -/
theorem log_three_lt_ratio : Real.log 3 < 4701 / 2966 * Real.log 2 := by
  have hn : (3 : ℕ) ^ 2966 < 2 ^ 4701 := by norm_num
  have h : (3 : ℝ) ^ 2966 < 2 ^ 4701 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  linarith

/-- `log (2r₀) = log 300000 = log 3 + 5 log 10 < 12.61154`. -/
theorem log_300000_lt : Real.log 300000 < 12.61154 := by
  have e : Real.log 300000 = Real.log 3 + 5 * Real.log 10 := by
    rw [show (300000 : ℝ) = 3 * 10 ^ 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have := log_three_lt_ratio
  have := log_ten_lt_ratio
  have := Real.log_two_lt_d9
  rw [e]; linarith

/-- `log 800000 = 3 log 2 + 5 log 10 < 13.592369`. -/
theorem log_800000_lt : Real.log 800000 < 13.592369 := by
  have e : Real.log 800000 = 3 * Real.log 2 + 5 * Real.log 10 := by
    rw [show (800000 : ℝ) = 2 ^ 3 * 10 ^ 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have := log_ten_lt_ratio
  have := Real.log_two_lt_d9
  rw [e]; linarith

/-- (7.32) with (7.33), (7.34): `(0.07455/3.35976) 0.60295 + (1 − 0.07455/3.35976) 0.58341 ≤
0.58385`. MATCHES, value 0.5838436. -/
theorem mix_r0 : (0.07455 / 3.35976 : ℝ) * 0.60295 + (1 - 0.07455 / 3.35976) * 0.58341 ≤ 0.58385 := by
  norm_num

/-- (7.32) with (7.36), (7.39): `(0.07455/3.35976) 0.71392 + (1 − 0.07455/3.35976) 0.71215 ≤
0.71219`. MATCHES, value 0.7121893. -/
theorem mix_r1 : (0.07455 / 3.35976 : ℝ) * 0.71392 + (1 - 0.07455 / 3.35976) * 0.71215 ≤ 0.71219 := by
  norm_num

/-- `P₂(t) = t² + 4t + 8`, `P₂⁻(t) = 2t² + 16t + 48`. -/
def P2 (t : ℝ) : ℝ := t ^ 2 + 4 * t + 8
def P2m (t : ℝ) : ℝ := 2 * t ^ 2 + 16 * t + 48

theorem P2_le : P2 (Real.log 300000) ≤ P2 12.61154 := by
  have h := log_300000_lt
  have h0 : 0 ≤ Real.log 300000 := Real.log_nonneg (by norm_num)
  unfold P2; nlinarith

theorem P2m_le : P2m (Real.log 300000) ≤ P2m 12.61154 := by
  have h := log_300000_lt
  have h0 : 0 ≤ Real.log 300000 := Real.log_nonneg (by norm_num)
  unfold P2m; nlinarith

/-- The constants of the bound for `I_{0,r₀,r₁,z}`, `r₀ = 150000`: for `z = y`,
`0.58341² P₂(log 2r₀)/√r₀ ≤ 0.19115` and `(0.71215² − 0.41415²) P₂⁻(log 2r₀)/√r₀ ≤ 0.49214`;
for `z = y/K`, `0.60295² P₂/√r₀ ≤ 0.20416` and `(0.71392² − 0.41415²) P₂⁻/√r₀ ≤ 0.49584`.
MATCHES, values 0.1911418, 0.4921373, 0.2041599, 0.4958384. -/
theorem I0_consts :
    0.58341 ^ 2 * P2 (Real.log 300000) / Real.sqrt 150000 ≤ (0.19115 : ℝ) ∧
    (0.71215 ^ 2 - 0.41415 ^ 2) * P2m (Real.log 300000) / Real.sqrt 150000 ≤ (0.49214 : ℝ) ∧
    0.60295 ^ 2 * P2 (Real.log 300000) / Real.sqrt 150000 ≤ (0.20416 : ℝ) ∧
    (0.71392 ^ 2 - 0.41415 ^ 2) * P2m (Real.log 300000) / Real.sqrt 150000 ≤ (0.49584 : ℝ) := by
  have hs : (387.2983 : ℝ) ≤ Real.sqrt 150000 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs0 : (0 : ℝ) < Real.sqrt 150000 := by linarith
  have h1 := P2_le
  have h2 := P2m_le
  have hp1 : 0 ≤ P2 (Real.log 300000) := by unfold P2; nlinarith [sq_nonneg (Real.log 300000 + 2)]
  have hp2 : 0 ≤ P2m (Real.log 300000) := by
    unfold P2m; nlinarith [sq_nonneg (Real.log 300000 + 4)]
  have k : ∀ c P Pmax target : ℝ, 0 ≤ c → 0 ≤ P → P ≤ Pmax → c * Pmax ≤ target * 387.2983 →
      0 ≤ target → c * P / Real.sqrt 150000 ≤ target := by
    intro c P Pmax target hc hP hPm h ht
    rw [div_le_iff₀ hs0]
    nlinarith [mul_le_mul_of_nonneg_left hPm hc]
  refine ⟨k _ _ _ _ (by norm_num) hp1 h1 ?_ (by norm_num), k _ _ _ _ (by norm_num) hp2 h2 ?_
    (by norm_num), k _ _ _ _ (by norm_num) hp1 h1 ?_ (by norm_num),
    k _ _ _ _ (by norm_num) hp2 h2 ?_ (by norm_num)⟩ <;> simp only [P2, P2m] <;> norm_num

/-- The common shape of (7.43) and (7.44):
`(1 − cϕ) √(a + 0.49214/D) + cϕ √(b + 0.49584/D)` with `cϕ = 0.02219`, `D = (4/15) log y − log 800000`. -/
noncomputable def Ishape (a b D : ℝ) : ℝ :=
  0.97781 * Real.sqrt (a + 0.49214 / D) + 0.02219 * Real.sqrt (b + 0.49584 / D)

theorem Ishape_anti {a b D D0 : ℝ} (hD0 : 0 < D0) (hD : D0 ≤ D) :
    Ishape a b D ≤ Ishape a b D0 := by
  unfold Ishape
  have h1 : 0.49214 / D ≤ 0.49214 / D0 := div_le_div_of_nonneg_left (by norm_num) hD0 hD
  have h2 : 0.49584 / D ≤ 0.49584 / D0 := div_le_div_of_nonneg_left (by norm_num) hD0 hD
  have := Real.sqrt_le_sqrt (by linarith : a + 0.49214 / D ≤ a + 0.49214 / D0)
  have := Real.sqrt_le_sqrt (by linarith : b + 0.49584 / D ≤ b + 0.49584 / D0)
  linarith

/-- `D ≥ 1.75819` for `y ≥ 10^25`. -/
theorem D_ge_25 {y : ℝ} (hy : 1e25 ≤ y) : (1.75819 : ℝ) ≤ 4 / 15 * Real.log y - Real.log 800000 := by
  have h1 : Real.log 1e25 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have e : Real.log (1e25 : ℝ) = 25 * Real.log 10 := by
    rw [show (1e25 : ℝ) = 10 ^ 25 by norm_num, Real.log_pow]; push_cast; ring
  have := log_ten_gt_ratio
  have := Real.log_two_gt_d9
  have := log_800000_lt
  linarith

/-- `D ≥ 78.5` for `y ≥ 10^150`. -/
theorem D_ge_150 {y : ℝ} (hy : 1e150 ≤ y) : (78.5 : ℝ) ≤ 4 / 15 * Real.log y - Real.log 800000 := by
  have h1 : Real.log 1e150 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have e : Real.log (1e150 : ℝ) = 150 * Real.log 10 := by
    rw [show (1e150 : ℝ) = 10 ^ 150 by norm_num, Real.log_pow]; push_cast; ring
  have := log_ten_gt_ratio
  have := Real.log_two_gt_d9
  have := log_800000_lt
  linarith

/-- (7.43) at `y ≥ 10^25`: `≤ 0.68659`. MATCHES, value 0.6865814 at `y = 10^25`. -/
theorem I743 {y : ℝ} (hy : 1e25 ≤ y) :
    Ishape 0.19115 0.20416 (4 / 15 * Real.log y - Real.log 800000) ≤ (0.68659 : ℝ) := by
  refine le_trans (Ishape_anti (by norm_num) (D_ge_25 hy)) ?_
  unfold Ishape
  have h1 : Real.sqrt (0.19115 + 0.49214 / 1.75819) ≤ (0.6863402 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : Real.sqrt (0.20416 + 0.49584 / 1.75819) ≤ (0.6972642 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- (7.44) at `y ≥ 10^150`: `≤ 0.33247`. MATCHES, value 0.3324654. -/
theorem I744 {y : ℝ} (hy : 1e150 ≤ y) :
    Ishape 0.10426 0.10439 (4 / 15 * Real.log y - Real.log 800000) ≤ (0.33247 : ℝ) := by
  refine le_trans (Ishape_anti (by norm_num) (D_ge_150 hy)) ?_
  unfold Ishape
  have h1 : Real.sqrt (0.10426 + 0.49214 / 78.5) ≤ (0.3324595 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : Real.sqrt (0.10439 + 0.49584 / 78.5) ≤ (0.3327258 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- (7.44): `0.43086² P₂(log 2r₀)/√r₀ ≤ 0.10426` and `0.43113² P₂(log 2r₀)/√r₀ ≤ 0.10439`.
MATCHES, values 0.1042510, 0.1043817. -/
theorem I744_consts :
    0.43086 ^ 2 * P2 (Real.log 300000) / Real.sqrt 150000 ≤ (0.10426 : ℝ) ∧
    0.43113 ^ 2 * P2 (Real.log 300000) / Real.sqrt 150000 ≤ (0.10439 : ℝ) := by
  have hs : (387.2983 : ℝ) ≤ Real.sqrt 150000 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs0 : (0 : ℝ) < Real.sqrt 150000 := by linarith
  have h1 := P2_le
  have hp1 : 0 ≤ P2 (Real.log 300000) := by unfold P2; nlinarith [sq_nonneg (Real.log 300000 + 2)]
  constructor <;>
  · rw [div_le_iff₀ hs0]
    have : P2 12.61154 = 12.61154 ^ 2 + 4 * 12.61154 + 8 := rfl
    nlinarith

/-- The crude bound on page 68: `0.68659 · √(2 · 5.73827/√r₀) ≤ 0.11819`. MATCHES. -/
theorem f0_crude : 0.68659 * Real.sqrt (2 * 5.73827 / Real.sqrt 150000) ≤ (0.11819 : ℝ) := by
  have hs : (387.2983 : ℝ) ≤ Real.sqrt 150000 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hq : 2 * 5.73827 / Real.sqrt 150000 ≤ (0.1721404 : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := (Real.sqrt_le_left (by norm_num)).mpr hq
  nlinarith

/-- (7.46) as printed: `0.069219 + 0.016367 + 0.001332 ≤ 0.086918` and
`1.280418 · 0.086918 ≤ 0.111292`. Both MATCH; the first input is F-5001. -/
theorem printed_746 : (0.069219 : ℝ) + 0.016367 + 0.001332 ≤ 0.086918 ∧
    (1.280418 : ℝ) * 0.086918 ≤ 0.111292 := by
  constructor <;> norm_num

end LeanLab.Helfgott2013
