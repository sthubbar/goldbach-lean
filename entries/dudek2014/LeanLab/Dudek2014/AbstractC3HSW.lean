module

public import Mathlib
public import LeanLab.Dudek2014.Theorem1HSW

/-!
P0100 Dudek 2014, arXiv 1402.6417, the abstract and Section 2.4, `c = 3 + ε` in Cramér's theorem,
and Theorem 3 of Section 2.3, unit U-6730, CLOUD 20261020T2018Z-cloud50.

Under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` bound `HSWN70 gZ` only:
* `abstract_c3_of_RH_hsw`: for every `ε > 0` and all large `x`, more than `√x` primes lie in
  `(x, x + (3 + ε)√x log x]`, the conclusion of the statement `Statements.abstract_c3_stmt`;
* `theorem3_of_RH_hsw`: for every `ε > 0` and all large `x`, a prime lies in
  `(x - (1 + ε)√x log x, x]`, the conclusion of the statement `Statements.theorem3_stmt`.
Method of Section 2.3: the refined single zero bound `num_bound`,
`|Δ² y^{ρ+1}| ≤ y^{3/2}(4 sin²(γu/2) + 4u + 4|γ|u²)` with `u = h/y`, which replaces Dudek's
`O(αh/x)` steps; the Ingham step, Dudek's integral of `log u sin²(hu/2x)/u²` by Theorem A, is
done here discretely in `fejer_sum`: the zeros are cut into blocks of length `b = 2δy/h`, each
block counted by `HSWN70`, and the block sums are compared with the exact Fourier series
`Σ sin²(nδ)/n² = (πδ - δ²)/2`, `hasSum_sin_sq`, from Mathlib's Bernoulli series; that is where
Dudek's `∫_0^∞ sin² t/t² dt = π/2` enters. The tail `|γ| > T = Kb ≈ αy/h` is the page 5 `Σ₂`
bound with `α = 64/ε`. `zero_sum_c3` collects these; Lemma 5 is the PROVED `lemma4_Zpatch`
route of Theorem1HSW.lean, and the prime powers are bounded by `Theorem1H.mass_gen`.
The constant: `Σ_{x<n≤x+2h} Λ(n) ≥ h - (1/2 + ε/24)√x log x + O(√x)`, so `2h = (3 + ε)√x log x`
leaves `(1 + 11ε/24)√x log x`, and `2h = (1 + ε)√x log x` centred at `x - h` leaves
`(11ε/24)√x log x > 0`.
The thresholds `X` are not explicit: they come from `log x = o(x^{1/4})` and depend on
`Σ_ρ 1/|ρ(ρ+1)|`. KNOWN mathematics, Dudek 2014; not claimed new.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.AbstractC3
open Real Finset
open LeanLab.Dudek2014.SigmaT (rhoF fz Zr wgt norm_rho_mul_ge norm_rho_mul_ge' wgt_nonneg
  log_ge_four)
open LeanLab.Dudek2014.SigmaT (wgt_le_inv_sq ne_of_large second_diff_large)
open LeanLab.Dudek2014.SigmaH (HSWN70 Mt_eq Rt_le Rt_nonneg summable_fz summable_wgt tail_inv_sq)
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt)
open LeanLab.Dudek2014.Section22 (WS lemma5_of)
open LeanLab.Dudek2014.Theorem1H (WS_le mass_gen split_sum prime_sum_le patch_eq primesIn_mono)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ lemma4_Zpatch)
open scoped ArithmeticFunction.vonMangoldt

/-- `Σ_{n ≥ 1} sin²(nδ)/n² = (πδ - δ²)/2` for `0 ≤ δ ≤ π`. -/
theorem hasSum_sin_sq {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ π) :
    HasSum (fun n : ℕ => Real.sin (n * δ) ^ 2 / (n : ℝ) ^ 2) ((π * δ - δ ^ 2) / 2) := by
  have hp := Real.pi_pos
  have hx : δ / π ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg h0 hp.le, (div_le_one hp).2 h1⟩
  have hc := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hz := hasSum_zeta_two
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (δ / π) =
      (δ / π) ^ 2 - δ / π + 6⁻¹ := bernoulliFun_two _
  rw [hb] at hc
  have := (hz.sub hc).div_const 2
  convert this using 1
  · funext n
    rw [Real.sin_sq_eq_half_sub]
    have : 2 * π * (n : ℝ) * (δ / π) = 2 * (n * δ) := by field_simp
    rw [this]
    ring
  · field_simp
    ring

/-- `t^{ρ+1} = t^{3/2} e^{i γ log t}` for `t > 0`. -/
theorem cpow_rho (g : ℝ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (rhoF g + 1) =
      ((t * √t : ℝ) : ℂ) * Complex.exp (((g * Real.log t : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), ← Complex.ofReal_log ht.le]
  have e : t * √t = Real.exp (Real.log t * (3 / 2)) := by
    rw [← Real.rpow_def_of_pos ht, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add ht, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [e, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [rhoF]
  push_cast
  ring

/-- `|e^{ia} - e^{ib}| ≤ |a - b|`. -/
theorem norm_eI_sub (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have e : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; push_cast; ring_nf
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  simpa using this

theorem norm_eI (a : ℝ) : ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I a

/-- `e^{iθ} + e^{-iθ} - 2 = 2 cos θ - 2`. -/
theorem eI_add_neg (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - 2 =
      ((2 * Real.cos θ - 2 : ℝ) : ℂ) := by
  push_cast
  rw [Complex.cos, show -(θ : ℂ) * Complex.I = -((θ : ℂ) * Complex.I) by ring]
  ring

/-- `|(y+h)^{3/2} - y^{3/2}| ≤ 2 h √y` and `|y^{3/2} - (y-h)^{3/2}| ≤ 2 h √y` for `0 < h ≤ y`. -/
theorem pow32_diff {y h : ℝ} (hy : 0 < y) (hh : 0 < h) (hhy : h ≤ y) :
    |(y + h) * √(y + h) - y * √y| ≤ 2 * h * √y ∧ |(y - h) * √(y - h) - y * √y| ≤ 2 * h * √y := by
  set s := √y with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hy
  have hs2 : s ^ 2 = y := Real.sq_sqrt hy.le
  set r := √(y + h)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = y + h := Real.sq_sqrt (by linarith)
  set q := √(y - h)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = y - h := Real.sq_sqrt (by linarith)
  have hrs : s ≤ r := Real.sqrt_le_sqrt (by linarith)
  have hqs : q ≤ s := Real.sqrt_le_sqrt (by linarith)
  constructor
  · rw [abs_le]; constructor
    · nlinarith
    · -- 2 r s ≤ 2 s² + h
      have h1 : 2 * r * s ≤ 2 * s ^ 2 + h := by nlinarith [sq_nonneg (r - s)]
      have h2 : h ^ 2 ≤ h * s ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ s ^ 2 + h by positivity)]
  · rw [abs_le]; constructor
    · -- q ≥ s - h/s, i.e. q s ≥ s² - h
      have h1 : s ^ 2 - h ≤ q * s := by
        by_contra hc
        push Not at hc
        have : (q * s) ^ 2 < (s ^ 2 - h) ^ 2 := by
          have : 0 ≤ q * s := by positivity
          nlinarith
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ s ^ 2 - h by nlinarith)]
    · nlinarith [mul_le_mul hqs hqs hq0 hs0.le]

/-- `|log(1 ± u) ∓ u| ≤ 2u²` for `0 ≤ u ≤ 1/2`. -/
theorem log_one_add_sub {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ 2 * u ^ 2 ∧ |Real.log (1 - u) + u| ≤ 2 * u ^ 2 := by
  have hb : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg u]
  have a := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; linarith) 1
  have b := Real.abs_log_sub_add_sum_range_le (x := u) (by rw [abs_of_nonneg h0]; linarith) 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, abs_neg,
    abs_of_nonneg h0, sub_neg_eq_add] at a b
  constructor
  · rw [show Real.log (1 + u) - u = -u + Real.log (1 + u) by ring]; linarith
  · rw [show Real.log (1 - u) + u = u + Real.log (1 - u) by ring]; linarith

/-- **The refined single zero bound** of Section 2.3: with `u = h/y`,
`|(y+h)^{ρ+1} - 2y^{ρ+1} + (y-h)^{ρ+1}| ≤ y^{3/2} (4 sin²(γu/2) + 4u + 4|γ|u²)` for `2h ≤ y`. -/
theorem num_bound (g : ℝ) {y h : ℝ} (hy : 0 < y) (hh : 0 < h) (h2 : 2 * h ≤ y) :
    ‖((y + h : ℝ) : ℂ) ^ (rhoF g + 1) - 2 * ((y : ℝ) : ℂ) ^ (rhoF g + 1) +
        ((y - h : ℝ) : ℂ) ^ (rhoF g + 1)‖ ≤
      y * √y * (4 * Real.sin (g * (h / y) / 2) ^ 2 + 4 * (h / y) + 4 * |g| * (h / y) ^ 2) := by
  have hyh : 0 < y - h := by linarith
  rw [cpow_rho g (by linarith), cpow_rho g hy, cpow_rho g hyh]
  set u := h / y with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 2 := by rw [hu, div_le_iff₀ hy]; linarith
  set e : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * Complex.I) with he
  set pP := (y + h) * √(y + h)
  set p := y * √y
  set pM := (y - h) * √(y - h)
  set φP := g * Real.log (y + h)
  set φ := g * Real.log y
  set φM := g * Real.log (y - h)
  have hp0 : 0 ≤ p := by positivity
  have hadd : ∀ a b : ℝ, e (a + b) = e a * e b := fun a b => by
    simp only [he]; rw [← Complex.exp_add]; push_cast; ring_nf
  have key : (pP : ℂ) * e φP - 2 * ((p : ℂ) * e φ) + (pM : ℂ) * e φM =
      ((pP - p : ℝ) : ℂ) * e φP + (p : ℂ) * (e φP - e (φ + g * u)) +
      (((pM - p : ℝ) : ℂ) * e φM + (p : ℂ) * (e φM - e (φ + -(g * u)))) +
      (p : ℂ) * e φ * (e (g * u) + e (-(g * u)) - 2) := by
    rw [hadd φ (g * u), hadd φ (-(g * u))]; push_cast; ring
  change ‖(pP : ℂ) * e φP - 2 * ((p : ℂ) * e φ) + (pM : ℂ) * e φM‖ ≤ _
  rw [key]
  have hcos := eI_add_neg (g * u)
  have hn1 : ‖((pP - p : ℝ) : ℂ) * e φP‖ ≤ 2 * h * √y := by
    rw [norm_mul, he]; simp only [norm_eI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact (pow32_diff hy hh (by linarith)).1
  have hn3 : ‖((pM - p : ℝ) : ℂ) * e φM‖ ≤ 2 * h * √y := by
    rw [norm_mul, he]; simp only [norm_eI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact (pow32_diff hy hh (by linarith)).2
  obtain ⟨l1, l2⟩ := log_one_add_sub hu0 hu1
  have e1 : Real.log (y + h) = Real.log y + Real.log (1 + u) := by
    rw [← Real.log_mul hy.ne' (by linarith)]; congr 1; rw [hu]; field_simp
  have e2 : Real.log (y - h) = Real.log y + Real.log (1 - u) := by
    rw [← Real.log_mul hy.ne' (by linarith)]; congr 1; rw [hu]; field_simp
  have hn2 : ‖(p : ℂ) * (e φP - e (φ + g * u))‖ ≤ p * (|g| * (2 * u ^ 2)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    apply mul_le_mul_of_nonneg_left _ hp0
    refine (norm_eI_sub _ _).trans ?_
    have : φP - (φ + g * u) = g * (Real.log (1 + u) - u) := by
      simp only [φP, φ]; rw [e1]; ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left l1 (abs_nonneg _)
  have hn4 : ‖(p : ℂ) * (e φM - e (φ + -(g * u)))‖ ≤ p * (|g| * (2 * u ^ 2)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    apply mul_le_mul_of_nonneg_left _ hp0
    refine (norm_eI_sub _ _).trans ?_
    have : φM - (φ + -(g * u)) = g * (Real.log (1 - u) + u) := by
      simp only [φM, φ]; rw [e2]; ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left l2 (abs_nonneg _)
  have hn5 : ‖(p : ℂ) * e φ * (e (g * u) + e (-(g * u)) - 2)‖ ≤
      p * (4 * Real.sin (g * u / 2) ^ 2) := by
    have hc : e (g * u) + e (-(g * u)) - 2 = ((2 * Real.cos (g * u) - 2 : ℝ) : ℂ) := by
      simp only [he]; rw [← hcos]
    rw [hc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0, he]
    simp only [norm_eI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ hp0
    have : Real.cos (g * u) = 1 - 2 * Real.sin (g * u / 2) ^ 2 := by
      rw [show g * u = 2 * (g * u / 2) by ring, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (g * u / 2)
      rw [show 2 * (g * u / 2) / 2 = g * u / 2 by ring]
      linarith
    rw [this]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.sin (g * u / 2))]
  have hpu : h * √y = p * u := by
    simp only [p, hu]; field_simp
  calc _ ≤ ‖((pP - p : ℝ) : ℂ) * e φP + (p : ℂ) * (e φP - e (φ + g * u)) +
          (((pM - p : ℝ) : ℂ) * e φM + (p : ℂ) * (e φM - e (φ + -(g * u))))‖ +
          ‖(p : ℂ) * e φ * (e (g * u) + e (-(g * u)) - 2)‖ := norm_add_le _ _
    _ ≤ (‖((pP - p : ℝ) : ℂ) * e φP‖ + ‖(p : ℂ) * (e φP - e (φ + g * u))‖) +
          (‖((pM - p : ℝ) : ℂ) * e φM‖ + ‖(p : ℂ) * (e φM - e (φ + -(g * u)))‖) +
          ‖(p : ℂ) * e φ * (e (g * u) + e (-(g * u)) - 2)‖ := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr <;> exact norm_add_le _ _
    _ ≤ _ := by nlinarith

/-! ### The Ingham step: the Fejér sum over the zeros, by blocks -/

theorem log_two_pi_pos : 0 < Real.log (2 * π) :=
  Real.log_pos (by linarith [Real.pi_gt_three])

theorem Mt_le {b : ℝ} (hb : 0 < b) : Mt b ≤ b * Real.log b / (2 * π) + 7 / 8 := by
  rw [Mt_eq hb]
  have := log_two_pi_pos
  have hp := Real.pi_pos
  have : b * (Real.log b - Real.log (2 * π) - 1) ≤ b * Real.log b := by nlinarith
  have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith

theorem Mt_diff {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    Mt t₂ - Mt t₁ ≤ (t₂ - t₁) * Real.log t₂ / (2 * π) := by
  have h2 : 0 < t₂ := by linarith
  rw [Mt_eq h2, Mt_eq h1]
  have hc := log_two_pi_pos
  have hp := Real.pi_pos
  have hl : Real.log t₂ - Real.log t₁ ≤ t₂ / t₁ - 1 := by
    rw [← Real.log_div h2.ne' h1.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
  have hl' : t₁ * (Real.log t₂ - Real.log t₁) ≤ t₂ - t₁ := by
    have := mul_le_mul_of_nonneg_left hl h1.le
    have e : t₁ * (t₂ / t₁ - 1) = t₂ - t₁ := by field_simp
    linarith
  rw [show t₂ * (Real.log t₂ - Real.log (2 * π) - 1) / (2 * π) + 7 / 8 -
      (t₁ * (Real.log t₁ - Real.log (2 * π) - 1) / (2 * π) + 7 / 8) =
      (t₂ * (Real.log t₂ - Real.log (2 * π) - 1) - t₁ * (Real.log t₁ - Real.log (2 * π) - 1)) /
        (2 * π) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

variable {ι : Type*}

/-- The block of a zero: `⌈|γ|/b⌉ - 1`. -/
noncomputable def blk (b : ℝ) (g : ℝ) : ℕ := ⌈|g| / b⌉₊ - 1

theorem blk_spec {b g : ℝ} (hb : 0 < b) {k : ℕ} (hk : blk b g = k) :
    (k = 0 → |g| ≤ b) ∧ (1 ≤ k → k * b < |g| ∧ |g| ≤ (k + 1) * b) := by
  unfold blk at hk
  constructor
  · intro h0
    have : ⌈|g| / b⌉₊ ≤ 1 := by omega
    have := (Nat.ceil_le).1 this
    rw [div_le_iff₀ hb] at this; simpa using this
  · intro h1
    have hc : ⌈|g| / b⌉₊ = k + 1 := by omega
    rw [Nat.ceil_eq_iff (by omega)] at hc
    simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at hc
    rw [lt_div_iff₀ hb, div_le_iff₀ hb] at hc
    exact hc

/-- The count of a block: at most `b log T/π + 2 log T + 41` for `T = K b`. -/
theorem blk_count {γ : ι → ℝ} (hN : HSWN70 γ) {b : ℝ} (hb : 70 ≤ b) {K : ℕ} (k : ℕ)
    (hk : k < K) (s : Finset ι) :
    (((s.filter (fun i => |γ i| ≤ K * b)).filter (fun i => blk b (γ i) = k)).card : ℝ) ≤
      b * Real.log (K * b) / π + 2 * Real.log (K * b) + 41 := by
  have hb0 : 0 < b := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hKb : b ≤ K * b := by nlinarith
  have hp := Real.pi_pos
  have hlb : Real.log b ≤ Real.log (K * b) := Real.log_le_log hb0 hKb
  have hl4 := log_ge_four hb
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    have hsub : (s.filter (fun i => |γ i| ≤ K * b)).filter (fun i => blk b (γ i) = 0) ⊆
        s.filter (fun i => |γ i| ≤ b) := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, (blk_spec hb0 hi.2).1 rfl⟩
    have hc : (((s.filter (fun i => |γ i| ≤ K * b)).filter (fun i => blk b (γ i) = 0)).card : ℝ)
        ≤ ((s.filter (fun i => |γ i| ≤ b)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have h := hN.1 b hb s
    have hM := Mt_le hb0
    have hR := Rt_le hb
    have : 2 * (b * Real.log b / (2 * π)) = b * Real.log b / π := by field_simp
    have : b * Real.log b / π ≤ b * Real.log (K * b) / π :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlb hb0.le) hp.le
    linarith
  · have hk1 : 1 ≤ k := h1
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkK : ((k : ℝ) + 1) ≤ K := by exact_mod_cast (show k + 1 ≤ K by omega)
    have ht1 : 70 ≤ k * b := by nlinarith
    have ht12 : k * b ≤ (k + 1) * b := by nlinarith
    have ht2K : (k + 1) * b ≤ K * b := by nlinarith
    have hsub : (s.filter (fun i => |γ i| ≤ K * b)).filter (fun i => blk b (γ i) = k) ⊆
        s.filter (fun i => k * b < |γ i| ∧ |γ i| ≤ (k + 1) * b) := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, (blk_spec hb0 hi.2).2 hk1⟩
    have hc : (((s.filter (fun i => |γ i| ≤ K * b)).filter (fun i => blk b (γ i) = k)).card : ℝ)
        ≤ ((s.filter (fun i => k * b < |γ i| ∧ |γ i| ≤ (k + 1) * b)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h := hN.2 (k * b) ((k + 1) * b) ht1 ht12 s
    have hM := Mt_diff (by linarith) ht12
    have hR1 := Rt_le ht1
    have hR2 := Rt_le (ht1.trans ht12)
    have hl1 : Real.log (k * b) ≤ Real.log (K * b) := Real.log_le_log (by linarith) (by linarith)
    have hl2 : Real.log ((k + 1) * b) ≤ Real.log (K * b) :=
      Real.log_le_log (by linarith) ht2K
    have e : ((k : ℝ) + 1) * b - k * b = b := by ring
    rw [e] at hM
    have : 2 * (b * Real.log ((k + 1) * b) / (2 * π)) ≤ b * Real.log (K * b) / π := by
      rw [show 2 * (b * Real.log ((k + 1) * b) / (2 * π)) = b * Real.log ((k + 1) * b) / π by
        field_simp]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl2 hb0.le) hp.le
    linarith

/-- The weight of block `k` for the Fejér sum. -/
noncomputable def tau (δ b : ℝ) (k : ℕ) : ℝ :=
  (δ ^ 2 * (if k = 0 then 1 else 0) + (1 + √δ) * (Real.sin (k * δ) ^ 2 / (k : ℝ) ^ 2) +
    2 * δ * √δ * (1 / (k : ℝ) ^ 2)) / b ^ 2

theorem term_le {b δ g : ℝ} (hb : 0 < b) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {k : ℕ}
    (hk : blk b g = k) :
    Real.sin (g * (δ / b)) ^ 2 * (1 / ‖rhoF g * (rhoF g + 1)‖) ≤ tau δ b k := by
  have hn : 0 < ‖rhoF g * (rhoF g + 1)‖ := lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' g)
  have hng := norm_rho_mul_ge g
  obtain ⟨hk0, hk1⟩ := blk_spec hb hk
  have hsa : Real.sin (g * (δ / b)) ^ 2 = Real.sin (|g| * (δ / b)) ^ 2 := by
    rcases abs_choice g with h | h <;> rw [h]
    rw [neg_mul, Real.sin_neg, neg_sq]
  rw [hsa]
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    have hg := hk0 rfl
    unfold tau
    simp only [ite_true, Nat.cast_zero, zero_mul, Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, mul_zero, add_zero, mul_one]
    have h1 : Real.sin (|g| * (δ / b)) ^ 2 ≤ (|g| * (δ / b)) ^ 2 := by
      have := Real.abs_sin_le_abs (x := |g| * (δ / b))
      have h0 : 0 ≤ |g| * (δ / b) := by positivity
      rw [abs_of_nonneg h0] at this
      nlinarith [abs_nonneg (Real.sin (|g| * (δ / b))), sq_abs (Real.sin (|g| * (δ / b)))]
    have h2 : (|g| * (δ / b)) ^ 2 * (1 / ‖rhoF g * (rhoF g + 1)‖) ≤ δ ^ 2 / b ^ 2 := by
      rw [mul_pow, sq_abs, mul_one_div, div_le_iff₀ hn]
      have : (δ / b) ^ 2 = δ ^ 2 / b ^ 2 := by ring
      rw [this]
      have : 0 ≤ δ ^ 2 / b ^ 2 := by positivity
      nlinarith
    calc _ ≤ (|g| * (δ / b)) ^ 2 * (1 / ‖rhoF g * (rhoF g + 1)‖) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := h2
  · obtain ⟨hlo, hhi⟩ := hk1 h1
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast h1
    set r := √δ with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hδ0
    have hr2 : r ^ 2 = δ := Real.sq_sqrt hδ0.le
    have hr1 : r ≤ 1 := by rw [hr, Real.sqrt_le_one]; exact hδ1
    have hdist : |(|g| * (δ / b)) - k * δ| ≤ δ := by
      rw [abs_le]
      have e : |g| * (δ / b) - k * δ = δ * (|g| / b - k) := by field_simp
      rw [e]
      have : (k : ℝ) < |g| / b := by rw [lt_div_iff₀ hb]; linarith
      have : |g| / b ≤ k + 1 := by rw [div_le_iff₀ hb]; linarith
      constructor <;> nlinarith
    have hsin : |Real.sin (|g| * (δ / b))| ≤ |Real.sin (k * δ)| + δ := by
      have := Real.abs_sin_sub_sin_le (|g| * (δ / b)) (k * δ)
      have := abs_sub_abs_le_abs_sub (Real.sin (|g| * (δ / b))) (Real.sin (k * δ))
      linarith
    set a := |Real.sin (k * δ)|
    have ha0 : 0 ≤ a := abs_nonneg _
    have hsq : Real.sin (|g| * (δ / b)) ^ 2 ≤ (1 + r) * a ^ 2 + 2 * δ * r := by
      have h1 : Real.sin (|g| * (δ / b)) ^ 2 ≤ (a + δ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsin 2
      have h2 : (a + δ) ^ 2 ≤ (1 + r) * a ^ 2 + 2 * δ * r := by
        have h4 : r ^ 4 ≤ r ^ 3 := by nlinarith [pow_pos hr0 3]
        rw [← hr2]; nlinarith [mul_nonneg hr0.le (sq_nonneg (a - r))]
      linarith
    have hw : 1 / ‖rhoF g * (rhoF g + 1)‖ ≤ 1 / (k * b) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (k * b) ^ 2 ≤ g ^ 2 := by
        rw [← sq_abs g]; exact pow_le_pow_left₀ (by positivity) hlo.le 2
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    unfold tau
    rw [if_neg (show k ≠ 0 by omega), ← sq_abs (Real.sin (k * δ))]
    have : (δ ^ 2 * 0 + (1 + r) * (a ^ 2 / (k : ℝ) ^ 2) + 2 * δ * r * (1 / (k : ℝ) ^ 2)) / b ^ 2
        = ((1 + r) * a ^ 2 + 2 * δ * r) * (1 / (k * b) ^ 2) := by
      field_simp
      ring
    rw [this]
    exact mul_le_mul hsq hw (by positivity) (by positivity)

theorem tau_sum {b δ : ℝ} (hb : 0 < b) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, tau δ b k ≤ (π * δ / 2 + 10 * δ * √δ) / b ^ 2 := by
  set r := √δ with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hδ0
  have hr2 : r ^ 2 = δ := Real.sq_sqrt hδ0.le
  have hr1 : r ≤ 1 := by rw [hr, Real.sqrt_le_one]; exact hδ1
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_d4
  unfold tau
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have h1 : ∑ k ∈ Finset.range K, (if k = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
  have h2 : ∑ k ∈ Finset.range K, Real.sin (k * δ) ^ 2 / (k : ℝ) ^ 2 ≤ (π * δ - δ ^ 2) / 2 :=
    sum_le_hasSum _ (fun k _ => by positivity) (hasSum_sin_sq hδ0.le (by linarith))
  have h3 : ∑ k ∈ Finset.range K, 1 / (k : ℝ) ^ 2 ≤ π ^ 2 / 6 :=
    sum_le_hasSum _ (fun k _ => by positivity) hasSum_zeta_two
  have hd2 : δ ^ 2 ≤ δ * r := by rw [← hr2]; nlinarith [pow_pos hr0 3]
  have hpp : π ^ 2 / 6 ≤ 1.65 := by nlinarith
  have e1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ δ ^ 2)
  have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 + r)
  have e3 := mul_le_mul_of_nonneg_left (h3.trans hpp) (by positivity : (0 : ℝ) ≤ 2 * δ * r)
  have e4 : (1 + r) * ((π * δ - δ ^ 2) / 2) ≤ π * δ / 2 + 1.6 * δ * r := by
    have : 0 ≤ δ ^ 2 := by positivity
    nlinarith [mul_pos hδ0 hr0]
  nlinarith [mul_pos hδ0 hr0]

/-- **The Fejér sum over the zeros**, CONDITIONAL ON `HSWN70`: for `b ≥ 70`, `0 < δ ≤ 1`,
`K ≥ 1` and `T = K b`, `Σ_{|γ| ≤ T} sin²(γδ/b)/|ρ(ρ+1)| ≤ (b log T/π + 2 log T + 41)(πδ/2 + 10 δ^{3/2})/b²`.
This is the lab's discrete form of Dudek's use of Ingham's Theorem A on page 8. -/
theorem fejer_sum {γ : ι → ℝ} (hN : HSWN70 γ) {b δ : ℝ} (hb : 70 ≤ b) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) {K : ℕ} (hK : 1 ≤ K) (s : Finset ι) :
    ∑ i ∈ s.filter (fun i => |γ i| ≤ K * b), Real.sin (γ i * (δ / b)) ^ 2 * wgt γ i ≤
      (b * Real.log (K * b) / π + 2 * Real.log (K * b) + 41) *
        ((π * δ / 2 + 10 * δ * √δ) / b ^ 2) := by
  have hb0 : 0 < b := by linarith
  set H := s.filter (fun i => |γ i| ≤ K * b)
  have hmap : ∀ i ∈ H, blk b (γ i) ∈ Finset.range K := by
    intro i hi
    simp only [H, Finset.mem_filter] at hi
    rw [Finset.mem_range]
    unfold blk
    have : ⌈|γ i| / b⌉₊ ≤ K := Nat.ceil_le.2 (by rw [div_le_iff₀ hb0]; exact hi.2)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  set C := b * Real.log (K * b) / π + 2 * Real.log (K * b) + 41
  have hC0 : 0 ≤ C := by
    have := log_ge_four hb
    have : Real.log b ≤ Real.log (K * b) := Real.log_le_log hb0 (by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith)
    have hl0 : 0 ≤ Real.log (K * b) := by linarith
    have := div_nonneg (mul_nonneg hb0.le hl0) Real.pi_pos.le
    linarith
  calc _ ≤ ∑ k ∈ Finset.range K, C * tau δ b k := by
        apply Finset.sum_le_sum
        intro k hk
        calc _ ≤ ∑ i ∈ H.filter (fun i => blk b (γ i) = k), tau δ b k := by
              apply Finset.sum_le_sum
              intro i hi
              exact term_le hb0 hδ0 hδ1 (Finset.mem_filter.1 hi).2
          _ = ((H.filter (fun i => blk b (γ i) = k)).card : ℝ) * tau δ b k := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ C * tau δ b k := by
              apply mul_le_mul_of_nonneg_right (blk_count hN hb k (Finset.mem_range.1 hk) s)
              unfold tau
              positivity
    _ = C * ∑ k ∈ Finset.range K, tau δ b k := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tau_sum hb0 hδ0 hδ1 K) hC0

/-! ### The zero sum with the sharp constant -/

/-- **Dudek's Section 2.3 bound for the second difference of the zero sum**, CONDITIONAL ON
`HSWN70 γ`: with `u = h/y`, block length `b = 2δy/h ≥ 70`, `T = K b`, `ℓ = log T`, and
`W = Σ 1/|ρ(ρ+1)|`, the second difference is at most
`4 y^{3/2} (bℓ/π + 2ℓ + 41)(πδ/2 + 10δ^{3/2})/b² + y^{3/2}(4u + 4Tu²) W
 + 4 (y+h)^{3/2} (ℓ/(πT) + (1.004ℓ + 41.26)/T²)`. -/
theorem zero_sum_c3 {γ : ι → ℝ} (hN : HSWN70 γ) {y h δ b : ℝ} (hy : 0 < y) (hh : 0 < h)
    (h2 : 2 * h ≤ y) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hbd : b * h = 2 * δ * y) (hb : 70 ≤ b)
    {K : ℕ} (hK : 1 ≤ K) :
    |Zr γ (y + h) - 2 * Zr γ y + Zr γ (y - h)| ≤
      y * √y * (4 * ((b * Real.log (K * b) / π + 2 * Real.log (K * b) + 41) *
          ((π * δ / 2 + 10 * δ * √δ) / b ^ 2)) +
        (4 * (h / y) + 4 * (K * b) * (h / y) ^ 2) * ∑' i, wgt γ i) +
      4 * (y + h) ^ (3 / 2 : ℝ) * (Real.log (K * b) / (π * (K * b)) +
        (1.004 * Real.log (K * b) + 41.26) / (K * b) ^ 2) := by
  have hhy : h < y := by linarith
  have hyh : 0 < y - h := by linarith
  have hb0 : 0 < b := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set T := (K : ℝ) * b with hT
  have hT70 : 70 ≤ T := by nlinarith
  set ℓ := Real.log T
  set u := h / y with hu
  set D : ι → ℂ := fun i =>
    fz (rhoF (γ i)) (y + h) - 2 * fz (rhoF (γ i)) y + fz (rhoF (γ i)) (y - h)
  have sa := summable_fz hN (by linarith : 0 < y + h)
  have sb := summable_fz hN hy
  have sc := summable_fz hN hyh
  have eD : ∑' i, D i = (∑' i, fz (rhoF (γ i)) (y + h)) - 2 * (∑' i, fz (rhoF (γ i)) y)
      + ∑' i, fz (rhoF (γ i)) (y - h) := by
    rw [← tsum_mul_left, ← sa.tsum_sub (sb.mul_left 2), ← (sa.sub (sb.mul_left 2)).tsum_add sc]
  have e : Zr γ (y + h) - 2 * Zr γ y + Zr γ (y - h) = (∑' i, D i).re := by
    rw [eD]; unfold Zr; simp [Complex.add_re, Complex.sub_re]
  rw [e]
  set B := 4 * (y + h) ^ (3 / 2 : ℝ)
  have hB : 0 ≤ B := by positivity
  have hDn : ∀ i, ‖D i‖ ≤ B * wgt γ i := fun i => by
    have := second_diff_large (γ i) hh hhy; unfold wgt; rw [mul_one_div]; exact this
  have hsw := summable_wgt hN
  have hsumN : Summable (fun i => ‖D i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hDn (hsw.mul_left B)
  set W := ∑' i, wgt γ i
  set F := (b * ℓ / π + 2 * ℓ + 41) * ((π * δ / 2 + 10 * δ * √δ) / b ^ 2)
  have hdb : δ / b = u / 2 := by
    rw [hu, div_eq_div_iff hb0.ne' (by norm_num), ]
    field_simp
    linarith
  -- the head terms
  have hhead : ∀ i, |γ i| ≤ T → ‖D i‖ ≤
      y * √y * 4 * (Real.sin (γ i * (δ / b)) ^ 2 * wgt γ i) +
        y * √y * (4 * u + 4 * T * u ^ 2) * wgt γ i := by
    intro i hi
    have hn : 0 < ‖rhoF (γ i) * (rhoF (γ i) + 1)‖ :=
      lt_of_lt_of_le (by norm_num) (norm_rho_mul_ge' _)
    have hnb := num_bound (γ i) hy hh h2
    have eDi : D i = (((y + h : ℝ) : ℂ) ^ (rhoF (γ i) + 1) - 2 * ((y : ℝ) : ℂ) ^ (rhoF (γ i) + 1) +
        ((y - h : ℝ) : ℂ) ^ (rhoF (γ i) + 1)) / (rhoF (γ i) * (rhoF (γ i) + 1)) := by
      simp only [D, fz]; ring
    rw [eDi, norm_div]
    have hw : wgt γ i = 1 / ‖rhoF (γ i) * (rhoF (γ i) + 1)‖ := rfl
    rw [hdb]
    rw [div_eq_mul_one_div, ← hw]
    have hw0 : 0 ≤ wgt γ i := wgt_nonneg γ i
    have hg : 4 * |γ i| * u ^ 2 ≤ 4 * T * u ^ 2 := by nlinarith [sq_nonneg u]
    have h' : γ i * (h / y) / 2 = γ i * (u / 2) := by rw [hu]; ring
    rw [h'] at hnb
    have := mul_le_mul_of_nonneg_right hnb hw0
    have hy0 : 0 ≤ y * √y := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hg (mul_nonneg hy0 hw0)]
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖D i‖ ≤
      y * √y * (4 * F + (4 * u + 4 * T * u ^ 2) * W) +
        B * (ℓ / (π * T) + (1.004 * ℓ + 41.26) / T ^ 2) := by
    intro s
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)]
    have hH : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), ‖D i‖ ≤
        y * √y * (4 * F + (4 * u + 4 * T * u ^ 2) * W) := by
      calc _ ≤ ∑ i ∈ s.filter (fun i => |γ i| ≤ T),
            (y * √y * 4 * (Real.sin (γ i * (δ / b)) ^ 2 * wgt γ i) +
              y * √y * (4 * u + 4 * T * u ^ 2) * wgt γ i) :=
            Finset.sum_le_sum fun i hi => hhead i (Finset.mem_filter.1 hi).2
        _ = y * √y * 4 * ∑ i ∈ s.filter (fun i => |γ i| ≤ T),
              Real.sin (γ i * (δ / b)) ^ 2 * wgt γ i +
            y * √y * (4 * u + 4 * T * u ^ 2) * ∑ i ∈ s.filter (fun i => |γ i| ≤ T), wgt γ i := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ y * √y * 4 * F + y * √y * (4 * u + 4 * T * u ^ 2) * W := by
            gcongr
            · exact fejer_sum hN hb hδ0 hδ1 hK s
            · exact hsw.sum_le_tsum _ (fun i _ => wgt_nonneg γ i)
        _ = _ := by ring
    have hTl : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), ‖D i‖ ≤
        B * (ℓ / (π * T) + (1.004 * ℓ + 41.26) / T ^ 2) := by
      calc _ ≤ ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), B * (1 / γ i ^ 2) :=
            Finset.sum_le_sum fun i hi => (hDn i).trans (mul_le_mul_of_nonneg_left
              (wgt_le_inv_sq γ (ne_of_large hT70 (Finset.mem_filter.1 hi).2)) hB)
        _ = B * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), 1 / γ i ^ 2 := by rw [Finset.mul_sum]
        _ ≤ B * (ℓ / (π * T) + (1.004 * ℓ + 41.26 - 0.25 * T) / T ^ 2) :=
            mul_le_mul_of_nonneg_left (tail_inv_sq hN hT70 s) hB
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hB
            have : (1.004 * ℓ + 41.26 - 0.25 * T) / T ^ 2 ≤ (1.004 * ℓ + 41.26) / T ^ 2 :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)
            linarith
    linarith
  calc |(∑' i, D i).re| ≤ ‖∑' i, D i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' i, ‖D i‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ _ := hsumN.tsum_le_of_sum_le hfin

/-! ### Eventual sizes and the assembly -/

/-- For any constants, eventually `1 ≤ x`, `L₀ ≤ log x` and `M (log x)² ≤ √x`. -/
theorem eventually_sizes (L₀ M : ℝ) : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    1 ≤ x ∧ L₀ ≤ Real.log x ∧ M * Real.log x ^ 2 ≤ √x := by
  have hc : (0 : ℝ) < 1 / (|M| + 1) := by positivity
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound hc
  have h2 := Real.tendsto_log_atTop.eventually_ge_atTop L₀
  have h3 := Filter.eventually_ge_atTop (1 : ℝ)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hb, hl, h1x⟩ := hX x hx
  refine ⟨h1x, hl, ?_⟩
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hb
  have hq : (x ^ (1 / 4 : ℝ)) ^ 2 = √x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]; norm_num
  have hsq : Real.log x ^ 2 ≤ (1 / (|M| + 1)) ^ 2 * √x := by
    rw [← hq, ← mul_pow, ← sq_abs (Real.log x)]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hl2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hM : |M| * (1 / (|M| + 1)) ^ 2 ≤ 1 := by
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith [abs_nonneg M]
  calc M * Real.log x ^ 2 ≤ |M| * Real.log x ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self M) hl2
    _ ≤ |M| * ((1 / (|M| + 1)) ^ 2 * √x) := mul_le_mul_of_nonneg_left hsq (abs_nonneg M)
    _ ≤ √x := by nlinarith

/-- The final inequality, pure arithmetic. -/
theorem final_arith {s L e lam AW δ ℓ P Φ M h c : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hs : 0 < s) (hL : 42 ≤ L) (hlam0 : 0 ≤ lam) (hlamL : 2 * lam ≤ L) (hAW : 0 ≤ AW)
    (hδ0 : 0 < δ) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ lam + L / 2) (hP0 : 0 ≤ P) (hP : P ≤ s + L)
    (hC1 : 1 + 2 * lam + 4 * AW + 1 ≤ 11 * e / 48 * L)
    (hC2 : 48 * (12 + 4 * AW + 10.2 / δ) / (11 * e) * L ^ 2 ≤ s)
    (hΦ : Φ ≤ P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ + 4 * P * AW +
      9 * L * (1.004 * ℓ + 41.26))
    (hh : h = (3 + e) / 2 * s * L) (hM : M ≤ 9 * L ^ 3) (hc : c ≤ L + 1) :
    s * c < h - Φ - 1 - M := by
  have hL1 : 1 ≤ L := by linarith
  have hℓL : ℓ ≤ L := by linarith
  -- φ1
  have k1 : P * ℓ * (1 + e / 12) ≤ s * L / 2 + e * s * L / 24 + 2 * s * lam + 2 * L ^ 2 := by
    have : P * ℓ ≤ (s + L) * (lam + L / 2) := mul_le_mul hP hℓ hℓ0 (by positivity)
    have h2 : P * ℓ * (1 + e / 12) ≤ (s + L) * (lam + L / 2) * (1 + e / 12) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : L * lam ≤ L ^ 2 / 2 := by nlinarith
    nlinarith [mul_nonneg hs.le hlam0, mul_nonneg (mul_nonneg he0.le hs.le) hlam0,
      mul_nonneg (mul_nonneg he0.le (by linarith : (0:ℝ) ≤ L)) hlam0]
  have k2 : 3.4 * (2 * ℓ + 41) * L / δ ≤ 10.2 / δ * L ^ 3 := by
    have : 3.4 * (2 * ℓ + 41) * L ≤ 10.2 * L ^ 3 := by nlinarith
    calc 3.4 * (2 * ℓ + 41) * L / δ ≤ 10.2 * L ^ 3 / δ := div_le_div_of_nonneg_right this hδ0.le
      _ = _ := by ring
  have k3 : 4 * P * AW ≤ 4 * s * AW + 4 * AW * L ^ 3 := by
    have : L ≤ L ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hP hAW, mul_le_mul_of_nonneg_left this hAW]
  have k4 : 9 * L * (1.004 * ℓ + 41.26) ≤ L ^ 3 := by nlinarith
  have hL3 : 2 * L ^ 2 + 1 ≤ L ^ 3 := by nlinarith
  have hD : 0 < 12 + 4 * AW + 10.2 / δ := by positivity
  have hsC2 : (12 + 4 * AW + 10.2 / δ) * L ^ 3 ≤ 11 * e / 48 * s * L := by
    have := mul_le_mul_of_nonneg_right hC2 (by positivity : (0 : ℝ) ≤ 11 * e / 48 * L)
    have e1 : 48 * (12 + 4 * AW + 10.2 / δ) / (11 * e) * L ^ 2 * (11 * e / 48 * L) =
        (12 + 4 * AW + 10.2 / δ) * L ^ 3 := by field_simp
    linarith
  have hsC1 : (1 + 2 * lam + 4 * AW + 1) * s ≤ 11 * e / 48 * L * s :=
    mul_le_mul_of_nonneg_right hC1 hs.le
  have hcs : s * c ≤ s * (L + 1) := mul_le_mul_of_nonneg_left hc hs.le
  have e2 : 10.2 / δ * L ^ 3 + 4 * AW * L ^ 3 + L ^ 3 + L ^ 3 + 9 * L ^ 3 + L ^ 3 ≥
      (12 + 4 * AW + 10.2 / δ) * L ^ 3 := by nlinarith
  rw [hh]
  nlinarith

/-- Sizes of the window: with `h = (3+e)/2 · s L`, `y = s² + h` and `2000 L ≤ s`. -/
theorem window_facts {s L e h y : ℝ} (hs0 : 0 < s) (hL : 42 ≤ L) (he0 : 0 < e) (he1 : e ≤ 1)
    (hsL : 2000 * L ≤ s) (hh : h = (3 + e) / 2 * s * L) (hy : y = s ^ 2 + h) :
    0 < h ∧ 1.5 * s * L ≤ h ∧ h ≤ 2 * s * L ∧ 2 * h ≤ y ∧ h ≤ 0.001 * y ∧ y ≤ s * h ∧
      2 * h ≤ s ^ 2 := by
  have hsL0 : 0 < s * L := mul_pos hs0 (by linarith)
  have hh' : h = 1.5 * (s * L) + e / 2 * (s * L) := by rw [hh]; ring
  have hhlo : 1.5 * s * L ≤ h := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ e / 2) hsL0.le
    rw [hh']; linarith
  have hhhi : h ≤ 2 * s * L := by
    have := mul_le_mul_of_nonneg_right (by linarith : e / 2 ≤ 1 / 2) hsL0.le
    rw [hh']; linarith
  have hss : 2000 * (s * L) ≤ s * s := by
    have := mul_le_mul_of_nonneg_left hsL hs0.le; linarith
  have hx2 : 4 * s * L ≤ s ^ 2 := by nlinarith
  refine ⟨by linarith, hhlo, hhhi, by rw [hy]; nlinarith, by rw [hy]; nlinarith, ?_, by nlinarith⟩
  rw [hy]
  have h1 : s ≤ 1.5 * L * (s - 1) := by nlinarith
  have h2 : 1.5 * L * (s - 1) * s ≤ h * (s - 1) := by
    have := mul_le_mul_of_nonneg_right hhlo (by linarith : (0:ℝ) ≤ s - 1); nlinarith
  nlinarith

theorem hPsL_lem {P y s h L : ℝ} (hPdef : P = √y) (hy : y = s ^ 2 + h) (hs0 : 0 < s)
    (hhhi : h ≤ 2 * s * L) (hL : 0 ≤ L) : P ≤ s + L := by
  rw [hPdef, Real.sqrt_le_left (by positivity), hy]; nlinarith

theorem hPh_lem {P h y L s : ℝ} (hy0 : 0 < y) (hPy : P ^ 2 = y) (hPs : s ≤ P) (hs0 : 0 < s)
    (hhhi : h ≤ 2 * s * L) (hh0 : 0 < h) : P * h / y ≤ 2 * L := by
  have hP0 : 0 < P := by linarith
  rw [← hPy, show P * h / P ^ 2 = h / P by field_simp, div_le_iff₀ hP0]
  have : 2 * L * s ≤ 2 * L * P := by
    have hL : 0 ≤ 2 * L := by
      by_contra hc; push Not at hc; nlinarith
    exact mul_le_mul_of_nonneg_left hPs hL
  linarith

theorem h32_lem {y h P : ℝ} (hy0 : 0 < y) (hh0 : 0 < h) (hhy : h ≤ 0.001 * y)
    (hPy : P ^ 2 = y) (hP0 : 0 ≤ P) : (y + h) ^ (3 / 2 : ℝ) ≤ 1.01 * (y * P) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  have hq : √(y + h) ≤ 1.0005 * P := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, hPy]; nlinarith
  have := mul_le_mul (show y + h ≤ 1.001 * y by linarith) hq (Real.sqrt_nonneg _) (by positivity)
  nlinarith [mul_nonneg hy0.le hP0]

/-- The arithmetic of the zero sum: each of the five pieces is `h` times a piece of `Φ`. -/
theorem pieces {y h P b T ℓ δ r e α W L Z : ℝ} (hy0 : 0 < y) (hh0 : 0 < h) (hP0 : 0 ≤ P)
    (hPy : P ^ 2 = y) (hδ0 : 0 < δ) (hr0 : 0 < r) (hr1 : r ≤ 1 / 128) (hrd : δ = r ^ 2)
    (he0 : 0 < e) (hre : r * 128 = e) (hα : α = 64 / e) (he1 : e ≤ 1) (hW0 : 0 ≤ W) (hℓ0 : 0 ≤ ℓ) (hL0 : 0 ≤ L)
    (hbd : b = 2 * δ * y / h) (hThlo : α * y ≤ T * h) (hThhi : T * h ≤ (α + 1) * y)
    (hPh : P * h / y ≤ 2 * L) (h32 : (y + h) ^ (3 / 2 : ℝ) ≤ 1.01 * (y * P))
    (hZ : Z ≤ y * P * (4 * ((b * ℓ / π + 2 * ℓ + 41) * ((π * δ / 2 + 10 * δ * r) / b ^ 2)) +
        (4 * (h / y) + 4 * T * (h / y) ^ 2) * W) +
      4 * (y + h) ^ (3 / 2 : ℝ) * (ℓ / (π * T) + (1.004 * ℓ + 41.26) / T ^ 2)) :
    Z ≤ h * (P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ + 4 * P * ((α + 2) * W) +
      9 * L * (1.004 * ℓ + 41.26)) := by
  have hp := Real.pi_gt_three
  have hp2 := Real.pi_lt_d2
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα64 : 64 ≤ α := by rw [hα, le_div_iff₀ he0]; linarith
  have hT0 : 0 < T := by
    have : 0 < T * h := by nlinarith [mul_pos hα0 hy0]
    exact pos_of_mul_pos_left this hh0.le
  have ea : y * P * (4 * ((b * ℓ / π + 2 * ℓ + 41) * ((π * δ / 2 + 10 * δ * r) / b ^ 2))) =
      h * (P * ℓ * (1 + 20 * r / π)) +
        h * ((2 * ℓ + 41) * (π / 2 + 10 * r) / δ * (P * h / y)) := by
    rw [hbd]; field_simp
    try ring
  have eb : y * P * ((4 * (h / y) + 4 * T * (h / y) ^ 2) * W) =
      h * (4 * P * W * (1 + T * h / y)) := by
    field_simp
    try ring
  have hTu : T * h / y ≤ α + 1 := by rw [div_le_iff₀ hy0]; linarith
  have hT0' : 0 < α * y / h := by positivity
  have hTge : α * y / h ≤ T := by rw [div_le_iff₀ hh0]; linarith
  have ec1 : ℓ / (π * T) ≤ ℓ / (π * (α * y / h)) :=
    div_le_div_of_nonneg_left hℓ0 (by positivity) (by nlinarith)
  have ec2 : (1.004 * ℓ + 41.26) / T ^ 2 ≤ (1.004 * ℓ + 41.26) / (α * y / h) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hT0'.le hTge 2)
  have ec : 4 * (y + h) ^ (3 / 2 : ℝ) * (ℓ / (π * T) + (1.004 * ℓ + 41.26) / T ^ 2) ≤
      h * (4.04 / (π * α) * P * ℓ + 4.04 / α ^ 2 * (1.004 * ℓ + 41.26) * (P * h / y)) := by
    have hpos : 0 ≤ ℓ / (π * T) + (1.004 * ℓ + 41.26) / T ^ 2 := by positivity
    calc _ ≤ 4 * (1.01 * (y * P)) * (ℓ / (π * (α * y / h)) +
          (1.004 * ℓ + 41.26) / (α * y / h) ^ 2) := by
          apply mul_le_mul (by linarith) (by linarith) hpos (by positivity)
      _ = _ := by field_simp; ring
  have k1 : (2 * ℓ + 41) * (π / 2 + 10 * r) / δ * (P * h / y) ≤ 3.4 * (2 * ℓ + 41) * L / δ := by
    have h1 : (π / 2 + 10 * r) ≤ 1.7 := by linarith
    have h2 : (2 * ℓ + 41) * (π / 2 + 10 * r) * (P * h / y) ≤ (2 * ℓ + 41) * 1.7 * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hPh (by positivity)
        (by positivity)
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ0]
    linarith
  have k2 : 4 * P * W * (1 + T * h / y) ≤ 4 * P * ((α + 2) * W) := by
    have := mul_le_mul_of_nonneg_left (show 1 + T * h / y ≤ α + 2 by linarith)
      (by positivity : (0:ℝ) ≤ 4 * P * W)
    linarith
  have k3 : P * ℓ * (1 + 20 * r / π) + 4.04 / (π * α) * P * ℓ ≤ P * ℓ * (1 + e / 12) := by
    have h1 : 20 * r / π ≤ e / 19 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [← hre]
      have := mul_le_mul_of_nonneg_left hp.le (show (0:ℝ) ≤ r * 128 by positivity)
      linarith
    have h2 : 4.04 / (π * α) ≤ e / 49 := by
      have := Real.pi_gt_d2
      rw [div_le_div_iff₀ (by positivity) (by norm_num), hα]
      have : e * (π * (64 / e)) = 64 * π := by field_simp
      linarith
    have h3 : 20 * r / π + 4.04 / (π * α) ≤ e / 12 := by linarith
    have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hP0 hℓ0)
    have e1 : P * ℓ * (1 + 20 * r / π) + 4.04 / (π * α) * P * ℓ =
        P * ℓ + P * ℓ * (20 * r / π + 4.04 / (π * α)) := by ring
    have e2 : P * ℓ * (1 + e / 12) = P * ℓ + P * ℓ * (e / 12) := by ring
    rw [e1, e2]; linarith
  have k4 : 4.04 / α ^ 2 * (1.004 * ℓ + 41.26) * (P * h / y) ≤ 9 * L * (1.004 * ℓ + 41.26) := by
    have h1 : 4.04 / α ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity), sq]
      have := mul_le_mul hα64 hα64 (by norm_num) hα0.le
      linarith
    have h2 : 0 ≤ 1.004 * ℓ + 41.26 := by positivity
    have h3 : 0 ≤ L * (1.004 * ℓ + 41.26) := mul_nonneg hL0 h2
    calc _ ≤ 1 * (1.004 * ℓ + 41.26) * (2 * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 h2) hPh (by positivity) (by positivity)
      _ ≤ _ := by linarith
  rw [mul_add (y * P), ea, eb] at hZ
  have hsum := add_le_add (add_le_add (add_le_add k3 k1) k2) k4
  have hm := mul_le_mul_of_nonneg_left hsum hh0.le
  set A1 := P * ℓ * (1 + 20 * r / π)
  set A2 := (2 * ℓ + 41) * (π / 2 + 10 * r) / δ * (P * h / y)
  set A3 := 4 * P * W * (1 + T * h / y)
  set A4 := 4.04 / (π * α) * P * ℓ
  set A5 := 4.04 / α ^ 2 * (1.004 * ℓ + 41.26) * (P * h / y)
  have e3 : h * A1 + h * A2 + h * A3 + h * (A4 + A5) = h * (A1 + A4 + A2 + A3 + A5) := by ring
  have e4 : h * (P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ + 4 * P * ((α + 2) * W) +
      9 * L * (1.004 * ℓ + 41.26)) = h * (P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ +
      4 * P * ((α + 2) * W) + 9 * L * (1.004 * ℓ + 41.26)) := rfl
  linarith

/-- The prime power mass and `log(x + 2h)`: both small. -/
theorem mass_arith {x s L h : ℝ} (hs0 : 0 < s) (hs2 : s ^ 2 = x) (hx1 : 1 ≤ x) (hL : 42 ≤ L)
    (hLx : L = Real.log x) (hh0 : 0 < h) (hhhi : h ≤ 2 * s * L) (h2x : 2 * h ≤ x) :
    Real.log (x + 2 * h) ≤ L + 1 ∧
      Real.log (x + 2 * h) / Real.log 2 * (Real.log (x + 2 * h) / 2 * (√(x + 2 * h) - √x + 1))
        ≤ 9 * L ^ 3 := by
  have hx0 : 0 < x := by nlinarith
  have hlb : Real.log (x + 2 * h) ≤ L + 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (x + 2 * h) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h1
    have : (x + 2 * h) / x - 1 ≤ 1 := by rw [div_sub_one hx0.ne', div_le_one hx0]; linarith
    linarith
  have hlb0 : 0 ≤ Real.log (x + 2 * h) := Real.log_nonneg (by linarith)
  have hsq : √(x + 2 * h) ≤ s + 2 * L := by
    rw [Real.sqrt_le_left (by positivity), ← hs2]; nlinarith
  have hsx : √x = s := by rw [← hs2, Real.sqrt_sq hs0.le]
  have hd : √(x + 2 * h) - √x + 1 ≤ 2 * L + 1 := by rw [hsx]; linarith
  have hd0 : 0 ≤ √(x + 2 * h) - √x + 1 := by
    have := Real.sqrt_le_sqrt (show x ≤ x + 2 * h by linarith); linarith
  have hl2 := Real.log_two_gt_d9
  refine ⟨hlb, ?_⟩
  have m1 : Real.log (x + 2 * h) / Real.log 2 ≤ (L + 1) / 0.69 :=
    div_le_div₀ (by linarith) hlb (by norm_num) (by linarith)
  have m2 : Real.log (x + 2 * h) / 2 * (√(x + 2 * h) - √x + 1) ≤ (L + 1) / 2 * (2 * L + 1) :=
    mul_le_mul (by linarith) hd hd0 (by linarith)
  have m3 := mul_le_mul m1 m2 (by positivity) (by positivity)
  have a1 : (L + 1) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  have a2 : 2 * L + 1 ≤ 3 * L := by linarith
  have a3 : (L + 1) ^ 2 * (2 * L + 1) ≤ 2 * L ^ 2 * (3 * L) :=
    mul_le_mul a1 a2 (by linarith) (by positivity)
  have : (L + 1) / 0.69 * ((L + 1) / 2 * (2 * L + 1)) = (L + 1) ^ 2 * (2 * L + 1) / 1.38 := by
    ring
  rw [this] at m3
  have : (L + 1) ^ 2 * (2 * L + 1) / 1.38 ≤ 9 * L ^ 3 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **Dudek's `c = 3 + ε` for Cramér's theorem, for `ε ≤ 1`**: under RH, CONDITIONAL ON
`HSWN70 gZ`, for all large `x` more than `√x` primes lie in `(x, x + (3 + ε)√x log x]`. -/
theorem core (hRH : RiemannHypothesis) (hN : HSWN70 gZ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → √x < primesIn x ((3 + e) * √x * Real.log x) := by
  set r := e / 128 with hr
  set δ := r ^ 2 with hδ
  set α := 64 / e with hα
  set K := ⌈α / (2 * δ)⌉₊ with hKdef
  set W := ∑' i, wgt gZ i with hW
  set lam := Real.log (α + 1) with hlam
  set AW := (α + 2) * W with hAWdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 128 := by rw [hr]; linarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; nlinarith
  have h2d : 2 * δ ≤ 1 := by rw [hδ]; nlinarith
  have hsδ : √δ = r := Real.sqrt_sq hr0.le
  have hα0 : 0 < α := by positivity
  have hW0 : 0 ≤ W := tsum_nonneg (fun i => wgt_nonneg gZ i)
  have hAW0 : 0 ≤ AW := by positivity
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hKlo : α / (2 * δ) ≤ K := Nat.le_ceil _
  have hKhi : (K : ℝ) < α / (2 * δ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  obtain ⟨X, hX⟩ := eventually_sizes (max (max 42 (2 * lam)) (48 * (1 + 2 * lam + 4 * AW + 1) /
      (11 * e))) (max (48 * (12 + 4 * AW + 10.2 / δ) / (11 * e)) (70 / δ + 2000))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hx1, hL0, hM⟩ := hX x hx
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  set L := Real.log x with hL
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hL42 : 42 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL0
  have hlamL : 2 * lam ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL0
  have hC1 : 1 + 2 * lam + 4 * AW + 1 ≤ 11 * e / 48 * L := by
    have := le_trans (le_max_right _ _) hL0
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hC2 : 48 * (12 + 4 * AW + 10.2 / δ) / (11 * e) * L ^ 2 ≤ s :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hM
  have hM2 : (70 / δ + 2000) * L ^ 2 ≤ s :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) hM
  have hL1 : 1 ≤ L := by linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h70 : 0 ≤ 70 / δ * L ^ 2 := by positivity
  have hsL : 2000 * L ≤ s := by linarith
  have hδs : 70 * L ≤ δ * s := by
    have h1 : 70 / δ * L ≤ s := by
      have := mul_le_mul_of_nonneg_left hLL (show (0:ℝ) ≤ 70 / δ by positivity)
      have : 0 ≤ 2000 * L ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left h1 hδ0.le
    rw [show δ * (70 / δ * L) = 70 * L by field_simp] at this
    exact this
  -- the window
  set h := (3 + e) / 2 * s * L with hhdef
  set y := x + h with hydef
  obtain ⟨hh0, hhlo, hhhi, h2y, hhy, hyhs, h2x⟩ :=
    window_facts (y := y) hs0 hL42 he0 he1 hsL hhdef (by rw [hs2])
  rw [hs2] at h2x
  have hy0 : 0 < y := by positivity
  set b := 2 * δ * y / h with hbdef
  have hbd : b * h = 2 * δ * y := by rw [hbdef]; field_simp
  have hb70 : 70 ≤ b := by
    rw [hbdef, le_div_iff₀ hh0]
    have h1 : 70 * h ≤ 70 * (2 * s * L) := by linarith
    have h2 : 70 * (2 * s * L) ≤ 2 * δ * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hδs (by linarith : (0:ℝ) ≤ 2 * s); nlinarith
    have h3 : 2 * δ * s ^ 2 ≤ 2 * δ * y := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); rw [hydef, ← hs2]; linarith
    linarith
  set T := (K : ℝ) * b with hTdef
  have hTh : T * h = K * (2 * δ * y) := by rw [hTdef, mul_assoc, hbd]
  have hThlo : α * y ≤ T * h := by
    rw [hTh]
    have := mul_le_mul_of_nonneg_right hKlo (by positivity : (0:ℝ) ≤ 2 * δ * y)
    rw [show α / (2 * δ) * (2 * δ * y) = α * y by field_simp] at this
    linarith
  have hThhi : T * h ≤ (α + 1) * y := by
    rw [hTh]
    have := mul_le_mul_of_nonneg_right hKhi.le (by positivity : (0:ℝ) ≤ 2 * δ * y)
    rw [show (α / (2 * δ) + 1) * (2 * δ * y) = α * y + 2 * δ * y by field_simp] at this
    have := mul_le_mul_of_nonneg_right h2d hy0.le
    linarith
  have hT70 : 70 ≤ T := by
    rw [hTdef]; have := mul_le_mul_of_nonneg_right hK1r (by linarith : (0:ℝ) ≤ b); linarith
  set ℓ := Real.log T with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓ : ℓ ≤ lam + L / 2 := by
    have hT0 : 0 < T := by linarith
    have hTs : T ≤ (α + 1) * s := by
      rw [← mul_le_mul_iff_of_pos_right hh0]
      have := mul_le_mul_of_nonneg_left hyhs (by linarith : (0:ℝ) ≤ α + 1)
      linarith
    have := Real.log_le_log hT0 hTs
    rw [Real.log_mul (by linarith) hs0.ne', hs, Real.log_sqrt hx0.le] at this
    linarith
  -- the zero sum
  have hZ := zero_sum_c3 hN hy0 hh0 h2y hδ0 hδ1 hbd hb70 hK1
  rw [← hTdef, ← hℓdef, hsδ] at hZ
  set P := √y with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hPs : s ≤ P := Real.sqrt_le_sqrt (by linarith)
  have hPy : P ^ 2 = y := Real.sq_sqrt hy0.le
  have hPsL : P ≤ s + L := hPsL_lem hPdef (by rw [hydef, ← hs2]) hs0 hhhi (by linarith)
  have hPh := hPh_lem hy0 hPy hPs hs0 hhhi hh0
  have h32 := h32_lem hy0 hh0 hhy hPy hP0
  set Φ := P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ + 4 * P * AW +
      9 * L * (1.004 * ℓ + 41.26) with hΦdef
  have hS : |Zr gZ (y + h) - 2 * Zr gZ y + Zr gZ (y - h)| ≤ h * Φ :=
    pieces hy0 hh0 hP0 hPy hδ0 hr0 hr1 hδ he0 (by rw [hr]; ring) hα he1 hW0 hℓ0 (by linarith) hbdef hThlo hThhi
      hPh h32 hZ
  -- Lemma 5 at the centre `y`
  have hxgt : 1 < x := by
    rw [← hs2]; exact one_lt_pow₀ (by linarith) two_ne_zero
  have h5 := lemma5_of lemma4_Zpatch y h hh0 (by linarith)
  simp only at h5
  rw [patch_eq hRH (by linarith), patch_eq hRH (by linarith), patch_eq hRH (by linarith)] at h5
  set S := Zr gZ (y + h) - 2 * Zr gZ y + Zr gZ (y - h) with hSdef
  have hSh : S / h ≤ Φ := by
    rw [div_le_iff₀ hh0]; have := le_abs_self S; linarith
  have h48 : 48 / (5 * h) ≤ 1 := by
    have h10 : 10 * 1 ≤ s * L := mul_le_mul (by linarith) hL1 (by norm_num) hs0.le
    rw [div_le_iff₀ (by positivity)]; linarith
  have hWS : h - Φ - 1 < WS y h := by
    have := (abs_lt.1 h5).1; linarith
  have hWle := WS_le hh0 (by linarith : h ≤ y)
  rw [show y - h = x by rw [hydef]; ring, show y + h = x + 2 * h by rw [hydef]; ring,
    split_sum] at hWle
  obtain ⟨hlb, hmass⟩ := mass_arith hs0 hs2 hx1 hL42 hL hh0 hhhi h2x
  have hm := mass_gen (a := x) (b := x + 2 * h) hx1 (by linarith)
  have hpr := prime_sum_le (x := x) (b := x + 2 * h) hx0.le (by linarith)
  rw [show x + 2 * h - x = (3 + e) * s * L by rw [hhdef]; ring] at hpr
  set Pc := (primesIn x ((3 + e) * s * L) : ℝ)
  by_contra hcon
  push Not at hcon
  have hlb0 : 0 ≤ Real.log (x + 2 * h) := Real.log_nonneg (by linarith)
  have hfa := final_arith he0 he1 hs0 hL42 hlam0 hlamL hAW0 hδ0 hℓ0 hℓ hP0 hPsL hC1 hC2 le_rfl
    hhdef (hm.trans hmass) hlb
  have := mul_le_mul_of_nonneg_right hcon hlb0
  linarith

/-- **The `c = 3 + ε` form of Theorem 1, the abstract and Section 2.4 of Dudek 2014**:
under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` bound `HSWN70 gZ` only, for every
`ε > 0` and all large `x`, more than `√x` primes lie in `(x, x + (3 + ε)√x log x]`.
The conclusion of the statement `Statements.abstract_c3_stmt`. -/
theorem abstract_c3_of_RH_hsw (hRH : RiemannHypothesis) (hN : HSWN70 gZ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      √x < primesIn x ((3 + ε) * √x * Real.log x) := by
  intro ε hε
  obtain ⟨X, hX⟩ := core hRH hN (lt_min hε one_pos) (min_le_right ε 1)
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h1 := hX x (le_trans (le_max_left _ _) hx)
  have hL : 0 ≤ √x * Real.log x := mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hx1)
  have hle : (3 + min ε 1) * √x * Real.log x ≤ (3 + ε) * √x * Real.log x := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [min_le_left ε 1]) hL
  exact h1.trans_le (by exact_mod_cast primesIn_mono hle)

/-! ### Theorem 3: the window `(x - 2h, x]` -/

theorem window_facts3 {s L e h y : ℝ} (hs0 : 0 < s) (hL : 42 ≤ L) (he0 : 0 < e) (he1 : e ≤ 1)
    (hsL : 2000 * L ≤ s) (hh : h = (1 + e) / 2 * s * L) (hy : y = s ^ 2 - h) :
    0 < h ∧ h ≤ s * L ∧ 2 * h ≤ y ∧ h ≤ 0.001 * y ∧ y ≤ s * h ∧ 2 * h ≤ s ^ 2 ∧
      s / 2 ≤ √y ∧ √y ≤ s := by
  have hsL0 : 0 < s * L := mul_pos hs0 (by linarith)
  have hh' : h = 0.5 * (s * L) + e / 2 * (s * L) := by rw [hh]; ring
  have hhlo : 0.5 * s * L ≤ h := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ e / 2) hsL0.le
    rw [hh']; linarith
  have hhhi : h ≤ s * L := by
    have := mul_le_mul_of_nonneg_right (by linarith : e / 2 ≤ 1 / 2) hsL0.le
    rw [hh']; linarith
  have hss : 2000 * (s * L) ≤ s * s := by
    have := mul_le_mul_of_nonneg_left hsL hs0.le; linarith
  have hy2 : 3 * h ≤ 0.002 * s ^ 2 := by nlinarith
  have hy0 : 0 ≤ y := by rw [hy]; nlinarith
  refine ⟨by linarith, hhhi, by rw [hy]; nlinarith, by rw [hy]; nlinarith, ?_, by nlinarith,
    ?_, ?_⟩
  · rw [hy]
    have h1 : s ≤ 0.5 * L * (s + 1) := by nlinarith
    have h2 : 0.5 * L * (s + 1) * s ≤ h * (s + 1) := by
      have := mul_le_mul_of_nonneg_right hhlo (by linarith : (0:ℝ) ≤ s + 1); nlinarith
    nlinarith
  · rw [Real.le_sqrt (by positivity) hy0, hy]; nlinarith
  · rw [Real.sqrt_le_left hs0.le, hy]; linarith

theorem hPh_lem' {P h y L : ℝ} (hP0 : 0 < P) (hPy : P ^ 2 = y) (hhP : h ≤ 2 * L * P) :
    P * h / y ≤ 2 * L := by
  rw [← hPy, show P * h / P ^ 2 = h / P by field_simp, div_le_iff₀ hP0]
  linarith

theorem mass_arith3 {x s L h : ℝ} (hs0 : 0 < s) (hs2 : s ^ 2 = x) (hL : 42 ≤ L)
    (hLx : L = Real.log x) (hh0 : 0 < h) (hhhi : h ≤ s * L) (h2x : 2 * h ≤ x) :
    Real.log x / Real.log 2 * (Real.log x / 2 * (√x - √(x - 2 * h) + 1)) ≤ 9 * L ^ 3 := by
  have hsx : √x = s := by rw [← hs2, Real.sqrt_sq hs0.le]
  have hq0 : 0 ≤ √(x - 2 * h) := Real.sqrt_nonneg _
  have hq2 : √(x - 2 * h) ^ 2 = x - 2 * h := Real.sq_sqrt (by linarith)
  have hqs : √(x - 2 * h) ≤ s := by rw [← hsx]; exact Real.sqrt_le_sqrt (by linarith)
  have hd : √x - √(x - 2 * h) + 1 ≤ 2 * L + 1 := by
    rw [hsx]
    have : (s - √(x - 2 * h)) * (s + √(x - 2 * h)) = 2 * h := by nlinarith
    have : (s - √(x - 2 * h)) * s ≤ 2 * s * L := by nlinarith
    have : s - √(x - 2 * h) ≤ 2 * L := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  have hd0 : 0 ≤ √x - √(x - 2 * h) + 1 := by rw [hsx]; linarith
  have hl2 := Real.log_two_gt_d9
  rw [← hLx]
  have m1 : L / Real.log 2 ≤ L / 0.69 := div_le_div_of_nonneg_left (by linarith) (by norm_num)
    (by linarith)
  have m2 : L / 2 * (√x - √(x - 2 * h) + 1) ≤ L / 2 * (2 * L + 1) :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have m3 := mul_le_mul m1 m2 (by positivity) (by positivity)
  have : L / 0.69 * (L / 2 * (2 * L + 1)) = L ^ 2 * (2 * L + 1) / 1.38 := by ring
  rw [this] at m3
  have : L ^ 2 * (2 * L + 1) / 1.38 ≤ 9 * L ^ 3 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

/-- The final inequality for Theorem 3, pure arithmetic. -/
theorem final_arith3 {s L e lam AW δ ℓ P Φ M h : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hs : 0 < s) (hL : 42 ≤ L) (hlam0 : 0 ≤ lam) (hlamL : 2 * lam ≤ L) (hAW : 0 ≤ AW)
    (hδ0 : 0 < δ) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ lam + L / 2) (hP0 : 0 ≤ P) (hP : P ≤ s + L)
    (hC1 : 1 + 2 * lam + 4 * AW + 1 ≤ 11 * e / 48 * L)
    (hC2 : 48 * (12 + 4 * AW + 10.2 / δ) / (11 * e) * L ^ 2 ≤ s)
    (hΦ : Φ ≤ P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ + 4 * P * AW +
      9 * L * (1.004 * ℓ + 41.26))
    (hh : h = (1 + e) / 2 * s * L) (hM : M ≤ 9 * L ^ 3) :
    0 < h - Φ - 1 - M := by
  have := final_arith (c := 0) (h := (3 + e) / 2 * s * L) he0 he1 hs hL hlam0 hlamL hAW hδ0 hℓ0
    hℓ hP0 hP hC1 hC2 hΦ rfl hM (by linarith)
  have e1 : (3 + e) / 2 * s * L = h + s * L := by rw [hh]; ring
  have hsL : 0 ≤ s * L := mul_nonneg hs.le (by linarith)
  rw [e1, mul_zero] at this
  -- `final_arith` gives `0 < h + sL - Φ - 1 - M`; redo it with the `sL` margin removed
  have hL1 : 1 ≤ L := by linarith
  have hℓL : ℓ ≤ L := by linarith
  have k1 : P * ℓ * (1 + e / 12) ≤ s * L / 2 + e * s * L / 24 + 2 * s * lam + 2 * L ^ 2 := by
    have : P * ℓ ≤ (s + L) * (lam + L / 2) := mul_le_mul hP hℓ hℓ0 (by positivity)
    have h2 : P * ℓ * (1 + e / 12) ≤ (s + L) * (lam + L / 2) * (1 + e / 12) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : L * lam ≤ L ^ 2 / 2 := by nlinarith
    nlinarith [mul_nonneg hs.le hlam0, mul_nonneg (mul_nonneg he0.le hs.le) hlam0,
      mul_nonneg (mul_nonneg he0.le (by linarith : (0:ℝ) ≤ L)) hlam0]
  have k2 : 3.4 * (2 * ℓ + 41) * L / δ ≤ 10.2 / δ * L ^ 3 := by
    have : 3.4 * (2 * ℓ + 41) * L ≤ 10.2 * L ^ 3 := by nlinarith
    calc 3.4 * (2 * ℓ + 41) * L / δ ≤ 10.2 * L ^ 3 / δ := div_le_div_of_nonneg_right this hδ0.le
      _ = _ := by ring
  have k3 : 4 * P * AW ≤ 4 * s * AW + 4 * AW * L ^ 3 := by
    have : L ≤ L ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hP hAW, mul_le_mul_of_nonneg_left this hAW]
  have k4 : 9 * L * (1.004 * ℓ + 41.26) ≤ L ^ 3 := by nlinarith
  have hL3 : 2 * L ^ 2 + 1 ≤ L ^ 3 := by nlinarith
  have hsC2 : (12 + 4 * AW + 10.2 / δ) * L ^ 3 ≤ 11 * e / 48 * s * L := by
    have := mul_le_mul_of_nonneg_right hC2 (by positivity : (0 : ℝ) ≤ 11 * e / 48 * L)
    have e1 : 48 * (12 + 4 * AW + 10.2 / δ) / (11 * e) * L ^ 2 * (11 * e / 48 * L) =
        (12 + 4 * AW + 10.2 / δ) * L ^ 3 := by field_simp
    linarith
  have hsC1 : (1 + 2 * lam + 4 * AW + 1) * s ≤ 11 * e / 48 * L * s :=
    mul_le_mul_of_nonneg_right hC1 hs.le
  have e2 : 10.2 / δ * L ^ 3 + 4 * AW * L ^ 3 + L ^ 3 + L ^ 3 + 9 * L ^ 3 + L ^ 3 ≥
      (12 + 4 * AW + 10.2 / δ) * L ^ 3 := by nlinarith
  rw [hh]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Dudek's Theorem 3 for `ε ≤ 1`**: under RH, CONDITIONAL ON `HSWN70 gZ`, for all large `x`
there is a prime in `(x - (1 + ε)√x log x, x]`. -/
theorem core3 (hRH : RiemannHypothesis) (hN : HSWN70 gZ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p : ℕ, p.Prime ∧ x - (1 + e) * √x * Real.log x < p ∧ (p : ℝ) ≤ x := by
  set r := e / 128 with hr
  set δ := r ^ 2 with hδ
  set α := 64 / e with hα
  set K := ⌈α / (2 * δ)⌉₊ with hKdef
  set W := ∑' i, wgt gZ i with hW
  set lam := Real.log (α + 1) with hlam
  set AW := (α + 2) * W with hAWdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 128 := by rw [hr]; linarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; nlinarith
  have h2d : 2 * δ ≤ 1 := by rw [hδ]; nlinarith
  have hsδ : √δ = r := Real.sqrt_sq hr0.le
  have hα0 : 0 < α := by positivity
  have hW0 : 0 ≤ W := tsum_nonneg (fun i => wgt_nonneg gZ i)
  have hAW0 : 0 ≤ AW := by positivity
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hKlo : α / (2 * δ) ≤ K := Nat.le_ceil _
  have hKhi : (K : ℝ) < α / (2 * δ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  obtain ⟨X, hX⟩ := eventually_sizes (max (max 42 (2 * lam)) (48 * (1 + 2 * lam + 4 * AW + 1) /
      (11 * e))) (max (48 * (12 + 4 * AW + 10.2 / δ) / (11 * e)) (70 / δ + 2000))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hx1, hL0, hM⟩ := hX x hx
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  set L := Real.log x with hL
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hL42 : 42 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL0
  have hlamL : 2 * lam ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL0
  have hC1 : 1 + 2 * lam + 4 * AW + 1 ≤ 11 * e / 48 * L := by
    have := le_trans (le_max_right _ _) hL0
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hC2 : 48 * (12 + 4 * AW + 10.2 / δ) / (11 * e) * L ^ 2 ≤ s :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hM
  have hM2 : (70 / δ + 2000) * L ^ 2 ≤ s :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) hM
  have hL1 : 1 ≤ L := by linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h70 : 0 ≤ 70 / δ * L ^ 2 := by positivity
  have hsL : 2000 * L ≤ s := by linarith
  have hδs : 70 * L ≤ δ * s := by
    have h1 : 70 / δ * L ≤ s := by
      have := mul_le_mul_of_nonneg_left hLL (show (0:ℝ) ≤ 70 / δ by positivity)
      have : 0 ≤ 2000 * L ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left h1 hδ0.le
    rw [show δ * (70 / δ * L) = 70 * L by field_simp] at this
    exact this
  -- the window `(x - 2h, x]`, centre `y = x - h`
  set h := (1 + e) / 2 * s * L with hhdef
  set y := x - h with hydef
  obtain ⟨hh0, hhhi, h2y, hhy, hyhs, h2x, hPlo, hPhi⟩ :=
    window_facts3 (y := y) hs0 hL42 he0 he1 hsL hhdef (by rw [hs2])
  rw [hs2] at h2x
  have hy0 : 0 < y := by linarith
  set b := 2 * δ * y / h with hbdef
  have hbd : b * h = 2 * δ * y := by rw [hbdef]; field_simp
  set P := √y with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hPy : P ^ 2 = y := Real.sq_sqrt hy0.le
  have hb70 : 70 ≤ b := by
    rw [hbdef, le_div_iff₀ hh0]
    have h1 : 70 * h ≤ 70 * (s * L) := by linarith
    have h2 : 70 * (s * L) ≤ δ * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hδs hs0.le; nlinarith
    have h3 : δ * s ^ 2 ≤ 2 * δ * y := by
      have : s ^ 2 ≤ 2 * y := by
        have := pow_le_pow_left₀ (by positivity) hPlo 2
        rw [hPy] at this; nlinarith
      nlinarith
    linarith
  set T := (K : ℝ) * b with hTdef
  have hTh : T * h = K * (2 * δ * y) := by rw [hTdef, mul_assoc, hbd]
  have hThlo : α * y ≤ T * h := by
    rw [hTh]
    have := mul_le_mul_of_nonneg_right hKlo (by positivity : (0:ℝ) ≤ 2 * δ * y)
    rw [show α / (2 * δ) * (2 * δ * y) = α * y by field_simp] at this
    linarith
  have hThhi : T * h ≤ (α + 1) * y := by
    rw [hTh]
    have := mul_le_mul_of_nonneg_right hKhi.le (by positivity : (0:ℝ) ≤ 2 * δ * y)
    rw [show (α / (2 * δ) + 1) * (2 * δ * y) = α * y + 2 * δ * y by field_simp] at this
    have := mul_le_mul_of_nonneg_right h2d hy0.le
    linarith
  have hT70 : 70 ≤ T := by
    rw [hTdef]; have := mul_le_mul_of_nonneg_right hK1r (by linarith : (0:ℝ) ≤ b); linarith
  set ℓ := Real.log T with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓ : ℓ ≤ lam + L / 2 := by
    have hT0 : 0 < T := by linarith
    have hTs : T ≤ (α + 1) * s := by
      rw [← mul_le_mul_iff_of_pos_right hh0]
      have := mul_le_mul_of_nonneg_left hyhs (by linarith : (0:ℝ) ≤ α + 1)
      linarith
    have := Real.log_le_log hT0 hTs
    rw [Real.log_mul (by linarith) hs0.ne', hs, Real.log_sqrt hx0.le] at this
    linarith
  -- the zero sum
  have hZ := zero_sum_c3 hN hy0 hh0 h2y hδ0 hδ1 hbd hb70 hK1
  rw [← hTdef, ← hℓdef, hsδ] at hZ
  have hhP : h ≤ 2 * L * P := by
    have := mul_le_mul_of_nonneg_left hPlo (by linarith : (0:ℝ) ≤ 2 * L)
    have e1 : 2 * L * (s / 2) = s * L := by ring
    linarith
  have hPh := hPh_lem' (by linarith) hPy hhP
  have h32 := h32_lem hy0 hh0 hhy hPy hP0
  set Φ := P * ℓ * (1 + e / 12) + 3.4 * (2 * ℓ + 41) * L / δ + 4 * P * AW +
      9 * L * (1.004 * ℓ + 41.26) with hΦdef
  have hS : |Zr gZ (y + h) - 2 * Zr gZ y + Zr gZ (y - h)| ≤ h * Φ :=
    pieces hy0 hh0 hP0 hPy hδ0 hr0 hr1 hδ he0 (by rw [hr]; ring) hα he1 hW0 hℓ0 (by linarith)
      hbdef hThlo hThhi hPh h32 hZ
  -- Lemma 5 at the centre `y`
  have h210 : 210 ≤ h := by
    have h10 : 10 * 42 ≤ s * L := mul_le_mul (by linarith) hL42 (by norm_num) hs0.le
    rw [hhdef]
    have := mul_le_mul_of_nonneg_right (show (1:ℝ) / 2 ≤ (1 + e) / 2 by linarith)
      (show (0:ℝ) ≤ s * L by positivity)
    have e2 : (1 + e) / 2 * s * L = (1 + e) / 2 * (s * L) := by ring
    linarith
  have hxh : 1 < y - h := by linarith
  have h5 := lemma5_of lemma4_Zpatch y h hh0 (by linarith)
  simp only at h5
  rw [patch_eq hRH (by linarith), patch_eq hRH (by linarith), patch_eq hRH hxh] at h5
  set S := Zr gZ (y + h) - 2 * Zr gZ y + Zr gZ (y - h) with hSdef
  have hSh : S / h ≤ Φ := by
    rw [div_le_iff₀ hh0]; have := le_abs_self S; linarith
  have h48 : 48 / (5 * h) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hWS : h - Φ - 1 < WS y h := by
    have := (abs_lt.1 h5).1; linarith
  have hWle := WS_le hh0 (by linarith : h ≤ y)
  rw [show y - h = x - 2 * h by rw [hydef]; ring, show y + h = x by rw [hydef]; ring,
    split_sum] at hWle
  have hmass := mass_arith3 hs0 hs2 hL42 hL hh0 hhhi h2x
  have hm := mass_gen (a := x - 2 * h) (b := x) (by linarith) (by linarith)
  have hfa := final_arith3 he0 he1 hs0 hL42 hlam0 hlamL hAW0 hδ0 hℓ0 hℓ hP0 (by linarith) hC1 hC2
    le_rfl hhdef (hm.trans hmass)
  have hpos : 0 < ∑ p ∈ (Finset.Ioc ⌊x - 2 * h⌋₊ ⌊x⌋₊).filter Nat.Prime, Real.log p := by
    linarith
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have h1 : x - 2 * h < (⌊x - 2 * h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (⌊x - 2 * h⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
    rw [show (1 + e) * s * L = 2 * h by rw [hhdef]; ring]
    linarith
  · exact (Nat.cast_le.2 hp.1.2).trans (Nat.floor_le hx0.le)

/-- **Dudek 2014 Theorem 3**: under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` bound
`HSWN70 gZ` only, for every `ε > 0` and all large `x` there is a prime in
`(x - (1 + ε)√x log x, x]`. The conclusion of the statement `Statements.theorem3_stmt`. -/
theorem theorem3_of_RH_hsw (hRH : RiemannHypothesis) (hN : HSWN70 gZ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p : ℕ, p.Prime ∧ x - (1 + ε) * √x * Real.log x < p ∧ (p : ℝ) ≤ x := by
  intro ε hε
  obtain ⟨X, hX⟩ := core3 hRH hN (lt_min hε one_pos) (min_le_right ε 1)
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨p, hp, h1, h2⟩ := hX x (le_trans (le_max_left _ _) hx)
  have hL : 0 ≤ √x * Real.log x := mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hx1)
  have hle : (1 + min ε 1) * √x * Real.log x ≤ (1 + ε) * √x * Real.log x := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [min_le_left ε 1]) hL
  exact ⟨p, hp, by linarith, h2⟩

end LeanLab.Dudek2014.AbstractC3

