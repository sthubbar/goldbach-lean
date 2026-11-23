module

public import LeanLab.PNTPort.ExplicitPsi1.VonKoch2

/-!
# Zero counts for Selberg's mean square

Lab proof, unit U-5920, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input, unconditional.

For the nontrivial zeros `ρ` of `ζ`, `0 < Re ρ < 1`, with multiplicity `m(ρ)`:

* `norm_E_le`: `‖e^z - 2 + e^{-z}‖ ≤ 12 min(‖z‖², 1)` when `|Re z| ≤ 3/2`;
* `mult_le`: `m(ρ) ≤ C log(‖ρ‖ + 4)`;
* `head_count`: `Σ_{‖ρ‖ ≤ T} m(ρ) ≤ H T (log T + 2)` for `T ≥ 6`, from the lab's `tail_count`
  by dyadic shells;
* `key_sum`: for `0 < λ ≤ 1`,
  `Σ_ρ m(ρ)² min(λ⁴, ‖ρ‖⁻⁴) log(‖ρ‖ + 4) ≤ C λ³ (log(1/λ) + 3)³`,
  over every finite set of nontrivial zeros.

`key_sum` is the zero sum that the Gaussian mean value theorem `Gallagher.zero_mean_value`
leaves when it is fed the coefficients of the second difference of the explicit formula.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset
open LeanLab.PNTPort.ExplicitPsi1

local notation "ζ" => riemannZeta

/-- The nontrivial zeros. -/
def NZ (ρ : ℂ) : Prop := ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The multiplicity `m(ρ)` as a real number. -/
noncomputable def mz (ρ : ℂ) : ℝ := (analyticOrderNatAt ζ ρ : ℝ)

lemma mz_nonneg (ρ : ℂ) : 0 ≤ mz ρ := by unfold mz; positivity

lemma exp_three_halves_lt : Real.exp (3 / 2) < 5 := by
  have h : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have hp := Real.exp_pos (3 / 2)
  have h3 : Real.exp 1 ^ 3 < 25 := by
    have h0 := Real.exp_pos 1
    have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ h0.le he.le 3
    linarith [show (2.7182818286 : ℝ) ^ 3 < 25 by norm_num]
  nlinarith

/-- `‖e^z - 2 + e^{-z}‖ ≤ 12 min(‖z‖², 1)` for `|Re z| ≤ 3/2`. -/
lemma norm_E_le (z : ℂ) (hz : |z.re| ≤ 3 / 2) :
    ‖cexp z - 2 + cexp (-z)‖ ≤ 12 * min (‖z‖ ^ 2) 1 := by
  rcases le_or_gt ‖z‖ 1 with h | h
  · have h1 := Complex.norm_exp_sub_one_sub_id_le h
    have h2 := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by rwa [norm_neg])
    rw [norm_neg] at h2
    have e : cexp z - 2 + cexp (-z) = (cexp z - 1 - z) + (cexp (-z) - 1 - -z) := by ring
    rw [e, min_eq_left (by nlinarith [norm_nonneg z])]
    calc _ ≤ ‖cexp z - 1 - z‖ + ‖cexp (-z) - 1 - -z‖ := norm_add_le _ _
      _ ≤ ‖z‖ ^ 2 + ‖z‖ ^ 2 := add_le_add h1 h2
      _ ≤ 12 * ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  · rw [min_eq_right (by nlinarith)]
    have he1 : ‖cexp z‖ ≤ Real.exp (3 / 2) := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hz)
    have he2 : ‖cexp (-z)‖ ≤ Real.exp (3 / 2) := by
      rw [Complex.norm_exp, neg_re]
      exact Real.exp_le_exp.mpr (by linarith [neg_abs_le z.re])
    have h5 := exp_three_halves_lt
    calc _ ≤ ‖cexp z - 2‖ + ‖cexp (-z)‖ := norm_add_le _ _
      _ ≤ (‖cexp z‖ + ‖(2 : ℂ)‖) + ‖cexp (-z)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 12 * 1 := by rw [Complex.norm_ofNat]; linarith

lemma one_le_log_add_four {r : ℝ} (hr : 0 ≤ r) : 1 ≤ Real.log (r + 4) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9; linarith

lemma NZ_ne_zero {ρ : ℂ} (h : NZ ρ) : ρ ≠ 0 := by
  intro h0; have := h.2.1; rw [h0, zero_re] at this; exact lt_irrefl _ this

lemma NZ_add_one_ne_zero {ρ : ℂ} (h : NZ ρ) : ρ + 1 ≠ 0 := by
  intro h0
  have : (ρ + 1).re = 0 := by rw [h0, zero_re]
  rw [add_re, one_re] at this; linarith [h.2.1]

lemma mz_eq_hw {ρ : ℂ} (h : NZ ρ) : mz ρ = hw ρ * ‖ρ * (ρ + 1)‖ := by
  unfold mz hw
  have : ‖ρ * (ρ + 1)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact mul_ne_zero (NZ_ne_zero h) (NZ_add_one_ne_zero h)
  field_simp

lemma norm_le_of_NZ {ρ : ℂ} (h : NZ ρ) : ‖ρ‖ ≤ 1 + |ρ.im| := by
  have := norm_le_abs_re_add_abs_im ρ
  rw [abs_of_pos h.2.1] at this; linarith [h.2.2]

lemma norm_mul_le {ρ : ℂ} {R : ℝ} (hR : ‖ρ‖ ≤ R) : ‖ρ * (ρ + 1)‖ ≤ R * (R + 1) := by
  rw [norm_mul]
  have h1 : ‖ρ + 1‖ ≤ R + 1 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  exact mul_le_mul hR h1 (norm_nonneg _) (by linarith [norm_nonneg ρ])

/-- Nontrivial zeros of height at most `R`: `Σ m(ρ) ≤ (1 + R)(2 + R) B`, from the rectangle
sum of `hw`. -/
lemma sum_mz_low : ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ S : Finset ℂ,
    (∀ ρ ∈ S, NZ ρ ∧ |ρ.im| ≤ R) → ∑ ρ ∈ S, mz ρ ≤ (1 + R) * (2 + R) * B := by
  obtain ⟨B, hB⟩ := zero_sum_bound
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun ρ _ => hw_nonneg ρ) (hB 0 le_rfl)
  refine ⟨B, hB0, fun R hR S hS => ?_⟩
  have hsub : S ⊆ (zeros_rect_finite 2 R).toFinset := by
    intro ρ hρ
    obtain ⟨hN, hi⟩ := hS ρ hρ
    rw [Set.Finite.mem_toFinset]
    refine ⟨(mem_rect (by norm_num) hR).mpr ⟨⟨by linarith [hN.2.1], by linarith [hN.2.2]⟩,
      abs_le.mp hi⟩, hN.1⟩
  calc ∑ ρ ∈ S, mz ρ ≤ ∑ ρ ∈ S, hw ρ * ((1 + R) * (2 + R)) := by
        refine sum_le_sum fun ρ hρ => ?_
        obtain ⟨hN, hi⟩ := hS ρ hρ
        rw [mz_eq_hw hN]
        apply mul_le_mul_of_nonneg_left _ (hw_nonneg ρ)
        have := norm_mul_le (le_trans (norm_le_of_NZ hN) (by linarith : 1 + |ρ.im| ≤ 1 + R))
        linarith
    _ = (∑ ρ ∈ S, hw ρ) * ((1 + R) * (2 + R)) := by rw [sum_mul]
    _ ≤ B * ((1 + R) * (2 + R)) := by
        gcongr
        exact (sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ => hw_nonneg ρ).trans (hB R hR)
    _ = (1 + R) * (2 + R) * B := by ring

/-- **Multiplicity bound** `m(ρ) ≤ C log(‖ρ‖ + 4)`. -/
theorem mult_le : ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℂ, NZ ρ → mz ρ ≤ C * Real.log (‖ρ‖ + 4) := by
  obtain ⟨C, hC, hfib⟩ := fiber_count
  obtain ⟨B, hB0, hB⟩ := sum_mz_low
  refine ⟨4 * C + 30 * B + 1, by positivity, fun ρ hρ => ?_⟩
  have hL := one_le_log_add_four (norm_nonneg ρ)
  rcases le_or_gt |ρ.im| 4 with h4 | h4
  · have := hB 4 (by norm_num) {ρ} (by simpa using ⟨hρ, h4⟩)
    rw [sum_singleton] at this
    nlinarith [mz_nonneg ρ]
  · set n := ⌈|ρ.im|⌉₊ with hn
    have hn1 : |ρ.im| ≤ n := Nat.le_ceil _
    have hn2 : (n : ℝ) < |ρ.im| + 1 := Nat.ceil_lt_add_one (abs_nonneg _)
    have hn5 : 5 ≤ n := by
      have : (4 : ℝ) < n := lt_of_lt_of_le h4 hn1
      have : 4 < n := by exact_mod_cast this
      omega
    have hc : (n : ℝ) - 1 < |ρ.im| := by
      have := (Nat.ceil_eq_iff (by omega)).mp hn.symm
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this.1
    have := hfib n hn5 {ρ} (by simpa using ⟨hρ.1, hc, hn1⟩)
    rw [sum_singleton] at this
    have hlog : Real.log n ≤ Real.log (‖ρ‖ + 4) :=
      Real.log_le_log (by positivity) (by linarith [abs_im_le_norm ρ])
    have : mz ρ ≤ 4 * C * Real.log (‖ρ‖ + 4) := by
      unfold mz; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))]
    nlinarith [mz_nonneg ρ]

/-- A dyadic shell: zeros with `T/2 < ‖ρ‖ ≤ T`, `T ≥ 12`, have `Σ m ≤ 2 C₃ T (log T + 2)`. -/
lemma shell_count : ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ T : ℝ, 12 ≤ T → ∀ S : Finset ℂ,
    (∀ ρ ∈ S, NZ ρ ∧ T / 2 < ‖ρ‖ ∧ ‖ρ‖ ≤ T) → ∑ ρ ∈ S, mz ρ ≤ 2 * C₃ * T * (Real.log T + 2) := by
  obtain ⟨C₃, hC₃, htail⟩ := tail_count
  refine ⟨C₃, hC₃, fun T hT S hS => ?_⟩
  have h := htail (T / 2) (by linarith) S (fun ρ hρ => ⟨(hS ρ hρ).1.1, (hS ρ hρ).1.2.1,
    (hS ρ hρ).1.2.2, (hS ρ hρ).2.1⟩)
  have hlog : Real.log (T / 2) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
  calc ∑ ρ ∈ S, mz ρ ≤ ∑ ρ ∈ S, T ^ 2 * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
        refine sum_le_sum fun ρ hρ => ?_
        obtain ⟨_, h1, h2⟩ := hS ρ hρ
        have hp : 0 < ‖ρ‖ := by linarith
        have : ‖ρ‖ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hp.le h2 2
        have e : mz ρ = ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) * ‖ρ‖ ^ 2 := by
          unfold mz; field_simp
        rw [e, mul_comm (T ^ 2)]
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = T ^ 2 * ∑ ρ ∈ S, (analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2 := by rw [mul_sum]
    _ ≤ T ^ 2 * (C₃ * (Real.log (T / 2) + 1) / (T / 2)) := by gcongr
    _ = 2 * C₃ * T * (Real.log (T / 2) + 1) := by field_simp
    _ ≤ 2 * C₃ * T * (Real.log T + 2) := by gcongr; linarith

/-- **Head count** `Σ_{‖ρ‖ ≤ T} m(ρ) ≤ H T (log T + 2)` for `T ≥ 6`. -/
theorem head_count : ∃ H : ℝ, 0 ≤ H ∧ ∀ T : ℝ, 6 ≤ T → ∀ S : Finset ℂ,
    (∀ ρ ∈ S, NZ ρ ∧ ‖ρ‖ ≤ T) → ∑ ρ ∈ S, mz ρ ≤ H * T * (Real.log T + 2) := by
  obtain ⟨B, hB0, hB⟩ := sum_mz_low
  obtain ⟨C₃, hC₃, hshell⟩ := shell_count
  set H₀ := (1 + 12) * (2 + 12) * B with hH₀
  have hH₀0 : 0 ≤ H₀ := by positivity
  -- the induction on the dyadic range `T ≤ 12 · 2^k`
  have hind : ∀ k : ℕ, ∀ T : ℝ, 6 ≤ T → T ≤ 12 * 2 ^ k → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, NZ ρ ∧ ‖ρ‖ ≤ T) → ∑ ρ ∈ S, mz ρ ≤ H₀ + 8 * C₃ * T * (Real.log T + 2) := by
    intro k
    induction k with
    | zero =>
      intro T h6 hT S hS
      have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      have := hB 12 (by norm_num) S (fun ρ hρ => ⟨(hS ρ hρ).1,
        le_trans (abs_im_le_norm ρ) (le_trans (hS ρ hρ).2 (by simpa using hT))⟩)
      have : 0 ≤ 8 * C₃ * T * (Real.log T + 2) := by positivity
      linarith
    | succ k ih =>
      intro T h6 hT S hS
      rcases le_or_gt T (12 * 2 ^ k) with hk | hk
      · exact ih T h6 hk S hS
      have h12 : 12 ≤ T := le_trans (by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        linarith) hk.le
      rw [← sum_filter_add_sum_filter_not S (fun ρ => ‖ρ‖ ≤ T / 2)]
      have h1 := ih (T / 2) (by linarith) (by rw [pow_succ] at hT; linarith)
        (S.filter (fun ρ => ‖ρ‖ ≤ T / 2))
        (fun ρ hρ => by rw [mem_filter] at hρ; exact ⟨(hS ρ hρ.1).1, hρ.2⟩)
      have h2 := hshell T h12 (S.filter (fun ρ => ¬ ‖ρ‖ ≤ T / 2))
        (fun ρ hρ => by
          rw [mem_filter] at hρ
          exact ⟨(hS ρ hρ.1).1, lt_of_not_ge hρ.2, (hS ρ hρ.1).2⟩)
      have hlog : Real.log (T / 2) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
      have hl0 : 0 ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
      have hl1 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      have : 8 * C₃ * (T / 2) * (Real.log (T / 2) + 2) + 2 * C₃ * T * (Real.log T + 2)
          ≤ 8 * C₃ * T * (Real.log T + 2) := by
        have : 8 * C₃ * (T / 2) * (Real.log (T / 2) + 2) ≤ 4 * C₃ * T * (Real.log T + 2) := by
          have : 8 * C₃ * (T / 2) = 4 * C₃ * T := by ring
          rw [this]; gcongr
        nlinarith [mul_nonneg (mul_nonneg hC₃ (by linarith : (0 : ℝ) ≤ T)) hl1]
      linarith
  refine ⟨H₀ / 12 + 8 * C₃, by positivity, fun T h6 S hS => ?_⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (T / 12) (by norm_num : (1 : ℝ) < 2)
  have := hind k T h6 (by linarith) S hS
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h12 : 12 ≤ T * (Real.log T + 2) := by nlinarith
  have : H₀ ≤ H₀ / 12 * (T * (Real.log T + 2)) := by
    have : H₀ / 12 * 12 ≤ H₀ / 12 * (T * (Real.log T + 2)) := by gcongr
    linarith
  nlinarith

/-- `log(r + 4)/r` decreases: `T log(r + 4) ≤ r log(T + 4)` for `0 < T ≤ r`. -/
lemma log_ratio_le {T r : ℝ} (hT : 0 < T) (hr : T ≤ r) :
    T * Real.log (r + 4) ≤ r * Real.log (T + 4) := by
  have h1 : Real.log (r + 4) - Real.log (T + 4) ≤ (r - T) / (T + 4) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < (r + 4) / (T + 4) from div_pos (by linarith) (by linarith))
    have e : (r + 4) / (T + 4) - 1 = (r - T) / (T + 4) := by field_simp; ring
    linarith
  have hL := one_le_log_add_four hT.le
  have h2 : T * ((r - T) / (T + 4)) ≤ (r - T) * Real.log (T + 4) := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hT.le]
  nlinarith

/-- **The key zero sum.** For `0 < λ ≤ 1` and every finite set of nontrivial zeros,
`Σ m(ρ)² min(λ⁴, ‖ρ‖⁻⁴) log(‖ρ‖ + 4) ≤ C λ³ (log(1/λ) + 3)³`. -/
theorem key_sum : ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ S : Finset ℂ, (∀ ρ ∈ S, NZ ρ) →
    ∑ ρ ∈ S, mz ρ ^ 2 * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)
      ≤ C * l ^ 3 * (Real.log (1 / l) + 3) ^ 3 := by
  obtain ⟨C₁, hC₁, hm⟩ := mult_le
  obtain ⟨H, hH, hhead⟩ := head_count
  obtain ⟨C₃, hC₃, htail⟩ := tail_count
  refine ⟨C₁ * (12 * H + C₃), by positivity, fun l hl0 hl1 S hS => ?_⟩
  set T := 6 / l with hT
  have hT6 : 6 ≤ T := by rw [hT, le_div_iff₀ hl0]; linarith
  set A := Real.log (1 / l) + 3 with hA
  have hlA : 0 ≤ Real.log (1 / l) := Real.log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  set LT := Real.log (T + 4) with hLT
  have hLT1 : 1 ≤ LT := one_le_log_add_four (by linarith)
  have hLTA : LT ≤ A := by
    have : T + 4 ≤ 10 * (1 / l) := by
      rw [hT]; have : 4 ≤ 4 / l := by rw [le_div_iff₀ hl0]; linarith
      have e : 6 / l + 4 / l = 10 * (1 / l) := by ring
      linarith
    have h10 : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
      have : (10 : ℝ) < 2.7182818283 ^ 3 := by norm_num
      linarith
    calc LT ≤ Real.log (10 * (1 / l)) := Real.log_le_log (by linarith) this
      _ = Real.log 10 + Real.log (1 / l) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ A := by rw [hA]; linarith
  have hlogT : Real.log T + 2 ≤ 2 * A := by
    have : Real.log T = Real.log 6 + Real.log (1 / l) := by
      rw [hT, div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity)]
    have h6 : Real.log 6 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h.le 2
      have : (6 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      linarith
    rw [hA]; linarith
  -- pointwise: `m² ≤ C₁ m log(‖ρ‖ + 4)`
  have hpt : ∀ ρ ∈ S, mz ρ ^ 2 * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)
      ≤ C₁ * (mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ^ 2) := by
    intro ρ hρ
    have h := hm ρ (hS ρ hρ)
    have hmin : 0 ≤ min (l ^ 4) (‖ρ‖⁻¹ ^ 4) := le_min (by positivity) (by positivity)
    have hL := one_le_log_add_four (norm_nonneg ρ)
    have := mz_nonneg ρ
    have e : mz ρ ^ 2 * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)
        = mz ρ * (mz ρ * (min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4))) := by ring
    rw [e]
    have : mz ρ * (mz ρ * (min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4))) ≤
        (C₁ * Real.log (‖ρ‖ + 4)) * (mz ρ * (min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4))) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, ← sum_filter_add_sum_filter_not S (fun ρ => ‖ρ‖ ≤ T)]
  -- the head
  have hhd : ∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T),
      mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ^ 2 ≤ 12 * H * l ^ 3 * A ^ 3 := by
    calc _ ≤ ∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T), mz ρ * (l ^ 4 * LT ^ 2) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mem_filter] at hρ
          have hlog : Real.log (‖ρ‖ + 4) ≤ LT := Real.log_le_log (by positivity) (by linarith)
          have hl0' := Real.log_nonneg (show (1 : ℝ) ≤ ‖ρ‖ + 4 by linarith [norm_nonneg ρ])
          have := mz_nonneg ρ
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ this
          exact mul_le_mul (min_le_left _ _) (pow_le_pow_left₀ hl0' hlog 2) (by positivity)
            (by positivity)
      _ = (∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T), mz ρ) * (l ^ 4 * LT ^ 2) := by rw [sum_mul]
      _ ≤ (H * T * (Real.log T + 2)) * (l ^ 4 * LT ^ 2) := by
          gcongr
          exact hhead T hT6 _ (fun ρ hρ => by
            rw [mem_filter] at hρ; exact ⟨hS ρ hρ.1, hρ.2⟩)
      _ ≤ (H * T * (2 * A)) * (l ^ 4 * A ^ 2) := by gcongr
      _ = 12 * H * l ^ 3 * A ^ 3 := by rw [hT]; field_simp; ring
  -- the tail
  have htl : ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
      mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ^ 2 ≤ C₃ * l ^ 3 * A ^ 3 := by
    calc _ ≤ ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (LT / T) ^ 2 * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mem_filter] at hρ
          have hr : T < ‖ρ‖ := lt_of_not_ge hρ.2
          have hp : 0 < ‖ρ‖ := by linarith
          have hrat := log_ratio_le (by linarith) hr.le
          -- `log(r + 4)/r ≤ LT/T`
          have hq : Real.log (‖ρ‖ + 4) / ‖ρ‖ ≤ LT / T := by
            rw [div_le_div_iff₀ hp (by linarith)]; linarith
          have hq0 : 0 ≤ Real.log (‖ρ‖ + 4) / ‖ρ‖ :=
            div_nonneg (Real.log_nonneg (by linarith)) hp.le
          have hsq := pow_le_pow_left₀ hq0 hq 2
          have e : mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ^ 2
              ≤ (Real.log (‖ρ‖ + 4) / ‖ρ‖) ^ 2 * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
            have : mz ρ * (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ^ 2
                = (Real.log (‖ρ‖ + 4) / ‖ρ‖) ^ 2 * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
              unfold mz; field_simp
            rw [← this]
            have := mz_nonneg ρ
            gcongr
            exact min_le_right _ _
          exact e.trans (mul_le_mul_of_nonneg_right hsq (by positivity))
      _ = (LT / T) ^ 2 * ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2 := by rw [mul_sum]
      _ ≤ (LT / T) ^ 2 * (C₃ * (Real.log T + 1) / T) := by
          gcongr
          exact htail T hT6 _ (fun ρ hρ => by
            rw [mem_filter] at hρ
            exact ⟨(hS ρ hρ.1).1, (hS ρ hρ.1).2.1, (hS ρ hρ.1).2.2, lt_of_not_ge hρ.2⟩)
      _ ≤ (A / T) ^ 2 * (C₃ * (2 * A) / T) := by
          have h0 : 0 ≤ LT := by linarith
          have hT0 : 0 < T := by linarith
          have h1 : (LT / T) ^ 2 ≤ (A / T) ^ 2 :=
            pow_le_pow_left₀ (div_nonneg h0 hT0.le) (div_le_div_of_nonneg_right hLTA hT0.le) 2
          have h2 : C₃ * (Real.log T + 1) / T ≤ C₃ * (2 * A) / T := by
            apply div_le_div_of_nonneg_right _ hT0.le
            exact mul_le_mul_of_nonneg_left (by linarith) hC₃
          have h3 : 0 ≤ C₃ * (Real.log T + 1) / T :=
            div_nonneg (mul_nonneg hC₃ (by linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ T)]))
              hT0.le
          exact mul_le_mul h1 h2 h3 (by positivity)
      _ = C₃ * l ^ 3 * A ^ 3 / 108 := by rw [hT]; field_simp; ring
      _ ≤ C₃ * l ^ 3 * A ^ 3 := by
          have : 0 ≤ C₃ * l ^ 3 * A ^ 3 := by positivity
          linarith
  calc C₁ * (_ + _) ≤ C₁ * (12 * H * l ^ 3 * A ^ 3 + C₃ * l ^ 3 * A ^ 3) := by
        gcongr
    _ = C₁ * (12 * H + C₃) * l ^ 3 * A ^ 3 := by ring

end LeanLab.PNTPort.Selberg

