module

public import LeanLab.HardyLittlewood1923.U1503Explicit
public import LeanLab.HardyLittlewood1923.U1489TruncB

/-!
AI-written Lean code, Claude, 2026-10-23, CLOUD run 20261023T1343Z-19109, unit U-1503, paper P0004.

# Hardy-Littlewood 1923, Theorem A on `47/64 < Θ < 3/4` with no cited input

U1503Explicit proves, from Hypothesis R alone, the bound `ψ(x, χ) - [q = 1] x ≪ x^Θ (log x)³` for
primitive `χ`, hence U-1473's `PsiChiPrimBound Θ'` and U-1453's `PsiPowerLog Θ'` for every
`Θ' > Θ`. The extra `log x` costs the closed endpoint `Θ = 47/64` of U-1489: at `Θ > 47/64` the
saving `(1 - Θ')/17` of U-1453's rate still beats `3/4 - Θ` for `Θ'` close to `Θ`, exactly as in
U-1453's `printedA3_upper_of_R`, which used the cited `PsiPowerOfR` at this point.

* `psiPowerLog_of_noZeros`: `1/2 ≤ Θ < 1`, `NoZerosRight Θ`, `Θ < θ` give `PsiPowerLog θ`.
* `psiPower_of_noZeros`: the same for U-1438's `PsiPower θ`, no log factor.
* `psiPowerOfR_half`: U-1438's cited `PsiPowerOfR` for every `Θ ≥ 1/2`, PROVED. The case
  `Θ < 1/2` is not reached; it would need a nontrivial zero of `ζ` in the lab to rule out.
* `printedA3_U1503`: printed Theorem A for `r = 3`, eq. 3.113 p. 21, `47/64 < Θ < 3/4`.
* `printedA_form_all_U1503`: eq. 3.113 for every `r ≥ 3`, `47/64 < Θ < 3/4`.
Both with Hypothesis R at level `Θ` as the paper's own hypothesis and NO cited input.
Binary Goldbach is OPEN.

Packaging note: in this copy U-1438's cited Prop `PsiPowerOfR` was removed, as no compared
theorem uses it; `psiPowerOfR_half` states its content unfolded. See PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1503

open Real Finset
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight PsiPower psiPower_one sing3)
open LeanLab.HardyLittlewood1923.U1444 (singR printedA3Bound)
open LeanLab.HardyLittlewood1923.U1453 (PsiPowerLog)
open LeanLab.HardyLittlewood1923.U1463
open LeanLab.HardyLittlewood1923.U1468

/-- **Hypothesis R at level `Θ ∈ [1/2, 1)` gives `PsiPowerLog θ` for every `θ > Θ`.** -/
theorem psiPowerLog_of_noZeros {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (h1 : Θ < 1) (hZ : NoZerosRight Θ)
    {θ : ℝ} (hθ : Θ < θ) : PsiPowerLog θ :=
  U1473.psiPowerLog_of_prim (by linarith)
    (psiChiPrimBound_of_noZeros h0 h1 (U1473.noZerosRightPrim_of hZ) hθ)

/-- **The same without the log factor**: `PsiPower θ` for every `θ > Θ`. -/
theorem psiPower_of_noZeros {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (h1 : Θ < 1) (hZ : NoZerosRight Θ)
    {θ : ℝ} (hθ : Θ < θ) : PsiPower θ := by
  set θ' := (Θ + θ) / 2 with hθ'
  obtain ⟨C, hC, hb⟩ := psiPowerLog_of_noZeros h0 h1 hZ (θ := θ') (by rw [hθ']; linarith)
  set δ := (θ - θ') / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ, hθ']; linarith
  refine ⟨C / δ ^ 2, by positivity, fun x hx k l hk hc hkx ↦ (hb x hx k l hk hc hkx).trans ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : Real.log x ^ 2 ≤ (x ^ δ / δ) ^ 2 := pow_le_pow_left₀ hl0 hlog 2
  have e : x ^ θ = x ^ θ' * (x ^ δ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, hδ]
    congr 1; push_cast; ring
  have hxθ : 0 ≤ x ^ θ' := by positivity
  calc C * x ^ θ' * Real.log x ^ 2 ≤ C * x ^ θ' * (x ^ δ / δ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = C / δ ^ 2 * x ^ θ := by rw [e]; field_simp

/-- **U-1438's cited `PsiPowerOfR`, for every `Θ ≥ 1/2`, PROVED.** -/
theorem psiPowerOfR_half : ∀ Θ : ℝ, 1 / 2 ≤ Θ → NoZerosRight Θ → ∀ θ : ℝ, Θ < θ → PsiPower θ := by
  intro Θ h0 hZ θ hθ
  rcases lt_or_ge Θ 1 with h1 | h1
  · exact psiPower_of_noZeros h0 h1 hZ hθ
  · obtain ⟨C, hC, hb⟩ := psiPower_one
    refine ⟨C, hC, fun x hx k l hk hc hkx ↦ (hb x hx k l hk hc hkx).trans ?_⟩
    have : x ^ (1 : ℝ) ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left this hC

/-- **Printed Theorem A for `r = 3`, eq. 3.113 p. 21, on `47/64 < Θ < 3/4`, no cited input.** -/
theorem printedA3_U1503 :
    ∀ Θ : ℝ, 47 / 64 < Θ → Θ < 3 / 4 → NoZerosRight Θ → printedA3Bound Θ := by
  intro Θ h0 h1 hZ
  set θ := (Θ + (17 * Θ - 47 / 4)) / 2 with hθ
  have hψ := psiPowerLog_of_noZeros (by linarith) (by linarith) hZ (θ := θ) (by rw [hθ]; linarith)
  obtain ⟨K, hK, n₀, h⟩ :=
    U1453.nur3_rate_of_psiPowerLog (by rw [hθ]; linarith) (by rw [hθ]; linarith) hψ
  refine ⟨5, by norm_num, 32 * K, max n₀ 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hn3'
  have hm := h n (le_trans (le_max_left _ _) hn)
  have hexp : (n : ℝ) ^ (2 - (1 - θ) / 17) ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hθ]; linarith)
  have hl5 : (1 + Real.log n) ^ 5 ≤ 32 * Real.log n ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (1 + Real.log n) ^ 5 ≤ (2 * Real.log n) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      _ = 32 * Real.log n ^ 5 := by ring
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      ≤ K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5) := hm
    _ ≤ K * ((n : ℝ) ^ (2 + (Θ - 3 / 4)) * (32 * Real.log n ^ (5 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact mul_le_mul hexp hl5 (by positivity) (by positivity)
    _ = 32 * K * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ (5 : ℝ) := by ring

/-- **Printed Theorem A, eq. 3.113 p. 21, every `r ≥ 3`, every large `n`, `47/64 < Θ < 3/4`, on
the paper's Hypothesis R at level `Θ`, with NO cited input.** The final assembly is U-1489's
`printedA_form_all_U1489` with `PsiPowerLog θ` at `θ = 9Θ - 47/8` in place of `Θ`. -/
theorem printedA_form_all_U1503 :
    ∀ r : ℕ, 3 ≤ r → ∀ Θ : ℝ, 47 / 64 < Θ → Θ < 3 / 4 → NoZerosRight Θ →
      ∃ B : ℕ, ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        |nur r n - (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n| ≤
          K * (n : ℝ) ^ ((r : ℝ) - 1 + (Θ - 3 / 4)) * Real.log n ^ B := by
  intro r hr Θ h0 h1 hZ
  set θ := (Θ + (17 * Θ - 47 / 4)) / 2 with hθ
  have hψ := psiPowerLog_of_noZeros (by linarith) (by linarith) hZ (θ := θ) (by rw [hθ]; linarith)
  obtain ⟨B₀, hA⟩ : ∃ B : ℕ, APow r (Θ - 3 / 4) B :=
    apow_all (θ := θ) (by rw [hθ]; linarith) (by rw [hθ]; linarith) hψ
      (apow_three_of_bound (printedA3_U1503 Θ h0 h1 hZ)) r hr
  obtain ⟨K, hK, n₀, hn⟩ := apow_mono (le_max_left B₀ r) hA
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  refine ⟨max B₀ (s + 2), K + 3 * (s + 2) * 2 ^ s, max n₀ 3, fun n hn' => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL1 := one_le_log_of_three hn3
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) := by positivity
  have hZ0 : 0 ≤ Real.log n ^ max B₀ (s + 2) := by positivity
  by_cases hpar : n % 2 = (s + 2) % 2
  · rw [← Mr_eq_printed_pos hr (by omega) hpar]
    refine (hn n hpar (le_trans (le_max_left _ _) hn')).trans ?_
    have : 0 ≤ 3 * (s + 2 : ℝ) * 2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    nlinarith
  · rw [(singRProductPos (s + 2) hr n (by omega)).2 hpar, mul_zero, sub_zero,
      abs_of_nonneg (nur_nonneg _ _)]
    refine (nur_unlike_le s n hpar).trans ?_
    have q1 : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) s
    have q2 : (n : ℝ) ^ s ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) :=
      npow_le_rpow (by omega) (by push_cast; linarith)
    have q3 : Real.log n ^ (s + 2) ≤ Real.log n ^ max B₀ (s + 2) :=
      log_pow_mono hn3 (le_max_right _ _)
    have hKY : 0 ≤ K * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    calc 3 * ((s : ℝ) + 2) * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 2)
        ≤ 3 * ((s : ℝ) + 2) * (2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4))) *
            Real.log n ^ max B₀ (s + 2) := by
          gcongr
          exact q1.trans (mul_le_mul_of_nonneg_left q2 (by positivity))
      _ ≤ (K + 3 * (s + 2) * 2 ^ s) * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
            Real.log n ^ max B₀ (s + 2) := by
          linarith only [hKY]

/-! ### Vacuity -/

/-- The range of the headline is not empty, and the analytic input's range `1/2 ≤ Θ < 1`
contains it. -/
theorem range_nonvacuous : (47 : ℝ) / 64 < 95 / 128 ∧ (95 : ℝ) / 128 < 3 / 4 ∧
    (1 : ℝ) / 2 ≤ 95 / 128 := by norm_num

end LeanLab.HardyLittlewood1923.U1503
