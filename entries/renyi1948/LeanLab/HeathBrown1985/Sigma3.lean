module

public import Mathlib
public import LeanLab.HeathBrown1985.Theorem1Chain
public import LeanLab.HeathBrown1985.DivisorEps
public import LeanLab.HeathBrown1985.Bound24

/-!
P0096 Heath-Brown 1985, pages 55 to 56, the bound `Σ₃² ≪ x⁴ L¹³ Q⁻¹`, `BoundSigma3`.
PROVED here: the crude bound `Σ₃ ≤ 3x (3x)² 3x log 3x (Q³ + log 3x)`, `sigma3_crude`; the
reduction of `BoundSigma3` to large `x`, `boundSigma3_of_eventually`; the support fact
`r < 3 Q²` for nonzero terms of `S₃`, `S3_term_support`.
NOT IN THIS COPY: the lab placeholder `sigma3_eventually_of_siegelWalfisz`, the dyadic, Cauchy, diagonal 3.6 and
off-diagonal 3.8 argument of pages 55 to 56 for large `x`.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

theorem log_natCast_le_of_le (k : ℕ) (y : ℝ) (hy : 1 ≤ y) (hk : (k : ℝ) ≤ y) :
    Real.log k ≤ Real.log y := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hy
  · exact Real.log_le_log (by exact_mod_cast h) hk

/-- The crude bound `Σ₃ ≤ 3x · (3x)² · 3x log 3x (Q³ + log 3x)`. -/
theorem sigma3_crude (x Q : ℝ) (hx : 1 ≤ x) (hQ : 0 ≤ Q) :
    Sigma3 x Q ≤
      3 * x * ((3 * x) ^ 2 * (3 * x * Real.log (3 * x) * (Q ^ 3 + Real.log (3 * x)))) := by
  have hx0 : 0 < x := by linarith
  have h3x : 1 ≤ 3 * x := by linarith
  have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg h3x
  set N := ⌊3 * x⌋₊ with hN
  have hNR : (N : ℝ) ≤ 3 * x := Nat.floor_le (by linarith)
  set T := 3 * x * Real.log (3 * x) * (Q ^ 3 + Real.log (3 * x)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hper : ∀ m ∈ mRange x, |S3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ N (fm x Q m)| ≤ (3 * x) ^ 2 * T := by
    intro m hm
    simp only [mRange, mem_filter, mem_Icc] at hm
    have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm.1.2) hNR
    unfold S3
    have hpt : ∀ r ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
        |(if ⌊Q⌋₊ < r ∧ ⌊x / Q ^ 2⌋₊ < n ∧ r * n ≤ N then
          dr ⌊Q⌋₊ r * Λ n * fm x Q m (r * n) else 0)| ≤ T := by
      intro r hr n hn
      have hrR : (r : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast (mem_Icc.mp hr).2) hNR
      have hnR : (n : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast (mem_Icc.mp hn).2) hNR
      split_ifs
      · rw [abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have h1 : |dr ⌊Q⌋₊ r| ≤ 3 * x := (abs_dr_le _ r).trans
          (le_trans (by exact_mod_cast Nat.card_divisors_le_self r) hrR)
        have h2 : Λ n ≤ Real.log (3 * x) := vonMangoldt_le_log_of_le n _ h3x hnR
        have h3 : |fm x Q m (r * n)| ≤ Q ^ 3 + Real.log (3 * x) := by
          unfold fm
          split_ifs
          · refine (abs_DeltaQ_le_cube_log Q hQ _).trans ?_
            exact add_le_add le_rfl (log_natCast_le_of_le _ _ h3x
              (le_trans (by exact_mod_cast Nat.sub_le m (r * n)) hmR))
          · simp only [abs_zero]; positivity
        rw [hT]
        have := mul_le_mul h1 h2 ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        exact mul_le_mul this h3 (abs_nonneg _) (by positivity)
      · simp only [abs_zero]; exact hT0
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hin : ∀ r ∈ Icc 1 N, |∑ n ∈ Icc 1 N,
        (if ⌊Q⌋₊ < r ∧ ⌊x / Q ^ 2⌋₊ < n ∧ r * n ≤ N then
          dr ⌊Q⌋₊ r * Λ n * fm x Q m (r * n) else 0)| ≤ 3 * x * T := by
      intro r hr
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum (hpt r hr)).trans ?_
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_right hNR hT0
    refine (sum_le_sum hin).trans ?_
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    calc (N : ℝ) * (3 * x * T) ≤ 3 * x * (3 * x * T) :=
          mul_le_mul_of_nonneg_right hNR (by positivity)
      _ = (3 * x) ^ 2 * T := by ring
  unfold Sigma3
  refine (sum_le_sum hper).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_mRange_le x hx0.le) (by positivity)

/-- Support of `S₃`: a nonzero term has `n > v = ⌊x/Q²⌋` and `rn ≤ 3x`, so `r < 3Q²`. -/
theorem S3_term_support (x Q : ℝ) (hx : 0 < x) (hQ : 0 < Q) (r n : ℕ)
    (hn : ⌊x / Q ^ 2⌋₊ < n) (hrn : r * n ≤ ⌊3 * x⌋₊) : (r : ℝ) < 3 * Q ^ 2 := by
  have hn' : x / Q ^ 2 < n := Nat.lt_of_floor_lt hn
  have hrn' : (r : ℝ) * n ≤ 3 * x :=
    le_trans (by exact_mod_cast hrn) (Nat.floor_le (by linarith))
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hxn : x < n * Q ^ 2 := by rwa [div_lt_iff₀ hQ2] at hn'
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn'
  by_contra h
  push Not at h
  have : 3 * x < (r : ℝ) * n := by nlinarith
  linarith

/-- Reduction: the bound for large `x` gives `BoundSigma3`, via `sigma3_crude` on `[2, X₀]`. -/
theorem boundSigma3_of_eventually
    (h : ∀ B : ℝ, 0 < B → ∃ K X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      Sigma3 x (Real.log x ^ B) ^ 2 ≤ K * x ^ 4 * Real.log x ^ 13 / Real.log x ^ B) :
    BoundSigma3 := by
  intro B hB
  obtain ⟨K, X0, hK⟩ := h B hB
  set X1 := max X0 2
  have hX1 : 2 ≤ X1 := le_max_right _ _
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set E := Real.log X1 ^ B
  have hlX1 : l2 ≤ Real.log X1 := Real.log_le_log (by norm_num) hX1
  have hE : 0 < E := Real.rpow_pos_of_pos (by linarith) _
  set D := 3 * X1 * ((3 * X1) ^ 2 * (3 * X1 * Real.log (3 * X1) *
      (E ^ 3 + Real.log (3 * X1))))
  have hl3X1 : 0 ≤ Real.log (3 * X1) := Real.log_nonneg (by linarith)
  have hD : 0 ≤ D := by positivity
  refine ⟨max |K| (D ^ 2 * E / (16 * l2 ^ 13)), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hLB : 0 < L ^ B := Real.rpow_pos_of_pos hL0 _
  have eR : max |K| (D ^ 2 * E / (16 * l2 ^ 13)) * x ^ 4 * L ^ 13 / L ^ B =
      max |K| (D ^ 2 * E / (16 * l2 ^ 13)) * (x ^ 4 * L ^ 13 / L ^ B) := by ring
  rw [eR]
  have hF : 0 ≤ x ^ 4 * L ^ 13 / L ^ B := by positivity
  rcases le_or_gt X1 x with hxX | hxX
  · have h1 := hK x (le_trans (le_max_left _ _) hxX)
    have eK : K * x ^ 4 * L ^ 13 / L ^ B = K * (x ^ 4 * L ^ 13 / L ^ B) := by ring
    rw [eK] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hF)
    exact (le_abs_self K).trans (le_max_left _ _)
  · -- small `x`: `2 ≤ x < X₁`
    have hLX : L ≤ Real.log X1 := Real.log_le_log hx0 hxX.le
    have hQE : L ^ B ≤ E := Real.rpow_le_rpow hL0.le hLX hB.le
    have hl3 : Real.log (3 * x) ≤ Real.log (3 * X1) := Real.log_le_log (by linarith) (by linarith)
    have hl30 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    have hcr := sigma3_crude x (L ^ B) (by linarith) hLB.le
    have hSD : Sigma3 x (L ^ B) ≤ D := by
      refine hcr.trans ?_
      have hA : (L ^ B) ^ 3 + Real.log (3 * x) ≤ E ^ 3 + Real.log (3 * X1) := by
        gcongr
      have hB3 : 3 * x * Real.log (3 * x) ≤ 3 * X1 * Real.log (3 * X1) := by
        gcongr
      have hC := mul_le_mul hB3 hA (by positivity) (by positivity)
      have hC2 : (3 * x) ^ 2 ≤ (3 * X1) ^ 2 := by gcongr
      have hC3 := mul_le_mul hC2 hC (by positivity) (by positivity)
      exact mul_le_mul (by linarith) hC3 (by positivity) (by positivity)
    have hS0 : 0 ≤ Sigma3 x (L ^ B) := sum_nonneg (fun _ _ => abs_nonneg _)
    have hsq : Sigma3 x (L ^ B) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hS0 hSD 2
    refine hsq.trans ?_
    have hx4 : 16 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg x]
    have hL13 : l2 ^ 13 ≤ L ^ 13 := pow_le_pow_left₀ hl2.le hL2 13
    have hF' : 16 * l2 ^ 13 / E ≤ x ^ 4 * L ^ 13 / L ^ B := by
      rw [div_le_div_iff₀ hE hLB]
      have := mul_le_mul hx4 hL13 (by positivity) (by positivity)
      calc 16 * l2 ^ 13 * L ^ B ≤ x ^ 4 * L ^ 13 * L ^ B :=
            mul_le_mul_of_nonneg_right this hLB.le
        _ ≤ x ^ 4 * L ^ 13 * E := by gcongr
    calc D ^ 2 = D ^ 2 * E / (16 * l2 ^ 13) * (16 * l2 ^ 13 / E) := by
          field_simp
      _ ≤ max |K| (D ^ 2 * E / (16 * l2 ^ 13)) * (x ^ 4 * L ^ 13 / L ^ B) :=
          mul_le_mul (le_max_right _ _) hF' (by positivity) (by positivity)

/-- The Cauchy step 3.5 in abstract form: `(Σ w |a|)² ≤ (Σ w²)(Σ a²)`. -/
theorem cauchy_abs {ι : Type*} (s : Finset ι) (w a : ι → ℝ) :
    (∑ i ∈ s, w i * |a i|) ^ 2 ≤ (∑ i ∈ s, w i ^ 2) * ∑ i ∈ s, a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s w (fun i => |a i|)
  simpa only [sq_abs] using h


end LeanLab.HeathBrown1985
