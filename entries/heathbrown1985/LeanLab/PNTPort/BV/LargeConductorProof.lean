module

public import LeanLab.PNTPort.BV.LCAux
public import LeanLab.PNTPort.BV.Helpers

/-!
lab proof, AI wrote this file, known mathematics, no cited input

# The large conductor estimate

`largeConductor : LargeConductor`: for every `A > 0`, with `C₁ = B = A + 5`,

  `∑_{(log x)^C₁ < d ≤ √x/(log x)^B} φ(d)⁻¹ ∑*_{χ mod d} ‖ψ(x, χ)‖ ≪_A x / (log x)^A`.

Route (Vaughan's proof of Bombieri-Vinogradov): Vaughan's identity with `u = v = ⌊x^{1/10}⌋`,
Pólya-Vinogradov for the Type I sums (`typeI_total`), the hyperbolic bilinear large sieve with
dyadic blocks in the modulus for the Type II sum (`typeII_total`), and the trivial bound
when `log x < 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction
open LeanLab.PNTPort.LargeSieve (primIdx)

lemma norm_psiChi_le_trivial {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) :
    ‖psiChi x χ‖ ≤ 6 * x := by
  unfold psiChi
  have h1 : ‖∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) * χ (n : ZMod q)‖ ≤
      ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one _ _)
  have h2 : ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n = Chebyshev.psi x := by
    rw [Chebyshev.psi]; congr 1
  have h3 := Chebyshev.psi_le_const_mul_self hx
  have h4 : Real.log 4 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [h2] at h1
  nlinarith

/-- The range `log x < 1`, by the trivial bound. -/
lemma small_case {A B C₁ : ℝ} (hA : 0 < A) (hB : 0 < B) {x : ℝ} (hx : 2 ≤ x)
    (hL : Real.log x < 1) :
    ∑ p ∈ (primSigma ⌊Real.sqrt x / Real.log x ^ B⌋₊).filter
        (fun p => Real.log x ^ C₁ < p.1), ‖psiChi x p.2‖ / p.1.totient ≤
      12 / Real.log 2 ^ B * x / Real.log x ^ A := by
  set L := Real.log x
  set Q := ⌊Real.sqrt x / L ^ B⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hLB : Real.log 2 ^ B ≤ L ^ B := Real.rpow_le_rpow hl2.le hL2 hB.le
  have hl2B : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hl2 B
  have hLA : L ^ A ≤ 1 := Real.rpow_le_one hL0.le hL.le hA.le
  have hLA0 : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hxe : x < 4 := by
    have := Real.exp_log (show 0 < x by linarith)
    have h1 : Real.exp L < Real.exp 1 := Real.exp_lt_exp.2 hL
    have := Real.exp_one_lt_d9
    linarith
  have hs : Real.sqrt x ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hQ : (Q : ℝ) ≤ 2 / Real.log 2 ^ B := by
    refine (Nat.floor_le (by positivity)).trans ?_
    exact div_le_div₀ (by norm_num) hs hl2B hLB
  calc _ ≤ ∑ p ∈ (primSigma Q).filter (fun p => L ^ C₁ < p.1), (6 * x) / (p.1.totient : ℝ) :=
        sum_le_sum fun p _ => div_le_div_of_nonneg_right (norm_psiChi_le_trivial x p.2 hx0)
          (by positivity)
    _ ≤ Q * (6 * x) := sum_inv_totient_primSigma_le Q _ (by positivity)
    _ ≤ 2 / Real.log 2 ^ B * (6 * x) := mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = 12 / Real.log 2 ^ B * x := by ring
    _ ≤ 12 / Real.log 2 ^ B * x / L ^ A := by
        rw [le_div_iff₀ hLA0]
        exact mul_le_of_le_one_right (by positivity) hLA

/-- Vaughan's decomposition, in norm. -/
lemma norm_psiChi_le_parts {q : ℕ} (x : ℝ) {w : ℕ} (hw : 1 ≤ w) (χ : DirichletCharacter ℂ q) :
    ‖psiChi x χ‖ ≤ (‖S1 x w χ‖ + ‖S2 x w w χ‖ + ‖S3 x w χ‖) + ‖S4 x w w χ‖ := by
  rw [psiChi_decomp x w w χ hw]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact norm_sub_le _ _

/-- The Type I numerics. -/
lemma typeI_arith {x y L Q w : ℝ} (hy : 1 ≤ y) (hL : 0 ≤ L) (_hQ0 : 0 ≤ Q) (hQ : Q ≤ y ^ 10)
    (hsQ : Real.sqrt Q ≤ y ^ 5) (hlQ : Real.log Q ≤ L) (hlQ0 : 0 ≤ Real.log Q)
    (hw0 : 0 ≤ w) (hw : w ≤ y ^ 2) (hxy : x = y ^ 20) :
    Q * ((Real.log 4 + 4) * w + 3 * (w * w + w) * L * (Real.sqrt Q * (1 + Real.log Q))) ≤
      6 * (2 + L) ^ 2 * (x / y) := by
  have hl4 : Real.log 4 + 4 ≤ 6 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hl40 : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hy0 : 0 < y := by linarith
  have hxy' : x / y = y ^ 19 := by rw [hxy, div_eq_iff hy0.ne']; ring
  have hww : w * w + w ≤ 2 * y ^ 4 := by
    have : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
    nlinarith
  have h29 : y ^ 2 ≤ y ^ 9 := pow_le_pow_right₀ hy (by norm_num)
  calc _ ≤ y ^ 10 * (6 * y ^ 2 + 3 * (2 * y ^ 4) * L * (y ^ 5 * (1 + L))) := by
        gcongr
    _ ≤ y ^ 10 * (6 * y ^ 9 * (2 + L) ^ 2) := by
        gcongr
        have e : 3 * (2 * y ^ 4) * L * (y ^ 5 * (1 + L)) = 6 * y ^ 9 * (L * (1 + L)) := by ring
        rw [e]
        have : 6 * y ^ 2 ≤ 6 * y ^ 9 := by linarith
        have h9 : 0 ≤ y ^ 9 := by positivity
        nlinarith [mul_nonneg h9 hL, mul_nonneg h9 (mul_nonneg hL hL)]
    _ = _ := by rw [hxy']; ring

set_option maxHeartbeats 1000000 in
/-- The range `log x ≥ 1`. -/
lemma main_case {A K₂ K₃ : ℝ} (hA : 0 < A) (hK₂ : 0 < K₂) (hK₃ : 0 < K₃)
    (hII : ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → ∀ R : ℕ, 1 ≤ R →
      ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 x w w i.2‖ ≤
        K₂ * (2 + Real.log x) ^ 4 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x))
    (hlog : ∀ x : ℝ, 2 ≤ x → Real.log x ^ (A + 5) ≤ K₃ * x ^ (1 / 20 : ℝ))
    {x : ℝ} (hx : 2 ≤ x) (hL1 : 1 ≤ Real.log x) :
    ∑ p ∈ (primSigma ⌊Real.sqrt x / Real.log x ^ (A + 5)⌋₊).filter
        (fun p => Real.log x ^ (A + 5) < p.1), ‖psiChi x p.2‖ / p.1.totient ≤
      (1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃) * x / Real.log x ^ A := by
  set L := Real.log x with hLdef
  set U := L ^ (A + 5) with hUdef
  set Q := ⌊Real.sqrt x / U⌋₊ with hQdef
  set P := L ^ A with hPdef
  set ℓ := 2 + L with hℓ
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 A
  have hU : U = P * L ^ 5 := by
    rw [hUdef, Real.rpow_add hL0, hPdef]
    congr 1
    exact_mod_cast Real.rpow_natCast L 5
  have hU1 : 1 ≤ U := Real.one_le_rpow hL1 (by linarith)
  have hU0 : 0 < U := by linarith
  have hKpos : 0 ≤ (1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃) * x / P := by positivity
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · have : primSigma Q = ∅ := by rw [hQ0]; rfl
    rw [this, filter_empty, sum_empty]; exact hKpos
  have hQ1 : 1 ≤ Q := hQpos
  -- y = x^{1/20}, w = ⌊y²⌋
  set y := x ^ (1 / 20 : ℝ) with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by norm_num)
  have hy0 : 0 < y := by linarith
  have hxy : x = y ^ 20 := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hsx : Real.sqrt x = y ^ 10 := by
    rw [hxy, show y ^ 20 = (y ^ 10) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set w := ⌊y ^ 2⌋₊ with hwdef
  have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
  have hw1 : 1 ≤ w := Nat.le_floor (by exact_mod_cast hy2)
  have hwle : (w : ℝ) ≤ y ^ 2 := Nat.floor_le (by positivity)
  have hwge : y ^ 2 / 2 ≤ w := by
    have h1 := Nat.lt_floor_add_one (y ^ 2)
    have h2 : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    rw [← hwdef] at h1
    linarith
  have hω : y / 2 ≤ Real.sqrt w := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  have hxω : x / Real.sqrt w ≤ 2 * (x / y) := by
    calc x / Real.sqrt w ≤ x / (y / 2) := div_le_div_of_nonneg_left hx0 (by positivity) hω
      _ = 2 * (x / y) := by field_simp
  -- Q
  have hQle : (Q : ℝ) ≤ Real.sqrt x / U := Nat.floor_le (by positivity)
  have hQs : (Q : ℝ) ≤ Real.sqrt x := hQle.trans (div_le_self (Real.sqrt_nonneg _) hU1)
  have hQx : (Q : ℝ) ≤ x := by
    refine hQs.trans ?_
    rw [Real.sqrt_le_left hx0]; nlinarith
  have hQsx : (Q : ℝ) * Real.sqrt x ≤ x / U := by
    calc (Q : ℝ) * Real.sqrt x ≤ Real.sqrt x / U * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hQle (Real.sqrt_nonneg _)
      _ = x / U := by
          rw [div_mul_eq_mul_div, Real.mul_self_sqrt hx0]
  have hsQ : Real.sqrt Q ≤ y ^ 5 := by
    rw [show y ^ 5 = Real.sqrt ((y ^ 5) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    calc (Q : ℝ) ≤ Real.sqrt x := hQs
      _ = (y ^ 5) ^ 2 := by rw [hsx]; ring
  have hlQ : Real.log Q ≤ L := log_nat_le (by linarith) hQx
  -- decomposition
  have hsplit : ∑ p ∈ (primSigma Q).filter (fun p => U < p.1), ‖psiChi x p.2‖ / p.1.totient ≤
      ∑ p ∈ (primSigma Q).filter (fun p => U < p.1),
        (‖S1 x w p.2‖ + ‖S2 x w w p.2‖ + ‖S3 x w p.2‖) / (p.1.totient : ℝ) +
      ∑ p ∈ (primSigma Q).filter (fun p => U < p.1), ‖S4 x w w p.2‖ / (p.1.totient : ℝ) := by
    rw [← sum_add_distrib]
    apply sum_le_sum; intro p _
    rw [← add_div]
    exact div_le_div_of_nonneg_right (norm_psiChi_le_parts x hw1 p.2) (by positivity)
  refine hsplit.trans ?_
  have hTI := typeI_total hx hw1 Q hU1
  have hTII := typeII_total hK₂ hII hx hw1 hQ1 hU1
  -- Type I numerics
  have hTI' : (Q : ℝ) * ((Real.log 4 + 4) * w + 3 * ((w * w + w : ℕ) : ℝ) * L *
        (Real.sqrt Q * (1 + Real.log Q))) ≤ 6 * ℓ ^ 2 * (x / y) := by
    push_cast
    exact typeI_arith hy1 hL0.le (by positivity) (by rw [← hsx]; exact hQs) hsQ hlQ
      (Real.log_natCast_nonneg Q) (by positivity) hwle hxy
  -- Type II numerics
  have hJ : ((Nat.log 2 Q + 1 : ℕ) : ℝ) ≤ 2 * ℓ := by
    have := natLog_two_le hQ1 hQx
    push_cast; rw [hℓ]; linarith
  have hTII' : ((Nat.log 2 Q + 1 : ℕ) : ℝ) * (K₂ * (2 + Real.log x) ^ 4 *
        (x / U + 2 * x / Real.sqrt w + 2 * Q * Real.sqrt x)) ≤
      2 * K₂ * ℓ ^ 5 * (3 * (x / U) + 4 * (x / y)) := by
    have hin : x / U + 2 * x / Real.sqrt w + 2 * Q * Real.sqrt x ≤ 3 * (x / U) + 4 * (x / y) := by
      have : 2 * x / Real.sqrt w = 2 * (x / Real.sqrt w) := by ring
      rw [this]; nlinarith
    calc _ ≤ (2 * ℓ) * (K₂ * ℓ ^ 4 * (3 * (x / U) + 4 * (x / y))) := by
          apply mul_le_mul hJ _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hin (by positivity)
      _ = _ := by ring
  -- final numerics
  have hℓ3 : ℓ ≤ 3 * L := by rw [hℓ]; linarith
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hℓ5 : ℓ ^ 5 ≤ 243 * L ^ 5 := by
    calc ℓ ^ 5 ≤ (3 * L) ^ 5 := pow_le_pow_left₀ (by linarith) hℓ3 5
      _ = 243 * L ^ 5 := by ring
  have hL5 : 0 < L ^ 5 := by positivity
  have hyP : L ^ 5 * P ≤ K₃ * y := by
    have := hlog x hx
    rw [← hUdef, hU] at this; linarith
  set E := x / P with hE
  have hE0 : 0 ≤ E := by positivity
  have f1 : ℓ ^ 5 * (x / U) ≤ 243 * E := by
    calc ℓ ^ 5 * (x / U) ≤ 243 * L ^ 5 * (x / U) :=
          mul_le_mul_of_nonneg_right hℓ5 (by positivity)
      _ = 243 * E := by rw [hU, hE]; field_simp
  have f2 : L ^ 5 * (x / y) ≤ K₃ * E := by
    rw [hE, mul_div_assoc', div_le_iff₀ hy0]
    rw [show K₃ * (x / P) * y = x * (K₃ * y) / P by ring, le_div_iff₀ hP0]
    have h := mul_le_mul_of_nonneg_left hyP hx0
    linarith
  have f3 : ℓ ^ 5 * (x / y) ≤ 243 * K₃ * E := by
    calc ℓ ^ 5 * (x / y) ≤ 243 * L ^ 5 * (x / y) :=
          mul_le_mul_of_nonneg_right hℓ5 (by positivity)
      _ = 243 * (L ^ 5 * (x / y)) := by ring
      _ ≤ 243 * (K₃ * E) := mul_le_mul_of_nonneg_left f2 (by norm_num)
      _ = _ := by ring
  have f4 : ℓ ^ 2 * (x / y) ≤ ℓ ^ 5 * (x / y) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hℓ1 (by norm_num)) (by positivity)
  have hfin : 6 * ℓ ^ 2 * (x / y) + 2 * K₂ * ℓ ^ 5 * (3 * (x / U) + 4 * (x / y)) ≤
      (1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃) * x / P := by
    have e : (1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃) * x / P =
        6 * (243 * K₃ * E) + 2 * K₂ * (3 * (243 * E) + 4 * (243 * K₃ * E)) := by
      rw [hE]; ring
    rw [e]
    have g1 : 6 * ℓ ^ 2 * (x / y) ≤ 6 * (243 * K₃ * E) := by linarith
    have g2 : 2 * K₂ * ℓ ^ 5 * (3 * (x / U) + 4 * (x / y)) =
        2 * K₂ * (3 * (ℓ ^ 5 * (x / U)) + 4 * (ℓ ^ 5 * (x / y))) := by ring
    have g3 : 2 * K₂ * (3 * (ℓ ^ 5 * (x / U)) + 4 * (ℓ ^ 5 * (x / y))) ≤
        2 * K₂ * (3 * (243 * E) + 4 * (243 * K₃ * E)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  linarith

/-- **The large conductor estimate**, the analytic heart of Bombieri-Vinogradov. -/
theorem largeConductor : LargeConductor := by
  intro A hA
  obtain ⟨K₂, hK₂, hII⟩ := typeII_bound
  obtain ⟨K₃, hK₃, hlog⟩ := log_rpow_le_rpow (A + 5) (1 / 20) (by norm_num)
  refine ⟨A + 5, A + 5, (1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃) +
    12 / Real.log 2 ^ (A + 5), by linarith, ?_⟩
  intro x hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hs0 : 0 ≤ 12 / Real.log 2 ^ (A + 5) := by
    have := Real.rpow_pos_of_pos hl2 (A + 5); positivity
  have hm0 : 0 ≤ 1458 * K₃ + 1458 * K₂ + 1944 * K₂ * K₃ := by positivity
  have hx0 : 0 ≤ x := by linarith
  rcases lt_or_ge (Real.log x) 1 with hL | hL
  · refine (small_case hA (by linarith) hx hL).trans ?_
    rw [div_le_div_iff_of_pos_right hLA]
    nlinarith
  · refine (main_case hA hK₂ hK₃ hII hlog hx hL).trans ?_
    rw [div_le_div_iff_of_pos_right hLA]
    nlinarith

end LeanLab.PNTPort.BV

