module

public import LeanLab.PNTPort.BV.TypeIIAux
public import LeanLab.PNTPort.BV.Hyperbolic

/-!
lab proof, AI wrote this file, known mathematics, no cited input

# The Type II estimate for the Vaughan sum `S₄`

`typeII_bound`: there is an absolute `K` with, for `x ≥ 2`, `w ≥ 1`, `R ≥ 1`,

  `∑_{q ≤ R} q/φ(q) ∑*_{χ mod q} ‖S₄(x, w, w, χ)‖ ≤ K (2 + log x)⁴ (x + R x / √w + R² √x)`.

Route: dyadic blocks in the first variable (`S4_eq_blocks`), the hyperbolic bilinear
large sieve on each block, Chebyshev's bound for `Λ` and `∑ d(n)² ≪ N log³ N` for `g_v`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction
open LeanLab.PNTPort.LargeSieve (primIdx)

lemma blk_arith {C₀ c x ℓ L lg M N₂ R w Sa Sb A1 B1 : ℝ} (hC₀ : 0 < C₀) (hc : 0 ≤ c)
    (hx : 1 ≤ x) (hℓ : 1 ≤ ℓ) (hM : 0 ≤ M) (hN : 0 ≤ N₂) (hR : 0 ≤ R) (hw : 0 < w)
    (hSa0 : 0 ≤ Sa) (hSb0 : 0 ≤ Sb) (_hA0 : 0 ≤ A1) (hB0 : 0 ≤ B1)
    (hSa : Sa ≤ 2 * c * ℓ * M) (hSb : Sb ≤ 2 * N₂ * ℓ ^ 3)
    (hA : A1 ≤ 2 * c * M) (hB : B1 ≤ 2 * N₂ * ℓ ^ 3)
    (hMN : M * N₂ ≤ x) (hMw : M * w ≤ x) (hNw : N₂ * w ≤ x)
    (hlg : 1 + L + lg ≤ 3 * ℓ) :
    C₀ * (1 + L + lg) * Real.sqrt (((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb)) +
      C₀ * R ^ 2 * A1 * B1 / x ≤
      (24 * C₀ * Real.sqrt c + 4 * C₀ * c) * ℓ ^ 3 *
        (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by
  have hsq := sqrt_block_le hM hN hR hw hc (by linarith) hSa0 hSb0 hSa hSb hMN hMw hNw
  have hs1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hω : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hsc := Real.sqrt_nonneg c
  set G := x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x with hG
  have hG0 : 0 ≤ R * x / Real.sqrt w := by positivity
  have hRs : R ^ 2 ≤ R ^ 2 * Real.sqrt x := le_mul_of_one_le_right (by positivity) hs1
  have hGx : x + 4 * R * x / Real.sqrt w + 4 * R ^ 2 * Real.sqrt x ≤ 4 * G := by
    rw [hG]; have : 4 * R * x / Real.sqrt w = 4 * (R * x / Real.sqrt w) := by ring
    rw [this]; nlinarith
  have hsqP := Real.sqrt_nonneg (((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb))
  have t1 : C₀ * (1 + L + lg) * Real.sqrt (((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb)) ≤
      24 * C₀ * Real.sqrt c * ℓ ^ 3 * G := by
    have hlg0 : 0 ≤ 1 + L + lg ∨ 1 + L + lg < 0 := le_or_gt 0 _
    rcases hlg0 with h0 | h0
    · calc _ ≤ C₀ * (3 * ℓ) * (2 * Real.sqrt c * ℓ ^ 2 * (4 * G)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hlg hC₀.le) (hsq.trans
              (mul_le_mul_of_nonneg_left hGx (by positivity))) hsqP (by positivity)
        _ = _ := by ring
    · have : C₀ * (1 + L + lg) * Real.sqrt (((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hC₀.le h0.le) hsqP
      have : 0 ≤ 24 * C₀ * Real.sqrt c * ℓ ^ 3 * G := by rw [hG]; positivity
      linarith
  have t2 : C₀ * R ^ 2 * A1 * B1 / x ≤ 4 * C₀ * c * ℓ ^ 3 * G := by
    have hx0 : 0 < x := by linarith
    rw [div_le_iff₀ hx0]
    have e1 : A1 * B1 ≤ (2 * c * M) * (2 * N₂ * ℓ ^ 3) := mul_le_mul hA hB hB0 (by positivity)
    have e2 : (2 * c * M) * (2 * N₂ * ℓ ^ 3) ≤ 4 * c * ℓ ^ 3 * x := by
      have : (2 * c * M) * (2 * N₂ * ℓ ^ 3) = 4 * c * ℓ ^ 3 * (M * N₂) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hMN (by positivity)
    have e3 : R ^ 2 ≤ G := by rw [hG]; nlinarith
    calc C₀ * R ^ 2 * A1 * B1 = C₀ * R ^ 2 * (A1 * B1) := by ring
      _ ≤ C₀ * R ^ 2 * (4 * c * ℓ ^ 3 * x) :=
          mul_le_mul_of_nonneg_left (e1.trans e2) (by positivity)
      _ = 4 * C₀ * c * ℓ ^ 3 * x * R ^ 2 := by ring
      _ ≤ 4 * C₀ * c * ℓ ^ 3 * x * G := mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = _ := by ring
  calc _ ≤ 24 * C₀ * Real.sqrt c * ℓ ^ 3 * G + 4 * C₀ * c * ℓ ^ 3 * G := add_le_add t1 t2
    _ = _ := by ring


lemma log_two_mul_le {x : ℝ} (hx : 1 ≤ x) {y : ℝ} (hy0 : 1 ≤ y) (hy : y ≤ 2 * x) :
    Real.log y ≤ 1 + Real.log x := by
  have h1 : Real.log y ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hy
  rw [Real.log_mul (by norm_num) (by linarith)] at h1
  have := Real.log_two_lt_d9
  linarith

/-- **One dyadic block, all characters.** -/
theorem blk_sum_bound : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → ∀ R : ℕ, 1 ≤ R →
    ∀ M : ℕ, w ≤ M →
    ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖blk x w M (⌊x⌋₊ / M) i.2‖ ≤
      K * (2 + Real.log x) ^ 3 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by
  obtain ⟨C₀, hC₀, hyp⟩ := hyperbolic_large_sieve
  set c := Real.log 4 + 4 with hc
  have hc0 : 0 ≤ c := by rw [hc]; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  refine ⟨24 * C₀ * Real.sqrt c + 4 * C₀ * c, by positivity, ?_⟩
  intro x hx w hw R hR M hwM
  set N := ⌊x⌋₊ with hNdef
  set N₂ := N / M with hN₂
  set L := Real.log x with hL
  set ℓ := 2 + L with hℓ
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hM1 : 1 ≤ M := le_trans hw hwM
  have hRHS : 0 ≤ (24 * C₀ * Real.sqrt c + 4 * C₀ * c) * ℓ ^ 3 *
      (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by positivity
  by_cases hMw : N ≤ M * w
  · have hz : ∀ i ∈ primIdx R, blk x w M N₂ i.2 = 0 := by
      intro i _
      unfold blk
      apply sum_eq_zero; intro t ht; apply sum_eq_zero; intro r hr
      simp only [mem_Ioc] at ht hr
      apply gS4_eq_zero hx0
      show N < t * r
      nlinarith
    rw [sum_eq_zero (fun i hi => by rw [hz i hi, norm_zero, mul_zero])]
    exact hRHS
  push Not at hMw
  set a : ℤ → ℂ := fun m => (vonMangoldt m.toNat : ℂ) with ha
  set b : ℤ → ℂ := fun n => (gV w n.toNat : ℂ) with hb
  have key : ∀ i : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)), blk x w M N₂ i.2 =
      ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + ((M : ℕ) : ℤ)), ∑ n ∈ Ioc (w : ℤ) ((w : ℤ) + ((N₂ : ℕ) : ℤ)),
        (if ((m * n : ℤ) : ℝ) ≤ x then a m * b n * i.2 ((m * n : ℤ)) else 0) := by
    intro i
    rw [sum_Ioc_int]
    unfold blk
    refine sum_congr rfl fun t _ => ?_
    rw [sum_Ioc_int]
    refine sum_congr rfl fun r _ => ?_
    unfold gS4
    simp only [ha, hb, Int.toNat_natCast]
    push_cast
    rfl
  have h := hyp x hx R hR M w M N₂ (by positivity) (by positivity) a b
  rw [sum_congr rfl (fun i _ => by rw [key i])]
  refine h.trans ?_
  -- the numerical facts
  have hwN : w ≤ N₂ := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; omega)
  have hMN : ((M : ℕ) : ℝ) * (N₂ : ℝ) ≤ x := by
    have : M * N₂ ≤ N := Nat.mul_div_le N M
    exact le_trans (by exact_mod_cast this) hNx
  have hMwx : ((M : ℕ) : ℝ) * (w : ℝ) ≤ x := le_trans (by exact_mod_cast hMw.le) hNx
  have hNw : (N₂ : ℝ) * (w : ℝ) ≤ x := by
    refine le_trans ?_ hMN
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hwM) (by positivity)
  have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hw1r : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hMx : (M : ℝ) ≤ x := by nlinarith
  have hN₂x : (N₂ : ℝ) ≤ x := by nlinarith
  have hwN₂ : (w : ℝ) ≤ N₂ := by exact_mod_cast hwN
  -- the sums
  have hSa : ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + ((M : ℕ) : ℤ)), ‖a m‖ ^ 2 =
      ∑ t ∈ Ioc M (M + M), vonMangoldt t ^ 2 := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [ha, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hA : ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + ((M : ℕ) : ℤ)), ‖a m‖ =
      ∑ t ∈ Ioc M (M + M), vonMangoldt t := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [ha, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
  have hSb : ∑ n ∈ Ioc (w : ℤ) ((w : ℤ) + ((N₂ : ℕ) : ℤ)), ‖b n‖ ^ 2 =
      ∑ r ∈ Ioc w (w + N₂), gV w r ^ 2 := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [hb, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hB : ∑ n ∈ Ioc (w : ℤ) ((w : ℤ) + ((N₂ : ℕ) : ℤ)), ‖b n‖ =
      ∑ r ∈ Ioc w (w + N₂), |gV w r| := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [hb, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hSa, hA, hSb, hB]
  have hlog2M : Real.log (2 * M) ≤ ℓ := by
    have := log_two_mul_le (by linarith : (1 : ℝ) ≤ x) (by linarith : (1 : ℝ) ≤ 2 * M)
      (by linarith); rw [hℓ]; linarith
  have hlogwN : 1 + Real.log ((w + N₂ : ℕ) : ℝ) ≤ ℓ := by
    have := log_two_mul_le (by linarith : (1 : ℝ) ≤ x) (y := ((w + N₂ : ℕ) : ℝ))
      (by push_cast; linarith) (by push_cast; linarith)
    rw [hℓ]; linarith
  have hlogwN0 : 0 ≤ 1 + Real.log ((w + N₂ : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg (w + N₂); linarith
  have hwN2 : ((w + N₂ : ℕ) : ℝ) ≤ 2 * N₂ := by push_cast; linarith
  have hgsq : ((w + N₂ : ℕ) : ℝ) * (1 + Real.log ((w + N₂ : ℕ) : ℝ)) ^ 3 ≤ 2 * N₂ * ℓ ^ 3 :=
    mul_le_mul hwN2 (pow_le_pow_left₀ hlogwN0 hlogwN 3) (by positivity) (by positivity)
  have hlg : 1 + Real.log x + Real.log (1 + (M : ℝ) + (N₂ : ℝ) + ((M : ℤ) : ℝ) + ((w : ℤ) : ℝ))
      ≤ 3 * ℓ := by
    push_cast
    have h5 : Real.log (1 + (M : ℝ) + N₂ + M + w) ≤ Real.log (5 * x) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h5
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    rw [hℓ, hL]; linarith
  have hlogM0 : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ c * (2 * M) := by positivity
  apply blk_arith hC₀ hc0 (by linarith) (by rw [hℓ]; linarith) (by positivity) (by positivity)
    (by positivity) (by positivity) (sum_nonneg fun _ _ => by positivity)
    (sum_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => vonMangoldt_nonneg)
    (sum_nonneg fun _ _ => by positivity)
  · refine (sum_vonMangoldt_sq_block M).trans ?_
    calc Real.log (2 * M) * (c * (2 * M)) ≤ ℓ * (c * (2 * M)) :=
          mul_le_mul_of_nonneg_right hlog2M hc4
      _ = _ := by ring
  · exact (sum_gV_sq_le w N₂).trans hgsq
  · refine (sum_vonMangoldt_block M).trans (le_of_eq ?_); ring
  · exact (sum_abs_gV_le w N₂).trans hgsq
  · exact hMN
  · exact hMwx
  · exact hNw
  · exact hlg

/-- `Nat.log 2 N ≤ 2 log y` for `N ≤ y`. -/
lemma natLog_two_le {N : ℕ} {y : ℝ} (hN : 1 ≤ N) (hy : (N : ℝ) ≤ y) :
    (Nat.log 2 N : ℝ) ≤ 2 * Real.log y := by
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 N ≤ y := le_trans (by exact_mod_cast h1) hy
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have := Real.log_two_gt_d9
  have h0 : (0 : ℝ) ≤ Nat.log 2 N := by positivity
  nlinarith

/-- **The Type II estimate.** -/
theorem typeII_bound : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → ∀ R : ℕ, 1 ≤ R →
    ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 x w w i.2‖ ≤
      K * (2 + Real.log x) ^ 4 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by
  obtain ⟨K₁, hK₁, hblk⟩ := blk_sum_bound
  refine ⟨2 * K₁, by positivity, ?_⟩
  intro x hx w hw R hR
  set N := ⌊x⌋₊ with hNdef
  set J := Nat.log 2 N + 1 with hJ
  set G := x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x with hG
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNJ : N ≤ w * 2 ^ J := by
    have : N < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) N
    have : 2 ^ J ≤ w * 2 ^ J := Nat.le_mul_of_pos_left _ hw
    omega
  have hW : ∀ i ∈ primIdx R, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  have hJr : (J : ℝ) ≤ 2 * (2 + Real.log x) := by
    have := natLog_two_le hN1 (Nat.floor_le hx0)
    rw [hJ]; push_cast; linarith
  calc ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 x w w i.2‖
      ≤ ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ∑ j ∈ range J, ‖blk x w (w * 2 ^ j) (N / (w * 2 ^ j)) i.2‖ := by
        apply sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (hW i hi)
        rw [S4_eq_blocks hx0 hw w hNJ]
        exact norm_sum_le _ _
    _ = ∑ j ∈ range J, ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ‖blk x w (w * 2 ^ j) (N / (w * 2 ^ j)) i.2‖ := by
        simp_rw [mul_sum]; exact sum_comm
    _ ≤ ∑ _j ∈ range J, K₁ * (2 + Real.log x) ^ 3 * G := by
        apply sum_le_sum; intro j _
        exact hblk x hx w hw R hR (w * 2 ^ j) (Nat.le_mul_of_pos_right w (by positivity))
    _ = J * (K₁ * (2 + Real.log x) ^ 3 * G) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (2 * (2 + Real.log x)) * (K₁ * (2 + Real.log x) ^ 3 * G) :=
        mul_le_mul_of_nonneg_right hJr (by rw [hG]; positivity)
    _ = _ := by ring

end LeanLab.PNTPort.BV

