module

public import Mathlib
public import LeanLab.HeathBrown1985.MainTermLocal
public import LeanLab.HeathBrown1985.Theorem1Chain

/-!
P0096 Heath-Brown 1985, page 57, the main term: `MainTerm4` from 2.4, hence from the
Siegel-Walfisz theorem 1.1, and Theorem 1 from the bound for Σ₃ and Siegel-Walfisz.
For one `m`, 4.1 is `x Σ_{q ≤ Q} g_m(q) + O(x Q⁻¹)`, the tail of the singular series is
`O(x Q⁻¹ L d(m)²)` (2.3 in the form of `tail_gcd_le`), and the case `t = 2` of 2.2 sums
`d(m)²` over `m ≤ 3x`, giving `x² L⁴ Q⁻¹` in all.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- One `m`: `|Σ_{n ≤ x} Λ_Q(n) Λ(m - n) - x 𝔖(m)| ≤ δ + Q + 4x (6 + 2 log F) d(m)²/F`,
`F = ⌊Q⌋`, `δ` the local error. -/
theorem per_m_bound (A K4 : ℝ) (hA : 0 < A)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-A))
    (x : ℝ) (hx : 3 ≤ x) (Q : ℝ) (hQ1 : 1 ≤ Q) (hQx : Q ≤ x - 1) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - x * singular m| ≤
      2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
        (Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) + Q +
      x * (4 * ((6 + 2 * Real.log ⌊Q⌋₊) * (m.divisors.card : ℝ) ^ 2 / ⌊Q⌋₊)) := by
  have hloc := local_expansion A K4 hA hK4 x hx Q hQ1 hQx m hm
  have hm1 : 1 ≤ m := by simp only [mRange, mem_filter, mem_Icc] at hm; exact hm.1.1
  set F := ⌊Q⌋₊
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hQ1)
  have hF : (F : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have htail := abs_singular_sub_le m F hm1 hF1
  set S := ∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)
  set Mf := ∑ q ∈ Icc 1 F, gm m q
  have hMf : |Mf| ≤ Q := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum (fun q _ => abs_gm_le_one m q)).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
    exact hF
  have hx0 : 0 < x := by linarith
  have hN1 : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Nat.lt_floor_add_one x]
    · linarith [Nat.floor_le hx0.le]
  have e : S - x * singular m = (S - ⌊x⌋₊ * Mf) + ((⌊x⌋₊ : ℝ) - x) * Mf +
      x * -(singular m - Mf) := by ring
  rw [e]
  have h2 : |((⌊x⌋₊ : ℝ) - x) * Mf| ≤ Q := by
    rw [abs_mul]
    calc |(⌊x⌋₊ : ℝ) - x| * |Mf| ≤ 1 * Q :=
          mul_le_mul hN1 hMf (abs_nonneg _) zero_le_one
      _ = Q := one_mul Q
  have h3 : |x * -(singular m - Mf)| ≤
      x * (4 * ((6 + 2 * Real.log F) * (m.divisors.card : ℝ) ^ 2 / F)) := by
    rw [abs_mul, abs_neg, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_left htail hx0.le
  calc _ ≤ |S - ⌊x⌋₊ * Mf + ((⌊x⌋₊ : ℝ) - x) * Mf| + |x * -(singular m - Mf)| := abs_add_le _ _
    _ ≤ |S - ⌊x⌋₊ * Mf| + |((⌊x⌋₊ : ℝ) - x) * Mf| + |x * -(singular m - Mf)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- `Σ_{2x < m ≤ 3x} d(m)² ≤ 648 x L³` for `x ≥ 2`. -/
theorem sum_dsq_mRange_le (x : ℝ) (hx : 2 ≤ x) :
    ∑ m ∈ mRange x, (m.divisors.card : ℝ) ^ 2 ≤ 648 * x * Real.log x ^ 3 := by
  have hx0 : 0 < x := by linarith
  set N := ⌊3 * x⌋₊
  have hN : (N : ℝ) ≤ 3 * x := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hl2 := Real.log_two_gt_d9
  have hL2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hH : Hn N ≤ 6 * Real.log x := by
    refine (Hn_le N).trans ?_
    have : Real.log N ≤ Real.log 3 + Real.log x := by
      rw [← Real.log_mul (by norm_num) hx0.ne']
      exact Real.log_le_log (by linarith) hN
    linarith
  calc ∑ m ∈ mRange x, (m.divisors.card : ℝ) ^ 2 ≤ ∑ m ∈ Icc 1 N, (m.divisors.card : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ N * Hn N ^ 3 := sum_sq_divisors_le N
    _ ≤ (3 * x) * (6 * Real.log x) ^ 3 :=
        mul_le_mul hN (pow_le_pow_left₀ (Hn_nonneg N) hH 3) (pow_nonneg (Hn_nonneg N) 3) (by positivity)
    _ = 648 * x * Real.log x ^ 3 := by ring

/-- The local error is `≤ c₁ x/Q` with `A = 2B + 2`. -/
theorem delta_le (A B K4 x : ℝ) (hAB : A = 2 * B + 2) (hx : 2 ≤ x) :
    2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
        (Real.log x ^ B * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) ≤
      6 * |K4| * 2 ^ A * ((1 + 1 / Real.log 2) * (2 * Real.exp 1 / Real.log 2)) * x /
        Real.log x ^ B := by
  set L := Real.log x
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have he := Real.exp_pos 1
  have e1 : (L / 2) ^ (-A) = 2 ^ A * L ^ (-A) := by
    rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have e2 : L ^ (-A) * L ^ B * L ^ 2 = (L ^ B)⁻¹ := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_neg hL0.le]
    congr 1; rw [hAB]; push_cast; ring
  have h1L : 1 + L ≤ (1 + 1 / l2) * L := by
    have : 1 ≤ L / l2 := by rw [le_div_iff₀ hl2]; linarith
    have e : (1 + 1 / l2) * L = L + L / l2 := by field_simp
    linarith
  have hE : Real.exp 1 * (1 + L / l2) ≤ 2 * Real.exp 1 / l2 * L := by
    have : 1 ≤ L / l2 := by rw [le_div_iff₀ hl2]; linarith
    have e : 2 * Real.exp 1 / l2 * L = Real.exp 1 * (L / l2 + L / l2) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) he.le
  have hprod : (1 + L) * (Real.exp 1 * (1 + L / l2)) ≤
      ((1 + 1 / l2) * (2 * Real.exp 1 / l2)) * L ^ 2 := by
    have := mul_le_mul h1L hE (by positivity) (by positivity)
    calc _ ≤ (1 + 1 / l2) * L * (2 * Real.exp 1 / l2 * L) := this
      _ = _ := by ring
  have hQ0 : 0 < L ^ B := Real.rpow_pos_of_pos hL0 _
  have hc : 0 ≤ 2 * (|K4| * (3 * x) * (2 ^ A * L ^ (-A))) * L ^ B := by positivity
  rw [e1]
  calc 2 * (|K4| * (3 * x) * (2 ^ A * L ^ (-A))) *
        (L ^ B * ((1 + L) * (Real.exp 1 * (1 + L / l2))))
      = 2 * (|K4| * (3 * x) * (2 ^ A * L ^ (-A))) * L ^ B *
        ((1 + L) * (Real.exp 1 * (1 + L / l2))) := by ring
    _ ≤ 2 * (|K4| * (3 * x) * (2 ^ A * L ^ (-A))) * L ^ B *
        (((1 + 1 / l2) * (2 * Real.exp 1 / l2)) * L ^ 2) := mul_le_mul_of_nonneg_left hprod hc
    _ = 6 * |K4| * 2 ^ A * ((1 + 1 / l2) * (2 * Real.exp 1 / l2)) * x *
        (L ^ (-A) * L ^ B * L ^ 2) := by ring
    _ = _ := by rw [e2]; ring

/-- The tail term is `≤ c₃ x L d(m)²/Q`. -/
theorem tailterm_le (B x : ℝ) (hB : 0 < B) (hx : 2 ≤ x) (hQ1 : 1 ≤ Real.log x ^ B) (D : ℝ)
    (hD : 0 ≤ D) :
    x * (4 * ((6 + 2 * Real.log ⌊Real.log x ^ B⌋₊) * D / ⌊Real.log x ^ B⌋₊)) ≤
      8 * (6 / Real.log 2 + 2 * B) * x * Real.log x * D / Real.log x ^ B := by
  set L := Real.log x
  set Q := L ^ B
  set F := ⌊Q⌋₊
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := by linarith
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hQ1)
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF1
  have hFQ : (F : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hQF : Q ≤ 2 * F := by
    have := Nat.lt_floor_add_one Q
    linarith
  have hlogF : Real.log F ≤ B * L := by
    have h1 : Real.log F ≤ Real.log Q := Real.log_le_log (by linarith) hFQ
    have h2 : Real.log Q = B * Real.log L := Real.log_rpow hL0 B
    have h3 : Real.log L ≤ L := by have := Real.log_le_sub_one_of_pos hL0; linarith
    have : B * Real.log L ≤ B * L := mul_le_mul_of_nonneg_left h3 hB.le
    linarith
  have hlogF0 : 0 ≤ Real.log F := Real.log_nonneg hFR
  have h6 : 6 + 2 * Real.log F ≤ (6 / l2 + 2 * B) * L := by
    have : 6 ≤ 6 / l2 * L := by rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
    nlinarith
  have hA0 : 0 ≤ (6 + 2 * Real.log F) * D := by positivity
  have hstep : (6 + 2 * Real.log F) * D / F ≤ 2 * ((6 / l2 + 2 * B) * L * D) / Q := by
    rw [div_le_div_iff₀ (by linarith) hQ0]
    have := mul_le_mul_of_nonneg_right h6 hD
    nlinarith
  calc x * (4 * ((6 + 2 * Real.log F) * D / F))
      ≤ x * (4 * (2 * ((6 / l2 + 2 * B) * L * D) / Q)) := by gcongr
    _ = _ := by ring

/-- **Large `x`**: the bound once `x ≥ 3`, `L ≥ 1` and `Q² ≤ x`. -/
theorem mainTerm_large (B : ℝ) (hB : 0 < B) (K4 : ℝ)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-(2 * B + 2))) :
    ∃ K : ℝ, ∀ x : ℝ, 3 ≤ x → 1 ≤ Real.log x → (Real.log x ^ B) ^ 2 ≤ x →
      ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) -
        x * singular m| ≤ K * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B := by
  set c1 := 6 * |K4| * 2 ^ (2 * B + 2) * ((1 + 1 / Real.log 2) * (2 * Real.exp 1 / Real.log 2))
  set c3 := 8 * (6 / Real.log 2 + 2 * B)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc1 : 0 ≤ c1 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  refine ⟨3 * (c1 + 1) + 648 * c3, fun x hx hL1 hQx => ?_⟩
  set L := Real.log x
  set Q := L ^ B
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL1 hB.le
  have hQ0 : 0 < Q := by linarith
  have hQx1 : Q ≤ x - 1 := by
    by_contra h
    have h' : x - 1 < Q := lt_of_not_ge h
    nlinarith
  have hQxQ : Q ≤ x / Q := by rw [le_div_iff₀ hQ0]; nlinarith
  have hper : ∀ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - x * singular m| ≤
      (c1 + 1) * (x / Q) + c3 * x * L / Q * (m.divisors.card : ℝ) ^ 2 := by
    intro m hm
    have h := per_m_bound (2 * B + 2) K4 (by linarith) hK4 x hx Q hQ1 hQx1 m hm
    have hd := delta_le (2 * B + 2) B K4 x rfl (by linarith)
    have ht := tailterm_le B x hB (by linarith) hQ1 ((m.divisors.card : ℝ) ^ 2) (by positivity)
    have e1 : c1 * x / Q = c1 * (x / Q) := by ring
    have e3 : c3 * x * L * (m.divisors.card : ℝ) ^ 2 / Q =
        c3 * x * L / Q * (m.divisors.card : ℝ) ^ 2 := by ring
    linarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  have hcard := card_mRange_le x hx0.le
  have hdsq := sum_dsq_mRange_le x (by linarith)
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hxQ : 0 ≤ x / Q := by positivity
  have hcx : 0 ≤ c3 * x * L / Q := by positivity
  calc (#(mRange x) : ℝ) * ((c1 + 1) * (x / Q)) + c3 * x * L / Q *
        ∑ m ∈ mRange x, (m.divisors.card : ℝ) ^ 2
      ≤ 3 * x * ((c1 + 1) * (x / Q)) + c3 * x * L / Q * (648 * x * L ^ 3) := by
        gcongr
    _ = (3 * (c1 + 1) * 1 + 648 * c3 * L ^ 4) * (x ^ 2 / Q) := by ring
    _ ≤ (3 * (c1 + 1) * L ^ 4 + 648 * c3 * L ^ 4) * (x ^ 2 / Q) := by
        gcongr
    _ = _ := by ring

/-- `|𝔖(m)| ≤ 1 + 24 d(m)²` for `m ≥ 1`. -/
theorem abs_singular_le (m : ℕ) (hm : 1 ≤ m) :
    |singular m| ≤ 1 + 24 * (m.divisors.card : ℝ) ^ 2 := by
  have h := abs_singular_sub_le m 1 hm le_rfl
  have e : ∑ q ∈ Icc 1 1, gm m q = 1 := by simp [gm_one]
  rw [e] at h
  simp only [Nat.cast_one, Real.log_one, div_one] at h
  have := abs_sub_abs_le_abs_sub (singular m) 1
  rw [abs_one] at this
  nlinarith

/-- The crude bound for one `m`. -/
theorem per_m_crude (B x : ℝ) (hx : 2 ≤ x) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) - x * singular m| ≤
      x * (Real.log x ^ B) ^ 3 * Real.log (3 * x) + x * (1 + 216 * x ^ 2) := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, _⟩ := hm
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set Q := Real.log x ^ B
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hL0 _
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hS : |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)| ≤ x * Q ^ 3 * Real.log (3 * x) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ n ∈ Icc 1 ⌊x⌋₊, |LambdaQ Q n * Λ (m - n)| ≤ Q ^ 3 * Real.log (3 * x) := by
      intro n _
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul (abs_LambdaQ_le_cube Q hQ0 n)
        (vonMangoldt_le_log_of_le _ _ (by linarith)
          (le_trans (by exact_mod_cast Nat.sub_le m n) hmR))
        ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    refine (sum_le_sum hpt).trans ?_
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le)
      (by positivity)) hl3
  have hsing := abs_singular_le m hm1
  have hd : (m.divisors.card : ℝ) ≤ 3 * x :=
    le_trans (by exact_mod_cast Nat.card_divisors_le_self m) hmR
  have hd0 : (0 : ℝ) ≤ m.divisors.card := by positivity
  have hsing' : |singular m| ≤ 1 + 216 * x ^ 2 := by nlinarith
  calc _ ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)| + |x * singular m| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_pos hx0]
        have := mul_le_mul_of_nonneg_left hsing' hx0.le
        linarith

/-- **Bounded `x`**: the crude bound. -/
theorem mainTerm_small (B : ℝ) (hB : 0 < B) (X1 : ℝ) (hX1 : 3 ≤ X1) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → x ≤ X1 →
      ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) -
        x * singular m| ≤ K * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B := by
  set LX := Real.log X1
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hLX : l2 ≤ LX := Real.log_le_log (by norm_num) (by linarith)
  have hLX0 : 0 < LX := by linarith
  set C0 := X1 * (LX ^ B) ^ 3 * Real.log (3 * X1) + X1 * (1 + 216 * X1 ^ 2)
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ Real.log (3 * X1) := Real.log_nonneg (by linarith)
    have : 0 ≤ LX ^ B := Real.rpow_nonneg hLX0.le _
    positivity
  have hLXB : 0 < LX ^ B := Real.rpow_pos_of_pos hLX0 _
  refine ⟨3 * X1 * C0 * LX ^ B / (4 * l2 ^ 4), fun x hx hxX => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hLLX : L ≤ LX := Real.log_le_log hx0 hxX
  have hQ : L ^ B ≤ LX ^ B := Real.rpow_le_rpow hL0.le hLLX hB.le
  have hQ0 : 0 < L ^ B := Real.rpow_pos_of_pos hL0 _
  have hper : ∀ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (L ^ B) n * Λ (m - n) -
      x * singular m| ≤ C0 := by
    intro m hm
    refine (per_m_crude B x hx m hm).trans ?_
    have h3 : Real.log (3 * x) ≤ Real.log (3 * X1) := Real.log_le_log (by linarith) (by linarith)
    have h3' : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    have hQ3 : (L ^ B) ^ 3 ≤ (LX ^ B) ^ 3 := pow_le_pow_left₀ hQ0.le hQ 3
    have a1 : x * (L ^ B) ^ 3 * Real.log (3 * x) ≤ X1 * (LX ^ B) ^ 3 * Real.log (3 * X1) := by
      apply mul_le_mul (mul_le_mul hxX hQ3 (by positivity) (by linarith)) h3 h3'
        (by positivity)
    have a2 : x * (1 + 216 * x ^ 2) ≤ X1 * (1 + 216 * X1 ^ 2) := by
      apply mul_le_mul hxX _ (by positivity) (by linarith)
      nlinarith
    simp only [C0]; linarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard := card_mRange_le x hx0.le
  have h1 : (#(mRange x) : ℝ) * C0 ≤ 3 * X1 * C0 :=
    mul_le_mul_of_nonneg_right (hcard.trans (by linarith)) hC0
  refine h1.trans ?_
  have hL4 : l2 ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hl2.le hL2 4
  have hfac : 1 ≤ LX ^ B / (4 * l2 ^ 4) * (x ^ 2 * L ^ 4 / L ^ B) := by
    rw [div_mul_div_comm, le_div_iff₀ (by positivity), one_mul]
    have hx2 : 4 ≤ x ^ 2 := by nlinarith
    have := mul_le_mul hx2 hL4 (by positivity) (by positivity)
    calc 4 * l2 ^ 4 * L ^ B ≤ x ^ 2 * L ^ 4 * L ^ B :=
          mul_le_mul_of_nonneg_right (by linarith) hQ0.le
      _ ≤ x ^ 2 * L ^ 4 * LX ^ B := mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = LX ^ B * (x ^ 2 * L ^ 4) := by ring
  have h3X : 0 ≤ 3 * X1 * C0 := by positivity
  calc 3 * X1 * C0 = 3 * X1 * C0 * 1 := by ring
    _ ≤ 3 * X1 * C0 * (LX ^ B / (4 * l2 ^ 4) * (x ^ 2 * L ^ 4 / L ^ B)) :=
        mul_le_mul_of_nonneg_left hfac h3X
    _ = _ := by ring

/-- **The main term on page 57 from 2.4**: `MainTerm4`, zero sorry. -/
theorem mainTerm4_of_bound2_4 (h4 : Bound2_4) : MainTerm4 := by
  intro B hB
  obtain ⟨K4, hK4⟩ := h4 (2 * B + 2) (by linarith)
  obtain ⟨Kl, hKl⟩ := mainTerm_large B hB K4 hK4
  obtain ⟨KP, hKP⟩ := log_rpow_le_sqrt (2 * B) (by linarith)
  set X1 := max 3 (KP ^ 2)
  have hX1 : 3 ≤ X1 := le_max_left _ _
  obtain ⟨Ks, hKs⟩ := mainTerm_small B hB X1 hX1
  refine ⟨max Kl Ks, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hR0 : 0 ≤ x ^ 2 * Real.log x ^ 4 / Real.log x ^ B := by
    have := Real.rpow_pos_of_pos hL0 B
    positivity
  rcases le_or_gt X1 x with h | h
  · have hx3 : 3 ≤ x := hX1.trans h
    have hL1 : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
    have hQx : (Real.log x ^ B) ^ 2 ≤ x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      have h1 := hKP x hx
      have hKPx : KP ≤ Real.sqrt x :=
        (le_abs_self KP).trans (Real.abs_le_sqrt ((le_max_right _ _).trans h))
      have hs0 := Real.sqrt_nonneg x
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
      have e : B * ((2 : ℕ) : ℝ) = 2 * B := by push_cast; ring
      rw [e]
      nlinarith
    refine (hKl x hx3 hL1 hQx).trans ?_
    have : Kl * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B =
        Kl * (x ^ 2 * Real.log x ^ 4 / Real.log x ^ B) := by ring
    rw [this, show max Kl Ks * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B =
        max Kl Ks * (x ^ 2 * Real.log x ^ 4 / Real.log x ^ B) by ring]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
  · refine (hKs x hx h.le).trans ?_
    have : Ks * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B =
        Ks * (x ^ 2 * Real.log x ^ 4 / Real.log x ^ B) := by ring
    rw [this, show max Kl Ks * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B =
        max Kl Ks * (x ^ 2 * Real.log x ^ 4 / Real.log x ^ B) by ring]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hR0

/-- **The main term on page 57 from the Siegel-Walfisz theorem 1.1.** Zero sorry. -/
theorem mainTerm4_of_siegelWalfisz (hSW : SiegelWalfisz) : MainTerm4 :=
  mainTerm4_of_bound2_4 (bound2_4_of hSW)

/-- **Theorem 1 of Heath-Brown 1985 from the bound for Σ₃ on page 56 and Siegel-Walfisz.** -/
theorem theorem1_of_sigma3 (h3 : BoundSigma3) (hSW : SiegelWalfisz) : Theorem1 :=
  theorem1_of h3 (mainTerm4_of_siegelWalfisz hSW) hSW

end LeanLab.HeathBrown1985
