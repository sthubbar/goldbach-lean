module

public import Mathlib
public import LeanLab.HeathBrown1985.SingularSeries
public import LeanLab.HeathBrown1985.Section3

/-!
P0096 Heath-Brown 1985, page 57, the local expansion of 4.1: for `2x < m ≤ 3x`,
`Σ_{n ≤ x} Λ_Q(n) Λ(m - n) = Σ_{q ≤ Q} μ(q)²/φ(q) Σ_{d ∣ q} d μ(d) Σ_{n ≤ x, d ∣ n} Λ(m - n)`,
the inner sum is `ψ(m - 1; d, m) - ψ(m - 1 - ⌊x⌋; d, m)`, and 2.4 applied twice gives
`⌊x⌋ Σ_{q ≤ Q} g_m(q) + O(x L^{-A} Σ_{q ≤ Q} σ(q)/φ(q))`.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `T_d(m) = Σ_{n ≤ x, d ∣ n} Λ(m - n)`. -/
def Td (x : ℝ) (d m : ℕ) : ℝ := ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (d ∣ ·), Λ (m - n)

/-- The expansion by the definition of `Λ_Q`. -/
theorem sum_LambdaQ_mul_eq (x Q : ℝ) (m : ℕ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) =
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
        ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Td x d m := by
  unfold LambdaQ Td
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro q hq
  have hq1 := (mem_Icc.mp hq).1
  have e1 : ∀ n ∈ Icc 1 ⌊x⌋₊, (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) *
      (∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)) * Λ (m - n) =
      (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) *
        ∑ d ∈ q.divisors.filter (· ∣ n), (d : ℝ) * (μ d : ℝ) * Λ (m - n) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    rw [Nat.gcd_comm, divisors_gcd_eq q n hq1 hn1, mul_assoc, sum_mul]
  rw [sum_congr rfl e1, ← mul_sum]; congr 1
  rw [Finset.sum_comm' (t' := q.divisors) (s' := fun d => (Icc 1 ⌊x⌋₊).filter (d ∣ ·))]
  · apply sum_congr rfl; intro d _
    rw [mul_sum]
  · intro n d; simp only [mem_filter]; tauto

/-- `T_d(m) = ψ(m - 1; d, m) - ψ(m - 1 - ⌊x⌋; d, m)` for `⌊x⌋ < m`. -/
theorem Td_eq (x : ℝ) (d m : ℕ) (hm : ⌊x⌋₊ < m) :
    Td x d m = psi ((m - 1 : ℕ) : ℝ) d m - psi ((m - 1 - ⌊x⌋₊ : ℕ) : ℝ) d m := by
  set N := ⌊x⌋₊
  unfold psi Td
  rw [Nat.floor_natCast, Nat.floor_natCast]
  have hsplit : (Icc 1 (m - 1)).filter (fun n => n % d = m % d) =
      (Icc 1 (m - 1 - N)).filter (fun n => n % d = m % d) ∪
        (Icc (m - N) (m - 1)).filter (fun n => n % d = m % d) := by
    rw [← filter_union]; congr 1
    ext k; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint ((Icc 1 (m - 1 - N)).filter (fun n => n % d = m % d))
      ((Icc (m - N) (m - 1)).filter (fun n => n % d = m % d)) := by
    rw [disjoint_left]; intro k h1 h2
    simp only [mem_filter, mem_Icc] at h1 h2; omega
  rw [hsplit, sum_union hdisj, add_sub_cancel_left]
  apply Finset.sum_nbij' (fun n => m - n) (fun k => m - k)
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hlt : m - n < m := by omega
    rw [eq_comm, mod_eq_iff_dvd_sub hlt, Nat.sub_sub_self (by omega)]
    exact h3
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hlt : k < m := by omega
    rw [eq_comm, mod_eq_iff_dvd_sub hlt] at h3
    exact h3
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    omega
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    omega
  · intro n _; rfl

/-- For `x ≥ 3` and `x - 1 ≤ y`: `L/2 ≤ log y`. -/
theorem half_log_le (x y : ℝ) (hx : 3 ≤ x) (hy : x - 1 ≤ y) : Real.log x / 2 ≤ Real.log y := by
  have h1 : x ≤ (x - 1) ^ 2 := by nlinarith
  have h2 : Real.log x ≤ 2 * Real.log (x - 1) := by
    have e := Real.log_pow (x - 1) 2
    push_cast at e
    rw [← e]; exact Real.log_le_log (by linarith) h1
  have h3 : Real.log (x - 1) ≤ Real.log y := Real.log_le_log (by linarith) hy
  linarith

/-- **2.4 twice**: `|T_d(m) - E_{d,m} ⌊x⌋/φ(d)| ≤ 2 |K| 3x (L/2)^{-A}`. -/
theorem abs_Td_sub_le (A K4 : ℝ) (hA : 0 < A)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-A))
    (x : ℝ) (hx : 3 ≤ x) (m : ℕ) (hm : m ∈ mRange x) (d : ℕ) (hd : 1 ≤ d)
    (hdx : (d : ℝ) ≤ x - 1) :
    |Td x d m - Ecop d m * ⌊x⌋₊ / (Nat.totient d : ℝ)| ≤
      2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, hm2⟩ := hm
  set N := ⌊x⌋₊
  have hx0 : 0 < x := by linarith
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  have hNm : N < m := by
    have : (N : ℝ) < m := by linarith
    exact_mod_cast this
  rw [Td_eq x d m hNm]
  set y1 : ℝ := ((m - 1 : ℕ) : ℝ)
  set y0 : ℝ := ((m - 1 - N : ℕ) : ℝ)
  have hy1 : y1 = (m : ℝ) - 1 := by simp only [y1]; push_cast [show 1 ≤ m by omega]; ring
  have hy0 : y0 = (m : ℝ) - 1 - N := by
    simp only [y0]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hy0lo : x - 1 ≤ y0 := by rw [hy0]; linarith
  have hy1lo : x - 1 ≤ y1 := by rw [hy1]; linarith
  have hy1hi : y1 ≤ 3 * x := by rw [hy1]; linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hy0hi : y0 ≤ 3 * x := by rw [hy0]; linarith
  have hL : 0 < Real.log x / 2 := by have := Real.log_pos (by linarith : (1 : ℝ) < x); linarith
  have hbound : ∀ y : ℝ, x - 1 ≤ y → y ≤ 3 * x →
      |psi y d m - (if Nat.Coprime m d then y / (Nat.totient d : ℝ) else 0)| ≤
        |K4| * (3 * x) * (Real.log x / 2) ^ (-A) := by
    intro y hylo hyhi
    have h := hK4 y (by linarith) d m hd (by linarith)
    have hly : Real.log x / 2 ≤ Real.log y := half_log_le x y hx hylo
    have hr : Real.log y ^ (-A) ≤ (Real.log x / 2) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hL hly (by linarith)
    have hy0' : 0 ≤ y := by linarith
    refine h.trans ?_
    calc K4 * y * Real.log y ^ (-A) ≤ |K4| * y * Real.log y ^ (-A) := by
          have : 0 ≤ y * Real.log y ^ (-A) := mul_nonneg hy0' (Real.rpow_nonneg (by linarith) _)
          nlinarith [le_abs_self K4]
      _ ≤ |K4| * (3 * x) * (Real.log x / 2) ^ (-A) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hyhi (abs_nonneg _)) hr
            (Real.rpow_nonneg (by linarith) _) (by positivity)
  have b1 := hbound y1 hy1lo hy1hi
  have b0 := hbound y0 hy0lo hy0hi
  have hdiff : y1 - y0 = N := by rw [hy1, hy0]; ring
  have e : psi y1 d m - psi y0 d m - Ecop d m * N / (Nat.totient d : ℝ) =
      (psi y1 d m - (if Nat.Coprime m d then y1 / (Nat.totient d : ℝ) else 0)) -
      (psi y0 d m - (if Nat.Coprime m d then y0 / (Nat.totient d : ℝ) else 0)) := by
    unfold Ecop
    split_ifs
    · rw [← hdiff]; ring
    · ring
  rw [e]
  exact (abs_sub _ _).trans (by linarith)

/-- `Σ_{q ≤ Q} σ(q)/φ(q) ≤ Q (1 + L) e (1 + L/log 2)` for `Q ≤ x`. -/
theorem sum_sigma_div_totient_le (x Q : ℝ) (hx : 2 ≤ x) (hQ0 : 0 ≤ Q) (hQx : Q ≤ x) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, (∑ d ∈ q.divisors, (d : ℝ)) / (Nat.totient q : ℝ) ≤
      Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2))) := by
  set L := Real.log x
  set E := Real.exp 1 * (1 + L / Real.log 2)
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by have := Real.log_pos one_lt_two; positivity
  have hF : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0
  calc _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, (1 + L) * E := by
        apply sum_le_sum; intro q hq
        have hq1 := (mem_Icc.mp hq).1
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
        have hqx : (q : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (hF.trans hQx)
        have h1 := sigma_le q hq1
        have h2 := inv_totient_le x q hq1 hqx
        have hlq : Real.log q ≤ L := Real.log_le_log hqR hqx
        have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
        rw [div_eq_mul_inv]
        calc (∑ d ∈ q.divisors, (d : ℝ)) * (Nat.totient q : ℝ)⁻¹
            ≤ (q * (1 + Real.log q)) * (E / q) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (1 + Real.log q) * E := by field_simp
          _ ≤ (1 + L) * E := mul_le_mul_of_nonneg_right (by linarith) hE0
    _ = (⌊Q⌋₊ : ℝ) * ((1 + L) * E) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ Q * ((1 + L) * E) := mul_le_mul_of_nonneg_right hF (by positivity)

/-- **The local expansion, page 57**: for `2x < m ≤ 3x`, `1 ≤ Q ≤ x - 1`,
`|Σ_{n ≤ x} Λ_Q(n) Λ(m - n) - ⌊x⌋ Σ_{q ≤ Q} g_m(q)| ≤ 6|K| x (L/2)^{-A} Q (1 + L) e (1 + L/log 2)`. -/
theorem local_expansion (A K4 : ℝ) (hA : 0 < A)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-A))
    (x : ℝ) (hx : 3 ≤ x) (Q : ℝ) (hQ1 : 1 ≤ Q) (hQx : Q ≤ x - 1) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - ⌊x⌋₊ * ∑ q ∈ Icc 1 ⌊Q⌋₊, gm m q| ≤
      2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
        (Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) := by
  set δ := 2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A))
  have hδ : 0 ≤ δ := by
    have : 0 ≤ (Real.log x / 2) ^ (-A) :=
      Real.rpow_nonneg (by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x); linarith) _
    have : 0 ≤ x := by linarith
    positivity
  set F := ⌊Q⌋₊
  have hF : (F : ℝ) ≤ Q := Nat.floor_le (by linarith)
  rw [sum_LambdaQ_mul_eq, mul_sum, ← sum_sub_distrib]
  have hterm : ∀ q ∈ Icc 1 F,
      |(μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Td x d m -
        ⌊x⌋₊ * gm m q| ≤ δ * ((∑ d ∈ q.divisors, (d : ℝ)) / (Nat.totient q : ℝ)) := by
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hμ : (μ q : ℝ) ^ 2 ≤ 1 := by
      have h' : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [abs_nonneg (μ q : ℝ), sq_abs (μ q : ℝ)]
    have hc0 : 0 ≤ (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) := by positivity
    have hc1 : (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤ 1 / (Nat.totient q : ℝ) :=
      div_le_div_of_nonneg_right hμ (by linarith)
    have e : (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Td x d m -
        ⌊x⌋₊ * gm m q = (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) *
          (Td x d m - Ecop d m * ⌊x⌋₊ / (Nat.totient d : ℝ)) := by
      unfold gm
      have : ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) *
          (Td x d m - Ecop d m * ⌊x⌋₊ / (Nat.totient d : ℝ)) =
          ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Td x d m - ⌊x⌋₊ *
            ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Ecop d m / (Nat.totient d : ℝ) := by
        rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro d _; ring
      rw [this]; ring
    rw [e, abs_mul, abs_of_nonneg hc0]
    have hin : |∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) *
        (Td x d m - Ecop d m * ⌊x⌋₊ / (Nat.totient d : ℝ))| ≤ δ * ∑ d ∈ q.divisors, (d : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]; apply sum_le_sum; intro d hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
      have hdx : (d : ℝ) ≤ x - 1 := by
        have : (d : ℝ) ≤ q := by exact_mod_cast Nat.divisor_le hd
        have : (q : ℝ) ≤ F := by exact_mod_cast (mem_Icc.mp hq).2
        linarith
      rw [abs_mul, abs_mul, Nat.abs_cast]
      have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 := abs_Td_sub_le A K4 hA hK4 x hx m hm d hd1 hdx
      have h3 : (0 : ℝ) ≤ d := by positivity
      calc (d : ℝ) * |(μ d : ℝ)| * |Td x d m - Ecop d m * ⌊x⌋₊ / (Nat.totient d : ℝ)|
          ≤ (d : ℝ) * 1 * δ := mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 (abs_nonneg _)
            (by positivity)
        _ = δ * d := by ring
    calc (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * |_| ≤ 1 / (Nat.totient q : ℝ) *
          (δ * ∑ d ∈ q.divisors, (d : ℝ)) := mul_le_mul hc1 hin (abs_nonneg _) (by positivity)
      _ = _ := by ring
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_sigma_div_totient_le x Q (by linarith) (by linarith)
    (by linarith)) hδ

end LeanLab.HeathBrown1985
