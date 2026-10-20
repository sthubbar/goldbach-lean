module

public import Mathlib
public import LeanLab.HeathBrown1985.Vaughan

/-!
P0096 Heath-Brown 1985, pages 55 to 56, helpers for the bound on Σ₃: `|d_r| ≤ d(r)`, the
divisor bound `d(n)^k ≤ C_k n`, hence `d(n) ≤ C n^{1/k}`, and its use on page 56,
`d(r) ≪ L` for `r ≤ 3 Q²`, `Q = L^B` (the scan's exponent `r^{2/(2B)}` read as `d(r) ≪_ε r^ε`).
PROVED here, zero sorry.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- `|d_r| ≤ d(r)`, page 56. -/
theorem abs_dr_le (U r : ℕ) : |dr U r| ≤ (r.divisors.card : ℝ) := by
  unfold dr
  calc |∑ c ∈ r.divisors.filter (· ≤ U), (μ c : ℝ)|
      ≤ ∑ c ∈ r.divisors.filter (· ≤ U), |(μ c : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ r.divisors.filter (· ≤ U), (1 : ℝ) := by
        apply sum_le_sum
        intro c _
        have h := ArithmeticFunction.abs_moebius_le_one (n := c)
        rw [← Int.cast_abs]
        exact_mod_cast h
    _ = ((r.divisors.filter (· ≤ U)).card : ℝ) := by simp
    _ ≤ (r.divisors.card : ℝ) := by exact_mod_cast card_filter_le _ _

/-- `(a + 1)^k ≤ M 2^a` for all `a`. -/
theorem exists_pow_le_two_pow (k : ℕ) : ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ℕ, ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) one_lt_two
  have ht' : Tendsto (fun a : ℕ => ((a + 1 : ℕ) : ℝ) ^ k / 2 ^ (a + 1)) atTop (𝓝 0) :=
    ht.comp (tendsto_add_atTop_nat 1)
  obtain ⟨S, hS⟩ := ht'.bddAbove_range
  refine ⟨max 1 (2 * S), le_max_left _ _, fun a => ?_⟩
  have h1 : ((a + 1 : ℕ) : ℝ) ^ k / 2 ^ (a + 1) ≤ S := hS ⟨a, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ (a + 1) := by positivity
  rw [div_le_iff₀ h2] at h1
  push_cast at h1
  have h3 : (0 : ℝ) < 2 ^ a := by positivity
  calc ((a : ℝ) + 1) ^ k ≤ S * 2 ^ (a + 1) := h1
    _ = (2 * S) * 2 ^ a := by ring
    _ ≤ max 1 (2 * S) * 2 ^ a := by gcongr; exact le_max_right _ _

/-- The prime power factor bound behind `d(n)^k ≪ n`. -/
theorem prime_pow_factor_le (k : ℕ) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ a : ℕ, ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ^ k ≤ (if p < 2 ^ k then M else 1) * (p : ℝ) ^ a := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  split_ifs with h
  · calc ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a := hM a
      _ ≤ M * (p : ℝ) ^ a := by gcongr
  · push Not at h
    have ha : (a : ℝ) + 1 ≤ 2 ^ a := by
      have := Nat.lt_two_pow_self (n := a)
      exact_mod_cast this
    have hpk : ((2 : ℝ) ^ k) ≤ p := by exact_mod_cast h
    calc ((a : ℝ) + 1) ^ k ≤ ((2 : ℝ) ^ a) ^ k := by gcongr
      _ = ((2 : ℝ) ^ k) ^ a := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (p : ℝ) ^ a := by gcongr
      _ = 1 * (p : ℝ) ^ a := by ring

/-- The divisor bound `d(n)^k ≤ C_k n`. -/
theorem card_divisors_pow_le (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ^ k ≤ C * n := by
  obtain ⟨M, hM1, hM⟩ := exists_pow_le_two_pow k
  refine ⟨M ^ (2 ^ k), one_le_pow₀ hM1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  push_cast
  rw [← prod_pow]
  have hg : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ k ≤
      (if p < 2 ^ k then M else 1) * (p : ℝ) ^ n.factorization p := by
    intro p hp
    exact prime_pow_factor_le k M hM1 hM p _ (Nat.prime_of_mem_primeFactors hp).two_le
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ k
      ≤ ∏ p ∈ n.primeFactors, ((if p < 2 ^ k then M else 1) * (p : ℝ) ^ n.factorization p) :=
        prod_le_prod₀ (fun p _ => by positivity) hg
    _ = (∏ p ∈ n.primeFactors, (if p < 2 ^ k then M else 1)) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := prod_mul_distrib
    _ ≤ M ^ (2 ^ k) * n := by
        have hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
          conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
          push_cast; rfl
        rw [← hn']
        gcongr
        rw [← prod_filter, prod_const]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (· < 2 ^ k)).card ≤ (range (2 ^ k)).card := by
              apply card_le_card
              intro p hp
              simp only [mem_filter] at hp
              simpa using hp.2
          _ = 2 ^ k := card_range _

/-- `d(n) ≤ C n^{1/k}`. -/
theorem card_divisors_le_rpow (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  obtain ⟨C, hC1, hC⟩ := card_divisors_pow_le k
  refine ⟨C ^ ((k : ℝ)⁻¹), by positivity, fun n hn => ?_⟩
  have hk0 : k ≠ 0 := by omega
  have hd0 : (0 : ℝ) ≤ n.divisors.card := by positivity
  calc (n.divisors.card : ℝ) = ((n.divisors.card : ℝ) ^ k) ^ ((k : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hd0 hk0).symm
    _ ≤ (C * n) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) (hC n hn) (by positivity)
    _ = C ^ ((k : ℝ)⁻¹) * (n : ℝ) ^ ((k : ℝ)⁻¹) :=
        Real.mul_rpow (by linarith) (by positivity)

/-- `L^e ≤ L / log 2` for `0 ≤ e ≤ 1`, `L ≥ log 2`. -/
theorem rpow_le_div_log_two (L e : ℝ) (hL : Real.log 2 ≤ L) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    L ^ e ≤ L / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hL0 : 0 < L := lt_of_lt_of_le hl2 hL
  have hdiv : L ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hl2]; nlinarith
  rcases le_or_gt L 1 with h | h
  · calc L ^ e ≤ 1 := Real.rpow_le_one hL0.le h he0
      _ ≤ L / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
  · calc L ^ e ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le he1
      _ = L := Real.rpow_one L
      _ ≤ L / Real.log 2 := hdiv

/-- Page 56: `d(r) ≪ L` for `1 ≤ r ≤ 3 Q²`, `Q = L^B`, `L = log x`. -/
theorem card_divisors_le_log (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ 3 * (Real.log x ^ B) ^ 2 → (r.divisors.card : ℝ) ≤ K * Real.log x := by
  set k : ℕ := ⌈2 * B⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  obtain ⟨C, hC, hCd⟩ := card_divisors_le_rpow k hk1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  refine ⟨C * 3 ^ ((k : ℝ)⁻¹) / Real.log 2, by positivity, fun x hx r hr hrx => ?_⟩
  have hL : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le hl2 hL
  have hQ : (Real.log x ^ B) ^ 2 = Real.log x ^ (2 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
  have he0 : 0 ≤ 2 * B / k := by positivity
  have he1 : 2 * B / k ≤ 1 := by
    rw [div_le_one hkpos]
    have := Nat.le_ceil (2 * B)
    have : ((⌈2 * B⌉₊ : ℕ) : ℝ) + 1 = (k : ℝ) := by rw [hk]; push_cast; ring
    linarith
  have h1 := hCd r hr
  have h2 : (r : ℝ) ^ ((k : ℝ)⁻¹) ≤ (3 * Real.log x ^ (2 * B)) ^ ((k : ℝ)⁻¹) := by
    rw [← hQ]; exact Real.rpow_le_rpow (by positivity) hrx (by positivity)
  have h3 : (3 * Real.log x ^ (2 * B)) ^ ((k : ℝ)⁻¹) =
      3 ^ ((k : ℝ)⁻¹) * Real.log x ^ (2 * B / k) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hL0.le]
    rfl
  have h4 := rpow_le_div_log_two (Real.log x) (2 * B / k) hL he0 he1
  calc (r.divisors.card : ℝ) ≤ C * (r : ℝ) ^ ((k : ℝ)⁻¹) := h1
    _ ≤ C * (3 ^ ((k : ℝ)⁻¹) * Real.log x ^ (2 * B / k)) := by rw [← h3]; gcongr
    _ ≤ C * (3 ^ ((k : ℝ)⁻¹) * (Real.log x / Real.log 2)) := by gcongr
    _ = C * 3 ^ ((k : ℝ)⁻¹) / Real.log 2 * Real.log x := by ring

end LeanLab.HeathBrown1985
