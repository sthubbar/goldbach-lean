module

public import LeanLab.SchnirelmannGoldbach.S1.Remainder
public import LeanLab.SchnirelmannGoldbach.S1.MainTerm

/-!
AI-written Lean code, Claude, 2026-10-16.
S1 final: the uniform Selberg sieve upper bound `S1u` for Goldbach representations.
-/

@[expose] public section

open Finset
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace LeanLab.SchnirelmannGoldbach.S1

/-- Sieve bound for even `n` at sifting level `z > 1`. -/
theorem r_le_of_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) {z : ℝ} (hz : 1 < z) :
    (r n : ℝ) ≤ 32 * n * singProd n / Real.log z ^ 2 + z * (1 + Real.log z) ^ 6 + 2 * (z + 1) := by
  have h1 := r_le_siftedSum n hn z hz.le
  have h2 : siftedSum (s := (gSieve n hn z hz.le).toBoundingSieve) ≤
      (n : ℝ) / selbergBoundingSum (gSieve n hn z hz.le) +
      ∑ d ∈ (gSieve n hn z hz.le).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d *
          |rem (s := (gSieve n hn z hz.le).toBoundingSieve) d| else 0) :=
    LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple (gSieve n hn z hz.le)
  have h3 := errSum_gSieve_le (n := n) (hn := hn) (z := z) (hz := hz.le)
  have h4 := boundingSum_gSieve_ge n hn hn0 z hz.le
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hsp := singProd_pos n
  have hlow : 0 < Real.log z ^ 2 / (32 * singProd n) := by positivity
  have h5 : (n : ℝ) / selbergBoundingSum (gSieve n hn z hz.le) ≤
      (n : ℝ) / (Real.log z ^ 2 / (32 * singProd n)) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlow h4
  have h6 : (n : ℝ) / (Real.log z ^ 2 / (32 * singProd n)) =
      32 * n * singProd n / Real.log z ^ 2 := by
    field_simp
  linarith

/-- For odd `n`, one of `p`, `n - p` is `2`. -/
lemma r_le_three_of_not {n : ℕ} (h : ¬ (Even n ∧ 4 ≤ n)) : r n ≤ 3 := by
  by_cases h4 : n < 4
  · unfold r
    exact (card_filter_le _ _).trans (by simp; omega)
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with he | ho
    · exact absurd ⟨he, by omega⟩ h
    · exact Nat.odd_iff.mp ho
  unfold r
  have hsub : {p ∈ range n | p.Prime ∧ (n - p).Prime} ⊆ {2, n - 2} := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpn, hp, hq⟩ := hp
    simp only [mem_insert, mem_singleton]
    rcases hp.eq_two_or_odd with h2 | h2
    · left; exact h2
    · right
      rcases hq.eq_two_or_odd with h3 | h3
      · omega
      · omega
  exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by simp))

lemma one_le_singProd (n : ℕ) : 1 ≤ singProd n := by
  unfold singProd
  calc (1 : ℝ) = ∏ p ∈ n.primeFactors, (1 : ℝ) := by simp
    _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) (fun p _ => by
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith)

lemma log_sq_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h := Real.log_le_rpow_div (x := x) (by linarith) (ε := 1 / 2) (by norm_num)
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [← Real.sqrt_eq_rpow] at h
  have hs : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have : Real.log x ≤ 2 * √x := by linarith
  nlinarith [Real.sqrt_nonneg x]

lemma polylog_bound (x : ℝ) (hx : 1 ≤ x) :
    √x * (1 + Real.log x) ^ 6 * Real.log x ^ 2 ≤ 17 ^ 8 * x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  set t := x ^ (1 / 16 : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hx (by norm_num)
  have hlog : Real.log x ≤ 16 * t := by
    have := Real.log_le_rpow_div (x := x) (by linarith) (ε := 1 / 16) (by norm_num)
    rw [← ht] at this; linarith
  have h1 : 1 + Real.log x ≤ 17 * t := by linarith
  have ht8 : t ^ 8 = √x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]
    norm_num
  have hsx : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have h2 : Real.log x ^ 2 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have h3 : (1 + Real.log x) ^ 8 ≤ (17 * t) ^ 8 := by
    apply pow_le_pow_left₀ (by linarith) h1
  calc √x * (1 + Real.log x) ^ 6 * Real.log x ^ 2
      ≤ √x * (1 + Real.log x) ^ 6 * (1 + Real.log x) ^ 2 := by gcongr
    _ = √x * (1 + Real.log x) ^ 8 := by ring
    _ ≤ √x * (17 * t) ^ 8 := by gcongr
    _ = 17 ^ 8 * (√x * t ^ 8) := by ring
    _ = 17 ^ 8 * x := by rw [ht8, hsx]

end LeanLab.SchnirelmannGoldbach.S1

namespace LeanLab.SchnirelmannGoldbach

open LeanLab.SchnirelmannGoldbach.S1 in
/-- **S1u.** Uniform Selberg sieve upper bound for Goldbach representations. -/
theorem S1u_holds : S1u := by
  refine ⟨128 + 5 * 17 ^ 8 + 12, fun N hN n hn => ?_⟩
  simp only [mem_Icc] at hn
  have hN1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsp := one_le_singProd n
  have hNl : (N : ℝ) / Real.log N ^ 2 ≥ 1 / 4 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [log_sq_le N (by linarith)]
  have hQ0 : 0 ≤ (N : ℝ) / Real.log N ^ 2 * singProd n := by positivity
  by_cases hev : Even n ∧ 4 ≤ n
  · obtain ⟨hev, hn4⟩ := hev
    have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hn4.trans hn.2
    set z := √(N : ℝ) with hz
    have hz2 : 2 ≤ z := by
      rw [hz, show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hN4
    have hrz := r_le_of_even hev (by omega) (by linarith : (1 : ℝ) < z)
    have hlogz : Real.log z = Real.log N / 2 := Real.log_sqrt (by positivity)
    have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    -- main term
    have hmain : 32 * n * singProd n / Real.log z ^ 2 ≤ 128 * (N / Real.log N ^ 2 * singProd n) := by
      rw [hlogz]
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ singProd n := by linarith
      field_simp
      nlinarith
    -- error terms
    have hlz : Real.log z ≤ Real.log N := by rw [hlogz]; linarith
    have hpow1 : 1 ≤ (1 + Real.log z) ^ 6 := one_le_pow₀ (by linarith)
    have herr1 : z * (1 + Real.log z) ^ 6 + 2 * (z + 1) ≤ 5 * (z * (1 + Real.log N) ^ 6) := by
      have : (1 + Real.log z) ^ 6 ≤ (1 + Real.log N) ^ 6 := by gcongr
      nlinarith
    have hpb := polylog_bound N (by linarith)
    have herr2 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * (N / Real.log N ^ 2 * singProd n) := by
      have h1 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * (N / Real.log N ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        exact hpb
      have h2 : (17 : ℝ) ^ 8 * (N / Real.log N ^ 2) ≤ 17 ^ 8 * (N / Real.log N ^ 2 * singProd n) := by
        have : (0 : ℝ) ≤ N / Real.log N ^ 2 := by positivity
        nlinarith
      linarith
    have : (r n : ℝ) ≤ (128 + 5 * 17 ^ 8) * (N / Real.log N ^ 2 * singProd n) := by
      linarith
    calc (r n : ℝ) ≤ (128 + 5 * 17 ^ 8) * (N / Real.log N ^ 2 * singProd n) := this
      _ ≤ (128 + 5 * 17 ^ 8 + 12) * (N / Real.log N ^ 2 * singProd n) := by nlinarith
      _ = _ := by ring
  · have h3 : (r n : ℝ) ≤ 3 := by exact_mod_cast r_le_three_of_not hev
    have : (3 : ℝ) ≤ 12 * (N / Real.log N ^ 2 * singProd n) := by nlinarith
    calc (r n : ℝ) ≤ 12 * (N / Real.log N ^ 2 * singProd n) := by linarith
      _ ≤ (128 + 5 * 17 ^ 8 + 12) * (N / Real.log N ^ 2 * singProd n) := by nlinarith
      _ = _ := by ring

end LeanLab.SchnirelmannGoldbach
