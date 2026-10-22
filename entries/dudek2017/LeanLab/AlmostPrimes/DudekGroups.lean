module

public import LeanLab.AlmostPrimes.DudekFrom4e18
public import LeanLab.AlmostPrimes.DDLemma22

/-!
# Groundwork for Dudek's theorem from `10⁹`, I-5067

Unit U-5661, CLOUD 20261019T1515Z-cloud27. AI wrote the Lean code. KNOWN mathematics.

I-5067 asks for Dudek's even theorem with no cited input, from the lab's kernel-checked even
Goldbach to `10⁹` and a count valid from `e^20.72`. That count needs a level `θ` per group of
primes `r`, and prime-weighted sums `Σ 1/(r(r - 1))` per group. This file gives both pieces:

* `cls_card_pow_gen`: the class bound of `DudekFrom4e18.cls_card_pow` for any `0 < θ < 1/2`,
  `#cls(N, r) ≤ N^θ + (1/θ)(N + 1)(1 + 2e^{-λ} + 2e^{-(1 - 2θ)λ}) / (λ r(r - 1))`;
* `wsum_le`: `Σ_{a < r ≤ b, r prime} 1/(r(r - 1)) ≤ c/10¹²` from a kernel check of the rounded
  terms `⌈10¹²/(n(n - 1))⌉` over `DDLemma22.cand`, which contains every prime `3 ≤ r < 10⁴`; and
  the three instances for `(31, 127]`, `(127, 511]`, `(511, 2047]`.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.DudekGroups

open LeanLab.AlmostPrimes.DudekLarge LeanLab.AlmostPrimes.DudekFrom4e18
open LeanLab.AlmostPrimes.DDLemma22

/-- **One class, any level `0 < θ < 1/2`.** -/
theorem cls_card_pow_gen {N r : ℕ} (hr : r.Prime) (h2 : 2 * r ^ 2 ≤ N + 1) (hN : 1 ≤ N)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    {lam : ℝ} (hlam : 0 < lam) (hlt : lam ≤ Real.log (((N + 1 : ℕ) : ℝ) / ((r ^ 2 : ℕ) : ℝ))) :
    ((cls N r).card : ℝ) ≤ (N : ℝ) ^ θ +
      1 / θ * ((N : ℝ) + 1) * (1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam))) /
        (lam * ((r : ℝ) * ((r : ℝ) - 1))) := by
  have hr2 : 2 ≤ r := hr.two_le
  have hk : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbt := LeanLab.PNTPort.LargeSieve.brun_titchmarsh_ap_pow 0 (N + 1) (r ^ 2) N hk h2 hθ0
  rw [← cls_eq] at hbt
  set t : ℝ := (((N + 1 : ℕ) : ℝ)) / ((r ^ 2 : ℕ) : ℝ) with ht
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hk0 : (0 : ℝ) < ((r ^ 2 : ℕ) : ℝ) := by positivity
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hk0]; exact_mod_cast h2
  have ht0 : 0 < t := by linarith
  have hlogt : lam ≤ Real.log t := hlt
  have hlogt0 : 0 < Real.log t := lt_of_lt_of_le hlam hlogt
  have htN : t ≤ N := by
    rw [ht, div_le_iff₀ hk0]
    have : 4 ≤ r ^ 2 := by nlinarith
    have : (4 : ℝ) ≤ ((r ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Nat.cast_add, Nat.cast_one]; nlinarith
  have hpow1 : t ^ θ ≤ (N : ℝ) ^ θ := Real.rpow_le_rpow ht0.le htN hθ0.le
  have hsplit : t ^ (2 * θ) = t * t ^ (2 * θ - 1) := by
    rw [show 2 * θ = 1 + (2 * θ - 1) by ring, Real.rpow_add ht0, Real.rpow_one]; ring_nf
  have hneg : t ^ (2 * θ - 1) ≤ exp (-((1 - 2 * θ) * lam)) := by
    rw [Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    have : 0 < 1 - 2 * θ := by linarith
    nlinarith
  have hinv : 1 / t ≤ exp (-lam) := by
    have : exp lam ≤ t := by
      calc exp lam ≤ exp (Real.log t) := Real.exp_le_exp.mpr hlogt
        _ = t := Real.exp_log ht0
    rw [Real.exp_neg, div_le_iff₀ ht0, inv_mul_eq_div, le_div_iff₀ (exp_pos _)]; linarith
  have htot : (((r ^ 2).totient : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hr two_pos]
    rw [Nat.cast_mul, Nat.cast_sub hr.one_lt.le]; simp
  rw [htot] at hbt
  have hrr : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
  have hkt : ((r ^ 2 : ℕ) : ℝ) * t = (N : ℝ) + 1 := by
    rw [ht, mul_div_cancel₀ _ hk0.ne']; push_cast; ring
  have hmain : ((r ^ 2 : ℕ) : ℝ) * (t + 2 + 2 * t ^ (2 * θ)) =
      ((N : ℝ) + 1) * (1 + 2 * (1 / t) + 2 * t ^ (2 * θ - 1)) := by
    rw [hsplit, ← hkt]; field_simp
  have hfac : 1 + 2 * (1 / t) + 2 * t ^ (2 * θ - 1) ≤
      1 + 2 * exp (-lam) + 2 * exp (-((1 - 2 * θ) * lam)) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc ((cls N r).card : ℝ) ≤ t ^ θ + ((r ^ 2 : ℕ) : ℝ) * (t + 2 + 2 * t ^ (2 * θ)) /
          (θ * ((r : ℝ) * ((r : ℝ) - 1) * Real.log t)) := by
        convert hbt using 2
    _ = t ^ θ + 1 / θ * ((N : ℝ) + 1) * (1 + 2 * (1 / t) + 2 * t ^ (2 * θ - 1)) /
          (Real.log t * ((r : ℝ) * ((r : ℝ) - 1))) := by
        rw [hmain]; field_simp
    _ ≤ _ := by
        gcongr

/-- `1/(n(n - 1)) ≤ ⌈10¹²/(n(n - 1))⌉ / 10¹²` for `n ≥ 2`. -/
def ub2 (n : ℕ) : ℕ := (10 ^ 12 + n * (n - 1) - 1) / (n * (n - 1))

lemma inv_le_ub2 (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ (ub2 n : ℝ) / 10 ^ 12 := by
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have key : 10 ^ 12 ≤ ub2 n * (n * (n - 1)) := by
    unfold ub2
    have h1 := Nat.lt_div_mul_add (a := 10 ^ 12 + n * (n - 1) - 1) hpos
    generalize (10 ^ 12 + n * (n - 1) - 1) / (n * (n - 1)) * (n * (n - 1)) = X at h1 ⊢
    generalize n * (n - 1) = m at h1 hpos ⊢
    omega
  have hcast : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]; simp
  have hr : (10 : ℝ) ^ 12 ≤ (ub2 n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [← hcast]; exact_mod_cast key
  have hpos' : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by rw [← hcast]; exact_mod_cast hpos
  rw [div_le_div_iff₀ hpos' (by norm_num)]
  linarith

/-- **Prime weight sums from a kernel check.** For `2 ≤ a`, `b < 10⁴`, if the rounded terms over
`cand` in `(a, b]` sum to at most `c`, the primes in `(a, b]` have `Σ 1/(r(r - 1)) ≤ c/10¹²`. -/
theorem wsum_le (a b c : ℕ) (ha : 2 ≤ a) (hb : b < 10000)
    (hc : ∑ n ∈ (Ioc a b).filter (fun n => cand n = true), ub2 n ≤ c) :
    ∑ r ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ (c : ℝ) / 10 ^ 12 := by
  have hsub : (Ioc a b).filter Nat.Prime ⊆ (Ioc a b).filter (fun n => cand n = true) := by
    intro r hr
    rw [mem_filter, mem_Ioc] at hr ⊢
    exact ⟨hr.1, cand_of_prime hr.2 (by omega)⟩
  calc _ ≤ ∑ r ∈ (Ioc a b).filter (fun n => cand n = true), (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro r hr _
        rw [mem_filter, mem_Ioc] at hr
        have : (2 : ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
        have : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
        positivity
    _ ≤ ∑ r ∈ (Ioc a b).filter (fun n => cand n = true), (ub2 r : ℝ) / 10 ^ 12 := by
        apply sum_le_sum
        intro r hr
        rw [mem_filter, mem_Ioc] at hr
        exact inv_le_ub2 r (by omega)
    _ = ((∑ r ∈ (Ioc a b).filter (fun n => cand n = true), ub2 r : ℕ) : ℝ) / 10 ^ 12 := by
        rw [← sum_div]; push_cast; rfl
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast hc

theorem w31_127 : ∑ n ∈ (Ioc 31 127).filter (fun n => cand n = true), ub2 n ≤ 4975753612 := by
  decide +kernel

theorem w127_511 : ∑ n ∈ (Ioc 127 511).filter (fun n => cand n = true), ub2 n ≤ 1054344475 := by
  decide +kernel

theorem w511_2047 :
    ∑ n ∈ (Ioc 511 2047).filter (fun n => cand n = true), ub2 n ≤ 208827941 := by
  decide +kernel

/-- `Σ_{31 < r ≤ 127 prime} 1/(r(r - 1)) ≤ 0.004976`. -/
theorem wsum_31_127 :
    ∑ r ∈ (Ioc 31 127).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.004976 := by
  refine (wsum_le 31 127 4975753612 (by norm_num) (by norm_num) w31_127).trans ?_
  norm_num

/-- `Σ_{127 < r ≤ 511 prime} 1/(r(r - 1)) ≤ 0.0010544`. -/
theorem wsum_127_511 :
    ∑ r ∈ (Ioc 127 511).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.0010544 := by
  refine (wsum_le 127 511 1054344475 (by norm_num) (by norm_num) w127_511).trans ?_
  norm_num

/-- `Σ_{511 < r ≤ 2047 prime} 1/(r(r - 1)) ≤ 0.00020883`. -/
theorem wsum_511_2047 :
    ∑ r ∈ (Ioc 511 2047).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.00020883 := by
  refine (wsum_le 511 2047 208827941 (by norm_num) (by norm_num) w511_2047).trans ?_
  norm_num

end LeanLab.AlmostPrimes.DudekGroups

