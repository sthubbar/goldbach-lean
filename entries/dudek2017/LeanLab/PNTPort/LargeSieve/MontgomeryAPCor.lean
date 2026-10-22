module

public import LeanLab.PNTPort.LargeSieve.MontgomeryAP

/-!
# Brun-Titchmarsh in progressions with the sieve level chosen

Lab proof, unit U-5560, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics.
No cited input.

* `brun_titchmarsh_ap_cube`: for `k ≥ 1`, `y ≥ 2k` and `t = y/k`, the number of primes
  `p ≡ r mod k` in `(x, x + y]` is at most `t^{1/3} + 3k (t + 2 + 2t^{2/3})/(φ(k) log t)`,
  that is `(3 + o(1)) y/(φ(k) log(y/k))`, from `brun_titchmarsh_ap_montgomery` at
  `Q = ⌊t^{1/3}⌋`.
* `brun_titchmarsh_ap_pow`: the same at `Q = ⌊t^θ⌋` for any `θ > 0`, with `1/θ` in place of `3`
  and `t^{2θ}` in place of `t^{2/3}`; `θ` just below `1/2` gives `(2 + o(1))`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Finset Real

theorem brun_titchmarsh_ap_cube (x y k r : ℕ) (hk : 1 ≤ k) (hy : 2 * k ≤ y) :
    ((((Ioc x (x + y)).filter (fun p => p.Prime ∧ p % k = r % k)).card : ℕ) : ℝ) ≤
      ((y : ℝ) / k) ^ ((1 : ℝ) / 3) +
        3 * k * ((y : ℝ) / k + 2 + 2 * ((y : ℝ) / k) ^ ((2 : ℝ) / 3)) /
          (k.totient * Real.log ((y : ℝ) / k)) := by
  set t : ℝ := (y : ℝ) / k with ht
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hk']; exact_mod_cast (by omega : 2 * k ≤ y)
  have ht0 : 0 < t := by linarith
  set c : ℝ := t ^ ((1 : ℝ) / 3) with hc
  have hc0 : 0 ≤ c := rpow_nonneg ht0.le _
  have hc1 : 1 ≤ c := one_le_rpow (by linarith) (by norm_num)
  set Q := ⌊c⌋₊ with hQ
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hc1)
  have hQc : (Q : ℝ) ≤ c := Nat.floor_le hc0
  have hcQ : c ≤ (Q : ℝ) + 1 := (Nat.lt_floor_add_one c).le
  have hmain := brun_titchmarsh_ap_montgomery x y k r Q hk hQ1
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 hk
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogc : Real.log c = Real.log t / 3 := by
    rw [hc, Real.log_rpow ht0]; ring
  have hlogQ : Real.log t / 3 ≤ Real.log ((Q : ℝ) + 1) := by
    rw [← hlogc]; exact Real.log_le_log (by linarith) hcQ
  have hyk : ((y / k : ℕ) : ℝ) ≤ t := by rw [ht]; exact Nat.cast_div_le
  have hQ2 : (Q : ℝ) ^ 2 ≤ t ^ ((2 : ℝ) / 3) := by
    have : c ^ 2 = t ^ ((2 : ℝ) / 3) := by
      rw [hc, ← rpow_natCast, ← rpow_mul ht0.le]; norm_num
    rw [← this]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hQc 2
  have hnum : ((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2 ≤ t + 2 + 2 * t ^ ((2 : ℝ) / 3) := by
    linarith
  have hnum0 : 0 ≤ ((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2 := by positivity
  have hstep : (((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2) * k /
      (k.totient * Real.log ((Q : ℝ) + 1)) ≤
      3 * k * (t + 2 + 2 * t ^ ((2 : ℝ) / 3)) / (k.totient * Real.log t) := by
    have hden : 0 < (k.totient : ℝ) * (Real.log t / 3) := by positivity
    calc (((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * Real.log ((Q : ℝ) + 1))
        ≤ (((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * (Real.log t / 3)) := by
          apply div_le_div_of_nonneg_left (by positivity) hden
          exact mul_le_mul_of_nonneg_left hlogQ hφ.le
      _ ≤ (t + 2 + 2 * t ^ ((2 : ℝ) / 3)) * k / (k.totient * (Real.log t / 3)) := by
          apply div_le_div_of_nonneg_right _ hden.le
          exact mul_le_mul_of_nonneg_right hnum hk'.le
      _ = 3 * k * (t + 2 + 2 * t ^ ((2 : ℝ) / 3)) / (k.totient * Real.log t) := by
          field_simp
  linarith

/-- The level `Q = ⌊t^θ⌋` for any `0 < θ`: `(1/θ + o(1)) y/(φ(k) log(y/k))` when `θ < 1/2`. -/
theorem brun_titchmarsh_ap_pow (x y k r : ℕ) (hk : 1 ≤ k) (hy : 2 * k ≤ y) {θ : ℝ} (hθ : 0 < θ) :
    ((((Ioc x (x + y)).filter (fun p => p.Prime ∧ p % k = r % k)).card : ℕ) : ℝ) ≤
      ((y : ℝ) / k) ^ θ +
        k * ((y : ℝ) / k + 2 + 2 * ((y : ℝ) / k) ^ (2 * θ)) /
          (θ * (k.totient * Real.log ((y : ℝ) / k))) := by
  set t : ℝ := (y : ℝ) / k with ht
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hk']; exact_mod_cast (by omega : 2 * k ≤ y)
  have ht0 : 0 < t := by linarith
  set c : ℝ := t ^ θ with hc
  have hc0 : 0 ≤ c := rpow_nonneg ht0.le _
  have hc1 : 1 ≤ c := one_le_rpow (by linarith) hθ.le
  set Q := ⌊c⌋₊ with hQ
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hc1)
  have hQc : (Q : ℝ) ≤ c := Nat.floor_le hc0
  have hcQ : c ≤ (Q : ℝ) + 1 := (Nat.lt_floor_add_one c).le
  have hmain := brun_titchmarsh_ap_montgomery x y k r Q hk hQ1
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 hk
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogc : Real.log c = θ * Real.log t := by
    rw [hc, Real.log_rpow ht0]
  have hlogQ : θ * Real.log t ≤ Real.log ((Q : ℝ) + 1) := by
    rw [← hlogc]; exact Real.log_le_log (by linarith) hcQ
  have hyk : ((y / k : ℕ) : ℝ) ≤ t := by rw [ht]; exact Nat.cast_div_le
  have hQ2 : (Q : ℝ) ^ 2 ≤ t ^ (2 * θ) := by
    have : c ^ 2 = t ^ (2 * θ) := by
      rw [hc, ← rpow_natCast, ← rpow_mul ht0.le]; ring_nf
    rw [← this]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hQc 2
  have hnum : ((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2 ≤ t + 2 + 2 * t ^ (2 * θ) := by
    linarith
  have hnum0 : 0 ≤ ((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2 := by positivity
  have hstep : (((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2) * k /
      (k.totient * Real.log ((Q : ℝ) + 1)) ≤
      k * (t + 2 + 2 * t ^ (2 * θ)) / (θ * (k.totient * Real.log t)) := by
    have hden : 0 < (k.totient : ℝ) * (θ * Real.log t) := by positivity
    calc (((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * Real.log ((Q : ℝ) + 1))
        ≤ (((y / k : ℕ) : ℝ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * (θ * Real.log t)) := by
          apply div_le_div_of_nonneg_left (by positivity) hden
          exact mul_le_mul_of_nonneg_left hlogQ hφ.le
      _ ≤ (t + 2 + 2 * t ^ (2 * θ)) * k / (k.totient * (θ * Real.log t)) := by
          apply div_le_div_of_nonneg_right _ hden.le
          exact mul_le_mul_of_nonneg_right hnum hk'.le
      _ = k * (t + 2 + 2 * t ^ (2 * θ)) / (θ * (k.totient * Real.log t)) := by
          ring
  linarith

end LeanLab.PNTPort.LargeSieve

