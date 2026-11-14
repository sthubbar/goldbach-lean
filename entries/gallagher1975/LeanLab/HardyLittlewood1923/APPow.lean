module

public import LeanLab.HardyLittlewood1923.APSums
public import LeanLab.PNTSieve.BrunTitchmarshAP

/-! AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5901, paper P0004.
Power weighted and log weighted prime sums in a fixed progression, inputs for Hardy-Littlewood 1923.
* `ap_sum_pow`: for fixed `k` and fixed modulus `d`, uniformly in `a` coprime to `d`,
  `Σ_{p ≤ n, p ≡ a (d)} log p (n - p)^k = n^(k+1) / ((k+1) φ(d)) + o(n^(k+1))`.
  Route: a general summation by parts identity `abel_conv` turns the von Mangoldt sum into
  `Σ_j ψ(j; d, a) Δ_k(n - j)` with nonnegative weights summing to `n^k`; the lab's
  `psi_ap_eventually` from Siegel-Walfisz gives `ψ(j; d, a) = j/φ(d) + o(j)`; Mathlib's
  `Chebyshev.psi_sub_theta_le` removes prime powers; `Σ_{i<n} i^k` is squeezed between
  `n^(k+1)/(k+1) - n^k` and `n^(k+1)/(k+1)` by the geometric sum identity.
* `ap_log_sum_le`: a bound uniform in the modulus, with `A = 8` and `B = 4`:
  `Σ_{p ≤ n, p ≡ a (d)} log p ≤ 8 n / φ(d) + 4 n^(1/2)` for all large `n` and all `d ≥ 1`, `a`.
  Route: the lab's Brun-Titchmarsh theorem `brunTitchmarsh_ap` with sieve level `z = n^(1/4)`.
* `theta_le`: Chebyshev's bound `θ(n) ≤ log 4 · n`, from Mathlib's `theta_le_log4_mul_x`.
No cited input beyond what `siegelWalfisz` and `brunTitchmarsh_ap` prove. Binary Goldbach is OPEN. -/

@[expose] public section

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt

namespace LeanLab.HardyLittlewood1923

/-- First difference of `f`, with `dif f 0 = f 0`. -/
noncomputable def dif (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | i + 1 => f (i + 1) - f i

lemma sum_dif (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range (n + 1), dif f i = f n := by
  induction n with
  | zero => simp [dif]
  | succ n ih => rw [sum_range_succ, ih]; simp [dif]

lemma sum_reflect (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), f (n - j) = ∑ j ∈ range (n + 1), f j := by
  have := sum_range_reflect f (n + 1)
  simpa using this

/-- Summation by parts against an arbitrary weight. -/
lemma abel_conv (f : ℕ → ℝ) (n : ℕ) : ∀ g : ℕ → ℝ,
    ∑ m ∈ range (n + 1), g m * f (n - m) =
      ∑ j ∈ range (n + 1), (∑ m ∈ range (j + 1), g m) * dif f (n - j) := by
  induction n with
  | zero => intro g; simp [dif]
  | succ n ih =>
    intro g
    rw [sum_range_succ' _ (n + 1), sum_range_succ' _ (n + 1)]
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ih (fun m => g (m + 1))]
    have hG : ∀ j, ∑ m ∈ range (j + 1 + 1), g m = ∑ m ∈ range (j + 1), g (m + 1) + g 0 :=
      fun j => sum_range_succ' _ _
    simp only [hG, add_mul, sum_add_distrib, ← mul_sum]
    have hr : ∑ j ∈ range (n + 1), dif f (n - j) = f n := by
      rw [sum_reflect (dif f) n]; exact sum_dif f n
    rw [hr]
    simp [dif]
    ring

lemma dif_pow_nonneg (k i : ℕ) : 0 ≤ dif (fun i : ℕ => (i : ℝ) ^ k) i := by
  cases i with
  | zero => simp only [dif]; positivity
  | succ i =>
    simp only [dif]
    exact sub_nonneg.2 (pow_le_pow_left₀ (Nat.cast_nonneg i) (by push_cast; linarith) k)

lemma pow_succ_diff (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ((k : ℝ) + 1) * x ^ k ≤ (x + 1) ^ (k + 1) - x ^ (k + 1) ∧
      (x + 1) ^ (k + 1) - x ^ (k + 1) ≤ ((k : ℝ) + 1) * (x + 1) ^ k := by
  have h := geom_sum₂_mul (x + 1) x (k + 1)
  rw [show (x + 1 - x) = 1 by ring, mul_one] at h
  rw [← h]
  constructor
  · have : ∑ _i ∈ range (k + 1), x ^ k ≤
        ∑ i ∈ range (k + 1), (x + 1) ^ i * x ^ (k + 1 - 1 - i) := by
      apply sum_le_sum; intro i hi
      have hi' : i ≤ k := by simp at hi; omega
      calc x ^ k = x ^ i * x ^ (k + 1 - 1 - i) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := by gcongr; linarith
    rw [sum_const, card_range, nsmul_eq_mul] at this; push_cast at this; exact this
  · have : ∑ i ∈ range (k + 1), (x + 1) ^ i * x ^ (k + 1 - 1 - i) ≤
        ∑ _i ∈ range (k + 1), (x + 1) ^ k := by
      apply sum_le_sum; intro i hi
      have hi' : i ≤ k := by simp at hi; omega
      calc (x + 1) ^ i * x ^ (k + 1 - 1 - i) ≤ (x + 1) ^ i * (x + 1) ^ (k + 1 - 1 - i) := by
            gcongr; linarith
        _ = (x + 1) ^ k := by rw [← pow_add]; congr 1; omega
    rw [sum_const, card_range, nsmul_eq_mul] at this; push_cast at this; exact this

lemma sum_pow_upper (k n : ℕ) : ((k : ℝ) + 1) * ∑ i ∈ range n, (i : ℝ) ^ k ≤ (n : ℝ) ^ (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add]; push_cast
    linarith [(pow_succ_diff (n : ℝ) (Nat.cast_nonneg n) k).1]

lemma sum_pow_lower (k n : ℕ) :
    (n : ℝ) ^ (k + 1) ≤ ((k : ℝ) + 1) * ∑ i ∈ range n, ((i : ℝ) + 1) ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add]; push_cast
    linarith [(pow_succ_diff (n : ℝ) (Nat.cast_nonneg n) k).2]

lemma sum_pow_lower' (k n : ℕ) :
    (n : ℝ) ^ (k + 1) - ((k : ℝ) + 1) * (n : ℝ) ^ k ≤ ((k : ℝ) + 1) * ∑ i ∈ range n, (i : ℝ) ^ k := by
  have h1 : ∑ i ∈ range (n + 1), (i : ℝ) ^ k = ∑ i ∈ range n, ((i : ℝ) + 1) ^ k + (0 : ℝ) ^ k := by
    rw [sum_range_succ']; push_cast; rfl
  have h2 : ∑ i ∈ range (n + 1), (i : ℝ) ^ k = ∑ i ∈ range n, (i : ℝ) ^ k + (n : ℝ) ^ k :=
    sum_range_succ _ _
  have h0 : (0 : ℝ) ≤ (0 : ℝ) ^ k := pow_nonneg le_rfl k
  have := sum_pow_lower k n
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith

lemma sum_j_dif (k n : ℕ) :
    ∑ j ∈ range (n + 1), (j : ℝ) * dif (fun i : ℕ => (i : ℝ) ^ k) (n - j) =
      ∑ i ∈ range n, (i : ℝ) ^ k := by
  set P : ℕ → ℝ := fun i => (i : ℝ) ^ k with hP
  have h1 := abel_conv P n (fun _ => 1)
  simp only [one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h1
  have h2 : ∑ j ∈ range (n + 1), dif P (n - j) = P n := by
    rw [sum_reflect (dif P) n]; exact sum_dif P n
  have h3 : ∑ m ∈ range (n + 1), P (n - m) = ∑ i ∈ range n, (i : ℝ) ^ k + (n : ℝ) ^ k := by
    rw [sum_reflect P n, sum_range_succ]
  have h4 : ∑ j ∈ range (n + 1), (j : ℝ) * dif P (n - j) =
      ∑ j ∈ range (n + 1), (((j + 1 : ℕ) : ℝ)) * dif P (n - j) - ∑ j ∈ range (n + 1), dif P (n - j) := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
  rw [h4, ← h1, h2, h3]
  simp [hP]

/-- The weighted sum `W_k` against the main term. -/
lemma W_pow_approx (d a k : ℕ) (B δ : ℝ) (hδ : 0 ≤ δ)
    (hB : ∀ j : ℕ, |HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ)| ≤ B + δ * j)
    (n : ℕ) :
    |∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k
      - (∑ i ∈ range n, (i : ℝ) ^ k) / (Nat.totient d : ℝ)| ≤ (B + δ * n) * (n : ℝ) ^ k := by
  set P : ℕ → ℝ := fun i => (i : ℝ) ^ k with hP
  have e1 : ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k =
      ∑ m ∈ range (n + 1), gfun d a m * P (n - m) := by
    apply sum_congr rfl; intro m hm
    have : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
    simp only [hP]; rw [Nat.cast_sub this]
  rw [e1, abel_conv, ← sum_j_dif, sum_div, ← sum_sub_distrib]
  calc _ ≤ ∑ j ∈ range (n + 1), |(∑ m ∈ range (j + 1), gfun d a m) * dif P (n - j)
          - (j : ℝ) * dif P (n - j) / (Nat.totient d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (n + 1), (B + δ * n) * dif P (n - j) := by
        apply sum_le_sum; intro j hj
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hj)
        have hD := dif_pow_nonneg k (n - j)
        have : (∑ m ∈ range (j + 1), gfun d a m) * dif P (n - j)
            - (j : ℝ) * dif P (n - j) / (Nat.totient d : ℝ) =
            (HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ)) * dif P (n - j) := by
          rw [psi_eq_sum_gfun]; ring
        rw [this, abs_mul, abs_of_nonneg hD]
        apply mul_le_mul_of_nonneg_right _ hD
        exact (hB j).trans (by nlinarith)
    _ = (B + δ * n) * (n : ℝ) ^ k := by
        rw [← mul_sum, sum_reflect (dif P) n, sum_dif]

lemma T_le_W_pow (d a n k : ℕ) :
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), Real.log p * ((n : ℝ) - p) ^ k
      ≤ ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k := by
  rw [sum_filter]
  refine sum_le_sum fun m hm => ?_
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hm)
  split_ifs with h
  · simp [gfun, h.2, ArithmeticFunction.vonMangoldt_apply_prime h.1]
  · unfold gfun; split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg (sub_nonneg.2 hm') _)
    · simp

lemma W_sub_T_le_pow (d a n k : ℕ) :
    ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k
      - ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
          Real.log p * ((n : ℝ) - p) ^ k
      ≤ (n : ℝ) ^ k * (Chebyshev.psi n - Chebyshev.theta n) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter,
    sum_filter, sum_Ioc_zero_eq_range _ (by simp), mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun m hm => ?_
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hm)
  have hsq : ((n : ℝ) - m) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ (sub_nonneg.2 hm') (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) k
  have hsq0 : 0 ≤ ((n : ℝ) - m) ^ k := pow_nonneg (sub_nonneg.2 hm') k
  have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  by_cases hp : m.Prime
  · by_cases hc : m % d = a % d
    · simp [gfun, hp, hc, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [gfun, hp, hc]
  · simp only [hp, false_and, ite_false, sub_zero, not_false_eq_true, ite_true]
    unfold gfun; split_ifs
    · rw [mul_comm ((n : ℝ) ^ k)]; exact mul_le_mul_of_nonneg_left hsq hΛ
    · rw [zero_mul]; exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) hΛ

lemma ap_sum_pow_eventually (k d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : Nat.Coprime a d) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
    |∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
        Real.log p * ((n : ℝ) - p) ^ k
      - (n : ℝ) ^ (k + 1) / ((k + 1) * (Nat.totient d : ℝ))| ≤ ε * (n : ℝ) ^ (k + 1) := by
  set δ := ε / 5 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨B, hB0, hB⟩ := exists_B _ δ hδ.le (psi_ap_eventually d a hd ha δ hδ)
  have hφ : (1 : ℝ) ≤ Nat.totient d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.2 (by omega)).ne'
  filter_upwards [eventually_log_le (δ / 2) (1 / 2) (by positivity) (by norm_num),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (B / δ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / δ),
    eventually_ge_atTop 2] with n h1 h3 h4 h5
  have hWM := W_pow_approx d a k B δ hδ.le hB n
  have hTW := T_le_W_pow d a n k
  have hWT := W_sub_T_le_pow d a n k
  have hup := sum_pow_upper k n
  have hlo := sum_pow_lower' k n
  set N : ℝ := (n : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast h5
  have hN0 : 0 < N := by linarith
  set φ : ℝ := (Nat.totient d : ℝ) with hφdef
  set S := ∑ i ∈ range n, (i : ℝ) ^ k with hSdef
  set T := ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
    Real.log p * ((n : ℝ) - p) ^ k with hTdef
  set W := ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k with hWdef
  have hNk : 0 < N ^ k := pow_pos hN0 k
  have hNk1 : N ^ (k + 1) = N ^ k * N := pow_succ N k
  have hps : Chebyshev.psi N - Chebyshev.theta N ≤ δ * N := by
    refine (Chebyshev.psi_sub_theta_le (by linarith)).trans ?_
    rw [← Real.sqrt_eq_rpow] at h1
    have hs := Real.mul_self_sqrt hN0.le
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt N)
    nlinarith
  have hWT' : W - T ≤ δ * N ^ (k + 1) := by
    have := mul_le_mul_of_nonneg_left hps hNk.le
    rw [hNk1]; linarith
  have hBN : B ≤ δ * N := by rwa [div_le_iff₀ hδ, mul_comm] at h3
  have h1N : 1 ≤ δ * N := by rwa [div_le_iff₀ hδ, mul_comm] at h4
  have hWS : |W - S / φ| ≤ 2 * δ * N ^ (k + 1) := by
    refine hWM.trans ?_
    have := mul_le_mul_of_nonneg_right (by linarith : B + δ * N ≤ 2 * (δ * N)) hNk.le
    rw [hNk1]; linarith
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hφ0 : 0 < φ := by linarith
  have hSM : |S / φ - N ^ (k + 1) / (((k : ℝ) + 1) * φ)| ≤ δ * N ^ (k + 1) := by
    have e : S / φ - N ^ (k + 1) / (((k : ℝ) + 1) * φ) =
        (((k : ℝ) + 1) * S - N ^ (k + 1)) / (((k : ℝ) + 1) * φ) := by
      field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hk0 hφ0), div_le_iff₀ (mul_pos hk0 hφ0)]
    have hX : |((k : ℝ) + 1) * S - N ^ (k + 1)| ≤ ((k : ℝ) + 1) * N ^ k :=
      abs_le.2 ⟨by linarith, by nlinarith⟩
    refine hX.trans ?_
    have a1 : ((k : ℝ) + 1) * N ^ k ≤ ((k : ℝ) + 1) * N ^ k * φ :=
      le_mul_of_one_le_right (by positivity) hφ
    have a2 : ((k : ℝ) + 1) * N ^ k * φ ≤ δ * N ^ (k + 1) * (((k : ℝ) + 1) * φ) := by
      rw [hNk1]
      have : 0 ≤ ((k : ℝ) + 1) * N ^ k * φ := by positivity
      nlinarith
    linarith
  have hT0 : 0 ≤ W - T := by linarith
  have hWS' := abs_le.1 hWS
  have hSM' := abs_le.1 hSM
  have hpos : 0 ≤ N ^ (k + 1) := by positivity
  have h4 : δ * N ^ (k + 1) * 4 ≤ ε * N ^ (k + 1) := by
    have := mul_le_mul_of_nonneg_right (show δ * 4 ≤ ε by rw [hδdef]; linarith) hpos
    linarith
  clear_value T W S φ N
  rw [abs_le]
  constructor <;> linarith

/-- PNT in progressions with power weight. -/
theorem ap_sum_pow (k d : ℕ) (hd : 1 ≤ d) : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a : ℕ,
    Nat.Coprime a d →
    |∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d),
        Real.log p * ((n : ℝ) - p) ^ k
      - (n : ℝ) ^ (k + 1) / ((k + 1) * (Nat.totient d : ℝ))| ≤ ε * (n : ℝ) ^ (k + 1) := by
  intro ε hε
  have h : ∀ᶠ n : ℕ in atTop, ∀ r ∈ range d, Nat.Coprime r d →
      |∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = r % d),
          Real.log p * ((n : ℝ) - p) ^ k
        - (n : ℝ) ^ (k + 1) / ((k + 1) * (Nat.totient d : ℝ))| ≤ ε * (n : ℝ) ^ (k + 1) := by
    rw [eventually_all_finset]
    intro r _
    by_cases hr : Nat.Coprime r d
    · exact (ap_sum_pow_eventually k d hd r hr ε hε).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n hn => absurd hn hr
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  refine ⟨n₀, fun n hn a ha => ?_⟩
  have hra : Nat.Coprime (a % d) d := by
    unfold Nat.Coprime; rw [← Nat.gcd_rec]; exact Nat.Coprime.symm ha
  have := hn₀ n hn (a % d) (mem_range.2 (Nat.mod_lt _ (by omega))) hra
  simpa only [Nat.mod_mod] using this

/-- Uniform upper bound in the modulus, from Brun-Titchmarsh, with `A = 8`, `B = 4`. -/
theorem ap_log_sum_le : ∃ A B : ℝ, ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ d a : ℕ, 1 ≤ d →
    ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d), Real.log p
      ≤ A * n / (Nat.totient d : ℝ) + B * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hev := eventually_log_le 1 (1 / 16) one_pos (by norm_num)
  have hev2 : ∀ᶠ n : ℕ in atTop, (4 / 3 : ℝ) ≤ Real.log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hev.and (hev2.and (eventually_ge_atTop 2)))
  refine ⟨8, 4, n₁, fun n hn d a hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hn₁ n hn
  set N : ℝ := (n : ℝ) with hNdef
  have hN : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast h3
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 < L := by linarith
  set z : ℝ := N ^ ((1 : ℝ) / 4) with hzdef
  have hz1 : 1 < z := Real.one_lt_rpow (by linarith) (by norm_num)
  have hlz : Real.log z = L / 4 := by rw [hzdef, Real.log_rpow hN0]; ring
  have hBT := LeanLab.PNTSieve.BrunTitchmarshAP.brunTitchmarsh_ap (1 / 2) N z d a
    (by norm_num) hN0 hz1 (by omega)
  set P := (range (n + 1)).filter (fun p => p.Prime ∧ p % d = a % d) with hPdef
  have hsub : P ⊆ (Icc ⌈(1 / 2 : ℝ)⌉₊ ⌊(1 / 2 : ℝ) + N⌋₊).filter
      (fun p => p.Prime ∧ p % d = a % d) := by
    intro p hp
    rw [hPdef, mem_filter, mem_range] at hp
    rw [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · rw [Nat.ceil_le]
      have : (1 : ℝ) < p := by exact_mod_cast hp.2.1.one_lt
      linarith
    · rw [Nat.le_floor_iff (by positivity)]
      have : (p : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Nat.lt_succ_iff.1 hp.1
      linarith
  have hcard : (P.card : ℝ) ≤ 2 * N / ((d.totient : ℝ) * (L / 4)) + 4 * z * (1 + L / 4) ^ 3 := by
    rw [← hlz]; exact le_trans (by exact_mod_cast card_le_card hsub) hBT
  have hsum : ∑ p ∈ P, Real.log p ≤ P.card * L := by
    calc ∑ p ∈ P, Real.log p ≤ ∑ _p ∈ P, L := by
          apply sum_le_sum; intro p hp
          rw [hPdef, mem_filter, mem_range] at hp
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
          have hpn : (p : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Nat.lt_succ_iff.1 hp.1
          exact Real.log_le_log hp0 hpn
      _ = P.card * L := by rw [sum_const, nsmul_eq_mul]
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have e1 : 2 * N / ((d.totient : ℝ) * (L / 4)) * L = 8 * N / (d.totient : ℝ) := by
    field_simp; ring
  have hz0 : 0 < z := by linarith
  have e2 : 4 * z * (1 + L / 4) ^ 3 * L ≤ 4 * N ^ ((1 : ℝ) / 2) := by
    have a1 : (1 + L / 4) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h1' : L ≤ N ^ ((1 : ℝ) / 16) := by simpa using h1
    have a2 : L ^ 4 ≤ (N ^ ((1 : ℝ) / 16)) ^ 4 := pow_le_pow_left₀ hL.le h1' 4
    have a3 : (N ^ ((1 : ℝ) / 16)) ^ 4 = z := by
      rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have a4 : z * z = N ^ ((1 : ℝ) / 2) := by
      rw [hzdef, ← Real.rpow_add hN0]; norm_num
    have a5 : (1 + L / 4) ^ 3 * L ≤ L ^ 4 := by
      have := mul_le_mul_of_nonneg_right a1 hL.le
      linarith [show L ^ 3 * L = L ^ 4 by ring]
    have a6 : (1 + L / 4) ^ 3 * L ≤ z := by linarith
    have := mul_le_mul_of_nonneg_left a6 (by positivity : (0 : ℝ) ≤ 4 * z)
    nlinarith
  calc ∑ p ∈ P, Real.log p ≤ P.card * L := hsum
    _ ≤ (2 * N / ((d.totient : ℝ) * (L / 4)) + 4 * z * (1 + L / 4) ^ 3) * L :=
        mul_le_mul_of_nonneg_right hcard hL.le
    _ = 2 * N / ((d.totient : ℝ) * (L / 4)) * L + 4 * z * (1 + L / 4) ^ 3 * L := by ring
    _ ≤ 8 * N / (d.totient : ℝ) + 4 * N ^ ((1 : ℝ) / 2) := by rw [e1]; linarith

/-- Chebyshev: θ(n) ≤ log 4 · n, e.g. from Mathlib's primorial_le_4_pow. -/
theorem theta_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have e : Chebyshev.theta (n : ℝ) = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, sum_filter, sum_filter]
    exact sum_Ioc_zero_eq_range _ (by simp) n
  rw [← e]; exact h

end LeanLab.HardyLittlewood1923

