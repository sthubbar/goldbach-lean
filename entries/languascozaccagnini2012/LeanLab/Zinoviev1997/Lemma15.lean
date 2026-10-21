module

public import Mathlib
public import LeanLab.ChebyshevExplicit.Psi30Upper
public import LeanLab.Zinoviev1997.Arith

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T2314Z-cloud29, unit U-5754, paper P0097.

# Zinoviev 1997, Lemma 1.5, unconditional, from Chebyshev's constants

Lemma 1.5, p. 341: `Σ_{p > 2} ln²(p) e^{-2p/N} < 0.96 N ln N`, used with Parseval in (3.17), p. 357.
Here `lemma15`: for every natural `N ≥ 10^20` and every cutoff `M`,
`Σ_{1 ≤ n ≤ M} Λ(n)² e^{-2n/N} ≤ 0.96 N ln N`. The sum over all prime powers is the one that
Parseval actually gives for `S(α) = Σ Λ(n) e(-αn) e^{-n/N}`; the printed (3.17) keeps only
the odd primes, `lemma15_primes` is that form.

Proof, the lab's own: blocks `kN/4 ≤ n < (k+1)N/4`; on block `k`,
`ln n · e^{-2n/N} ≤ L e^{-k/2} + e^{-1} e^{-k/4}` with `L = ln N`, by `ln n ≤ L + n/N` and
`t e^{-t} ≤ e^{-1}`; the prime mass of a block is at most `(1.1062 + 0.185k) N/4` plus lower
order, by `ChebyshevExplicit.psi_le_11062` and `psi_ge_09212`; then two geometric series. The
model constant is `0.887 L + 0.734`, below `0.96 L` for `L ≥ 10`. No cited input.

Binary Goldbach is OPEN; this is an input of the ternary problem under GRH.
-/

@[expose] public section

namespace LeanLab.Zinoviev1997
open Real Finset ArithmeticFunction

/-- `ln n · e^{-2n/N} ≤ L e^{-k/2} + e^{-1} e^{-k/4}` on block `k = ⌊4n/N⌋`. -/
theorem weight_le (N n : ℕ) (hN : 0 < N) (hn : 1 ≤ n) :
    Real.log n * exp (-2 * n / N) ≤
      Real.log N * exp (-1 / 2) ^ ⌊4 * (n : ℝ) / N⌋₊ +
        exp (-1) * exp (-1 / 4) ^ ⌊4 * (n : ℝ) / N⌋₊ := by
  set k := ⌊4 * (n : ℝ) / N⌋₊ with hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkle : (k : ℝ) ≤ 4 * n / N := Nat.floor_le (by positivity)
  set t := (n : ℝ) / N with ht
  have ht0 : 0 < t := by positivity
  have hkt : (k : ℝ) ≤ 4 * t := by rw [ht]; linarith [show 4 * (n : ℝ) / N = 4 * (n / N) by ring]
  -- ln n ≤ L + t
  have hlog : Real.log n ≤ Real.log N + t := by
    have h1 : Real.log n = Real.log N + Real.log t := by
      rw [ht, Real.log_div hn0.ne' hN0.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos ht0
    linarith
  have hexp : exp (-2 * n / N) = exp (-t) * exp (-t) := by
    rw [← Real.exp_add]; congr 1; rw [ht]; ring
  have ha : exp (-2 * n / N) ≤ exp (-1 / 2) ^ k := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
    rw [show -2 * (n : ℝ) / N = -2 * t by rw [ht]; ring]; linarith
  have hb : exp (-t) ≤ exp (-1 / 4) ^ k := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; linarith
  -- t e^{-t} ≤ e^{-1}
  have hte : t * exp (-t) ≤ exp (-1) := by
    have h := Real.add_one_le_exp (t - 1)
    have : t ≤ exp (t - 1) := by linarith
    calc t * exp (-t) ≤ exp (t - 1) * exp (-t) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = exp (-1) := by rw [← Real.exp_add]; ring_nf
  have hE0 : 0 ≤ exp (-2 * n / N) := (Real.exp_pos _).le
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc Real.log n * exp (-2 * n / N) ≤ (Real.log N + t) * exp (-2 * n / N) :=
        mul_le_mul_of_nonneg_right hlog hE0
    _ = Real.log N * exp (-2 * n / N) + (t * exp (-t)) * exp (-t) := by rw [hexp]; ring
    _ ≤ Real.log N * exp (-1 / 2) ^ k + exp (-1) * exp (-1 / 4) ^ k := by
        gcongr

/-- `Σ_{a < n ≤ b} Λ(n) = ψ(b) - ψ(a)`. -/
theorem sum_Ioc_vonMangoldt {a b : ℕ} (h : a ≤ b) :
    ∑ n ∈ Ioc a b, Λ n = Chebyshev.psi b - Chebyshev.psi a := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast]
  have hs : Icc 0 a ⊆ Icc 0 b := Finset.Icc_subset_Icc le_rfl h
  have he : Icc 0 b \ Icc 0 a = Ioc a b := by
    ext n; simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [← Finset.sum_sdiff hs, he]; ring

/-- `4 ln²N + 5 ln N + 188 ≤ 0.00025 N` for `N ≥ 10^20`. -/
theorem logN_small (N : ℝ) (hN : 10 ^ 20 ≤ N) :
    4 * Real.log N ^ 2 + 5 * Real.log N + 188 ≤ 0.00025 * N := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  set s := N ^ ((1 : ℝ) / 4) with hs
  have hs4 : s ^ 4 = N := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hs0 : 0 ≤ s := Real.rpow_nonneg hN0.le _
  have hs5 : (10 : ℝ) ^ 5 ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 4 < ((10 : ℝ) ^ 5) ^ 4 := pow_lt_pow_left₀ h hs0 (by norm_num)
    rw [hs4] at this; norm_num at this; linarith
  have hlog : Real.log N ≤ 4 * s := by
    have := Real.log_le_rpow_div hN0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hs] at this; linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h1 : Real.log N ^ 2 ≤ 16 * s ^ 2 := by nlinarith
  have hs2 : (10 : ℝ) ^ 10 * s ^ 2 ≤ N := by rw [← hs4]; nlinarith
  have hs3 : (10 : ℝ) ^ 5 * s ≤ s ^ 2 := by nlinarith
  nlinarith

/-- `ln y ≤ 2 √y` and so `ln² y ≤ 4 y` for `y ≥ 1`. -/
theorem log_sq_le (y : ℝ) (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have hy0 : 0 < y := by linarith
  have h := Real.log_le_rpow_div hy0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h0 := Real.log_nonneg hy
  have hr : (y ^ ((1 : ℝ) / 2)) ^ 2 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hr0 : 0 ≤ y ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0.le _
  have : Real.log y ≤ 2 * y ^ ((1 : ℝ) / 2) := by linarith
  nlinarith

/-- The lower order terms of a block: `2ℓ² + 5ℓ + 162 ≤ 0.00025 (k+1) N`, `ℓ = ln((k+1)N)`. -/
theorem err_le (N : ℝ) (hN : 10 ^ 20 ≤ N) (k : ℕ) :
    2 * Real.log ((k + 1) * N) ^ 2 + 5 * Real.log ((k + 1) * N) + 162 ≤
      0.00025 * ((k + 1) * N) := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hk1 : (1 : ℝ) ≤ k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hsplit : Real.log ((k + 1) * N) = Real.log (k + 1) + Real.log N :=
    Real.log_mul (by linarith) hN0.ne'
  set lam := Real.log ((k : ℝ) + 1)
  set L := Real.log N
  have hl0 : 0 ≤ lam := Real.log_nonneg hk1
  have hl1 : lam ≤ k + 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < k + 1); linarith
  have hl2 : lam ^ 2 ≤ 4 * (k + 1) := log_sq_le _ hk1
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hsm := logN_small N hN
  rw [hsplit]
  have hA : 2 * (lam + L) ^ 2 + 5 * (lam + L) + 162 ≤ (k + 1) * (4 * L ^ 2 + 5 * L + 188) := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hP : 0 ≤ 4 * L ^ 2 + 5 * L := by positivity
    have h1 : 2 * (lam + L) ^ 2 ≤ 4 * lam ^ 2 + 4 * L ^ 2 := by nlinarith [sq_nonneg (lam - L)]
    have h2 : (k : ℝ) * (4 * L ^ 2 + 5 * L) ≥ 0 := mul_nonneg hk0 hP
    nlinarith
  calc 2 * (lam + L) ^ 2 + 5 * (lam + L) + 162 ≤ (k + 1) * (4 * L ^ 2 + 5 * L + 188) := hA
    _ ≤ (k + 1) * (0.00025 * N) := mul_le_mul_of_nonneg_left hsm (by linarith)
    _ = 0.00025 * ((k + 1) * N) := by ring

/-- The prime mass of block `k`: `Σ_{n ≤ M, ⌊4n/N⌋ = k} Λ(n) ≤ (1.1072 + 0.186 k) N/4`. -/
theorem block_le (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (M k : ℕ) :
    ∑ n ∈ (Icc 1 M).filter (fun n : ℕ => ⌊4 * (n : ℝ) / N⌋₊ = k), Λ n ≤
      (1.1072 + 0.186 * k) * N / 4 := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  set a := ⌊(k : ℝ) * N / 4⌋₊ - 1 with ha
  set b := ⌊((k : ℝ) + 1) * N / 4⌋₊ with hb
  have hab : a ≤ b := by
    have : ⌊(k : ℝ) * N / 4⌋₊ ≤ b := Nat.floor_mono (by nlinarith)
    omega
  have hsub : (Icc 1 M).filter (fun n : ℕ => ⌊4 * (n : ℝ) / N⌋₊ = k) ⊆ Ioc a b := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, -⟩, hk⟩ := hn
    have hnr : (0 : ℝ) ≤ 4 * n / N := by positivity
    rw [Nat.floor_eq_iff hnr] at hk
    obtain ⟨h1, h2⟩ := hk
    simp only [Finset.mem_Ioc]
    constructor
    · have : ⌊(k : ℝ) * N / 4⌋₊ ≤ n := by
        apply Nat.floor_le_of_le
        rw [le_div_iff₀ hN0] at h1; linarith
      omega
    · apply Nat.le_floor
      rw [div_lt_iff₀ hN0] at h2; linarith
  calc ∑ n ∈ (Icc 1 M).filter (fun n : ℕ => ⌊4 * (n : ℝ) / N⌋₊ = k), Λ n
      ≤ ∑ n ∈ Ioc a b, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = Chebyshev.psi b - Chebyshev.psi a := sum_Ioc_vonMangoldt hab
    _ ≤ (1.1072 + 0.186 * k) * N / 4 := by
      set ℓ := Real.log (((k : ℝ) + 1) * N)
      have hk1 : (1 : ℝ) ≤ k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
      have hkN : (1 : ℝ) ≤ (k + 1) * N := by nlinarith
      have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hkN
      have hbR : (b : ℝ) ≤ ((k : ℝ) + 1) * N / 4 := Nat.floor_le (by positivity)
      have hbℓ : Real.log b ^ 2 ≤ ℓ ^ 2 := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · rw [h0]; simp; positivity
        · have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast h0
          have h1 : Real.log b ≤ ℓ := Real.log_le_log (by linarith) (by linarith)
          have h2 := Real.log_nonneg hb1
          nlinarith
      have hup := LeanLab.ChebyshevExplicit.psi_le_11062 b
      have hlow : 0.9212 * ((k : ℝ) * N / 4) - 1.85 - 5 * ℓ ≤ Chebyshev.psi a := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · have : a = 0 := by rw [ha, hk0]; simp
          rw [this, hk0]; simp; nlinarith [Chebyshev.psi_nonneg 0]
        · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
          have hx : (k : ℝ) * N / 4 ≥ 2.5e19 := by nlinarith
          have hfl := Nat.lt_floor_add_one ((k : ℝ) * N / 4)
          have hfl1 : 1 ≤ ⌊(k : ℝ) * N / 4⌋₊ := by
            apply Nat.le_floor; push_cast; linarith
          have haR : ((k : ℝ) * N / 4) - 2 ≤ a := by
            rw [ha, Nat.cast_sub hfl1]; push_cast; linarith
          have ha30 : 30 ≤ a := by
            have : (30 : ℝ) ≤ a := by linarith
            exact_mod_cast this
          have hlow0 := LeanLab.ChebyshevExplicit.psi_ge_09212 a ha30
          have haR' : (a : ℝ) ≤ ((k : ℝ) + 1) * N := by
            have : (a : ℝ) ≤ ⌊(k : ℝ) * N / 4⌋₊ := by
              rw [ha]; exact_mod_cast Nat.sub_le _ _
            have h2 : (⌊(k : ℝ) * N / 4⌋₊ : ℝ) ≤ (k : ℝ) * N / 4 := Nat.floor_le (by positivity)
            nlinarith
          have hla : Real.log a ≤ ℓ :=
            Real.log_le_log (by have : (30 : ℝ) ≤ a := by exact_mod_cast ha30
                                linarith) haR'
          linarith
      have herr := err_le N hN k
      nlinarith

/-- `(1 - r) Σ_{k<m} r^k = 1 - r^m`. -/
theorem geom0_id (r : ℝ) (m : ℕ) : (1 - r) * ∑ k ∈ range m, r ^ k = 1 - r ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- `(1 - r)² Σ_{k<m} k r^k = r - m r^m + (m - 1) r^{m+1}`. -/
theorem geom1_id (r : ℝ) (m : ℕ) :
    (1 - r) ^ 2 * ∑ k ∈ range m, (k : ℝ) * r ^ k = r - m * r ^ m + (m - 1) * r ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem geom0_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (m : ℕ) :
    ∑ k ∈ range m, r ^ k ≤ 1 / (1 - r) := by
  rw [le_div_iff₀ (by linarith), mul_comm, geom0_id]
  have := pow_nonneg h0 m; linarith

theorem geom1_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (m : ℕ) :
    ∑ k ∈ range m, (k : ℝ) * r ^ k ≤ r / (1 - r) ^ 2 := by
  rw [le_div_iff₀ (by nlinarith), mul_comm, geom1_id]
  have hr : r ^ (m + 1) = r ^ m * r := pow_succ r m
  have hm := pow_nonneg h0 m
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [h0]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
    rw [hr]; nlinarith [mul_nonneg hm (by linarith : (0 : ℝ) ≤ 1 - r)]

/-- `e^{-1} < 0.36788`. -/
theorem exp_neg_one_lt : exp (-1) < 0.36788 := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith [Real.exp_one_gt_d9]

theorem a_le : exp (-1 / 2) ≤ 0.6066 := by
  have h : exp (-1 / 2) ^ 2 = exp (-1) := by rw [← Real.exp_nat_mul]; norm_num
  rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (two_ne_zero), h]
  linarith [exp_neg_one_lt]

theorem b_le : exp (-1 / 4) ≤ 0.7789 := by
  have h : exp (-1 / 4) ^ 4 = exp (-1) := by rw [← Real.exp_nat_mul]; norm_num
  rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (four_ne_zero), h]
  linarith [exp_neg_one_lt]

/-- **Zinoviev 1997, Lemma 1.5**, p. 341, in the prime power form that Parseval gives: for every
natural `N ≥ 10^20` and every cutoff `M`, `Σ_{1 ≤ n ≤ M} Λ(n)² e^{-2n/N} ≤ 0.96 N ln N`.
PROVED unconditional. -/
theorem lemma15 (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (M : ℕ) :
    ∑ n ∈ Icc 1 M, Λ n ^ 2 * exp (-2 * n / N) ≤ 0.96 * N * Real.log N := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hNn : 0 < N := by exact_mod_cast hN0
  set a := exp (-1 / 2) with hadef
  set b := exp (-1 / 4) with hbdef
  set c := exp (-1) with hcdef
  set L := Real.log N with hLdef
  have hL46 : 46 ≤ L := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  set kf : ℕ → ℕ := fun n => ⌊4 * (n : ℝ) / N⌋₊ with hkf
  set w : ℕ → ℝ := fun k => L * a ^ k + c * b ^ k with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    simp only [hw]; have := Real.exp_pos (-1 / 2); have := Real.exp_pos (-1 / 4)
    have := Real.exp_pos (-1); positivity
  -- step 1, pointwise
  have h1 : ∀ n ∈ Icc 1 M, Λ n ^ 2 * exp (-2 * n / N) ≤ Λ n * w (kf n) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
    have hΛ : Λ n ≤ Real.log n := vonMangoldt_le_log
    have hwt := weight_le N n hNn hn.1
    calc Λ n ^ 2 * exp (-2 * n / N) = Λ n * (Λ n * exp (-2 * n / N)) := by ring
      _ ≤ Λ n * (Real.log n * exp (-2 * n / N)) := by
          gcongr
      _ ≤ Λ n * w (kf n) := mul_le_mul_of_nonneg_left hwt hΛ0
  -- step 2, fibres
  set K := kf M
  have hmaps : ∀ n ∈ Icc 1 M, kf n ∈ range (K + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range, hkf]
    have : ⌊4 * (n : ℝ) / N⌋₊ ≤ ⌊4 * (M : ℝ) / N⌋₊ := by
      apply Nat.floor_mono
      have : (n : ℝ) ≤ M := by exact_mod_cast hn.2
      gcongr
    exact Nat.lt_succ_of_le this
  have h2 : ∑ n ∈ Icc 1 M, Λ n * w (kf n) =
      ∑ k ∈ range (K + 1), w k * ∑ n ∈ (Icc 1 M).filter (fun n : ℕ => kf n = k), Λ n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_filter] at hn
    rw [hn.2, mul_comm]
  -- step 3, blocks
  have h3 : ∑ k ∈ range (K + 1), w k * ∑ n ∈ (Icc 1 M).filter (fun n : ℕ => kf n = k), Λ n ≤
      ∑ k ∈ range (K + 1), w k * ((1.1072 + 0.186 * k) * N / 4) := by
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hw0 k)
    exact block_le N hN M k
  -- step 4, series
  have hexp : ∑ k ∈ range (K + 1), w k * ((1.1072 + 0.186 * k) * N / 4) =
      N / 4 * (L * (1.1072 * ∑ k ∈ range (K + 1), a ^ k +
        0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * a ^ k) +
        c * (1.1072 * ∑ k ∈ range (K + 1), b ^ k +
        0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * b ^ k)) := by
    simp only [hw, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have ha1 := a_le
  have hb1 := b_le
  have hc1 := exp_neg_one_lt
  have A0 := geom0_le a ha0 (by linarith) (K + 1)
  have A1 := geom1_le a ha0 (by linarith) (K + 1)
  have B0 := geom0_le b hb0 (by linarith) (K + 1)
  have B1 := geom1_le b hb0 (by linarith) (K + 1)
  have nA0 : 1 / (1 - a) ≤ 2.5420 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have nA1 : a / (1 - a) ^ 2 ≤ 3.9197 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have nB0 : 1 / (1 - b) ≤ 4.5230 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have nB1 : b / (1 - b) ^ 2 ≤ 15.934 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have hS : L * (1.1072 * ∑ k ∈ range (K + 1), a ^ k +
        0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * a ^ k) +
        c * (1.1072 * ∑ k ∈ range (K + 1), b ^ k +
        0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * b ^ k) ≤ 3.84 * L := by
    have e1 : 1.1072 * ∑ k ∈ range (K + 1), a ^ k + 0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * a ^ k
        ≤ 3.5436 := by linarith
    have e2 : 1.1072 * ∑ k ∈ range (K + 1), b ^ k + 0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * b ^ k
        ≤ 7.9716 := by linarith
    have e3 : 0 ≤ 1.1072 * ∑ k ∈ range (K + 1), b ^ k +
        0.186 * ∑ k ∈ range (K + 1), (k : ℝ) * b ^ k := by
      have : 0 ≤ ∑ k ∈ range (K + 1), b ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hb0 k
      have : 0 ≤ ∑ k ∈ range (K + 1), (k : ℝ) * b ^ k :=
        Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hb0 k)
      positivity
    have hL0 : 0 ≤ L := by linarith
    have f1 := mul_le_mul_of_nonneg_left e1 hL0
    have f2 := mul_le_mul hc1.le e2 e3 (by norm_num)
    linarith
  calc ∑ n ∈ Icc 1 M, Λ n ^ 2 * exp (-2 * n / N) ≤ ∑ n ∈ Icc 1 M, Λ n * w (kf n) :=
        Finset.sum_le_sum h1
    _ = _ := h2
    _ ≤ _ := h3
    _ = _ := hexp
    _ ≤ N / 4 * (3.84 * L) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 0.96 * N * Real.log N := by rw [hLdef]; ring

/-- Lemma 1.5 as printed, over the odd primes: `Σ_{2 < p ≤ M} ln²p e^{-2p/N} ≤ 0.96 N ln N`. -/
theorem lemma15_primes (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (M : ℕ) :
    ∑ p ∈ (Icc 3 M).filter Nat.Prime, Real.log p ^ 2 * exp (-2 * p / N) ≤
      0.96 * N * Real.log N := by
  refine le_trans ?_ (lemma15 N hN M)
  calc ∑ p ∈ (Icc 3 M).filter Nat.Prime, Real.log p ^ 2 * exp (-2 * p / N)
      = ∑ p ∈ (Icc 3 M).filter Nat.Prime, Λ p ^ 2 * exp (-2 * p / N) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [Finset.mem_filter] at hp
        rw [vonMangoldt_apply_prime hp.2]
    _ ≤ ∑ n ∈ Icc 1 M, Λ n ^ 2 * exp (-2 * n / N) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢; omega
        · intro n _ _; exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

end LeanLab.Zinoviev1997

