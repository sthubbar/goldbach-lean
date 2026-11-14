module

public import Mathlib
public import LeanLab.Linnik.U7201Lemma14

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, the proof of
Theorem 1 on p.139-140, read from the page images, PDF pages 15 to 17: Lemma 13, display (3)
of p.138, and the expansion of the square on p.139. Unit U-7204, CLOUD MANUAL-N2, 2026-10-21.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Gallagher's proof of Theorem 1, `g = 2`, `D = 2`, `φ(D) = 1`, `λ = 2 L^k / log N`:
`Σ'(r'_k(n) - λ)² = Σ' r'_k(n)² - 2λ Σ' r'_k(n) + λ² Σ' 1`, the dash meaning `n` odd; the
first sum by Lemma 13, the second by Lemma 14 less the even terms, at most `L^k`, the third is
`[(N+1)/2]`.

* `Lemma13`: Gallagher's Lemma 13, display (3), p.138, cited as a `Prop`, NOT proved here.
  It is the second moment bound that the circle method of Sections 1 to 3 delivers, by Theorem 3,
  Lemmas 2, 5 to 12 and the Brun-Selberg sieve.
* `card_odd`: PROVED, `#{n ≤ N, n odd} = (N + 1) / 2`.
* `key_alg`: PROVED, the real arithmetic of the expansion.
* `theorem1_of`: PROVED, `Lemma13 → Lemma14 → Theorem1`, the paper's proof of Theorem 1.
* `theorem1_of_lemma13`: Theorem 1, display (3), CONDITIONAL ON `Lemma13` alone, since
  `Lemma14` is PROVED in U7201Lemma14.lean.
* `theorem2_of_lemma13`: Theorem 2, display (4), `g = 2`, CONDITIONAL ON `Lemma13` alone.

Faithfulness remark, QUESTION level, not a paper error: the paper writes `O(log² k / k)` in (3)
for `k ≥ 1`, which is `0` at `k = 1`; read literally at `k = 1` the bound would say
`Σ r'_1(n)² ≤ 2 N L² / log² N` with constant 1, and numerics/lemma13_U7204.out gives the
ratio 1.39 at `N = 2^20`, above 1. The lab reads `log² k` as `log² 2k`, as `Theorem1` already
does; for `k ≥ 2` the two differ by at most a factor 4.
-/

@[expose] public section

open Finset Real Filter
open scoped Topology

noncomputable section
namespace LeanLab.Linnik.U7204

open LeanLab.Linnik.Gallagher1975 LeanLab.Linnik.Gallagher1975Thm2 LeanLab.Linnik.U7201

/-- **Gallagher 1975, Lemma 13**, display (3), p.138, `g = 2`, so `D / φ(D) = 2`, cited: for
`k ≥ 1` and `N ≥ N_k`, `Σ_{n ≤ N} r'_k(n)² ≤ (2 N L^{2k} / log² N)(1 + O(log² 2k / k))`, with an
absolute `O`, `L = [log₂ N]`. The paper prints `log² k`; see the module docstring. -/
def Lemma13 : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ∑ n ∈ range (N + 1), (rk k N n : ℝ) ^ 2 ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 * (1 + C * (Real.log (2 * k) ^ 2 / k))

/-- The odd `n ≤ N` number `(N + 1) / 2`. -/
theorem card_odd (N : ℕ) : #{n ∈ range (N + 1) | Odd n} = (N + 1) / 2 := by
  induction N with
  | zero => decide
  | succ n ih =>
    rw [range_add_one, filter_insert]
    by_cases h : Odd (n + 1)
    · rw [if_pos h, card_insert_of_notMem (by simp), ih]
      obtain ⟨m, hm⟩ := h; omega
    · rw [if_neg h, ih]
      rw [Nat.not_odd_iff_even] at h
      obtain ⟨m, hm⟩ := h; omega

/-- The real arithmetic of the proof of Theorem 1, p.139: with `X = N L^{2k} / log² N`,
`λ = 2 L^k / log N`, the three sums combine to at most `(2C + 1) a X`. -/
theorem key_alg {S2 S1 c Nr Lk ℓ a ε C : ℝ} (hℓ : 0 < ℓ) (hNr : 0 < Nr) (hLk : 0 ≤ Lk)
    (h2 : S2 ≤ 2 * (Nr * Lk ^ 2 / ℓ ^ 2) * (1 + C * a))
    (h1 : (1 - ε) * (Nr * Lk / ℓ) - Lk ≤ S1)
    (hc : c ≤ (Nr + 1) / 2)
    (hε : 4 * ε ≤ a / 3) (hN1 : 2 / Nr ≤ a / 3) (hN2 : 4 * ℓ / Nr ≤ a / 3) :
    S2 - 2 * (2 * Lk / ℓ) * S1 + (2 * Lk / ℓ) ^ 2 * c ≤
      (2 * C + 1) * a * (Nr * Lk ^ 2 / ℓ ^ 2) := by
  set X := Nr * Lk ^ 2 / ℓ ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hlam : 0 ≤ 2 * Lk / ℓ := by positivity
  have e1 : 2 * (2 * Lk / ℓ) * ((1 - ε) * (Nr * Lk / ℓ) - Lk) =
      4 * X - 4 * ε * X - X * (4 * ℓ / Nr) := by
    rw [hX]; field_simp <;> ring
  have e2 : (2 * Lk / ℓ) ^ 2 * ((Nr + 1) / 2) = 2 * X + X * (2 / Nr) := by
    rw [hX]; field_simp <;> ring
  have t1 : 2 * (2 * Lk / ℓ) * ((1 - ε) * (Nr * Lk / ℓ) - Lk) ≤ 2 * (2 * Lk / ℓ) * S1 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have t2 : (2 * Lk / ℓ) ^ 2 * c ≤ (2 * Lk / ℓ) ^ 2 * ((Nr + 1) / 2) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have t3 : X * (4 * ℓ / Nr) ≤ X * (a / 3) := mul_le_mul_of_nonneg_left hN2 hX0
  have t4 : X * (2 / Nr) ≤ X * (a / 3) := mul_le_mul_of_nonneg_left hN1 hX0
  have t5 : 4 * ε * X ≤ a / 3 * X := mul_le_mul_of_nonneg_right hε hX0
  rw [e1] at t1
  rw [e2] at t2
  nlinarith

/-- `L² ≤ 3 log² N` scaled: `N L^{2k} / log² N ≤ 3 N L^{2k-2}` for `N ≥ 2`, `k ≥ 1`, from
`2^L ≤ N` and `log² 2 > 1/3`. -/
theorem X_le {k N : ℕ} (hk : 1 ≤ k) (hN : 2 ≤ N) :
    (N : ℝ) * ((Nat.log 2 N : ℝ) ^ k) ^ 2 / Real.log N ^ 2 ≤
      3 * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by
  set L : ℝ := (Nat.log 2 N : ℝ) with hL
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hL0 : 0 ≤ L := by positivity
  have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hLlog : L * Real.log 2 ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hlog2 : 0.6 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : L ^ 2 ≤ 3 * Real.log N ^ 2 := by
    have h0 : 0 ≤ L * Real.log 2 := by positivity
    have : (L * Real.log 2) ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ h0 hLlog 2
    have hsq : (0.36 : ℝ) < Real.log 2 ^ 2 := by nlinarith
    have h3 : L ^ 2 * 0.36 ≤ L ^ 2 * Real.log 2 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq.le (sq_nonneg L)
    rw [mul_pow] at this
    nlinarith [sq_nonneg L]
  have hk2 : (L ^ k) ^ 2 = L ^ (2 * k - 2) * L ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [hk2, div_le_iff₀ (by positivity)]
  have hP : 0 ≤ L ^ (2 * k - 2) := by positivity
  have := mul_le_mul_of_nonneg_left hL2 (mul_nonneg hNpos.le hP)
  nlinarith

/-- `log N / N → 0` and `2 / N → 0` along the naturals, in the form used below. -/
theorem eventually_small {a : ℝ} (ha : 0 < a) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      2 ≤ N ∧ 2 / (N : ℝ) ≤ a / 3 ∧ 4 * Real.log N / N ≤ a / 3 := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h1' : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) :=
    h1.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have e1 := (tendsto_order.1 h1').2 (a / 12) (by positivity)
  have e2 := (tendsto_order.1 h2).2 (a / 3) (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (e1.and (e2.and (eventually_ge_atTop 2)))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨h1N, h2N, h3N⟩ := hN0 N hN
  refine ⟨h3N, h2N.le, ?_⟩
  have : 4 * Real.log N / N = 4 * (Real.log N / N) := by ring
  rw [this]; linarith

/-- **The proof of Theorem 1**, p.139-140, PROVED: `Lemma13 → Lemma14 → Theorem1`. -/
theorem theorem1_of (h13 : Lemma13) (h14 : Lemma14) : Theorem1 := by
  obtain ⟨C0, hC0⟩ := h13
  set C := max C0 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨3 * (2 * C + 1), fun k hk => ?_⟩
  set a := Real.log (2 * k) ^ 2 / k with hadef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ha : 0 < a := by
    have : 0 < Real.log (2 * k) :=
      Real.log_pos (by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                       linarith)
    positivity
  obtain ⟨N13, hN13⟩ := hC0 k hk
  obtain ⟨N14, hN14⟩ := h14 k hk (a / 12) (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_small ha
  refine ⟨max N13 (max N14 N0), fun N hN => ?_⟩
  obtain ⟨hN2, hsm1, hsm2⟩ := hN0 N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hA := hN13 N (le_trans (le_max_left _ _) hN)
  have hB := hN14 N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  set L : ℝ := (Nat.log 2 N : ℝ) with hL
  set ℓ := Real.log N with hℓ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hℓpos : 0 < ℓ := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hL0 : 0 ≤ L := by positivity
  -- the three dashed sums
  set S2 := ∑ n ∈ range (N + 1) with Odd n, (rk k N n : ℝ) ^ 2 with hS2
  set S1 := ∑ n ∈ range (N + 1) with Odd n, (rk k N n : ℝ) with hS1
  set c : ℝ := ((#{n ∈ range (N + 1) | Odd n} : ℕ) : ℝ) with hc
  -- expansion of the square
  have hexp : ∑ n ∈ range (N + 1) with Odd n, ((rk k N n : ℝ) - 2 * L ^ k / ℓ) ^ 2 =
      S2 - 2 * (2 * L ^ k / ℓ) * S1 + (2 * L ^ k / ℓ) ^ 2 * c := by
    have : ∀ n ∈ {n ∈ range (N + 1) | Odd n}, ((rk k N n : ℝ) - 2 * L ^ k / ℓ) ^ 2 =
        (rk k N n : ℝ) ^ 2 - 2 * (2 * L ^ k / ℓ) * (rk k N n : ℝ) + (2 * L ^ k / ℓ) ^ 2 := by
      intro n _; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      nsmul_eq_mul, hc]
    ring
  -- Lemma 13 on the odd terms
  have h2 : S2 ≤ 2 * (N * (L ^ k) ^ 2 / ℓ ^ 2) * (1 + C * a) := by
    have hsub : S2 ≤ ∑ n ∈ range (N + 1), (rk k N n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    have hCa : C0 * a ≤ C * a := mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le
    have hX : 0 ≤ 2 * (N : ℝ) * L ^ (2 * k) / ℓ ^ 2 := by positivity
    have e : 2 * (N : ℝ) * L ^ (2 * k) / ℓ ^ 2 = 2 * (N * (L ^ k) ^ 2 / ℓ ^ 2) := by
      rw [← pow_mul, mul_comm k 2]; ring
    calc S2 ≤ _ := hsub
      _ ≤ _ := hA
      _ ≤ 2 * (N : ℝ) * L ^ (2 * k) / ℓ ^ 2 * (1 + C * a) :=
          mul_le_mul_of_nonneg_left (by linarith) hX
      _ = _ := by rw [e]
  -- Lemma 14 less the even terms
  have h1 : (1 - a / 12) * (N * L ^ k / ℓ) - L ^ k ≤ S1 := by
    have hsplit := sum_filter_add_sum_filter_not (range (N + 1)) (fun n => Odd n)
      (fun n => (rk k N n : ℝ))
    have heven : ∑ n ∈ range (N + 1) with ¬ Odd n, (rk k N n : ℝ) ≤ L ^ k := by
      have := even_sum_le k N
      have h' : ∑ n ∈ range (N + 1) with Even n, (rk k N n : ℝ) ≤ L ^ k := by
        rw [hL]; exact_mod_cast this
      simpa only [Nat.not_odd_iff_even] using h'
    have hlow := (abs_le.1 hB).1
    rw [← hS1] at hsplit
    nlinarith
  have hcard : c ≤ ((N : ℝ) + 1) / 2 := by
    rw [hc, card_odd]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : 2 * ((N + 1) / 2) ≤ N + 1 := Nat.mul_div_le (N + 1) 2
    have : ((2 * ((N + 1) / 2) : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hkey := key_alg (Lk := L ^ k) hℓpos hNpos (by positivity) h2 h1 hcard
    (by linarith) hsm1 (by rw [hℓ]; exact hsm2)
  rw [hexp]
  calc _ ≤ (2 * C + 1) * a * (N * (L ^ k) ^ 2 / ℓ ^ 2) := hkey
    _ ≤ (2 * C + 1) * a * (3 * N * L ^ (2 * k - 2)) :=
        mul_le_mul_of_nonneg_left (X_le hk hN2) (by positivity)
    _ = 3 * (2 * C + 1) * a * N * L ^ (2 * k - 2) := by ring

/-- **Gallagher 1975, Theorem 1**, display (3), CONDITIONAL ON `Lemma13` alone. -/
theorem theorem1_of_lemma13 (h13 : Lemma13) : Theorem1 := theorem1_of h13 lemma14

/-- **Gallagher 1975, Theorem 2**, display (4), `g = 2`, CONDITIONAL ON `Lemma13` alone:
for `k ≥ 2` and even `N ≥ N_k`, `r''_k(N) = (2 N L^k / log² N)(1 + O(log² k / k))`. -/
theorem theorem2_of_lemma13 (h13 : Lemma13) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(rpp k N : ℝ) - 2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  theorem2_of_theorem1 (theorem1_of_lemma13 h13)

/-- Vacuity check of `Lemma13`'s left side: `Σ_{n ≤ 8} r'_1(n)² > 0`. -/
theorem lemma13_lhs_pos : 0 < ∑ n ∈ range 9, (rk 1 8 n : ℝ) ^ 2 := by
  have h : 0 < rk 1 8 5 := (rk_pos_iff (by norm_num)).mpr
    ⟨3, Nat.prime_three, fun _ => 1, fun _ => le_rfl, by simp⟩
  have h5 : (0 : ℝ) < (rk 1 8 5 : ℝ) ^ 2 := by positivity
  calc (0 : ℝ) < (rk 1 8 5 : ℝ) ^ 2 := h5
    _ ≤ ∑ n ∈ range 9, (rk 1 8 n : ℝ) ^ 2 :=
        single_le_sum (f := fun n => (rk 1 8 n : ℝ) ^ 2) (fun _ _ => by positivity)
          (by simp)

end LeanLab.Linnik.U7204

