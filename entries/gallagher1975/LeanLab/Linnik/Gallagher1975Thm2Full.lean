module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975Thm2

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, Theorem 2,
display (4), p.125, assembled by the convolution of p.140, for g = 2, from the page images of
papers/P0094.pdf, PDF pages 2, 15, 16, 17. Unit U-6833, CLOUD 20261021T0217Z-cloud56.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Theorem 2: for `k ≥ 2` and even `N ≥ N_k`, `r''_k(N) = (2 N L^k / log² N)(1 + O(log² k / k))`.
The proof on p.140 writes `k = i + j`, `i = j` or `j + 1`, and `r''_k(N) = Σ_{m+n=N} r'_i(m) r'_j(n)`.

* `theorem2_conv`: PROVED, CONDITIONAL ON `Theorem1`, display (3), and `Lemma14`, display (7),
  as named hypotheses: with `i = k - ⌊k/2⌋`, `j = ⌊k/2⌋`, the convolution
  `Σ_{m ≤ N} r'_i(m) r'_j(N-m)` is `(2 N L^k / log² N)(1 + O(log² k / k))` for even `N ≥ N_k`,
  with an absolute `O`.
* Lemma 13 is NOT needed for g = 2: when `N` is even, a violation of (a) means `m` even, hence
  `n = N - m` even too, and both factors are bounded by `even_sq_sum_le`, giving at most `L^k`.
  Lemma 13 is analytic, p.138, from Lemma 5 and Theorem 3, and is not formalized.
* Not formalized: the counting identity `r''_k(N) = Σ_{m+n=N} r'_i(m) r'_j(n)`, splitting the
  `k`-tuple of exponents into `i` and `j`; the theorem is stated for the convolution.
-/

@[expose] public section

open Finset Real Filter
open scoped Topology

noncomputable section
namespace LeanLab.Linnik.Gallagher1975Thm2

open LeanLab.Linnik.Gallagher1975

/-- **Gallagher 1975, Lemma 14**, display (7), p.139, cited: `Σ_{n ≤ N} r'_k(n) ~ N L^k / log N`. -/
def Lemma14 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    |∑ n ∈ range (N + 1), (rk k N n : ℝ) - N * (Nat.log 2 N : ℝ) ^ k / Real.log N| ≤
      ε * (N * (Nat.log 2 N : ℝ) ^ k / Real.log N)

/-- The convolution `Σ_{m ≤ N} r'_i(m) r'_j(N - m)` of p.140. -/
def conv (i j N : ℕ) : ℝ := ∑ m ∈ range (N + 1), (rk i N m : ℝ) * rk j N (N - m)

theorem filter_not_even_eq {N : ℕ} (hN : Even N) :
    {m ∈ range (N + 1) | ¬ Even m} = oddPairs N := by
  ext m
  simp only [oddPairs, mem_filter, mem_range, Nat.not_even_iff_odd, Nat.odd_iff]
  rw [Nat.even_iff] at hN
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩

/-- The even `m` part is at most `L^k`, `k = i + j`, when `N` is even. -/
theorem even_part_le (i j N : ℕ) (hN : Even N) :
    ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m) ≤
      (Nat.log 2 N : ℝ) ^ (i + j) := by
  set S := ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m)
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  have hCS := sum_mul_sq_le_sq_mul_sq ({m ∈ range (N + 1) | Even m})
    (fun m => (rk i N m : ℝ)) (fun m => (rk j N (N - m) : ℝ))
  have hY : ∑ m ∈ range (N + 1) with Even m, (rk j N (N - m) : ℝ) ^ 2 ≤
      (Nat.log 2 N : ℝ) ^ (2 * j) := by
    refine le_trans ?_ (even_sq_sum_le j N)
    rw [← sum_image (s := {m ∈ range (N + 1) | Even m}) (g := fun m => N - m)
      (f := fun n => (rk j N n : ℝ) ^ 2)]
    · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro x hx
      simp only [mem_image, mem_filter, mem_range, Nat.even_iff] at hx ⊢
      rw [Nat.even_iff] at hN
      omega
    · intro x hx y hy hxy
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
      simp only at hxy
      omega
  have hY0 : 0 ≤ ∑ m ∈ range (N + 1) with Even m, (rk j N (N - m) : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  have hsq : S ^ 2 ≤ ((Nat.log 2 N : ℝ) ^ (i + j)) ^ 2 := by
    calc S ^ 2 ≤ _ := hCS
      _ ≤ (Nat.log 2 N : ℝ) ^ (2 * i) * (Nat.log 2 N : ℝ) ^ (2 * j) :=
          mul_le_mul (even_sq_sum_le i N) hY hY0 (by positivity)
      _ = ((Nat.log 2 N : ℝ) ^ (i + j)) ^ 2 := by rw [← pow_add, ← pow_mul]; ring_nf
  exact (pow_le_pow_iff_left₀ hS0 (by positivity) (by norm_num)).1 hsq

/-- Reflection `m ↦ N - m` permutes `oddPairs N`. -/
theorem sum_oddPairs_reflect (f : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ oddPairs N, f (N - m) = ∑ m ∈ oddPairs N, f m := by
  apply sum_nbij' (fun m => N - m) (fun m => N - m)
  · intro m hm
    simp only [oddPairs, mem_filter, mem_range, mem_coe] at hm ⊢
    refine ⟨by omega, hm.2.2, ?_⟩
    rw [show N - (N - m) = m by omega]; exact hm.2.1
  · intro m hm
    simp only [oddPairs, mem_filter, mem_range, mem_coe] at hm ⊢
    refine ⟨by omega, hm.2.2, ?_⟩
    rw [show N - (N - m) = m by omega]; exact hm.2.1
  · intro m hm
    simp only [oddPairs, mem_filter, mem_range, mem_coe] at hm
    omega
  · intro m hm
    simp only [oddPairs, mem_filter, mem_range, mem_coe] at hm
    omega
  · intro m _; rfl

/-- The middle sums of (10): `|Σ'' s_i(m)| ≤ |Σ_{n ≤ N} r'_i(n) - N L^i / log N| + L^i`. -/
theorem middle_le (i N : ℕ) (hN : Even N) :
    |∑ m ∈ oddPairs N, s i N m| ≤
      |∑ n ∈ range (N + 1), (rk i N n : ℝ) - N * (Nat.log 2 N : ℝ) ^ i / Real.log N| +
        (Nat.log 2 N : ℝ) ^ i := by
  have hsplit := sum_filter_add_sum_filter_not (range (N + 1)) (fun m => Even m)
    (fun m => (rk i N m : ℝ))
  rw [filter_not_even_eq hN] at hsplit
  have hev : ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) ≤ (Nat.log 2 N : ℝ) ^ i := by
    exact_mod_cast even_sum_le i N
  have hev0 : 0 ≤ ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) :=
    sum_nonneg fun _ _ => by positivity
  have hs : ∑ m ∈ oddPairs N, s i N m = ∑ m ∈ oddPairs N, (rk i N m : ℝ) - M i N * (N / 2 : ℕ) := by
    simp only [s, sum_sub_distrib, sum_const, card_oddPairs hN, nsmul_eq_mul]; ring
  have hN2 : ((N / 2 : ℕ) : ℝ) = N / 2 := by
    obtain ⟨r, rfl⟩ := hN
    rw [show (r + r) / 2 = r by omega]; push_cast; ring
  have hM : M i N * ((N / 2 : ℕ) : ℝ) = N * (Nat.log 2 N : ℝ) ^ i / Real.log N := by
    rw [hN2, M]; ring
  rw [hs, hM]
  have hR := le_abs_self (∑ n ∈ range (N + 1), (rk i N n : ℝ) -
      N * (Nat.log 2 N : ℝ) ^ i / Real.log N)
  have hR' := neg_abs_le (∑ n ∈ range (N + 1), (rk i N n : ℝ) -
      N * (Nat.log 2 N : ℝ) ^ i / Real.log N)
  rw [abs_le]
  constructor <;> linarith

/-- `log (2k)² ≤ 4 log² k` for `k ≥ 2`. -/
theorem log_two_mul_sq_le {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * k) ^ 2 ≤ 4 * Real.log k ^ 2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : Real.log (2 * k) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) (by linarith)
  have h2 : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk'
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [h1]; nlinarith

/-- `log² N ≤ c N` for large `N`, any `c > 0`. -/
theorem eventually_log_sq_le {c : ℝ} (hc : 0 < c) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Real.log N ^ 2 ≤ c * N := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)
  have h2 := h.comp tendsto_natCast_atTop_atTop
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h2.eventually (gt_mem_nhds hc))
  refine ⟨max N0 1, fun N hN => ?_⟩
  have := hN0 N (le_of_max_le_left hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  simp only [Function.comp, one_mul, add_zero] at this
  rw [div_lt_iff₀ hNpos] at this
  linarith

/-- **Gallagher 1975, Theorem 2, display (4), g = 2, for the convolution of p.140**, PROVED,
CONDITIONAL ON `Theorem1` and `Lemma14`: there is an absolute `K` such that for `k ≥ 2` and
even `N ≥ N_k`, with `i = k - ⌊k/2⌋`, `j = ⌊k/2⌋`,
`|Σ_{m ≤ N} r'_i(m) r'_j(N-m) - 2 N L^k / log² N| ≤ K (log² k / k) · 2 N L^k / log² N`. -/
theorem theorem2_conv (h1 : Theorem1) (h14 : Lemma14) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |conv (k - k / 2) (k / 2) N - 2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) := by
  obtain ⟨C, hC⟩ := last_term_sq h1
  refine ⟨5 + 24 * |C|, fun k hk => ?_⟩
  set i := k - k / 2 with hi
  set j := k / 2 with hj
  have hij : i + j = k := by omega
  have hj1 : 1 ≤ j := by omega
  have hi1 : 1 ≤ i := by omega
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set δ := Real.log k ^ 2 / k with hδ
  have hlogk : 0 < Real.log k := Real.log_pos (by linarith)
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N1, hN1⟩ := hC i j hj1 (by omega)
  obtain ⟨N2, hN2⟩ := h14 i hi1 δ hδ0
  obtain ⟨N3, hN3⟩ := h14 j hj1 δ hδ0
  obtain ⟨N4, hN4⟩ := eventually_log_sq_le (c := 2 * δ) (by positivity)
  refine ⟨max (max N1 N2) (max (max N3 N4) 8), fun N hN hev => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN8
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1n : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hL1' : (1 : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hL1n
  set L : ℝ := (Nat.log 2 N : ℝ) with hL
  have hL1 : (1 : ℝ) ≤ L := hL1' 
  set Λ := Real.log N with hΛ
  have hΛ2 : 2 ≤ Λ := by
    have h8 : Real.log 8 ≤ Λ := Real.log_le_log (by norm_num) hNr
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hΛL : Λ ≤ 2 * L := log_le_two_mul_log2 (by omega)
  have hΛ0 : Λ ≠ 0 := by linarith
  set Lk := L ^ k with hLk
  have hLk1 : 1 ≤ Lk := one_le_pow₀ hL1
  set main := 2 * N * Lk / Λ ^ 2 with hmain
  have hmain0 : 0 < main := by positivity
  -- decomposition
  have hsplit := sum_filter_add_sum_filter_not (range (N + 1)) (fun m => Even m)
    (fun m => (rk i N m : ℝ) * rk j N (N - m))
  rw [filter_not_even_eq hev, conv_decomp] at hsplit
  have hconv : conv i j N = ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m) +
      (M i N * M j N * #(oddPairs N) + M i N * ∑ m ∈ oddPairs N, s j N (N - m) +
        M j N * ∑ m ∈ oddPairs N, s i N m + ∑ m ∈ oddPairs N, s i N m * s j N (N - m)) := by
    rw [conv, ← hsplit]
  -- pieces
  have hE := even_part_le i j N hev
  rw [hij] at hE
  have hE0 : 0 ≤ ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m) :=
    sum_nonneg fun _ _ => by positivity
  have hN2r : ((N / 2 : ℕ) : ℝ) = N / 2 := by
    obtain ⟨r, hr⟩ := hev
    rw [hr, show (r + r) / 2 = r by omega]; push_cast; ring
  have hMi' : M i N = 2 * L ^ i / Λ := rfl
  have hMj' : M j N = 2 * L ^ j / Λ := rfl
  have hMM : M i N * M j N * #(oddPairs N) = main := by
    rw [card_oddPairs hev, hN2r, hMi', hMj', hmain, hLk, ← hij, pow_add]
    field_simp
    try ring
  have hmid_i := middle_le i N hev
  have hmid_j := middle_le j N hev
  rw [← sum_oddPairs_reflect (fun m => s j N m) N] at hmid_j
  have hA := hN2 N (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hB := hN3 N (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)))
  have hlast := hN1 N (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
  have hlog4 := hN4 N (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)))
  rw [← hΛ] at hlog4
  -- L^k ≤ δ main
  have hLkδ : Lk ≤ δ * main := by
    rw [hmain, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  -- middle terms
  have hMi : M i N = 2 * L ^ i / Λ := rfl
  have hMj : M j N = 2 * L ^ j / Λ := rfl
  have hLij : L ^ i * L ^ j = Lk := by rw [← pow_add, hij]
  have hLkΛ : 2 * Lk / Λ ≤ Lk := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hΛ2 (by linarith : (0 : ℝ) ≤ Lk)
    linarith
  have hmid1 : |M i N * ∑ m ∈ oddPairs N, s j N (N - m)| ≤ δ * main + Lk := by
    rw [abs_mul, abs_of_nonneg (by rw [hMi]; positivity)]
    calc M i N * |∑ m ∈ oddPairs N, s j N (N - m)|
        ≤ M i N * (δ * (N * L ^ j / Λ) + L ^ j) :=
          mul_le_mul_of_nonneg_left (hmid_j.trans (by linarith)) (by rw [hMi]; positivity)
      _ = δ * main + 2 * Lk / Λ := by
          rw [hMi, hmain, ← hLij]; field_simp; try ring
      _ ≤ δ * main + Lk := by linarith [hLkΛ]
  have hmid2 : |M j N * ∑ m ∈ oddPairs N, s i N m| ≤ δ * main + Lk := by
    rw [abs_mul, abs_of_nonneg (by rw [hMj]; positivity)]
    calc M j N * |∑ m ∈ oddPairs N, s i N m|
        ≤ M j N * (δ * (N * L ^ i / Λ) + L ^ i) :=
          mul_le_mul_of_nonneg_left (hmid_i.trans (by linarith)) (by rw [hMj]; positivity)
      _ = δ * main + 2 * Lk / Λ := by
          rw [hMj, hmain, ← hLij]; field_simp; try ring
      _ ≤ δ * main + Lk := by linarith [hLkΛ]
  -- last term
  have hlast' : |∑ m ∈ oddPairs N, s i N m * s j N (N - m)| ≤ 24 * |C| * δ * main := by
    rw [show i + j = k from hij] at hlast
    set X := 3 * C * (Real.log (2 * ((k : ℕ) : ℝ)) ^ 2 / ((k : ℕ) : ℝ)) * N * L ^ (k - 2)
    have h1' : |∑ m ∈ oddPairs N, s i N m * s j N (N - m)| ≤ |X| := sq_le_sq.1 hlast
    have hb : Real.log (2 * (k : ℝ)) ^ 2 / k ≤ 4 * δ := by
      rw [hδ, div_le_iff₀ (by linarith)]
      have := log_two_mul_sq_le hk
      rw [mul_div_assoc', div_mul_cancel₀ _ (by linarith)]; linarith
    have hb0 : 0 ≤ Real.log (2 * (k : ℝ)) ^ 2 / k := by positivity
    have hpow : L ^ (k - 2) * L ^ 2 = Lk := by rw [← pow_add]; congr 1; omega
    have hNL : N * L ^ (k - 2) ≤ 2 * main := by
      rw [hmain, ← hpow]
      rw [show 2 * (2 * N * (L ^ (k - 2) * L ^ 2) / Λ ^ 2) =
        N * L ^ (k - 2) * (4 * L ^ 2 / Λ ^ 2) by ring]
      have : 1 ≤ 4 * L ^ 2 / Λ ^ 2 := by
        rw [le_div_iff₀ (by positivity), one_mul]
        have := pow_le_pow_left₀ (by linarith : 0 ≤ Λ) hΛL 2
        have e2 : (2 * L) ^ 2 = 4 * L ^ 2 := by ring
        linarith
      have h0 : 0 ≤ N * L ^ (k - 2) := by positivity
      exact le_mul_of_one_le_right h0 this
    set b' := Real.log (2 * ((k : ℕ) : ℝ)) ^ 2 / ((k : ℕ) : ℝ)
    have hX' : X = C * (3 * b' * (N * L ^ (k - 2))) := by simp only [X, b']; ring
    have hpos : 0 ≤ 3 * b' * (N * L ^ (k - 2)) := by positivity
    have hX : |X| = |C| * (3 * b' * (N * L ^ (k - 2))) := by
      rw [hX', abs_mul, abs_of_nonneg hpos]
    have h3 : 3 * b' * (N * L ^ (k - 2)) ≤ 3 * (4 * δ) * (2 * main) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) hNL (by positivity) (by positivity)
    have h4 : |C| * (3 * b' * (N * L ^ (k - 2))) ≤ |C| * (3 * (4 * δ) * (2 * main)) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
    have h5 : |C| * (3 * (4 * δ) * (2 * main)) = 24 * |C| * δ * main := by ring
    exact (h1'.trans (le_of_eq hX)).trans (h4.trans (le_of_eq h5))
  -- assemble
  rw [hconv, hMM]
  have hδm : 0 ≤ δ * main := by positivity
  have : |∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m) +
      (main + M i N * ∑ m ∈ oddPairs N, s j N (N - m) + M j N * ∑ m ∈ oddPairs N, s i N m +
        ∑ m ∈ oddPairs N, s i N m * s j N (N - m)) - main| ≤
      Lk + (δ * main + Lk) + (δ * main + Lk) + 24 * |C| * δ * main := by
    have e : ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m) +
        (main + M i N * ∑ m ∈ oddPairs N, s j N (N - m) + M j N * ∑ m ∈ oddPairs N, s i N m +
          ∑ m ∈ oddPairs N, s i N m * s j N (N - m)) - main =
        ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m) +
        M i N * ∑ m ∈ oddPairs N, s j N (N - m) + M j N * ∑ m ∈ oddPairs N, s i N m +
          ∑ m ∈ oddPairs N, s i N m * s j N (N - m) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ hlast'
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ hmid2
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ hmid1
    rw [abs_of_nonneg hE0]; exact hE
  refine this.trans ?_
  have hC0 := abs_nonneg C
  rw [show (5 + 24 * |C|) * δ * main = 5 * (δ * main) + 24 * |C| * δ * main by ring]
  linarith

/-- Vacuity: the main term is positive at `k = 2`, `N = 8`, `L = 3`. -/
theorem main_pos_example : 0 < 2 * (8 : ℕ) * ((Nat.log 2 8 : ℕ) : ℝ) ^ 2 / Real.log (8 : ℕ) ^ 2 := by
  have h : Nat.log 2 8 = 3 := by decide
  rw [h]
  have : 0 < Real.log ((8 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  positivity

end LeanLab.Linnik.Gallagher1975Thm2

