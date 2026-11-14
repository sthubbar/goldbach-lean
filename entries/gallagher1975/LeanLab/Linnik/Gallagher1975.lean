module

public import Mathlib
public import LeanLab.LPZ2007.Elementary

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, read from the
GDZ Goettingen scan, papers/P0094.pdf. Unit U-6810, CLOUD 20261021T0117Z-cloud55.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN. This is the one-prime, de Polignac side of the Linnik-Goldbach line.

* `rk k N n`: Gallagher's `r'_k(n)`, p.125, the representations `n = p + 2^{ν1} + ... + 2^{νk}`
  with `1 ≤ νi ≤ L = [log₂ N]`, the range of `G(α)` on p.132.
* `rk_pos_iff`: for `n ≤ N`, `r'_k(n) > 0` exactly when `n` is a prime plus `k` powers of 2.
* `Theorem1`: display (3), p.125, cited as a `Prop`, never proved here.
* `exceptions_le`: CONDITIONAL ON `Theorem1`, the odd `n ≤ N` that are not a prime plus `k`
  powers of 2 number at most `C (log² 2k / k) N`, the Chebyshev step from (3).
* `density_tends_to_one`: CONDITIONAL ON `Theorem1`, for every `ε > 0` some `k` leaves at most
  `ε N` odd exceptions up to `N`, for all large `N`: the density statement of p.125.
* `fL_le`, `fL_ge`: Lemma 14's counting bounds, p.139,
  `[log₂ (x/k)]^k ≤ f(x) ≤ [log₂ x]^k`, PROVED, unconditional.
-/

@[expose] public section

open Finset Real Filter
open scoped Topology

noncomputable section
namespace LeanLab.Linnik.Gallagher1975

open LeanLab.LPZ2007 (tuples pow2sum card_tuples pow_le_pow2sum)

/-- `n` is a prime plus exactly `k` powers of 2, exponents at least 1, Gallagher's (2), p.125. -/
def PolignacExact (k n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ ν : Fin k → ℕ, (∀ i, 1 ≤ ν i) ∧ n = p + ∑ i, 2 ^ ν i

/-- Gallagher's `r'_k(n)`, p.125, with `L = [log₂ N]`: pairs `(p, ν)`, `p` prime,
`ν ∈ [1, L]^k`, `n = p + 2^{ν1} + ... + 2^{νk}`. A prime below `n` is at most `n`. -/
def rk (k N n : ℕ) : ℕ :=
  #{x ∈ range (n + 1) ×ˢ tuples k (Nat.log 2 N) | x.1.Prime ∧ n = x.1 + pow2sum x.2}

/-- For `n ≤ N`, `r'_k(n) > 0` exactly when `n` is a prime plus `k` powers of 2. -/
theorem rk_pos_iff {k N n : ℕ} (hn : n ≤ N) : 0 < rk k N n ↔ PolignacExact k n := by
  unfold rk
  rw [card_pos]
  constructor
  · rintro ⟨⟨p, ν⟩, hx⟩
    simp only [mem_filter, mem_product, tuples, Fintype.mem_piFinset, mem_Icc] at hx
    exact ⟨p, hx.2.1, ν, fun i => (hx.1.2 i).1, hx.2.2⟩
  · rintro ⟨p, hp, ν, hν, hn'⟩
    refine ⟨⟨p, ν⟩, ?_⟩
    simp only [mem_filter, mem_product, mem_range, tuples, Fintype.mem_piFinset, mem_Icc]
    refine ⟨⟨by omega, fun i => ⟨hν i, Nat.le_log_of_pow_le (by norm_num) ?_⟩⟩, hp, hn'⟩
    have h1 : 2 ^ ν i ≤ pow2sum ν := pow_le_pow2sum ν i
    unfold pow2sum at h1
    omega

open Classical in
/-- The odd `n ≤ N` that are not a prime plus exactly `k` powers of 2. -/
def exceptions (k N : ℕ) : Finset ℕ :=
  {n ∈ range (N + 1) | Odd n ∧ ¬ PolignacExact k n}

/-- **Gallagher 1975, Theorem 1**, display (3), p.125, `g = 2`, cited: for `k ≥ 1` and
`N ≥ N_k`, `Σ_{n ≤ N, n odd} (r'_k(n) - 2L^k/log N)² ≪ (log² 2k / k) N L^{2k-2}`, with an
absolute implied constant, p.126 Notation. The sum is over odd `n`, as the definition of
`r'_k` and the dashed sums of p.139 fix. -/
def Theorem1 : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ∑ n ∈ range (N + 1) with Odd n,
        ((rk k N n : ℝ) - 2 * (Nat.log 2 N : ℝ) ^ k / Real.log N) ^ 2 ≤
      C * (Real.log (2 * k) ^ 2 / k) * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)

/-- `log N ≤ 2 [log₂ N]` for `N ≥ 2`. -/
theorem log_le_two_mul_log2 {N : ℕ} (hN : 2 ≤ N) : Real.log N ≤ 2 * (Nat.log 2 N : ℝ) := by
  have hL : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : Real.log N < (Nat.log 2 N + 1 : ℝ) * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    apply Real.log_lt_log hNpos
    rw [show ((Nat.log 2 N : ℝ) + 1) = ((Nat.log 2 N + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    exact_mod_cast hlt
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h3 : (1 : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hL
  have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The algebra of the Chebyshev step: from `x (2 l^k / g)² ≤ A l^{2k-2}`, `x ≥ 0`, `l ≥ 1`,
`0 < g ≤ 2 l`, `k ≥ 1`, get `x ≤ A`. -/
theorem cheb_algebra {x A l g : ℝ} {k : ℕ} (hk : 1 ≤ k) (hx : 0 ≤ x) (hl : 1 ≤ l)
    (hg : 0 < g) (hgl : g ≤ 2 * l)
    (h : x * (2 * l ^ k / g) ^ 2 ≤ A * l ^ (2 * k - 2)) : x ≤ A := by
  set P := l ^ (2 * k - 2) with hP
  have hPpos : 0 < P := by positivity
  have hlk : (l ^ k) ^ 2 = P * l ^ 2 := by
    rw [hP, ← pow_mul, ← pow_add]; congr 1; omega
  have h' : x * (4 * (P * l ^ 2)) ≤ A * P * g ^ 2 := by
    have hg2 : 0 < g ^ 2 := by positivity
    rw [div_pow, mul_pow, hlk] at h
    have h2 : x * (2 ^ 2 * (P * l ^ 2)) / g ^ 2 ≤ A * P := by
      rwa [mul_div_assoc]
    rw [div_le_iff₀ hg2] at h2
    nlinarith
  have hA : 0 ≤ A := by
    by_contra hA
    push Not at hA
    have : 0 ≤ x * (4 * (P * l ^ 2)) := by positivity
    have : A * P * g ^ 2 < 0 := by
      have : 0 < P * g ^ 2 := by positivity
      nlinarith
    linarith
  have hg2 : g ^ 2 ≤ 4 * l ^ 2 := by nlinarith
  have : A * P * g ^ 2 ≤ A * P * (4 * l ^ 2) :=
    mul_le_mul_of_nonneg_left hg2 (by positivity)
  have hpos : 0 < 4 * (P * l ^ 2) := by positivity
  nlinarith

/-- CONDITIONAL ON `Theorem1`: the odd `n ≤ N` that are not a prime plus exactly `k` powers
of 2 are at most `C (log² 2k / k) N`, for `k ≥ 1` and `N ≥ N_k`. -/
theorem exceptions_le (h1 : Theorem1) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      (#(exceptions k N) : ℝ) ≤ C * (Real.log (2 * k) ^ 2 / k) * N := by
  obtain ⟨C, hC⟩ := h1
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨Nk, hNk⟩ := hC k hk
  refine ⟨max Nk 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hS := hNk N (le_of_max_le_left hN)
  set M : ℝ := 2 * (Nat.log 2 N : ℝ) ^ k / Real.log N with hM
  have hsub : exceptions k N ⊆ {n ∈ range (N + 1) | Odd n} := by
    intro n hn
    simp only [exceptions, mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hterm : ∀ n ∈ exceptions k N, ((rk k N n : ℝ) - M) ^ 2 = M ^ 2 := by
    intro n hn
    simp only [exceptions, mem_filter, mem_range] at hn
    have h0 : rk k N n = 0 := by
      by_contra hne
      exact hn.2.2 ((rk_pos_iff (by omega)).1 (Nat.pos_of_ne_zero hne))
    rw [h0]; ring
  have hle : (#(exceptions k N) : ℝ) * M ^ 2 ≤
      C * (Real.log (2 * k) ^ 2 / k) * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by
    calc (#(exceptions k N) : ℝ) * M ^ 2 = ∑ n ∈ exceptions k N, ((rk k N n : ℝ) - M) ^ 2 := by
          rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ range (N + 1) with Odd n, ((rk k N n : ℝ) - M) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      _ ≤ _ := hS
  have hL : (1 : ℝ) ≤ Nat.log 2 N := by
    exact_mod_cast (Nat.le_log_of_pow_le (by norm_num) (by simpa using hN2) : 1 ≤ Nat.log 2 N)
  have hg : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  exact cheb_algebra hk (by positivity) hL hg (log_le_two_mul_log2 hN2) hle

/-- `log² (2k) / k → 0` along the naturals. -/
theorem tendsto_log_sq_div : Tendsto (fun k : ℕ => Real.log (2 * k) ^ 2 / k) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) 0 2 (by norm_num)
  have h2 : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  refine (h.comp h2).congr fun k => ?_
  simp only [Function.comp]
  congr 1; ring

/-- CONDITIONAL ON `Theorem1`: **the density of the odd `p + 2^{ν1} + ... + 2^{νk}` tends to 1
as `k → ∞`**, p.125: for every `ε > 0` there is `k ≥ 1` such that for all large `N` at most
`ε N` odd `n ≤ N` fail to be a prime plus exactly `k` powers of 2. -/
theorem density_tends_to_one (h1 : Theorem1) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (#(exceptions k N) : ℝ) ≤ ε * N := by
  obtain ⟨C, hC⟩ := exceptions_le h1
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have ht : Tendsto (fun k : ℕ => C' * (Real.log (2 * k) ^ 2 / k)) atTop (𝓝 0) := by
    simpa using tendsto_log_sq_div.const_mul C'
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hε))
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  obtain ⟨Nk, hNk⟩ := hC (max K 1) (le_max_right _ _)
  refine ⟨Nk, fun N hN => ?_⟩
  have ha : 0 ≤ Real.log (2 * ((max K 1 : ℕ) : ℝ)) ^ 2 / ((max K 1 : ℕ) : ℝ) := by positivity
  have hlt := hK (max K 1) (le_max_left _ _)
  have hNn : (0 : ℝ) ≤ N := by positivity
  calc (#(exceptions (max K 1) N) : ℝ)
      ≤ C * (Real.log (2 * ((max K 1 : ℕ) : ℝ)) ^ 2 / ((max K 1 : ℕ) : ℝ)) * N := hNk N hN
    _ ≤ C' * (Real.log (2 * ((max K 1 : ℕ) : ℝ)) ^ 2 / ((max K 1 : ℕ) : ℝ)) * N := by
        apply mul_le_mul_of_nonneg_right _ hNn
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) ha
    _ ≤ ε * N := mul_le_mul_of_nonneg_right hlt.le hNn

/-! ### Lemma 14's counting function, p.139 -/

/-- Gallagher's `f(x)`, p.139: the `k`-tuples `ν` with `1 ≤ νi ≤ L` and
`2^{ν1} + ... + 2^{νk} ≤ x`. -/
def fL (k L x : ℕ) : ℕ := #{ν ∈ tuples k L | pow2sum ν ≤ x}

/-- Lemma 14, upper bound, p.139: `f(x) ≤ [log₂ x]^k`, for every cap `L`. -/
theorem fL_le (k L x : ℕ) : fL k L x ≤ Nat.log 2 x ^ k := by
  unfold fL
  rw [← card_tuples k (Nat.log 2 x)]
  apply card_le_card
  intro ν hν
  simp only [mem_filter, tuples, Fintype.mem_piFinset, mem_Icc] at hν ⊢
  intro i
  refine ⟨(hν.1 i).1, Nat.le_log_of_pow_le (by norm_num) ?_⟩
  exact (pow_le_pow2sum ν i).trans hν.2

/-- Lemma 14, lower bound, p.139: `[log₂ (x/k)]^k ≤ f(x)`, when `[log₂ (x/k)] ≤ L`; for
`x ≤ N` and `L = [log₂ N]` this always holds. -/
theorem fL_ge (k L x : ℕ) (hL : Nat.log 2 (x / k) ≤ L) : Nat.log 2 (x / k) ^ k ≤ fL k L x := by
  unfold fL
  rw [← card_tuples k (Nat.log 2 (x / k))]
  apply card_le_card
  intro ν hν
  simp only [mem_filter, tuples, Fintype.mem_piFinset, mem_Icc] at hν ⊢
  refine ⟨fun i => ⟨(hν i).1, (hν i).2.trans hL⟩, ?_⟩
  have hb : ∀ i, 2 ^ ν i ≤ x / k := by
    intro i
    have h1 : 1 ≤ Nat.log 2 (x / k) := (hν i).1.trans (hν i).2
    have hne : x / k ≠ 0 := by
      intro h0; rw [h0] at h1; simp at h1
    exact (Nat.pow_le_pow_right (by norm_num) (hν i).2).trans (Nat.pow_log_le_self 2 hne)
  calc pow2sum ν = ∑ i, 2 ^ ν i := rfl
    _ ≤ ∑ _i : Fin k, x / k := sum_le_sum fun i _ => hb i
    _ = k * (x / k) := by simp
    _ ≤ x := Nat.mul_div_le x k

/-- With `x ≤ N` and `L = [log₂ N]`, Lemma 14's hypothesis holds. -/
theorem fL_ge_of_le (k N x : ℕ) (hx : x ≤ N) :
    Nat.log 2 (x / k) ^ k ≤ fL k (Nat.log 2 N) x :=
  fL_ge k _ x (Nat.log_mono_right ((Nat.div_le_self x k).trans hx))

/-! ### Vacuity tests -/

/-- `7 = 3 + 2 + 2` is a prime plus two powers of 2, so `PolignacExact` is not empty. -/
theorem polignac_7 : PolignacExact 2 7 :=
  ⟨3, Nat.prime_three, fun _ => 1, fun _ => le_rfl, by simp⟩

/-- `f(4) = 1` for `k = 2`, `L = 2`: only `2 + 2`. Lemma 14's bounds read `1 ≤ 1 ≤ 4`. -/
theorem fL_example : fL 2 2 4 = 1 := by decide

end LeanLab.Linnik.Gallagher1975
