module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, the proof of
Theorem 2 on p.140, displays (9) and (10), for g = 2, read from the page image of
papers/P0094.pdf, PDF page 17. Unit U-6824, CLOUD 20261021T0217Z-cloud56.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Binary Goldbach is OPEN.

For g = 2: D = g(g-1) = 2, φ(D) = 1, and conditions (a), (b) read m odd, n odd. The paper
puts `r'_i(m) = 2 L^i / log N + s_i(m)` for odd m and splits the double dashed sum (9) into the
four terms of (10).

* `conv_decomp`: PROVED, the four-term identity (10) for g = 2, pure algebra.
* `last_term_sq`: PROVED, CONDITIONAL ON `Theorem1`: the last sum of (10),
  `Σ'' s_i(m) s_j(n)`, is at most `3 |C| (log² 2k / k) N L^{k-2}` in absolute value, for
  `k = i + j`, `i = j` or `i = j + 1`, `j ≥ 1`, `N ≥ N_i, N_j`. The paper writes `log² k / k`;
  for `k ≥ 2` these differ by at most a factor 4, so this is the paper's bound.
* `ai_le`: the elementary step `log² 2i / i ≤ 3 log² 2k / k` when `k ≤ 3i`, `i ≤ k`.

* `even_sq_sum_le`: PROVED, `Σ_{m even} r'_i(m)² ≤ L^{2i}`, the remark that such
  representations have `p | g(g-1)`, so `p = 2`; `even_terms_sq`: PROVED, the m even terms of
  `r''_k(N)` are at most `L^{2i} B` in square when `Σ r'_j(n)² ≤ B`, the slot for Lemma 13.
* `card_oddPairs`: PROVED, the first sum of (10) is exactly `N/2` for even `N`, `N D'/D`.

Not formalized: Lemma 13 itself; the middle terms of (10), by Lemma 14 and the `o(N)` errors;
hence Theorem 2 itself stays cited.
-/

@[expose] public section

open Finset Real

noncomputable section
namespace LeanLab.Linnik.Gallagher1975Thm2

open LeanLab.Linnik.Gallagher1975

/-- The main term `2 L^k / log N`, `L = [log₂ N]`, of Theorem 1 and of p.140, `g = 2`. -/
def M (k N : ℕ) : ℝ := 2 * (Nat.log 2 N : ℝ) ^ k / Real.log N

/-- `s_k(m) = r'_k(m) - 2 L^k / log N`, p.140. -/
def s (k N m : ℕ) : ℝ := (rk k N m : ℝ) - M k N

/-- The representations `N = m + n` with `m`, `n` odd: conditions (a), (b) for `g = 2`. -/
def oddPairs (N : ℕ) : Finset ℕ := {m ∈ range (N + 1) | Odd m ∧ Odd (N - m)}

/-- **Display (10), g = 2**, PROVED: the double dashed sum of (9) splits into four terms. -/
theorem conv_decomp (i j N : ℕ) :
    ∑ m ∈ oddPairs N, (rk i N m : ℝ) * rk j N (N - m) =
      M i N * M j N * #(oddPairs N) +
        M i N * ∑ m ∈ oddPairs N, s j N (N - m) + M j N * ∑ m ∈ oddPairs N, s i N m +
        ∑ m ∈ oddPairs N, s i N m * s j N (N - m) := by
  have h : ∀ m, (rk i N m : ℝ) * rk j N (N - m) =
      M i N * M j N + M i N * s j N (N - m) + M j N * s i N m + s i N m * s j N (N - m) := by
    intro m; simp only [s]; ring
  rw [sum_congr rfl (fun m _ => h m), sum_add_distrib, sum_add_distrib, sum_add_distrib,
    sum_const, nsmul_eq_mul, mul_sum, mul_sum]
  ring

/-- The reflection `m ↦ N - m` sends `oddPairs N` into the odd `n ≤ N`. -/
theorem sum_reflect_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    ∑ m ∈ oddPairs N, f (N - m) ≤ ∑ n ∈ range (N + 1) with Odd n, f n := by
  rw [← sum_image (s := oddPairs N) (g := fun m => N - m) (f := f)]
  · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => hf _)
    intro x hx
    simp only [mem_image, oddPairs, mem_filter, mem_range] at hx ⊢
    obtain ⟨m, ⟨hm, _, hodd⟩, rfl⟩ := hx
    exact ⟨by omega, hodd⟩
  · intro x hx y hy hxy
    simp only [oddPairs, coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    omega

theorem oddPairs_subset (N : ℕ) : oddPairs N ⊆ {n ∈ range (N + 1) | Odd n} := by
  intro m hm
  simp only [oddPairs, mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1⟩

/-- `log² 2i / i ≤ 3 log² 2k / k` for `1 ≤ i ≤ k ≤ 3i`. -/
theorem ai_le {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (hk : k ≤ 3 * i) :
    Real.log (2 * i) ^ 2 / i ≤ 3 * (Real.log (2 * k) ^ 2 / k) := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
  have hk' : (k : ℝ) ≤ 3 * i := by exact_mod_cast hk
  have hl0 : 0 ≤ Real.log (2 * i) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 * i) ≤ Real.log (2 * k) :=
    Real.log_le_log (by linarith) (by linarith)
  have hsq : Real.log (2 * i) ^ 2 ≤ Real.log (2 * k) ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have hB : 0 ≤ Real.log (2 * k) ^ 2 := sq_nonneg _
  have hkpos : (0 : ℝ) < k := by linarith
  have h3 : (1 : ℝ) ≤ 3 * i / k := by rw [one_le_div hkpos]; linarith
  rw [div_le_iff₀ (by linarith)]
  calc Real.log (2 * i) ^ 2 ≤ Real.log (2 * k) ^ 2 * 1 := by linarith
    _ ≤ Real.log (2 * k) ^ 2 * (3 * i / k) := mul_le_mul_of_nonneg_left h3 hB
    _ = 3 * (Real.log (2 * k) ^ 2 / k) * i := by ring

/-- **The last sum of (10)**, PROVED, CONDITIONAL ON `Theorem1`: with `k = i + j`, `i = j` or
`i = j + 1`, `j ≥ 1`, for all large `N`,
`(Σ'' s_i(m) s_j(N - m))² ≤ (3 C (log² 2k / k) N L^{k-2})²`, by Cauchy's inequality and (3). -/
theorem last_term_sq (h1 : Theorem1) :
    ∃ C : ℝ, ∀ i j : ℕ, 1 ≤ j → (i = j ∨ i = j + 1) → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ m ∈ oddPairs N, s i N m * s j N (N - m)) ^ 2 ≤
        (3 * C * (Real.log (2 * (i + j : ℕ)) ^ 2 / (i + j : ℕ)) * N *
          (Nat.log 2 N : ℝ) ^ (i + j - 2)) ^ 2 := by
  obtain ⟨C, hC⟩ := h1
  refine ⟨C, fun i j hj hij => ?_⟩
  have hi : 1 ≤ i := by omega
  obtain ⟨Ni, hNi⟩ := hC i hi
  obtain ⟨Nj, hNj⟩ := hC j hj
  refine ⟨max Ni Nj, fun N hN => ?_⟩
  have hSi := hNi N (le_of_max_le_left hN)
  have hSj := hNj N (le_of_max_le_right hN)
  set L : ℝ := (Nat.log 2 N : ℝ)
  set k := i + j with hk
  set ai := Real.log (2 * i) ^ 2 / i
  set aj := Real.log (2 * j) ^ 2 / j
  set b := Real.log (2 * (k : ℕ)) ^ 2 / (k : ℕ)
  have hX : ∑ m ∈ oddPairs N, s i N m ^ 2 ≤ C * ai * N * L ^ (2 * i - 2) :=
    (sum_le_sum_of_subset_of_nonneg (oddPairs_subset N) (fun _ _ _ => sq_nonneg _)).trans hSi
  have hY : ∑ m ∈ oddPairs N, s j N (N - m) ^ 2 ≤ C * aj * N * L ^ (2 * j - 2) :=
    (sum_reflect_le (fun n => s j N n ^ 2) (fun _ => sq_nonneg _) N).trans hSj
  have hCS := sum_mul_sq_le_sq_mul_sq (oddPairs N) (fun m => s i N m) (fun m => s j N (N - m))
  have hX0 : 0 ≤ ∑ m ∈ oddPairs N, s i N m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hY0 : 0 ≤ ∑ m ∈ oddPairs N, s j N (N - m) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hXY := mul_le_mul hX hY hY0 (hX0.trans hX)
  have hai : ai ≤ 3 * b := by
    have := ai_le (i := i) (k := k) hi (by omega) (by omega)
    simpa [b] using this
  have haj : aj ≤ 3 * b := by
    have := ai_le (i := j) (k := k) hj (by omega) (by omega)
    simpa [b] using this
  have hai0 : 0 ≤ ai := by positivity
  have haj0 : 0 ≤ aj := by positivity
  have hab : ai * aj ≤ (3 * b) * (3 * b) := mul_le_mul hai haj haj0 (hai0.trans hai)
  have hpow : L ^ (2 * i - 2) * L ^ (2 * j - 2) = (L ^ (k - 2)) ^ 2 := by
    rw [← pow_add, ← pow_mul]; congr 1; omega
  have hR : C * ai * N * L ^ (2 * i - 2) * (C * aj * N * L ^ (2 * j - 2)) =
      (ai * aj) * (C ^ 2 * (N : ℝ) ^ 2 * (L ^ (k - 2)) ^ 2) := by
    rw [← hpow]; ring
  have hQ : 0 ≤ C ^ 2 * (N : ℝ) ^ 2 * (L ^ (k - 2)) ^ 2 := by positivity
  calc (∑ m ∈ oddPairs N, s i N m * s j N (N - m)) ^ 2
      ≤ (∑ m ∈ oddPairs N, s i N m ^ 2) * ∑ m ∈ oddPairs N, s j N (N - m) ^ 2 := hCS
    _ ≤ _ := hXY
    _ = (ai * aj) * (C ^ 2 * (N : ℝ) ^ 2 * (L ^ (k - 2)) ^ 2) := hR
    _ ≤ ((3 * b) * (3 * b)) * (C ^ 2 * (N : ℝ) ^ 2 * (L ^ (k - 2)) ^ 2) :=
        mul_le_mul_of_nonneg_right hab hQ
    _ = (3 * C * b * N * L ^ (k - 2)) ^ 2 := by ring

/-- Vacuity: `oddPairs 10 = {1, 3, 5, 7, 9}`, the condition (a), (b) pairs exist. -/
theorem oddPairs_10 : #(oddPairs 10) = 5 := by decide

/-! ### The terms of p.140 that violate (a): `m` even -/

open LeanLab.LPZ2007 (tuples pow2sum card_tuples)

/-- For even `m`, only `p = 2` can occur, so `r'_i(m)` counts tuples with `2 + Σ 2^{ν} = m`. -/
theorem rk_even_le (i N m : ℕ) (hm : Even m) :
    rk i N m ≤ #{ν ∈ tuples i (Nat.log 2 N) | 2 + pow2sum ν = m} := by
  unfold rk
  apply card_le_card_of_injOn (fun x => x.2)
  · intro x hx
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hx
    obtain ⟨⟨_, hν⟩, hp, hmx⟩ := hx
    have hev : Even (pow2sum x.2) := by
      unfold pow2sum
      apply Finset.even_sum
      intro j _
      have h1 : 1 ≤ x.2 j := by
        simp only [tuples, Fintype.mem_piFinset, mem_Icc] at hν
        exact (hν j).1
      exact (Nat.even_pow).2 ⟨even_two, by omega⟩
    have hp2 : x.1 = 2 := by
      rw [← hp.even_iff]
      have : x.1 = m - pow2sum x.2 := by omega
      rw [this]
      exact (Nat.even_sub (by omega)).2 ⟨fun _ => hev, fun _ => hm⟩
    simp only [coe_filter, Set.mem_ofPred_eq]
    exact ⟨hν, by omega⟩
  · intro x hx y hy hxy
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    apply Prod.ext _ hxy
    have h1 := hx.2.2
    have h2 := hy.2.2
    rw [hxy] at h1
    omega

/-- `Σ_{m ≤ N, m even} r'_i(m) ≤ L^i`: each tuple gives at most one `m`. -/
theorem even_sum_le (i N : ℕ) :
    ∑ m ∈ range (N + 1) with Even m, rk i N m ≤ Nat.log 2 N ^ i := by
  classical
  calc ∑ m ∈ range (N + 1) with Even m, rk i N m
      ≤ ∑ m ∈ range (N + 1) with Even m,
          #{ν ∈ tuples i (Nat.log 2 N) | 2 + pow2sum ν = m} :=
        sum_le_sum fun m hm => rk_even_le i N m (mem_filter.1 hm).2
    _ = #{ν ∈ tuples i (Nat.log 2 N) | 2 + pow2sum ν ∈ {m ∈ range (N + 1) | Even m}} :=
        sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ #(tuples i (Nat.log 2 N)) := card_le_card (filter_subset _ _)
    _ = Nat.log 2 N ^ i := card_tuples _ _

/-- **The (a)-violating terms, p.140**, PROVED: `Σ_{m even} r'_i(m)² ≤ L^{2i}`, the paper's
`≪ L^{2i}` by the remark on p.139 that such representations have `p | g(g-1)`. -/
theorem even_sq_sum_le (i N : ℕ) :
    ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) ^ 2 ≤ (Nat.log 2 N : ℝ) ^ (2 * i) := by
  have h := even_sum_le i N
  have h' : ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) ≤ (Nat.log 2 N : ℝ) ^ i := by
    exact_mod_cast h
  calc ∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) ^ 2
      ≤ (∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ)) ^ 2 :=
        sum_sq_le_sq_sum_of_nonneg fun _ _ => by positivity
    _ ≤ ((Nat.log 2 N : ℝ) ^ i) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
    _ = (Nat.log 2 N : ℝ) ^ (2 * i) := by rw [← pow_mul, mul_comm]

/-- **The first error term of (9)**, PROVED with Lemma 13 as a hypothesis `B`: if
`Σ_{n ≤ N} r'_j(n)² ≤ B`, the terms of `r''_k(N)` with `m` even contribute at most
`L^{2i} B` in square, the paper's `{L^{2i} · N L^{2j-2}}^{1/2}`. -/
theorem even_terms_sq (i j N : ℕ) {B : ℝ}
    (hB : ∑ n ∈ range (N + 1), (rk j N n : ℝ) ^ 2 ≤ B) :
    (∑ m ∈ range (N + 1) with Even m, (rk i N m : ℝ) * rk j N (N - m)) ^ 2 ≤
      (Nat.log 2 N : ℝ) ^ (2 * i) * B := by
  have hCS := sum_mul_sq_le_sq_mul_sq ({m ∈ range (N + 1) | Even m})
    (fun m => (rk i N m : ℝ)) (fun m => (rk j N (N - m) : ℝ))
  have hY : ∑ m ∈ range (N + 1) with Even m, (rk j N (N - m) : ℝ) ^ 2 ≤ B := by
    refine le_trans ?_ hB
    rw [← sum_image (s := {m ∈ range (N + 1) | Even m}) (g := fun m => N - m)
      (f := fun n => (rk j N n : ℝ) ^ 2)]
    · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro x hx
      simp only [mem_image, mem_filter, mem_range] at hx ⊢
      omega
    · intro x hx y hy hxy
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
      simp only at hxy
      omega
  have hY0 : 0 ≤ ∑ m ∈ range (N + 1) with Even m, (rk j N (N - m) : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  calc _ ≤ _ := hCS
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * i) * B :=
        mul_le_mul (even_sq_sum_le i N) hY hY0 (by positivity)

/-- **The first sum of (10) for g = 2**, PROVED exactly: for even `N`, `Σ'' 1 = N/2`, which is
the paper's `N D'/D` with `D = 2`, `D' = 1`. -/
theorem card_oddPairs {N : ℕ} (hN : Even N) : #(oddPairs N) = N / 2 := by
  have h : oddPairs N = (range (N / 2)).image (fun t => 2 * t + 1) := by
    ext m
    obtain ⟨r, hr⟩ := hN
    simp only [oddPairs, mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hm, ⟨c, hc⟩, _⟩
      exact ⟨c, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by omega, ⟨t, rfl⟩, ⟨r - t - 1, by omega⟩⟩
  rw [h, card_image_of_injective _ (fun a b hab => by omega), card_range]

end LeanLab.Linnik.Gallagher1975Thm2

