module

public import GoldbachLean.Wu2008.Sum

/-!
T1, unit U-1133, PC run 20261020T0003Z-10609. P0043 Wu 2008 Lemma 2.2: the O(N^{1−κ₁}) term made
explicit. For any finite A of integers 0 < a < N coprime to N and κ₁ with N^κ₁ > 1,
  E = #{a ∈ A : a sifted at N^κ₁, a not squarefree} ≤ N/(N^κ₁ − 1),     `Esq_le`
since such an a has q² | a for a prime q ≥ N^κ₁, at most N/q² of 1..N are multiples of q², and
Σ_{q ≥ M} 1/q² ≤ 1/(M − 1). With Wu2008Lemma22Sum.lean this gives (2.2) with an explicit error,
  3Υ₁ + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁ ≤ 4 D₁₂ + 4N/(N^κ₁ − 1),   `lemma22_explicit`,
and for Wu's own A = {N − p : p < N prime, p ∤ N}, `wuA`, `lemma22_wuA`.
KNOWN mathematics. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuSum
open Finset
open GoldbachLean.Wu2008.WuSieve (Sifted)
open GoldbachLean.Wu2008.WuReal (Admissible)

@[expose] public noncomputable section
open scoped Classical

/-- `Σ_{M ≤ m ≤ K} 1/m² ≤ 1/(M − 1)` for `M ≥ 2`. -/
lemma sum_inv_sq_le (M : ℕ) (hM : 2 ≤ M) (K : ℕ) :
    ∑ m ∈ Icc M K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / (max K (M - 1) : ℕ) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  induction K with
  | zero =>
    have : Icc M 0 = ∅ := by ext x; simp; omega
    rw [this, sum_empty]
    have : max 0 (M - 1) = M - 1 := by omega
    rw [this]; push_cast [show 1 ≤ M by omega]; simp
  | succ K ih =>
    by_cases hK : K + 1 < M
    · have : Icc M (K + 1) = ∅ := by ext x; simp; omega
      rw [this, sum_empty]
      have : max (K + 1) (M - 1) = M - 1 := by omega
      rw [this]; push_cast [show 1 ≤ M by omega]; simp
    · have hI : Icc M (K + 1) = insert (K + 1) (Icc M K) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hI, sum_insert (by simp)]
      have hmax : max (K + 1) (M - 1) = K + 1 := by omega
      have hmax' : max K (M - 1) = K := by omega
      rw [hmax]; rw [hmax'] at ih
      have hK1 : (1 : ℝ) ≤ K := by
        have : 1 ≤ K := by omega
        exact_mod_cast this
      have key : (1 : ℝ) / ((K + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

lemma sum_inv_sq_le' (M : ℕ) (hM : 2 ≤ M) (K : ℕ) :
    ∑ m ∈ Icc M K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have := sum_inv_sq_le M hM K
  have : (0 : ℝ) ≤ 1 / (max K (M - 1) : ℕ) := by positivity
  linarith

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

/-- **The non-squarefree error, explicit.** -/
theorem Esq_le (hN : 1 < (N : ℝ) ^ k1) (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (Esq A N k1 : ℝ) ≤ N / ((N : ℝ) ^ k1 - 1) := by
  set M := ⌈(N : ℝ) ^ k1⌉₊ with hMdef
  have hM2 : 2 ≤ M := by
    have : (1 : ℝ) < M := lt_of_lt_of_le hN (Nat.le_ceil _)
    exact_mod_cast this
  set Q := (Icc M N).filter Nat.Prime with hQ
  -- every bad a has q² | a for some q ∈ Q
  have hsub : {a ∈ A | Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a} ⊆
      Q.biUnion (fun q => (Ioc 0 N).filter (fun a => q * q ∣ a)) := by
    intro a ha
    obtain ⟨haA, hs, hsq⟩ := mem_filter.1 ha
    obtain ⟨h0, hlt, hcop⟩ := hAN a haA
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push_neg at hsq
    obtain ⟨q, hq, hqq⟩ := hsq
    have hqa : q ∣ a := dvd_trans (dvd_mul_right q q) hqq
    have hk := (sifted_iff h0 hlt hcop _).1 hs q ((mem_pf h0 hlt hcop).2 ⟨hq, hqa⟩)
    have hqN : q ≤ N := (Nat.le_of_dvd h0 hqa).trans hlt.le
    rw [mem_biUnion]
    refine ⟨q, mem_filter.2 ⟨mem_Icc.2 ⟨Nat.ceil_le.2 hk, hqN⟩, hq⟩, mem_filter.2
      ⟨mem_Ioc.2 ⟨h0, hlt.le⟩, hqq⟩⟩
  have h1 : (Esq A N k1 : ℝ) ≤ ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) := by
    unfold Esq
    have := (card_le_card hsub).trans card_biUnion_le
    calc (#{a ∈ A | Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a} : ℝ)
        ≤ ((∑ q ∈ Q, #((Ioc 0 N).filter (fun a => q * q ∣ a)) : ℕ) : ℝ) := by exact_mod_cast this
      _ = ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) := by
        push_cast
        refine sum_congr rfl fun q _ => ?_
        rw [Nat.Ioc_filter_dvd_card_eq_div]
  have h2 : ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) ≤ ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) := by
    calc ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) ≤ ∑ q ∈ Q, (N : ℝ) * (1 / (q : ℝ) ^ 2) := by
          refine sum_le_sum fun q hq => ?_
          have hq0 : (0 : ℝ) < q := by
            have := (mem_filter.1 hq).2.pos; exact_mod_cast this
          rw [mul_one_div, le_div_iff₀ (by positivity)]
          have := Nat.cast_div_le (α := ℝ) (m := N) (n := q * q)
          push_cast at this
          calc ((N / (q * q) : ℕ) : ℝ) * (q : ℝ) ^ 2 ≤ (N : ℝ) / ((q : ℝ) * q) * (q : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = N := by field_simp
      _ ≤ ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have h3 : ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) ≤ N * (1 / ((M : ℝ) - 1)) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_le' M hM2 N) (Nat.cast_nonneg _)
  have h4 : (N : ℝ) * (1 / ((M : ℝ) - 1)) ≤ N / ((N : ℝ) ^ k1 - 1) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith [Nat.le_ceil ((N : ℝ) ^ k1)])
  linarith

/-- **Wu 2008 (2.2), Υ₁₁ repaired, with the error explicit.** -/
theorem lemma22_explicit (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ k1)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : ℝ) - Y3 A N k1 - Y4 A N k1
      - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2
      ≤ 4 * D12 A + 4 * (N / ((N : ℝ) ^ k1 - 1)) := by
  have h := lemma22_sum A N k1 k2 hA hN hAN
  have hR : ((3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : ℤ) - Y3 A N k1 - Y4 A N k1
      - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2 : ℝ)
      ≤ ((4 * D12 A + 4 * Esq A N k1 : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  have := Esq_le A N k1 hNk hAN
  linarith

/-- Wu's set `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA : Finset ℕ := ((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

lemma wuA_ok : ∀ a ∈ wuA N, 0 < a ∧ a < N ∧ a.Coprime N := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
  obtain ⟨hpN, hpr, hnd⟩ := by simpa only [mem_filter, mem_range] using hp
  have h2 := hpr.two_le
  refine ⟨by omega, by omega, ?_⟩
  have hc : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hpr).2 hnd
  exact (Nat.coprime_self_sub_left (by omega)).2 hc

/-- **(2.2) for Wu's own `A = {N − p}`, explicit error.** -/
theorem lemma22_wuA (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ k1) :
    (3 * Y1 (wuA N) N k1 + Y2 (wuA N) N k2 + Y5 (wuA N) N k1 k2 + Y6 (wuA N) N k1 k2 : ℝ)
      - Y3 (wuA N) N k1 - Y4 (wuA N) N k1 - 2 * Y7 (wuA N) N k1 - Y8 (wuA N) N k1
      - Y9 (wuA N) N k1 k2 - Y10 (wuA N) N k1 k2 - Y11 (wuA N) N k1 k2
      ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ k1 - 1)) :=
  lemma22_explicit (wuA N) N k1 k2 hA hN hNk (wuA_ok N)

/-- Vacuity: `N = 2^100` with Wu's κ₁ has `N^κ₁ > 1`, and `wuA` is nonempty at `N = 10`. -/
example : 1 < ((2 ^ 100 : ℕ) : ℝ) ^ WuReal.wk1 :=
  Real.one_lt_rpow (by norm_num) (by unfold WuReal.wk1; norm_num)
example : 7 ∈ wuA 10 := by
  unfold wuA; rw [mem_image]; exact ⟨3, by simp only [mem_filter, mem_range]; norm_num, rfl⟩

end

end GoldbachLean.Wu2008.WuSum

