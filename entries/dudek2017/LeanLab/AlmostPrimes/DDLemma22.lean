module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T1203Z-2488, unit U-0945.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
Lemma 2.2, the step `1/3 + Σ_{2 < p < z} 1/p² < 0.5357`, read earlier in Claude in Chrome.

PROVED `lemma2_2_primeSum`: for every natural `z`, `1/3 + Σ_{p prime, 2 < p < z} 1/p² < 0.5357`.
Method: the primes in `[3, 10⁴)` are the `n` with no divisor `d` in `[2, 100]` below `n`, a
kernel check; each `1/n²` is rounded up to `⌈10¹²/n²⌉ / 10¹²` and the 1228 rounded terms sum to
`202237604947`, a kernel check; the tail over all `n ≥ 10⁴` telescopes to at most `1/9999`.
Total about `0.5356709`, margin about `2.9 · 10⁻⁵`.
-/

@[expose] public section

open Finset

noncomputable section
namespace LeanLab.AlmostPrimes.DDLemma22

/-- `n` has a divisor `d` with `2 ≤ d ≤ 100` and `d < n`. -/
def smallFac (n : ℕ) : Bool := (List.range' 2 99).any (fun d => decide (d < n) && n % d == 0)

/-- Candidates for odd primes below `10⁴`. -/
def cand (n : ℕ) : Bool := decide (3 ≤ n) && !smallFac n

/-- `⌈10¹² / n²⌉`. -/
def ub (n : ℕ) : ℕ := (10 ^ 12 + n ^ 2 - 1) / n ^ 2

lemma cand_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : cand p = true := by
  unfold cand
  simp only [h3, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true]
  unfold smallFac
  rw [Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨d, hd, hdp⟩ := h
  rw [List.mem_range'_1] at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hdp
  have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hdp.2
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · omega
  · omega

/-- The kernel check: the rounded head sum. -/
theorem head_nat :
    ∑ n ∈ (range 10000).filter (fun n => cand n = true), ub n ≤ 202237604947 := by
  decide +kernel

lemma inv_sq_le_ub (n : ℕ) (hn : 0 < n) : (1 : ℝ) / (n : ℝ) ^ 2 ≤ (ub n : ℝ) / 10 ^ 12 := by
  have hn2 : 0 < n ^ 2 := by positivity
  have key : 10 ^ 12 ≤ ub n * n ^ 2 := by
    unfold ub
    have := Nat.div_add_mod (10 ^ 12 + n ^ 2 - 1) (n ^ 2)
    have := Nat.mod_lt (10 ^ 12 + n ^ 2 - 1) hn2
    nlinarith [Nat.div_mul_cancel (dvd_refl (n ^ 2)), Nat.sub_add_cancel (by omega : 1 ≤ 10 ^ 12 + n ^ 2)]
  have hr : (10 : ℝ) ^ 12 ≤ (ub n : ℝ) * (n : ℝ) ^ 2 := by exact_mod_cast key
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- The telescoping tail: for `M ≥ 2`, `Σ_{M ≤ n < z} 1/n² ≤ 1/(M - 1)`. -/
lemma tail_le (M : ℕ) (hM : 2 ≤ M) (z : ℕ) :
    ∑ n ∈ Ico M z, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  -- stronger: the sum is at most 1/(M-1) - 1/(max z M - 1)
  suffices h : ∀ z, ∑ n ∈ Ico M z, (1 : ℝ) / (n : ℝ) ^ 2 ≤
      1 / ((M : ℝ) - 1) - 1 / ((max z M : ℕ) - 1 : ℝ) by
    have := h z
    have hpos : 0 ≤ 1 / ((max z M : ℕ) - 1 : ℝ) := by
      have : (2 : ℝ) ≤ (max z M : ℕ) := by exact_mod_cast le_trans hM (le_max_right _ _)
      apply div_nonneg (by norm_num); linarith
    linarith
  intro z
  induction z with
  | zero => simp
  | succ k ih =>
    by_cases hk : M ≤ k
    · rw [Finset.sum_Ico_succ_top hk]
      have e1 : max k M = k := max_eq_left hk
      have e2 : max (k + 1) M = k + 1 := max_eq_left (by omega)
      rw [e1] at ih; rw [e2]
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast le_trans hM hk
      have step : (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (((k + 1 : ℕ) : ℝ) - 1) := by
        push_cast
        rw [show (k : ℝ) + 1 - 1 = k by ring, div_sub_div _ _ (by linarith) (by linarith),
          div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith
      linarith
    · have hk2 : Ico M (k + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hk2, Finset.sum_empty]
      have e2 : max (k + 1) M = M := max_eq_right (by omega)
      rw [e2]; simp

/-- **Dudek-Dunn Lemma 2.2's prime sum, PROVED.** For every `z`,
`1/3 + Σ_{p prime, 2 < p < z} 1/p² < 0.5357`; the true limit is about `0.535581`. -/
theorem lemma2_2_primeSum (z : ℕ) :
    (1 : ℝ) / 3 + ∑ p ∈ (range z).filter (fun p => p.Prime ∧ 2 < p), (1 : ℝ) / (p : ℝ) ^ 2 <
      5357 / 10000 := by
  set S := (range z).filter (fun p => p.Prime ∧ 2 < p) with hS
  have hsplit : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 =
      ∑ p ∈ S.filter (fun p => p < 10000), (1 : ℝ) / (p : ℝ) ^ 2 +
        ∑ p ∈ S.filter (fun p => ¬ p < 10000), (1 : ℝ) / (p : ℝ) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  -- head
  have hsub1 : S.filter (fun p => p < 10000) ⊆ (range 10000).filter (fun n => cand n = true) := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.2, cand_of_prime hp.1.2.1 hp.1.2.2⟩
  have hhead : ∑ p ∈ S.filter (fun p => p < 10000), (1 : ℝ) / (p : ℝ) ^ 2 ≤
      202237604947 / 10 ^ 12 := by
    calc ∑ p ∈ S.filter (fun p => p < 10000), (1 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (range 10000).filter (fun n => cand n = true), (1 : ℝ) / (p : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _ => by positivity)
      _ ≤ ∑ p ∈ (range 10000).filter (fun n => cand n = true), (ub p : ℝ) / 10 ^ 12 := by
          apply Finset.sum_le_sum
          intro n hn
          simp only [Finset.mem_filter, cand, Bool.and_eq_true, decide_eq_true_eq] at hn
          exact inv_sq_le_ub n (by omega)
      _ = (∑ p ∈ (range 10000).filter (fun n => cand n = true), ub p : ℕ) / 10 ^ 12 := by
          rw [← Finset.sum_div]; push_cast; rfl
      _ ≤ 202237604947 / 10 ^ 12 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact_mod_cast head_nat
  -- tail
  have hsub2 : S.filter (fun p => ¬ p < 10000) ⊆ Ico 10000 z := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hp ⊢
    omega
  have htail : ∑ p ∈ S.filter (fun p => ¬ p < 10000), (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 9999 := by
    calc _ ≤ ∑ n ∈ Ico 10000 z, (1 : ℝ) / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ ≤ 1 / ((10000 : ℕ) - 1 : ℝ) := tail_le 10000 (by norm_num) z
      _ = 1 / 9999 := by norm_num
  rw [hsplit]
  have : (1 : ℝ) / 3 + 202237604947 / 10 ^ 12 + 1 / 9999 < 5357 / 10000 := by norm_num
  linarith

end LeanLab.AlmostPrimes.DDLemma22
