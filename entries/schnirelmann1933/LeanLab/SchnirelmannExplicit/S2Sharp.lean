module

public import LeanLab.SchnirelmannGoldbach.S2

/-!
Sharper mean square bound for the singular product, unit U-0310, I-0063.
`∑_{n ≤ N} singProd n ^ 2 ≤ 2.52 N`, replacing the constant `9` of `S2_explicit`.
Method: `singProd n ^ 2 = ∏_{p ∣ n} (1 + h p)` with `h p = (2p + 1)/p²`, expand over subsets of
the prime factors, swap the sums, count multiples, and bound `∏_{p ≤ N} (1 + (2p + 1)/p³)` by the
exact product over the primes up to 100 times a telescoping tail `100/98`.
The true value of the infinite product is about 2.4748.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1302Z-30907. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannExplicit.Sharper3

open LeanLab.SchnirelmannGoldbach

/-- `h p = (1 + 1/p)^2 - 1 = (2p + 1)/p²`. -/
noncomputable def h (p : ℕ) : ℝ := (2 * p + 1) / (p : ℝ) ^ 2

/-- `a n = h n / n = (2n + 1)/n³`. -/
noncomputable def a (n : ℕ) : ℝ := (2 * n + 1) / (n : ℝ) ^ 3

lemma h_nonneg (p : ℕ) : 0 ≤ h p := by unfold h; positivity

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by unfold a; positivity

lemma sq_one_add (p : ℕ) (hp : p ≠ 0) : (1 + 1 / (p : ℝ)) ^ 2 = 1 + h p := by
  unfold h
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp
  ring

lemma h_div (p : ℕ) : h p / p = a p := by
  unfold h a
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp

lemma singProd_sq (n : ℕ) :
    singProd n ^ 2 = ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, h p := by
  unfold singProd
  rw [← Finset.prod_pow]
  rw [Finset.prod_congr rfl
    (fun p hp => sq_one_add p (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  exact Finset.prod_one_add _

/-- The primes up to `N`. -/
noncomputable def P (N : ℕ) : Finset ℕ := (Icc 1 N).filter Nat.Prime

lemma pointwise (N n : ℕ) (hn : n ∈ Icc 1 N) :
    singProd n ^ 2 ≤ ∑ t ∈ (P N).powerset,
      if (∏ p ∈ t, p) ∣ n then ∏ p ∈ t, h p else 0 := by
  rw [singProd_sq, ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    simp only [mem_powerset] at ht
    simp only [mem_filter, mem_powerset]
    simp only [mem_Icc] at hn
    refine ⟨fun p hp => ?_, ?_⟩
    · have hpf := ht hp
      have hpr := Nat.prime_of_mem_primeFactors hpf
      have hle : p ≤ n := Nat.le_of_mem_primeFactors hpf
      simp only [P, mem_filter, mem_Icc]
      exact ⟨⟨hpr.one_lt.le, hle.trans hn.2⟩, hpr⟩
    · exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id ht).trans
        (Nat.prod_primeFactors_dvd n)
  · intro t _ _
    exact Finset.prod_nonneg fun p _ => h_nonneg p

lemma prod_P_pos (N : ℕ) (t : Finset ℕ) (ht : t ∈ (P N).powerset) :
    (0 : ℝ) < ((∏ p ∈ t, p : ℕ) : ℝ) := by
  have : 0 < ∏ p ∈ t, p := by
    apply Finset.prod_pos
    intro p hp
    simp only [mem_powerset] at ht
    have := ht hp
    simp only [P, mem_filter] at this
    exact this.2.pos
  exact_mod_cast this

/-- **Mean square, multiplicative form.** -/
theorem sum_sq_le_prod (N : ℕ) :
    ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ N * ∏ p ∈ P N, (1 + a p) := by
  calc ∑ n ∈ Icc 1 N, singProd n ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ t ∈ (P N).powerset,
          (if (∏ p ∈ t, p) ∣ n then ∏ p ∈ t, h p else 0) :=
        Finset.sum_le_sum fun n hn => pointwise N n hn
    _ = ∑ t ∈ (P N).powerset, ∑ n ∈ Icc 1 N,
          (if (∏ p ∈ t, p) ∣ n then ∏ p ∈ t, h p else 0) := Finset.sum_comm
    _ = ∑ t ∈ (P N).powerset,
          (#{n ∈ Icc 1 N | (∏ p ∈ t, p) ∣ n} : ℝ) * ∏ p ∈ t, h p := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ (P N).powerset, ((N : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)) * ∏ p ∈ t, h p := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_right (card_dvd N _)
          (Finset.prod_nonneg fun p _ => h_nonneg p)
    _ = N * ∑ t ∈ (P N).powerset, ∏ p ∈ t, a p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hpos := prod_P_pos N t ht
        rw [Nat.cast_prod] at hpos ⊢
        rw [← Finset.prod_congr rfl (fun p _ => h_div p), Finset.prod_div_distrib]
        field_simp
    _ = N * ∏ p ∈ P N, (1 + a p) := by rw [Finset.prod_one_add]

/-- The exact product over the primes up to 100, about 2.46579. -/
lemma head_value : ∏ p ∈ (range 101).filter Nat.Prime, (1 + a p) ≤ 2.4658 := by
  rw [Finset.prod_filter]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, a]
  norm_num

lemma head_le (N : ℕ) : ∏ p ∈ (P N).filter (· ≤ 100), (1 + a p) ≤ 2.4658 := by
  refine le_trans ?_ head_value
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    simp only [P, mem_filter, mem_Icc] at hp
    simp only [mem_filter, mem_range]
    exact ⟨by omega, hp.1.2⟩
  · intro p _; linarith [a_nonneg p]
  · intro p _ _; linarith [a_nonneg p]

lemma step_ineq (n : ℝ) (hn : 101 ≤ n) :
    (1 + (2 * n + 1) / n ^ 3) * ((n - 3) / (n - 1)) ≤ (n - 2) / n := by
  have h1 : 0 < n - 1 := by linarith
  have hn0 : 0 < n := by linarith
  rw [show (1 + (2 * n + 1) / n ^ 3) = (n ^ 3 + 2 * n + 1) / n ^ 3 by field_simp; ring,
    div_mul_div_comm, div_le_div_iff₀ (by positivity) hn0]
  nlinarith [sq_nonneg n, mul_pos hn0 hn0, mul_pos (mul_pos hn0 hn0) hn0]

/-- Telescoping tail: `∏_{100 < n ≤ N} (1 + a n) ≤ (100/98) (N - 2)/N`. -/
lemma tail_aux : ∀ k : ℕ, ∏ n ∈ Ioc 100 (100 + k), (1 + a n) ≤
    (100 / 98) * (((100 + k : ℕ) : ℝ) - 2) / ((100 + k : ℕ) : ℝ)
  | 0 => by norm_num
  | k + 1 => by
    have e : Ioc 100 (100 + (k + 1)) = insert (100 + (k + 1)) (Ioc 100 (100 + k)) := by
      ext x; simp only [mem_Ioc, mem_insert]; omega
    have hnot : 100 + (k + 1) ∉ Ioc 100 (100 + k) := by simp
    rw [e, Finset.prod_insert hnot]
    have ih := tail_aux k
    set n : ℝ := ((100 + (k + 1) : ℕ) : ℝ) with hn
    have hn' : ((100 + k : ℕ) : ℝ) = n - 1 := by rw [hn]; push_cast; ring
    rw [hn'] at ih
    have hn101 : (101 : ℝ) ≤ n := by rw [hn]; push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have ha : a (100 + (k + 1)) = (2 * n + 1) / n ^ 3 := by unfold a; rw [hn]
    rw [ha]
    have hpos : 0 ≤ 1 + (2 * n + 1) / n ^ 3 := by positivity
    calc (1 + (2 * n + 1) / n ^ 3) * ∏ n ∈ Ioc 100 (100 + k), (1 + a n)
        ≤ (1 + (2 * n + 1) / n ^ 3) * ((100 / 98) * (n - 1 - 2) / (n - 1)) :=
          mul_le_mul_of_nonneg_left ih hpos
      _ = (100 / 98) * ((1 + (2 * n + 1) / n ^ 3) * ((n - 3) / (n - 1))) := by ring
      _ ≤ (100 / 98) * ((n - 2) / n) := by
          gcongr
          exact step_ineq n hn101
      _ = (100 / 98) * (n - 2) / n := by ring

lemma tail_le (N : ℕ) : ∏ n ∈ Ioc 100 N, (1 + a n) ≤ 100 / 98 := by
  rcases le_or_gt N 100 with hN | hN
  · rw [Finset.Ioc_eq_empty (by omega)]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, N = 100 + k := ⟨N - 100, by omega⟩
    refine (tail_aux k).trans ?_
    have hpos : (0 : ℝ) < ((100 + k : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc]
    have : (((100 + k : ℕ) : ℝ) - 2) / ((100 + k : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    nlinarith

lemma tail_P_le (N : ℕ) : ∏ p ∈ (P N).filter (fun p => ¬ p ≤ 100), (1 + a p) ≤ 100 / 98 := by
  refine le_trans ?_ (tail_le N)
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    simp only [P, mem_filter, mem_Icc] at hp
    simp only [mem_Ioc]; omega
  · intro p _; linarith [a_nonneg p]
  · intro p _ _; linarith [a_nonneg p]

/-- `∏_{p ≤ N} (1 + (2p + 1)/p³) ≤ 2.52` for every `N`. -/
theorem prod_P_le (N : ℕ) : ∏ p ∈ P N, (1 + a p) ≤ 2.52 := by
  rw [← Finset.prod_filter_mul_prod_filter_not (P N) (· ≤ 100)]
  have h1 := head_le N
  have h2 := tail_P_le N
  have h0 : 0 ≤ ∏ p ∈ (P N).filter (fun p => ¬ p ≤ 100), (1 + a p) :=
    Finset.prod_nonneg fun p _ => by linarith [a_nonneg p]
  calc _ ≤ 2.4658 * ∏ p ∈ (P N).filter (fun p => ¬ p ≤ 100), (1 + a p) :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ 2.4658 * (100 / 98) := by gcongr
    _ ≤ 2.52 := by norm_num

/-- **S2, sharper.** `∑_{n ≤ N} singProd n ^ 2 ≤ 2.52 N`. The old constant was `9`. -/
theorem S2_sharp : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ 2.52 * N := by
  intro N _
  calc ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ N * ∏ p ∈ P N, (1 + a p) := sum_sq_le_prod N
    _ ≤ N * 2.52 := by gcongr; exact prod_P_le N
    _ = 2.52 * N := by ring

end LeanLab.SchnirelmannExplicit.Sharper3
