module

public import LeanLab.DensityGoldbach.AlsetriShaoLocal
public import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5907, paper P0047.
Two facts about the local count of Alsetri and Shao 2024, Theorem 2.1.
First, `card_X_one_le`: at `n = 1` the lower bound `card_X_ge` is an equality bound, that is
`|X(1)| ≤ ∏_{p ∣ m} (p - 2)` for squarefree `m`, so the count of Theorem 2.1 is attained.
Second, `exists_modulus`: for every `ε > 0` there is an odd squarefree modulus `m` with
`∏_{p ∣ m} (p - 2) ≤ ε φ(m)`, taken as the product of the odd primes below a cutoff, using the
divergence of the sum of prime reciprocals from Mathlib.
No cited input. Binary Goldbach is OPEN; these are local facts only.
Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.DensityGoldbach.AlsetriShaoLocal
open Finset

lemma card_X_prime_one (p : ℕ) [hp : Fact p.Prime] : (Xset p 1).card = p - 2 := by
  have hX : Xset p 1 = univ \ {0, 1} := by
    ext x
    simp only [Xset, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert, mem_singleton,
      isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
    tauto
  rw [hX, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  rw [card_insert_of_notMem (by simp), card_singleton]

/-- Upper bound matching card_X_ge at n = 1. -/
theorem card_X_one_le (m : ℕ) (hm : 0 < m) (hsq : Squarefree m) :
    haveI : NeZero m := ⟨hm.ne'⟩
    (Xset m 1).card ≤ ∏ p ∈ m.primeFactors, (p - 2) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hpp hk =>
    have hk1 : k = 1 := by
      by_contra hne
      have h2 : 2 ≤ k := by omega
      have : p * p ∣ p ^ k := by
        rw [← pow_two]; exact pow_dvd_pow p h2
      have := hsq p this
      exact hpp.one_lt.ne' (Nat.isUnit_iff.mp this)
    subst hk1
    have : Fact (p ^ 1).Prime := ⟨by simpa using hpp⟩
    rw [show (p ^ 1).primeFactors = {p} by simp [hpp.primeFactors], prod_singleton]
    have := card_X_prime_one (p ^ 1)
    simp only [pow_one] at this ⊢
    exact this.le
  | zero => exact absurd hm (lt_irrefl 0)
  | one =>
    simp only [Nat.primeFactors_one, prod_empty]
    have : NeZero 1 := ⟨one_ne_zero⟩
    calc (Xset 1 1).card ≤ (univ : Finset (ZMod 1)).card := card_le_card (subset_univ _)
      _ = 1 := by rw [card_univ, ZMod.card]
  | coprime a b ha hb hab iha ihb =>
    have : NeZero a := ⟨by omega⟩
    have : NeZero b := ⟨by omega⟩
    have : NeZero (a * b) := ⟨hm.ne'⟩
    have hsa : Squarefree a := hsq.of_mul_left
    have hsb : Squarefree b := hsq.of_mul_right
    rw [card_X_mul a b hab 1, map_one, Nat.Coprime.primeFactors_mul hab,
      prod_union (Nat.Coprime.disjoint_primeFactors hab)]
    exact Nat.mul_le_mul (iha (by omega) hsa) (ihb (by omega) hsb)

/-- The odd primes below `K`. -/
def oddPrimesBelow (K : ℕ) : Finset ℕ := (Nat.primesBelow K).filter (· ≠ 2)

lemma prime_of_mem_oddPrimesBelow {K p : ℕ} (hp : p ∈ oddPrimesBelow K) : p.Prime :=
  Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1

lemma ne_two_of_mem_oddPrimesBelow {K p : ℕ} (hp : p ∈ oddPrimesBelow K) : p ≠ 2 :=
  (mem_filter.mp hp).2

/-- The partial sums of `1/p` over odd primes are unbounded. -/
lemma exists_oddPrimesBelow_sum_gt (C : ℝ) :
    ∃ K, C < ∑ p ∈ oddPrimesBelow K, (1 : ℝ) / p := by
  by_contra hcon
  push Not at hcon
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := C + 1 / 2) ?_ ?_
  · intro n
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> positivity
  · intro K
    have hsum : ∑ i ∈ range K, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
        ∑ p ∈ Nat.primesBelow K, (1 : ℝ) / p := by
      rw [Nat.primesBelow, sum_filter]
      refine sum_congr rfl fun i _ => ?_
      simp [Set.indicator]
    rw [hsum, Nat.primesBelow, ← sum_filter_add_sum_filter_not _ (· ≠ 2)]
    have h1 := hcon K
    have h2 : ∑ p ∈ ((range K).filter Nat.Prime).filter (fun p => ¬ p ≠ 2), (1 : ℝ) / p ≤
        ∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_filter, not_not] at hx
        simp [hx.2]
      · intros; positivity
    simp only [sum_singleton] at h2
    unfold oddPrimesBelow Nat.primesBelow at h1
    push_cast at h2
    linarith

/-- Odd squarefree moduli with ∏_{p ∣ m} (p-2) ≤ ε φ(m). -/
theorem exists_modulus : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 0 < m ∧ Odd m ∧ Squarefree m ∧
    ((∏ p ∈ m.primeFactors, (p - 2) : ℕ) : ℝ) ≤ ε * (Nat.totient m : ℝ) := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_oddPrimesBelow_sum_gt (-Real.log ε)
  set S := oddPrimesBelow K with hS
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => prime_of_mem_oddPrimesBelow hp
  set m := ∏ p ∈ S, p with hmdef
  have hm : 0 < m := prod_pos fun p hp => (hprime p hp).pos
  have hsq : Squarefree m := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      fun p hp => (hprime p hp).squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  have hodd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨p, hp, h2p⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h2
    exact ne_two_of_mem_oddPrimesBelow hp
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hprime p hp)).mp h2p).symm
  have hpf : m.primeFactors = S := Nat.primeFactors_prod hprime
  refine ⟨m, hm, hodd, hsq, ?_⟩
  rw [totient_squarefree hm hsq, hpf]
  push_cast
  have hcast2 : ∀ p ∈ S, (((p - 2 : ℕ)) : ℝ) = (p : ℝ) - 2 := fun p hp => by
    rw [Nat.cast_sub (hprime p hp).two_le]; norm_num
  have hcast1 : ∀ p ∈ S, (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := fun p hp => by
    rw [Nat.cast_sub (hprime p hp).one_le]; norm_num
  rw [prod_congr rfl hcast2, prod_congr rfl hcast1]
  have hfac : ∀ p ∈ S, (p : ℝ) - 2 ≤ ((p : ℝ) - 1) * Real.exp (-(1 / (p : ℝ))) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have he := Real.add_one_le_exp (-(1 / (p : ℝ)))
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    calc (p : ℝ) - 2 ≤ ((p : ℝ) - 1) * (-(1 / (p : ℝ)) + 1) := by
          field_simp; nlinarith
      _ ≤ ((p : ℝ) - 1) * Real.exp (-(1 / (p : ℝ))) := mul_le_mul_of_nonneg_left he hp1
  have hle : ∏ p ∈ S, ((p : ℝ) - 2) ≤ ∏ p ∈ S, (((p : ℝ) - 1) * Real.exp (-(1 / (p : ℝ)))) := by
    apply prod_le_prod₀
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
      linarith
    · exact hfac
  rw [prod_mul_distrib, ← Real.exp_sum, sum_neg_distrib] at hle
  have hexp : Real.exp (-∑ p ∈ S, 1 / (p : ℝ)) ≤ ε := by
    calc Real.exp (-∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.exp (Real.log ε) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ε := Real.exp_log hε
  have hnn : 0 ≤ ∏ p ∈ S, ((p : ℝ) - 1) := prod_nonneg fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    linarith
  calc ∏ p ∈ S, ((p : ℝ) - 2) ≤ (∏ p ∈ S, ((p : ℝ) - 1)) * Real.exp (-∑ p ∈ S, 1 / (p : ℝ)) := hle
    _ ≤ (∏ p ∈ S, ((p : ℝ) - 1)) * ε := mul_le_mul_of_nonneg_left hexp hnn
    _ = ε * ∏ p ∈ S, ((p : ℝ) - 1) := mul_comm _ _

end LeanLab.DensityGoldbach.AlsetriShaoLocal

