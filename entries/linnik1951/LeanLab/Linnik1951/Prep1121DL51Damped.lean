module

public import LeanLab.Linnik1951.Decomp520a

/-!
P0093 page 159 before display 5.3. Split of the open leaf damped_from_count_prep1121
of Prep1121MixedRepair520: the size N over ln N of the damped prime sum with doubled
decay, from a Chebyshev counting bound, by summation in blocks of length N. The prime
p lies in the block numbered p divided by N, carries weight at most exp of minus 2 k
there, and the primes up to k plus one times N number at most C times k plus one times
N over ln N.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset

/-- P0093 page 159 before display 5.3. The block weights k plus one times
exp of minus 2 k are summable. -/
theorem block_weight_summable_prep1121D :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp (-2 * (k : ℝ))) := by
  have hr : ‖Real.exp (-2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  have h := h1.add h0
  convert h using 1
  ext k
  rw [pow_one, ← Real.exp_nat_mul]
  have : (k : ℝ) * (-2) = -2 * k := by ring
  rw [this]
  ring

/-- P0093 page 159 before display 5.3. The block count of primes up to k plus one
times N is at most k plus one times N plus one. -/
theorem block_count_le_prep1121D (N k : ℕ) :
    (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ) ≤ ((k + 1) * N + 1 : ℕ) := by
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range _).le

/-- P0093 page 159 before display 5.3. The block terms exp of minus 2 k times the
prime count up to k plus one times N are summable. -/
theorem block_terms_summable_prep1121D (N : ℕ) :
    Summable (fun k : ℕ => Real.exp (-2 * (k : ℝ)) *
      (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ)) := by
  have hs := block_weight_summable_prep1121D.mul_left ((N : ℝ) + 1)
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hs
  intro k
  have hc := block_count_le_prep1121D N k
  push_cast at hc
  have he := (Real.exp_pos (-2 * (k : ℝ))).le
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc Real.exp (-2 * (k : ℝ)) * (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ)
      ≤ Real.exp (-2 * (k : ℝ)) * (((k : ℝ) + 1) * N + 1) := mul_le_mul_of_nonneg_left hc he
    _ ≤ ((N : ℝ) + 1) * (((k : ℝ) + 1) * Real.exp (-2 * (k : ℝ))) := by nlinarith [mul_nonneg hk he, mul_nonneg hN he, mul_nonneg (mul_nonneg hk hN) he]

/-- LEAF: P0093 page 159 before display 5.3, the block summation for a finite set
of primes. Grouping the primes of S by the block p divided by N, each carries weight
at most exp of minus 2 k, and the primes in block k are among the primes up to
k plus one times N. -/
theorem block_finite_le_prep1121D (N : ℕ) (hN : 1 ≤ N) (S : Finset Nat.Primes) :
    ∑ p ∈ S, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) ≤
      ∑' k : ℕ, Real.exp (-2 * (k : ℝ)) *
        (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ) := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set b : ℕ → ℝ := fun k => Real.exp (-2 * (k : ℝ)) *
    (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
  set T : Finset ℕ := S.map ⟨fun p : Nat.Primes => (p : ℕ), Nat.Primes.coe_nat_injective⟩ with hT
  have hST : ∑ p ∈ S, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) =
      ∑ u ∈ T, Real.exp (-(2 * (u : ℝ)) / N) := by
    rw [hT, Finset.sum_map]
    rfl
  rw [hST]
  have hmaps : ∀ u ∈ T, u / N ∈ range (T.sup id / N + 1) := by
    intro u hu
    rw [mem_range]
    have h1 : u ≤ T.sup id := Finset.le_sup (f := id) hu
    have h2 := Nat.div_le_div_right (c := N) h1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans ?_ ((block_terms_summable_prep1121D N).sum_le_tsum
    (range (T.sup id / N + 1)) (fun k _ => hb0 k))
  apply Finset.sum_le_sum
  intro k _
  have hsub : T.filter (fun u => u / N = k) ⊆ (Finset.range ((k + 1) * N + 1)).filter Nat.Prime := by
    intro u hu
    rw [mem_filter] at hu
    obtain ⟨huT, hk⟩ := hu
    rw [hT, Finset.mem_map] at huT
    obtain ⟨p, _, hp⟩ := huT
    rw [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have h := Nat.div_add_mod u N
      have hr := Nat.mod_lt u (show 0 < N by omega)
      rw [hk] at h
      rw [add_mul, one_mul]
      linarith
    · rw [← hp]
      exact p.property
  calc ∑ u ∈ T.filter (fun u => u / N = k), Real.exp (-(2 * (u : ℝ)) / N)
      ≤ ∑ u ∈ T.filter (fun u => u / N = k), Real.exp (-2 * (k : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [mem_filter] at hu
        apply Real.exp_le_exp.mpr
        have h1 : k * N ≤ u := by rw [← hu.2]; exact Nat.div_mul_le_self u N
        have h2 : (k : ℝ) * N ≤ u := by exact_mod_cast h1
        rw [div_le_iff₀ hNp]
        linarith
    _ = Real.exp (-2 * (k : ℝ)) * ((T.filter (fun u => u / N = k)).card : ℝ) := by
        rw [sum_const, nsmul_eq_mul]
        ring
    _ ≤ b k := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact_mod_cast Finset.card_le_card hsub

/-- P0093 page 159 before display 5.3, the block summation. The damped prime sum
with doubled decay is at most the block sum of exp of minus 2 k times the number
of primes up to k plus one times N. -/
theorem block_sum_le_prep1121D (N : ℕ) (hN : 1 ≤ N) :
    ∑' p : Nat.Primes, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) ≤
      ∑' k : ℕ, Real.exp (-2 * (k : ℝ)) *
        (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ) :=
  Real.tsum_le_of_sum_le (fun _ => (Real.exp_pos _).le) (block_finite_le_prep1121D N hN)

/-- P0093 page 159 before display 5.3. Each block count is at most C times k plus
one times N over ln N, from the counting bound at k plus one times N and the
monotonicity of the logarithm. -/
theorem block_count_chebyshev_prep1121D (C : ℝ) (hC : 0 < C)
    (hcount : ∀ x : ℕ, 2 ≤ x →
      (((Finset.range (x + 1)).filter Nat.Prime).card : ℝ) ≤ C * (x : ℝ) / Real.log x)
    (N k : ℕ) (hN : 2 ≤ N) :
    (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ) ≤
      C * (N : ℝ) / Real.log N * ((k : ℝ) + 1) := by
  have hx : 2 ≤ (k + 1) * N := le_trans hN (Nat.le_mul_of_pos_left N (Nat.succ_pos k))
  have h := hcount _ hx
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hxN : (N : ℝ) ≤ ((k + 1) * N : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_left N (Nat.succ_pos k)
  have hlog : Real.log N ≤ Real.log ((k + 1) * N : ℕ) :=
    Real.log_le_log (by linarith) hxN
  refine h.trans ?_
  have hpos : (0 : ℝ) ≤ C * (((k + 1) * N : ℕ) : ℝ) := by positivity
  calc C * (((k + 1) * N : ℕ) : ℝ) / Real.log ((k + 1) * N : ℕ)
      ≤ C * (((k + 1) * N : ℕ) : ℝ) / Real.log N := div_le_div_of_nonneg_left hpos hlogN hlog
    _ = C * (N : ℝ) / Real.log N * ((k : ℝ) + 1) := by push_cast; ring

/-- P0093 page 159 before display 5.3. Exact statement of the parent leaf
damped_from_count_prep1121. -/
theorem damped_from_count_prep1121D (C : ℝ) (hC : 0 < C)
    (hcount : ∀ x : ℕ, 2 ≤ x →
      (((Finset.range (x + 1)).filter Nat.Prime).card : ℝ) ≤ C * (x : ℝ) / Real.log x) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∑' p : Nat.Primes, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) ≤
        C' * (N : ℝ) / Real.log N := by
  set K := ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp (-2 * (k : ℝ)) with hK
  have hK1 : 1 ≤ K := by
    have h : (((0 : ℕ) : ℝ) + 1) * Real.exp (-2 * ((0 : ℕ) : ℝ)) ≤ K :=
      block_weight_summable_prep1121D.le_tsum 0 (fun k _ => by positivity)
    rw [Nat.cast_zero, zero_add, one_mul, mul_zero, Real.exp_zero] at h
    exact h
  refine ⟨C * K, by positivity, 1, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  refine (block_sum_le_prep1121D N (by omega)).trans ?_
  have hA : 0 ≤ C * (N : ℝ) / Real.log N := by positivity
  have hle : ∀ k : ℕ, Real.exp (-2 * (k : ℝ)) *
      (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ) ≤
        C * (N : ℝ) / Real.log N * (((k : ℝ) + 1) * Real.exp (-2 * (k : ℝ))) := by
    intro k
    have h := block_count_chebyshev_prep1121D C hC hcount N k hN2
    have he := (Real.exp_pos (-2 * (k : ℝ))).le
    calc Real.exp (-2 * (k : ℝ)) *
        (((Finset.range ((k + 1) * N + 1)).filter Nat.Prime).card : ℝ)
        ≤ Real.exp (-2 * (k : ℝ)) * (C * (N : ℝ) / Real.log N * ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h he
      _ = _ := by ring
  refine (Summable.tsum_le_tsum hle (block_terms_summable_prep1121D N)
    (block_weight_summable_prep1121D.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, ← hK]
  ring

end LeanLab.Linnik1951
