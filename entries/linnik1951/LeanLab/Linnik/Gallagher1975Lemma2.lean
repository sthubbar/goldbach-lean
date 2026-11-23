module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975Lemma1

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142, Lemma 2, p.132-133,
for g = 2, its counting core, read from the page images of papers/P0094.pdf, PDF pages 9, 10.
Unit U-6824, CLOUD 20261021T0217Z-cloud56. AI-written Lean code, Claude, 2026-10-21.
Checked only by the Lean kernel. Binary Goldbach is OPEN.

The page: the set of `α ∈ (0, 1]` with `|G(α)| ≥ (1-η)L` has measure `≪ N^{ε-1}`,
`ε = Cη log(e/η)`. Proof: by Lemma 1 the measure is at most `g^{-L}` times the number of
digit strings with few changes, then a binomial estimate.

* `measure_le_card`: PROVED, the first step for g = 2 with Lemma 1's constant 4: the set of
  `α ∈ [0, 1)` with `(1-η)L ≤ |G(α)|` has measure at most `#T / 2^{L+1}`, `T` the `n < 2^{L+1}`
  whose binary digits, read as `a_1, ..., a_{L+1}`, change at most `4ηL` times in `[2, L]`.
  The paper's `(0, 1]` and our `[0, 1)` differ by two points, measure zero.
* `card_T_le`: PROVED, `#T ≤ 4 · #{S ⊆ [2, L] : #S ≤ 4ηL}`, the strings counted by their
  first two digits and change set, the paper's `2 (L choose m)` count.
* `card_small_subsets_le`: PROVED, the binomial estimate, subsets of size at most `x` of an
  `n`-set number at most `(e n / x)^x`, for `0 < x ≤ n`.
* `lemma2_explicit`: PROVED, for `0 < 4ηL ≤ L - 1` the measure is at most
  `4 (e (L-1) / (4ηL))^{4ηL} / 2^{L+1}`.
* `lemma2`: PROVED, the paper's form with explicit constants: for `N ≥ 2`, `L = [log₂ N]`,
  `0 < 4ηL ≤ L - 1`, `η ≤ 1/4`, the measure is at most `4 N^{ε-1}`,
  `ε = (4 / log 2) η log(e/η)`, so `C = 4 / log 2`. The paper assumes `η` small and `N` large.
-/

@[expose] public section

open Finset MeasureTheory

noncomputable section
namespace LeanLab.Linnik.Gallagher1975Lemma1

/-- The `μ`-th binary digit of `n`, reading `n < 2^K` as `a_1 ... a_K`, `a_1` the top digit. -/
def bit (K n μ : ℕ) : ℕ := n / 2 ^ (K - μ) % 2

/-- The changes `a_m ≠ a_{m+1}`, `m ∈ [2, L]`, of the digit string of `n`, `K = L + 1`. -/
def bitChanges (L n : ℕ) : Finset ℕ := {m ∈ Icc 2 L | bit (L + 1) n m ≠ bit (L + 1) n (m + 1)}

/-- `T`: the `n < 2^{L+1}` with at most `4ηL` changes. -/
def T (L : ℕ) (η : ℝ) : Finset ℕ := {n ∈ range (2 ^ (L + 1)) | (#(bitChanges L n) : ℝ) ≤ 4 * η * L}

/-- The set of Lemma 2, on `[0, 1)`. -/
def bigSet (L : ℕ) (η : ℝ) : Set ℝ := {α | α ∈ Set.Ico 0 1 ∧ (1 - η) * L ≤ ‖G L α‖}

/-- For `μ ≤ K`, the digit `a_μ` of `α` is the `μ`-th digit of `n = ⌊2^K α⌋`. -/
theorem digit_eq_bit {α : ℝ} {K μ : ℕ} (hμ : μ ≤ K) (hα : 0 ≤ α) :
    digit α μ = (bit K ⌊(2 : ℝ) ^ K * α⌋₊ μ : ℤ) := by
  have h1 : (2 : ℝ) ^ μ * α = (2 : ℝ) ^ K * α / ((2 ^ (K - μ) : ℕ) : ℝ) := by
    push_cast
    rw [show K = μ + (K - μ) by omega, pow_add]
    field_simp
    simp
  unfold digit bit
  rw [h1, Int.floor_div_natCast, ← Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  rfl

theorem changes_eq_bitChanges {α : ℝ} {L : ℕ} (hα : 0 ≤ α) :
    changes α L = bitChanges L ⌊(2 : ℝ) ^ (L + 1) * α⌋₊ := by
  ext m
  simp only [changes, bitChanges, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hm, hne⟩
    refine ⟨hm, fun h => hne ?_⟩
    rw [digit_eq_bit (K := L + 1) (by omega) hα, digit_eq_bit (K := L + 1) (by omega) hα, h]
  · rintro ⟨hm, hne⟩
    refine ⟨hm, fun h => hne ?_⟩
    rw [digit_eq_bit (K := L + 1) (by omega) hα, digit_eq_bit (K := L + 1) (by omega) hα] at h
    exact_mod_cast h

/-- **Lemma 2, first step, g = 2**, PROVED: `meas{α ∈ [0,1) : |G(α)| ≥ (1-η)L} ≤ #T / 2^{L+1}`. -/
theorem measure_le_card (L : ℕ) (η : ℝ) :
    volume (bigSet L η) ≤ (#(T L η) : ENNReal) * ENNReal.ofReal (1 / 2 ^ (L + 1)) := by
  set K := L + 1
  have hsub : bigSet L η ⊆ ⋃ n ∈ T L η, Set.Ico ((n : ℝ) / 2 ^ K) ((n + 1) / 2 ^ K) := by
    intro α ⟨⟨h0, h1⟩, hG⟩
    set n := ⌊(2 : ℝ) ^ K * α⌋₊
    have hK : (0 : ℝ) < 2 ^ K := by positivity
    have hx0 : 0 ≤ (2 : ℝ) ^ K * α := by positivity
    have hn1 : (n : ℝ) ≤ 2 ^ K * α := Nat.floor_le hx0
    have hn2 : 2 ^ K * α < n + 1 := Nat.lt_floor_add_one _
    simp only [Set.mem_iUnion, Set.mem_Ico]
    refine ⟨n, ?_, ?_, ?_⟩
    · simp only [T, mem_filter, mem_range]
      refine ⟨?_, ?_⟩
      · have : (n : ℝ) < 2 ^ K := by nlinarith
        exact_mod_cast this
      · rw [← changes_eq_bitChanges h0]; exact lemma1 α η L hG
    · rw [div_le_iff₀ hK]; linarith
    · rw [lt_div_iff₀ hK]; linarith
  calc volume (bigSet L η)
      ≤ volume (⋃ n ∈ T L η, Set.Ico ((n : ℝ) / 2 ^ K) ((n + 1) / 2 ^ K)) := measure_mono hsub
    _ ≤ ∑ n ∈ T L η, volume (Set.Ico ((n : ℝ) / 2 ^ K) ((n + 1) / 2 ^ K)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _n ∈ T L η, ENNReal.ofReal (1 / 2 ^ K) := by
        apply sum_congr rfl
        intro n _
        rw [Real.volume_Ico]
        congr 1
        ring
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- Same digits `a_1, ..., a_K` give the same `n < 2^K`. -/
theorem eq_of_bits {K n n' : ℕ} (hn : n < 2 ^ K) (hn' : n' < 2 ^ K)
    (h : ∀ μ, 1 ≤ μ → μ ≤ K → bit K n μ = bit K n' μ) : n = n' := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < K
  · have := h (K - j) (by omega) (by omega)
    simp only [bit, show K - (K - j) = j by omega] at this
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, this]
  · push Not at hj
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hj)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn' (Nat.pow_le_pow_right (by norm_num) hj))]

theorem bit_lt_two (K n μ : ℕ) : bit K n μ < 2 := Nat.mod_lt _ (by norm_num)

/-- Same digit `a_2` and same change set give the same digits `a_2, ..., a_{L+1}`. -/
theorem bits_eq_of_changes {L n n' : ℕ} (h2 : bit (L + 1) n 2 = bit (L + 1) n' 2)
    (hc : bitChanges L n = bitChanges L n') :
    ∀ j, j ≤ L - 1 → bit (L + 1) n (2 + j) = bit (L + 1) n' (2 + j) := by
  intro j
  induction j with
  | zero => intro _; simpa using h2
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hm : 2 + j ∈ Icc 2 L := by simp only [mem_Icc]; omega
    have hiff : (2 + j ∈ bitChanges L n) ↔ (2 + j ∈ bitChanges L n') := by rw [hc]
    simp only [bitChanges, mem_filter, hm, true_and] at hiff
    rw [show 2 + (j + 1) = 2 + j + 1 by ring]
    have a1 := bit_lt_two (L + 1) n (2 + j + 1)
    have a2 := bit_lt_two (L + 1) n' (2 + j + 1)
    have a3 := bit_lt_two (L + 1) n (2 + j)
    omega

/-- **The count of Lemma 2's proof, g = 2**, PROVED: `#T ≤ 4 · #{S ⊆ [2, L], #S ≤ 4ηL}`. -/
theorem card_T_le (L : ℕ) (η : ℝ) :
    #(T L η) ≤ 4 * #{S ∈ (Icc 2 L).powerset | (#S : ℝ) ≤ 4 * η * L} := by
  classical
  set P := {S ∈ (Icc 2 L).powerset | (#S : ℝ) ≤ 4 * η * L}
  have h : #(T L η) ≤ #(range 2 ×ˢ range 2 ×ˢ P) := by
    apply card_le_card_of_injOn (fun n => (bit (L + 1) n 1, bit (L + 1) n 2, bitChanges L n))
    · intro n hn
      simp only [T, coe_filter, mem_range, Set.mem_ofPred_eq] at hn
      simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio, P, coe_filter,
        mem_powerset, Set.mem_ofPred_eq]
      exact ⟨bit_lt_two _ _ _, bit_lt_two _ _ _, filter_subset _ _, hn.2⟩
    · intro n hn n' hn' heq
      simp only [T, coe_filter, mem_range, Set.mem_ofPred_eq] at hn hn'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2, hc⟩ := heq
      have hb := bits_eq_of_changes h2 hc
      apply eq_of_bits hn.1 hn'.1
      intro μ hμ1 hμK
      by_cases hμ : μ = 1
      · rw [hμ]; exact h1
      · have := hb (μ - 2) (by omega)
        rwa [show 2 + (μ - 2) = μ by omega] at this
  rw [card_product, card_product, card_range] at h
  linarith

/-- Vacuity: `n = 0`, all digits 0, lies in `T L η` for every `η ≥ 0`. -/
theorem zero_mem_T (L : ℕ) {η : ℝ} (hη : 0 ≤ η) : 0 ∈ T L η := by
  simp only [T, mem_filter, mem_range]
  refine ⟨by positivity, ?_⟩
  have : bitChanges L 0 = ∅ := by
    ext m; simp [bitChanges, bit]
  rw [this, card_empty, Nat.cast_zero]
  positivity

/-- The binomial estimate: for `0 < x ≤ #s`, the subsets of `s` of size at most `x` number
at most `(e #s / x)^x`, by `t^{-x} (1 + t)^{#s}` at `t = x / #s`. -/
theorem card_small_subsets_le (s : Finset ℕ) {x : ℝ} (hx : 0 < x) (hxn : x ≤ #s) :
    (#{S ∈ s.powerset | (#S : ℝ) ≤ x} : ℝ) ≤ (Real.exp 1 * #s / x) ^ x := by
  set n : ℝ := ((#s : ℕ) : ℝ) with hn
  have hn0 : 0 < n := lt_of_lt_of_le hx hxn
  set t := x / n with ht
  have ht0 : 0 < t := div_pos hx hn0
  have ht1 : t ≤ 1 := (div_le_one hn0).2 hxn
  have hterm : ∀ S ∈ {S ∈ s.powerset | (#S : ℝ) ≤ x}, (1 : ℝ) ≤ t ^ (#S : ℕ) * t ^ (-x) := by
    intro S hS
    simp only [mem_filter] at hS
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith [hS.2])
  calc (#{S ∈ s.powerset | (#S : ℝ) ≤ x} : ℝ)
      = ∑ _S ∈ {S ∈ s.powerset | (#S : ℝ) ≤ x}, (1 : ℝ) := by simp
    _ ≤ ∑ S ∈ {S ∈ s.powerset | (#S : ℝ) ≤ x}, t ^ (#S : ℕ) * t ^ (-x) := sum_le_sum hterm
    _ ≤ ∑ S ∈ s.powerset, t ^ (#S : ℕ) * t ^ (-x) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (1 + t) ^ #s * t ^ (-x) := by
        rw [← sum_mul, add_comm, ← sum_pow_mul_eq_add_pow t 1 s]
        simp
    _ ≤ Real.exp x * t ^ (-x) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (1 + t) ^ #s ≤ Real.exp t ^ #s :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) _
          _ = Real.exp x := by
              rw [← Real.exp_nat_mul, ← hn, ht]; congr 1; field_simp
    _ = (Real.exp 1 * n / x) ^ x := by
        rw [← Real.exp_one_rpow, Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le,
          ← Real.mul_rpow (by positivity) (by positivity), ht]
        congr 1
        field_simp

/-- **Gallagher 1975, Lemma 2, g = 2, explicit form**, PROVED: for `0 < 4ηL ≤ L - 1`,
`meas{α ∈ [0,1) : |G(α)| ≥ (1-η)L} ≤ 4 (e (L-1) / (4ηL))^{4ηL} / 2^{L+1}`.
With `M = 4ηL` this is `2^{-L} exp(M log(e L / M)) · 2`, the paper's
`g^{-L} exp(L (2 (M/L) log(L/M) + C₃ M/L))`, so `≪ N^{ε-1}`, `ε = C η log(e/η)`. -/
theorem lemma2_explicit (L : ℕ) (η : ℝ) (hη : 0 < 4 * η * L) (hηL : 4 * η * L ≤ (L - 1 : ℕ)) :
    volume (bigSet L η) ≤
      ENNReal.ofReal (4 * (Real.exp 1 * (L - 1 : ℕ) / (4 * η * L)) ^ (4 * η * L) / 2 ^ (L + 1)) := by
  have h1 := measure_le_card L η
  have h2 := card_T_le L η
  have hcard : #(Icc 2 L) = L - 1 := by simp
  have h3 := card_small_subsets_le (Icc 2 L) hη (by rw [hcard]; exact hηL)
  rw [hcard] at h3
  have h2r : (#(T L η) : ℝ) ≤ 4 * (Real.exp 1 * (L - 1 : ℕ) / (4 * η * L)) ^ (4 * η * L) := by
    have : (#(T L η) : ℝ) ≤ 4 * (#{S ∈ (Icc 2 L).powerset | (#S : ℝ) ≤ 4 * η * L} : ℝ) := by
      exact_mod_cast h2
    linarith
  refine h1.trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right h2r (by positivity)

/-- **Gallagher 1975, Lemma 2, g = 2, in the paper's form**, PROVED: for `N ≥ 2`,
`L = [log₂ N]`, `0 < 4ηL ≤ L - 1` and `η ≤ 1/4`, the `α ∈ [0, 1)` with
`|G(α)| ≥ (1-η)L` have measure at most `4 N^{ε-1}`, `ε = (4 / log 2) η log(e/η)`. -/
theorem lemma2 (N : ℕ) (hN : 2 ≤ N) (η : ℝ) (hη : 0 < 4 * η * (Nat.log 2 N : ℕ))
    (hηL : 4 * η * (Nat.log 2 N : ℕ) ≤ (Nat.log 2 N - 1 : ℕ)) (hη4 : η ≤ 1 / 4) :
    volume (bigSet (Nat.log 2 N) η) ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ (4 / Real.log 2 * η * Real.log (Real.exp 1 / η) - 1)) := by
  set L := Nat.log 2 N with hLdef
  refine (lemma2_explicit L η hη hηL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : (0 : ℝ) < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h] at hη; simp at hη
    · exact_mod_cast h
  have hηpos : 0 < η := by
    by_contra h; push Not at h; nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := Real.exp_one_gt_d9
  set x := 4 * η * (L : ℝ) with hx
  have hx0 : 0 < x := hη
  -- the base: e (L-1) / (4ηL) ≤ e / η
  have hLm : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
  have hbase0 : 0 ≤ Real.exp 1 * ((L - 1 : ℕ) : ℝ) / x := by positivity
  have hbase : Real.exp 1 * ((L - 1 : ℕ) : ℝ) / x ≤ Real.exp 1 / η := by
    rw [div_le_div_iff₀ hx0 hηpos, hx]
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    have hA : Real.exp 1 * η * ((L - 1 : ℕ) : ℝ) ≤ Real.exp 1 * η * L :=
      mul_le_mul_of_nonneg_left hLm (by positivity)
    have hB : 0 < Real.exp 1 * η * (L : ℝ) := by positivity
    linarith
  have h1 : (Real.exp 1 * ((L - 1 : ℕ) : ℝ) / x) ^ x ≤ (Real.exp 1 / η) ^ x :=
    Real.rpow_le_rpow hbase0 hbase hx0.le
  -- (e/η)^x = exp(x log(e/η)) ≤ N^ε
  have hel : 0 ≤ Real.log (Real.exp 1 / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hηpos]; linarith
  have hLlog : (L : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  set ε := 4 / Real.log 2 * η * Real.log (Real.exp 1 / η) with hε
  have hε0 : 0 ≤ ε := by positivity
  have h2 : (Real.exp 1 / η) ^ x ≤ (N : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hN0]
    apply Real.exp_le_exp.2
    have : x * Real.log (Real.exp 1 / η) = ε * ((L : ℝ) * Real.log 2) := by
      rw [hε, hx]; field_simp
    rw [mul_comm (Real.log (Real.exp 1 / η)), this, mul_comm (Real.log (N : ℝ))]
    exact mul_le_mul_of_nonneg_left hLlog hε0
  -- 2^{L+1} > N
  have h3 : (N : ℝ) < 2 ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hNe : (N : ℝ) ^ ε > 0 := by positivity
  calc 4 * (Real.exp 1 * ((L - 1 : ℕ) : ℝ) / x) ^ x / 2 ^ (L + 1)
      ≤ 4 * (N : ℝ) ^ ε / 2 ^ (L + 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
    _ ≤ 4 * (N : ℝ) ^ ε / N := by
        apply div_le_div_of_nonneg_left (by positivity) hN0 h3.le
    _ = 4 * (N : ℝ) ^ (ε - 1) := by
        rw [Real.rpow_sub_one hN0.ne']; ring

end LeanLab.Linnik.Gallagher1975Lemma1

