module

public import Mathlib

/-!
I-5230, unit U-6601, CLOUD 20261020T1618Z-cloud46: prime powers `p^k`, `k ≥ 2`, in a window.

`sum_nonprime_le`: for naturals `A ≤ B`, the von Mangoldt mass of the non-prime `n ∈ (A, B]` is
at most `Σ_{2 ≤ k ≤ log₂ B} (log B / k) · #{m : A < m^k ≤ B}`, since such an `n` is `p^k`
with `k ≥ 2`, `Λ(n) = log p ≤ log B / k`, and `n ↦ p` is injective for fixed `k`.
`count_le`: `#{m : ⌊a⌋ < m^k ≤ ⌊b⌋} ≤ b^{1/k} - a^{1/k} + 1` for `0 ≤ a ≤ b`.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.PrimePowerWindow
open Real Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The exponent of a prime power. -/
def ex (n : ℕ) : ℕ := n.factorization n.minFac

lemma pow_ex {n : ℕ} (hn : IsPrimePow n) : n.minFac ^ ex n = n :=
  hn.minFac_pow_factorization_eq

lemma minFac_prime_of {n : ℕ} (hn : IsPrimePow n) : n.minFac.Prime :=
  Nat.minFac_prime hn.ne_one

lemma two_le_ex {n : ℕ} (hn : IsPrimePow n) (hnp : ¬ n.Prime) : 2 ≤ ex n := by
  have h := pow_ex hn
  by_contra hlt
  push_neg at hlt
  interval_cases hk : ex n
  · rw [pow_zero] at h; exact hn.ne_one h.symm
  · rw [pow_one] at h; exact hnp (h ▸ minFac_prime_of hn)

/-- **The prime power mass of the non-primes in `(A, B]`.** -/
theorem sum_nonprime_le (A B : ℕ) :
    ∑ n ∈ (Ioc A B).filter (fun n => ¬ n.Prime), Λ n ≤
      ∑ k ∈ Icc 2 (Nat.log 2 B), (Real.log B / k) *
        (((Iic B).filter (fun m => A < m ^ k ∧ m ^ k ≤ B)).card : ℝ) := by
  classical
  set S := (Ioc A B).filter (fun n => ¬ n.Prime) with hS
  set T := S.filter IsPrimePow with hT
  -- only prime powers carry mass
  have h1 : ∑ n ∈ S, Λ n = ∑ n ∈ T, Λ n := by
    rw [hT]
    refine (sum_filter_of_ne fun n _ h => ?_).symm
    by_contra hp
    exact h (by rw [ArithmeticFunction.vonMangoldt_apply, if_neg hp])
  -- facts on T
  have hTfacts : ∀ n ∈ T, IsPrimePow n ∧ ¬ n.Prime ∧ A < n ∧ n ≤ B := by
    intro n hn
    rw [hT, mem_filter, hS, mem_filter, mem_Ioc] at hn
    exact ⟨hn.2, hn.1.2, hn.1.1.1, hn.1.1.2⟩
  have hBpos : ∀ n ∈ T, (0 : ℝ) < B := by
    intro n hn
    obtain ⟨hpp, -, -, hnB⟩ := hTfacts n hn
    have : 0 < n := hpp.pos
    exact_mod_cast lt_of_lt_of_le this hnB
  -- pointwise: Λ n ≤ log B / ex n
  have h2 : ∀ n ∈ T, Λ n ≤ Real.log B / ex n := by
    intro n hn
    obtain ⟨hpp, hnp, -, hnB⟩ := hTfacts n hn
    have hk := two_le_ex hpp hnp
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp, le_div_iff₀ (by positivity)]
    have hp := minFac_prime_of hpp
    have hpos : (0 : ℝ) < n.minFac := by exact_mod_cast hp.pos
    have e : Real.log (n.minFac) * (ex n : ℝ) = Real.log n := by
      conv_rhs => rw [← pow_ex hpp]
      rw [Nat.cast_pow, Real.log_pow]; ring
    rw [e]
    apply Real.log_le_log (by exact_mod_cast hpp.pos)
    exact_mod_cast hnB
  have hmaps : ∀ n ∈ T, ex n ∈ Icc 2 (Nat.log 2 B) := by
    intro n hn
    obtain ⟨hpp, hnp, -, hnB⟩ := hTfacts n hn
    rw [mem_Icc]
    refine ⟨two_le_ex hpp hnp, Nat.le_log_of_pow_le (by norm_num) ?_⟩
    calc 2 ^ ex n ≤ n.minFac ^ ex n := Nat.pow_le_pow_left (minFac_prime_of hpp).two_le _
      _ = n := pow_ex hpp
      _ ≤ B := hnB
  rw [h1]
  calc ∑ n ∈ T, Λ n ≤ ∑ n ∈ T, Real.log B / ex n := sum_le_sum h2
    _ = ∑ k ∈ Icc 2 (Nat.log 2 B), ∑ n ∈ T with ex n = k, Real.log B / ex n :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ _ := by
        refine sum_le_sum fun k hk => ?_
        have hc : ∑ n ∈ T with ex n = k, Real.log B / ex n =
            (Real.log B / k) * ((T.filter (fun n => ex n = k)).card : ℝ) := by
          rw [sum_congr rfl (fun n hn => by rw [(mem_filter.1 hn).2]), sum_const, nsmul_eq_mul]
          ring
        rw [hc]
        have hlogB : 0 ≤ Real.log B / k := by
          apply div_nonneg _ (Nat.cast_nonneg _)
          rcases Nat.eq_zero_or_pos B with h0 | h0
          · rw [h0]; simp
          · exact Real.log_nonneg (by exact_mod_cast h0)
        apply mul_le_mul_of_nonneg_left _ hlogB
        have : (T.filter (fun n => ex n = k)).card ≤
            ((Iic B).filter (fun m => A < m ^ k ∧ m ^ k ≤ B)).card := by
          apply card_le_card_of_injOn (fun n => n.minFac)
          · intro n hn
            rw [mem_coe, mem_filter] at hn
            obtain ⟨hpp, -, hAn, hnB⟩ := hTfacts n hn.1
            have he : n.minFac ^ k = n := hn.2 ▸ pow_ex hpp
            rw [mem_coe, mem_filter, mem_Iic, he]
            exact ⟨(Nat.minFac_le hpp.pos).trans hnB, hAn, hnB⟩
          · intro n hn m hm hnm
            rw [mem_coe, mem_filter] at hn hm
            have hen : n.minFac ^ k = n := hn.2 ▸ pow_ex (hTfacts n hn.1).1
            have hem : m.minFac ^ k = m := hm.2 ▸ pow_ex (hTfacts m hm.1).1
            simp only at hnm
            rw [← hen, ← hem, hnm]
        exact_mod_cast this

/-- **Counting `k`-th powers in a window.** For `0 ≤ a ≤ b` and `k ≥ 1`,
`#{m ≤ ⌊b⌋ : ⌊a⌋ < m^k ≤ ⌊b⌋} ≤ b^{1/k} - a^{1/k} + 1`. -/
theorem count_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {k : ℕ} (hk : 1 ≤ k) :
    ((((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℕ) : ℝ) ≤
      b ^ (1 / (k : ℝ)) - a ^ (1 / (k : ℝ)) + 1 := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set u := a ^ (1 / (k : ℝ)) with hu
  set v := b ^ (1 / (k : ℝ)) with hv
  have hu0 : 0 ≤ u := Real.rpow_nonneg ha _
  have hv0 : 0 ≤ v := Real.rpow_nonneg hb _
  have hsub : (Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊) ⊆ Ioc ⌊u⌋₊ ⌊v⌋₊ := by
    intro m hm
    rw [mem_filter] at hm
    obtain ⟨-, h1, h2⟩ := hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    -- m^k > a, so m > u
    have h1r : a < (m : ℝ) ^ k := by
      have := Nat.lt_floor_add_one a
      have h1' : (⌊a⌋₊ : ℝ) + 1 ≤ ((m ^ k : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'; linarith
    have h2r : (m : ℝ) ^ k ≤ b := by
      have : ((m ^ k : ℕ) : ℝ) ≤ ⌊b⌋₊ := by exact_mod_cast h2
      push_cast at this; exact this.trans (Nat.floor_le hb)
    have hmu : u < m := by
      rw [hu]
      have e : (m : ℝ) = ((m : ℝ) ^ k) ^ (1 / (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hm0, mul_one_div_cancel hkpos.ne', Real.rpow_one]
      rw [e]
      exact Real.rpow_lt_rpow ha h1r (by positivity)
    have hmv : (m : ℝ) ≤ v := by
      rw [hv]
      have e : (m : ℝ) = ((m : ℝ) ^ k) ^ (1 / (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hm0, mul_one_div_cancel hkpos.ne', Real.rpow_one]
      rw [e]
      exact Real.rpow_le_rpow (by positivity) h2r (by positivity)
    rw [mem_Ioc]
    constructor
    · exact (Nat.floor_lt hu0).2 hmu
    · exact Nat.le_floor hmv
  have hc := card_le_card hsub
  rw [Nat.card_Ioc] at hc
  have hc' : ((((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℕ) : ℝ) ≤
      ((⌊v⌋₊ - ⌊u⌋₊ : ℕ) : ℝ) := by exact_mod_cast hc
  refine hc'.trans ?_
  have hfv : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0
  have hfu : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  rcases le_or_gt ⌊u⌋₊ ⌊v⌋₊ with h | h
  · rw [Nat.cast_sub h]; linarith
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    have : u ≤ v := Real.rpow_le_rpow ha hab (by positivity)
    linarith

/-- With the window under one `k`-th power step, at most one `k`-th power lies in it. -/
theorem count_le_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {k : ℕ} (hk : 1 ≤ k)
    (hstep : b ^ (1 / (k : ℝ)) < a ^ (1 / (k : ℝ)) + 1) :
    ((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card ≤ 1 := by
  have h := count_le ha hab hk
  have : ((((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℕ) : ℝ) < 2 := by
    linarith
  exact Nat.lt_succ_iff.1 (by exact_mod_cast this)

/-- `r ↦ b^r - a^r` is monotone for `1 ≤ a ≤ b`. -/
theorem rpow_sub_mono {a b r s : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hr : 0 ≤ r) (hrs : r ≤ s) :
    b ^ r - a ^ r ≤ b ^ s - a ^ s := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hbr : a ^ r ≤ b ^ r := Real.rpow_le_rpow ha0.le hab hr
  have har : 0 ≤ a ^ r := Real.rpow_nonneg ha0.le _
  have hsr : 0 ≤ s - r := by linarith
  have h1a : 1 ≤ a ^ (s - r) := Real.one_le_rpow ha hsr
  have hab' : a ^ (s - r) ≤ b ^ (s - r) := Real.rpow_le_rpow ha0.le hab hsr
  have ea : a ^ s = a ^ r * a ^ (s - r) := by
    rw [← Real.rpow_add ha0]; ring_nf
  have eb : b ^ s = b ^ r * b ^ (s - r) := by
    rw [← Real.rpow_add hb0]; ring_nf
  rw [ea, eb]
  nlinarith [mul_le_mul_of_nonneg_left hab' (le_trans har hbr)]

end LeanLab.PrimePowerWindow

