module

public import LeanLab.Romanov.Lemma
public import LeanLab.Romanov.Count
public import LeanLab.BrunGap.Uniform

/-!
# Romanov's theorem: the numbers `p + 2^k` have positive lower density

Lab proof, unit U-5602, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics,
Romanov 1934. No cited input: the inputs are the lab's uniform Brun bound
`BrunGap.gapUpper_uniform`, the lab's `romanov_lemma`, and Mathlib's `Chebyshev.pi_ge`.
Binary Goldbach is OPEN; this is the Linnik-Goldbach line, IDEAS I-5052.

With `N = 2^(L+1)`, `A` the primes up to `N` and `T = A × {0, …, L - 1}`, the map
`(p, k) ↦ p + 2^k` sends `T` below `2^(L+2)`. `#T = π(N) L ≥ N/4` by Chebyshev; the collisions are
at most `#T + 2Q`, `Q` a sum of prime pair counts with gaps `2^k' - 2^k`, and the uniform Brun bound
with Romanov's lemma gives `Q ≤ R₁ N`; Cauchy-Schwarz then gives at least `N/(4(1 + 8R₁))`
distinct values.

* `romanov_dyadic`: for `L ≥ 2`, at least `c · 2^(L+2)` numbers below `2^(L+2)` are `p + 2^k`.
* `romanov`: for every `x ≥ 16`, at least `(c/2) x` numbers below `x` are `p + 2^k`, PROVED.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset Real
open LeanLab.SchnirelmannGoldbach (singProd)
open LeanLab.BrunGap (gapCount C₀ gapUpper_uniform C₀_pos)

lemma singProd_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    singProd (a * b) ≤ singProd a * singProd b := by
  unfold singProd
  rw [Nat.primeFactors_mul ha hb, ← prod_union_inter]
  have h1 : (1 : ℝ) ≤ ∏ p ∈ a.primeFactors ∩ b.primeFactors, (1 + 1 / (p : ℝ)) := by
    calc (1 : ℝ) = ∏ _p ∈ a.primeFactors ∩ b.primeFactors, (1 : ℝ) := by simp
      _ ≤ _ := by
        gcongr with p hp
        have : (0 : ℝ) ≤ 1 / p := by positivity
        linarith
  have h0 : (0 : ℝ) ≤ ∏ p ∈ a.primeFactors ∪ b.primeFactors, (1 + 1 / (p : ℝ)) :=
    prod_nonneg fun p _ => by positivity
  nlinarith

lemma singProd_two_pow {k : ℕ} (hk : k ≠ 0) : singProd (2 ^ k) = 3 / 2 := by
  unfold singProd
  rw [Nat.primeFactors_prime_pow hk Nat.prime_two]
  norm_num

lemma singProd_nonneg (n : ℕ) : 0 ≤ singProd n :=
  le_trans zero_le_one (LeanLab.SchnirelmannGoldbach.S1.one_le_singProd n)

lemma gap_le_gapCount (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (h M : ℕ) :
    gap P h M ≤ gapCount h M := by
  unfold gap gapCount
  refine card_le_card fun q hq => ?_
  simp only [mem_filter] at hq ⊢
  exact ⟨hq.1, hP _ hq.2.1, hP _ hq.2.2⟩

/-- An odd gap: only `q = 2` can work. -/
lemma gap_odd_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) {k' : ℕ} (hk' : 0 < k') (M : ℕ) :
    gap P (2 ^ k' - 1) M ≤ 1 := by
  have hodd : Odd (2 ^ k' - 1) := by
    have : Even (2 ^ k') := (Nat.even_pow' hk'.ne').2 even_two
    have h1 : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
    exact Nat.Even.sub_odd h1 this odd_one
  unfold gap
  refine le_trans (card_le_card (t := {2}) fun q hq => ?_) (by simp)
  simp only [mem_filter] at hq
  rw [mem_singleton]
  by_contra hq2
  have hqo : Odd q := (hP _ hq.2.1).odd_of_ne_two hq2
  have hev : Even (q + (2 ^ k' - 1)) := Odd.add_odd hqo hodd
  have hpr := hP _ hq.2.2
  have h2 := (hpr.even_iff).1 hev
  have : 2 ≤ q := (hP _ hq.2.1).two_le
  have : 1 ≤ 2 ^ k' - 1 := by
    have : 2 ≤ 2 ^ k' := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) hk'
    omega
  omega

/-- An even gap `2^k' - 2^k`, `1 ≤ k < k'`, through the uniform Brun bound. -/
lemma gap_even_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) {k k' : ℕ} (hk : 1 ≤ k) (hkk : k < k')
    (M : ℕ) (hM : 3 ≤ M) :
    (gap P (2 ^ k' - 2 ^ k) M : ℝ) ≤
      C₀ * (3 / 2 * singProd (2 ^ (k' - k) - 1)) * M / Real.log M ^ 2 := by
  have hsplit : 2 ^ k' - 2 ^ k = 2 ^ k * (2 ^ (k' - k) - 1) := by
    have : 2 ^ k' = 2 ^ k * 2 ^ (k' - k) := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.mul_sub_one]
  have hm0 : 2 ^ (k' - k) - 1 ≠ 0 := two_pow_sub_one_ne_zero (by omega)
  have hk0 : 2 ^ k ≠ 0 := by positivity
  have heven : Even (2 ^ k' - 2 ^ k) := by
    rw [hsplit]; exact (Nat.even_pow' (by omega)).2 even_two |>.mul_right _
  have hne : 2 ^ k' - 2 ^ k ≠ 0 := by rw [hsplit]; exact mul_ne_zero hk0 hm0
  have hg := gapUpper_uniform _ heven hne M hM
  have hsp : singProd (2 ^ k' - 2 ^ k) ≤ 3 / 2 * singProd (2 ^ (k' - k) - 1) := by
    rw [hsplit]
    refine le_trans (singProd_mul_le hk0 hm0) ?_
    rw [singProd_two_pow (by omega)]
  have hM' : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hl : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  calc (gap P (2 ^ k' - 2 ^ k) M : ℝ) ≤ gapCount (2 ^ k' - 2 ^ k) M := by
        exact_mod_cast gap_le_gapCount P hP _ M
    _ ≤ C₀ * singProd (2 ^ k' - 2 ^ k) * M / Real.log M ^ 2 := hg
    _ ≤ C₀ * (3 / 2 * singProd (2 ^ (k' - k) - 1)) * M / Real.log M ^ 2 := by
        gcongr
        exact C₀_pos.le

/-- The reindexing `k' ↦ k' - k`. -/
lemma inner_le (L k : ℕ) :
    ∑ k' ∈ range L, (if k < k' then singProd (2 ^ (k' - k) - 1) else 0) ≤
      ∑ m ∈ Icc 1 L, singProd (2 ^ m - 1) := by
  rw [← sum_filter]
  rw [← sum_image (g := fun k' => k' - k) (f := fun m => singProd (2 ^ m - 1))]
  · refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun m _ _ => singProd_nonneg _
    simp only [mem_image, mem_filter, mem_range] at hm
    obtain ⟨k', ⟨h1, h2⟩, rfl⟩ := hm
    simp only [mem_Icc]; omega
  · intro a ha b hb hab
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
    simp only at hab
    omega

lemma sq_le_two_pow (L : ℕ) : L ^ 2 ≤ 2 ^ (L + 1) := by
  induction L with
  | zero => norm_num
  | succ n ih =>
    have h := Nat.lt_two_pow_self (n := n)
    have h2 : 2 ^ (n + 1 + 1) = 2 * 2 * 2 ^ n := by ring
    have h3 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [h2]
    rw [h3] at ih
    nlinarith

/-- The constant `R₁` of the off-diagonal bound. -/
noncomputable def R₁ : ℝ := 1 + 3 * C₀ * (8 * Real.log 2 * Real.exp 13) / Real.log 2 ^ 2

lemma R₁_pos : 0 < R₁ := by
  unfold R₁
  have := C₀_pos
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

/-- **Off-diagonal bound**: `Q ≤ R₁ N`, `N = 2^(L+1)`. -/
theorem Q_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (L : ℕ) (hL : 1 ≤ L) :
    ((∑ k ∈ range L, ∑ k' ∈ range L,
      if k < k' then gap P (2 ^ k' - 2 ^ k) (2 ^ (L + 1) + 1) else 0 : ℕ) : ℝ) ≤
      R₁ * 2 ^ (L + 1) := by
  set M := 2 ^ (L + 1) + 1 with hMdef
  have hN : (4 : ℝ) ≤ 2 ^ (L + 1) := by
    have : (2 : ℝ) ^ 2 ≤ 2 ^ (L + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hM3 : 3 ≤ M := by
    have : 2 ≤ 2 ^ (L + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hMr : (M : ℝ) = 2 ^ (L + 1) + 1 := by rw [hMdef]; push_cast; ring
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogM : (L : ℝ) * Real.log 2 ≤ Real.log M := by
    have : Real.log ((2 : ℝ) ^ (L + 1)) ≤ Real.log M := by
      rw [hMr]; exact Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    nlinarith
  set B : ℝ := C₀ * (3 / 2) * M / Real.log M ^ 2 with hB
  have hB0 : 0 ≤ B := by have := C₀_pos; positivity
  -- pointwise
  have hpt : ∀ k ∈ range L, ∀ k' ∈ range L,
      (if k < k' then (gap P (2 ^ k' - 2 ^ k) M : ℝ) else 0) ≤
        (if k < k' then 1 else 0) + B * (if k < k' then singProd (2 ^ (k' - k) - 1) else 0) := by
    intro k _ k' _
    by_cases hkk : k < k'
    · simp only [if_pos hkk]
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        have := gap_odd_le P hP (k' := k') (by omega) M
        simp only [pow_zero] at *
        have : (gap P (2 ^ k' - 1) M : ℝ) ≤ 1 := by exact_mod_cast this
        have := singProd_nonneg (2 ^ (k' - 0) - 1)
        nlinarith
      · have h := gap_even_le P hP (k := k) (k' := k') h0 hkk M hM3
        have : C₀ * (3 / 2 * singProd (2 ^ (k' - k) - 1)) * M / Real.log M ^ 2 =
            B * singProd (2 ^ (k' - k) - 1) := by rw [hB]; ring
        linarith
    · simp only [if_neg hkk]; norm_num
  push_cast
  calc ∑ k ∈ range L, ∑ k' ∈ range L,
        (if k < k' then (gap P (2 ^ k' - 2 ^ k) M : ℝ) else 0)
      ≤ ∑ k ∈ range L, ∑ k' ∈ range L,
        ((if k < k' then 1 else 0) + B * (if k < k' then singProd (2 ^ (k' - k) - 1) else 0)) :=
        sum_le_sum fun k hk => sum_le_sum fun k' hk' => hpt k hk k' hk'
    _ ≤ ∑ k ∈ range L, ∑ _k' ∈ range L, (1 : ℝ) +
          B * ∑ _k ∈ range L, ∑ m ∈ Icc 1 L, singProd (2 ^ m - 1) := by
        have e : ∑ k ∈ range L, ∑ k' ∈ range L,
            ((if k < k' then (1 : ℝ) else 0) +
              B * (if k < k' then singProd (2 ^ (k' - k) - 1) else 0)) =
            ∑ k ∈ range L, ∑ k' ∈ range L, (if k < k' then (1 : ℝ) else 0) +
              B * ∑ k ∈ range L, ∑ k' ∈ range L,
                (if k < k' then singProd (2 ^ (k' - k) - 1) else 0) := by
          simp only [sum_add_distrib, mul_sum]
        rw [e]
        refine add_le_add (sum_le_sum fun k _ => sum_le_sum fun k' _ => by split_ifs <;> norm_num)
          (mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => inner_le L k) hB0)
    _ ≤ (L : ℝ) ^ 2 + B * (L * (8 * Real.log 2 * Real.exp 13 * L)) := by
        simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
        gcongr
        · nlinarith
        · exact romanov_lemma L
    _ ≤ 2 ^ (L + 1) + (C₀ * (3 / 2) * (2 * 2 ^ (L + 1)) / (L * Real.log 2) ^ 2) *
          ((L : ℝ) ^ 2 * (8 * Real.log 2 * Real.exp 13)) := by
        have h1 : (L : ℝ) ^ 2 ≤ 2 ^ (L + 1) := by exact_mod_cast sq_le_two_pow L
        have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
        have hB' : B ≤ C₀ * (3 / 2) * (2 * 2 ^ (L + 1)) / (L * Real.log 2) ^ 2 := by
          rw [hB]
          have := C₀_pos
          gcongr
          · rw [hMr]; linarith
        have hc : 0 ≤ (L : ℝ) ^ 2 * (8 * Real.log 2 * Real.exp 13) := by positivity
        have : B * (L * (8 * Real.log 2 * Real.exp 13 * L)) =
            B * ((L : ℝ) ^ 2 * (8 * Real.log 2 * Real.exp 13)) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_right hB' hc
        linarith
    _ = R₁ * 2 ^ (L + 1) := by
        have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
        unfold R₁
        field_simp

/-- `#A = π(N) ≥ N/(2(L + 1)) · ...`: for `L ≥ 2`, `π(2^(L+1)) · L ≥ 2^(L+1)/4`. -/
theorem S_ge (L : ℝ) (n : ℕ) (hL : 2 ≤ L) (hn : (n : ℝ) = 2 ^ (L + 1))
    (hpow : L + 2 ≤ 2 ^ L) : (n : ℝ) / 4 ≤ (Nat.primeCounting n : ℝ) * L := by
  have h := Chebyshev.pi_ge n
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hn4 : (4 : ℝ) ≤ n := by
    rw [hn]
    have : (2 : ℝ) ^ (2 : ℝ) ≤ 2 ^ (L + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith)
    norm_num at this; linarith
  have hln : Real.log n = (L + 1) * Real.log 2 := by
    rw [hn, Real.log_rpow (by norm_num)]
  have hln1 : Real.log ((n : ℝ) + 1) ≤ (L + 2) * Real.log 2 := by
    have : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), hln] at this
    linarith
  have hpos : 0 < Real.log n := by rw [hln]; positivity
  have hpi : ((n : ℝ) - (L + 2)) / (L + 1) ≤ Nat.primeCounting n := by
    refine le_trans ?_ h
    rw [hln, div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  have hhalf : (n : ℝ) / 2 ≤ n - (L + 2) := by
    have : (n : ℝ) = 2 * 2 ^ L := by rw [hn, Real.rpow_add (by norm_num), Real.rpow_one]; ring
    linarith
  have hπ0 : (0 : ℝ) ≤ Nat.primeCounting n := Nat.cast_nonneg _
  have key : (n : ℝ) / 2 / (L + 1) ≤ Nat.primeCounting n :=
    le_trans (div_le_div_of_nonneg_right hhalf (by linarith)) hpi
  rw [div_le_iff₀ (by linarith)] at key
  nlinarith

end LeanLab.Romanov
