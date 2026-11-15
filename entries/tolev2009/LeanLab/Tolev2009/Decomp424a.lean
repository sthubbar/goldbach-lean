module

public import LeanLab.Tolev2009.Decomp310c
public import LeanLab.HeathBrown1985.Vaughan

/-!
AI wrote this Lean code. Codex task424.
Binary Goldbach is open.
Source: Tolev 1999 page 71 Lemma 4 and pages 82 to 83 displays 52 to 54.
Written proof: Heath Brown 1982 pages 1367 to 1368 displays 6 to 8.
The dyadic grouping is proved. The coefficient identity and outer bookkeeping are proved.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp424a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Dyadic
open LeanLab.Tolev2009.Decomp286b LeanLab.Tolev2009.Decomp310c

/-- A Dirichlet convolution vanishes below the product of support lower bounds.
This is the finite support step behind Heath Brown 1982 page 1367 display 7. -/
theorem convolution_vanish_below {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    (u v n : ℕ) (hf : ∀ m < u, f m = 0) (hg : ∀ m < v, g m = 0)
    (hn : n < u * v) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  have he : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h₁ : p.1 < u
  · rw [hf _ h₁, zero_mul]
  · have h₂ : p.2 < v := by
      by_contra h₂
      have hle := Nat.mul_le_mul (le_of_not_gt h₁) (le_of_not_gt h₂)
      omega
    rw [hg _ h₂, mul_zero]

/-- The kth convolution power vanishes below the kth power of a support bound.
Source: Heath Brown 1982 page 1367 display 7 and the vanishing remainder after display 6. -/
theorem convolution_pow_vanish_below {R : Type*} [Semiring R] (f : ArithmeticFunction R)
    (u k n : ℕ) (hf : ∀ m < u, f m = 0) (hn : n < u ^ k) : (f ^ k) n = 0 := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp
  | succ k ih =>
    rw [pow_succ]
    exact convolution_vanish_below (f ^ k) f (u ^ k) u n (fun m hm => ih m hm) hf
      (by simpa [pow_succ] using hn)

/-- The cubic algebra identity underlying the k equal to three specialization.
Source: Heath Brown 1982 page 1367 display 6. -/
theorem heathBrown_three_ring {R : Type*} [CommRing R] (Z M L : R) :
    L = 3 * M * (Z * L) - 3 * Z * M ^ 2 * (Z * L) +
      Z ^ 2 * M ^ 3 * (Z * L) + (1 - Z * M) ^ 3 * L := by
  ring

/-- The k equal to three identity in the ring of arithmetic functions.
Mathlib supplies the truncated Moebius factor and its exact convolution with zeta.
Source: Heath Brown 1982 page 1367 displays 6 and 7. -/
theorem heathBrown_three_convolution (U : ℕ) (hU : 1 ≤ U) :
    ArithmeticFunction.vonMangoldt =
      3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
      3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
        LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log -
      LeanLab.HeathBrown1985.dGt U ^ 3 * ArithmeticFunction.vonMangoldt := by
  have h := heathBrown_three_ring (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (LeanLab.HeathBrown1985.muLe U) ArithmeticFunction.vonMangoldt
  rw [ArithmeticFunction.zeta_mul_vonMangoldt] at h
  have hd : 1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      LeanLab.HeathBrown1985.muLe U = -LeanLab.HeathBrown1985.dGt U := by
    rw [mul_comm, LeanLab.HeathBrown1985.muLe_mul_zeta U hU]
    ring
  rw [hd] at h
  convert h using 1 <;> ring

/-- On the range below the cubic support threshold the remainder vanishes exactly.
This is the finite coefficient form of Heath Brown 1982 page 1367 displays 6 to 8.
No dyadic factor grouping or coefficient estimate is asserted. -/
theorem heathBrown_three_coefficient (U n : ℕ) (hU : 1 ≤ U) (hn : n < (U + 1) ^ 3) :
    ArithmeticFunction.vonMangoldt n =
      (3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
        3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
          LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
  have hd : ∀ m < U + 1, LeanLab.HeathBrown1985.dGt U m = 0 := by
    intro m hm
    simp [LeanLab.HeathBrown1985.dGt, show ¬U < m by omega]
  have hp : ∀ m < (U + 1) ^ 3, (LeanLab.HeathBrown1985.dGt U ^ 3) m = 0 :=
    fun m hm => convolution_pow_vanish_below _ (U + 1) 3 m hd hm
  have hz : (LeanLab.HeathBrown1985.dGt U ^ 3 * ArithmeticFunction.vonMangoldt) n = 0 := by
    apply convolution_vanish_below _ _ ((U + 1) ^ 3) 1 n hp
    · intro m hm
      have hm0 : m = 0 := by omega
      subst m
      simp
    · simpa using hn
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (heathBrown_three_convolution U hU)
  change ArithmeticFunction.vonMangoldt n =
    (3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
      3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
        LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log : ArithmeticFunction ℝ) n -
      (LeanLab.HeathBrown1985.dGt U ^ 3 * ArithmeticFunction.vonMangoldt) n at h
  simpa only [hz, sub_zero] using h


/-- The norm of a Dirichlet convolution is at most the convolution of pointwise majorants.
This is the triangle step in the coefficient bounds of Tolev 1999 page 71 Lemma 4. -/
theorem norm_convolution_le (f g : ArithmeticFunction ℂ) (F G : ArithmeticFunction ℝ)
    (hf : ∀ n, ‖f n‖ ≤ F n) (hg : ∀ n, ‖g n‖ ≤ G n) (n : ℕ) :
    ‖(f * g) n‖ ≤ (F * G) n := by
  simp only [ArithmeticFunction.mul_apply]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [norm_mul]
  exact mul_le_mul (hf p.1) (hg p.2) (norm_nonneg _) ((norm_nonneg _).trans (hf p.1))

/-- A finite convolution of bounded factors is majorized by the matching power of zeta.
Source: the divisor coefficient bound in Tolev 1999 page 71 Lemma 4. -/
theorem norm_product_le_zeta_power {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ArithmeticFunction ℂ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, n ≠ 0 → ‖f i n‖ ≤ 1) (n : ℕ) :
    ‖(∏ i ∈ s, f i) n‖ ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ s.card) n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [prod_empty, card_empty, pow_zero, ArithmeticFunction.one_apply]
    split_ifs <;> simp
  | @insert i s hi ih =>
    rw [prod_insert hi, card_insert_of_notMem hi, pow_succ, mul_comm _ (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
    apply norm_convolution_le
    · intro m
      by_cases hm : m = 0
      · subst m; simp
      · simpa [ArithmeticFunction.zeta_apply, hm] using hf i (mem_insert_self _ _) m hm
    · intro m
      exact ih (fun j hj => hf j (mem_insert_of_mem hj)) m


/-- Five bounded convolution factors have coefficient norm at most tau5.
Source: Tolev 1999 page 71 Lemma 4 and page 83 displays 53 and 54. -/
theorem norm_five_product_le_tau5 (f : Fin 5 → ArithmeticFunction ℂ)
    (hf : ∀ i, ∀ n : ℕ, n ≠ 0 → ‖f i n‖ ≤ 1) (n : ℕ) :
    ‖(∏ i, f i) n‖ ≤ (tau5 n : ℝ) := by
  have h := norm_product_le_zeta_power Finset.univ f (fun i _ => hf i) n
  have hz : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (5 : ℕ)) n = (tau5 n : ℝ) := by
    norm_num [tau5, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.zeta_apply]
  simpa only [Finset.card_univ, Fintype.card_fin, hz] using h

/-- One factor bounded by L and four factors bounded by one give tau5 times L.
This isolates the logarithmic coefficient normalization of Tolev 1999 page 71 Lemma 4. -/
theorem norm_logarithmic_five_coefficient (L : ℝ) (_hL : 0 ≤ L)
    (f : ArithmeticFunction ℂ) (g : Fin 4 → ArithmeticFunction ℂ)
    (hf : ∀ n : ℕ, n ≠ 0 → ‖f n‖ ≤ L)
    (hg : ∀ i, ∀ n : ℕ, n ≠ 0 → ‖g i n‖ ≤ 1) (n : ℕ) :
    ‖(f * ∏ i, g i) n‖ ≤ (tau5 n : ℝ) * L := by
  have hf' : ∀ m, ‖f m‖ ≤ (L • (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m := by
    intro m
    by_cases hm : m = 0
    · subst m; simp
    · simpa [ArithmeticFunction.smul_map, ArithmeticFunction.zeta_apply, hm, smul_eq_mul] using hf m hm
  have hg' : ∀ m, ‖(∏ i, g i) m‖ ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (4 : ℕ)) m := by
    intro m
    simpa using norm_product_le_zeta_power Finset.univ g (fun i _ => hg i) m
  calc
    _ ≤ ((L • (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (4 : ℕ)) n :=
      norm_convolution_le f (∏ i, g i) _ _ hf' hg' n
    _ = L * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (5 : ℕ)) n := by
      rw [smul_mul_assoc, ← pow_succ']
      rfl
    _ = _ := by
      have hz : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (5 : ℕ)) n = (tau5 n : ℝ) := by
        norm_num [tau5, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.zeta_apply]
      rw [hz]
      ring


/-- The weighted von Mangoldt polynomial on one annulus, with the original upper cap.
Tolev 1999 page 71 display 9 with G containing the phase and divisor weight. -/
noncomputable def annularMangoldt (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, if x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then
    (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)
  else 0

/-- The explicit truncated k equal to three Heath Brown convolution polynomial.
Source: Heath Brown 1982 page 1367 display 6 after omitting the remainder. -/
noncomputable def heathBrownPolynomial (U : ℕ) : ArithmeticFunction ℝ :=
  3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
    3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
      LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log

/-- The floor of the real cube root is a valid truncated Moebius cutoff.
Source: Heath Brown 1982 page 1367, the choice of X before display 7. -/
theorem cubic_cutoff (x : ℝ) (hx : 3 ≤ x) :
    1 ≤ ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ ∧
      2 * x < ((⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by
  have hx0 : 0 ≤ 2 * x := by linarith
  have hr : 1 ≤ (2 * x) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hp : ((2 * x) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 2 * x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  refine ⟨?_, ?_⟩
  · exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hr)
  · have hlt := Nat.lt_floor_add_one ((2 * x) ^ ((1 : ℝ) / 3))
    have hpow := pow_lt_pow_left₀ hlt (by positivity : (0 : ℝ) ≤ (2 * x) ^ ((1 : ℝ) / 3)) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [hp, Nat.cast_add, Nat.cast_one] using hpow

/-- The weighted annular polynomial with the explicit truncated convolution coefficient.
Source: Heath Brown 1982 page 1367 displays 6 to 8. -/
noncomputable def annularHeathBrown (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, if x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then
    (heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ n : ℂ) *
      ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)
  else 0

/-- The coefficient identity replaces von Mangoldt on an entire annulus exactly.
There is no dyadic grouping input here.
Source: Heath Brown 1982 page 1367 displays 6 to 8. -/
theorem annularMangoldt_eq_heathBrown (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ)
    (hx : 3 ≤ x) : annularMangoldt lam l₃ K N α x = annularHeathBrown lam l₃ K N α x := by
  obtain ⟨hU, hcube⟩ := cubic_cutoff x hx
  unfold annularMangoldt annularHeathBrown
  apply sum_congr rfl
  intro n hn
  by_cases hc : x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x
  · simp only [hc, ite_true]
    have hncube : n < (⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ + 1) ^ 3 := by
      exact_mod_cast hc.2.trans_lt hcube
    have he : ArithmeticFunction.vonMangoldt n =
        heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ n :=
      heathBrown_three_coefficient _ n hU hncube
    rw [he]
  · simp only [hc, ite_false]

/-- The printed u, v and z satisfy every numerical hypothesis of Lemma 4
at an explicit large threshold. This removes a parameter admissibility input.
Source: Tolev 1999 page 71 Lemma 4 and page 82 before display 53. -/
theorem source_parameters (x : ℝ) (hx : Real.exp 100000 ≤ x) :
    2 ≤ x ^ ((1 : ℝ) / 1000) ∧
    x ^ ((1 : ℝ) / 1000) < 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
    2 ^ 30 * x ^ ((1 : ℝ) / 3) ≤ x ^ ((249 : ℝ) / 500) ∧
    x ^ ((249 : ℝ) / 500) ≤ x ∧
    (x ^ ((1 : ℝ) / 1000)) ^ (2 : ℕ) ≤ x ^ ((249 : ℝ) / 500) ∧
    128 * x ^ ((1 : ℝ) / 1000) * (x ^ ((249 : ℝ) / 500)) ^ (2 : ℕ) ≤ 2 * x ∧
    2 ^ 18 * (2 * x) ≤ (2 ^ 30 * x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hL : 100000 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogv : Real.log (2 ^ 30 * x ^ ((1 : ℝ) / 3)) =
      30 * Real.log 2 + (1 / 3) * Real.log x := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_rpow hxpos]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Real.log_le_log_iff (by norm_num) (by positivity)).mp
    rw [Real.log_rpow hxpos]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_rpow hxpos, hlogv]
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [hlogv, Real.log_rpow hxpos]
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) hxpos).mp
    rw [Real.log_rpow hxpos]
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, Real.log_rpow hxpos, Real.log_rpow hxpos]
    norm_num
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hxpos, Real.log_rpow hxpos, Real.log_mul (by positivity) hxpos.ne']
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h128]
    norm_num
    nlinarith
  · have hp : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    rw [mul_pow, hp]
    norm_num
    nlinarith


/-- A family of factors at most u whose product reaches u contains a nonempty
subset with product from u to strictly below u squared.
Source: the small factor grouping in Heath Brown 1982 page 1368 after display 8. -/
theorem exists_subset_product_between {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (hu : 1 < u)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ u) (hprod : u ≤ ∏ i ∈ s, a i) :
    ∃ t : Finset ι, t ⊆ s ∧ t.Nonempty ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) < u ^ (2 : ℕ) := by
  classical
  let T := s.powerset.filter (fun t => u ≤ ∏ i ∈ t, a i)
  have hT : T.Nonempty := ⟨s, by simp [T, hprod]⟩
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image T (fun t => t.card) hT
  obtain ⟨htS, htp⟩ := mem_filter.mp ht
  have hts : t ⊆ s := mem_powerset.mp htS
  have htne : t.Nonempty := by
    by_contra hn
    have he : t = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp only [he, prod_empty] at htp
    linarith
  obtain ⟨i, hi⟩ := htne
  have herase : (∏ j ∈ t.erase i, a j) < u := by
    by_contra hnot
    have hm : t.erase i ∈ T := by
      apply mem_filter.mpr
      exact ⟨mem_powerset.mpr ((erase_subset i t).trans hts), le_of_not_gt hnot⟩
    have hc := hmin (t.erase i) hm
    have hl := card_erase_lt_of_mem hi
    omega
  have hpnon : 0 ≤ ∏ j ∈ t.erase i, a j :=
    prod_nonneg (fun j hj => (ha j (hts (mem_of_mem_erase hj))).1)
  have hu0 : 0 < u := by linarith
  refine ⟨t, hts, ⟨i, hi⟩, htp, ?_⟩
  calc
    (∏ j ∈ t, a j) = (∏ j ∈ t.erase i, a j) * a i := (prod_erase_mul t a hi).symm
    _ ≤ (∏ j ∈ t.erase i, a j) * u := mul_le_mul_of_nonneg_left (ha i (hts hi)).2 hpnon
    _ < u * u := mul_lt_mul_of_pos_right herase hu0
    _ = u ^ (2 : ℕ) := by ring



/-- Small nonnegative factors partition into disjoint nonempty groups with products
from u to below u squared, and a disjoint remainder with product below u.
Source: Heath Brown 1982 page 1368, the groups P and the remainder Q. -/
theorem partition_small_products {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (hu : 1 < u)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ u) :
    ∃ R : Finset ι, ∃ T : Finset (Finset ι),
      R ⊆ s ∧
      (∀ t ∈ T, t ⊆ s ∧ t.Nonempty ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) < u ^ (2 : ℕ)) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧
      Disjoint R (T.biUnion id) ∧ R ∪ T.biUnion id = s ∧ (∏ i ∈ R, a i) < u := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hp : u ≤ ∏ i ∈ s, a i
  · obtain ⟨t, hts, htne, htlo, hthi⟩ := exists_subset_product_between s a u hu ha hp
    obtain ⟨R, T, hR, hTs, hpair, hd, hcover, hprod⟩ :=
      ih (s \ t) (sdiff_ssubset hts htne) (fun i hi => ha i (mem_sdiff.mp hi).1)
    have hRt : Disjoint R t := by
      apply disjoint_left.mpr
      intro i hi hit
      exact (mem_sdiff.mp (hR hi)).2 hit
    have hTt : ∀ q ∈ T, Disjoint t q := by
      intro q hq
      apply disjoint_left.mpr
      intro i hit hiq
      exact (mem_sdiff.mp ((hTs q hq).1 hiq)).2 hit
    refine ⟨R, insert t T, hR.trans sdiff_subset, ?_, ?_, ?_, ?_, hprod⟩
    · intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact ⟨hts, htne, htlo, hthi⟩
      · exact ⟨(hTs q hq).1.trans sdiff_subset, (hTs q hq).2⟩
    · intro q hq q' hq' hne
      by_cases hqt : q = t
      · subst q
        exact hTt q' ((mem_insert.mp hq').resolve_left (Ne.symm hne))
      · have hqT : q ∈ T := (mem_insert.mp hq).resolve_left hqt
        by_cases hq't : q' = t
        · subst q'
          exact (hTt q hqT).symm
        · exact hpair q hqT q' ((mem_insert.mp hq').resolve_left hq't) hne
    · rw [biUnion_insert]
      exact disjoint_union_right.mpr ⟨hRt, hd⟩
    · rw [biUnion_insert]
      change R ∪ (t ∪ T.biUnion id) = s
      rw [show R ∪ (t ∪ T.biUnion id) = (R ∪ T.biUnion id) ∪ t by ac_rfl,
        hcover, sdiff_union_of_subset hts]
  · refine ⟨s, ∅, subset_rfl, ?_, ?_, ?_, ?_, lt_of_not_ge hp⟩ <;> simp


/-- Groups whose factors lie between V and z give either the two group upper bound
or the three group lower bound, after including a remainder between one and u.
Source: the two product inequalities on Heath Brown 1982 page 1368. -/
theorem group_product_dichotomy {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (Q u V z : ℝ) (hQ : 1 ≤ Q) (hQu : Q ≤ u) (hV : 1 ≤ V) (hz : 1 ≤ z)
    (hg : ∀ i ∈ s, V ≤ g i ∧ g i ≤ z) :
    Q * (∏ i ∈ s, g i) ≤ u * z ^ (2 : ℕ) ∨ V ^ (3 : ℕ) ≤ Q * (∏ i ∈ s, g i) := by
  have hnon : ∀ i ∈ s, 0 ≤ g i := fun i hi => (zero_le_one.trans hV).trans (hg i hi).1
  have hp0 : 0 ≤ ∏ i ∈ s, g i := prod_nonneg hnon
  have hpupper : (∏ i ∈ s, g i) ≤ z ^ s.card := by
    calc
      _ ≤ ∏ i ∈ s, z := prod_le_prod₀ hnon (fun i hi => (hg i hi).2)
      _ = _ := by simp
  have hplower : V ^ s.card ≤ ∏ i ∈ s, g i := by
    calc
      _ = ∏ i ∈ s, V := by simp
      _ ≤ _ := prod_le_prod₀ (fun i hi => zero_le_one.trans hV) (fun i hi => (hg i hi).1)
  by_cases hk : s.card ≤ 2
  · left
    have hp2 := hpupper.trans (pow_le_pow_right₀ hz hk)
    exact mul_le_mul hQu hp2 hp0 ((zero_le_one.trans hQ).trans hQu)
  · right
    have hp3 := (pow_le_pow_right₀ hV (show 3 ≤ s.card by omega)).trans hplower
    exact hp3.trans (le_mul_of_one_le_left hp0 hQ)



/-- The product contradiction selects a subset in the middle range for factors
at least one. Source: Heath Brown 1982 page 1368 after display 8. -/
theorem exists_subset_product_in_range {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u V z : ℝ) (hu : 1 < u)
    (huV : u ≤ V) (hu2 : u ^ (2 : ℕ) ≤ z)
    (ha : ∀ i ∈ s, 1 ≤ a i ∧ a i ≤ z)
    (hlo : u * z ^ (2 : ℕ) < ∏ i ∈ s, a i)
    (hhi : (∏ i ∈ s, a i) < V ^ (3 : ℕ)) :
    ∃ t : Finset ι, t ⊆ s ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) ≤ V := by
  classical
  by_contra hnone
  have hno : ∀ t : Finset ι, t ⊆ s → u ≤ ∏ i ∈ t, a i → V < ∏ i ∈ t, a i := by
    intro t hts htu
    by_contra htV
    exact hnone ⟨t, hts, htu, le_of_not_gt htV⟩
  let small := s.filter (fun i => a i < u)
  let large := s.filter (fun i => u ≤ a i)
  have hsmallS : small ⊆ s := filter_subset _ _
  have hlargeS : large ⊆ s := filter_subset _ _
  have hsl : small ∪ large = s := by
    ext i
    simp only [small, large, mem_union, mem_filter]
    constructor
    · tauto
    · intro hi
      rcases lt_or_ge (a i) u with h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, h⟩
  have hdsl : Disjoint small large := by
    apply disjoint_left.mpr
    intro i his hil
    exact (not_lt_of_ge (mem_filter.mp hil).2) (mem_filter.mp his).2
  obtain ⟨R, T, hR, hTs, hpair, hd, hcover, hprodR⟩ :=
    partition_small_products small a u hu (fun i hi =>
      ⟨(zero_le_one.trans (ha i (hsmallS hi)).1), (mem_filter.mp hi).2.le⟩)
  have hR1 : 1 ≤ ∏ i ∈ R, a i := by
    calc
      (1 : ℝ) = ∏ i ∈ R, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (by intro i hi; norm_num)
        (fun i hi => (ha i (hsmallS (hR hi))).1)
  have htpair : (T : Set (Finset ι)).PairwiseDisjoint id := by
    intro t ht q hq hne
    exact hpair t ht q hq hne
  have hsmallprod : (∏ i ∈ small, a i) = (∏ i ∈ R, a i) * (∏ t ∈ T, ∏ i ∈ t, a i) := by
    rw [← hcover, prod_union hd, prod_biUnion htpair]
    rfl
  let groups := large.disjSum T
  let g : Sum ι (Finset ι) → ℝ := Sum.elim a (fun t => ∏ i ∈ t, a i)
  have hgroup : ∀ j ∈ groups, V ≤ g j ∧ g j ≤ z := by
    intro j hj
    cases j with
    | inl i =>
      have hi : i ∈ large := by simpa [groups] using hj
      have his := hlargeS hi
      have htu : u ≤ a i := (mem_filter.mp hi).2
      have ht := hno {i} (singleton_subset_iff.mpr his) (by simpa using htu)
      exact ⟨by simpa [g] using ht.le, (ha i his).2⟩
    | inr t =>
      have ht : t ∈ T := by simpa [groups] using hj
      have hts := hTs t ht
      have hl := hno t (hts.1.trans hsmallS) hts.2.2.1
      exact ⟨hl.le, hts.2.2.2.le.trans hu2⟩
  have hgp : (∏ j ∈ groups, g j) = (∏ i ∈ large, a i) * (∏ t ∈ T, ∏ i ∈ t, a i) := by
    simp [groups, g]
  have hfull : (∏ i ∈ s, a i) = (∏ i ∈ R, a i) * (∏ j ∈ groups, g j) := by
    rw [hgp, ← hsl, prod_union hdsl, hsmallprod]
    ring
  have hz : 1 ≤ z := by nlinarith
  rcases group_product_dichotomy groups g (∏ i ∈ R, a i) u V z hR1 hprodR.le
    (by linarith) hz hgroup with h | h
  · rw [← hfull] at h
    linarith
  · rw [← hfull] at h
    linarith



/-- Replacing factors at least one half by their maximum with one changes the
product by at most two to the number of factors. This handles singleton dyadic intervals
in the adaptation of Heath Brown 1982 pages 1367 to 1368. -/
theorem product_max_one_bounds {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, (1 : ℝ) / 2 ≤ a i) :
    (∏ i ∈ s, a i) ≤ (∏ i ∈ s, max 1 (a i)) ∧
      (∏ i ∈ s, max 1 (a i)) ≤ 2 ^ s.card * (∏ i ∈ s, a i) := by
  constructor
  · exact prod_le_prod₀ (fun i hi => by linarith [ha i hi]) (fun i hi => le_max_right _ _)
  · calc
      _ ≤ ∏ i ∈ s, 2 * a i := prod_le_prod₀ (fun i hi => by positivity) (fun i hi => by
        apply max_le <;> linarith [ha i hi])
      _ = _ := by rw [prod_mul_distrib]; simp

/-- The middle product selection extends to at most six factors at least one half.
Explicit factors of 64 account for the dyadic singleton intervals.
Source: the adapted grouping argument of Heath Brown 1982 pages 1367 to 1368. -/
theorem exists_subset_product_half_scale {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u V z : ℝ) (hu : 1 < u)
    (huV : 64 * u ≤ V) (hu2 : (64 * u) ^ (2 : ℕ) ≤ z)
    (ha : ∀ i ∈ s, (1 : ℝ) / 2 ≤ a i ∧ a i ≤ z) (hcard : s.card ≤ 6)
    (hlo : (64 * u) * z ^ (2 : ℕ) < ∏ i ∈ s, a i)
    (hhi : 64 * (∏ i ∈ s, a i) < V ^ (3 : ℕ)) :
    ∃ t : Finset ι, t ⊆ s ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) ≤ V := by
  classical
  let b : ι → ℝ := fun i => max 1 (a i)
  have hz : 1 ≤ z := by nlinarith
  have hb : ∀ i ∈ s, 1 ≤ b i ∧ b i ≤ z := by
    intro i hi
    exact ⟨le_max_left _ _, max_le hz (ha i hi).2⟩
  have hbound : ∀ t : Finset ι, t ⊆ s →
      (∏ i ∈ t, a i) ≤ (∏ i ∈ t, b i) ∧
      (∏ i ∈ t, b i) ≤ 64 * (∏ i ∈ t, a i) := by
    intro t hts
    have ht := product_max_one_bounds t a (fun i hi => (ha i (hts hi)).1)
    have hp0 : 0 ≤ ∏ i ∈ t, a i := prod_nonneg (fun i hi => by linarith [(ha i (hts hi)).1])
    refine ⟨ht.1, ht.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right ?_ hp0
    have hc : t.card ≤ 6 := (card_le_card hts).trans hcard
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc
    norm_num at hh ⊢
    exact hh
  have hbs := hbound s subset_rfl
  obtain ⟨t, hts, htu, htV⟩ := exists_subset_product_in_range s b (64 * u) V z
    (by linarith) huV hu2 hb (hlo.trans_le hbs.1) (hbs.2.trans_lt hhi)
  have hbt := hbound t hts
  refine ⟨t, hts, ?_, hbt.1.trans htV⟩
  have hh := htu.trans hbt.2
  linarith



/-- The printed exponents have enough slack for the explicit singleton adjustment.
Source: Tolev 1999 page 82 and the adapted grouping on Heath Brown 1982 page 1368.
The constants 64 and 4096 here are implementation bounds, not printed claims. -/
theorem source_half_scale_parameters (x : ℝ) (hx : Real.exp 100000 ≤ x) :
    64 * x ^ ((1 : ℝ) / 1000) ≤ 2 ^ 24 * x ^ ((1 : ℝ) / 3) ∧
    (64 * x ^ ((1 : ℝ) / 1000)) ^ (2 : ℕ) ≤ x ^ ((249 : ℝ) / 500) ∧
    4096 * x ^ ((1 : ℝ) / 1000) * (x ^ ((249 : ℝ) / 500)) ^ (2 : ℕ) < x ∧
    128 * x < (2 ^ 24 * x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hL : 100000 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h4096 : Real.log 4096 = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, Real.log_pow]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hxpos, Real.log_rpow hxpos, h64]
    norm_num
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hxpos, Real.log_rpow hxpos, h64]
    norm_num
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) hxpos).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hxpos, Real.log_rpow hxpos, h4096]
    norm_num
    nlinarith
  · have hp : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    rw [mul_pow, hp]
    norm_num
    nlinarith


/-- Tolev 1999 page 71 Lemma 4 and page 83 displays 53 and 54.
Heath Brown 1982 pages 1367 to 1368 give the six variable dyadic subdivision and grouping.
The coefficient identity is already proved. This leaf only groups its explicit polynomial
on one annulus into normalized blocks. There is no outer shell or prime conversion. Proved. -/
theorem grouped_annular_decomposition :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 3 ≤ X₀ ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      ∀ x : ℝ, X₀ ≤ x → x ≤ N →
      ∀ lam : ℕ → ℝ, ∀ l₃ K : ℕ, ∀ α : ℝ,
        ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
        ∃ M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
          annularHeathBrown lam l₃ K N α x =
            ∑ j : Fin J, c j * bilinear lam l₃ K N α x
              (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
          ∀ j : Fin J,
            ‖c j‖ ≤ C ∧
            0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
            0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
            x / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x ∧
            (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
            ((x ^ ((249 : ℝ) / 500) ≤ H j ∧
                (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
              (x ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
                ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  -- 2026-11-12 route burst: was an unproved placeholder; the proved twin has the same statement over
  -- copied definitions with identical bodies.
  exact LeanLab.Tolev2009.Sup83Split.grouped_annular_decomposition

/-- The annular von Mangoldt identity follows from the explicit polynomial grouping.
Derived from grouped_annular_decomposition. The coefficient identity is proved. -/
theorem annular_decomposition :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 3 ≤ X₀ ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      ∀ x : ℝ, X₀ ≤ x → x ≤ N →
      ∀ lam : ℕ → ℝ, ∀ l₃ K : ℕ, ∀ α : ℝ,
        ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (6 : ℕ) ∧
        ∃ M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
          annularMangoldt lam l₃ K N α x =
            ∑ j : Fin J, c j * bilinear lam l₃ K N α x
              (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
          ∀ j : Fin J,
            ‖c j‖ ≤ C ∧
            0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
            0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
            x / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x ∧
            (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
            ((x ^ ((249 : ℝ) / 500) ≤ H j ∧
                (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
              (x ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
                ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  obtain ⟨C, X₀, hC, hX₀, hgroup⟩ := grouped_annular_decomposition
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro N hL x hx hxN lam l₃ K α
  simpa only [annularMangoldt_eq_heathBrown lam l₃ K N α x (hX₀.trans hx)] using
    hgroup N hL x hx hxN lam l₃ K α

end LeanLab.Tolev2009.Decomp424a
