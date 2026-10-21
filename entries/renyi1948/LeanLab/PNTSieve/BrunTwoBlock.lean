module

public import LeanLab.PNTSieve.BrunPure

/-!
# Brun's sieve with two blocks of primes

Unit U-5503, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics, Brun 1920:
the first step from the pure sieve toward the fundamental lemma, IDEAS I-5051.

For disjoint finsets `P, Q` of primes, `x ∈ [0, 1]` the indicator that `a` has no prime factor in `P`,
`y` the same for `Q`, and Bonferroni truncations `l ≤ x ≤ u`, `l' ≤ y ≤ u'` with `u, u' ≥ 0`,
`(u - x)(u' - y) ≥ 0` gives `x y ≥ u l' + l u' - u u'`. Summed over `A`:

* `brun_two_block`: for even `re, se` and odd `ro, so`,
  `pairSum re so + pairSum ro se - pairSum re se ≤ S(A, P ∪ Q)`, where `pairSum r s` is the
  Brun sum over `T ⊆ P, |T| ≤ r` and `T' ⊆ Q, |T'| ≤ s` of `(-1)^{|T| + |T'|} A_{∏T ∏T'}`;
* `brun_two_block_main`: with densities and remainders as in `BrunPure`,
  `S(A, P ∪ Q) ≥ X (V_P V_Q - E_Q^{so} - E_P^{ro}(1 + E_Q^{se}) - E_P^{re}(E_Q^{so} + E_Q^{se})) - R`,
  `V_P = ∏_P (1 - x_p)`, `E_P^r = (Σ_P x_p)^{r+1}/(r+1)!`, `R` the three remainder sums.

The gain over `brun_pure_lower`: the truncation on `P` and on `Q` are chosen separately, so a block of
small primes with a large `Σ x_p` gets a deep truncation at a low level, and a block of large primes
with `Σ x_p` bounded gets a shallow one.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- The two-block Brun sum. -/
def pairSum (A P Q : Finset ℕ) (r s : ℕ) : ℤ :=
  ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), ∑ T' ∈ Q.powerset.filter (fun T => T.card ≤ s),
    (-1 : ℤ) ^ (T.card + T'.card) * (A.filter (fun a => (∏ p ∈ T, p) * (∏ p ∈ T', p) ∣ a)).card

lemma coprime_prod_of_disjoint {P Q T T' : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint P Q) (hT : T ⊆ P) (hT' : T' ⊆ Q) :
    Nat.Coprime (∏ p ∈ T, p) (∏ p ∈ T', p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  have hne : p ≠ q := by
    rintro rfl
    exact Finset.disjoint_left.mp hPQ (hT hp) (hT' hq)
  exact (Nat.coprime_primes (hP p (hT hp)) (hQ q (hT' hq))).mpr hne

/-- The pairSum is the sum over `a` of the product of the two pointwise truncations. -/
lemma pairSum_eq (A P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hPQ : Disjoint P Q) (r s : ℕ) :
    pairSum A P Q r s = ∑ a ∈ A, trunc (P.filter (· ∣ a)) r * trunc (Q.filter (· ∣ a)) s := by
  have hpt : ∀ a, trunc (P.filter (· ∣ a)) r * trunc (Q.filter (· ∣ a)) s =
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), ∑ T' ∈ Q.powerset.filter (fun T => T.card ≤ s),
        (if (∏ p ∈ T, p) * (∏ p ∈ T', p) ∣ a then (-1 : ℤ) ^ (T.card + T'.card) else 0) := by
    intro a
    rw [← pointwise P hP r a, ← pointwise Q hQ s a, sum_mul_sum]
    refine sum_congr rfl (fun T hT => sum_congr rfl (fun T' hT' => ?_))
    rw [mem_filter, mem_powerset] at hT hT'
    have hcop := coprime_prod_of_disjoint hP hQ hPQ hT.1 hT'.1
    by_cases h1 : (∏ p ∈ T, p) ∣ a <;> by_cases h2 : (∏ p ∈ T', p) ∣ a
    · rw [if_pos h1, if_pos h2, if_pos (hcop.mul_dvd_of_dvd_of_dvd h1 h2), pow_add]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 ((dvd_mul_left _ _).trans h)), mul_zero]
    · rw [if_neg h1, if_neg (fun h => h1 ((dvd_mul_right _ _).trans h)), zero_mul]
    · rw [if_neg h1, if_neg (fun h => h1 ((dvd_mul_right _ _).trans h)), zero_mul]
  rw [sum_congr rfl (fun a _ => hpt a), sum_comm]
  unfold pairSum
  refine sum_congr rfl (fun T _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun T' _ => ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

lemma sifted_union (A P Q : Finset ℕ) :
    sifted A (P ∪ Q) = ∑ a ∈ A, (if P.filter (· ∣ a) = ∅ then (1 : ℤ) else 0) *
      (if Q.filter (· ∣ a) = ∅ then (1 : ℤ) else 0) := by
  rw [sifted_eq]
  refine sum_congr rfl (fun a _ => ?_)
  rw [filter_union]
  by_cases h1 : P.filter (· ∣ a) = ∅ <;> by_cases h2 : Q.filter (· ∣ a) = ∅ <;>
    simp [h1, h2, union_eq_empty]

/-- The pointwise two-block inequality: `x y ≥ u l' + l u' - u u'`. -/
lemma two_block_pointwise {x y u l u' l' : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hlx : l ≤ x) (hxu : x ≤ u)
    (hly : l' ≤ y) (hyu : y ≤ u') : u * l' + l * u' - u * u' ≤ x * y := by
  have h1 : 0 ≤ (u - x) * (u' - y) := mul_nonneg (by linarith) (by linarith)
  have h2 : u * l' ≤ u * y := mul_le_mul_of_nonneg_left hly (by linarith)
  have h3 : l * u' ≤ x * u' := mul_le_mul_of_nonneg_right hlx (by linarith)
  nlinarith

/-- **Brun's two-block sieve, combinatorial form.** -/
theorem brun_two_block (A P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hPQ : Disjoint P Q) {re ro se so : ℕ} (hre : Even re) (hro : Odd ro) (hse : Even se)
    (hso : Odd so) :
    pairSum A P Q re so + pairSum A P Q ro se - pairSum A P Q re se ≤ sifted A (P ∪ Q) := by
  rw [pairSum_eq A P Q hP hQ hPQ, pairSum_eq A P Q hP hQ hPQ, pairSum_eq A P Q hP hQ hPQ,
    sifted_union, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_le_sum (fun a _ => ?_)
  apply two_block_pointwise
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num
  · exact bonferroni_odd _ hro
  · exact bonferroni_even _ hre
  · exact bonferroni_odd _ hso
  · exact bonferroni_even _ hse

/-- The two-block remainder `R_{T,T'} = A_{∏T ∏T'} - X ∏_T x_p ∏_{T'} x_p`. -/
noncomputable def rem2 (A : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (T T' : Finset ℕ) : ℝ :=
  cnt A ((∏ p ∈ T, p) * (∏ p ∈ T', p)) - X * ((∏ p ∈ T, x p) * (∏ p ∈ T', x p))

/-- The truncated main sum `Σ_{T ⊆ P, |T| ≤ r} (-1)^{|T|} ∏_T x_p`. -/
noncomputable def msum (P : Finset ℕ) (x : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p

/-- The sum of `|R_{T,T'}|` over the two truncations. -/
noncomputable def remSum (A P Q : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (r s : ℕ) : ℝ :=
  ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), ∑ T' ∈ Q.powerset.filter (fun T => T.card ≤ s),
    |rem2 A x X T T'|

lemma pairSum_split (A P Q : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (r s : ℕ) :
    (pairSum A P Q r s : ℝ) = X * msum P x r * msum Q x s +
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), ∑ T' ∈ Q.powerset.filter (fun T => T.card ≤ s),
        (-1 : ℝ) ^ (T.card + T'.card) * rem2 A x X T T' := by
  unfold pairSum msum rem2 cnt
  push_cast
  rw [mul_assoc, sum_mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun T _ => ?_)
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun T' _ => ?_)
  rw [pow_add]
  ring

lemma pair_rem_le (A P Q : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (r s : ℕ) :
    -remSum A P Q x X r s ≤
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), ∑ T' ∈ Q.powerset.filter (fun T => T.card ≤ s),
        (-1 : ℝ) ^ (T.card + T'.card) * rem2 A x X T T' := by
  unfold remSum
  rw [← sum_neg_distrib]
  refine sum_le_sum (fun T _ => ?_)
  rw [← sum_neg_distrib]
  refine sum_le_sum (fun T' _ => ?_)
  have h := neg_abs_le ((-1 : ℝ) ^ (T.card + T'.card) * rem2 A x X T T')
  rwa [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h

/-- The main-term algebra: `M₁M₂ + M₃M₄ - M₁M₄ ≥ V_P V_Q - E₂ - E₃(1 + E₄) - E₁(E₂ + E₄)`. -/
lemma main_alg {M1 M2 M3 M4 VP VQ E1 E2 E3 E4 : ℝ} (hVP0 : 0 ≤ VP) (hVP1 : VP ≤ 1)
    (hVQ0 : 0 ≤ VQ) (hVQ1 : VQ ≤ 1) (h1 : |M1 - VP| ≤ E1) (h2 : |M2 - VQ| ≤ E2)
    (h3 : |M3 - VP| ≤ E3) (h4 : |M4 - VQ| ≤ E4) :
    VP * VQ - E2 - E3 * (1 + E4) - E1 * (E2 + E4) ≤ M1 * M2 + M3 * M4 - M1 * M4 := by
  have hid : M1 * M2 + M3 * M4 - M1 * M4 =
      VP * VQ + VP * (M2 - VQ) + (M3 - VP) * M4 + (M1 - VP) * (M2 - M4) := by ring
  have hE1 : 0 ≤ E1 := (abs_nonneg _).trans h1
  have hE3 : 0 ≤ E3 := (abs_nonneg _).trans h3
  have hA : |VP * (M2 - VQ)| ≤ E2 := by
    rw [abs_mul, abs_of_nonneg hVP0]
    calc VP * |M2 - VQ| ≤ 1 * |M2 - VQ| := mul_le_mul_of_nonneg_right hVP1 (abs_nonneg _)
      _ ≤ E2 := by linarith
  have hM4 : |M4| ≤ 1 + E4 := by
    have : |M4| ≤ |M4 - VQ| + |VQ| := by
      have := abs_add_le (M4 - VQ) VQ; simpa using this
    rw [abs_of_nonneg hVQ0] at this
    linarith
  have hB : |(M3 - VP) * M4| ≤ E3 * (1 + E4) := by
    rw [abs_mul]; exact mul_le_mul h3 hM4 (abs_nonneg _) hE3
  have hM24 : |M2 - M4| ≤ E2 + E4 := by
    have := abs_sub_le M2 VQ M4
    rw [abs_sub_comm VQ M4] at this
    linarith
  have hC : |(M1 - VP) * (M2 - M4)| ≤ E1 * (E2 + E4) := by
    rw [abs_mul]; exact mul_le_mul h1 hM24 (abs_nonneg _) hE1
  rw [hid]
  have := neg_abs_le (VP * (M2 - VQ))
  have := neg_abs_le ((M3 - VP) * M4)
  have := neg_abs_le ((M1 - VP) * (M2 - M4))
  linarith

/-- `E_P^r = (Σ_P x_p)^{r+1}/(r+1)!`, the pure sieve truncation error on one block. -/
noncomputable def truncErr (P : Finset ℕ) (x : ℕ → ℝ) (r : ℕ) : ℝ :=
  (∑ p ∈ P, x p) ^ (r + 1) / (r + 1).factorial

/-- **Brun's two-block sieve, lower bound with main term.** For disjoint finsets `P, Q` of primes,
densities `0 ≤ x_p ≤ 1`, `X ≥ 0`, even `re, se`, odd `ro, so`:
`S(A, P ∪ Q) ≥ X (V_P V_Q - E_Q^{so} - E_P^{ro}(1 + E_Q^{se}) - E_P^{re}(E_Q^{so} + E_Q^{se}))`
minus the three remainder sums. -/
theorem brun_two_block_main (A P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hPQ : Disjoint P Q) (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (X : ℝ)
    (hX : 0 ≤ X) {re ro se so : ℕ} (hre : Even re) (hro : Odd ro) (hse : Even se) (hso : Odd so) :
    X * ((∏ p ∈ P, (1 - x p)) * (∏ p ∈ Q, (1 - x p)) - truncErr Q x so -
        truncErr P x ro * (1 + truncErr Q x se) -
        truncErr P x re * (truncErr Q x so + truncErr Q x se)) -
      (remSum A P Q x X re so + remSum A P Q x X ro se + remSum A P Q x X re se) ≤
      (sifted A (P ∪ Q) : ℝ) := by
  have h := brun_two_block A P Q hP hQ hPQ hre hro hse hso
  have hR : ((pairSum A P Q re so + pairSum A P Q ro se - pairSum A P Q re se : ℤ) : ℝ) ≤
      (sifted A (P ∪ Q) : ℝ) := by exact_mod_cast h
  push_cast at hR
  rw [pairSum_split A P Q x X, pairSum_split A P Q x X, pairSum_split A P Q x X] at hR
  have r1 := pair_rem_le A P Q x X re so
  have r2 := pair_rem_le A P Q x X ro se
  have r3 : ∑ T ∈ P.powerset.filter (fun T => T.card ≤ re),
      ∑ T' ∈ Q.powerset.filter (fun T => T.card ≤ se),
        (-1 : ℝ) ^ (T.card + T'.card) * rem2 A x X T T' ≤ remSum A P Q x X re se := by
    unfold remSum
    refine sum_le_sum (fun T _ => sum_le_sum (fun T' _ => ?_))
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hVP0 : 0 ≤ ∏ p ∈ P, (1 - x p) := prod_nonneg (fun p _ => by linarith [hx1 p])
  have hVP1 : ∏ p ∈ P, (1 - x p) ≤ 1 :=
    prod_le_one₀ (fun p _ => by linarith [hx1 p]) (fun p _ => by linarith [hx0 p])
  have hVQ0 : 0 ≤ ∏ p ∈ Q, (1 - x p) := prod_nonneg (fun p _ => by linarith [hx1 p])
  have hVQ1 : ∏ p ∈ Q, (1 - x p) ≤ 1 :=
    prod_le_one₀ (fun p _ => by linarith [hx1 p]) (fun p _ => by linarith [hx0 p])
  have halg := main_alg hVP0 hVP1 hVQ0 hVQ1 (main_dev P x hx0 hx1 re) (main_dev Q x hx0 hx1 so)
    (main_dev P x hx0 hx1 ro) (main_dev Q x hx0 hx1 se)
  have hXalg := mul_le_mul_of_nonneg_left halg hX
  unfold truncErr
  unfold msum at hR
  nlinarith

end LeanLab.PNTSieve.Bonferroni

