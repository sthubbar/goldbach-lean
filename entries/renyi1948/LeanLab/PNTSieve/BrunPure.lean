module

public import LeanLab.PNTSieve.BonferroniWeighted
public import LeanLab.PNTSieve.Esymm

/-!
# Brun's pure sieve

Lab proof, unit U-5326, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Brun 1915 to 1920. For a finite set `A` of naturals, a finset `P` of primes, densities
`0 ≤ x_p ≤ 1`, any `X ≥ 0` and the remainders `R_T = A_{∏T} - X ∏_T x_p`:

* `brun_pure_lower`, odd `r`: `S(A, P) ≥ X ∏_P (1 - x_p) - X (Σ_P x_p)^{r+1}/(r + 1)! - Σ_{T ⊆ P, |T| ≤ r} |R_T|`;
* `brun_pure_upper`, even `r`: `S(A, P) ≤ X ∏_P (1 - x_p) + X (Σ_P x_p)^{r+1}/(r + 1)! + Σ_{T ⊆ P, |T| ≤ r} |R_T|`.
The remainders are defined, not assumed, so the statement holds for every `A`; it is useful when the
`R_T` are small, as Bombieri-Vinogradov makes them on average for `A = {N - p}`, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- `A_d = #{a ∈ A : d ∣ a}` as a real number. -/
noncomputable def cnt (A : Finset ℕ) (d : ℕ) : ℝ := ((A.filter (fun a => d ∣ a)).card : ℝ)

/-- The remainder `R_T = A_{∏T} - X ∏_T x_p`. -/
noncomputable def rem (A : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (T : Finset ℕ) : ℝ :=
  cnt A (∏ p ∈ T, p) - X * ∏ p ∈ T, x p

lemma brunSum_split (A P : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (r : ℕ) :
    (brunSum A P r : ℝ) =
      X * ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p +
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * rem A x X T := by
  unfold brunSum rem cnt
  push_cast
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun T _ => ?_)
  ring

lemma rem_sum_le (A P : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) (r : ℕ) :
    |∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * rem A x X T| ≤
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), |rem A x X T| := by
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl (fun T _ => ?_)))
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

lemma main_dev (P : Finset ℕ) (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (r : ℕ) :
    |∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p -
      ∏ p ∈ P, (1 - x p)| ≤ (∑ p ∈ P, x p) ^ (r + 1) / (r + 1).factorial := by
  refine (weighted_dev x hx0 hx1 P r).trans ?_
  have h := factorial_mul_esymm_le x hx0 P (r + 1)
  rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos _)]
  unfold esymm at h
  linarith

theorem brun_pure_lower (A P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (X : ℝ) (hX : 0 ≤ X) {r : ℕ} (hr : Odd r) :
    X * ∏ p ∈ P, (1 - x p) - X * ((∑ p ∈ P, x p) ^ (r + 1) / (r + 1).factorial) -
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), |rem A x X T| ≤ (sifted A P : ℝ) := by
  have h1 : (brunSum A P r : ℝ) ≤ sifted A P := by exact_mod_cast brun_lower A P hP hr
  rw [brunSum_split A P x X r] at h1
  have h2 := main_dev P x hx0 hx1 r
  have h3 := rem_sum_le A P x X r
  rw [abs_le] at h2 h3
  have h4 := mul_le_mul_of_nonneg_left h2.1 hX
  nlinarith

theorem brun_pure_upper (A P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (X : ℝ) (hX : 0 ≤ X) {r : ℕ} (hr : Even r) :
    (sifted A P : ℝ) ≤ X * ∏ p ∈ P, (1 - x p) + X * ((∑ p ∈ P, x p) ^ (r + 1) / (r + 1).factorial) +
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), |rem A x X T| := by
  have h1 : (sifted A P : ℝ) ≤ brunSum A P r := by exact_mod_cast brun_upper A P hP hr
  rw [brunSum_split A P x X r] at h1
  have h2 := main_dev P x hx0 hx1 r
  have h3 := rem_sum_le A P x X r
  rw [abs_le] at h2 h3
  have h4 := mul_le_mul_of_nonneg_left h2.2 hX
  nlinarith

end LeanLab.PNTSieve.Bonferroni

