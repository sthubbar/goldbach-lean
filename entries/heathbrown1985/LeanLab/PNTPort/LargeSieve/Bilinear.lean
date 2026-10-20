module

public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
# The bilinear multiplicative large sieve

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

`bilinear_large_sieve`: with `W(q) = q/φ(q)`,

  `(∑_{q ≤ Q} W(q) ∑_{χ prim} ‖∑_{m,n} a_m b_n χ(mn)‖)² ≤ (N₁ + 2Q²)(N₂ + 2Q²) ‖a‖² ‖b‖²`,

`m` in `(M₁, M₁+N₁]`, `n` in `(M₂, M₂+N₂]`. This is the Type II input of Bombieri-Vinogradov.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

/-- Weighted Cauchy-Schwarz. -/
lemma cs_weighted {α : Type*} (s : Finset α) (w f g : α → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (f i * g i)) ^ 2 ≤ (∑ i ∈ s, w i * f i ^ 2) * ∑ i ∈ s, w i * g i ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i) * f i)
    (fun i => Real.sqrt (w i) * g i)
  have e1 : ∀ i ∈ s, Real.sqrt (w i) * f i * (Real.sqrt (w i) * g i) = w i * (f i * g i) := by
    intro i hi
    have := Real.mul_self_sqrt (hw i hi)
    calc _ = (Real.sqrt (w i) * Real.sqrt (w i)) * f i * g i := by ring
      _ = _ := by rw [this]; ring
  have e2 : ∀ (u : α → ℝ), ∀ i ∈ s, (Real.sqrt (w i) * u i) ^ 2 = w i * u i ^ 2 := by
    intro u i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [sum_congr rfl e1, sum_congr rfl (e2 f), sum_congr rfl (e2 g)] at h
  exact h

/-- The index set of `(q - 1, χ)` with `χ` primitive mod `q ≤ Q`. -/
noncomputable def primIdx (Q : ℕ) : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
  (range Q).sigma (fun k => (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
    (fun χ => χ.IsPrimitive))

/-- The multiplicative large sieve over `primIdx`. -/
lemma mls_primIdx {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      ‖∑ n ∈ Ioc M (M + N), a n * i.2 n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  unfold primIdx
  rw [sum_sigma]
  simp_rw [← mul_sum]
  exact multiplicative_large_sieve hQ a M N

/-- **The bilinear large sieve.** -/
theorem bilinear_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a b : ℤ → ℂ) (M₁ M₂ : ℤ) (N₁ N₂ : ℕ) :
    (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂), a m * b n * i.2 ((m * n : ℤ))‖) ^ 2 ≤
      ((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖ ^ 2) *
      ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖ ^ 2) := by
  have hfac : ∀ i : Σ k : ℕ, DirichletCharacter ℂ (k + 1),
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂), a m * b n * i.2 ((m * n : ℤ))‖ =
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), a m * i.2 m‖ * ‖∑ n ∈ Ioc M₂ (M₂ + N₂), b n * i.2 n‖ := by
    intro i
    rw [← norm_mul, sum_mul_sum]
    congr 1
    apply sum_congr rfl; intro m _
    apply sum_congr rfl; intro n _
    rw [Int.cast_mul, map_mul]
    ring
  simp_rw [hfac]
  have hw : ∀ i ∈ primIdx Q, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  refine (cs_weighted (primIdx Q) _ _ _ hw).trans ?_
  exact mul_le_mul (mls_primIdx hQ a M₁ N₁) (mls_primIdx hQ b M₂ N₂)
    (sum_nonneg (fun i hi => mul_nonneg (hw i hi) (by positivity)))
    (mul_nonneg (by positivity) (sum_nonneg (fun _ _ => by positivity)))

end LeanLab.PNTPort.LargeSieve
