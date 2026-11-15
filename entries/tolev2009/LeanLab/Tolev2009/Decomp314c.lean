module

public import LeanLab.Tolev2009.Decomp314b

/-!
AI wrote this Lean code. Codex task314.
Binary Goldbach is open.
Sources: Halupczok 2008 pages 12 and 18 to 19.
The tail is separated from the arithmetic first moment average.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp314c
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a LeanLab.Tolev2009.Decomp314b

/-- Halupczok page 18, the elementary first moment bound for a scalar series tail. -/
theorem first_moment_tail (f : ℕ → ℂ) (hf0 : f 0 = 0)
    (hs : Summable (fun q : ℕ => (q : ℝ) * ‖f q‖)) (Q : ℝ) (hQ : 1 ≤ Q) :
    ‖(∑ q ∈ Icc 1 ⌊Q⌋₊, f q) - ∑' q : ℕ, f q‖ ≤
      (∑' q : ℕ, (q : ℝ) * ‖f q‖) / Q := by
  have hQ0 : 0 < Q := by linarith
  have hf : Summable f := hs.of_norm_bounded (fun q => by
    by_cases hq : q = 0
    · simp [hq, hf0]
    · exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq))
  let H := ⌊Q⌋₊ + 1
  have ht : Summable (fun n : ℕ => f (n + H)) := (summable_nat_add_iff H).mpr hf
  have hwt : Summable (fun n : ℕ => ((n + H : ℕ) : ℝ) * ‖f (n + H)‖) :=
    (summable_nat_add_iff H).mpr hs
  have hp : ∑ q ∈ Icc 1 ⌊Q⌋₊, f q = ∑ q ∈ range H, f q := by
    apply sum_subset
    · intro q hq
      have hq' := mem_Icc.mp hq
      exact mem_range.mpr (by dsimp [H]; omega)
    · intro q hq hnot
      have hq0 : q = 0 := by
        have hq' := mem_range.mp hq
        simp only [mem_Icc, not_and_or, not_le] at hnot
        dsimp [H] at hq'
        omega
      simp [hq0, hf0]
  have heq : (∑ q ∈ Icc 1 ⌊Q⌋₊, f q) - ∑' q : ℕ, f q =
      -(∑' n : ℕ, f (n + H)) := by
    rw [hp, ← hf.sum_add_tsum_nat_add H]
    abel
  rw [heq, norm_neg]
  calc
    _ ≤ ∑' n : ℕ, ‖f (n + H)‖ := norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' n : ℕ, (((n + H : ℕ) : ℝ) * ‖f (n + H)‖) / Q := by
      apply Summable.tsum_le_tsum _ ht.norm (hwt.div_const Q)
      intro n
      have hq : Q ≤ ((n + H : ℕ) : ℝ) := by
        have hfloor := Nat.lt_floor_add_one Q
        dsimp [H]
        push_cast
        linarith
      apply (le_div_iff₀ hQ0).mpr
      nlinarith [norm_nonneg (f (n + H))]
    _ = (∑' n : ℕ, ((n + H : ℕ) : ℝ) * ‖f (n + H)‖) / Q := by rw [tsum_div_const]
    _ ≤ (∑' q : ℕ, (q : ℝ) * ‖f q‖) / Q := by
      apply div_le_div_of_nonneg_right _ hQ0.le
      have he := hs.sum_add_tsum_nat_add H
      have hn : 0 ≤ ∑ q ∈ range H, (q : ℝ) * ‖f q‖ :=
        sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      linarith

/-- Halupczok page 12 e1 and page 18, remove the finite singular series.
Tolev 1999 page 79 display 40 and pages 80 to 81 displays 45 to 47.
This is a scalar tail bound for one admissible triple, conditional on summability.
No progression sum, geometric integral or modulus average occurs. -/
theorem scalar_series_tail (Q : ℝ) (k l : Fin 3 → ℕ) (N : ℕ)
    (hQ : 1 ≤ Q) (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hs : Summable (fun q : ℕ => weightedCoeff k l N q)) :
    |truncatedMain Q k l N - M singSeries k l N| ≤
      ((N : ℝ) ^ 2 / Q) * coefficientMass k l N := by
  let f : ℕ → ℂ := fun q => ssTerm k l N q / (phiProduct k : ℂ)
  have hn (q : ℕ) : (q : ℝ) * ‖f q‖ = weightedCoeff k l N q := by
    simp [f, weightedCoeff, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (phiProduct_nonneg k)]
    ring
  have hsf : Summable (fun q : ℕ => (q : ℝ) * ‖f q‖) := by simpa only [hn] using hs
  have hf0 : f 0 = 0 := by simp [f, ssTerm]
  have hf : Summable f := hsf.of_norm_bounded (fun q => by
    by_cases hq : q = 0
    · simp [hq, hf0]
    · exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq))
  have hd : (∏ i : Fin 3, ((k i).totient : ℂ)) = (phiProduct k : ℂ) := by
    simp [phiProduct]
  have hcast : ((N : ℂ) ^ 2 / 2) = (((N : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hp : truncatedMain Q k l N =
      (∑ q ∈ Icc 1 ⌊Q⌋₊, f q).re * ((N : ℝ) ^ 2 / 2) := by
    rw [truncatedMain_as_re]
    simp_rw [hd]
    rw [← sum_mul, hcast]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  have ht : (∑' q : ℕ, f q).re = singSeries k l N / phiProduct k := by
    rw [hf.tsum_eq_zero_add, hf0, zero_add]
    simp only [f, tsum_div_const, Complex.div_ofReal_re, singSeries]
  have hm : M singSeries k l N = (∑' q : ℕ, f q).re * ((N : ℝ) ^ 2 / 2) := by
    rw [ht]
    simp only [M, phiProduct, Fin.prod_univ_three]
    ring
  rw [hp, hm, ← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2)]
  have hb := first_moment_tail f hf0 hsf Q hQ
  have hmass : (∑' q : ℕ, (q : ℝ) * ‖f q‖) = coefficientMass k l N := by
    simp only [hn, coefficientMass]
  rw [hmass] at hb
  calc
    _ ≤ (coefficientMass k l N / Q) * ((N : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hb) (by positivity)
    _ ≤ ((N : ℝ) ^ 2 / Q) * coefficientMass k l N := by
      have hmass0 := coefficientMass_nonneg k l N
      have hQ0 : 0 < Q := by linarith
      have hn0 : (0 : ℝ) ≤ (N : ℝ) ^ 2 / Q * coefficientMass k l N := by positivity
      nlinarith [show (coefficientMass k l N / Q) * ((N : ℝ) ^ 2 / 2) =
        (((N : ℝ) ^ 2 / Q) * coefficientMass k l N) / 2 by ring]


/-- Exact sealed singular series tail statement.
Derived from the shared arithmetic summability and first moment leaves. -/
theorem singular_series_tail :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => truncatedMain (Qof A N) k l N -
            M singSeries k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, Nm, hC, hm⟩ := coefficient_mass_mean A hA l₃ hl₃
  obtain ⟨Ng, hg⟩ := integral_cutoff_regime A
  refine ⟨C, max Nm Ng, ?_⟩
  intro lam hlam N hodd hN
  have hNm := (le_max_left _ _).trans hN
  have hNg := (le_max_right _ _).trans hN
  have hL := (hg N hNg).1
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  have he : ∀ k l, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      |truncatedMain (Qof A N) k l N - M singSeries k l N| ≤
        (1 * (N : ℝ) ^ 2 / Qof A N) * coefficientMass k l N := by
    intro k l hk hl
    simpa only [one_mul] using scalar_series_tail (Qof A N) k l N hQ hk hl
      (weighted_coeff_summable k l N hk hl hodd)
  simpa only [one_mul] using mean_of_mass_bound _ A 1 C lam l₃ N hA hL
    (by norm_num) hC hlam (hm N hodd hNm) he

end LeanLab.Tolev2009.Decomp314c
