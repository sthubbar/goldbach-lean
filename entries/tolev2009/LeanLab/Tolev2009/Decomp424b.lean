module

public import LeanLab.Tolev2009.Decomp424a

/-!
AI wrote this Lean code. Codex task424.
Binary Goldbach is open.
Source: the outer dyadic subdivision of Tolev 1999 page 82 display 52.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp424b

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Dyadic
open LeanLab.Tolev2009.Decomp286b LeanLab.Tolev2009.Decomp310c
open LeanLab.Tolev2009.Decomp424a

/-- Consecutive doubled annuli telescope exactly, including both endpoints.
This is the finite outer subdivision in Tolev 1999 page 82 display 52. -/
theorem sum_doubled_annuli (f : ℕ → ℂ) (N t : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (∑ j ∈ range t, ∑ n ∈ Icc 1 N,
      if y * 2 ^ j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (y * 2 ^ j) then f n else 0) =
    ∑ n ∈ Icc 1 N, if y < (n : ℝ) ∧ (n : ℝ) ≤ y * 2 ^ t then f n else 0 := by
  induction t with
  | zero =>
    simp only [range_zero, sum_empty, pow_zero, mul_one]
    symm
    apply sum_eq_zero
    intro n hn
    exact if_neg (fun h => (not_lt_of_ge h.2) h.1)
  | succ t ih =>
    rw [sum_range_succ, ih, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hp : y ≤ y * 2 ^ t := le_mul_of_one_le_right hy (one_le_pow₀ (by norm_num))
    rw [show y * 2 ^ (t + 1) = 2 * (y * 2 ^ t) by ring]
    by_cases h₁ : y < (n : ℝ) <;>
      by_cases h₂ : (n : ℝ) ≤ y * 2 ^ t <;>
        by_cases h₃ : (n : ℝ) ≤ 2 * (y * 2 ^ t) <;>
          simp_all <;> linarith

/-- Annuli above the cap are empty, so unused outer shells require no blocks.
This keeps the original cap in Tolev 1999 page 82 display 52. -/
theorem annularMangoldt_eq_zero (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ)
    (hx : (N : ℝ) ≤ x) : annularMangoldt lam l₃ K N α x = 0 := by
  apply sum_eq_zero
  intro n hn
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  exact if_neg (fun h => (not_lt_of_ge (hnN.trans hx)) h.1)

/-- The retained polynomial is the exact sum of doubled annuli once their upper
endpoint reaches N. This is the full interval completion of Tolev 1999 display 52. -/
theorem retainedMangoldt_eq_annuli (A : ℝ) (lam : ℕ → ℝ) (l₃ K N t : ℕ) (α : ℝ)
    (hcover : (N : ℝ) ≤ (N : ℝ) * Real.log N ^ (-4 * A) * 2 ^ t) :
    retainedMangoldt A lam l₃ K N α =
      ∑ j ∈ range t, annularMangoldt lam l₃ K N α
        ((N : ℝ) * Real.log N ^ (-4 * A) * 2 ^ j) := by
  unfold annularMangoldt
  rw [sum_doubled_annuli _ _ _ _ (by positivity)]
  unfold retainedMangoldt
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  simp only [and_iff_left (hnN.trans hcover)]

/-- The existing logarithmic shell bound also bounds the number of retained annuli.
Source: the six log factors on Heath Brown page 1367 gain one outer log factor. -/
theorem shell_count_le (N : ℕ) (hL : 1 ≤ Real.log N) :
    (Nat.clog 2 N : ℝ) ≤ (1 / Real.log 2 + 2) * Real.log N := by
  exact (show (Nat.clog 2 N : ℝ) ≤ (Nat.clog 2 N + 1 : ℝ) by norm_num).trans
    (Dyadic.block_count_le N N le_rfl hL)

/-- The retained lower endpoint eventually exceeds any fixed positive threshold.
This justifies applying the annular identity after removing the short initial segment.
Source: the full interval adaptation of Tolev 1999 page 82 display 52. -/
theorem eventual_retained_radius (A X₀ : ℝ) (hX : 1 ≤ X₀) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ Real.log N ∧ X₀ ≤ (N : ℝ) * Real.log N ^ (-4 * A) := by
  have hXpos : 0 < X₀ := by linarith
  have he := (isLittleO_log_rpow_rpow_atTop (4 * A) (by norm_num : (0 : ℝ) < 1)).bound
    (show (0 : ℝ) < 1 / X₀ by positivity)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp he
  refine ⟨max T (Real.exp 1), ?_⟩
  intro N hN
  have hNe : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := (Real.exp_pos 1).trans_le hNe
  have hL : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hLpos : 0 < Real.log N := by linarith
  have hb := hT (N : ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hLpos.le _), abs_of_pos hNpos] at hb
  have hb' : Real.log N ^ (4 * A) ≤ (N : ℝ) / X₀ := by
    convert hb using 1 <;> ring
  have hm := (le_div_iff₀ hXpos).mp hb'
  refine ⟨hL, ?_⟩
  rw [show -4 * A = -(4 * A) by ring, Real.rpow_neg hLpos.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)).mpr
  nlinarith

end LeanLab.Tolev2009.Decomp424b
