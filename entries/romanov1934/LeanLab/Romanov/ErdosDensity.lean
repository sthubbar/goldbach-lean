module

public import LeanLab.Romanov.PositiveK
public import LeanLab.Romanov.Erdos

/-!
# Romanov and Erdős together: both the numbers p + 2^k and the odd numbers that are not of that
form have positive lower density

Unit U-1083, PC run 20261019T1603Z-20267. AI wrote the Lean code. Known mathematics, Romanov 1934,
Erdős 1950. No cited input. Binary Goldbach is OPEN. This is the covering barrier of ROUTES R-5063
in density form: the p + 2^k analogue of Goldbach fails on a positive proportion of odd numbers.

* `erdos_density`: for `x ≥ 4 · 346729110`, at least `x/(2 · 346729110)` odd numbers below `x`
  are not `p + 2^k` for any prime `p` and `k ≥ 0`. PROVED.
* `romanov_erdos`: positive lower density for the `p + 2^k`, `k ≥ 1`, and for the odd non-sums,
  together. PROVED.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset

/-- **Erdős in density form.** -/
theorem erdos_density : ∀ x : ℕ, 4 * 346729110 ≤ x → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < x ∧ Odd n ∧ ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k) ∧
    (1 / (2 * 346729110) : ℝ) * x ≤ #I := by
  intro x hx
  set m := x / 346729110 - 1 with hm
  refine ⟨(range m).image (fun t => 119477317 + 346729110 * t), fun n hn => ?_, ?_⟩
  · rw [mem_image] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    rw [mem_range] at ht
    refine ⟨by omega, erdos_odd_not_sum t⟩
  · rw [card_image_of_injective _ (fun a b hab => by omega), card_range]
    have h : x ≤ 2 * 346729110 * m := by omega
    have h' : (x : ℝ) ≤ 2 * 346729110 * m := by exact_mod_cast h
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by norm_num)]
    linarith

/-- **Romanov and Erdős**: the numbers `p + 2^k`, `k ≥ 1`, and the odd numbers that are no
`p + 2^k`, `k ≥ 0`, both have positive lower density. -/
theorem romanov_erdos : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    (∃ I : Finset ℕ, (∀ n ∈ I, n < x ∧ ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 ^ k) ∧ c * x ≤ #I) ∧
    (∃ J : Finset ℕ, (∀ n ∈ J, n < x ∧ Odd n ∧ ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k) ∧
      c * x ≤ #J) := by
  obtain ⟨c, hc, X₁, h⟩ := romanov_pos
  refine ⟨min c (1 / (2 * 346729110)), lt_min hc (by norm_num), max X₁ (4 * 346729110),
    fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨I, hI, hcard⟩ := h x (le_of_max_le_left hx)
    refine ⟨I, hI, le_trans ?_ hcard⟩
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  · obtain ⟨J, hJ, hcard⟩ := erdos_density x (le_of_max_le_right hx)
    refine ⟨J, hJ, le_trans ?_ hcard⟩
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)

end LeanLab.Romanov
