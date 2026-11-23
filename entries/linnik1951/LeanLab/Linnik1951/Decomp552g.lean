module

public import LeanLab.Linnik1951.Supply470

/-!
P0093 page 160 equation 5.4. Finite character energy with the principal
coefficient removed. The Mellin estimate remains a separate input.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset

/-- P0093 page 160 equation 5.4. On functions supported on units,
the principal character coefficient is the ordinary finite sum. -/
theorem principal_character_sum552 (q : ℕ) [NeZero q] (G : ZMod q → ℂ)
    (hG : ∀ b, ¬ IsUnit b → G b = 0) :
    (∑ b : ZMod q, (1 : DirichletCharacter ℂ q) b * G b) = ∑ b : ZMod q, G b := by
  apply sum_congr rfl
  intro b hb
  by_cases hunit : IsUnit b
  · rw [MulChar.one_apply hunit, one_mul]
  · rw [hG b hunit, mul_zero]

/-- P0093 page 160 equation 5.4. Removing the principal coefficient
from the finite Parseval identity subtracts exactly its squared norm. -/
theorem nonprincipal_parseval552 (q : ℕ) [NeZero q] (G : ZMod q → ℂ)
    (hG : ∀ b, ¬ IsUnit b → G b = 0) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖∑ b : ZMod q, χ b * G b‖ ^ 2) =
      (q.totient : ℝ) * (∑ b : ZMod q, if IsUnit b then ‖G b‖ ^ 2 else 0) -
        ‖∑ b : ZMod q, G b‖ ^ 2 := by
  classical
  have hp := LeanLab.PNTPort.LargeSieve.sum_chars_normSq G
  have he := Finset.add_sum_erase (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => ‖∑ b : ZMod q, χ b * G b‖ ^ 2) (mem_univ (1 : DirichletCharacter ℂ q))
  have hf : (univ : Finset (DirichletCharacter ℂ q)).erase 1 =
      univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) := by
    ext χ
    simp
  rw [hf, principal_character_sum552 q G hG] at he
  linarith

/-- P0093 page 160 equation 5.4. When the principal coefficient is
zero, the restricted additive transform is bounded by q over phi q
times the sum of the nonprincipal squared coefficients. This is finite
character algebra only. No Mellin or prime estimate is assumed. -/
theorem zero_mean_gauss_energy552 (q : ℕ) [NeZero q] (G : ZMod q → ℂ)
    (hG : ∀ b, ¬ IsUnit b → G b = 0) (hzero : ∑ b : ZMod q, G b = 0) :
    (∑ a : ZMod q, if IsUnit a then
      ‖∑ b : ZMod q, ZMod.stdAddChar (-(b * a)) * G b‖ ^ 2 else 0) ≤
      (q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ b : ZMod q, χ b * G b‖ ^ 2 := by
  classical
  rw [unit_transform_energy470 q G hG]
  have hz : ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ^ 2 *
      ‖∑ b : ZMod q, (1 : DirichletCharacter ℂ q) b * G b‖ ^ 2 = 0 := by
    rw [principal_character_sum552 q G hG, hzero]
    simp
  have he := Finset.add_sum_erase (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * ‖∑ b : ZMod q, χ b * G b‖ ^ 2)
    (mem_univ (1 : DirichletCharacter ℂ q))
  have hf : (univ : Finset (DirichletCharacter ℂ q)).erase 1 =
      univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) := by
    ext χ
    simp
  rw [hf, hz, zero_add] at he
  rw [← he]
  calc
    _ ≤ (1 / (q.totient : ℝ)) *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          (q : ℝ) * ‖∑ b : ZMod q, χ b * G b‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro χ hχ
      have hg : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤ (q : ℝ) := by
        simpa only [residue_gauss_eq470] using residue_gauss_sq_le470 q χ
      exact mul_le_mul_of_nonneg_right hg (sq_nonneg _)
    _ = _ := by rw [← mul_sum]; ring


/-- P0093 page 160 equation 5.4. Subtracting the exact unit mean
removes the principal character before applying the finite Gauss energy
bound. Every nonprincipal coefficient is preserved. This is the finite
projection step only, with no analytic hypothesis. -/
theorem centered_gauss_energy552 (q : ℕ) [NeZero q] (G : ZMod q → ℂ)
    (hG : ∀ b, ¬ IsUnit b → G b = 0) :
    (∑ a : ZMod q, if IsUnit a then
      ‖∑ b : ZMod q, ZMod.stdAddChar (-(b * a)) *
        (G b - (1 : DirichletCharacter ℂ q) b *
          ((∑ c : ZMod q, G c) / (q.totient : ℂ)))‖ ^ 2 else 0) ≤
      (q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ b : ZMod q, χ b * G b‖ ^ 2 := by
  classical
  let m : ℂ := (∑ c : ZMod q, G c) / (q.totient : ℂ)
  let C : ZMod q → ℂ := fun b => G b - (1 : DirichletCharacter ℂ q) b * m
  have hC : ∀ b, ¬ IsUnit b → C b = 0 := by
    intro b hb
    simp [C, hG b hb, MulChar.map_nonunit _ hb]
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hone : (∑ b : ZMod q, (1 : DirichletCharacter ℂ q) b) = (q.totient : ℂ) := by
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  have hzero : (∑ b : ZMod q, C b) = 0 := by
    simp only [C, sum_sub_distrib, ← sum_mul, hone]
    dsimp [m]
    field_simp [hφ]
    ring
  have hcoeff (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
      (∑ b : ZMod q, χ b * C b) = ∑ b : ZMod q, χ b * G b := by
    have hmul (b : ZMod q) : χ b * (1 : DirichletCharacter ℂ q) b = χ b := by
      by_cases hb : IsUnit b
      · rw [MulChar.one_apply hb, mul_one]
      · rw [MulChar.map_nonunit χ hb, zero_mul]
    calc
      _ = (∑ b : ZMod q, χ b * G b) - (∑ b : ZMod q,
          χ b * (1 : DirichletCharacter ℂ q) b) * m := by
        simp only [C, mul_sub, sum_sub_distrib, sum_mul, mul_assoc]
      _ = _ := by simp_rw [hmul]; rw [MulChar.sum_eq_zero_of_ne_one hχ]; simp
  calc
    _ ≤ (q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ b : ZMod q, χ b * C b‖ ^ 2 := zero_mean_gauss_energy552 q C hC hzero
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro χ hχ
      rw [hcoeff χ (mem_filter.mp hχ).2]

end LeanLab.Linnik1951
