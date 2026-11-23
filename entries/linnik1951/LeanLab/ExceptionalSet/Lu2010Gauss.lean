module

public import Mathlib
public import LeanLab.Routes.R0001Parseval

/-!
P0095 Lu 2010, equation 63 on page 2379 and equation 86 on page 2392.
CODEX task47, unit U-8090. AI wrote this Lean code. Binary Goldbach is open.

Complete-period mean squares of the generalized Gauss sums in equation 63.
These identities do not discharge equation 86 or define its zero sum.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.Lu2010Gauss
open Finset ZMod

variable {q : ℕ} [NeZero q]

/-- Lu's generalized Gauss sum with the positive additive sign. -/
noncomputable def G (χ : DirichletCharacter ℂ q) (k : ZMod q) : ℂ :=
  ∑ a : ZMod q, χ a * stdAddChar (a * k)

theorem G_eq_dft (χ : DirichletCharacter ℂ q) (k : ZMod q) :
    G χ k = 𝓕 (fun a => χ a) (-k) := by
  simp only [G, dft_apply, smul_eq_mul, mul_neg, neg_neg]
  apply sum_congr rfl
  intro a _
  ring

theorem character_energy (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ‖χ a‖ ^ 2 = (q.totient : ℝ) := by
  have h : ∀ a : ZMod q, ‖χ a‖ ^ 2 = (1 : DirichletCharacter ℝ q) a := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      simp
    · rw [χ.map_nonunit ha, (1 : DirichletCharacter ℝ q).map_nonunit ha]
      simp
  simp_rw [h]
  rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

/-- Complete-period mean square, also for imprimitive characters. -/
theorem G_energy (χ : DirichletCharacter ℂ q) :
    ∑ k : ZMod q, ‖G χ k‖ ^ 2 = (q : ℝ) * q.totient := by
  simp_rw [G_eq_dft]
  rw [Fintype.sum_equiv (Equiv.neg (ZMod q)) (fun k => ‖𝓕 (fun a => χ a) (-k)‖ ^ 2) (fun k => ‖𝓕 (fun a => χ a) k‖ ^ 2) (fun k => by simp),
    LeanLab.Routes.R0001.dft_parseval_norm, character_energy]

/-- The Gauss sum as Mathlib's multiplicative and additive character pairing. -/
theorem G_eq_gaussSum (χ : DirichletCharacter ℂ q) (k : ZMod q) :
    G χ k = gaussSum χ (stdAddChar.mulShift k) := by
  simp only [G, gaussSum, AddChar.mulShift_apply]
  apply sum_congr rfl
  intro a _
  rw [mul_comm a k]

/-- Primitive character twisting, with the positive sign convention. -/
theorem G_primitive (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (k : ZMod q) :
    G χ k = χ⁻¹ k * G χ 1 := by
  rw [G_eq_gaussSum, gaussSum_mulShift_of_isPrimitive _ hχ]
  congr 1
  simp [G_eq_gaussSum]

/-- The squared norm of a primitive Gauss sum is its conductor. -/
theorem primitive_gauss_norm_sq (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖G χ 1‖ ^ 2 = (q : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have h := G_energy χ
  have he : (∑ k : ZMod q, ‖G χ k‖ ^ 2) =
      ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 * ‖G χ 1‖ ^ 2 := by
    apply sum_congr rfl
    intro k _
    rw [G_primitive χ hχ k, norm_mul, mul_pow]
  rw [he, ← sum_mul, character_energy] at h
  nlinarith

/-- One modulus in equation 63, with both Gauss factors collected in z. -/
noncomputable def kernel (χ : DirichletCharacter ℂ q) (z : ℂ) (k : ZMod q) : ℂ :=
  z * G χ (-k) / (q.totient : ℂ) ^ 2

theorem kernel_energy (χ : DirichletCharacter ℂ q) (z : ℂ) :
    ∑ k : ZMod q, ‖kernel χ z k‖ ^ 2 =
      ‖z‖ ^ 2 * (q : ℝ) / (q.totient : ℝ) ^ 3 := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [kernel, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    div_pow, mul_pow]
  rw [show (∑ k : ZMod q, ‖z‖ ^ 2 * ‖G χ (-k)‖ ^ 2 / ((q.totient : ℝ) ^ 2) ^ 2) =
      ‖z‖ ^ 2 / (q.totient : ℝ) ^ 4 * ∑ k : ZMod q, ‖G χ (-k)‖ ^ 2 by
        rw [mul_sum]; apply sum_congr rfl; intro k _; ring]
  rw [Fintype.sum_equiv (Equiv.neg (ZMod q)) (fun k => ‖G χ (-k)‖ ^ 2) (fun k => ‖G χ k‖ ^ 2) (fun k => by simp), G_energy]
  field_simp

/-- The average has the inverse modulus saving if the two Gauss factors have norm at most q. -/
theorem kernel_mean_le (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ (q : ℝ) ^ 2) :
    (∑ k : ZMod q, ‖kernel χ z k‖ ^ 2) / q ≤
      ((q : ℝ) / q.totient) ^ 3 / q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [kernel_energy]
  calc (‖z‖ ^ 2 * (q : ℝ) / (q.totient : ℝ) ^ 3) / q
      ≤ (((q : ℝ) ^ 2 * q) / (q.totient : ℝ) ^ 3) / q := by gcongr
    _ = ((q : ℝ) / q.totient) ^ 3 / q := by field_simp

/-- The r of Lemma 22 is not the least common multiple of the conductors. -/
theorem diagonal_conductor_ratio (m : ℕ) (hm : 0 < m) :
    Nat.lcm m m / Nat.gcd m m = 1 := by
  simpa only [Nat.lcm_self, Nat.gcd_self] using Nat.div_self hm

theorem vacuity_G_energy :
    ∑ k : ZMod 2, ‖G (1 : DirichletCharacter ℂ 2) k‖ ^ 2 = 2 := by
  rw [G_energy]
  norm_num

end LeanLab.ExceptionalSet.Lu2010Gauss
