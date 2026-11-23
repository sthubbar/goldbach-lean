module

public import LeanLab.Perelli1996.Statements

/-!
P0083, page 488, equation 35. Root counts with repeated factors.
This records a QUESTION about the unrestricted printed root bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Roots
open Finset Polynomial Real
noncomputable section

/-- The integer representatives for the roots modulo d. -/
def rootResidues (F : ℤ[X]) (d : ℕ) : Finset ℕ :=
  (range d).filter (fun n => (d : ℤ) ∣ F.eval (n : ℤ))

/-- The literal unrestricted root growth assertion printed in equation 35. -/
def PrintedRootGrowth (F : ℤ[X]) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, 1 ≤ d → ((rootResidues F d).card : ℝ) ≤ C * (d : ℝ) ^ ε

/-- The representative count agrees with the folder's ZMod root count. -/
theorem card_rootResidues_eq_rho (F : ℤ[X]) (d : ℕ) [NeZero d] :
    (rootResidues F d).card = rho F d := by
  classical
  have hev (n : ℕ) : (F.map (Int.castRingHom (ZMod d))).eval (n : ZMod d) =
      ((F.eval (n : ℤ) : ℤ) : ZMod d) := by
    simpa using Polynomial.eval_intCast_map (Int.castRingHom (ZMod d)) F (n : ℤ)
  unfold rho
  apply Finset.card_bij (fun (n : ℕ) _ => (n : ZMod d))
  · intro n hn
    simp only [rootResidues, mem_filter, mem_range] at hn
    simp only [mem_filter, mem_univ, true_and, hev]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hn.2
  · intro n hn m hm heq
    have hnlt : n < d := (Finset.mem_filter.mp hn).1 |> Finset.mem_range.mp
    have hmlt : m < d := (Finset.mem_filter.mp hm).1 |> Finset.mem_range.mp
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt hnlt, ZMod.val_natCast_of_lt hmlt] using hv
  · intro z hz
    refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
    simp only [mem_filter, mem_univ, true_and] at hz
    simp only [rootResidues, mem_filter, mem_range]
    refine ⟨ZMod.val_lt z, ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    rw [← hev, ZMod.natCast_zmod_val]
    exact hz

/-- Every multiple of m below m squared is a root of X squared modulo m squared. -/
theorem square_roots_lower (m : ℕ) (hm : 0 < m) :
    m ≤ (rootResidues (X ^ 2 : ℤ[X]) (m ^ 2)).card := by
  have hi : Function.Injective (fun j : ℕ => m * j) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hm h
  have hsub : (range m).image (fun j => m * j) ⊆
      rootResidues (X ^ 2 : ℤ[X]) (m ^ 2) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    simp only [rootResidues, mem_filter, mem_range, eval_pow, eval_X]
    constructor
    · simpa only [pow_two] using Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hm
    · refine ⟨(j : ℤ) ^ 2, ?_⟩
      push_cast
      ring
  calc m = ((range m).image (fun j => m * j)).card := by
        rw [Finset.card_image_of_injective _ hi, card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-- The unrestricted printed root estimate fails for X squared. This is a QUESTION. -/
theorem not_printedRootGrowth_square : ¬ PrintedRootGrowth (X ^ 2 : ℤ[X]) := by
  intro h
  obtain ⟨C, hC, hb⟩ := h (1 / 4) (by norm_num)
  let n : ℕ := ⌈C⌉₊ + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCn : C < n := by
    have hceil := Nat.le_ceil C
    dsimp [n]
    push_cast
    linarith
  have hl := square_roots_lower (n ^ 2) (pow_pos hn 2)
  have hlR : (n : ℝ) ^ 2 ≤ (rootResidues (X ^ 2 : ℤ[X]) ((n ^ 2) ^ 2)).card := by
    exact_mod_cast hl
  have hpow : (((n ^ 2) ^ 2 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) := by
    have heq : (((n ^ 2) ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 4 := by push_cast; ring
    rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hu := hb ((n ^ 2) ^ 2) (by have hh := pow_pos (pow_pos hn 2) 2; omega)
  rw [hpow] at hu
  nlinarith

/-- On squarefree moduli X squared has exactly one root, namely zero. -/
theorem squarefree_square_roots {d : ℕ} (hd : Squarefree d) :
    (rootResidues (X ^ 2 : ℤ[X]) d).card = 1 := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hset : rootResidues (X ^ 2 : ℤ[X]) d = {0} := by
    ext n
    simp only [rootResidues, mem_filter, mem_range, eval_pow, eval_X, mem_singleton]
    constructor
    · rintro ⟨hn, hdiv⟩
      have hdivNat : d ∣ n ^ 2 := by
        apply Int.natCast_dvd_natCast.mp
        simpa only [Nat.cast_pow] using hdiv
      have hnDiv : d ∣ n := (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hdivNat
      exact Nat.eq_zero_of_dvd_of_lt hnDiv hn
    · rintro rfl
      exact ⟨hd0, by simp⟩
  rw [hset, Finset.card_singleton]

end
end LeanLab.Perelli1996.Roots
