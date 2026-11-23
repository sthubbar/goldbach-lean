module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.BhowmikGrimmelt2026.UnitFibers436

/-!
Residue fiber identities in Montgomery Vaughan 1975 pages 359 and 360.
These finite identities preserve the frequency and the totient quotient.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Restrict a twisted character sum to units since every nonunit term vanishes.
Source: Montgomery Vaughan page 359, the restriction before display 5.3. -/
theorem cChi_units443 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℤ) :
    cChi χ N = ∑ a : (ZMod q)ˣ,
      χ a * ee ((N : ℝ) * ((a : ZMod q).val : ℝ) / q) := by
  classical
  unfold cChi
  simp only [mul_comm (N : ℝ)]
  symm
  apply Fintype.sum_of_injective (fun a : (ZMod q)ˣ => (a : ZMod q))
    Units.val_injective
    (fun a => χ a * ee (((a : ZMod q).val : ℝ) * N / q))
    (fun a => χ a * ee ((a.val : ℝ) * N / q)) ?_ (fun _ => rfl)
  intro a ha
  rw [MulChar.map_nonunit χ (fun hu => ha ⟨hu.unit, hu.unit_spec⟩), zero_mul]

/-- The additive phase descends when the modulus and frequency share the same factor.
Source: Montgomery Vaughan page 359, the first displayed equality. -/
theorem stdAddChar_factor443 {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (g : ℕ) (hq : q = m * g) (M : ℤ) (a : ZMod q) :
    ZMod.stdAddChar ((((g : ℤ) * M * (a.val : ℤ)) : ℤ) : ZMod q) =
      ZMod.stdAddChar ((M * (a.val : ℤ) : ℤ) : ZMod m) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hg : (g : ℂ) ≠ 0 := by
    have hg' : g ≠ 0 := by intro hg; simp [hg] at hq; exact NeZero.ne q hq
    exact_mod_cast hg'
  have hcq : (q : ℂ) = (m : ℂ) * (g : ℂ) := by exact_mod_cast hq
  rw [hcq]
  field_simp
  <;> ring

/-- Exact frequency reduction along unit residue fibers.
Source: Montgomery Vaughan page 360, the first displayed formula after Case 2. -/
theorem cChi_factor443 {m q : ℕ} [NeZero m] [NeZero q]
    (χ : DirichletCharacter ℂ m) (hd : m ∣ q)
    (g : ℕ) (hq : q = m * g) (M : ℤ) :
    cChi (DirichletCharacter.changeLevel hd χ) ((g : ℤ) * M) =
      ((Nat.totient q : ℂ) / (Nat.totient m : ℂ)) * cChi χ M := by
  rw [cChi_units443, cChi_units443]
  have hterm (a : (ZMod q)ˣ) :
      DirichletCharacter.changeLevel hd χ a *
          ee ((((g : ℤ) * M : ℤ) : ℝ) * ((a : ZMod q).val : ℝ) / q) =
        χ (ZMod.unitsMap hd a) *
          ee ((M : ℝ) * ((ZMod.unitsMap hd a : ZMod m).val : ℝ) / m) := by
    have hc : DirichletCharacter.changeLevel hd χ a = χ (ZMod.unitsMap hd a) := by
      simp [DirichletCharacter.changeLevel_def]
    rw [hc]
    congr 1
    have he := stdAddChar_factor443 hd g hq M (a : ZMod q)
    have hleft :
        ZMod.stdAddChar ((((g : ℤ) * M) * ((a : ZMod q).val : ℤ) : ℤ) : ZMod q) =
          ee (((((g : ℤ) * M : ℤ) : ℝ) * ((a : ZMod q).val : ℝ)) / q) := by
      rw [ZMod.stdAddChar_coe]
      unfold ee
      congr 1
      push_cast
      ring
    rw [hleft] at he
    have hcast : (((a : ZMod q).val : ℕ) : ZMod m) = (ZMod.unitsMap hd a : ZMod m) := by
      simp [ZMod.unitsMap_val]
    have hr : ZMod.stdAddChar ((M * ((a : ZMod q).val : ℤ) : ℤ) : ZMod m) =
        ee ((M : ℝ) * ((ZMod.unitsMap hd a : ZMod m).val : ℝ) / m) := by
      have hz : ((M * ((a : ZMod q).val : ℤ) : ℤ) : ZMod m) =
          ((M * ((ZMod.unitsMap hd a : ZMod m).val : ℤ) : ℤ) : ZMod m) := by
        push_cast
        rw [hcast, ZMod.natCast_zmod_val]
      rw [hz, ZMod.stdAddChar_coe]
      unfold ee
      congr 1
      push_cast
      ring
    exact he.trans hr
  simp_rw [hterm]
  exact unitsMap_sum436 hd (fun a : (ZMod m)ˣ =>
    χ a * ee ((M : ℝ) * ((a : ZMod m).val : ℝ) / m))

end LeanLab.BhowmikGrimmelt2026

