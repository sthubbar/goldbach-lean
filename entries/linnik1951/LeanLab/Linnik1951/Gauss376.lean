module

public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
P0093 page 156 Lemma 1. The primitive case of the cited Gauss sum norm.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 156 Lemma 1 with conductor equal to the modulus.
The proved PNTPort square norm identity gives the primitive Gauss norm. -/
theorem primitive_gauss_norm376 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  rw [← LeanLab.PNTPort.LargeSieve.normSq_gaussSum_of_isPrimitive hχ,
    Real.sqrt_sq (norm_nonneg _)]

/-- P0093 page 156 Lemma 1. The principal character modulo one is
primitive and its Gauss sum has norm one. This supplies a concrete
instance for primitive_gauss_norm376. -/
theorem primitive_gauss_one376 :
    ‖gaussSum (1 : DirichletCharacter ℂ 1) ZMod.stdAddChar‖ = 1 := by
  simpa using primitive_gauss_norm376 (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one

end LeanLab.Linnik1951
