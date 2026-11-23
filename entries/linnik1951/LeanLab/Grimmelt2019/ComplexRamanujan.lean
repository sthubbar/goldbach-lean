module

public import LeanLab.Grimmelt2019.Ramanujan

/-!
AI wrote this Lean code for CODEX task51.
P0074 pages 7 and 8, the exponential expansion in Lemma 3.1.
Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- Complex tests can be summed over units or over their natural representatives. -/
theorem sum_units_val_complex {q : ℕ} [NeZero q] (f : ℕ → ℂ) :
    ∑ u : (ZMod q)ˣ, f (u : ZMod q).val =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), f r := by
  classical
  refine Finset.sum_bij (fun u _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      ZMod.val_coe_unit_coprime u⟩
  · intro u hu v hv hval
    apply Units.ext
    exact ZMod.val_injective q hval
  · intro r hr
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hr
    let u := ZMod.unitOfCoprime r hc
    refine ⟨u, Finset.mem_univ _, ?_⟩
    change (r : ZMod q).val = r
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  · intro u hu
    rfl

/-- Integer frequencies are unchanged by reduction of the argument modulo q. -/
theorem e_emod {q : ℕ} (hq : 0 < q) (m n : ℤ) :
    LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * n / q) = LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * (n % q : ℤ) / q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hn : (n : ℝ) = (n % q : ℤ) + q * (n / q : ℤ) := by
    have hi : n = n % (q : ℤ) + (q : ℤ) * (n / q) := by
      nlinarith only [Int.emod_add_ediv_mul n (q : ℤ)]
    exact_mod_cast hi
  have he : (m : ℝ) * n / q = (m : ℝ) * (n % q : ℤ) / q +
      ((m * (n / q) : ℤ) : ℝ) := by
    rw [Int.cast_mul, hn]
    field_simp
  rw [he, e_add, e_int, mul_one]

/-- The complex Ramanujan sum is fixed by conjugation through residue negation. -/
theorem ram_sum_conj {q : ℕ} (hq : 0 < q) (m : ℤ) :
    (starRingEnd ℂ) (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * a / q)) =
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * a / q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp only [← sum_units_val_complex, map_sum]
  have he (u : (ZMod q)ˣ) :
      (starRingEnd ℂ) (LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * (u : ZMod q).val / q)) =
      LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * ((-u : (ZMod q)ˣ) : ZMod q).val / q) := by
    rw [← e_neg]
    have h := e_emod hq m (-(u : ZMod q).val)
    rw [← ZMod.val_intCast] at h
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg, neg_div,
      ZMod.natCast_zmod_val, Units.val_neg] using h
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.neg (ZMod q)ˣ)
    (fun u : (ZMod q)ˣ => LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * (u : ZMod q).val / q))

/-- The complex exponential definition equals the real cosine definition. -/
theorem ram_sum_eq (q : ℕ) (m : ℤ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * a / q)) = (ram q m : ℂ) := by
  by_cases hq : q = 0
  · subst q
    simp [ram]
  · have hc := ram_sum_conj (Nat.pos_of_ne_zero hq) m
    rw [ram_eq_re_sum]
    apply Complex.ext
    · simp
    · have hi := congrArg Complex.im hc
      simp only [Complex.conj_im] at hi
      simp only [Complex.ofReal_im]
      linarith

end LeanLab.Grimmelt2019.MainTerm
