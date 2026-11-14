module

public import LeanLab.Linnik.Task37Display18

/-!
Li and Liu, https://arxiv.org/pdf/2610.15784, page 6, end of Proposition 3.2.
The diagonal residue density is the reciprocal order of 2.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Task37Diagonal
open Set Real Filter Finset Topology
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U1458Lemma42
open LeanLab.Linnik.U1464Display20
open LeanLab.Linnik.U1474R0

lemma good_one_one {d : ℕ} (hd : Odd d) (t s : Fin 1 → ℕ)
    (ht : t 0 < eps d) (hs : s 0 < eps d) : good d t s ↔ t = s := by
  have hf : IsOfFinOrder (2 : ZMod d) := orderOf_pos_iff.mp (eps_pos hd)
  simp only [good, Fin.sum_univ_one]
  constructor
  · intro h
    have hh := Nat.ModEq.add_right_cancel' 1 (hf.pow_inj_mod.mp h)
    change t 0 % eps d = s 0 % eps d at hh
    rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hs] at hh
    funext a
    have ha : a = 0 := Subsingleton.elim _ _
    simpa [ha] using hh
  · rintro rfl
    rfl

/-- The last finite identity in the proof of Proposition 3.2. -/
theorem Pd_one_one {d : ℕ} (hd : Odd d) : Pd d 1 1 = 1 / (eps d : ℝ) := by
  have he : (eps d : ℝ) ≠ 0 := by exact_mod_cast (eps_pos hd).ne'
  unfold Pd
  simp only [Fin.prod_univ_one]
  have inner (t : Fin 1 → ℕ) (ht : t ∈ Fintype.piFinset (fun _ : Fin 1 => range (eps d))) :
      (∑ s ∈ Fintype.piFinset (fun _ : Fin 1 => range (eps d)),
        (if good d t s then (1 : ℝ) else 0) * (1 / (eps d : ℝ)) * (1 / (eps d : ℝ))) =
        (1 / (eps d : ℝ)) * (1 / (eps d : ℝ)) := by
    rw [sum_eq_single_of_mem t ht]
    · simp [good]
    · intro s hs hst
      have hn : ¬ good d t s := by
        rw [good_one_one hd t s
          (mem_range.mp (Fintype.mem_piFinset.mp ht 0))
          (mem_range.mp (Fintype.mem_piFinset.mp hs 0))]
        exact Ne.symm hst
      simp [hn]
  rw [sum_congr rfl inner]
  simp only [sum_const, nsmul_eq_mul, Fintype.card_piFinset, Fin.prod_univ_one, card_range]
  field_simp

/-- The density B at the first diagonal is C0 times the Romanov series. -/
theorem Bdef_one_one : Bdef 0 0 = C0 * ∑' d : ℕ, wt d / (eps d : ℝ) := by
  unfold Bdef
  congr 1
  apply tsum_congr
  intro d
  change wt d * Pd d 1 1 = wt d / (eps d : ℝ)
  by_cases hd : Odd d
  · rw [Pd_one_one hd]
    simp [div_eq_mul_inv]
  · have hw : wt d = 0 := by simp [wt, hd]
    simp [hw]

/-- Display 20 now supplies the diagonal singular series upper bound without Prop32. -/
theorem singSum20 : SingSum20 (C0 * ∑' d : ℕ, wt d / (eps d : ℝ)) := by
  apply singSum20_of (display20_of_17 display17)
    (A := fun i j => Bdef i j - 1)
  · intro i j
    ring
  · rw [Bdef_one_one]

/-- A concrete odd modulus with order four. -/
theorem fifteen_instance : Pd 15 1 1 = 1 / 4 := by
  rw [Pd_one_one (by decide), wt_eps_instance.2]
  norm_num

end LeanLab.Linnik.Task37Diagonal

