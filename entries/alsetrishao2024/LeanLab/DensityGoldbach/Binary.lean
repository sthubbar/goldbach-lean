module

public import LeanLab.DensityGoldbach.Statements
public import LeanLab.ExceptionalSet.Statements

/-!
P0047 Alsetri-Shao 2024 Theorem 1.2 applied to all primes gives the classical "almost all
even numbers are Goldbach sums" of van der Corput, Chudakov and Estermann, as stated in
LeanLab.ExceptionalSet. Uses Dirichlet's theorem from Mathlib.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0092.
-/

@[expose] public section

open Finset Filter
open scoped Classical

namespace LeanLab.DensityGoldbach

/-- The primes have relative density `1` in every reduced class `b mod W`, by Dirichlet. -/
theorem lowerDensityRes_P (b W : ℕ) (hW : 0 < W) (hb : Nat.Coprime b W) :
    lowerDensityRes P b W = 1 := by
  obtain ⟨p, -, hp, hpb⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hW.ne' hb
  unfold lowerDensityRes
  have : (fun N : ℕ =>
      (#{n ∈ Icc 1 N | n ∈ P ∧ n.Prime ∧ n % W = b % W} : ℝ) /
        #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W}) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    refine eventually_atTop.2 ⟨p, fun N hN => ?_⟩
    dsimp only
    have h : #{n ∈ Icc 1 N | n ∈ P ∧ n.Prime ∧ n % W = b % W} =
        #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W} := by
      congr 1; ext n; simp [P]
    rw [h]
    have hpos : 0 < #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W} :=
      card_pos.2 ⟨p, mem_filter.2 ⟨mem_Icc.2 ⟨hp.one_lt.le, hN⟩, hp, hpb⟩⟩
    exact div_self (by exact_mod_cast hpos.ne')
  rw [liminf_congr this, liminf_const]

/-- **Alsetri-Shao Theorem 1.2 implies that almost all even numbers are Goldbach sums.** -/
theorem densityZero_of_alsetriShao (h : AlsetriShao12) : LeanLab.ExceptionalSet.DensityZero := by
  have ht := h P subset_rfl 1 (by norm_num)
    (fun W b hW hb => (lowerDensityRes_P b W hW hb).ge)
  unfold LeanLab.ExceptionalSet.DensityZero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun X => by positivity) (fun X => ?_)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold LeanLab.ExceptionalSet.E
  have : (Icc 4 X).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) ⊆
      {n ∈ Icc 1 X | Even n ∧ ¬ ∃ a ∈ P, ∃ b ∈ P, a + b = n} := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    refine ⟨⟨by omega, hn.1.2⟩, hn.2.1, ?_⟩
    rintro ⟨a, ha, b, hb, hab⟩
    exact hn.2.2 ⟨a, b, ha, hb, hab⟩
  refine Nat.cast_le.2 ?_
  convert card_le_card this using 2

end LeanLab.DensityGoldbach
