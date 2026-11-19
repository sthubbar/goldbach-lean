module

public import Mathlib

/-!
P0082 J. Brüdern, A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), https://aif.centre-mersenne.org/item/10.5802/aif.1621.pdf,
read through a text extraction of the scan; QUESTIONs in STATEMENTS.md.

* Theorem 1: for 1 < γ < 3/2, the number E_γ(N) of n ≤ N such that
  |p₁ + p₂ − exp((log n)^γ)| < 1 has no solution in odd primes satisfies
  E_γ(N) ≪ N exp(−c (log N)^{3−2γ}) for some c > 0. Stated as the Prop `Theorem1`;
  the lab's cited form of it is not part of this copy, see PORTING.md.
* PROVED: Theorem 1 gives density zero; a solution gives an even Goldbach number,
  a sum of two odd primes, within distance 1 of exp((log n)^γ), and that even integer is unique,
  our reading of the paper's remark that almost all of its even neighbours ṽ_n are Goldbach
  numbers; the abstract itself says only for almost all n.
* Theorem 2, the exponential sum bound, is stated in `State1539Data264`.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.BrudernPerelli1998
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- `F γ x = exp((log x)^γ)`. -/
noncomputable def F (γ x : ℝ) : ℝ := Real.exp (Real.log x ^ γ)

/-- The inequality of Theorem 1 has a solution in odd primes. -/
def Solvable (γ : ℝ) (n : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ Odd p₁ ∧ Odd p₂ ∧ |((p₁ + p₂ : ℕ) : ℝ) - F γ n| < 1

/-- `Eγ γ N`, the number of `n` with `1 ≤ n ≤ N` for which the inequality has no solution. -/
noncomputable def Eγ (γ : ℝ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => ¬ Solvable γ n)).card

theorem Eγ_le (γ : ℝ) (N : ℕ) : Eγ γ N ≤ N := by
  unfold Eγ
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- Theorem 1 of the paper. -/
def Theorem1 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ))

/-- Theorem 1 gives density zero for each `γ` in the range. -/
theorem densityZero_of_theorem1 (h : Theorem1) {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    Tendsto (fun N : ℕ => (Eγ γ N : ℝ) / N) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC⟩ := h γ h1 h2
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => Real.log N ^ (3 - 2 * γ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlogN
  have hexp : Tendsto (fun N : ℕ => Real.exp (-c * Real.log N ^ (3 - 2 * γ))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun N : ℕ => -c * Real.log N ^ (3 - 2 * γ)) atTop atBot := by
      simpa [Function.comp_def, neg_mul] using
        tendsto_neg_atTop_atBot.comp (hpow.const_mul_atTop hc)
    exact Real.tendsto_exp_atBot.comp hneg
  have hup : Tendsto (fun N : ℕ => max C 0 * Real.exp (-c * Real.log N ^ (3 - 2 * γ)))
      atTop (𝓝 0) := by simpa using hexp.const_mul (max C 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    rw [div_le_iff₀ hNpos]
    calc (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := hC N hN
      _ ≤ max C 0 * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
          gcongr; exact le_max_left _ _
      _ = max C 0 * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) * N := by ring

/-- An open interval of length 2 holds at most one even integer. -/
theorem even_near_unique {x : ℝ} {m m' : ℤ} (hm : Even m) (hm' : Even m')
    (h : |(m : ℝ) - x| < 1) (h' : |(m' : ℝ) - x| < 1) : m = m' := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hm'
  have h1 := abs_lt.mp h
  have h2 := abs_lt.mp h'
  push_cast at h1 h2
  have hab1 : ((a : ℝ) - b) < 1 := by linarith
  have hab2 : ((b : ℝ) - a) < 1 := by linarith
  have e1 : a - b < 1 := by exact_mod_cast hab1
  have e2 : b - a < 1 := by exact_mod_cast hab2
  omega

/-- A solution gives an even integer within distance 1 of `F γ n` that is a sum of two odd
primes, and every even integer within distance 1 of `F γ n` is that one. -/
theorem goldbach_near_of_solvable {γ : ℝ} {n : ℕ} (h : Solvable γ n) :
    ∃ m : ℕ, Even m ∧ |(m : ℝ) - F γ n| < 1 ∧
      (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ Odd p₁ ∧ Odd p₂ ∧ p₁ + p₂ = m) ∧
      ∀ m' : ℤ, Even m' → |(m' : ℝ) - F γ n| < 1 → m' = m := by
  obtain ⟨p₁, p₂, hp₁, hp₂, ho₁, ho₂, hlt⟩ := h
  refine ⟨p₁ + p₂, ho₁.add_odd ho₂, hlt, ⟨p₁, p₂, hp₁, hp₂, ho₁, ho₂, rfl⟩, ?_⟩
  intro m' hm' hlt'
  have hev : Even ((p₁ + p₂ : ℕ) : ℤ) := by
    have := ho₁.add_odd ho₂
    exact (Int.even_coe_nat _).mpr this
  exact even_near_unique hm' hev hlt' (by exact_mod_cast hlt)

/-- So the `n ≤ N` whose even neighbour of `F γ n` fails to be a sum of two odd primes are
among the `Eγ γ N` exceptions. -/
theorem bad_neighbours_le (γ : ℝ) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n : ℕ => ¬ ∃ m : ℕ, Even m ∧ |(m : ℝ) - F γ n| < 1 ∧
      ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ Odd p₁ ∧ Odd p₂ ∧ p₁ + p₂ = m)).card ≤ Eγ γ N := by
  unfold Eγ
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, fun hs => hn.2 ?_⟩
  obtain ⟨m, hm, hlt, hg, -⟩ := goldbach_near_of_solvable hs
  exact ⟨m, hm, hlt, hg⟩

/-- `n = 1` is always an exception: `F γ 1 = 1` and no even sum of two odd primes lies in
`(0, 2)`. Harmless for Theorem 1. -/
theorem not_solvable_one (γ : ℝ) (hγ : 0 < γ) : ¬ Solvable γ 1 := by
  rintro ⟨p₁, p₂, hp₁, hp₂, -, -, h⟩
  have hF : F γ (1 : ℕ) = 1 := by
    simp [F, Real.zero_rpow hγ.ne']
  rw [hF] at h
  have h2 := (abs_lt.mp h).2
  have : (4 : ℝ) ≤ ((p₁ + p₂ : ℕ) : ℝ) := by
    have := hp₁.two_le; have := hp₂.two_le
    exact_mod_cast (by omega : 4 ≤ p₁ + p₂)
  linarith

theorem one_le_Eγ {γ : ℝ} (hγ : 0 < γ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Eγ γ N := by
  unfold Eγ
  apply Finset.card_pos.mpr
  exact ⟨1, by simp [Finset.mem_Icc, hN, not_solvable_one γ hγ]⟩

end LeanLab.ExceptionalSet.BrudernPerelli1998
