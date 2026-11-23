module

public import LeanLab.BhowmikGrimmelt2026.Decomp508a
public import LeanLab.PNTPort.DirichletZF.U1482Jensen

/-!
ROUTE for `oscillatory_zero_modes508`, part six: the right half of the window count
`zero_window_count508`, for every Dirichlet character including the principal ones.
Source: P0029, the survey of Bhowmik and Grimmelt, page 11 display 3.7, which uses the zero
count of Davenport, Multiplicative Number Theory, chapter 16, the zero count by Jensen's
formula, and chapter 9, the functional equation. This file covers the half `1/2 ≤ Re ρ < 1`
of the window, where the Jensen count of the lab port `U1482Jensen` applies directly; the
left half needs the functional equation and is not treated here.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.PNTPort.DirichletZF (Z Z_pos one_le_Z)
open LeanLab.PNTPort.DirichletZF.U1482 (RW rw_count_L rw_count_zeta)

/-- P0029 page 11 display 3.7, Davenport chapter 16: the Jensen count of zeros with
`1/2 ≤ Re ρ < 1` and ordinate within one half of `τ`, with multiplicity, for every character
of level `q`. A principal character is induced from the modulus one character, whose
`L` function is the Riemann zeta function, and inducing keeps strip zeros and
multiplicities. -/
theorem right_half_window_count508 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ)
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, ρ ∈ RW (DirichletCharacter.LFunction χ) τ) :
    ∑ ρ ∈ s, (mult χ ρ : ℝ) ≤
      Real.log (24 * Z * q * (|τ| + 4) ^ 2) / Real.log (7 / 6) := by
  by_cases hχ : χ = 1
  · have hd : 1 ∣ q := one_dvd q
    have hχ' : χ = DirichletCharacter.changeLevel hd (1 : DirichletCharacter ℂ 1) := by
      rw [hχ, DirichletCharacter.changeLevel_one]
    have hpos : ∀ ρ ∈ s, 0 < ρ.re ∧ ρ.re < 1 := by
      intro ρ hρ
      obtain ⟨-, h0, h1, -⟩ := hs ρ hρ
      exact ⟨by linarith, h1⟩
    have hsum : ∑ ρ ∈ s, (mult χ ρ : ℝ) =
        ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      obtain ⟨h0, h1⟩ := hpos ρ hρ
      rw [hχ', character_mult_changeLevel508 hd (1 : DirichletCharacter ℂ 1) h0 h1]
      unfold mult
      rw [DirichletCharacter.LFunction_modOne_eq]
    have hmem : ∀ ρ ∈ s, ρ ∈ RW riemannZeta τ := by
      intro ρ hρ
      obtain ⟨hz, h0, h1, hi⟩ := hs ρ hρ
      obtain ⟨hp0, hp1⟩ := hpos ρ hρ
      refine ⟨?_, h0, h1, hi⟩
      rw [hχ'] at hz
      have := (character_zero_changeLevel508 hd (1 : DirichletCharacter ℂ 1) hp0 hp1).mp hz
      rwa [DirichletCharacter.LFunction_modOne_eq] at this
    rw [hsum]
    refine ((rw_count_zeta τ).2 s hmem).trans ?_
    have hZ := Z_pos
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hl : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
    apply div_le_div_of_nonneg_right _ hl.le
    apply Real.log_le_log (by positivity)
    have hp : (0 : ℝ) ≤ 24 * Z * (|τ| + 4) ^ 2 := by positivity
    nlinarith
  · exact (rw_count_L hχ τ).2 s hs

/-- Absorbing the Jensen bound into a multiple of `log (q (|t| + 2))`, using `1 ≤ q` and
`2 ≤ q (|t| + 2)`. Arithmetic behind P0029 page 11 display 3.7. -/
theorem right_window_absorb508 {q : ℕ} [NeZero q] {t τ : ℝ} (hτ : |τ| ≤ |t| + 1 / 2) :
    Real.log (24 * Z * q * (|τ| + 4) ^ 2) / Real.log (7 / 6) ≤
      ((Real.log (216 * Z) / Real.log 2 + 2) / Real.log (7 / 6)) *
        Real.log ((q : ℝ) * (|t| + 2)) := by
  have hZ1 := one_le_Z
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ht := abs_nonneg t
  have hτ0 := abs_nonneg τ
  have hl : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set x : ℝ := (q : ℝ) * (|t| + 2) with hx
  have hx2 : 2 ≤ x := by nlinarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hlZ : 0 ≤ Real.log (216 * Z) := Real.log_nonneg (by linarith)
  have hle : 24 * Z * q * (|τ| + 4) ^ 2 ≤ 216 * Z * x ^ 2 := by
    have h1 : (|τ| + 4) ^ 2 ≤ (3 * (|t| + 2)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (q : ℝ) * (|τ| + 4) ^ 2 ≤ 9 * x ^ 2 := by
      have h3 : (q : ℝ) * (|τ| + 4) ^ 2 ≤ (q : ℝ) * (3 * (|t| + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h4 : (q : ℝ) * (3 * (|t| + 2)) ^ 2 ≤ (q : ℝ) ^ 2 * (3 * (|t| + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      have h5 : (q : ℝ) ^ 2 * (3 * (|t| + 2)) ^ 2 = 9 * x ^ 2 := by rw [hx]; ring
      linarith
    have h6 : 24 * Z * q * (|τ| + 4) ^ 2 = 24 * Z * ((q : ℝ) * (|τ| + 4) ^ 2) := by ring
    rw [h6]
    have : 24 * Z * ((q : ℝ) * (|τ| + 4) ^ 2) ≤ 24 * Z * (9 * x ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have hlog : Real.log (24 * Z * q * (|τ| + 4) ^ 2) ≤
      (Real.log (216 * Z) / Real.log 2 + 2) * Real.log x := by
    calc Real.log (24 * Z * q * (|τ| + 4) ^ 2) ≤ Real.log (216 * Z * x ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log (216 * Z) + 2 * Real.log x := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; norm_num
      _ ≤ Real.log (216 * Z) / Real.log 2 * Real.log x + 2 * Real.log x := by
          have : Real.log (216 * Z) = Real.log (216 * Z) / Real.log 2 * Real.log 2 := by
            field_simp
          have h7 : Real.log (216 * Z) / Real.log 2 * Real.log 2 ≤
              Real.log (216 * Z) / Real.log 2 * Real.log x :=
            mul_le_mul_of_nonneg_left hlx (by positivity)
          linarith
      _ = (Real.log (216 * Z) / Real.log 2 + 2) * Real.log x := by ring
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hlog hl.le

/-- P0029 page 11 display 3.7, the right half of the zero count that the survey uses without
stating it, from Davenport, Multiplicative Number Theory, chapter 16: the zeros of
`L (s, χ)` with `1/2 ≤ Re ρ < 1` and ordinate within one of `t`, counted with multiplicity,
number at most a constant times `log (q (|t| + 2))`. Every character is covered, principal
or not. The window of half width one is split at `t` into two windows of half width one
half, each counted by Jensen's formula. -/
theorem right_window_count508 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
      (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧
        |ρ.im - t| ≤ 1) →
      ∑ ρ ∈ Z, (mult χ ρ : ℝ) ≤ A * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hZ1 := one_le_Z
  have hl : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlZ : 0 ≤ Real.log (216 * LeanLab.PNTPort.DirichletZF.Z) :=
    Real.log_nonneg (by linarith)
  refine ⟨2 * ((Real.log (216 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2) /
    Real.log (7 / 6)), by positivity, ?_⟩
  intro q _ χ t S hS
  have h1 : ∑ ρ ∈ S with ρ.im ≤ t, (mult χ ρ : ℝ) ≤
      ((Real.log (216 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2) /
        Real.log (7 / 6)) * Real.log ((q : ℝ) * (|t| + 2)) := by
    refine (right_half_window_count508 χ (t - 1 / 2) _ ?_).trans
      (right_window_absorb508 ?_)
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, hi⟩ := hS ρ hρ.1
      refine ⟨hz, h0, h1, ?_⟩
      have := abs_le.mp hi
      rw [abs_le]; constructor <;> linarith [hρ.2]
    · have := abs_sub t (1 / 2)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      exact this
  have h2 : ∑ ρ ∈ S with ¬ ρ.im ≤ t, (mult χ ρ : ℝ) ≤
      ((Real.log (216 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2) /
        Real.log (7 / 6)) * Real.log ((q : ℝ) * (|t| + 2)) := by
    refine (right_half_window_count508 χ (t + 1 / 2) _ ?_).trans
      (right_window_absorb508 ?_)
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, hi⟩ := hS ρ hρ.1
      refine ⟨hz, h0, h1, ?_⟩
      have := abs_le.mp hi
      have h3 := not_le.mp hρ.2
      rw [abs_le]; constructor <;> linarith
    · have := abs_add_le t (1 / 2)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      exact this
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ => ρ.im ≤ t)
    (fun ρ => (mult χ ρ : ℝ))
  linarith

end LeanLab.BhowmikGrimmelt2026
