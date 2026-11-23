module

public import LeanLab.BhowmikGrimmelt2026.RouteCount508

/-!
The sealed sharp arc declarations now use the proved oscillatory route.
Source: P0029 pages 11 and 12 and page 15 display 4.6.
The sharp explicit formula remains a named conditional input.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 pages 11 and 12 displays 3.5 through 3.7 and page 15 display 4.6.
This auxiliary sharp estimate is beyond the smoothed centre estimate printed by the survey.
The zero modes retain their oscillatory Abel differences and analytic multiplicities.
The existing route count proof supplies the uniform oscillatory control.
The source gap QUESTION for the sharp route remains in PROGRESS.md. -/
theorem oscillatory_zero_modes508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
          ‖zeroTwist508 χ Z X β‖ ≤
            C * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * X) := by
  exact oscillatory_zero_modes508_route_count Θ hΘ hZ

/-- P0029 pages 11 and 12, displays 3.5 through 3.7, auxiliary sharp rational arc assembly.
CONDITIONAL on the displayed sharp character explicit formula. This estimates the oscillatory
zero modes and sharp residual on one rational arc before the Dirichlet dissection.
The square root frequency factor is retained. The survey states only the smoothed centre bound.
CONDITIONAL on oscillatory_zero_modes508 and the existing Hardy input for Theta at least one half. -/
theorem sharp_rational_arc508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    (hpsi : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt X → ∀ a : ℕ, Nat.Coprime a q →
      ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
        ‖Ssum X ((a : ℝ) / q + β) -
          ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β‖ ≤
        C * (X : ℝ) ^ (Θ + ε) *
          (Real.sqrt q * Real.sqrt (1 + |β| * X)) := by
  classical
  intro ε hε
  obtain ⟨Cψ, hCψ, hψ⟩ := hpsi
  obtain ⟨Cz, hCz, hz⟩ := oscillatory_zero_modes508 Θ hΘ hZ ε hε
  let K : ℝ := (2 / ε) ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : 1 / 2 ≤ Θ := zeroBound_lower150 hZ
  let A : ℝ := 10 * Real.pi * Cψ * K
  let E : ℝ := K / Real.log 2
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCψ) hK
  have hE : 0 ≤ E := div_nonneg hK hL.le
  refine ⟨Cz + A + E, by positivity, ?_⟩
  intro X hX q hq hqQ a ha β hβ
  haveI : NeZero q := ⟨by omega⟩
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hxp : 0 < (X : ℝ) := lt_of_lt_of_le zero_lt_one hx
  let W : ℝ := (X : ℝ) ^ (Θ + ε)
  let F : ℝ := Real.sqrt q * Real.sqrt (1 + |β| * X)
  have hW : 0 ≤ W := Real.rpow_nonneg hxp.le _
  have hF : 1 ≤ F := by
    have hsq : (1 : ℝ) ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by
      norm_num
      exact_mod_cast hq)
    have hsf : (1 : ℝ) ≤ Real.sqrt (1 + |β| * X) :=
      Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg X)])
    dsimp [F]
    nlinarith
  have hWF : W ≤ W * F := by nlinarith
  have hrem : Real.sqrt X * Real.log X ^ 2 ≤ K * W :=
    sqrt_log_power_budget508 hx hhalf hε
  have hlog : Real.log X ^ 2 ≤ K * W :=
    (log_sq_power_budget508 hx hε).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hK)
  have hunit : IsUnit ((a : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime a q).mpr ha
  have hb := sharp_rational_mode_reduction508 (a : ℤ) hunit
    (by omega : 1 ≤ X) hq hqQ hβ (mul_nonneg hCψ (sq_nonneg (Real.log X)))
    (mul_nonneg (mul_nonneg hCz hW) (Real.sqrt_nonneg (1 + |β| * X))) (by
      intro χ
      obtain ⟨T, hT, Z, hspec, hr⟩ := hψ X hX q hqQ χ
      refine ⟨Z, ?_, hz X hX q hqQ χ T hT Z hspec β hβ⟩
      intro n hnX
      by_cases hn : n = 0
      · rw [hn, sharp_remainder_zero508 χ Z (fun ρ hρ => ((hspec ρ).mp hρ).2.1)]
        simpa only [norm_zero] using mul_nonneg hCψ (sq_nonneg (Real.log X))
      · simpa only [sharpRemainder508, psiCharacter502, zeroPartial508, mul_div_assoc] using
          hr n (by omega) hnX)
  have hrb : 10 * Real.pi * (Cψ * Real.log X ^ 2) * Real.sqrt X ≤ A * (W * F) := by
    calc
      _ = (10 * Real.pi * Cψ) * (Real.sqrt X * Real.log X ^ 2) := by ring
      _ ≤ (10 * Real.pi * Cψ) * (K * W) := mul_le_mul_of_nonneg_left hrem
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCψ)
      _ = A * W := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWF hA
  have hlb : Real.log X ^ 2 / Real.log 2 ≤ E * (W * F) := by
    calc
      _ ≤ (K * W) / Real.log 2 := div_le_div_of_nonneg_right hlog hL.le
      _ = E * W := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWF hE
  have hc : Real.sqrt q * (Cz * W * Real.sqrt (1 + |β| * X)) = Cz * (W * F) := by
    dsimp [F]
    ring
  change _ ≤ (Cz + A + E) * W * F
  convert hb.trans (add_le_add (add_le_add (le_of_eq hc) hrb) hlb) using 1
  ring

/-- P0029 pages 11 and 12, the sharp route beyond displays 3.5 through 3.7.
CONDITIONAL on sharp_rational_arc508 and the displayed explicit formula.
The least denominator arc, canonical numerator and quarter power scale are assembled exactly.
This declaration is moved from Decomp504a with its sealed statement unchanged. -/
theorem major_arc_partial_summation504 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    (hpsi : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC, hlocal⟩ := sharp_rational_arc508 Θ hΘ hZ hpsi ε hε
  refine ⟨C * Real.sqrt 5, ?_⟩
  intro X hX α hα
  obtain ⟨q, hq, hαq⟩ := exists_arc502 (by omega : 1 ≤ X) α
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hqQ := (Finset.mem_Icc.mp hq).2
  haveI : NeZero q := ⟨by omega⟩
  let a : ℕ := (nint150 ((q : ℝ) * α)).toNat
  let β : ℝ := α - (a : ℝ) / q
  have haZ : (a : ℤ) = nint150 ((q : ℝ) * α) :=
    Int.toNat_of_nonneg (nint_mem150 (q := q) hα).1
  have har : (a : ℝ) = (nint150 ((q : ℝ) * α) : ℝ) := by exact_mod_cast haZ
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq1
  have hβq : (q : ℝ) * |β| = |(q : ℝ) * α - nint150 ((q : ℝ) * α)| := by
    calc
      _ = |(q : ℝ) * β| := by rw [abs_mul, abs_of_pos hqp]
      _ = _ := by
        congr 1
        dsimp [β]
        rw [har]
        field_simp
  have hb1 : |β| ≤ (1 / (Nat.sqrt X : ℝ)) / q :=
    (le_div_iff₀ hqp).mpr (by rw [mul_comm, hβq]; exact hαq.1)
  have hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) := by
    simpa only [div_div, mul_comm] using hb1
  have hcop : Nat.Coprime a q := assigned_coprime504 hq1 hα hαq
  have hV : VX150 X α =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β := by
    rw [VX_eq_arcTerm502 hq hαq]
    change ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) *
      TX150 X (α - (nint150 ((q : ℝ) * α) : ℝ) / q) = _
    rw [← har]
  have hh := hlocal X hX q hq1 hqQ a hcop β hβ
  have hαeq : (a : ℝ) / q + β = α := by dsimp [β]; ring
  rw [hαeq] at hh
  rw [hV]
  calc
    _ ≤ C * (X : ℝ) ^ (Θ + ε) *
        (Real.sqrt q * Real.sqrt (1 + |β| * X)) := hh
    _ ≤ C * (X : ℝ) ^ (Θ + ε) *
        (Real.sqrt 5 * (X : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (gauss_arc_scale508 (by omega) hq1 hqQ hβ) (by positivity)
    _ = _ := by
      have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
      have he : (X : ℝ) ^ (Θ + 1 / 4 + ε) =
          (X : ℝ) ^ (Θ + ε) * (X : ℝ) ^ (1 / 4 : ℝ) := by
        rw [show Θ + 1 / 4 + ε = (Θ + ε) + 1 / 4 by ring, Real.rpow_add hxp]
      rw [he]
      ring


end LeanLab.BhowmikGrimmelt2026
