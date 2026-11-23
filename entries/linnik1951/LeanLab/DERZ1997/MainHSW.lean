module

public import LeanLab.DERZ1997.Lemma
public import LeanLab.PNTPort.ExplicitPsi1.ThetaSchoenfeldLarge

/-!
# P0011 DERZ 1997 without Schoenfeld's Corollary 1

Unit U-6660, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics.

`derz_main_of_cor1` takes Schoenfeld 1976 Corollary 1, `|θ(u) - u| ≤ √u log² u/(8π)` for
`u ≥ 599`, as a cited input, but `cor1_uniform` uses it only on `10^11 ≤ u ≤ 10^20`, where the
lab now proves it, `theta_schoenfeld_large`, under RH from the Hasanalizade-Shen-Wong `N(T)`
counts and `Ordinates14`. Here:
* `rh_of_strip` and `rh_of_GRH`: P0011's `GRH`, at `q = 1`, gives Mathlib's `RiemannHypothesis`,
  the zeros off the strip being handled by the functional equation;
* `cor1_uniform_hsw`: the `843842 · 10^6` bound on `[10^11, 10^20]` under RH;
* `derz_main_of_hsw`: GRH implies ternary Goldbach, CONDITIONAL ON Zinoviev's `10^20` bound, the
  `10^13` even check, and the zero-count inputs `HSWN70`, `HSWHead14`, `Ordinates14`, with no
  Schoenfeld input. Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.DERZ1997
open Real Chebyshev
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ theta_schoenfeld_large)
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)

/-- Zeros in the open strip on the line give Mathlib's `RiemannHypothesis`. -/
theorem rh_of_strip (h : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz hnt hs1
  rcases lt_or_ge 0 s.re with hpos | hneg
  · rcases lt_or_ge s.re 1 with hlt | hge
    · exact h s hz hpos hlt
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge)
  · exfalso
    set w := 1 - s with hw
    have hwre : 1 ≤ w.re := by simp [hw]; linarith
    have hs : s = 1 - w := by rw [hw]; ring
    have hw1 : w ≠ 1 := by
      intro h1
      have : s = 0 := by rw [hs, h1]; ring
      rw [this, riemannZeta_zero] at hz; norm_num at hz
    have hwn : ∀ n : ℕ, w ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hwn hw1
    rw [← hs, hz] at hfe
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hpi : (2 * (π : ℂ)) ^ (-w) ≠ 0 := by
      have h2p : (2 * (π : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl h2p)
    have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hcos : Complex.cos (π * w / 2) = 0 := by
      by_contra hc
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpi) hG) hc) hzw) hfe.symm
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hpi0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hwk : w = 2 * k + 1 := by
      have := hk
      field_simp at this
      exact this
    have hsk : s = -(2 * (k : ℂ)) := by rw [hs, hwk]; ring
    have hkre := congrArg Complex.re hsk
    simp at hkre
    have hk0 : 0 ≤ k := by
      have : (0 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hk1 : k ≠ 0 := by
      rintro rfl
      have : s = 0 := by rw [hsk]; simp
      rw [this, riemannZeta_zero] at hz; norm_num at hz
    apply hnt
    refine ⟨(k - 1).toNat, ?_⟩
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    rw [hsk]
    have : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by exact_mod_cast this
    rw [this]; ring

/-- P0011's `GRH` gives Mathlib's `RiemannHypothesis`, through `q = 1`. -/
theorem rh_of_GRH (hG : GRH) : RiemannHypothesis := by
  apply rh_of_strip
  intro s hz h0 h1
  have := hG 1 (1 : DirichletCharacter ℂ 1) s (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hz) h0 h1
  exact this

/-- `cor1_uniform` from the lab's θ bound on `[10^11, 10^20]` instead of `SchoenfeldCor1`. -/
theorem cor1_uniform_hsw (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    (x : ℝ) (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) :
    |θ x - x| ≤ 843842 * 10 ^ 6 := by
  refine (theta_schoenfeld_large hRH hN hH h14 h1).trans ?_
  have hL := Real.log_le_log (by linarith) h2
  have hL2 := log_1e20_lt
  have hg := log_ge_two (x := x) (by linarith)
  have hs := sqrt_le_1e10 h2
  have hs0 := Real.sqrt_nonneg x
  have hpi := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]
  have hprod : √x * Real.log x ^ 2 ≤ 10 ^ 10 * 46.0522 ^ 2 := by
    have hlx : Real.log x ≤ 46.0522 := hL.trans hL2.le
    have a : Real.log x ^ 2 ≤ 46.0522 ^ 2 := pow_le_pow_left₀ (by linarith) hlx 2
    exact mul_le_mul hs a (by positivity) (by norm_num)
  nlinarith

/-- **P0011 main theorem without Schoenfeld**: GRH implies ternary Goldbach, CONDITIONAL ON
Zinoviev's `10^20` bound, the `10^13` even check and the zero-count inputs `HSWN70`,
`HSWHead14`, `Ordinates14` for the zeta zeros. -/
theorem derz_main_of_hsw
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap (169 * 10 ^ 10) (by norm_num) hZ
    (fun hG => gap_of_theta (10 ^ 11) (843842 * 10 ^ 6) (169 * 10 ^ 10) le_rfl
      (fun x h1 h2 => cor1_uniform_hsw (rh_of_GRH hG) hN hH h14 x h1 h2)
      (by have := log_1e20_lt; norm_num; linarith) (by norm_num)) hD

end LeanLab.DERZ1997
