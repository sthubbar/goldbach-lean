module

public import LeanLab.PNTPort.PsiChi.Final
public import LeanLab.PNTPort.BV.Helpers

/-!
# The Siegel-Walfisz theorem, `HeathBrown1985.SiegelWalfisz`

Lab proof, unit U-5209, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics,
ineffective through Siegel's theorem; no cited input.

`siegelWalfisz : HeathBrown1985.SiegelWalfisz`: for every `A > 0` there are `c > 0` and `K` with
`|ψ(x; k, l) - x/φ(k)| ≤ K x exp(-c √log x)` for all `x ≥ 2`, `1 ≤ k ≤ (log x)^A`, `(l, k) = 1`.
From the character expansion `BV.abs_psi_sub_le`, the non-principal bound
`psiChi_nonprincipal_bound`, the prime number theorem `psi_explicit_strong` for the principal
character, and `BV.psiBad_le` for the prime powers dividing `k`.
-/

@[expose] public section


open Real Finset

namespace LeanLab.PNTPort.PsiChi

lemma sqrt_le_exp_sqrt_log {c x : ℝ} (hx1 : 1 ≤ x) :
    Real.sqrt x ≤ Real.exp (c ^ 2 / 2) * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  have hx : 0 < x := by linarith
  have h : 0 ≤ Real.log x := Real.log_nonneg hx1
  set u := Real.sqrt (Real.log x)
  have hsx : Real.sqrt x = x * Real.exp (-(Real.log x) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, show Real.log x * (1 / 2) = Real.log x -
      Real.log x / 2 by ring, Real.exp_sub, Real.exp_log hx, neg_div, Real.exp_neg]; ring
  rw [hsx, show Real.exp (c ^ 2 / 2) * (x * Real.exp (-c * u)) = x * Real.exp (c ^ 2 / 2 + -c * u)
    by rw [Real.exp_add]; ring]
  gcongr
  have hu2 : u ^ 2 = Real.log x := Real.sq_sqrt h
  have := sq_nonneg (u - c)
  have e : -Real.log x / 2 = -(u ^ 2) / 2 := by rw [hu2]
  rw [e]; nlinarith

theorem siegelWalfisz : HeathBrown1985.SiegelWalfisz := by
  intro A hA
  obtain ⟨c₁, K₁, hc₁, h₁⟩ := psiChi_nonprincipal_bound A hA
  obtain ⟨cP, hcP, KP, hP⟩ := psi_explicit_strong
  have hKP := KP_nonneg hP
  obtain ⟨K₂, hK₂, h₂⟩ := BV.log_rpow_le_sqrt 2
  set c := min c₁ cP with hcdef
  have hc : 0 < c := lt_min hc₁ hcP
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := max K₁ 0 + KP + A / Real.log 2 * K₂ * Real.exp (c ^ 2 / 2) with hKdef
  refine ⟨c, hc, K, fun x hx k l hk hlk hkx ↦ ?_⟩
  haveI : NeZero k := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set E := Real.exp (-c * Real.sqrt (Real.log x)) with hE
  have hsq : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hE₁ : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left c₁ cP) hsq; linarith
  have hEP : Real.exp (-cP * Real.sqrt (Real.log x)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right c₁ cP) hsq; linarith
  have hφ : (1 : ℝ) ≤ k.totient := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.2 (by omega)).ne'
  have hcop : l.Coprime k := hlk
  have key := BV.abs_psi_sub_le x hcop
  -- the non-principal characters
  have hnp : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, ‖BV.psiChi x χ‖ ≤
      k.totient * (max K₁ 0 * x * E) := by
    have hcard : ((univ : Finset (DirichletCharacter ℂ k)).erase 1).card ≤ k.totient := by
      have h1 := Finset.card_erase_le (s := (univ : Finset (DirichletCharacter ℂ k))) (a := 1)
      have h2 : (univ : Finset (DirichletCharacter ℂ k)).card = k.totient := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k
      omega
    have hb : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1,
        ‖BV.psiChi x χ‖ ≤ max K₁ 0 * x * E := by
      intro χ hχ
      have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
      refine (h₁ x hx k χ hχ1 hkx).trans ?_
      have : K₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤
          max K₁ 0 * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) := by
        gcongr; exact le_max_left _ _
      refine this.trans ?_
      gcongr
    calc _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, max K₁ 0 * x * E :=
          Finset.sum_le_sum hb
      _ = ((univ : Finset (DirichletCharacter ℂ k)).erase 1).card * (max K₁ 0 * x * E) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k.totient * (max K₁ 0 * x * E) := by
          have hm : 0 ≤ max K₁ 0 * x * E := by
            have := le_max_right K₁ 0; positivity
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hm
  -- the principal character
  have hprin : ‖BV.psiChi x (1 : DirichletCharacter ℂ k) - x‖ ≤
      KP * x * E + A / Real.log 2 * K₂ * Real.exp (c ^ 2 / 2) * x * E := by
    have h1 := BV.norm_psiChi_one_sub (q := k) x
    have hbad : ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n k), ArithmeticFunction.vonMangoldt n
        = BV.psiBad x k := rfl
    rw [hbad] at h1
    have h2 := BV.psiBad_le (by linarith : (1 : ℝ) ≤ x) hk
    have hlogk : Real.log k ≤ A * Real.log x := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have := Real.log_le_log hk0 hkx
      rw [Real.log_rpow hlx] at this
      have h3 : Real.log (Real.log x) ≤ Real.log x - 1 := Real.log_le_sub_one_of_pos hlx
      nlinarith
    have h4 : BV.psiBad x k ≤ A / Real.log 2 * Real.log x ^ (2 : ℝ) := by
      refine h2.trans ?_
      rw [Real.rpow_two]
      calc Real.log k / Real.log 2 * Real.log x ≤ A * Real.log x / Real.log 2 * Real.log x := by
            gcongr
        _ = A / Real.log 2 * Real.log x ^ 2 := by ring
    have h5 : Real.log x ^ (2 : ℝ) ≤ K₂ * Real.sqrt x := h₂ x hx
    have h6 := sqrt_le_exp_sqrt_log (c := c) (by linarith : (1 : ℝ) ≤ x)
    have hpsi := hP x hx
    have hψ : ‖((Chebyshev.psi x : ℝ) : ℂ) - (x : ℂ)‖ ≤ KP * x * E := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine hpsi.trans ?_
      gcongr
    have hA2 : 0 ≤ A / Real.log 2 := by positivity
    calc ‖BV.psiChi x (1 : DirichletCharacter ℂ k) - x‖
        ≤ ‖BV.psiChi x (1 : DirichletCharacter ℂ k) - Chebyshev.psi x‖ +
            ‖((Chebyshev.psi x : ℝ) : ℂ) - (x : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ BV.psiBad x k + KP * x * E := add_le_add h1 hψ
      _ ≤ A / Real.log 2 * (K₂ * (Real.exp (c ^ 2 / 2) * (x * E))) + KP * x * E := by
          gcongr
          calc BV.psiBad x k ≤ A / Real.log 2 * Real.log x ^ (2 : ℝ) := h4
            _ ≤ A / Real.log 2 * (K₂ * Real.sqrt x) := by gcongr
            _ ≤ A / Real.log 2 * (K₂ * (Real.exp (c ^ 2 / 2) * (x * E))) := by gcongr
      _ = _ := by ring
  refine key.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have hxE : 0 ≤ x * E := by positivity
  calc ‖BV.psiChi x (1 : DirichletCharacter ℂ k) - x‖ +
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, ‖BV.psiChi x χ‖
      ≤ (KP * x * E + A / Real.log 2 * K₂ * Real.exp (c ^ 2 / 2) * x * E) +
          k.totient * (max K₁ 0 * x * E) := add_le_add hprin hnp
    _ ≤ K * x * E * k.totient := by
        rw [hKdef]
        have hm : 0 ≤ max K₁ 0 := le_max_right _ _
        have h1 : KP * x * E ≤ KP * x * E * k.totient := le_mul_of_one_le_right (by positivity) hφ
        have h2 : A / Real.log 2 * K₂ * Real.exp (c ^ 2 / 2) * x * E ≤
            A / Real.log 2 * K₂ * Real.exp (c ^ 2 / 2) * x * E * k.totient :=
          le_mul_of_one_le_right (by positivity) hφ
        nlinarith

end LeanLab.PNTPort.PsiChi
