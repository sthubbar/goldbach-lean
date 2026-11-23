module

public import LeanLab.PNTPort.ZetaZeros.GammaBounds
public import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# A digamma bound: `|ψ(s)| ≪ log t` near `1 + it`

Lab proof, unit U-5270, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics, no
cited input. With `c = 1 + it`, `t ≥ 1`, the function `f(z) = Γ(c + z/2)/Γ(c)` has no zeros,
`|f| ≤ 3(t + 4)` on `‖z‖ ≤ 29/30` by `norm_Gamma_le_PL` and `|Γ(1 + it)|² = πt / sinh(πt)`, so the
ported Borel-Carathéodory bound `FinalBound`, Apache-2.0, PrimeNumberTheoremAnd, gives
`|Γ'/Γ(s)| ≪ log t` for `‖s - c‖ ≤ 1/3`. With Mathlib's `digamma_apply_add_one` this reaches
every vertical line, and with `logDeriv_riemannZeta_one_sub` the left half plane for `ζ'/ζ`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric
open scoped Real ComplexConjugate

/-- `|Γ(1 + it)|² = πt / sinh(πt)` for `t ≠ 0`. -/
theorem normSq_Gamma_one (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (1 + t * I)‖ ^ 2 = π * t / Real.sinh (π * t) := by
  have hit : (t : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
  have h1 : Gamma (1 + t * I) = (t * I) * Gamma (t * I) := by
    rw [add_comm]; exact Gamma_add_one _ hit
  have hrefl := Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hconj : (1 : ℂ) - t * I = conj (1 + t * I) := by
    apply Complex.ext <;> simp
  have hsin : Complex.sin (π * (t * I)) = Real.sinh (π * t) * I := by
    rw [show (π : ℂ) * (t * I) = ((π * t : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
      Complex.ofReal_sinh]
  have hsh : Real.sinh (π * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  have key : (((‖Gamma (1 + t * I)‖ ^ 2 : ℝ)) : ℂ) = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← Gamma_conj,
      ← hconj]
    rw [h1, mul_assoc, hrefl, hsin]
    have : ((Real.sinh (π * t)) : ℂ) ≠ 0 := by exact_mod_cast hsh
    push_cast
    field_simp
  exact_mod_cast key

/-- `|Γ(1 + it)| ≥ √(2π) e^{-πt/2}` for `t ≥ 1`. -/
theorem norm_Gamma_one_ge {t : ℝ} (ht : 1 ≤ t) :
    √(2 * π) * Real.exp (-(π * t / 2)) ≤ ‖Gamma (1 + t * I)‖ := by
  have h := normSq_Gamma_one t (by linarith)
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hsle : Real.sinh (π * t) ≤ Real.exp (π * t) / 2 := by
    rw [Real.sinh_eq]; have := Real.exp_pos (-(π * t)); linarith
  have hlow : 2 * π * Real.exp (-(π * t)) ≤ ‖Gamma (1 + t * I)‖ ^ 2 := by
    rw [h, le_div_iff₀ hs]
    have he : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by
      rw [← Real.exp_add]; simp
    have hp := Real.pi_pos
    have he0 := Real.exp_pos (-(π * t))
    calc 2 * π * Real.exp (-(π * t)) * Real.sinh (π * t)
        ≤ 2 * π * Real.exp (-(π * t)) * (Real.exp (π * t) / 2) :=
          mul_le_mul_of_nonneg_left hsle (by positivity)
      _ = π * (Real.exp (-(π * t)) * Real.exp (π * t)) := by ring
      _ = π := by rw [he, mul_one]
      _ ≤ π * t := by nlinarith
  have hsq : (√(2 * π) * Real.exp (-(π * t / 2))) ^ 2 = 2 * π * Real.exp (-(π * t)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [← hsq] at hlow
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (norm_nonneg _) hlow

lemma gamma_analyticAt {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Gamma w := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    have hne : ∀ m : ℕ, z ≠ -m := by
      intro m h; have := hz; rw [h] at this; simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact (Complex.differentiableAt_Gamma z hne).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hw)

lemma gamma_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : Gamma w ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h; rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `f(z) = Γ(1 + it + z/2) / Γ(1 + it)`. -/
noncomputable def fG (t : ℝ) (z : ℂ) : ℂ := Gamma (1 + t * I + z / 2) / Gamma (1 + t * I)

lemma fG_re {t : ℝ} {z : ℂ} (hz : ‖z‖ ≤ 1) : 1 / 2 ≤ (1 + t * I + z / 2).re ∧
    (1 + t * I + z / 2).re ≤ 3 / 2 := by
  have := Complex.abs_re_le_norm z
  have e : (1 + t * I + z / 2).re = 1 + z.re / 2 := by simp
  rw [e]; constructor <;> cases abs_cases z.re <;> linarith

/-- **`|ψ(w)| ≤ K log(t + 3)`** for `t ≥ 1` and `‖w - (1 + it)‖ ≤ 1/3`. -/
theorem digamma_near_one : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → ∀ w : ℂ,
    ‖w - (1 + t * I)‖ ≤ 1 / 3 → ‖digamma w‖ ≤ K * Real.log (t + 3) := by
  set K0 : ℝ := 16 * (3 / 4) ^ 2 / (3 / 4 - 2 / 3) ^ 3 +
    1 / (((29 / 30) ^ 2 / (4 / 5) - 4 / 5) * Real.log ((29 / 30) / (4 / 5))) with hK0
  have hl : 0 < Real.log ((29 / 30 : ℝ) / (4 / 5)) := Real.log_pos (by norm_num)
  have hK0p : 0 < K0 := by rw [hK0]; positivity
  refine ⟨4 * K0, by positivity, fun t ht w hw => ?_⟩
  set c : ℂ := 1 + t * I with hc
  have hcre : 0 < c.re := by simp [hc]
  have hGc := gamma_ne_zero_of_re_pos hcre
  set z : ℂ := 2 * (w - c) with hz
  have hzn : ‖z‖ ≤ 2 / 3 := by
    rw [hz, norm_mul]; norm_num; linarith
  have hwz : w = c + z / 2 := by rw [hz]; ring
  -- the setting of `FinalBound`
  have gA : AnalyticOnNhd ℂ (fG t) (closedBall (0 : ℂ) 1) := by
    intro u hu
    simp only [Metric.mem_closedBall, dist_zero_right] at hu
    have hre := (fG_re (t := t) hu).1
    unfold fG
    have hA : AnalyticAt ℂ (fun x : ℂ => 1 + (t : ℂ) * I + x / 2) u := by
      have e : (fun x : ℂ => 1 + (t : ℂ) * I + x / 2) = fun x => (1 + t * I) + (1 / 2 : ℂ) * x := by
        funext x; ring
      rw [e]; exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact (AnalyticAt.comp (g := Gamma) (f := fun x : ℂ => 1 + (t : ℂ) * I + x / 2)
      (gamma_analyticAt (w := 1 + t * I + u / 2) (by linarith)) hA).div_const
  have g0 : fG t 0 = 1 := by
    unfold fG; rw [zero_div, add_zero]; exact div_self hGc
  have hnz : ∀ u : ℂ, ‖u‖ ≤ 1 → fG t u ≠ 0 := by
    intro u hu
    unfold fG
    exact div_ne_zero (gamma_ne_zero_of_re_pos (by linarith [(fG_re (t := t) hu).1])) hGc
  have hfin : (SetOfZeros 1 (fG t)).Finite := by
    apply Set.Finite.subset Set.finite_empty
    intro u hu; exact absurd hu.2 (hnz u hu.1)
  set B : ℝ := 3 * (t + 3) with hB
  have hB1 : 1 < B := by rw [hB]; linarith
  have hbound : ∀ u : ℂ, ‖u‖ ≤ 29 / 30 → ‖fG t u‖ ≤ B := by
    intro u hu
    have hu1 : ‖u‖ ≤ 1 := by linarith
    obtain ⟨hr1, hr2⟩ := fG_re (t := t) hu1
    have hG := norm_Gamma_le_PL hr1 hr2
    have hlow := norm_Gamma_one_ge ht
    have him : t - 1 / 2 ≤ (1 + t * I + u / 2).im := by
      have := Complex.abs_im_le_norm u
      have e : (1 + t * I + u / 2).im = t + u.im / 2 := by simp
      rw [e]; cases abs_cases u.im <;> linarith
    have hn1 : ‖(1 + t * I + u / 2) + 1‖ ≤ t + 3 := by
      calc ‖(1 + t * I + u / 2) + 1‖ = ‖(2 : ℂ) + t * I + u / 2‖ := by ring_nf
        _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ + ‖u / 2‖ := norm_add₃_le
        _ ≤ t + 3 := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), norm_div]
            norm_num; linarith
    have hexp : Real.exp (-(π * (1 + t * I + u / 2).im / 2)) ≤
        Real.exp (-(π * t / 2)) * 3 := by
      have h1 : Real.exp (-(π * (1 + t * I + u / 2).im / 2)) ≤
          Real.exp (-(π * t / 2) + π / 4) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have h2 : Real.exp (π / 4) ≤ 3 := by
        have : Real.exp (π / 4) ≤ Real.exp 1 :=
          Real.exp_le_exp.mpr (by linarith [Real.pi_lt_four])
        linarith [Real.exp_one_lt_d9]
      rw [Real.exp_add] at h1
      calc _ ≤ Real.exp (-(π * t / 2)) * Real.exp (π / 4) := h1
        _ ≤ Real.exp (-(π * t / 2)) * 3 := by gcongr
    have hs2 : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    have hE := Real.exp_pos (-(π * t / 2))
    unfold fG
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hlow)]
    calc ‖Gamma (1 + t * I + u / 2)‖
        ≤ √(2 * π) * ‖(1 + t * I + u / 2) + 1‖ * Real.exp (-(π * (1 + t * I + u / 2).im / 2)) := hG
      _ ≤ √(2 * π) * (t + 3) * (Real.exp (-(π * t / 2)) * 3) := by gcongr
      _ = B * (√(2 * π) * Real.exp (-(π * t / 2))) := by rw [hB]; ring
      _ ≤ B * ‖Gamma (1 + t * I)‖ := by gcongr
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (4 / 5) (fG t) := by
    refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hzn, ?_⟩
    rintro ⟨hz1, hz2⟩; exact hnz z (by linarith) hz2
  have key := FinalBound hB1 (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (3 / 4 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 29 / 30) (by norm_num : (29 / 30 : ℝ) < 1) gA g0 hfin
    hbound hzmem
  have hsum : (∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset,
      (analyticOrderNatAt (fG t) ρ : ℂ) / (z - ρ)) = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact absurd hρ.2 (hnz ρ (by linarith [hρ.1]))
  rw [hsum, sub_zero] at key
  -- `f'/f(z) = ψ(w)/2`
  have hwre : 0 < w.re := by rw [hwz]; linarith [(fG_re (t := t) (by linarith : ‖z‖ ≤ 1)).1]
  have hGw := gamma_ne_zero_of_re_pos hwre
  have hd : deriv (fG t) z = (1 / 2) * deriv Gamma w / Gamma c := by
    have haff : HasDerivAt (fun u : ℂ => 1 + t * I + u / 2) (1 / 2) z := by
      simpa using ((hasDerivAt_id z).div_const (2 : ℂ)).const_add (1 + t * I)
    have hG : HasDerivAt Gamma (deriv Gamma w) (1 + t * I + z / 2) := by
      rw [← hc, ← hwz]
      exact (gamma_analyticAt hwre).differentiableAt.hasDerivAt
    have h := (hG.comp z haff).div_const (Gamma c)
    unfold fG
    rw [show (fun u => Gamma (1 + t * I + u / 2) / Gamma (1 + t * I)) =
      fun u => (Gamma ∘ fun u : ℂ => 1 + t * I + u / 2) u / Gamma c from rfl, h.deriv]
    ring
  have hfz : fG t z = Gamma w / Gamma c := by unfold fG; rw [← hc, ← hwz]
  have hratio : deriv (fG t) z / fG t z = (1 / 2) * digamma w := by
    rw [hd, hfz, digamma_def, logDeriv_apply]
    field_simp
  rw [hratio, norm_mul] at key
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12] at key
  have hK0' : 16 * (3 / 4 : ℝ) ^ 2 / (3 / 4 - 2 / 3) ^ 3 +
      1 / (((29 / 30) ^ 2 / (4 / 5) - 4 / 5) * Real.log ((29 / 30) / (4 / 5))) = K0 := by
    rw [hK0]
  rw [hK0'] at key
  -- `log B ≤ 2 log(t + 3)`
  have hlogB : Real.log B ≤ 2 * Real.log (t + 3) := by
    calc Real.log B ≤ Real.log ((t + 3) ^ 2) :=
          Real.log_le_log (by rw [hB]; positivity) (by rw [hB]; nlinarith)
      _ = 2 * Real.log (t + 3) := by rw [Real.log_pow]; norm_num
  have : ‖digamma w‖ ≤ 2 * (K0 * Real.log B) := by linarith
  calc ‖digamma w‖ ≤ 2 * (K0 * Real.log B) := this
    _ ≤ 2 * (K0 * (2 * Real.log (t + 3))) := by gcongr
    _ = 4 * K0 * Real.log (t + 3) := by ring

end LeanLab.PNTPort.ZetaZeros

