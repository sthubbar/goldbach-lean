module

public import LeanLab.PNTPort.Selberg.MeanSquare

/-!
# The left line integral: a sharper remainder

Lab proof, unit U-5923, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics; `selberg_smoothed_sharp` is CONDITIONAL ON RiemannHypothesis only.

The remainder of the explicit formula for `ψ₁(e^v)` is exactly
`Rem v = e^v (1/2π) ∫ F(e^v, -1/2 + it) dt = (1/2π) ∫ g(t) e^{v(1/2 + it)} dt` with
`g(t) = -ζ'/ζ(s)/(s(s+1))`, `s = -1/2 + it`, and `|g(t)| ≤ A (1 + |t|)^{-3/2}`. Its second
difference in `v` carries the factor `E(λ(s + 1))`, at most `12 min(λ²|s + 1|², 1) ≤ 12 (λ(1+|t|))^{3/8}`,
so

* `rem_second_difference`: `‖Rem(u+λ) - 2 Rem(u) + Rem(u-λ)‖ ≤ K λ^{3/8} e^{u/2}`, unconditional,
  where `explicit_exp` alone gives `5K e^{u/2}`;
* `selberg_smoothed_sharp`: under RH, the mean square of `selberg_smoothed` with remainder
  term `λ^{3/4} e^{-2U}` in place of `e^{-2U}`. In the variable `h = λX` this is
  `h log²(X/h) + h²/X² + X^{1/4} h^{-5/4}`, of Selberg quality once `h ≥ X^{1/9}`, where
  `selberg_smoothed` needs `h ≥ X^{1/3}/log X`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

local notation "ζ" => riemannZeta

/-- `g(s) = -ζ'/ζ(s)/(s(s+1))`. -/
noncomputable def Fg (s : ℂ) : ℂ := -(deriv ζ s / ζ s) / (s * (s + 1))

/-- The point `-1/2 + it` of the left line. -/
noncomputable def sl (t : ℝ) : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I

/-- The left line integrand `g(t) e^{v(s+1)}`. -/
noncomputable def fl (v t : ℝ) : ℂ := Fg (sl t) * cexp (v * (sl t + 1))

lemma F_exp (v : ℝ) (s : ℂ) :
    (Real.exp v : ℂ) * ExplicitPsi1.F (Real.exp v) s = Fg s * cexp (v * (s + 1)) := by
  unfold ExplicitPsi1.F Fg
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  rw [show (v : ℂ) * (s + 1) = v + v * s by ring, Complex.exp_add, mul_comm (v : ℂ) s]
  ring

lemma norm_Fg_le : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ‖Fg (sl t)‖ ≤ A * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨A, hA, h⟩ := left_bound
  refine ⟨A, hA, fun t => ?_⟩
  have h1 := h 1 one_pos t
  have e : ExplicitPsi1.F 1 (sl t) = Fg (sl t) := by
    unfold ExplicitPsi1.F Fg; rw [Complex.ofReal_one, Complex.one_cpow]; ring
  unfold sl at e
  rw [e, Real.one_rpow, mul_one] at h1
  exact h1

/-- **The remainder is the left line integral.** -/
lemma rem_eq (v : ℝ) :
    Rem v = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, fl v t := by
  have hx := Real.exp_pos v
  have hEF := explicit_formula_psi1 hx
  rw [logDeriv_zeta_zero] at hEF
  have e : (∑' ρ : Zall, zterm (Real.exp v) ρ) =
      ∑' ρ : NZs, zterm (Real.exp v) ρ.1 := by
    rw [Zall_eq]; rfl
  rw [e] at hEF
  have hint : (∫ t : ℝ, fl v t) =
      (Real.exp v : ℂ) * ∫ t : ℝ, ExplicitPsi1.F (Real.exp v) (((-1 / 2 : ℝ) : ℂ) + t * I) := by
    rw [← integral_const_mul]
    congr 1; ext t; rw [F_exp]; rfl
  rw [hint]
  unfold Rem psi1
  rw [hEF]
  simp_rw [ztE_eq]
  rw [tsum_mul_left]
  have : Real.exp (2 * v) = Real.exp v * Real.exp v := by rw [← Real.exp_add]; ring_nf
  rw [this]
  push_cast
  ring

lemma integrable_line (A : ℝ) (_hA : ∀ t : ℝ, ‖Fg (sl t)‖ ≤ A * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)))
    (v : ℝ) : Integrable (fl v) := by
  have h := (integrable_left (Real.exp_pos v)).const_mul (Real.exp v : ℂ)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [fl]
  rw [F_exp]; rfl

lemma norm_cexp_line (v t : ℝ) : ‖cexp (v * (sl t + 1))‖ = Real.exp (v / 2) := by
  rw [Complex.norm_exp]; congr 1; unfold sl; simp; ring

lemma min_sq_le_rpow {a : ℝ} (ha : 0 ≤ a) : min (a ^ 2) 1 ≤ a ^ (3 / 8 : ℝ) := by
  rcases le_or_gt a 1 with h | h
  · rcases eq_or_lt_of_le ha with h0 | h0
    · rw [← h0]; simp
    · refine (min_le_left _ _).trans ?_
      rw [show a ^ 2 = a ^ (2 : ℝ) by norm_cast]
      exact Real.rpow_le_rpow_of_exponent_ge h0 h (by norm_num)
  · exact (min_le_right _ _).trans (Real.one_le_rpow h.le (by norm_num))

/-- **The second difference of the remainder**, unconditional. -/
theorem rem_second_difference : ∃ K : ℝ, 0 ≤ K ∧ ∀ l u : ℝ, 0 ≤ l → l ≤ 1 →
    ‖Rem (u + l) - 2 * Rem u + Rem (u - l)‖ ≤ K * l ^ (3 / 8 : ℝ) * Real.exp (u / 2) := by
  obtain ⟨A, hA0, hA⟩ := norm_Fg_le
  set I0 := ∫ t : ℝ, (1 + ‖t‖) ^ (-(9 / 8 : ℝ))
  have hI0int : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(9 / 8 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hI0 : 0 ≤ I0 := integral_nonneg fun t => by positivity
  refine ⟨1 / (2 * Real.pi) * (12 * A * I0), by positivity, fun l u hl0 hl1 => ?_⟩
  have hi : ∀ v, Integrable (fl v) := fun v => integrable_line A hA v
  -- the combined integrand
  have hcomb : Rem (u + l) - 2 * Rem u + Rem (u - l) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, fl u t * Ez (l * (sl t + 1)) := by
    rw [rem_eq, rem_eq, rem_eq]
    have e : ∀ t, fl u t * Ez (l * (sl t + 1)) = fl (u + l) t - 2 * fl u t + fl (u - l) t := by
      intro t
      simp only [fl, Ez]
      rw [show ((u + l : ℝ) : ℂ) * (sl t + 1) = u * (sl t + 1) + l * (sl t + 1) by push_cast; ring,
        show ((u - l : ℝ) : ℂ) * (sl t + 1) = u * (sl t + 1) + -(l * (sl t + 1)) by push_cast; ring,
        Complex.exp_add, Complex.exp_add]
      ring
    simp_rw [e]
    have I1 : Integrable (fun t => fl (u + l) t - 2 * fl u t) := (hi _).sub ((hi u).const_mul 2)
    have I2 : Integrable (fun t => 2 * fl u t) := (hi u).const_mul 2
    rw [integral_add I1 (hi (u - l)), integral_sub (hi (u + l)) I2, integral_const_mul]
    ring
  rw [hcomb, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hpi]
  -- the pointwise bound
  have hpt : ∀ t : ℝ, ‖fl u t * Ez (l * (sl t + 1))‖ ≤
      12 * A * Real.exp (u / 2) * l ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (-(9 / 8 : ℝ)) := by
    intro t
    have hn1 : ‖sl t + 1‖ ≤ 1 + ‖t‖ := by
      unfold sl
      have : ((-1 / 2 : ℝ) : ℂ) + t * I + 1 = ((1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      norm_num
    have hz : |(l * (sl t + 1) : ℂ).re| ≤ 3 / 2 := by
      have : ((l : ℂ) * (sl t + 1)).re = l / 2 := by unfold sl; simp; ring
      rw [this, abs_of_nonneg (by positivity)]; linarith
    have hE := norm_E_le _ hz
    have hzn : ‖(l : ℂ) * (sl t + 1)‖ = l * ‖sl t + 1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
    rw [hzn] at hE
    have hmin := min_sq_le_rpow (mul_nonneg hl0 (norm_nonneg (sl t + 1)))
    have hpow : (l * ‖sl t + 1‖) ^ (3 / 8 : ℝ) ≤ l ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (3 / 8 : ℝ) := by
      rw [Real.mul_rpow hl0 (norm_nonneg _)]
      gcongr
    have hEz : ‖Ez (l * (sl t + 1))‖ ≤ 12 * (l ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (3 / 8 : ℝ)) := by
      unfold Ez; linarith
    have hu : 0 < 1 + ‖t‖ := by positivity
    have hcomb : (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖t‖) ^ (3 / 8 : ℝ) = (1 + ‖t‖) ^ (-(9 / 8 : ℝ)) := by
      rw [← Real.rpow_add hu]; norm_num
    simp only [fl]
    rw [norm_mul, norm_mul, norm_cexp_line]
    calc ‖Fg (sl t)‖ * Real.exp (u / 2) * ‖Ez (l * (sl t + 1))‖
        ≤ (A * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) * Real.exp (u / 2) *
            (12 * (l ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (3 / 8 : ℝ))) := by
          gcongr
          exact hA t
      _ = 12 * A * Real.exp (u / 2) * l ^ (3 / 8 : ℝ) *
            ((1 + ‖t‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖t‖) ^ (3 / 8 : ℝ)) := by ring
      _ = _ := by rw [hcomb]
  have hg : Integrable (fun t : ℝ =>
      12 * A * Real.exp (u / 2) * l ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (-(9 / 8 : ℝ))) :=
    hI0int.const_mul _
  have hle := norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
  rw [integral_const_mul] at hle
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, fl u t * Ez (l * (sl t + 1))‖
      ≤ 1 / (2 * Real.pi) * (12 * A * Real.exp (u / 2) * l ^ (3 / 8 : ℝ) * I0) := by gcongr
    _ = 1 / (2 * Real.pi) * (12 * A * I0) * l ^ (3 / 8 : ℝ) * Real.exp (u / 2) := by ring

/-- **Selberg's mean square under RH, smoothed form, sharper remainder.** -/
theorem selberg_smoothed_sharp (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ l : ℝ, 0 < l → l ≤ 1 →
    ∀ U : ℝ, Integrable (fun u => ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u) ∧
      ∫ u, ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u
        ≤ C * (l ^ 3 * (Real.log (1 / l) + 3) ^ 2 + l ^ 4 * Real.exp (-U) +
          l ^ (3 / 4 : ℝ) * Real.exp (-(2 * U))) := by
  obtain ⟨K, hK0, hsd⟩ := rem_second_difference
  obtain ⟨C, hC, h⟩ := selberg_of_remainder hRH (fun l => l ^ (3 / 8 : ℝ))
    ⟨K, hK0, fun l u h0 h1 => by rw [second_difference_eq]; exact hsd l u h0 h1⟩
  refine ⟨C, hC, fun l hl0 hl1 U => ?_⟩
  obtain ⟨hi, hb⟩ := h l hl0 hl1 U
  have e : (l ^ (3 / 8 : ℝ)) ^ 2 = l ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  refine ⟨hi, hb.trans_eq ?_⟩
  simp only [e]

end LeanLab.PNTPort.Selberg

