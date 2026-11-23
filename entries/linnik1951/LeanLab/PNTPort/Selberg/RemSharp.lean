module

public import LeanLab.PNTPort.Selberg.Sharp1

/-!
# A sharper first difference of the explicit formula remainder

Lab proof, unit U-6012, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, unconditional.

`Sharp1.rem_first_difference` bounds `Rem(v + η) - Rem(v)` by `K η^{3/8} e^{v/2}`, from
`min(x, 1) ≤ x^{3/8}` against the decay `(1 + abs t)^{-3/2}` of the left line integrand. Any
exponent `a < 1/2` works, at the price `1/(1/2 - a)` from `∫ (1 + abs t)^{a - 3/2} dt = 2/(1/2 - a)`;
choosing `a = 1/2 - 1/log(1/η)` gives

* `rem_first_difference_a`: `abs(Rem(v + η) - Rem(v)) ≤ K η^a e^{v/2}/(1/2 - a)` for `0 ≤ a < 1/2`;
* `rem_first_difference_half`: `abs(Rem(v + η) - Rem(v)) ≤ K η^{1/2} (log(1/η) + 2) e^{v/2}`
  for `0 < η ≤ 1`;
* `norm_Rq_le_half`: `abs(Rq a η) ≤ K η^{-1/2} (log(1/η) + 2) e^{-a/2}`, in place of `η^{-5/8}`.

Effect downstream, not yet propagated: the remainder of `selberg_sharp` becomes
`η^{-1}(log(1/η) + 2)² e^{-2U}` in place of `η^{-5/4} e^{-2U}`; with `η = √(δ/X)` it is below
the main term `δ log²(1/δ)` for every `δ ≥ 1/X`, that is every window `h ≥ 1`, where the
`η^{-5/4}` form needs `h ≥ X^{2/13}`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex MeasureTheory Filter Set

lemma min_le_rpow_a {x a : ℝ} (hx : 0 ≤ x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : min x 1 ≤ x ^ a := by
  rcases le_or_gt x 1 with h | h
  · rw [min_eq_left h]; exact Real.self_le_rpow_of_le_one hx h ha1
  · rw [min_eq_right h.le]; exact Real.one_le_rpow h.le ha0

/-- `∫ (1 + abs t)^{-r} dt = 2/(r - 1)` for `r > 1`. -/
lemma integral_one_add_norm_rpow {r : ℝ} (hr : 1 < r) :
    ∫ t : ℝ, (1 + ‖t‖) ^ (-r) = 2 / (r - 1) := by
  have h1 : ∫ t : ℝ, (1 + ‖t‖) ^ (-r) = 2 * ∫ t in Ioi (0 : ℝ), (1 + t) ^ (-r) := by
    simp_rw [Real.norm_eq_abs]
    exact integral_comp_abs (f := fun t => (1 + t) ^ (-r))
  set g : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun t => t ^ (-r)) with hg
  have h2 : ∫ t in Ioi (0 : ℝ), (1 + t) ^ (-r) = ∫ t, g t := by
    rw [← integral_add_right_eq_self g 1, ← integral_indicator measurableSet_Ioi]
    congr 1; ext t
    simp only [hg, Set.indicator, Set.mem_Ioi]
    by_cases ht : 0 < t
    · rw [if_pos ht, if_pos (by linarith)]; ring_nf
    · rw [if_neg ht, if_neg (by linarith)]
  have h3 : ∫ t, g t = ∫ t in Ioi (1 : ℝ), t ^ (-r) := integral_indicator measurableSet_Ioi
  rw [h1, h2, h3, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
  have hne : r - 1 ≠ 0 := by linarith
  have hne' : -r + 1 ≠ 0 := by intro h; apply hne; linarith
  field_simp
  ring

/-- **The first difference with any exponent `a < 1/2`.** -/
theorem rem_first_difference_a : ∃ K : ℝ, 0 ≤ K ∧ ∀ v η a : ℝ, 0 ≤ η → η ≤ 1 → 0 ≤ a → a < 1 / 2 →
    ‖Rem (v + η) - Rem v‖ ≤ K * η ^ a * Real.exp (v / 2) / (1 / 2 - a) := by
  obtain ⟨A, hA0, hA⟩ := norm_Fg_le
  refine ⟨1 / (2 * Real.pi) * (6 * A * 2), by positivity, fun v η a hη0 hη1 ha0 ha1 => ?_⟩
  have hi : ∀ w, Integrable (fl w) := fun w => integrable_line A hA w
  have hcomb : Rem (v + η) - Rem v = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, fl v t * (cexp (η * (sl t + 1)) - 1) := by
    rw [rem_eq, rem_eq]
    have e : ∀ t, fl v t * (cexp (η * (sl t + 1)) - 1) = fl (v + η) t - fl v t := by
      intro t
      simp only [fl]
      rw [show ((v + η : ℝ) : ℂ) * (sl t + 1) = v * (sl t + 1) + η * (sl t + 1) by push_cast; ring,
        Complex.exp_add]
      ring
    simp_rw [e]
    rw [integral_sub (hi (v + η)) (hi v)]
    ring
  rw [hcomb, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hpi]
  set r := 3 / 2 - a with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hpt : ∀ t : ℝ, ‖fl v t * (cexp (η * (sl t + 1)) - 1)‖ ≤
      6 * A * Real.exp (v / 2) * η ^ a * (1 + ‖t‖) ^ (-r) := by
    intro t
    have hn1 : ‖sl t + 1‖ ≤ 1 + ‖t‖ := by
      unfold sl
      have : ((-1 / 2 : ℝ) : ℂ) + t * I + 1 = ((1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      norm_num
    have hz : |((η : ℂ) * (sl t + 1)).re| ≤ 3 / 2 := by
      have : ((η : ℂ) * (sl t + 1)).re = η / 2 := by unfold sl; simp; ring
      rw [this, abs_of_nonneg (by positivity)]; linarith
    have hE := norm_exp_sub_one_le_six hz
    have hzn : ‖(η : ℂ) * (sl t + 1)‖ = η * ‖sl t + 1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0]
    rw [hzn] at hE
    have hmin := min_le_rpow_a (mul_nonneg hη0 (norm_nonneg (sl t + 1))) ha0 (by linarith)
    have hpow : (η * ‖sl t + 1‖) ^ a ≤ η ^ a * (1 + ‖t‖) ^ a := by
      rw [Real.mul_rpow hη0 (norm_nonneg _)]
      gcongr
    have hEz : ‖cexp (η * (sl t + 1)) - 1‖ ≤ 6 * (η ^ a * (1 + ‖t‖) ^ a) := by linarith
    have hu : 0 < 1 + ‖t‖ := by positivity
    have hc : (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖t‖) ^ a = (1 + ‖t‖) ^ (-r) := by
      rw [← Real.rpow_add hu, hr]; congr 1; ring
    simp only [fl]
    rw [norm_mul, norm_mul, norm_cexp_line]
    calc ‖Fg (sl t)‖ * Real.exp (v / 2) * ‖cexp (η * (sl t + 1)) - 1‖
        ≤ (A * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) * Real.exp (v / 2) *
            (6 * (η ^ a * (1 + ‖t‖) ^ a)) := by
          gcongr
          exact hA t
      _ = 6 * A * Real.exp (v / 2) * η ^ a *
            ((1 + ‖t‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖t‖) ^ a) := by ring
      _ = _ := by rw [hc]
  have hint : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-r)) := integrable_one_add_norm (by
    simp only [Module.finrank_self, Nat.cast_one]; exact hr1)
  have hg : Integrable (fun t : ℝ => 6 * A * Real.exp (v / 2) * η ^ a * (1 + ‖t‖) ^ (-r)) :=
    hint.const_mul _
  have hle := norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_one_add_norm_rpow hr1] at hle
  have hr' : r - 1 = 1 / 2 - a := by rw [hr]; ring
  rw [hr'] at hle
  have hpos : 0 < 1 / 2 - a := by linarith
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, fl v t * (cexp (η * (sl t + 1)) - 1)‖
      ≤ 1 / (2 * Real.pi) * (6 * A * Real.exp (v / 2) * η ^ a * (2 / (1 / 2 - a))) := by gcongr
    _ = 1 / (2 * Real.pi) * (6 * A * 2) * η ^ a * Real.exp (v / 2) / (1 / 2 - a) := by
        field_simp

/-- **The first difference with the exponent `1/2`, at the price of a logarithm.** -/
theorem rem_first_difference_half : ∃ K : ℝ, 0 ≤ K ∧ ∀ v η : ℝ, 0 < η → η ≤ 1 →
    ‖Rem (v + η) - Rem v‖ ≤ K * η ^ (1 / 2 : ℝ) * (Real.log (1 / η) + 2) * Real.exp (v / 2) := by
  obtain ⟨K, hK0, hK⟩ := rem_first_difference_a
  refine ⟨4 * Real.exp 1 * K, by positivity, fun v η hη0 hη1 => ?_⟩
  set L := Real.log (1 / η) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hev : 0 < Real.exp (v / 2) := Real.exp_pos _
  rcases le_or_gt L 2 with hL2 | hL2
  · -- `η ≥ e^{-2}`: take `a = 0`
    have h := hK v η 0 hη0.le hη1 le_rfl (by norm_num)
    rw [Real.rpow_zero] at h
    have hη2 : Real.exp (-1) ≤ η ^ (1 / 2 : ℝ) := by
      have : Real.log η ≥ -2 := by
        have : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
        linarith
      rw [Real.rpow_def_of_pos hη0]
      exact Real.exp_le_exp.mpr (by linarith)
    have he1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    calc ‖Rem (v + η) - Rem v‖ ≤ K * 1 * Real.exp (v / 2) / (1 / 2 - 0) := h
      _ = 2 * K * Real.exp (v / 2) := by ring
      _ ≤ 2 * K * Real.exp (v / 2) * (Real.exp 1 * η ^ (1 / 2 : ℝ) * (L + 2)) := by
          apply le_mul_of_one_le_right (by positivity)
          have : 1 ≤ Real.exp 1 * η ^ (1 / 2 : ℝ) := by nlinarith [Real.exp_pos 1]
          nlinarith
      _ ≤ _ := by
          have : 0 ≤ K * η ^ (1 / 2 : ℝ) * (L + 2) * Real.exp (v / 2) * Real.exp 1 := by positivity
          nlinarith
  · -- `η < e^{-2}`: take `a = 1/2 - 1/L`
    have hLpos : 0 < L := by linarith
    set a := 1 / 2 - 1 / L with ha
    have ha0 : 0 ≤ a := by
      rw [ha, sub_nonneg, div_le_div_iff₀ hLpos (by norm_num)]; linarith
    have ha1 : a < 1 / 2 := by
      have : 0 < 1 / L := by positivity
      rw [ha]; linarith
    have h := hK v η a hη0.le hη1 ha0 ha1
    have hden : 1 / 2 - a = 1 / L := by rw [ha]; ring
    rw [hden, div_div_eq_mul_div, div_one] at h
    -- `η^a = η^{1/2} η^{-1/L} = e η^{1/2}`
    have hpow : η ^ a = η ^ (1 / 2 : ℝ) * Real.exp 1 := by
      rw [ha, Real.rpow_sub hη0, div_eq_mul_inv]
      congr 1
      rw [Real.rpow_def_of_pos hη0, ← Real.exp_neg]
      congr 1
      have : Real.log η = -L := by rw [hL, one_div, Real.log_inv]; ring
      rw [this]; field_simp
    rw [hpow] at h
    calc ‖Rem (v + η) - Rem v‖ ≤ K * (η ^ (1 / 2 : ℝ) * Real.exp 1) * Real.exp (v / 2) * L := h
      _ ≤ 4 * Real.exp 1 * K * η ^ (1 / 2 : ℝ) * (L + 2) * Real.exp (v / 2) := by
          have : 0 ≤ K * η ^ (1 / 2 : ℝ) * Real.exp 1 * Real.exp (v / 2) := by positivity
          nlinarith

/-- **`abs(Rq a η) ≤ K η^{-1/2} (log(1/η) + 2) e^{-a/2}`.** -/
lemma norm_Rq_le_half : ∃ K : ℝ, 0 ≤ K ∧ ∀ a η : ℝ, 0 < η → η ≤ 1 →
    ‖Rq a η‖ ≤ K * η ^ (-(1 / 2) : ℝ) * (Real.log (1 / η) + 2) * Real.exp (-(a / 2)) := by
  obtain ⟨K, hK0, hK⟩ := rem_first_difference_half
  refine ⟨K, hK0, fun a η hη hη1 => ?_⟩
  have hD := den_pos (a := a) hη
  unfold Rq
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, div_le_iff₀ hD]
  have hη' : η ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
  have hpow : η ^ (-(1 / 2) : ℝ) * η = η ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hη.ne']; norm_num
  have hexp : Real.exp (-(a / 2)) * Real.exp a = Real.exp (a / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hL : 0 ≤ Real.log (1 / η) + 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / η by rw [le_div_iff₀ hη]; linarith); linarith
  calc ‖Rem (a + η) - Rem a‖ ≤ K * η ^ (1 / 2 : ℝ) * (Real.log (1 / η) + 2) * Real.exp (a / 2) :=
        hK a η hη hη1
    _ = K * η ^ (-(1 / 2) : ℝ) * (Real.log (1 / η) + 2) * Real.exp (-(a / 2)) *
          (Real.exp a * η) := by rw [← hpow, ← hexp]; ring
    _ ≤ K * η ^ (-(1 / 2) : ℝ) * (Real.log (1 / η) + 2) * Real.exp (-(a / 2)) *
          (Real.exp a * (Real.exp η - 1)) := by gcongr

end LeanLab.PNTPort.Selberg

