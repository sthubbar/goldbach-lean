module

public import LeanLab.Linnik1951.Gamma442

/-!
P0093 pages 156 and 159 equations 4.1 and 5.1. Scalar Mellin inversion supply.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace LeanLab.Linnik1951

/-- P0093 page 157 Gamma kernel domination. Every positive exponential rate
makes the cubic absolute value weight integrable on the whole real line. -/
theorem exp_decay_cubic_integrable473 (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by
  have hk (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(δ * t))) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := 1) (b := δ) (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) (Ioi 0) := by
    apply (((hk 3).add ((hk 2).const_mul 3)).add ((hk 1).const_mul 3)).add (hk 0) |>.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  have hc : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  have hn : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) (Iic 0) := by
    have hn := (show IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3)
      (Ici (-0)) from by simpa using hc).comp_neg_Iic
    simpa only [abs_neg] using hn
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

/-- P0093 page 157 Gamma decay. Gamma is integrable on every vertical line
in the closed strip from one half to three halves. -/
theorem gamma_vertical_integrable473 (σ : ℝ) (hlo : 1 / 2 ≤ σ) (hhi : σ ≤ 3 / 2) :
    Complex.VerticalIntegrable Complex.Gamma σ := by
  have hd := exp_decay_cubic_integrable473 (Real.pi / 2) (by positivity)
  have hc : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    intro n he
    have hre := congrArg Complex.re he
    simp at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hb : ∀ t : ℝ, ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (3 * Real.sqrt (2 * Real.pi)) *
        (Real.exp (-((Real.pi / 2) * |t|)) * (1 + |t|) ^ 3) := by
    intro t
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have h := gamma_absolute_decay442 ((σ : ℂ) + (t : ℂ) * Complex.I)
      (by simpa using hlo) (by simpa using hhi)
    have hn : ‖(σ : ℂ) + (t : ℂ) * Complex.I + 1‖ ≤ 3 + |t| := by
      have hn := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + (t : ℂ) * Complex.I + 1)
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hre, him,
        add_zero] at hn
      rw [abs_of_nonneg (by linarith : 0 ≤ σ + 1)] at hn
      linarith
    have hp : 3 + |t| ≤ 3 * (1 + |t|) ^ 3 := by
      nlinarith [abs_nonneg t, sq_nonneg |t|, pow_nonneg (abs_nonneg t) 3]
    rw [him] at h
    calc
      _ ≤ Real.sqrt (2 * Real.pi) * ‖(σ : ℂ) + (t : ℂ) * Complex.I + 1‖ *
          Real.exp (-(Real.pi * |t| / 2)) := h
      _ ≤ Real.sqrt (2 * Real.pi) * (3 * (1 + |t|) ^ 3) *
          Real.exp (-(Real.pi * |t| / 2)) := by
        gcongr
        exact hn.trans hp
      _ = _ := by
        rw [show -(Real.pi * |t| / 2) = -((Real.pi / 2) * |t|) by ring]
        ring
  exact (hd.const_mul (3 * Real.sqrt (2 * Real.pi))).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
/-- P0093 page 159 equation 5.1 scalar supply. Mellin inversion of Gamma
is the exponential whenever the vertical Gamma integral is integrable. -/
theorem inverse_mellin_gamma_of_vertical473 (σ : ℝ) (hσ : 0 < σ) (hV : Complex.VerticalIntegrable Complex.Gamma σ)
    (x : ℝ) (hx : 0 < x) :
    mellinInv σ Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  let f : ℝ → ℂ := fun y => (Real.exp (-y) : ℂ)
  have hf : MellinConvergent f (σ : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (s := (σ : ℂ)) (by simpa using hσ))
  have hm (t : ℝ) : mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) =
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    change mellin (fun y : ℝ => (Real.exp (-y) : ℂ)) _ = _
    rw [← Complex.GammaIntegral_eq_mellin]
    exact (Complex.Gamma_eq_integral (by simpa using hσ)).symm
  have hVM : Complex.VerticalIntegrable (mellin f) σ := by
    unfold Complex.VerticalIntegrable at hV ⊢
    simpa only [hm] using hV
  have he := mellinInv_mellin_eq σ f hx hf hVM (by fun_prop)
  unfold mellinInv at he ⊢
  simpa only [hm, f] using he

/-- P0093 page 159 equation 5.1 scalar supply. Mellin inversion of Gamma
is the exponential throughout the strip used by the shifted contour. -/
theorem inverse_mellin_gamma473 (σ : ℝ) (hlo : 1 / 2 ≤ σ) (hhi : σ ≤ 3 / 2)
    (x : ℝ) (hx : 0 < x) :
    mellinInv σ Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  exact inverse_mellin_gamma_of_vertical473 σ (by linarith)
    (gamma_vertical_integrable473 σ hlo hhi) x hx

/-- P0093 page 159 equation 5.1 scalar supply. At phase zero the Mellin
kernel applied to one positive exponential frequency gives its damping factor. -/
theorem mellin_single_exponential473 (N : ℕ) (hN : 3 ≤ N) (a : ℝ) (ha : 0 < a) :
    mellinU1622 N (fun t => (a : ℂ) ^ (-(mellinLine1622 N t))) 0 =
      (Real.exp (-a / N) : ℂ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hNr)
  have hInv := inverse_mellin_gamma473 (1 / 2 + 1 / Real.log (N : ℝ))
    (le_add_of_nonneg_right (by positivity))
    (by
      have h := (div_le_one (by linarith : 0 < Real.log (N : ℝ))).mpr hlog
      linarith)
    (a / N) (div_pos ha hNpos)

  rw [neg_div, ← hInv]
  unfold mellinU1622 mellinInv
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul,
    Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : ((a / (N : ℝ) : ℝ) : ℂ) ^ (-(mellinLine1622 N t)) =
      ((1 / (N : ℝ) : ℝ) : ℂ) ^ (-(mellinLine1622 N t)) * (a : ℂ) ^ (-(mellinLine1622 N t)) := by
    rw [show a / (N : ℝ) = (1 / (N : ℝ)) * a by ring, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) ha.le _
  change _ = ((a / (N : ℝ) : ℝ) : ℂ) ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)
  rw [he]
  ring

/-- P0093 page 159 equation 5.1 scalar supply. The real positive Mellin
kernel is integrable whenever Gamma is vertically integrable. -/
theorem gamma_real_kernel_integrable473 (σ : ℝ) (hV : Complex.VerticalIntegrable Complex.Gamma σ)
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc : Continuous (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')
  apply (hV.norm.const_mul (x ^ (-σ))).mono'
    (hc.aestronglyMeasurable.mul hV.aestronglyMeasurable)
  filter_upwards with t
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- P0093 page 159 equation 5.1 finite truncation supply. Mellin inversion
of a finite character style exponential sum evaluates every positive frequency
with its exponential damping. No infinite sum interchange occurs. -/
theorem inverse_mellin_finite_gamma473 {ι : Type*} (σ : ℝ)
    (hlo : 1 / 2 ≤ σ) (hhi : σ ≤ 3 / 2) (s : Finset ι) (a : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i ∈ s, 0 < a i) (x : ℝ) (hx : 0 < x) :
    mellinInv σ (fun z => Complex.Gamma z * ∑ i ∈ s, c i * (a i : ℂ) ^ (-z)) x =
      ∑ i ∈ s, c i * (Real.exp (-(x * a i)) : ℂ) := by
  have hK (y : ℝ) (hy : 0 < y) := gamma_real_kernel_integrable473 σ
    (gamma_vertical_integrable473 σ hlo hhi) y hy
  have hInv (y : ℝ) (hy : 0 < y) := inverse_mellin_gamma473 σ hlo hhi y hy
  let K : ℝ → ℝ → ℂ := fun y t =>
    (y : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
  have heq (i : ι) (hi : i ∈ s) (t : ℝ) :
      (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (c i * (a i : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))) = c i * K (x * a i) t := by
    dsimp [K]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (ha i hi).le]
    ring
  have hsum : (fun t : ℝ =>
      (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) *
          ∑ i ∈ s, c i * (a i : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))) =
      fun t : ℝ => ∑ i ∈ s, c i * K (x * a i) t := by
    funext t
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => heq i hi t)
  simp only [mellinInv, smul_eq_mul, Complex.real_smul]
  rw [hsum, integral_finsetSum s (fun i hi => (hK _ (mul_pos hx (ha i hi))).const_mul (c i)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  have h := hInv (x * a i) (mul_pos hx (ha i hi))
  simp only [mellinInv, smul_eq_mul, Complex.real_smul] at h
  change _ = c i * _
  rw [mul_left_comm, show (∫ t : ℝ, K (x * a i) t) =
    ∫ t : ℝ, ((x * a i : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) from rfl, h]

end LeanLab.Linnik1951
