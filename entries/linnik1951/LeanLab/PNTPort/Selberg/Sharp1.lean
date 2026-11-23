module

public import LeanLab.PNTPort.Selberg.LeftLine

/-!
# Sharp windows, part 1: squeezing `ψ` between difference quotients of `ψ₁`

Lab proof, unit U-5924, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input, unconditional except where RH is a hypothesis.

`Qr a η = (ψ₁(e^{a+η}) - ψ₁(e^a))/(e^a(e^η - 1))`, the mean of `ψ` over `[e^a, e^{a+η}]`.

* `Qr_ge`, `Qr_le`: `ψ(e^a) ≤ Qr a η ≤ ψ(e^{a+η})`, since `ψ` is monotone;
* `Qr_dec`: `Qr a η = e^a(e^η + 1)/2 - log 2π - Zq a + Rq a`, the main, zero and remainder parts
  from the explicit formula for `ψ₁`;
* `Zq_RH`: under RH, `Zq a = e^{a/2} Σ_ρ bq ρ e^{iγa}`, `bq ρ = m(ρ)(e^{η(ρ+1)} - 1)/((e^η - 1)ρ(ρ+1))`;
* `norm_bq_le`: under RH, `‖bq ρ‖ ≤ 6 m(ρ)/‖ρ‖`;
* `rem_first_difference`: `‖Rem(v + η) - Rem(v)‖ ≤ K η^{3/8} e^{v/2}`, so `‖Rq a‖ ≤ K η^{-5/8} e^{-a/2}`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

local notation "ζ" => riemannZeta

/-! ## The difference quotient -/

lemma psi1_eq_Rg {x : ℝ} (hx : 0 < x) {M : ℕ} (h : x ≤ M) :
    psi1 x = ((LZCesaroShort.Rg M x : ℝ) : ℂ) := by
  unfold psi1; rw [LZCesaroShort.Rg_eq hx h]

/-- The mean of `ψ` over `[e^a, e^{a+η}]`. -/
noncomputable def Qr (a η : ℝ) : ℝ :=
  (LZCesaroShort.Rg ⌈Real.exp (a + η)⌉₊ (Real.exp (a + η)) -
    LZCesaroShort.Rg ⌈Real.exp (a + η)⌉₊ (Real.exp a)) / (Real.exp a * (Real.exp η - 1))

lemma den_pos {a η : ℝ} (hη : 0 < η) : 0 < Real.exp a * (Real.exp η - 1) := by
  have : 1 < Real.exp η := Real.one_lt_exp_iff.mpr hη
  have := Real.exp_pos a
  nlinarith

lemma exp_add_sub (a η : ℝ) : Real.exp (a + η) - Real.exp a = Real.exp a * (Real.exp η - 1) := by
  rw [Real.exp_add]; ring

lemma Qr_ge {a η : ℝ} (hη : 0 < η) : Chebyshev.psi (Real.exp a) ≤ Qr a η := by
  unfold Qr
  rw [le_div_iff₀ (den_pos hη), ← exp_add_sub, mul_comm]
  exact ExplicitPsi1.Rg_sub_ge (Real.exp_pos a).le
    (Real.exp_le_exp.mpr (by linarith))
    ((Real.exp_le_exp.mpr (by linarith)).trans (Nat.le_ceil _))

lemma Qr_le {a η : ℝ} (hη : 0 < η) : Qr a η ≤ Chebyshev.psi (Real.exp (a + η)) := by
  unfold Qr
  rw [div_le_iff₀ (den_pos hη), ← exp_add_sub, mul_comm]
  exact ExplicitPsi1.Rg_sub_le (Real.exp_pos a).le
    (Real.exp_le_exp.mpr (by linarith)) (Nat.le_ceil _)

lemma Qr_complex {a η : ℝ} (hη : 0 < η) : (Qr a η : ℂ) =
    (psi1 (Real.exp (a + η)) - psi1 (Real.exp a)) / ((Real.exp a * (Real.exp η - 1) : ℝ) : ℂ) := by
  have h1 := psi1_eq_Rg (Real.exp_pos (a + η)) (Nat.le_ceil (Real.exp (a + η)))
  have h2 := psi1_eq_Rg (Real.exp_pos a)
    ((Real.exp_le_exp.mpr (by linarith : a ≤ a + η)).trans (Nat.le_ceil (Real.exp (a + η))))
  rw [h1, h2, Qr]; push_cast; ring

/-- The zero sum `Z(v) = Σ_ρ m(ρ) e^{v(ρ+1)}/(ρ(ρ+1))`. -/
noncomputable def Zs (v : ℝ) : ℂ := ∑' ρ : NZs, ztE v ρ.1

/-- The zero part of `Qr`. -/
noncomputable def Zq (a η : ℝ) : ℂ :=
  (Zs (a + η) - Zs a) / ((Real.exp a * (Real.exp η - 1) : ℝ) : ℂ)

/-- The remainder part of `Qr`. -/
noncomputable def Rq (a η : ℝ) : ℂ :=
  (Rem (a + η) - Rem a) / ((Real.exp a * (Real.exp η - 1) : ℝ) : ℂ)

lemma psi1_dec (w : ℝ) : psi1 (Real.exp w) =
    ((Real.exp (2 * w) / 2 - Real.exp w * Real.log (2 * Real.pi) : ℝ) : ℂ) - Zs w + Rem w := by
  unfold Rem Zs; ring

/-- **The decomposition of the difference quotient.** -/
lemma Qr_dec {a η : ℝ} (hη : 0 < η) : (Qr a η : ℂ) =
    ((Real.exp a * (Real.exp η + 1) / 2 - Real.log (2 * Real.pi) : ℝ) : ℂ) - Zq a η + Rq a η := by
  have hD := den_pos (a := a) hη
  have hD' : ((Real.exp a * (Real.exp η - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hD.ne'
  rw [Qr_complex hη, psi1_dec, psi1_dec, Zq, Rq]
  have e : ((Real.exp (2 * (a + η)) / 2 - Real.exp (a + η) * Real.log (2 * Real.pi) : ℝ) : ℂ) -
      ((Real.exp (2 * a) / 2 - Real.exp a * Real.log (2 * Real.pi) : ℝ) : ℂ) =
      ((Real.exp a * (Real.exp η + 1) / 2 - Real.log (2 * Real.pi) : ℝ) : ℂ) *
        ((Real.exp a * (Real.exp η - 1) : ℝ) : ℂ) := by
    rw [show 2 * (a + η) = 2 * a + 2 * η by ring, Real.exp_add, Real.exp_add,
      show 2 * a = a + a by ring, show 2 * η = η + η by ring, Real.exp_add, Real.exp_add]
    push_cast; ring
  have e2 : (((Real.exp (2 * (a + η)) / 2 - Real.exp (a + η) * Real.log (2 * Real.pi) : ℝ) : ℂ) -
      Zs (a + η) + Rem (a + η)) -
      (((Real.exp (2 * a) / 2 - Real.exp a * Real.log (2 * Real.pi) : ℝ) : ℂ) - Zs a + Rem a) =
      ((Real.exp a * (Real.exp η + 1) / 2 - Real.log (2 * Real.pi) : ℝ) : ℂ) *
        ((Real.exp a * (Real.exp η - 1) : ℝ) : ℂ) - (Zs (a + η) - Zs a) + (Rem (a + η) - Rem a) := by
    linear_combination e
  rw [e2, add_div, sub_div, mul_div_cancel_right₀ _ hD']

/-! ## The zero part under RH -/

/-- `bq ρ = m(ρ)(e^{η(ρ+1)} - 1)/((e^η - 1)ρ(ρ+1))`. -/
noncomputable def bq (η : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt ζ ρ : ℂ) * ((cexp (η * (ρ + 1)) - 1) / (((Real.exp η - 1 : ℝ) : ℂ) * (ρ * (ρ + 1))))

lemma ztE_RH0 (hRH : RiemannHypothesis) (u : ℝ) {ρ : ℂ} (hρ : NZ ρ) :
    ztE u ρ = (Real.exp (3 / 2 * u) : ℂ) * ((analyticOrderNatAt ζ ρ : ℂ) / (ρ * (ρ + 1)) *
      cexp (ρ.im * u * I)) := by
  unfold ztE
  have hr := re_half hRH hρ
  have key : (u : ℂ) * (ρ + 1) = ((3 / 2 * u : ℝ) : ℂ) + ρ.im * u * I := by
    apply Complex.ext <;> simp [hr] <;> ring
  rw [key, Complex.exp_add, ← Complex.ofReal_exp]
  ring

lemma summable_shift (v w : ℝ) : Summable (fun ρ : NZs => ztE v ρ.1 * cexp (w * (ρ.1 + 1))) := by
  have := summable_ztE (v + w); simp_rw [ztE_shift] at this; exact this

/-- **The zero part under RH.** -/
lemma Zq_RH (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (a : ℝ) :
    Zq a η = (Real.exp (a / 2) : ℂ) * ∑' ρ : NZs, bq η ρ.1 * cexp (ρ.1.im * a * I) := by
  unfold Zq Zs
  have h1 : (∑' ρ : NZs, ztE (a + η) ρ.1) = ∑' ρ : NZs, ztE a ρ.1 * cexp (η * (ρ.1 + 1)) := by
    congr 1; ext ρ; exact ztE_shift a η ρ.1
  rw [h1, ← (summable_shift a η).tsum_sub (summable_ztE a)]
  have hD := den_pos (a := a) hη
  have hη1 : (Real.exp η - 1) ≠ 0 := by
    have : 1 < Real.exp η := Real.one_lt_exp_iff.mpr hη; linarith
  rw [div_eq_mul_inv, ← tsum_mul_right, ← tsum_mul_left]
  congr 1; ext ρ
  rw [ztE_RH0 hRH a ρ.2]
  unfold bq
  have hρ0 : ρ.1 ≠ 0 := NZ_ne_zero ρ.2
  have hρ1 : ρ.1 + 1 ≠ 0 := NZ_add_one_ne_zero ρ.2
  have hea : (Real.exp a : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos a).ne'
  have e32 : (Real.exp (3 / 2 * a) : ℂ) = (Real.exp (a / 2) : ℂ) * (Real.exp a : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
  rw [e32]
  push_cast
  field_simp

lemma norm_exp_sub_one_le_six {z : ℂ} (hz : |z.re| ≤ 3 / 2) : ‖cexp z - 1‖ ≤ 6 * min ‖z‖ 1 := by
  rcases le_or_gt ‖z‖ 1 with h | h
  · rw [min_eq_left h]
    have := Complex.norm_exp_sub_one_le h
    linarith [norm_nonneg z]
  · rw [min_eq_right h.le]
    have he1 : ‖cexp z‖ ≤ Real.exp (3 / 2) := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hz)
    have h5 := exp_three_halves_lt
    calc ‖cexp z - 1‖ ≤ ‖cexp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 6 * 1 := by rw [norm_one]; linarith

/-- Under RH, `‖bq ρ‖ ≤ 6 m(ρ)/‖ρ‖` for `0 < η ≤ 1`. -/
lemma norm_bq_le (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {ρ : ℂ}
    (hρ : NZ ρ) : ‖bq η ρ‖ ≤ 6 * mz ρ / ‖ρ‖ := by
  have hr := re_half hRH hρ
  have hn : 1 / 2 ≤ ‖ρ‖ := by rw [← hr]; exact (le_abs_self _).trans (abs_re_le_norm ρ)
  have hp : 0 < ‖ρ‖ := by linarith
  have h1 : ‖ρ‖ ≤ ‖ρ + 1‖ := norm_le_norm_add_one (by rw [hr]; norm_num)
  have hp1 : 0 < ‖ρ + 1‖ := lt_of_lt_of_le hp h1
  have hz : |((η : ℂ) * (ρ + 1)).re| ≤ 3 / 2 := by
    have : ((η : ℂ) * (ρ + 1)).re = η * (3 / 2) := by
      simp only [mul_re, ofReal_re, ofReal_im, add_re, one_re, add_im, one_im, zero_mul,
        sub_zero, hr]
      ring
    rw [this, abs_of_nonneg (by positivity)]; nlinarith
  have hE := norm_exp_sub_one_le_six hz
  have hzn : ‖(η : ℂ) * (ρ + 1)‖ = η * ‖ρ + 1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  rw [hzn] at hE
  have hE' : ‖cexp (η * (ρ + 1)) - 1‖ ≤ 6 * (η * ‖ρ + 1‖) := hE.trans (by
    gcongr; exact min_le_left _ _)
  have hη' : η ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
  have hηpos : 0 < Real.exp η - 1 := by linarith
  have hm := mz_nonneg ρ
  unfold bq
  rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hηpos]
  rw [le_div_iff₀ hp]
  have hden : 0 < (Real.exp η - 1) * (‖ρ‖ * ‖ρ + 1‖) := by positivity
  calc (analyticOrderNatAt ζ ρ : ℝ) *
        (‖cexp (η * (ρ + 1)) - 1‖ / ((Real.exp η - 1) * (‖ρ‖ * ‖ρ + 1‖))) * ‖ρ‖
      ≤ (analyticOrderNatAt ζ ρ : ℝ) *
        (6 * (η * ‖ρ + 1‖) / (η * (‖ρ‖ * ‖ρ + 1‖))) * ‖ρ‖ := by
        gcongr
    _ = 6 * mz ρ := by unfold mz; field_simp

/-- Under RH, `‖bq ρ‖ ≤ (6/η) hw ρ`, for summability. -/
lemma norm_bq_le_hw (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {ρ : ℂ}
    (hρ : NZ ρ) : ‖bq η ρ‖ ≤ 6 / η * hw ρ := by
  have hr := re_half hRH hρ
  have hz : |((η : ℂ) * (ρ + 1)).re| ≤ 3 / 2 := by
    have : ((η : ℂ) * (ρ + 1)).re = η * (3 / 2) := by
      simp only [mul_re, ofReal_re, ofReal_im, add_re, one_re, add_im, one_im, zero_mul,
        sub_zero, hr]
      ring
    rw [this, abs_of_nonneg (by positivity)]; nlinarith
  have hE : ‖cexp (η * (ρ + 1)) - 1‖ ≤ 6 := (norm_exp_sub_one_le_six hz).trans (by
    have := min_le_right ‖(η : ℂ) * (ρ + 1)‖ 1; linarith)
  have hη' : η ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
  have hηpos : 0 < Real.exp η - 1 := by linarith
  have hq : 0 < ‖ρ * (ρ + 1)‖ := by
    rw [norm_pos_iff]; exact mul_ne_zero (NZ_ne_zero hρ) (NZ_add_one_ne_zero hρ)
  unfold bq hw
  rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hηpos]
  have hm : (0 : ℝ) ≤ analyticOrderNatAt ζ ρ := by positivity
  calc (analyticOrderNatAt ζ ρ : ℝ) * (‖cexp (η * (ρ + 1)) - 1‖ /
        ((Real.exp η - 1) * ‖ρ * (ρ + 1)‖))
      ≤ (analyticOrderNatAt ζ ρ : ℝ) * (6 / (η * ‖ρ * (ρ + 1)‖)) := by
        gcongr
    _ = 6 / η * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ * (ρ + 1)‖) := by field_simp

/-! ## The remainder part -/

lemma min_le_rpow {a : ℝ} (ha : 0 ≤ a) : min a 1 ≤ a ^ (3 / 8 : ℝ) := by
  rcases le_or_gt a 1 with h | h
  · rcases eq_or_lt_of_le ha with h0 | h0
    · rw [← h0]; simp
    · refine (min_le_left _ _).trans ?_
      calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
        _ ≤ a ^ (3 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h0 h (by norm_num)
  · exact (min_le_right _ _).trans (Real.one_le_rpow h.le (by norm_num))

/-- **The first difference of the remainder**, unconditional. -/
theorem rem_first_difference : ∃ K : ℝ, 0 ≤ K ∧ ∀ v η : ℝ, 0 ≤ η → η ≤ 1 →
    ‖Rem (v + η) - Rem v‖ ≤ K * η ^ (3 / 8 : ℝ) * Real.exp (v / 2) := by
  obtain ⟨A, hA0, hA⟩ := norm_Fg_le
  set I0 := ∫ t : ℝ, (1 + ‖t‖) ^ (-(9 / 8 : ℝ))
  have hI0int : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(9 / 8 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hI0 : 0 ≤ I0 := integral_nonneg fun t => by positivity
  refine ⟨1 / (2 * Real.pi) * (6 * A * I0), by positivity, fun v η hη0 hη1 => ?_⟩
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
  have hpt : ∀ t : ℝ, ‖fl v t * (cexp (η * (sl t + 1)) - 1)‖ ≤
      6 * A * Real.exp (v / 2) * η ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (-(9 / 8 : ℝ)) := by
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
    have hmin := min_le_rpow (mul_nonneg hη0 (norm_nonneg (sl t + 1)))
    have hpow : (η * ‖sl t + 1‖) ^ (3 / 8 : ℝ) ≤ η ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (3 / 8 : ℝ) := by
      rw [Real.mul_rpow hη0 (norm_nonneg _)]
      gcongr
    have hEz : ‖cexp (η * (sl t + 1)) - 1‖ ≤ 6 * (η ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (3 / 8 : ℝ)) := by
      linarith
    have hu : 0 < 1 + ‖t‖ := by positivity
    have hc : (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖t‖) ^ (3 / 8 : ℝ) = (1 + ‖t‖) ^ (-(9 / 8 : ℝ)) := by
      rw [← Real.rpow_add hu]; norm_num
    simp only [fl]
    rw [norm_mul, norm_mul, norm_cexp_line]
    calc ‖Fg (sl t)‖ * Real.exp (v / 2) * ‖cexp (η * (sl t + 1)) - 1‖
        ≤ (A * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) * Real.exp (v / 2) *
            (6 * (η ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (3 / 8 : ℝ))) := by
          gcongr
          exact hA t
      _ = 6 * A * Real.exp (v / 2) * η ^ (3 / 8 : ℝ) *
            ((1 + ‖t‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖t‖) ^ (3 / 8 : ℝ)) := by ring
      _ = _ := by rw [hc]
  have hg : Integrable (fun t : ℝ =>
      6 * A * Real.exp (v / 2) * η ^ (3 / 8 : ℝ) * (1 + ‖t‖) ^ (-(9 / 8 : ℝ))) :=
    hI0int.const_mul _
  have hle := norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
  rw [integral_const_mul] at hle
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, fl v t * (cexp (η * (sl t + 1)) - 1)‖
      ≤ 1 / (2 * Real.pi) * (6 * A * Real.exp (v / 2) * η ^ (3 / 8 : ℝ) * I0) := by gcongr
    _ = 1 / (2 * Real.pi) * (6 * A * I0) * η ^ (3 / 8 : ℝ) * Real.exp (v / 2) := by ring

/-- `‖Rq a η‖ ≤ K η^{-5/8} e^{-a/2}`. -/
lemma norm_Rq_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ a η : ℝ, 0 < η → η ≤ 1 →
    ‖Rq a η‖ ≤ K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(a / 2)) := by
  obtain ⟨K, hK0, hK⟩ := rem_first_difference
  refine ⟨K, hK0, fun a η hη hη1 => ?_⟩
  have hD := den_pos (a := a) hη
  unfold Rq
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, div_le_iff₀ hD]
  have hη' : η ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
  have hpow : η ^ (-(5 / 8) : ℝ) * η = η ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add_one hη.ne']; norm_num
  have hexp : Real.exp (-(a / 2)) * Real.exp a = Real.exp (a / 2) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖Rem (a + η) - Rem a‖ ≤ K * η ^ (3 / 8 : ℝ) * Real.exp (a / 2) := hK a η hη.le hη1
    _ = K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(a / 2)) * (Real.exp a * η) := by
        rw [← hpow, ← hexp]; ring
    _ ≤ K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(a / 2)) * (Real.exp a * (Real.exp η - 1)) := by
        gcongr

end LeanLab.PNTPort.Selberg

