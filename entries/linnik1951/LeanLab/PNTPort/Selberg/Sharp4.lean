module

public import LeanLab.PNTPort.Selberg.Sharp3

/-!
# Sharp windows, part 4: the theorem

Lab proof, unit U-5924, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. `selberg_sharp` is CONDITIONAL ON RiemannHypothesis only; see Sharp3.lean for the plain
statement and the route.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

local notation "ζ" => riemannZeta

/-- The main part of `Qr`. -/
noncomputable def Mp (a η : ℝ) : ℝ := Real.exp a * (Real.exp η + 1) / 2 - Real.log (2 * Real.pi)

lemma exp_sub_one_le {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) : Real.exp η - 1 ≤ 2 * η := by
  have := Real.abs_exp_sub_one_le (x := η) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  exact (le_abs_self _).trans this

lemma one_sub_exp_neg_le {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) : 1 - Real.exp (-η) ≤ 2 * η := by
  have := Real.abs_exp_sub_one_le (x := -η) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  rw [abs_neg, abs_of_nonneg h0, abs_sub_comm] at this
  exact (le_abs_self _).trans this

lemma exp_le_three {x : ℝ} (h : x ≤ 1) : Real.exp x ≤ 3 :=
  (Real.exp_le_exp.mpr h).trans (by have := Real.exp_one_lt_d9; linarith)

lemma Mp_hi {u δ η : ℝ} (hη0 : 0 < η) (hηδ : η ≤ δ) (hδ1 : δ ≤ 1) :
    |Mp (u + δ) η - Mp (u - η) η - (Real.exp (u + δ) - Real.exp u)| ≤ 4 * η * Real.exp u := by
  have e : Mp (u + δ) η - Mp (u - η) η - (Real.exp (u + δ) - Real.exp u) =
      Real.exp u * (Real.exp δ * (Real.exp η - 1) + (1 - Real.exp (-η))) / 2 := by
    unfold Mp
    rw [show u - η = u + -η by ring, Real.exp_add, Real.exp_add]
    have h : Real.exp (-η) * Real.exp η = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-(Real.exp u) / 2) * h
  rw [e]
  have h1 := exp_sub_one_le hη0.le (hηδ.trans hδ1)
  have h2 := one_sub_exp_neg_le hη0.le (hηδ.trans hδ1)
  have h3 := exp_le_three hδ1
  have h4 : 0 ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
  have h5 : 0 ≤ 1 - Real.exp (-η) := by
    have : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hu := Real.exp_pos u
  have hd := Real.exp_pos δ
  rw [abs_of_nonneg (by positivity)]
  have : Real.exp δ * (Real.exp η - 1) ≤ 3 * (2 * η) := mul_le_mul h3 h1 h4 (by norm_num)
  nlinarith

lemma Mp_lo {u δ η : ℝ} (hη0 : 0 < η) (hηδ : η ≤ δ) (hδ1 : δ ≤ 1) :
    |Mp (u + δ - η) η - Mp u η - (Real.exp (u + δ) - Real.exp u)| ≤ 4 * η * Real.exp u := by
  have e : Mp (u + δ - η) η - Mp u η - (Real.exp (u + δ) - Real.exp u) =
      -(Real.exp u * (Real.exp (δ - η) * (Real.exp η - 1) + (Real.exp η - 1)) / 2) := by
    have h1 : Real.exp (u + δ - η) = Real.exp u * Real.exp (δ - η) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (u + δ) = Real.exp u * Real.exp (δ - η) * Real.exp η := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    unfold Mp; rw [h1, h2]; ring
  rw [e, abs_neg]
  have h1 := exp_sub_one_le hη0.le (hηδ.trans hδ1)
  have h3 := exp_le_three (show δ - η ≤ 1 by linarith)
  have h4 : 0 ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
  have hu := Real.exp_pos u
  have hd := Real.exp_pos (δ - η)
  rw [abs_of_nonneg (by positivity)]
  have : Real.exp (δ - η) * (Real.exp η - 1) ≤ 3 * (2 * η) := mul_le_mul h3 h1 h4 (by norm_num)
  nlinarith

/-- **The window splits.** `Qr a η - Qr b η = (Mp a - Mp b) - (Zq a - Zq b) + (Rq a - Rq b)`. -/
lemma Qr_sub {a b η : ℝ} (hη : 0 < η) : ((Qr a η - Qr b η : ℝ) : ℂ) =
    ((Mp a η - Mp b η : ℝ) : ℂ) - (Zq a η - Zq b η) + (Rq a η - Rq b η) := by
  push_cast
  rw [Qr_dec hη, Qr_dec hη]
  unfold Mp; push_cast; ring

/-- One window bound: `|Qr a - Qr b - m| ≤ |Mp a - Mp b - m| + ‖Zq a - Zq b‖ + ‖Rq a‖ + ‖Rq b‖`. -/
lemma window_bound {a b η m : ℝ} (hη : 0 < η) :
    |Qr a η - Qr b η - m| ≤ |Mp a η - Mp b η - m| + ‖Zq a η - Zq b η‖ + ‖Rq a η‖ + ‖Rq b η‖ := by
  have e : ((Qr a η - Qr b η - m : ℝ) : ℂ) =
      ((Mp a η - Mp b η - m : ℝ) : ℂ) - (Zq a η - Zq b η) + (Rq a η - Rq b η) := by
    have := Qr_sub (a := a) (b := b) hη
    push_cast at this ⊢
    linear_combination this
  have hn := congrArg norm e
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn]
  calc ‖((Mp a η - Mp b η - m : ℝ) : ℂ) - (Zq a η - Zq b η) + (Rq a η - Rq b η)‖
      ≤ ‖((Mp a η - Mp b η - m : ℝ) : ℂ)‖ + ‖Zq a η - Zq b η‖ + (‖Rq a η‖ + ‖Rq b η‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        · exact norm_sub_le _ _
        · exact norm_sub_le _ _
    _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]; ring

/-- The normalised error of the sharp window. -/
noncomputable def Nw (δ u : ℝ) : ℝ :=
  Real.exp (-(u / 2)) * (Chebyshev.psi (Real.exp (u + δ)) - Chebyshev.psi (Real.exp u) -
    (Real.exp (u + δ) - Real.exp u))

lemma measurable_Nw (δ : ℝ) : Measurable (Nw δ) := by
  have hψ : Measurable (fun x : ℝ => Chebyshev.psi x) := Chebyshev.psi_mono.measurable
  unfold Nw
  have h1 : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp (u + δ))) :=
    hψ.comp (Real.measurable_exp.comp (measurable_id.add_const δ))
  have h2 : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp u)) := hψ.comp Real.measurable_exp
  exact (Continuous.measurable (by fun_prop)).mul ((h1.sub h2).sub (Continuous.measurable (by fun_prop)))

/-- **Selberg's mean square under RH for sharp multiplicative windows.** -/
theorem selberg_sharp (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ η : ℝ, 0 < η → η ≤ δ → δ ≤ 1 → ∀ U : ℝ,
    Integrable (fun u => Nw δ u ^ 2 * gw U u) ∧
      ∫ u, Nw δ u ^ 2 * gw U u ≤ C * (δ * (Real.log (1 / δ) + 3) ^ 2 +
        η ^ 2 * Real.exp U + η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U))) := by
  obtain ⟨Cw, hCw0, hwin⟩ := window_mean hRH
  obtain ⟨K, hK0, hRq⟩ := norm_Rq_le
  set c0 := ∫ u, gw 0 u with hc0def
  have hc0 : 0 ≤ c0 := integral_nonneg (gw_nonneg 0)
  refine ⟨8 * Cw + 256 * Real.exp (1 / 2) * c0 + 256 * K ^ 2 * Real.exp 2 * c0,
    by positivity, fun δ η hη0 hηδ hδ1 U => ?_⟩
  have hδ0 : 0 < δ := lt_of_lt_of_le hη0 hηδ
  have hη1 : η ≤ 1 := hηδ.trans hδ1
  have habs : ∀ w : ℝ, 0 ≤ w → w ≤ δ → |w| ≤ δ := fun w h0 h1 => by rw [abs_of_nonneg h0]; exact h1
  -- the two windows
  set dhi := dW η δ (-η)
  set dlo := dW η (δ - η) 0
  obtain ⟨Ihi, Bhi⟩ := hwin δ η hη0 hη1 hδ0 hδ1 δ (-η) (habs δ hδ0.le le_rfl)
    (by rw [abs_neg, abs_of_pos hη0]; exact hηδ) U
  obtain ⟨Ilo, Blo⟩ := hwin δ η hη0 hη1 hδ0 hδ1 (δ - η) 0 (habs _ (by linarith) (by linarith))
    (by rw [abs_zero]; exact hδ0.le) U
  set κ := 8 * K * η ^ (-(5 / 8) : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  -- the pointwise bound
  have hpt : ∀ u : ℝ, |Nw δ u| ≤ ‖fS dhi u‖ + ‖fS dlo u‖ + 8 * η * Real.exp (u / 2) +
      κ * Real.exp (-(1 * u)) := by
    intro u
    set A := Chebyshev.psi (Real.exp (u + δ)) - Chebyshev.psi (Real.exp u)
    set m := Real.exp (u + δ) - Real.exp u
    set hi := Qr (u + δ) η - Qr (u - η) η
    set lo := Qr (u + δ - η) η - Qr u η
    have hhi : A ≤ hi := by
      have h1 := Qr_ge (a := u + δ) hη0
      have h2 := Qr_le (a := u - η) hη0
      rw [show u - η + η = u by ring] at h2
      simp only [A, hi]; linarith
    have hlo : lo ≤ A := by
      have h1 := Qr_le (a := u + δ - η) hη0
      have h2 := Qr_ge (a := u) hη0
      rw [show u + δ - η + η = u + δ by ring] at h1
      simp only [A, lo]; linarith
    have hAm : |A - m| ≤ |hi - m| + |lo - m| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le (lo - m), abs_nonneg (hi - m)]
      · linarith [le_abs_self (hi - m), abs_nonneg (lo - m)]
    -- the zero parts
    have zhi : Zq (u + δ) η - Zq (u - η) η = (Real.exp (u / 2) : ℂ) * fS dhi u := by
      rw [show u - η = u + -η by ring]
      exact Zq_window hRH hη0 hη1 u (by rw [abs_of_pos hδ0]; exact hδ1)
        (by rw [abs_neg, abs_of_pos hη0]; exact hη1)
    have zlo : Zq (u + δ - η) η - Zq u η = (Real.exp (u / 2) : ℂ) * fS dlo u := by
      have := Zq_window hRH hη0 hη1 u (w₁ := δ - η) (w₂ := 0)
        (by rw [abs_of_nonneg (by linarith)]; linarith) (by rw [abs_zero]; norm_num)
      rw [show u + (δ - η) = u + δ - η by ring, add_zero] at this
      exact this
    have hnz : ∀ f : ℂ, ‖(Real.exp (u / 2) : ℂ) * f‖ = Real.exp (u / 2) * ‖f‖ := fun f => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    -- the remainders
    have hK' : ∀ a : ℝ, u - 1 ≤ a → ‖Rq a η‖ ≤ 2 * K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(u / 2)) := by
      intro a ha
      refine (hRq a η hη0 hη1).trans ?_
      have : Real.exp (-(a / 2)) ≤ 2 * Real.exp (-(u / 2)) := by
        calc Real.exp (-(a / 2)) ≤ Real.exp (1 / 2 + -(u / 2)) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (1 / 2) * Real.exp (-(u / 2)) := Real.exp_add _ _
          _ ≤ 2 * Real.exp (-(u / 2)) := by
            gcongr
            have h := Real.exp_one_lt_d9
            have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
            nlinarith [Real.exp_pos (1 / 2)]
      have : 0 ≤ K * η ^ (-(5 / 8) : ℝ) := by positivity
      nlinarith
    have hwhi := window_bound (a := u + δ) (b := u - η) (m := m) hη0
    have hwlo := window_bound (a := u + δ - η) (b := u) (m := m) hη0
    rw [zhi, hnz] at hwhi
    rw [zlo, hnz] at hwlo
    have r1 := hK' (u + δ) (by linarith)
    have r2 := hK' (u - η) (by linarith)
    have r3 := hK' (u + δ - η) (by linarith)
    have r4 := hK' u (by linarith)
    have m1 := Mp_hi (u := u) hη0 hηδ hδ1
    have m2 := Mp_lo (u := u) hη0 hηδ hδ1
    have hsum : |A - m| ≤ Real.exp (u / 2) * (‖fS dhi u‖ + ‖fS dlo u‖) + 8 * η * Real.exp u +
        8 * K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(u / 2)) := by
      simp only [hi, lo, m] at hAm hwhi hwlo
      linarith
    have he1 : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
      rw [← Real.exp_add]; ring_nf
    have he2 : Real.exp (-(u / 2)) * Real.exp (u / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have he3 : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-(1 * u)) := by
      rw [← Real.exp_add]; ring_nf
    unfold Nw
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hpos := Real.exp_pos (-(u / 2))
    calc Real.exp (-(u / 2)) * |A - m|
        ≤ Real.exp (-(u / 2)) * (Real.exp (u / 2) * (‖fS dhi u‖ + ‖fS dlo u‖) + 8 * η * Real.exp u +
          8 * K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(u / 2))) := by gcongr
      _ = (Real.exp (-(u / 2)) * Real.exp (u / 2)) * (‖fS dhi u‖ + ‖fS dlo u‖) +
          8 * η * (Real.exp (-(u / 2)) * Real.exp u) +
          8 * K * η ^ (-(5 / 8) : ℝ) * (Real.exp (-(u / 2)) * Real.exp (-(u / 2))) := by ring
      _ = ‖fS dhi u‖ + ‖fS dlo u‖ + 8 * η * Real.exp (u / 2) +
          8 * K * η ^ (-(5 / 8) : ℝ) * Real.exp (-(1 * u)) := by rw [he1, he2, he3]; ring
      _ = _ := by rw [hκ]
  set A2 := δ * (Real.log (1 / δ) + 3) ^ 2 with hA2
  have hG : ∀ u : ℝ, Nw δ u ^ 2 * gw U u ≤
      4 * (‖fS dhi u‖ ^ 2 * gw U u) + 4 * (‖fS dlo u‖ ^ 2 * gw U u) +
        (256 * η ^ 2) * (Real.exp (-(-1 * u)) * gw U u) +
        (4 * κ ^ 2) * (Real.exp (-(2 * u)) * gw U u) := by
    intro u
    have h := hpt u
    have hg := gw_nonneg U u
    set p := ‖fS dhi u‖
    set q := ‖fS dlo u‖
    set r := 8 * η * Real.exp (u / 2)
    set t := κ * Real.exp (-(1 * u))
    have hp : 0 ≤ p := norm_nonneg _
    have hq : 0 ≤ q := norm_nonneg _
    have hr : 0 ≤ r := by positivity
    have ht : 0 ≤ t := by positivity
    have hsq : Nw δ u ^ 2 ≤ 4 * p ^ 2 + 4 * q ^ 2 + 4 * r ^ 2 + 4 * t ^ 2 := by
      have h0 : Nw δ u ^ 2 ≤ (p + q + r + t) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - t), sq_nonneg (q - r),
        sq_nonneg (q - t), sq_nonneg (r - t)]
    have er : 4 * r ^ 2 = 256 * η ^ 2 * Real.exp (-(-1 * u)) := by
      have : Real.exp (u / 2) ^ 2 = Real.exp (-(-1 * u)) := by
        rw [← Real.exp_nat_mul]; ring_nf
      simp only [r]; rw [mul_pow, this]; ring
    have et : 4 * t ^ 2 = 4 * κ ^ 2 * Real.exp (-(2 * u)) := by
      have : Real.exp (-(1 * u)) ^ 2 = Real.exp (-(2 * u)) := by
        rw [← Real.exp_nat_mul]; ring_nf
      simp only [t]; rw [mul_pow, this]; ring
    calc Nw δ u ^ 2 * gw U u ≤ (4 * p ^ 2 + 4 * q ^ 2 + 4 * r ^ 2 + 4 * t ^ 2) * gw U u :=
          mul_le_mul_of_nonneg_right hsq hg
      _ = _ := by rw [er, et]; ring
  have I1 : Integrable (fun u : ℝ => 4 * (‖fS dhi u‖ ^ 2 * gw U u)) := Ihi.const_mul 4
  have I2 : Integrable (fun u : ℝ => 4 * (‖fS dlo u‖ ^ 2 * gw U u)) := Ilo.const_mul 4
  have I3 : Integrable (fun u : ℝ => (256 * η ^ 2) * (Real.exp (-(-1 * u)) * gw U u)) :=
    (integrable_exp_gw (-1) U).const_mul _
  have I4 : Integrable (fun u : ℝ => (4 * κ ^ 2) * (Real.exp (-(2 * u)) * gw U u)) :=
    (integrable_exp_gw 2 U).const_mul _
  have I12 : Integrable (fun u : ℝ => 4 * (‖fS dhi u‖ ^ 2 * gw U u) +
      4 * (‖fS dlo u‖ ^ 2 * gw U u)) := I1.add I2
  have I123 : Integrable (fun u : ℝ => 4 * (‖fS dhi u‖ ^ 2 * gw U u) +
      4 * (‖fS dlo u‖ ^ 2 * gw U u) + (256 * η ^ 2) * (Real.exp (-(-1 * u)) * gw U u)) :=
    I12.add I3
  have IG := I123.add I4
  have hLint : Integrable (fun u => Nw δ u ^ 2 * gw U u) := by
    refine IG.mono' (((measurable_Nw δ).pow_const 2).mul
      (gw_continuous U).measurable).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gw_nonneg U u))]
    exact hG u
  refine ⟨hLint, ?_⟩
  calc ∫ u, Nw δ u ^ 2 * gw U u
      ≤ ∫ u : ℝ, (4 * (‖fS dhi u‖ ^ 2 * gw U u) + 4 * (‖fS dlo u‖ ^ 2 * gw U u) +
          (256 * η ^ 2) * (Real.exp (-(-1 * u)) * gw U u) +
          (4 * κ ^ 2) * (Real.exp (-(2 * u)) * gw U u)) := integral_mono hLint IG hG
    _ = 4 * (∫ u, ‖fS dhi u‖ ^ 2 * gw U u) + 4 * (∫ u, ‖fS dlo u‖ ^ 2 * gw U u) +
          (256 * η ^ 2) * (Real.exp (-(-1 * U) + (-1) ^ 2 / 2) * c0) +
          (4 * κ ^ 2) * (Real.exp (-(2 * U) + 2 ^ 2 / 2) * c0) := by
        rw [integral_add I123 I4, integral_add I12 I3, integral_add I1 I2,
          integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
          integral_exp_gw, integral_exp_gw]
    _ ≤ 4 * (Cw * A2) + 4 * (Cw * A2) +
          (256 * η ^ 2) * (Real.exp U * Real.exp (1 / 2) * c0) +
          (4 * κ ^ 2) * (Real.exp (-(2 * U)) * Real.exp 2 * c0) := by
        rw [show -(-1 * U) + (-1) ^ 2 / 2 = U + 1 / 2 by ring,
          show -(2 * U) + 2 ^ 2 / 2 = -(2 * U) + 2 by ring, Real.exp_add, Real.exp_add]
        have b1 : ∫ u, ‖fS dhi u‖ ^ 2 * gw U u ≤ Cw * A2 := by rw [hA2]; linarith
        have b2 : ∫ u, ‖fS dlo u‖ ^ 2 * gw U u ≤ Cw * A2 := by rw [hA2]; linarith
        linarith
    _ ≤ _ := by
        have hk : κ ^ 2 = 64 * K ^ 2 * η ^ (-(5 / 4) : ℝ) := by
          rw [hκ, mul_pow, mul_pow, ← Real.rpow_natCast (η ^ _), ← Real.rpow_mul hη0.le]
          norm_num
        rw [hk]
        set X := A2
        set Y := η ^ 2 * Real.exp U
        set Z := η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U))
        have hX : 0 ≤ X := by
          have : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
          simp only [X, hA2]; positivity
        have hY : 0 ≤ Y := by positivity
        have hZ : 0 ≤ Z := by positivity
        set a := 256 * Real.exp (1 / 2) * c0
        set b := 256 * K ^ 2 * Real.exp 2 * c0
        have ha : 0 ≤ a := by positivity
        have hb : 0 ≤ b := by positivity
        have e1 : 4 * (Cw * X) + 4 * (Cw * X) + 256 * η ^ 2 * (Real.exp U * Real.exp (1 / 2) * c0) +
            4 * (64 * K ^ 2 * η ^ (-(5 / 4) : ℝ)) * (Real.exp (-(2 * U)) * Real.exp 2 * c0)
            = 8 * Cw * X + a * Y + b * Z := by simp only [a, b, Y, Z]; ring
        have e2 : (8 * Cw + a + b) * (X + Y + Z) = 8 * Cw * X + a * Y + b * Z +
            (8 * Cw * (Y + Z) + a * (X + Z) + b * (X + Y)) := by ring
        have : 0 ≤ 8 * Cw * (Y + Z) + a * (X + Z) + b * (X + Y) := by positivity
        rw [e1]
        linarith

end LeanLab.PNTPort.Selberg

