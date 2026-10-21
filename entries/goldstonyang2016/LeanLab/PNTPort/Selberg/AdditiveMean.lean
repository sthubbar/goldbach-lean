module

public import LeanLab.PNTPort.Selberg.Sharp4
public import LeanLab.PNTPort.Selberg.Additive

/-!
# Selberg's mean square for additive windows under RH

Lab proof, unit U-6000, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058 Lemma 1.
AI wrote this file. Known mathematics, Saffari-Vaughan's passage from multiplicative to additive
windows; CONDITIONAL ON RiemannHypothesis only, through `selberg_sharp`.

With `ω_U(x) = e^{-(log x - U)²/2} / x²`, a Gaussian weight in `log x` around `X = e^U`
normalised by `x⁻²`:

* `sharp_x`: `selberg_sharp` in the variable `x = e^u`,
  `∫_{x>0} Wm(x, δ)² ω_U(x) dx ≤ C (δ (log(1/δ) + 3)² + η² e^U + η^{-5/4} e^{-2U})`;
* `pointwise_avg`: for `x > 0`, `0 ≤ h ≤ x (K - 2) η` and `2Kη ≤ 1`,
  `K (ψ(x + h) - ψ(x) - h)² ≤ 8 Σ_{m=1}^{2K} (Wm(x, mη)² + Wm(x + h, mη)²) + 144 K (x + h)² η²`.
  This is Saffari-Vaughan's average over `δ`, done on the grid `δ = kη`, `K ≤ k < 2K`; the
  shifted windows of `additive_eq` are squeezed between grid windows by the monotonicity of `ψ`,
  at a cost `(x + h)η` that matches the `η² e^U` term of `selberg_sharp`. No Fubini is needed;
* `additive_mean`: **the theorem.** Under RH there is `C` such that for `η > 0`, `K ≥ 3`,
  `Δ = 2Kη ≤ 1`, `x₀ > 0` and `0 ≤ h` with `h ≤ x₀`, `h ≤ e^U` and `h ≤ x₀ (K - 2) η`,
  `∫_{x ≥ x₀} (ψ(x + h) - ψ(x) - h)² ω_U(x) dx ≤ C (Δ (log(1/Δ) + 3)² + η² e^U + η^{-5/4} e^{-2U})`.

Reading: near `X = e^U` the weight is about `X⁻²`, so with `Δ` of order `h/x₀` and
`η = √(Δ/X)` this is `∫_{x ≈ X} (ψ(x + h) - ψ(x) - h)² dx ≪ X h log²(X/h)`, Selberg 1943 and
Saffari-Vaughan 1977 in a Gaussian-weighted form, for `h ≥ X^{2/13}` or so.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Set
open LeanLab.PNTPort.Gallagher

/-- The weight `ω_U(x) = gw_U(log x) / x²`. -/
noncomputable def omg (U x : ℝ) : ℝ := gw U (Real.log x) / x ^ 2

lemma omg_nonneg (U x : ℝ) : 0 ≤ omg U x := by
  unfold omg; exact div_nonneg (gw_nonneg _ _) (sq_nonneg _)

lemma measurable_omg (U : ℝ) : Measurable (omg U) := by
  unfold omg
  exact ((gw_continuous U).measurable.comp Real.measurable_log).div (by fun_prop)

lemma measurable_psi : Measurable (fun x : ℝ => Chebyshev.psi x) := Chebyshev.psi_mono.measurable

lemma measurable_Wm (δ : ℝ) : Measurable (fun x => Wm x δ) := by
  unfold Wm
  exact ((measurable_psi.comp (by fun_prop)).sub measurable_psi).sub (by fun_prop)

lemma Nw_log_sq {x : ℝ} (hx : 0 < x) (δ : ℝ) : Nw δ (Real.log x) ^ 2 = Wm x δ ^ 2 / x := by
  have h1 : Nw δ (Real.log x) = Real.exp (-(Real.log x / 2)) * Wm x δ := by
    unfold Nw; rw [← Wm_exp, Real.exp_log hx]
  rw [h1, mul_pow]
  have : Real.exp (-(Real.log x / 2)) ^ 2 = x⁻¹ := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -(Real.log x / 2) = -Real.log x by push_cast; ring,
      Real.exp_neg, Real.exp_log hx]
  rw [this]; field_simp

/-- The integrand identity behind the change of variables `x = e^u`. -/
lemma smul_eq {x : ℝ} (hx : 0 < x) (δ U : ℝ) :
    x⁻¹ • (Nw δ (Real.log x) ^ 2 * gw U (Real.log x)) = Wm x δ ^ 2 * omg U x := by
  rw [smul_eq_mul, Nw_log_sq hx, omg]; field_simp

/-- **`selberg_sharp` in the variable `x`.** -/
theorem sharp_x (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ η : ℝ, 0 < η → η ≤ δ → δ ≤ 1 → ∀ U : ℝ,
    IntegrableOn (fun x => Wm x δ ^ 2 * omg U x) (Ioi 0) ∧
      ∫ x in Ioi 0, Wm x δ ^ 2 * omg U x ≤ C * (δ * (Real.log (1 / δ) + 3) ^ 2 +
        η ^ 2 * Real.exp U + η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U))) := by
  obtain ⟨C, hC, h⟩ := selberg_sharp hRH
  refine ⟨C, hC, fun δ η hη hηδ hδ1 U => ?_⟩
  obtain ⟨hi, hb⟩ := h δ η hη hηδ hδ1 U
  have hcongr : EqOn (fun x : ℝ => x⁻¹ • (Nw δ (Real.log x) ^ 2 * gw U (Real.log x)))
      (fun x => Wm x δ ^ 2 * omg U x) (Ioi 0) := fun x hx => smul_eq hx δ U
  have hI : IntegrableOn (fun x : ℝ => x⁻¹ • (Nw δ (Real.log x) ^ 2 * gw U (Real.log x)))
      (Ioi 0) :=
    (integrableOn_comp_log_Ioi_zero (fun u => Nw δ u ^ 2 * gw U u)).mpr hi
  refine ⟨hI.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_comp_log_Ioi_zero (fun u => Nw δ u ^ 2 * gw U u)]
  exact hb

/-- **The weight moves little under `x ↦ x + h`** when `h ≤ x` and `h ≤ e^U`. -/
lemma omg_shift {U x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hhx : h ≤ x) (hU : h ≤ Real.exp U) :
    omg U x ≤ 4 * Real.exp 1 * omg U (x + h) := by
  have hxh : 0 < x + h := by linarith
  set b := Real.log (x + h) - U with hb
  set t := Real.log (x + h) - Real.log x with ht
  have ht0 : 0 ≤ t := by
    rw [ht, sub_nonneg]; exact Real.log_le_log hx (by linarith)
  have htle : t ≤ h / x := by
    rw [ht, ← Real.log_div hxh.ne' hx.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < (x + h) / x by positivity)
    have e : (x + h) / x - 1 = h / x := by field_simp; ring
    linarith
  -- `b t ≤ 1`
  have hbt : b * t ≤ 1 := by
    rcases le_or_gt b 0 with hb0 | hb0
    · nlinarith
    · have hexp : x + h = Real.exp U * Real.exp b := by
        rw [← Real.exp_add, hb, show U + (Real.log (x + h) - U) = Real.log (x + h) by ring,
          Real.exp_log hxh]
      have h1 : h / x ≤ 2 * h / (x + h) := by
        rw [div_le_div_iff₀ hx hxh]; nlinarith
      have h2 : 2 * h / (x + h) ≤ 2 / Real.exp b := by
        rw [hexp, div_le_div_iff₀ (by positivity) (by positivity)]
        have := Real.exp_pos b
        nlinarith
      have h3 : 2 * b ≤ Real.exp b := by
        have := Real.quadratic_le_exp_of_nonneg hb0.le
        nlinarith [sq_nonneg (b - 1)]
      have h4 : b * t ≤ b * (2 / Real.exp b) :=
        mul_le_mul_of_nonneg_left (htle.trans (h1.trans h2)) hb0.le
      have h5 : b * (2 / Real.exp b) ≤ 1 := by
        rw [mul_div_assoc', div_le_one (Real.exp_pos b)]; linarith
      linarith
  have hg : gw U (Real.log x) ≤ Real.exp 1 * gw U (Real.log (x + h)) := by
    unfold gw
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log x - U = b - t := by rw [hb, ht]; ring
    rw [this, ← hb]
    nlinarith [sq_nonneg t]
  have hsq : 1 / x ^ 2 ≤ 4 / (x + h) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  unfold omg
  calc gw U (Real.log x) / x ^ 2 = gw U (Real.log x) * (1 / x ^ 2) := by ring
    _ ≤ (Real.exp 1 * gw U (Real.log (x + h))) * (4 / (x + h) ^ 2) :=
        mul_le_mul hg hsq (by positivity) (mul_nonneg (Real.exp_pos 1).le (gw_nonneg _ _))
    _ = _ := by ring

/-- **Squeeze by monotonicity of `ψ`**: a window `(y, ye^d]` with `a ≤ d ≤ b`. -/
lemma Wm_sandwich {y a b d : ℝ} (hy : 0 ≤ y) (had : a ≤ d) (hdb : d ≤ b) :
    Wm y d ^ 2 ≤ 2 * (Wm y a ^ 2 + Wm y b ^ 2) + 2 * (y * (Real.exp b - Real.exp a)) ^ 2 := by
  have ea : Real.exp a ≤ Real.exp d := Real.exp_le_exp.mpr had
  have eb : Real.exp d ≤ Real.exp b := Real.exp_le_exp.mpr hdb
  have pa : Chebyshev.psi (y * Real.exp a) ≤ Chebyshev.psi (y * Real.exp d) :=
    Chebyshev.psi_mono (mul_le_mul_of_nonneg_left ea hy)
  have pb : Chebyshev.psi (y * Real.exp d) ≤ Chebyshev.psi (y * Real.exp b) :=
    Chebyshev.psi_mono (mul_le_mul_of_nonneg_left eb hy)
  set D := y * (Real.exp b - Real.exp a)
  have hup : Wm y d ≤ Wm y b + D := by
    unfold Wm; nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.mpr ea) hy]
  have hlo : Wm y a - D ≤ Wm y d := by
    unfold Wm; nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.mpr eb) hy]
  have hD : 0 ≤ D := mul_nonneg hy (by linarith)
  rcases le_or_gt 0 (Wm y d) with h0 | h0
  · nlinarith [sq_nonneg (Wm y b - D), sq_nonneg (Wm y a)]
  · nlinarith [sq_nonneg (Wm y a + D), sq_nonneg (Wm y b)]

/-- `δ (log(1/δ) + 3)²` is increasing on `(0, 1]`. -/
lemma bmain_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    a * (Real.log (1 / a) + 3) ^ 2 ≤ b * (Real.log (1 / b) + 3) ^ 2 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set M := Real.log (1 / b) + 3
  set t := Real.log (b / a)
  have hM : 3 ≤ M := by
    have : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
    linarith
  have ht0 : 0 ≤ t := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hla : Real.log (1 / a) = Real.log (1 / b) + t := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hexp : Real.exp t = b / a := Real.exp_log (by positivity)
  have hhalf : 1 + t / 2 ≤ Real.exp (t / 2) := by linarith [Real.add_one_le_exp (t / 2)]
  have hsq : (1 + t / 2) ^ 2 ≤ Real.exp t := by
    have : Real.exp t = Real.exp (t / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [this]; exact pow_le_pow_left₀ (by linarith) hhalf 2
  have key : (M + t) ^ 2 ≤ Real.exp t * M ^ 2 := by
    have h1 : M + t ≤ (1 + t / 2) * M := by nlinarith
    calc (M + t) ^ 2 ≤ ((1 + t / 2) * M) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      _ = (1 + t / 2) ^ 2 * M ^ 2 := by ring
      _ ≤ Real.exp t * M ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  rw [hexp] at key
  rw [hla, show Real.log (1 / b) + t + 3 = M + t by ring]
  calc a * (M + t) ^ 2 ≤ a * (b / a * M ^ 2) := mul_le_mul_of_nonneg_left key ha.le
    _ = b * M ^ 2 := by field_simp

lemma sum_shift_le (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) {K c : ℕ} (hc : c + 1 ≤ K) :
    ∑ k ∈ Finset.Ico K (2 * K), f (k - c) ≤ ∑ m ∈ Finset.Icc 1 (2 * K), f m := by
  have hinj : Set.InjOn (fun k : ℕ => k - c) (Finset.Ico K (2 * K) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    simp only at hab
    omega
  rw [← Finset.sum_image (f := f) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => hf m)
  intro m hm
  simp only [Finset.mem_image, Finset.mem_Ico] at hm
  obtain ⟨k, hk, rfl⟩ := hm
  simp only [Finset.mem_Icc]
  omega

/-- **Saffari-Vaughan's average over `δ`, on the grid `δ = kη`.** -/
lemma pointwise_avg {x h η : ℝ} {K : ℕ} (hx : 0 < x) (hh : 0 ≤ h) (hη : 0 < η) (hK3 : 3 ≤ K)
    (hK : 2 * K * η ≤ 1) (hs : h ≤ x * ((K : ℝ) - 2) * η) :
    K * (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 ≤
      8 * ∑ m ∈ Finset.Icc 1 (2 * K), (Wm x (m * η) ^ 2 + Wm (x + h) (m * η) ^ 2) +
        144 * K * ((x + h) ^ 2 * η ^ 2) := by
  set A := Chebyshev.psi (x + h) - Chebyshev.psi x - h with hA
  set s := Real.log (1 + h / x) with hsdef
  obtain ⟨hs0, hsle⟩ := log_shift_le hx hh
  have hK3r : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  have hsK : s ≤ ((K : ℝ) - 2) * η := by
    calc s ≤ h / x := hsle
      _ ≤ _ := by rw [div_le_iff₀ hx]; linarith
  set j := ⌊s / η⌋₊ with hjdef
  have hsη : 0 ≤ s / η := div_nonneg hs0 hη.le
  have hj1 : (j : ℝ) * η ≤ s := by
    have := Nat.floor_le hsη; rwa [le_div_iff₀ hη] at this
  have hj2 : s < ((j : ℝ) + 1) * η := by
    have := Nat.lt_floor_add_one (s / η); rwa [div_lt_iff₀ hη] at this
  have hjK : j + 2 ≤ K := by
    have h2 : s / η ≤ (K : ℝ) - 2 := by rw [div_le_iff₀ hη]; exact hsK
    have : (j : ℝ) + 2 ≤ K := by linarith [Nat.floor_le hsη]
    exact_mod_cast this
  have hη1 : η ≤ 1 := by nlinarith
  -- the bound for one grid point
  have hk : ∀ k ∈ Finset.Ico K (2 * K),
      A ^ 2 ≤ 2 * Wm x (k * η) ^ 2 + 4 * (Wm (x + h) ((k - (j + 1) : ℕ) * η) ^ 2 +
        Wm (x + h) ((k - j : ℕ) * η) ^ 2) + 144 * ((x + h) ^ 2 * η ^ 2) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkj : j + 1 ≤ k := by omega
    have hk2 : (k : ℝ) + 1 ≤ 2 * K := by exact_mod_cast (by omega : k + 1 ≤ 2 * K)
    have e1 : (((k - (j + 1) : ℕ)) : ℝ) = k - j - 1 := by
      rw [Nat.cast_sub hkj]; push_cast; ring
    have e2 : (((k - j : ℕ)) : ℝ) = k - j := by rw [Nat.cast_sub (by omega)]
    have h1 := additive_sq_le hx hh ((k : ℝ) * η)
    rw [← hsdef] at h1
    have h2 := Wm_sandwich (y := x + h) (a := ((k - (j + 1) : ℕ) : ℝ) * η)
      (b := ((k - j : ℕ) : ℝ) * η) (d := (k : ℝ) * η - s) (by linarith)
      (by rw [e1]; nlinarith) (by rw [e2]; nlinarith)
    set a := (((k - (j + 1) : ℕ)) : ℝ) * η with ha
    have hb : (((k - j : ℕ)) : ℝ) * η = a + η := by rw [ha, e1, e2]; ring
    rw [hb] at h2
    have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have ha1 : a ≤ 1 := by rw [ha, e1]; nlinarith
    have hE : Real.exp (a + η) - Real.exp a ≤ 6 * η := by
      rw [Real.exp_add]
      have h3 := exp_le_three ha1
      have h4 := exp_sub_one_le hη.le hη1
      have h5 : 0 ≤ Real.exp η - 1 := by linarith [Real.add_one_le_exp η]
      have : Real.exp a * (Real.exp η - 1) ≤ 3 * (2 * η) :=
        mul_le_mul h3 h4 h5 (by norm_num)
      nlinarith
    have hE0 : 0 ≤ Real.exp (a + η) - Real.exp a :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
    have hD : ((x + h) * (Real.exp (a + η) - Real.exp a)) ^ 2 ≤ 36 * ((x + h) ^ 2 * η ^ 2) := by
      have hxh : 0 ≤ x + h := by linarith
      have := mul_le_mul_of_nonneg_left hE hxh
      have h6 := pow_le_pow_left₀ (mul_nonneg hxh hE0) this 2
      nlinarith
    rw [hb]
    rw [← hA] at h1
    linarith
  -- sum over the grid
  have hsum : ∑ k ∈ Finset.Ico K (2 * K), A ^ 2 ≤ ∑ k ∈ Finset.Ico K (2 * K),
      (2 * Wm x (k * η) ^ 2 + 4 * (Wm (x + h) ((k - (j + 1) : ℕ) * η) ^ 2 +
        Wm (x + h) ((k - j : ℕ) * η) ^ 2) + 144 * ((x + h) ^ 2 * η ^ 2)) :=
    Finset.sum_le_sum hk
  have hcard : ∑ k ∈ Finset.Ico K (2 * K), A ^ 2 = K * A ^ 2 := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [show 2 * K - K = K by omega]
  have hcard2 : ∑ k ∈ Finset.Ico K (2 * K), 144 * ((x + h) ^ 2 * η ^ 2) =
      144 * K * ((x + h) ^ 2 * η ^ 2) := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((2 * K - K : ℕ) : ℝ) = K := by rw [show 2 * K - K = K by omega]
    rw [this]; ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcard2, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, hcard] at hsum
  -- the three sums
  have hx1 : ∑ k ∈ Finset.Ico K (2 * K), Wm x (k * η) ^ 2 ≤
      ∑ m ∈ Finset.Icc 1 (2 * K), Wm x (m * η) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => sq_nonneg _)
    intro m hm; simp only [Finset.mem_Ico, Finset.mem_Icc] at hm ⊢; omega
  have hx2 := sum_shift_le (fun m => Wm (x + h) (m * η) ^ 2) (fun m => sq_nonneg _)
    (K := K) (c := j + 1) (by omega)
  have hx3 := sum_shift_le (fun m => Wm (x + h) (m * η) ^ 2) (fun m => sq_nonneg _)
    (K := K) (c := j) (by omega)
  have hS0 : 0 ≤ ∑ m ∈ Finset.Icc 1 (2 * K), Wm x (m * η) ^ 2 :=
    Finset.sum_nonneg (fun m _ => sq_nonneg _)
  rw [Finset.sum_add_distrib]
  linarith

/-- The weight against `dx`: `∫_{x>0} gw_U(log x) dx = e^{U + 1/2} ∫ gw_0`. -/
lemma gw_log (U : ℝ) : IntegrableOn (fun x => gw U (Real.log x)) (Ioi 0) ∧
    ∫ x in Ioi 0, gw U (Real.log x) = Real.exp (U + 1 / 2) * ∫ u, gw 0 u := by
  have hcongr : EqOn (fun x : ℝ => x⁻¹ • (Real.exp (-(-1 * Real.log x)) * gw U (Real.log x)))
      (fun x => gw U (Real.log x)) (Ioi 0) := by
    intro x hx
    simp only [smul_eq_mul, neg_mul, one_mul, neg_neg]
    rw [Real.exp_log hx, inv_mul_cancel_left₀ (ne_of_gt hx)]
  have hI := (integrableOn_comp_log_Ioi_zero
    (fun u => Real.exp (-(-1 * u)) * gw U u)).mpr (integrable_exp_gw (-1) U)
  refine ⟨hI.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_comp_log_Ioi_zero (fun u => Real.exp (-(-1 * u)) * gw U u), integral_exp_gw]
  congr 2; ring

/-- **Selberg's mean square for additive windows, under RH.** -/
theorem additive_mean (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (η : ℝ) (K : ℕ), 0 < η → 3 ≤ K → 2 * K * η ≤ 1 →
    ∀ U x₀ h : ℝ, 0 < x₀ → 0 ≤ h → h ≤ x₀ → h ≤ Real.exp U → h ≤ x₀ * ((K : ℝ) - 2) * η →
    IntegrableOn (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x)
        (Ici x₀) ∧
      ∫ x in Ici x₀, (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x ≤
        C * (2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 + η ^ 2 * Real.exp U +
          η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U))) := by
  obtain ⟨C1, hC1, hsx⟩ := sharp_x hRH
  set c0 := ∫ u, gw 0 u with hc0def
  have hc0 : 0 ≤ c0 := integral_nonneg (gw_nonneg 0)
  refine ⟨16 * (1 + 4 * Real.exp 1) * C1 + 576 * Real.exp (1 / 2) * c0, by positivity,
    fun η K hη hK3 hK U x₀ h hx₀ hh hhx₀ hhU hs => ?_⟩
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  set Δ := 2 * K * η with hΔ
  set B := Δ * (Real.log (1 / Δ) + 3) ^ 2 + η ^ 2 * Real.exp U +
    η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U)) with hB
  have hΔ0 : 0 < Δ := by positivity
  have hB1 : 0 ≤ Δ * (Real.log (1 / Δ) + 3) ^ 2 := by positivity
  have hB3 : 0 ≤ η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U)) := by positivity
  have hBη : η ^ 2 * Real.exp U ≤ B := by rw [hB]; linarith
  have hsub : Ici x₀ ⊆ Ioi 0 := Ici_subset_Ioi.mpr hx₀
  -- the windows of the grid
  have hgrid : ∀ m ∈ Finset.Icc 1 (2 * K),
      IntegrableOn (fun x => Wm x (m * η) ^ 2 * omg U x) (Ioi 0) ∧
        ∫ x in Ioi 0, Wm x (m * η) ^ 2 * omg U x ≤ C1 * B := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hm2 : (m : ℝ) ≤ 2 * K := by exact_mod_cast hm.2
    have hδ1 : η ≤ m * η := by nlinarith
    have hδ2 : m * η ≤ Δ := by rw [hΔ]; nlinarith
    obtain ⟨hi, hb⟩ := hsx (m * η) η hη hδ1 (hδ2.trans hK) U
    refine ⟨hi, hb.trans (mul_le_mul_of_nonneg_left ?_ hC1)⟩
    have := bmain_mono (by positivity) hδ2 hK
    rw [hB]; linarith
  -- the three kinds of terms on `Ici x₀`
  have hF : ∀ m ∈ Finset.Icc 1 (2 * K),
      IntegrableOn (fun x => Wm x (m * η) ^ 2 * omg U x) (Ici x₀) ∧
        ∫ x in Ici x₀, Wm x (m * η) ^ 2 * omg U x ≤ C1 * B := by
    intro m hm
    obtain ⟨hi, hb⟩ := hgrid m hm
    refine ⟨hi.mono_set hsub, le_trans ?_ hb⟩
    exact setIntegral_mono_set hi (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (omg_nonneg _ _))
      (Filter.Eventually.of_forall hsub)
  have hG : ∀ m ∈ Finset.Icc 1 (2 * K),
      IntegrableOn (fun x => Wm (x + h) (m * η) ^ 2 * omg U x) (Ici x₀) ∧
        ∫ x in Ici x₀, Wm (x + h) (m * η) ^ 2 * omg U x ≤ 4 * Real.exp 1 * (C1 * B) := by
    intro m hm
    obtain ⟨hi, hb⟩ := hgrid m hm
    set f := (Ioi (0 : ℝ)).indicator (fun y => Wm y (m * η) ^ 2 * omg U y) with hf
    have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioi).mpr hi
    have hf0 : ∀ y, 0 ≤ f y := fun y => by
      rw [hf]; exact indicator_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (omg_nonneg _ _)) y
    have hsh : Integrable (fun x => 4 * Real.exp 1 * f (x + h)) :=
      (hfi.comp_add_right h).const_mul _
    have hpt : ∀ x ∈ Ici x₀, Wm (x + h) (m * η) ^ 2 * omg U x ≤ 4 * Real.exp 1 * f (x + h) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
      have hxh : x + h ∈ Ioi (0 : ℝ) := by show 0 < x + h; linarith
      rw [hf, indicator_of_mem hxh]
      have := omg_shift (U := U) hx0 hh (hhx₀.trans hx) hhU
      calc Wm (x + h) (m * η) ^ 2 * omg U x ≤
            Wm (x + h) (m * η) ^ 2 * (4 * Real.exp 1 * omg U (x + h)) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = _ := by ring
    have hmeas : Measurable (fun x => Wm (x + h) (m * η) ^ 2 * omg U x) :=
      (((measurable_Wm _).comp (measurable_add_const h)).pow_const 2).mul (measurable_omg U)
    have hGi : IntegrableOn (fun x => Wm (x + h) (m * η) ^ 2 * omg U x) (Ici x₀) := by
      refine hsh.integrableOn.mono' hmeas.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (omg_nonneg _ _))]
      exact hpt x hx
    refine ⟨hGi, ?_⟩
    calc ∫ x in Ici x₀, Wm (x + h) (m * η) ^ 2 * omg U x
        ≤ ∫ x in Ici x₀, 4 * Real.exp 1 * f (x + h) :=
          setIntegral_mono_on hGi hsh.integrableOn measurableSet_Ici hpt
      _ ≤ ∫ x, 4 * Real.exp 1 * f (x + h) :=
          setIntegral_le_integral hsh (ae_of_all _ fun x => by have := hf0 (x + h); positivity)
      _ = 4 * Real.exp 1 * ∫ x in Ioi 0, Wm x (m * η) ^ 2 * omg U x := by
          rw [integral_const_mul, integral_add_right_eq_self (fun x => f x) h, hf,
            integral_indicator measurableSet_Ioi]
      _ ≤ 4 * Real.exp 1 * (C1 * B) := mul_le_mul_of_nonneg_left hb (by positivity)
  obtain ⟨hgi, hgv⟩ := gw_log U
  have hE : IntegrableOn (fun x => (x + h) ^ 2 * η ^ 2 * omg U x) (Ici x₀) ∧
      ∫ x in Ici x₀, (x + h) ^ 2 * η ^ 2 * omg U x ≤
        4 * η ^ 2 * (Real.exp (U + 1 / 2) * c0) := by
    have hpt : ∀ x ∈ Ici x₀, (x + h) ^ 2 * η ^ 2 * omg U x ≤ 4 * η ^ 2 * gw U (Real.log x) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
      have hhx : h ≤ x := hhx₀.trans hx
      unfold omg
      rw [div_eq_mul_inv]
      have hg := gw_nonneg U (Real.log x)
      have h1 : (x + h) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
      have h2 : x ^ 2 * (x ^ 2)⁻¹ = 1 := by field_simp
      calc (x + h) ^ 2 * η ^ 2 * (gw U (Real.log x) * (x ^ 2)⁻¹)
          ≤ 4 * x ^ 2 * η ^ 2 * (gw U (Real.log x) * (x ^ 2)⁻¹) := by gcongr
        _ = 4 * η ^ 2 * gw U (Real.log x) * (x ^ 2 * (x ^ 2)⁻¹) := by ring
        _ = _ := by rw [h2, mul_one]
    have hmeas : Measurable (fun x => (x + h) ^ 2 * η ^ 2 * omg U x) :=
      (by fun_prop : Measurable (fun x : ℝ => (x + h) ^ 2 * η ^ 2)).mul (measurable_omg U)
    have hgi4 : IntegrableOn (fun x => 4 * η ^ 2 * gw U (Real.log x)) (Ioi 0) := hgi.const_mul _
    have hdom : IntegrableOn (fun x => 4 * η ^ 2 * gw U (Real.log x)) (Ici x₀) :=
      hgi4.mono_set hsub
    have hEi : IntegrableOn (fun x => (x + h) ^ 2 * η ^ 2 * omg U x) (Ici x₀) := by
      refine hdom.mono' hmeas.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := omg_nonneg U x; positivity)]
      exact hpt x hx
    refine ⟨hEi, ?_⟩
    calc ∫ x in Ici x₀, (x + h) ^ 2 * η ^ 2 * omg U x
        ≤ ∫ x in Ici x₀, 4 * η ^ 2 * gw U (Real.log x) :=
          setIntegral_mono_on hEi hdom measurableSet_Ici hpt
      _ ≤ ∫ x in Ioi 0, 4 * η ^ 2 * gw U (Real.log x) :=
          setIntegral_mono_set hgi4
            (ae_of_all _ fun x => by have := gw_nonneg U (Real.log x); positivity)
            (Filter.Eventually.of_forall hsub)
      _ = _ := by rw [integral_const_mul, hgv]
  -- the right side
  have hSi : IntegrableOn (fun x => ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x)) (Ici x₀) :=
    integrable_finsetSum _ fun m hm => ((hF m hm).1.add (hG m hm).1)
  have hS8 : IntegrableOn (fun x => 8 * ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x)) (Ici x₀) :=
    hSi.const_mul 8
  have hEK : IntegrableOn (fun x => 144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) (Ici x₀) :=
    hE.1.const_mul _
  have hRi : IntegrableOn (fun x => 8 * ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
      144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) (Ici x₀) := hS8.add hEK
  have hsumeq : ∫ x in Ici x₀, ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) =
      ∑ m ∈ Finset.Icc 1 (2 * K), ∫ x in Ici x₀,
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) :=
    integral_finsetSum _ fun m hm => ((hF m hm).1.add (hG m hm).1)
  have hRv : ∫ x in Ici x₀, (8 * ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
      144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) ≤
      8 * (2 * K * ((1 + 4 * Real.exp 1) * (C1 * B))) +
      144 * K * (4 * η ^ 2 * (Real.exp (U + 1 / 2) * c0)) := by
    rw [integral_add hS8 hEK, integral_const_mul, integral_const_mul, hsumeq]
    have h1 : ∑ m ∈ Finset.Icc 1 (2 * K), ∫ x in Ici x₀,
        (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) ≤
        ∑ m ∈ Finset.Icc 1 (2 * K), (1 + 4 * Real.exp 1) * (C1 * B) := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [integral_add (hF m hm).1 (hG m hm).1]
      linarith [(hF m hm).2, (hG m hm).2]
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
    have hc : ((2 * K + 1 - 1 : ℕ) : ℝ) = 2 * K := by
      rw [show 2 * K + 1 - 1 = 2 * K by omega]; push_cast; ring
    rw [hc] at h1
    have h2 := hE.2
    have hK0' : (0 : ℝ) ≤ 144 * K := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hK0']
  -- the pointwise bound times the weight
  have hpt : ∀ x ∈ Ici x₀,
      K * ((Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x) ≤
        8 * ∑ m ∈ Finset.Icc 1 (2 * K),
          (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
        144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have hK2 : (0 : ℝ) ≤ ((K : ℝ) - 2) * η := by
      have : (3 : ℝ) ≤ K := by exact_mod_cast hK3
      nlinarith
    have hsx' : h ≤ x * ((K : ℝ) - 2) * η := by
      rw [mul_assoc] at hs ⊢; exact hs.trans (mul_le_mul_of_nonneg_right hx hK2)
    have := pointwise_avg hx0 hh hη hK3 hK hsx'
    have hω := omg_nonneg U x
    have h2 := mul_le_mul_of_nonneg_right this hω
    have expand : (8 * ∑ m ∈ Finset.Icc 1 (2 * K), (Wm x (m * η) ^ 2 + Wm (x + h) (m * η) ^ 2) +
        144 * K * ((x + h) ^ 2 * η ^ 2)) * omg U x =
        8 * ∑ m ∈ Finset.Icc 1 (2 * K),
          (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
        144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x) := by
      rw [add_mul, mul_assoc (8 : ℝ), Finset.sum_mul]
      congr 1
      · congr 1; exact Finset.sum_congr rfl (fun m _ => by ring)
      · ring
    rw [expand] at h2
    calc K * ((Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x)
        = K * (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x := by ring
      _ ≤ _ := h2
  have hmeasA : Measurable (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x) :=
    ((((measurable_psi.comp (measurable_add_const h)).sub measurable_psi).sub
      measurable_const).pow_const 2).mul (measurable_omg U)
  have hAi : IntegrableOn (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x)
      (Ici x₀) := by
    refine (hRi.const_mul (1 / (K : ℝ))).mono' hmeasA.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (omg_nonneg _ _))]
    have := hpt x hx
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hK0]
    linarith
  refine ⟨hAi, ?_⟩
  have hint : K * ∫ x in Ici x₀, (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x ≤
      ∫ x in Ici x₀, (8 * ∑ m ∈ Finset.Icc 1 (2 * K),
        (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
        144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hAi.const_mul _) hRi measurableSet_Ici hpt
  have hfin : K * ∫ x in Ici x₀, (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x ≤
      K * ((16 * (1 + 4 * Real.exp 1) * C1 + 576 * Real.exp (1 / 2) * c0) * B) := by
    refine hint.trans (hRv.trans ?_)
    have he : Real.exp (U + 1 / 2) = Real.exp (1 / 2) * Real.exp U := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have h1 : 0 ≤ Real.exp (1 / 2) * c0 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hBη h1
    have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 576 * K by positivity)
    calc 8 * (2 * K * ((1 + 4 * Real.exp 1) * (C1 * B))) +
          144 * K * (4 * η ^ 2 * (Real.exp (1 / 2) * Real.exp U * c0))
        = K * (16 * (1 + 4 * Real.exp 1) * C1 * B) +
          576 * K * (Real.exp (1 / 2) * c0 * (η ^ 2 * Real.exp U)) := by ring
      _ ≤ K * (16 * (1 + 4 * Real.exp 1) * C1 * B) +
          576 * K * (Real.exp (1 / 2) * c0 * B) := by linarith
      _ = _ := by ring
  exact le_of_mul_le_mul_left hfin hK0

end LeanLab.PNTPort.Selberg

