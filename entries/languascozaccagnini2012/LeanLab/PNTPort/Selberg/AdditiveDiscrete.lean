module

public import LeanLab.PNTPort.Selberg.AdditiveMean

/-!
# Selberg's mean square for additive windows under RH, the discrete form

Lab proof, unit U-6001, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058 Lemma 1.
AI wrote this file. Known mathematics, Selberg 1943 and Saffari-Vaughan 1977; CONDITIONAL ON
RiemannHypothesis only, through `additive_mean`.

`ψ` is constant on `[m, m + 1)`, so for an integer step `L` the integrand of `additive_mean` is
`(ψ(m + L) - ψ(m) - L)² ω_U(x)` there, and `ω_U ≥ e^{-1/2} e^{-2(U+1)}` on `[e^{U-1}, e^{U+1}]`.

* `discrete_mean`: under RH, with the parameters of `additive_mean` and `x₀ = e^{U-1}`,
  `Σ_{a ≤ m < b} (ψ(m + L) - ψ(m) - L)² ≤ C e^{2U} (Δ (log(1/Δ) + 3)² + η² e^U + η^{-5/4} e^{-2U})`
  for naturals `e^{U-1} ≤ a`, `b ≤ e^{U+1}`;
* `selberg_discrete`: **the clean form.** Under RH there is `C` such that for `X = e^U`, every
  natural `1 ≤ L ≤ X/14` and naturals `X/e ≤ a`, `b ≤ eX`,
  `Σ_{a ≤ m < b} (ψ(m + L) - ψ(m) - L)² ≤ C (X L (log(X/L) + 3)² + X^{5/4} L^{-5/8})`.
  The second term is at most `X L` once `L ≥ X^{2/13}`. This is the input that
  `Gallagher.gallagher_psi` takes, block by block.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Set
open LeanLab.PNTPort.Gallagher

/-- The additive window error at an integer point is constant on `[m, m + 1)`. -/
lemma window_const {m L : ℕ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    Chebyshev.psi (x + L) - Chebyshev.psi x - L =
      Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L := by
  obtain ⟨h1, h2⟩ := hx
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg m) h1
  have f1 : ⌊x⌋₊ = m := (Nat.floor_eq_iff hx0).mpr ⟨h1, h2⟩
  have f2 : ⌊x + L⌋₊ = m + L := by
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
  rw [Chebyshev.psi_eq_psi_coe_floor x, Chebyshev.psi_eq_psi_coe_floor (x + L), f1, f2]
  push_cast; ring

/-- The weight is bounded below on `[e^{U-1}, e^{U+1}]`. -/
lemma omg_lower {U x : ℝ} (h1 : Real.exp (U - 1) ≤ x) (h2 : x ≤ Real.exp (U + 1)) :
    Real.exp (-(1 / 2)) * Real.exp (-(2 * (U + 1))) ≤ omg U x := by
  have hx : 0 < x := lt_of_lt_of_le (Real.exp_pos _) h1
  have l1 : U - 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx]; exact h1
  have l2 : Real.log x ≤ U + 1 := by rw [Real.log_le_iff_le_exp hx]; exact h2
  have hg : Real.exp (-(1 / 2)) ≤ gw U (Real.log x) := by
    unfold gw; apply Real.exp_le_exp.mpr
    have : (Real.log x - U) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hsq : Real.exp (-(2 * (U + 1))) ≤ 1 / x ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : x ^ 2 ≤ Real.exp (U + 1) ^ 2 := pow_le_pow_left₀ hx.le h2 2
    have e : Real.exp (-(2 * (U + 1))) * Real.exp (U + 1) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
    nlinarith [Real.exp_pos (-(2 * (U + 1)))]
  unfold omg
  rw [div_eq_mul_one_div (gw U (Real.log x))]
  exact mul_le_mul hg hsq (by positivity) (gw_nonneg _ _)

/-- Interval integrals over adjacent unit intervals add up. -/
lemma sum_unit_intervals (f : ℝ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hf : ∀ m, a ≤ m → m < b → IntervalIntegrable f volume (m : ℝ) (m + 1)) :
    ∑ m ∈ Finset.Ico a b, ∫ x in (m : ℝ)..(m + 1), f x = ∫ x in (a : ℝ)..b, f x := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih (fun m h1 h2 => hf m h1 (by omega))]
    have h1 : IntervalIntegrable f volume (a : ℝ) n := by
      have := fun m (h1 : a ≤ m) (h2 : m < n) => hf m h1 (by omega)
      clear ih
      induction n, hn using Nat.le_induction with
      | base => exact IntervalIntegrable.refl
      | succ k hk ih2 =>
        have e := (ih2 (fun m h1 h2 => hf m h1 (by omega)) (fun m h1 h2 => this m h1 (by omega))).trans
          (this k hk (by omega))
        push_cast; exact e
    push_cast
    exact intervalIntegral.integral_add_adjacent_intervals h1 (hf n hn (by omega))

/-- **The discrete mean square, with free parameters.** -/
theorem discrete_mean (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (η : ℝ) (K : ℕ), 0 < η → 3 ≤ K → 2 * K * η ≤ 1 →
    ∀ (U : ℝ) (L a b : ℕ), Real.exp (U - 1) ≤ a → (b : ℝ) ≤ Real.exp (U + 1) →
    (L : ℝ) ≤ Real.exp (U - 1) → (L : ℝ) ≤ Real.exp (U - 1) * ((K : ℝ) - 2) * η →
    ∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 ≤
      C * Real.exp (2 * U) * (2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 +
        η ^ 2 * Real.exp U + η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U))) := by
  obtain ⟨C1, hC1, hadd⟩ := additive_mean hRH
  refine ⟨C1 * Real.exp (5 / 2), by positivity,
    fun η K hη hK3 hK U L a b ha hb hL1 hL2 => ?_⟩
  set B := 2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 +
    η ^ 2 * Real.exp U + η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ (Real.log (1 / (2 * K * η)) + 3) ^ 2 := sq_nonneg _
    rw [hB]; positivity
  set x₀ := Real.exp (U - 1) with hx₀
  have hx₀0 : 0 < x₀ := Real.exp_pos _
  have hLU : (L : ℝ) ≤ Real.exp U := hL1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨hI, hV⟩ := hadd η K hη hK3 hK U x₀ L hx₀0 (Nat.cast_nonneg L) hL1 hLU hL2
  set f := fun x : ℝ => (Chebyshev.psi (x + L) - Chebyshev.psi x - L) ^ 2 * omg U x with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (sq_nonneg _) (omg_nonneg _ _)
  set c := Real.exp (-(1 / 2)) * Real.exp (-(2 * (U + 1))) with hc
  have hc0 : 0 < c := by positivity
  have hkey : Real.exp (5 / 2) * Real.exp (2 * U) * c = 1 := by
    rw [hc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf; exact Real.exp_zero
  have hRHS : C1 * Real.exp (5 / 2) * Real.exp (2 * U) * B = C1 * B / c := by
    rw [eq_div_iff hc0.ne']
    calc C1 * Real.exp (5 / 2) * Real.exp (2 * U) * B * c
        = C1 * B * (Real.exp (5 / 2) * Real.exp (2 * U) * c) := by ring
      _ = C1 * B := by rw [hkey, mul_one]
  rw [hRHS, le_div_iff₀ hc0]
  rcases lt_or_ge b a with hba | hab
  · rw [Finset.Ico_eq_empty_of_le hba.le, Finset.sum_empty, zero_mul]; positivity
  have hsub : ∀ m, a ≤ m → Icc (m : ℝ) (m + 1) ⊆ Ici x₀ := by
    intro m hm y hy
    exact le_trans (ha.trans (by exact_mod_cast hm)) hy.1
  have hii : ∀ m, a ≤ m → m < b → IntervalIntegrable f volume (m : ℝ) (m + 1) := by
    intro m hm _
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact hI.mono_set (hsub m hm)
  -- each unit interval
  have hpiece : ∀ m ∈ Finset.Ico a b,
      (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c ≤
        ∫ x in (m : ℝ)..(m + 1), f x := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm1 : (m : ℝ) + 1 ≤ b := by exact_mod_cast hm.2
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    have hlow : ∀ x ∈ Ioo (m : ℝ) (m + 1),
        (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c ≤ f x := by
      intro x hx
      rw [hf]; simp only
      rw [window_const (m := m) (L := L) ⟨hx.1.le, hx.2⟩]
      refine mul_le_mul_of_nonneg_left (omg_lower ?_ ?_) (sq_nonneg _)
      · exact le_trans (ha.trans (by exact_mod_cast hm.1)) hx.1.le
      · exact le_trans (by linarith [hx.2]) hb
    have hIoo : IntegrableOn f (Ioo (m : ℝ) (m + 1)) :=
      hI.mono_set (Ioo_subset_Icc_self.trans (hsub m hm.1))
    calc (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c
        = ∫ x in Ioo (m : ℝ) (m + 1), (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioo,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring
      _ ≤ ∫ x in Ioo (m : ℝ) (m + 1), f x :=
          setIntegral_mono_on (integrableOn_const (by simp)) hIoo measurableSet_Ioo hlow
  calc (∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2) * c
      = ∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ m ∈ Finset.Ico a b, ∫ x in (m : ℝ)..(m + 1), f x := Finset.sum_le_sum hpiece
    _ = ∫ x in (a : ℝ)..b, f x := sum_unit_intervals f hab hii
    _ = ∫ x in Ioc (a : ℝ) b, f x := intervalIntegral.integral_of_le (by exact_mod_cast hab)
    _ ≤ ∫ x in Ici x₀, f x := by
        refine setIntegral_mono_set hI (ae_of_all _ hf0) (Filter.Eventually.of_forall ?_)
        intro y hy; exact ha.trans hy.1.le
    _ ≤ C1 * B := hV

set_option maxHeartbeats 1000000 in
/-- **Selberg's discrete mean square for additive windows, under RH.** With `X = e^U`, for
`1 ≤ L ≤ X/14` and `X/e ≤ a`, `b ≤ eX`:
`Σ_{a ≤ m < b} (ψ(m + L) - ψ(m) - L)² ≤ C (X L (log(X/L) + 3)² + X^{5/4} L^{-5/8})`. -/
theorem selberg_discrete (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (U : ℝ) (L a b : ℕ), 1 ≤ L → 14 * (L : ℝ) ≤ Real.exp U →
    Real.exp (U - 1) ≤ a → (b : ℝ) ≤ Real.exp (U + 1) →
    ∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 ≤
      C * (Real.exp U * L * (Real.log (Real.exp U / L) + 3) ^ 2 +
        Real.exp U ^ (5 / 4 : ℝ) * (L : ℝ) ^ (-(5 / 8) : ℝ)) := by
  obtain ⟨C0, hC0, hdm⟩ := discrete_mean hRH
  refine ⟨15 * C0, by positivity, fun U L a b hL hLX ha hb => ?_⟩
  set X := Real.exp U with hX
  have hX0 : 0 < X := Real.exp_pos U
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  set r := Real.sqrt L with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hL0
  have hrr : r * r = L := Real.mul_self_sqrt hL0.le
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hL1
  have hrL : r ≤ L := by nlinarith
  set η := r / X with hη
  have hη0 : 0 < η := div_pos hr0 hX0
  set K := ⌈Real.exp 1 * r⌉₊ + 3 with hK
  have he := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  have hKlo : Real.exp 1 * r + 1 ≤ (K : ℝ) - 2 := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (Real.exp 1 * r)]
  have hKhi : (K : ℝ) ≤ Real.exp 1 * r + 4 := by
    rw [hK]; push_cast; linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ Real.exp 1 * r)]
  have hK3 : 3 ≤ K := by rw [hK]; omega
  -- `Δ = 2Kη ≤ 14 L/X ≤ 1`
  have hΔ : 2 * K * η ≤ 14 * L / X := by
    rw [hη, le_div_iff₀ hX0]
    have : 2 * K * (r / X) * X = 2 * K * r := by field_simp
    rw [this]
    nlinarith
  have hΔ1 : 14 * L / X ≤ 1 := by rw [div_le_one hX0]; exact hLX
  have hΔ0 : 0 < 2 * K * η := by have : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
                                 positivity
  -- the hypotheses of `discrete_mean`
  have hU1 : Real.exp (U - 1) = X / Real.exp 1 := by rw [hX, Real.exp_sub]
  have hLe : (L : ℝ) ≤ Real.exp (U - 1) := by
    rw [hU1, le_div_iff₀ (Real.exp_pos 1)]; nlinarith
  have hLK : (L : ℝ) ≤ Real.exp (U - 1) * ((K : ℝ) - 2) * η := by
    rw [hU1, hη]
    have : X / Real.exp 1 * (Real.exp 1 * r) * (r / X) = L := by
      field_simp; rw [← hrr]; ring
    calc (L : ℝ) = X / Real.exp 1 * (Real.exp 1 * r) * (r / X) := this.symm
      _ ≤ X / Real.exp 1 * ((K : ℝ) - 2) * (r / X) := by
          gcongr; linarith
  have hmain := hdm η K hη0 hK3 (hΔ.trans hΔ1) U L a b ha hb hLe hLK
  refine hmain.trans ?_
  -- bound the bracket
  set ℓ := Real.log (X / L) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith)
  have hb1 : 2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 ≤
      14 * L / X * (ℓ + 3) ^ 2 := by
    refine (bmain_mono hΔ0 hΔ hΔ1).trans ?_
    have hlog : Real.log (1 / (14 * L / X)) ≤ ℓ := by
      rw [hℓ]; apply Real.log_le_log (by positivity)
      rw [one_div_div, div_le_div_iff₀ (by positivity) hL0]; nlinarith
    have hlog0 : 0 ≤ Real.log (1 / (14 * L / X)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hb2 : η ^ 2 * Real.exp U = L / X := by
    rw [hη, ← hX, div_pow, ← hrr]; field_simp
  have hb3 : η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U)) * Real.exp (2 * U) =
      X ^ (5 / 4 : ℝ) * (L : ℝ) ^ (-(5 / 8) : ℝ) := by
    rw [mul_assoc, ← Real.exp_add, show -(2 * U) + 2 * U = 0 by ring, Real.exp_zero, mul_one,
      hη, Real.div_rpow hr0.le hX0.le, hr, Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le,
      Real.rpow_neg hX0.le, div_inv_eq_mul, mul_comm]
    norm_num
  have hE2 : Real.exp (2 * U) = X * X := by rw [hX, ← Real.exp_add]; ring_nf
  have hsq : 1 ≤ (ℓ + 3) ^ 2 := by nlinarith
  have hXL : 0 ≤ X * L := by positivity
  set P := η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U)) with hP
  have hP0 : 0 ≤ P := by positivity
  calc C0 * Real.exp (2 * U) * (2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 +
        η ^ 2 * Real.exp U + P)
      ≤ C0 * Real.exp (2 * U) * (14 * L / X * (ℓ + 3) ^ 2 + L / X + P) := by
        rw [hb2]; gcongr
    _ = C0 * (14 * (X * L * (ℓ + 3) ^ 2) + X * L + P * Real.exp (2 * U)) := by
        rw [hE2]; field_simp
    _ ≤ C0 * (15 * (X * L * (ℓ + 3) ^ 2) + X ^ (5 / 4 : ℝ) * (L : ℝ) ^ (-(5 / 8) : ℝ)) := by
        rw [hP, hb3]
        apply mul_le_mul_of_nonneg_left _ hC0
        nlinarith [mul_le_mul_of_nonneg_left hsq hXL]
    _ ≤ 15 * C0 * (X * L * (ℓ + 3) ^ 2 + X ^ (5 / 4 : ℝ) * (L : ℝ) ^ (-(5 / 8) : ℝ)) := by
        have : 0 ≤ X ^ (5 / 4 : ℝ) * (L : ℝ) ^ (-(5 / 8) : ℝ) := by positivity
        nlinarith

end LeanLab.PNTPort.Selberg

