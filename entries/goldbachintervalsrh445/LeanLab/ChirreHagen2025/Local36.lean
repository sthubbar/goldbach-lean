module

public import Mathlib
public import LeanLab.ChirreHagen2025.ThetaPsi

/-!
P0075, A. Chirre and M. V. Hagen, On Goldbach numbers in short intervals, arXiv 2512.23534v1,
Section 3, proof of Theorem 2 from the local bound (3.6). Unit U-6350, track T2.
The paper proves, under RH, for `λ > 1`, `κ > 1`, `η > 0`, `x ≥ √2 λ` and `0 < δ ≤ 10^-13`,
display (3.6): `∫_x^{κx} 𝒱(δ, y)² dy ≤ 𝒞(κ, λ, η) δ log²(ℓ/δ) x²`, `ℓ = √(1+δ) + 1`,
and then sums it over `[x/κ^{n+1}, x/κ^n]` with `κ = 100`, `λ = 1.677`, `η = 5·10^-11`,
`𝒞/(κ² - 1) = 2.22571…`, to reach Theorem 2, `J_ψ(x, δ) ≤ 2.2258 δ log²(2.0001/δ) x²`.
Here (3.6) at those parameters is the one hypothesis, `Local36`; the dyadic sum, the
constant and the small range are proved. The small range `[1, 100 √2 λ]` is bounded by
Mathlib's Chebyshev bound `ψ x ≤ (log 4 + 4) x` and `∫ (ψ((1+δ)y) - ψ(y)) ≤ δ Y ψ((1+δ)Y)`,
so, unlike the paper, no Schoenfeld input and no numerical table is used there.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1125Z-cloud41.
Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.Local36
open Real Chebyshev

/-- `𝒱(δ, y) = ψ((1+δ)y) - ψ(y) - δ y`. -/
noncomputable def V (δ y : ℝ) : ℝ := ψ ((1 + δ) * y) - ψ y - δ * y

/-- The constant `𝒞(κ, λ, η)` displayed after (3.6). -/
noncomputable def Ccal (κ lam η : ℝ) : ℝ :=
  (1 + η) * (2.0282 / (√6 * π)) * (κ ^ 2 + 1 / lam ^ 2) * ((lam ^ 3 + 1) / (lam - 1))
  + 13 / 10 ^ 18 * (1 + 1 / η) * (lam ^ 3 - 1 / κ ^ 3) * ((lam + 1) / lam ^ 2)

/-- `ℓ = √(1+δ) + 1`. -/
noncomputable def ell (δ : ℝ) : ℝ := √(1 + δ) + 1

/-- Display (3.6) of Chirre-Hagen at `κ = 100`, `λ = 1.677`, `η = 5·10^-11`, the paper's
choice; the paper proves it under RH for every `x ≥ √2 λ`. -/
def Local36 : Prop :=
  ∀ x δ : ℝ, √2 * 1.677 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
    ∫ y in x..100 * x, V δ y ^ 2
      ≤ Ccal 100 1.677 (5 / 10 ^ 11) * δ * Real.log (ell δ / δ) ^ 2 * x ^ 2

theorem Ccal_le : Ccal 100 1.677 (5 / 10 ^ 11) ≤ 22255.1 := by
  have h6 : (2.44948 : ℝ) ≤ √6 := by
    rw [show (2.44948 : ℝ) = √(2.44948 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpi : (3.141592 : ℝ) ≤ π := le_of_lt Real.pi_gt_d6
  have hden : (2.44948 : ℝ) * 3.141592 ≤ √6 * π := by
    apply mul_le_mul h6 hpi (by norm_num) (by positivity)
  have hq : 2.0282 / (√6 * π) ≤ (0.263565 : ℝ) := by
    calc 2.0282 / (√6 * π) ≤ 2.0282 / ((2.44948 : ℝ) * 3.141592) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      _ ≤ 0.263565 := by norm_num
  have hq0 : 0 ≤ 2.0282 / (√6 * π) := by positivity
  unfold Ccal
  have hP : (0 : ℝ) ≤ (1 + 5 / 10 ^ 11) * ((100 : ℝ) ^ 2 + 1 / 1.677 ^ 2)
      * ((1.677 ^ 3 + 1) / (1.677 - 1)) := by norm_num
  have : (1 + 5 / 10 ^ 11) * (2.0282 / (√6 * π)) * ((100 : ℝ) ^ 2 + 1 / 1.677 ^ 2)
      * ((1.677 ^ 3 + 1) / (1.677 - 1))
      ≤ (1 + 5 / 10 ^ 11) * 0.263565 * ((100 : ℝ) ^ 2 + 1 / 1.677 ^ 2)
      * ((1.677 ^ 3 + 1) / (1.677 - 1)) := by nlinarith
  have hn : (1 + 5 / 10 ^ 11) * 0.263565 * ((100 : ℝ) ^ 2 + 1 / 1.677 ^ 2)
      * ((1.677 ^ 3 + 1) / (1.677 - 1))
      + 13 / 10 ^ 18 * (1 + 1 / (5 / 10 ^ 11)) * (1.677 ^ 3 - 1 / 100 ^ 3)
      * ((1.677 + 1) / 1.677 ^ 2) ≤ 22255.1 := by norm_num
  linarith

theorem Ccal_nonneg : 0 ≤ Ccal 100 1.677 (5 / 10 ^ 11) := by
  unfold Ccal; positivity

theorem V_sq_ii {δ c d : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    IntervalIntegrable (fun y => V δ y ^ 2) MeasureTheory.volume c d := by
  have := psi_integrand_ii hδ hc hcd
  simpa [V] using this

/-- `log(ℓ/δ) ≤ log(2.0001/δ)` and `1 ≤ log(ℓ/δ)` for `0 < δ ≤ 10^-13`. -/
theorem log_ell_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) :
    1 ≤ Real.log (ell δ / δ) ∧ Real.log (ell δ / δ) ≤ Real.log (2.0001 / δ) := by
  have hs : √(1 + δ) ≤ 1.0001 := by
    rw [show (1.0001 : ℝ) = √(1.0001 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs1 : 1 ≤ √(1 + δ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + δ by linarith)
    simpa using this
  have hl : ell δ ≤ 2.0001 := by unfold ell; linarith
  have hl2 : 2 ≤ ell δ := by unfold ell; linarith
  have hbig : 10 ^ 13 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; linarith
  have h1 : 2 * 10 ^ 13 ≤ ell δ / δ := by
    rw [div_eq_mul_one_div]; nlinarith
  refine ⟨?_, ?_⟩
  · have he : Real.exp 1 ≤ ell δ / δ := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (ell δ / δ) := Real.log_le_log (Real.exp_pos 1) he
  · apply Real.log_le_log (by linarith)
    exact div_le_div_of_nonneg_right hl hδ.le

/-- `∫_1^Y (ψ((1+δ)y) - ψ(y)) ≤ δ Y ψ((1+δ)Y)`, as `intD_le` for `ψ - θ`. -/
theorem intDpsi_le {X δ : ℝ} (hX : 1 ≤ X) (hδ : 0 < δ) :
    ∫ y in (1 : ℝ)..X, (ψ ((1 + δ) * y) - ψ y) ≤ δ * X * ψ ((1 + δ) * X) := by
  have hk : 0 < 1 + δ := by linarith
  have iF : ∀ a b, IntervalIntegrable (fun t => ψ t) MeasureTheory.volume a b :=
    fun a b => (show Monotone (fun t => ψ t) from fun u v huv => psi_mono huv).intervalIntegrable
  have iFk : IntervalIntegrable (fun t => ψ ((1 + δ) * t)) MeasureTheory.volume 1 X :=
    (show Monotone fun t => ψ ((1 + δ) * t) from
      fun u v huv => psi_mono (by nlinarith)).intervalIntegrable
  have hsplit : (∫ y in (1 : ℝ)..X, (ψ ((1 + δ) * y) - ψ y))
      = (∫ y in (1 : ℝ)..X, ψ ((1 + δ) * y)) - ∫ y in (1 : ℝ)..X, ψ y :=
    intervalIntegral.integral_sub iFk (iF 1 X)
  have hsub : (∫ y in (1 : ℝ)..X, ψ ((1 + δ) * y))
      = (1 + δ)⁻¹ * ∫ u in (1 + δ) * 1..(1 + δ) * X, ψ u := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => ψ t) (ne_of_gt hk), smul_eq_mul]
  have hI0 : 0 ≤ ∫ u in (1 + δ) * 1..(1 + δ) * X, ψ u :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun u _ => psi_nonneg u)
  have hinv : (1 + δ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h1 : (1 + δ)⁻¹ * (∫ u in (1 + δ) * 1..(1 + δ) * X, ψ u)
      ≤ ∫ u in (1 + δ) * 1..(1 + δ) * X, ψ u := by
    nlinarith
  have s1 : (∫ u in (1 + δ) * 1..X, ψ u) + (∫ u in X..(1 + δ) * X, ψ u)
      = ∫ u in (1 + δ) * 1..(1 + δ) * X, ψ u :=
    intervalIntegral.integral_add_adjacent_intervals (iF _ _) (iF _ _)
  have s2 : (∫ u in (1 : ℝ)..(1 + δ) * 1, ψ u) + (∫ u in (1 + δ) * 1..X, ψ u)
      = ∫ u in (1 : ℝ)..X, ψ u :=
    intervalIntegral.integral_add_adjacent_intervals (iF _ _) (iF _ _)
  have h0 : 0 ≤ ∫ u in (1 : ℝ)..(1 + δ) * 1, ψ u :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun u _ => psi_nonneg u)
  have htop : (∫ u in X..(1 + δ) * X, ψ u) ≤ ∫ u in X..(1 + δ) * X, ψ ((1 + δ) * X) := by
    apply intervalIntegral.integral_mono_on (by nlinarith) (iF _ _)
      (intervalIntegrable_const)
    intro u hu; exact psi_mono hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at htop
  have e : ((1 + δ) * X - X) * ψ ((1 + δ) * X) = δ * X * ψ ((1 + δ) * X) := by ring
  rw [hsplit, hsub]
  linarith

theorem psi_480_le : ψ 480 ≤ 2600 := by
  have h := psi_le_const_mul_self (x := (480 : ℝ)) (by norm_num)
  have hl : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  linarith

/-- The small range: `∫_1^Y 𝒱² ≤ 4·10^9 δ` for `1 ≤ Y ≤ 240` and `0 < δ ≤ 1`. -/
theorem small_range {Y δ : ℝ} (hY : 1 ≤ Y) (hY2 : Y ≤ 240) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ y in (1 : ℝ)..Y, V δ y ^ 2 ≤ 4 * 10 ^ 9 * δ := by
  set M : ℝ := ψ 480 with hM
  have hM0 : 0 ≤ M := psi_nonneg _
  have hM1 : M ≤ 2600 := psi_480_le
  have iD : IntervalIntegrable (fun y => ψ ((1 + δ) * y) - ψ y) MeasureTheory.volume 1 Y := by
    have a := (show Monotone fun t => ψ ((1 + δ) * t) from
      fun u v huv => psi_mono (by nlinarith)).intervalIntegrable (μ := MeasureTheory.volume)
      (a := 1) (b := Y)
    have b := (show Monotone (fun t => ψ t) from
      fun u v huv => psi_mono huv).intervalIntegrable (μ := MeasureTheory.volume) (a := 1) (b := Y)
    exact a.sub b
  have hpt : ∀ y ∈ Set.Icc (1 : ℝ) Y,
      V δ y ^ 2 ≤ 2 * M * (ψ ((1 + δ) * y) - ψ y) + 2 * δ * Y ^ 2 := by
    intro y hy
    have hD0 : 0 ≤ ψ ((1 + δ) * y) - ψ y := by
      have := psi_mono (show y ≤ (1 + δ) * y by nlinarith [hy.1]); linarith
    have hDM : ψ ((1 + δ) * y) - ψ y ≤ M := by
      have h1 : ψ ((1 + δ) * y) ≤ M := psi_mono (by nlinarith [hy.1, hy.2])
      have := psi_nonneg y; linarith
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hyY : y ^ 2 ≤ Y ^ 2 := by nlinarith [hy.2]
    have hδ2 : δ ^ 2 ≤ δ := by nlinarith
    unfold V
    set D := ψ ((1 + δ) * y) - ψ y
    have e : ψ ((1 + δ) * y) - ψ y - δ * y = D - δ * y := by simp [D]
    rw [e]
    nlinarith [sq_nonneg (D + δ * y), mul_le_mul_of_nonneg_left hDM hD0,
      mul_le_mul hδ2 hyY (sq_nonneg y) hδ.le]
  have hmono := intervalIntegral.integral_mono_on hY (V_sq_ii hδ (by norm_num) hY)
    ((iD.const_mul (2 * M)).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add (iD.const_mul (2 * M)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hD := intDpsi_le hY hδ
  have hpY : ψ ((1 + δ) * Y) ≤ M := psi_mono (by nlinarith)
  have hint0 : 0 ≤ ∫ y in (1 : ℝ)..Y, (ψ ((1 + δ) * y) - ψ y) := by
    apply intervalIntegral.integral_nonneg hY
    intro y hy
    have := psi_mono (show y ≤ (1 + δ) * y by nlinarith [hy.1]); linarith
  have k1 : 2 * M * (∫ y in (1 : ℝ)..Y, (ψ ((1 + δ) * y) - ψ y)) ≤ 2 * M * (δ * Y * M) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc _ ≤ δ * Y * ψ ((1 + δ) * Y) := hD
      _ ≤ δ * Y * M := mul_le_mul_of_nonneg_left hpY (by positivity)
  have k2 : 2 * M * (δ * Y * M) ≤ 2 * 2600 * (δ * 240 * 2600) := by
    have : M * M ≤ 2600 * 2600 := by nlinarith
    have hY0 : 0 ≤ Y := by linarith
    have : δ * Y ≤ δ * 240 := mul_le_mul_of_nonneg_left hY2 hδ.le
    nlinarith [mul_nonneg hδ.le hY0]
  have k3 : (Y - 1) * (2 * δ * Y ^ 2) ≤ 240 * (2 * δ * 240 ^ 2) := by
    have hY0 : 0 ≤ Y := by linarith
    have : Y ^ 2 ≤ 240 ^ 2 := by nlinarith
    have : Y - 1 ≤ 240 := by linarith
    have : 0 ≤ 2 * δ * Y ^ 2 := by positivity
    calc (Y - 1) * (2 * δ * Y ^ 2) ≤ 240 * (2 * δ * Y ^ 2) := by nlinarith
      _ ≤ 240 * (2 * δ * 240 ^ 2) := by nlinarith
  nlinarith

/-- The dyadic step: for `√2 λ ≤ x < √2 λ · 100^(n+1)`,
`∫_1^x 𝒱² ≤ 𝒞/(100² - 1) · δ log²(ℓ/δ) x² + 4·10^9 δ`. -/
theorem dyadic (h : Local36) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (n : ℕ) :
    ∀ x : ℝ, √2 * 1.677 ≤ x → x < √2 * 1.677 * 100 ^ (n + 1) →
      ∫ y in (1 : ℝ)..x, V δ y ^ 2
        ≤ Ccal 100 1.677 (5 / 10 ^ 11) / 9999 * δ * Real.log (ell δ / δ) ^ 2 * x ^ 2
          + 4 * 10 ^ 9 * δ := by
  set K := Ccal 100 1.677 (5 / 10 ^ 11) with hK
  set L := Real.log (ell δ / δ) ^ 2 with hL
  have hK0 : 0 ≤ K := Ccal_nonneg
  have hL0 : 0 ≤ L := sq_nonneg _
  have hs2 : √2 ≤ 1.4143 := by
    rw [show (1.4143 : ℝ) = √(1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs1 : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
  have hδ1' : δ ≤ 1 := by linarith [show (1 / 10 ^ 13 : ℝ) ≤ 1 by norm_num]
  have base : ∀ x : ℝ, √2 * 1.677 ≤ x → x < √2 * 1.677 * 100 →
      ∫ y in (1 : ℝ)..x, V δ y ^ 2 ≤ K / 9999 * δ * L * x ^ 2 + 4 * 10 ^ 9 * δ := by
    intro x hx1 hx2
    have := small_range (Y := x) (by nlinarith) (by nlinarith) hδ hδ1'
    have : 0 ≤ K / 9999 * δ * L * x ^ 2 := by positivity
    linarith
  induction n with
  | zero => intro x hx1 hx2; exact base x hx1 (by simpa using hx2)
  | succ n ih =>
    intro x hx1 hx2
    rcases lt_or_ge x (√2 * 1.677 * 100) with hlt | hge
    · exact base x hx1 hlt
    · have hx0 : 0 < x := by nlinarith
      have hy1 : √2 * 1.677 ≤ x / 100 := by rw [le_div_iff₀ (by norm_num)]; linarith
      have hy2 : x / 100 < √2 * 1.677 * 100 ^ (n + 1) := by
        rw [div_lt_iff₀ (by norm_num)]
        calc x < √2 * 1.677 * 100 ^ (n + 1 + 1) := hx2
          _ = √2 * 1.677 * 100 ^ (n + 1) * 100 := by ring
      have IH := ih (x / 100) hy1 hy2
      have LOC := h (x / 100) δ hy1 hδ hδ1
      rw [show 100 * (x / 100) = x by ring] at LOC
      have LOC' : ∫ y in x / 100..x, V δ y ^ 2 ≤ K * δ * L * (x / 100) ^ 2 := by
        rw [hK, hL]; exact LOC
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (V_sq_ii hδ (by norm_num) (show (1 : ℝ) ≤ x / 100 by nlinarith))
        (V_sq_ii hδ (by positivity) (show x / 100 ≤ x by linarith))
      rw [← hsplit]
      have e : K / 9999 * δ * L * (x / 100) ^ 2 + K * δ * L * (x / 100) ^ 2
          = K / 9999 * δ * L * x ^ 2 := by ring
      linarith

/-- Theorem 2 of Chirre-Hagen, `J_ψ(x, δ) ≤ 2.2258 δ log²(2.0001/δ) x²` for `x ≥ 10^13` and
`0 < δ ≤ 10^-13`, from the local bound (3.6) alone. -/
theorem theorem2_of_local36 (h : Local36) : ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ →
    δ ≤ 1 / 10 ^ 13 → Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 := by
  intro x δ hx hδ hδ1
  have hs2 : √2 ≤ 1.4143 := by
    rw [show (1.4143 : ℝ) = √(1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs1 : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
  have ha : 0 < √2 * 1.677 := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / (√2 * 1.677)) (by norm_num : (1 : ℝ) < 100)
  have hxn : x < √2 * 1.677 * 100 ^ (n + 1) := by
    rw [div_lt_iff₀ ha] at hn
    have : (100 : ℝ) ^ n ≤ 100 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hD := dyadic h hδ hδ1 n x (by nlinarith) hxn
  obtain ⟨hl1, hl2⟩ := log_ell_bounds hδ hδ1
  set L := Real.log (ell δ / δ) with hL
  set L2 := Real.log (2.0001 / δ) with hL2
  have hLL : L ^ 2 ≤ L2 ^ 2 := by nlinarith
  have hL21 : 1 ≤ L2 ^ 2 := by nlinarith
  have hK := Ccal_le
  have hK0 := Ccal_nonneg
  have hx2 : (10 : ℝ) ^ 26 ≤ x ^ 2 := by nlinarith
  have t1 : Ccal 100 1.677 (5 / 10 ^ 11) / 9999 * δ * L ^ 2 * x ^ 2
      ≤ 22255.1 / 9999 * δ * L2 ^ 2 * x ^ 2 := by
    have : Ccal 100 1.677 (5 / 10 ^ 11) / 9999 ≤ 22255.1 / 9999 := by linarith
    have hdx : 0 ≤ δ * x ^ 2 := by positivity
    have := mul_le_mul this hLL (sq_nonneg _) (by norm_num)
    nlinarith
  have t2 : 4 * 10 ^ 9 * δ ≤ (2.2258 - 22255.1 / 9999) * δ * L2 ^ 2 * x ^ 2 := by
    have : (10 : ℝ) ^ 26 ≤ L2 ^ 2 * x ^ 2 := by nlinarith
    have hc : (4 * 10 ^ 9 : ℝ) ≤ (2.2258 - 22255.1 / 9999) * 10 ^ 26 := by norm_num
    have hc0 : (0 : ℝ) ≤ 2.2258 - 22255.1 / 9999 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left this hc0]
  unfold Jpsi
  have e : (fun y => (ψ ((1 + δ) * y) - ψ y - δ * y) ^ 2) = fun y => V δ y ^ 2 := rfl
  rw [e]
  nlinarith

/-- With RH: Theorem 2 holds once (3.6) holds under RH. -/
theorem theorem2_of_RH_local36 (h : RiemannHypothesis → Local36) :
    RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 :=
  fun hRH => theorem2_of_local36 (h hRH)

end LeanLab.ChirreHagen2025.Local36

