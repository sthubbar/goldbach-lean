module

public import LeanLab.PNTPort.ExplicitPsi1.Edges

/-!
# The explicit formula for `ψ₁(x)/x` with all zeros

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input.

For `x > 0`, with `w₁(y) = max(0, 1 - y)` and `Zall` the zeros of ζ with `Re ρ ≥ -1/2`:

`explicit_formula_psi1`:
`Σ_n Λ(n) w₁(n/x) = x/2 - ζ'(0)/ζ(0) - Σ_{ρ ∈ Zall} m(ρ) x^ρ/(ρ(ρ + 1)) + (1/2π) ∫ F(-1/2 + it) dt`,
the zero sum absolutely convergent;

`explicit_formula_psi1_bound`: the last term is at most `K x^{-1/2}`.

`Σ_n Λ(n) w₁(n/x)` is `ψ₁(x)/x`, `ψ₁(x) = ∫₀ˣ ψ(u) du`. The classical form, Davenport ch. 17,
has `ψ₁(x) = x²/2 - Σ_ρ x^{ρ+1}/(ρ(ρ+1)) - x ζ'(0)/ζ(0) + O(x^{1/2})` as `x → ∞` after the
trivial zeros are summed; here they are left in the explicit left line integral, which is bounded
for every `x > 0`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology Set MeasureTheory
open scoped Real

local notation "ζ" => riemannZeta

/-- The zero term `m(ρ) x^ρ/(ρ(ρ + 1))`. -/
noncomputable def zterm (x : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)))

lemma Zall_re_lt {ρ : ℂ} (h : ρ ∈ Zall) : ρ.re < 1 := by
  by_contra h'
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h') h.1

lemma norm_zterm_le {x : ℝ} (hx : 0 < x) {ρ : ℂ} (h : ρ ∈ Zall) :
    ‖zterm x ρ‖ ≤ Xb x * hw ρ := by
  unfold zterm hw
  rw [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_natCast]
  have := rpow_le_Xb hx h.2 (by linarith [Zall_re_lt h])
  calc (analyticOrderNatAt ζ ρ : ℝ) * (x ^ ρ.re / ‖ρ * (ρ + 1)‖)
      = x ^ ρ.re * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ * (ρ + 1)‖) := by ring
    _ ≤ Xb x * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ * (ρ + 1)‖) :=
        mul_le_mul_of_nonneg_right this (by positivity)

/-- The zero sum converges absolutely. -/
theorem summable_zterm {x : ℝ} (hx : 0 < x) : Summable (fun ρ : Zall => zterm x ρ) :=
  Summable.of_norm_bounded (summable_hw.mul_left (Xb x)) (fun ρ => norm_zterm_le hx ρ.2)

lemma log_sq_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have h0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ y) (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have h3 : Real.log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
    have : y ^ (1 / 2 : ℝ) / (1 / 2) = 2 * y ^ (1 / 2 : ℝ) := by ring
    linarith
  calc Real.log y ^ 2 ≤ (2 * y ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h3 2
    _ = 4 * y := by rw [mul_pow, h2]; ring

/-- **The explicit formula for `ψ₁(x)/x`**, exact, with the left line integral kept. -/
theorem explicit_formula_psi1 {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / x) =
      x / 2 - deriv ζ 0 / ζ 0 - ∑' ρ : Zall, zterm x ρ +
        (1 / (2 * π) : ℂ) * ∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I) := by
  obtain ⟨C, hC, hgood⟩ := good_height_pm
  choose! Tf hTfI hTf using hgood
  set T : ℕ → ℝ := fun n => Tf (max (n : ℝ) 5) with hTdef
  have hT5 : ∀ n : ℕ, (5 : ℝ) ≤ max (n : ℝ) 5 := fun n => le_max_right _ _
  have hTI : ∀ n : ℕ, T n ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1) := fun n => hTfI _ (hT5 n)
  have hTge : ∀ n : ℕ, (n : ℝ) ≤ T n := fun n => (le_max_left _ _).trans (hTI n).1
  have hTpos : ∀ n : ℕ, 0 < T n := fun n => by linarith [(hTI n).1, hT5 n]
  have hTtop : Tendsto T atTop atTop := tendsto_atTop_mono hTge tendsto_natCast_atTop_atTop
  have hTb : ∀ n : ℕ, ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T n, -T n} : Set ℝ),
      ζ ((σ : ℂ) + y * I) ≠ 0 ∧
        ‖deriv ζ ((σ : ℂ) + y * I) / ζ ((σ : ℂ) + y * I)‖ ≤ C * Real.log (max (n : ℝ) 5) ^ 2 :=
    fun n => hTf _ (hT5 n)
  obtain ⟨CL, hCL, hL⟩ := ZetaZeros.logDeriv_left_line
  -- the border of each rectangle is free of zeros
  have hborder : ∀ n : ℕ, ∀ z ∈ RectangleBorder (⟨-1 / 2, -T n⟩ : ℂ) ⟨2, T n⟩, ζ z ≠ 0 := by
    intro n z hz
    have hzR := rectangleBorder_subset_rectangle _ _ hz
    rw [mem_rect (by norm_num) (hTpos n).le] at hzR
    obtain ⟨⟨hr1, hr2⟩, _, _⟩ := hzR
    have hzz : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
    rcases border_cases hz with h | h | h | h
    · rw [hzz, h]; exact (hTb n z.re ⟨hr1, hr2⟩ (-T n) (by simp)).1
    · rw [hzz, h]; exact (hL z.im).1
    · rw [hzz, h]; exact (hTb n z.re ⟨hr1, hr2⟩ (T n) (by simp)).1
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [h]; norm_num)
  have hid : ∀ n : ℕ, (1 / (2 * π) : ℂ) * (VInt x 2 (T n) - VInt x (-1 / 2) (T n)) +
      (1 / (2 * π * I)) * (HInt x (-T n) - HInt x (T n)) =
        x / 2 - deriv ζ 0 / ζ 0 - ∑ ρ ∈ (zeros_rect_finite 2 (T n)).toFinset, zterm x ρ := by
    intro n
    rw [← rect_decomp]
    exact rect_explicit hx (by norm_num) (hTpos n) (hborder n)
  -- the vertical integrals converge
  have hV2 : Tendsto (fun n => VInt x 2 (T n)) atTop
      (𝓝 (∫ t : ℝ, F x (((2 : ℝ) : ℂ) + t * I))) :=
    intervalIntegral_tendsto_integral (integrable_right hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hVL : Tendsto (fun n => VInt x (-1 / 2) (T n)) atTop
      (𝓝 (∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I))) :=
    intervalIntegral_tendsto_integral (integrable_left hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  -- the horizontal integrals tend to 0
  have hHb : ∀ n : ℕ, ‖HInt x (-T n) - HInt x (T n)‖ ≤ 2 * (10 * C * Xb x / max (n : ℝ) 5) := by
    intro n
    have hy5 := hT5 n
    have hlog := log_sq_le (by linarith : (1 : ℝ) ≤ max (n : ℝ) 5)
    have hX := Xb_pos hx
    have hb : ∀ y ∈ ({T n, -T n} : Set ℝ), ‖HInt x y‖ ≤ 10 * C * Xb x / max (n : ℝ) 5 := by
      intro y hy
      have hyabs : |y| = T n := by
        rcases hy with rfl | rfl
        · exact abs_of_pos (hTpos n)
        · rw [abs_neg]; exact abs_of_pos (hTpos n)
      refine (norm_HInt_le hx hy5 (hTI n).1 hyabs (fun σ hσ => (hTb n σ hσ y hy).2)).trans ?_
      have hm : 0 < max (n : ℝ) 5 := by linarith
      rw [le_div_iff₀ hm]
      have e : C * Real.log (max (n : ℝ) 5) ^ 2 * (Xb x / max (n : ℝ) 5 ^ 2) * (5 / 2) *
          max (n : ℝ) 5 = (5 / 2) * C * Xb x * (Real.log (max (n : ℝ) 5) ^ 2 / max (n : ℝ) 5) := by
        field_simp
      rw [e]
      have : Real.log (max (n : ℝ) 5) ^ 2 / max (n : ℝ) 5 ≤ 4 := by
        rw [div_le_iff₀ hm]; linarith
      calc (5 / 2) * C * Xb x * (Real.log (max (n : ℝ) 5) ^ 2 / max (n : ℝ) 5)
          ≤ (5 / 2) * C * Xb x * 4 := by gcongr
        _ = 10 * C * Xb x := by ring
    calc ‖HInt x (-T n) - HInt x (T n)‖ ≤ ‖HInt x (-T n)‖ + ‖HInt x (T n)‖ := norm_sub_le _ _
      _ ≤ 10 * C * Xb x / max (n : ℝ) 5 + 10 * C * Xb x / max (n : ℝ) 5 :=
          add_le_add (hb _ (by simp)) (hb _ (by simp))
      _ = 2 * (10 * C * Xb x / max (n : ℝ) 5) := by ring
  have hH : Tendsto (fun n => HInt x (-T n) - HInt x (T n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm hHb
    have hmax : Tendsto (fun n : ℕ => max (n : ℝ) 5) atTop atTop :=
      tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := 10 * C * Xb x)).div_atTop hmax
    simpa using this.const_mul 2
  -- the zero sums converge
  classical
  set fs : ℕ → Finset Zall := fun n => (zeros_rect_finite 2 (T n)).toFinset.subtype (· ∈ Zall)
  have hfs : ∀ n : ℕ, ∑ ρ ∈ (zeros_rect_finite 2 (T n)).toFinset, zterm x ρ =
      ∑ ρ ∈ fs n, zterm x ρ := by
    intro n
    rw [Finset.sum_subtype_of_mem]
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have := (mem_rect (by norm_num) (hTpos n).le).mp hρ.1
    exact ⟨hρ.2, this.1.1⟩
  have hfs_top : Tendsto fs atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    set M := ∑ ρ ∈ b, |(ρ : ℂ).im|
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop M] with n hn
    intro ρ hρ
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset]
    have him : |(ρ : ℂ).im| ≤ M :=
      Finset.single_le_sum (f := fun ρ : Zall => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
    refine ⟨(mem_rect (by norm_num) (hTpos n).le).mpr
      ⟨⟨ρ.2.2, by linarith [Zall_re_lt ρ.2]⟩, abs_le.mp ?_⟩, ρ.2.1⟩
    linarith [hTge n]
  have hS : Tendsto (fun n => ∑ ρ ∈ (zeros_rect_finite 2 (T n)).toFinset, zterm x ρ) atTop
      (𝓝 (∑' ρ : Zall, zterm x ρ)) := by
    simp_rw [hfs]
    exact (summable_zterm hx).hasSum.comp hfs_top
  -- pass to the limit
  have hlim1 : Tendsto (fun n => (1 / (2 * π) : ℂ) * (VInt x 2 (T n) - VInt x (-1 / 2) (T n)) +
      (1 / (2 * π * I)) * (HInt x (-T n) - HInt x (T n))) atTop
      (𝓝 ((1 / (2 * π) : ℂ) * ((∫ t : ℝ, F x (((2 : ℝ) : ℂ) + t * I)) -
        ∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I)) + (1 / (2 * π * I)) * 0)) :=
    ((hV2.sub hVL).const_mul _).add (hH.const_mul _)
  have hlim2 : Tendsto (fun n => (1 / (2 * π) : ℂ) * (VInt x 2 (T n) - VInt x (-1 / 2) (T n)) +
      (1 / (2 * π * I)) * (HInt x (-T n) - HInt x (T n))) atTop
      (𝓝 (x / 2 - deriv ζ 0 / ζ 0 - ∑' ρ : Zall, zterm x ρ)) := by
    simp_rw [hid]
    exact tendsto_const_nhds.sub hS
  have heq := tendsto_nhds_unique hlim1 hlim2
  rw [perron_F hx]
  rw [mul_zero, add_zero] at heq
  linear_combination heq

/-- **The explicit formula for `ψ₁(x)/x` with error `O(x^{-1/2})`**, for every `x > 0`. -/
theorem explicit_formula_psi1_bound : ∃ K : ℝ, ∀ x : ℝ, 0 < x →
    ‖∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / x) -
      (x / 2 - deriv ζ 0 / ζ 0 - ∑' ρ : Zall, zterm x ρ)‖ ≤ K * x ^ (-1 / 2 : ℝ) := by
  obtain ⟨K, hK⟩ := norm_integral_left_le
  refine ⟨K / (2 * π), fun x hx => ?_⟩
  rw [explicit_formula_psi1 hx, add_sub_cancel_left, norm_mul]
  have hπ : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hπ]
  calc 1 / (2 * π) * ‖∫ t : ℝ, F x (((-1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ 1 / (2 * π) * (K * x ^ (-1 / 2 : ℝ)) := by gcongr; exact hK x hx
    _ = K / (2 * π) * x ^ (-1 / 2 : ℝ) := by ring

end LeanLab.PNTPort.ExplicitPsi1

