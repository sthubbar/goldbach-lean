module

public import LeanLab.BhowmikGrimmelt2026.Decomp508a
public import LeanLab.BhowmikGrimmelt2026.PrimitivePsiEstimates592
public import LeanLab.BhowmikGrimmelt2026.SPLIT_davenport_integer_formula592
public import LeanLab.DERZ1997.Decomp1529b2
public import LeanLab.PNTPort.ExplicitPsi1.ZeroSum

/-!
A split of `primitive_psi_zero_expansion508` into three leaves plus an assembly.

The statement is a sharp explicit formula with zeros: for a primitive character of modulus
`q ≤ √X` there is a height `T` between `X` and `2X` and the finite list `Z` of the zeros with
`|Im ρ| ≤ T`, such that the twisted von Mangoldt sum up to `n` differs from the main term
minus the zero sum by a uniform `O((log X)²)`.

The three leaves are (1) the height and the zero list: up to any height at least `X` the zeros
in the open strip form a finite set, so a finset characterised exactly by the zero condition
exists; (2) the error estimate away from the trivial character, where the main term vanishes;
(3) the same estimate for the trivial character, where the main term is `n` itself. Leaves (2)
and (3) take `T` and `Z` as given, so neither of them has to produce the height or the list;
the assembly takes them from leaf (1) and splits on whether the character is trivial, keeping
the larger of the two constants.

AI wrote the Lean code. Binary Goldbach is open. The finite list and principal steps are proved.
The nonprincipal estimate is conditional on the cited Davenport half weighted formula leaf.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- PROVED from character_zero_finset504 with T equal to X.
This produces no zero avoidance estimate. Step 1, the height and the zero list: for a primitive `χ` of modulus `q` and any
`X ≥ 2` there is a height `T` between `X` and `2X` and a finset `Z` of complex numbers whose
members are exactly the zeros of the `L`-function of `χ` in the open strip with imaginary part
of absolute value at most `T`. This is the finiteness and the selection step; it produces no
estimate at all, and leaves (2) and (3) only use the characterisation it gives. -/
theorem zero_set_window508 {X q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hX : 2 ≤ X) (hprim : χ.IsPrimitive) :
    ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) := by
  refine ⟨(X : ℝ), ⟨le_rfl, ?_⟩, ?_⟩
  · nlinarith only [show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X]
  · exact character_zero_finset504 χ (X : ℝ)

/-! ### Auxiliary development for the principal leaf

The truncated sharp explicit formula for `ζ` at any good height `T ≥ 5`, together with the
zero count, the reciprocal zero sum and the strip bound it needs. These are private helpers;
only `principal_psi_zero_bound508` below uses them. -/

section PrimitivePsiZeroAux508

open Complex Set Filter Topology MeasureTheory

open LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp1529b2

/-- The horizontal log-derivative bound of `Decomp1529b.perron_logDeriv_all197`, with the
separation hypothesis replaced by explicit bounds on the strip `-1/2 <= σ <= 2`
(the shape produced by `PNTPort.ExplicitPsi1.good_height_pm`). -/
private theorem logDeriv_all_gen :
    ∃ C : ℝ, 0 < C ∧ ∀ {T C₀ : ℝ}, 5 ≤ T → 0 ≤ C₀ →
      (∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T, -T} : Set ℝ),
        riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
          ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤ C₀ * Real.log T ^ 2) →
      ∀ σ : ℝ, σ ≤ 3 → ∀ y ∈ ({T, -T} : Set ℝ),
        riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
          ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤
            C * (1 + C₀) * Real.log T ^ 2 * (1 + |σ|) := by
  obtain ⟨A, hA, hleft⟩ := LeanLab.PNTPort.ExplicitPsi1.Trivial.logDeriv_left_region
  refine ⟨1 + ‖deriv riemannZeta ((3 / 2 : ℝ) : ℂ) / riemannZeta ((3 / 2 : ℝ) : ℂ)‖ + 3 * A + 2, by positivity,
    ?_⟩
  intro T C₀ hT hC₀ hstrip σ hσ y hy
  set M : ℝ := ‖deriv riemannZeta ((3 / 2 : ℝ) : ℂ) / riemannZeta ((3 / 2 : ℝ) : ℂ)‖ with hMdef
  set C : ℝ := 1 + M + 3 * A + 2 with hCdef
  have hM : 0 ≤ M := norm_nonneg _
  have hC : 0 < C := by rw [hCdef]; positivity
  have hT0 : 0 < T := by linarith
  have hyT : |y| = T := by rcases hy with rfl | rfl <;> simp [abs_of_pos hT0]
  have hy1 : 1 ≤ |y| := by rw [hyT]; linarith
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hL2 : 1 ≤ Real.log T ^ 2 := by nlinarith
  have hLle : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  have hσ1 : 1 ≤ 1 + |σ| := by linarith [abs_nonneg σ]
  have hC1 : 1 + C₀ ≤ 1 + C₀ := le_rfl
  have hCpos : 0 ≤ 1 + C₀ := by linarith
  have hCC1 : C₀ ≤ C * (1 + C₀) := by
    nlinarith [hC₀, mul_nonneg hC.le hCpos, abs_nonneg σ]
  by_cases hneg : σ < -1 / 2
  · obtain ⟨hne, hb⟩ := hleft σ y hneg.le hy1
    refine ⟨hne, ?_⟩
    have hlog : Real.log (|y| + 3) ≤ 2 * Real.log T := by
      have h3 : (|y| : ℝ) + 3 ≤ T ^ 2 := by rw [hyT]; nlinarith
      calc Real.log (|y| + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) h3
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    have hlogA := mul_le_mul_of_nonneg_left hlog hA.le
    have hnegσ : -σ = |σ| := (abs_of_neg (by linarith)).symm
    have hCC : 3 * A + 1 ≤ C := by rw [hCdef]; nlinarith
    have hinner : A * Real.log (|y| + 3) - σ + A ≤
        (3 * A + 1) * Real.log T ^ 2 * (1 + |σ|) := by
      rw [sub_eq_add_neg, hnegσ]
      nlinarith [mul_nonneg hA.le (by positivity : (0:ℝ) ≤ Real.log T ^ 2 * |σ|),
        mul_nonneg hA.le (by positivity : (0:ℝ) ≤ Real.log T ^ 2), mul_nonneg hA.le (by linarith : (0:ℝ) ≤ Real.log T)]
    refine hb.trans (hinner.trans ?_)
    have hstep : (3 * A + 1) * Real.log T ^ 2 * (1 + |σ|) ≤
        C * (1 + C₀) * Real.log T ^ 2 * (1 + |σ|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [hCpos, hCC]
    exact hstep
  · have hσlo : -1 / 2 ≤ σ := le_of_not_gt hneg
    by_cases hσhi : σ ≤ 2
    · obtain ⟨hne, hb⟩ := hstrip σ ⟨hσlo, hσhi⟩ y hy
      refine ⟨hne, ?_⟩
      calc ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖
          ≤ C₀ * Real.log T ^ 2 := hb
        _ ≤ C * (1 + C₀) * Real.log T ^ 2 * (1 + |σ|) := by
            have h1 : C₀ * Real.log T ^ 2 ≤ C * (1 + C₀) * Real.log T ^ 2 := by
              apply mul_le_mul_of_nonneg_right hCC1 (by positivity)
            nlinarith [h1, mul_nonneg (mul_nonneg hC.le hCpos)
              (by positivity : (0:ℝ) ≤ Real.log T ^ 2), mul_nonneg (abs_nonneg σ)
              (by positivity : (0:ℝ) ≤ C * (1 + C₀) * Real.log T ^ 2), sq_nonneg (Real.log T)]
    · have hσ2 : 2 < σ := lt_of_not_ge hσhi
      by_cases hσ3 : 3 / 2 ≤ σ
      · have hne : riemannZeta ((σ : ℂ) + y * I) ≠ 0 := by
          apply riemannZeta_ne_zero_of_one_lt_re
          simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, mul_zero, I_im, mul_one]
          linarith
        refine ⟨hne, ?_⟩
        have hb : ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤ M := by
          have hre : ((σ : ℂ) + y * I).re = σ := by simp
          exact LeanLab.PNTPort.ExplicitPsi1.Trivial.logDeriv_right_le (u := (σ : ℂ) + y * I)
            (by rw [hre]; linarith)
        refine hb.trans ?_
        have hMC : M ≤ C := by rw [hCdef]; nlinarith
        calc M ≤ C := hMC
          _ ≤ C * Real.log T ^ 2 := le_mul_of_one_le_right hC.le hL2
          _ ≤ C * (1 + C₀) * Real.log T ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith [hCpos, hC.le]
          _ ≤ C * (1 + C₀) * Real.log T ^ 2 * (1 + |σ|) :=
              le_mul_of_one_le_right (by positivity) hσ1
      · exact absurd hσ2 (by linarith)

open LeanLab.Routes.Decomp1551a in
/-- The horizontal-edge integral bound of `Decomp1529b.perron_horizontal_bound197`, with the
separation hypothesis replaced by explicit `riemannZeta'/riemannZeta` bounds. -/
private theorem horizontal_gen {x T B : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) (hB : 0 ≤ B)
    (hln : ∀ σ : ℝ, σ ≤ 3 → ∀ y ∈ ({T, -T} : Set ℝ),
      riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤
          B * Real.log T ^ 2 * (1 + |σ|)) :
    ∀ a : ℝ, a ≤ 0 → ∀ y ∈ ({T, -T} : Set ℝ),
      IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume a
          (1 + 1 / Real.log x) ∧
      ‖∫ u in a..(1 + 1 / Real.log x), fK x ((u : ℂ) + y * I)‖ ≤
        39 * B * (x * Real.log T ^ 2 / T) := by
  have hnegative {a : ℝ} (ha : a ≤ 0) :
      ∫ u in a..0, Real.exp (u / 2) * (1 - u) ≤ 6 := by
    have hd (u : ℝ) : HasDerivAt (fun v : ℝ => (6 - 2 * v) * Real.exp (v / 2))
        (Real.exp (u / 2) * (1 - u)) u := by
      have h1 : HasDerivAt (fun v : ℝ => 6 - 2 * v) (-2) u := by
        convert (hasDerivAt_const u (6 : ℝ)).sub ((hasDerivAt_id u).const_mul 2) using 1
        · funext v
          simp [id]
        · norm_num
      have h2 : HasDerivAt (fun v : ℝ => Real.exp (v / 2)) (Real.exp (u / 2) / 2) u := by
        convert ((hasDerivAt_id u).div_const 2).exp using 1
        · funext v
          simp [id, div_eq_mul_inv]
        · simp [id, div_eq_mul_inv]
      convert h1.mul h2 using 1 <;> ring
    have hi : IntervalIntegrable (fun u : ℝ => Real.exp (u / 2) * (1 - u)) volume a 0 :=
      (by fun_prop : Continuous (fun u : ℝ => Real.exp (u / 2) * (1 - u))).intervalIntegrable _ _
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
    rw [heq]
    have hp : 0 ≤ (6 - 2 * a) * Real.exp (a / 2) := mul_nonneg (by linarith) (Real.exp_pos _).le
    norm_num only [mul_zero, sub_zero, zero_div, Real.exp_zero, mul_one]
    linarith
  intro a ha y hy
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hLx : 1 / 2 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_two_gt_d9
    linarith
  have hLx0 : 0 < Real.log x := by linarith
  let c : ℝ := 1 + 1 / Real.log x
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc3 : c ≤ 3 := by
    have hh : 1 / Real.log x ≤ 2 := (div_le_iff₀ hLx0).mpr (by linarith)
    dsimp [c]
    linarith
  have hxc : x ^ c ≤ 3 * x := by
    have heq : x ^ c = x * Real.exp 1 := by
      dsimp [c]
      rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
      congr 1
      rw [mul_one_div_cancel hLx0.ne']
    rw [heq]
    nlinarith [Real.exp_one_lt_three]
  let D : ℝ := B * Real.log T ^ 2 / T
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hyT : |y| = T := by rcases hy with rfl | rfl <;> simp [abs_of_pos hT0]
  have hy0 : y ≠ 0 := by intro hh; rw [hh, abs_zero] at hyT; linarith
  have hbound : ∀ u : ℝ, u ≤ 3 →
      riemannZeta ((u : ℂ) + y * I) ≠ 0 ∧
      ‖deriv riemannZeta ((u : ℂ) + y * I) / riemannZeta ((u : ℂ) + y * I)‖ ≤
        B * Real.log T ^ 2 * (1 + |u|) := by
    intro u hu
    exact hln u hu y hy
  have hpoint {u : ℝ} (hu : u ≤ 3) :
      ‖fK x ((u : ℂ) + y * I)‖ ≤ D * x ^ u * (1 + |u|) := by
    let z : ℂ := (u : ℂ) + y * I
    have hden : T ≤ ‖z‖ := by
      have hh := Complex.abs_im_le_norm z
      simpa [z, hyT] using hh
    have hn := (hbound u hu).2
    change ‖-logDeriv riemannZeta z * (x : ℂ) ^ z / z‖ ≤ _
    rw [norm_div, norm_mul, norm_neg, logDeriv_apply,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : z.re = u := by simp [z]
    rw [hre]
    calc
      _ ≤ (B * Real.log T ^ 2 * (1 + |u|)) * x ^ u / ‖z‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity)) (norm_nonneg _)
      _ ≤ (B * Real.log T ^ 2 * (1 + |u|)) * x ^ u / T :=
        div_le_div_of_nonneg_left (by positivity) hT0 hden
      _ = _ := by dsimp [D]; ring
  have hcont : ContinuousOn (fun u : ℝ => fK x ((u : ℂ) + y * I)) (Set.Icc a c) := by
    intro u hu
    have hzne := (hbound u (by linarith [hu.2])).1
    have hz0 : (u : ℂ) + y * I ≠ 0 := by
      intro hh
      have hi := congrArg Complex.im hh
      simp at hi
      exact hy0 hi
    have hz1 : (u : ℂ) + y * I ≠ 1 := by
      intro hh
      have hi := congrArg Complex.im hh
      simp at hi
      exact hy0 hi
    have hcA : ContinuousAt (fK x) ((u : ℂ) + y * I) :=
      (perron_integrand_analytic197 hx0 hz0 hz1 hzne).continuousAt
    have hcB : ContinuousAt (fun v : ℝ => (v : ℂ) + y * I) u := by fun_prop
    have hcC : ContinuousAt (fun v : ℝ => fK x ((v : ℂ) + y * I)) u :=
      ContinuousAt.comp (g := fK x) (f := fun v : ℝ => (v : ℂ) + y * I) hcA hcB
    exact hcC.continuousWithinAt
  have hac : a ≤ c := by linarith
  have hint : IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume a c :=
    hcont.intervalIntegrable_of_Icc hac
  refine ⟨hint, ?_⟩
  have hi0 : IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume a 0 :=
    (hcont.mono (Set.Icc_subset_Icc le_rfl hc0.le)).intervalIntegrable_of_Icc ha
  have h0i : IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume 0 c :=
    (hcont.mono (Set.Icc_subset_Icc ha le_rfl)).intervalIntegrable_of_Icc hc0.le
  have hneg : ‖∫ u in a..0, fK x ((u : ℂ) + y * I)‖ ≤ 6 * D := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun u : ℝ => fK x ((u : ℂ) + y * I))
      (g := fun u : ℝ => D * (Real.exp (u / 2) * (1 - u))) ha
      (Filter.Eventually.of_forall (fun u hu => by
        have hu0 : u ≤ 0 := hu.2
        have hxp : x ^ u ≤ Real.exp (u / 2) := by
          rw [Real.rpow_def_of_pos hx0]
          apply Real.exp_le_exp.mpr
          have hmul := mul_le_mul_of_nonpos_right hLx hu0
          nlinarith
        calc
          _ ≤ D * x ^ u * (1 + |u|) := hpoint (by linarith)
          _ = D * (x ^ u * (1 - u)) := by rw [abs_of_nonpos hu0]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxp (by linarith)) hD))
      ((by fun_prop : Continuous (fun u : ℝ => D * (Real.exp (u / 2) * (1 - u)))).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh.trans (by have := mul_le_mul_of_nonneg_left (hnegative ha) hD; nlinarith)
  have hpos : ‖∫ u in (0 : ℝ)..c, fK x ((u : ℂ) + y * I)‖ ≤ 36 * D * x := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := c) (C := 12 * D * x) (fun u hu => by
        rw [Set.uIoc_of_le hc0.le] at hu
        have hu0 : 0 ≤ u := hu.1.le
        have hpow : x ^ u ≤ 3 * x :=
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hu.2).trans hxc
        have hab : 1 + |u| ≤ 4 := by rw [abs_of_nonneg hu0]; linarith [hu.2]
        calc
          _ ≤ D * x ^ u * (1 + |u|) := hpoint (by linarith [hu.2])
          _ ≤ D * (3 * x) * 4 := mul_le_mul (mul_le_mul_of_nonneg_left hpow hD) hab
            (by positivity) (by positivity)
          _ = _ := by ring)
    rw [sub_zero, abs_of_pos hc0] at hh
    exact hh.trans (by have := mul_le_mul_of_nonneg_left hc3 (show 0 ≤ 12 * D * x by positivity); nlinarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 h0i]
  have hh := norm_add_le (∫ u in a..0, fK x ((u : ℂ) + y * I))
    (∫ u in (0 : ℝ)..c, fK x ((u : ℂ) + y * I))
  have hscale := mul_le_mul_of_nonneg_left hx hD
  have hsum : ‖(∫ u in a..0, fK x ((u : ℂ) + y * I)) +
      (∫ u in (0 : ℝ)..c, fK x ((u : ℂ) + y * I))‖ ≤ 39 * D * x :=
    hh.trans (by nlinarith)
  convert hsum using 1 <;> dsimp [D] <;> ring

open LeanLab.Routes.Decomp1551a in
/-- The contour shift of `Decomp1529b.contour_shift` with the separation hypothesis replaced by
explicit `riemannZeta'/riemannZeta` bounds on `[-1/2, 2] x {±iT}` (the shape produced by
`PNTPort.ExplicitPsi1.good_height_pm`), uniformly in `x` and `T`. -/
private theorem contour_gen :
    ∃ C : ℝ, 0 < C ∧ ∀ {x T B : ℝ}, 2 ≤ x → 5 ≤ T → 0 ≤ B →
      (∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T, -T} : Set ℝ),
        riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
          ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤ B * Real.log T ^ 2) →
      ∀ hfin : (zetaZeros T).Finite,
      ‖perronPsi x (1 + 1 / Real.log x) T -
          ((x : ℂ) - ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
            - Real.log (2 * Real.pi) - (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ)))‖ ≤
        C * (1 + B) * (x * Real.log T ^ 2 / T) := by
  obtain ⟨Cl, hClpos, hCl⟩ := logDeriv_all_gen
  refine ⟨2 * (39 * Cl) + 2, by positivity, ?_⟩
  intro x T B hx hT hB hstrip hfin
  set B' : ℝ := Cl * (1 + B) with hB'def
  have hB'0 : 0 ≤ B' := by rw [hB'def]; positivity
  have hB' : ∀ σ : ℝ, σ ≤ 3 → ∀ y ∈ ({T, -T} : Set ℝ),
      riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤
          B' * Real.log T ^ 2 * (1 + |σ|) := by
    intro σ hσ y hy
    exact hCl (C₀ := B) (by linarith) hB hstrip σ hσ y hy
  have hhor := horizontal_gen (x := x) (T := T) (B := B') hx (by linarith) hB'0 hB'
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  let c : ℝ := 1 + 1 / Real.log x
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlog]
  have hc3 : c ≤ 3 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    have : 1/2 ≤ Real.log x := by linarith [Real.log_two_gt_d9]
    have : 1 / Real.log x ≤ 2 := (div_le_iff₀ hlog).mpr (by linarith)
    dsimp [c]; linarith
  let V (a : ℝ) : ℂ := ∫ t in -T..T, fK x ((a:ℂ)+t*I)
  let H (a b y : ℝ) : ℂ := ∫ u in a..b, fK x ((u:ℂ)+y*I)
  let r : ℂ := 1/(2*Real.pi)
  let s : ℂ := 1/(2*Real.pi*I)
  let Q : ℂ := (x:ℂ) - ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ - Real.log (2*Real.pi)
  have hbound : ∀ u : ℝ, u ≤ 3 → ∀ y ∈ ({T,-T}:Set ℝ), riemannZeta ((u:ℂ)+y*I) ≠ 0 := by
    intro u hu y hy
    exact (hB' u hu y hy).1
  have hbd : ∀z ∈ RectangleBorder ⟨-1/2,-T⟩ ⟨c,T⟩, riemannZeta z ≠ 0 := by
    intro z hz
    have hzR := rectangleBorder_subset_rectangle _ _ hz
    have hmem := (LeanLab.PNTPort.ExplicitPsi1.mem_rect
      (by linarith : (-1/2:ℝ) ≤ c) hT0.le).mp hzR
    rcases LeanLab.PNTPort.ExplicitPsi1.border_cases hz with h | h | h | h
    · have he : z = (z.re:ℂ)+(-T:ℝ)*I := by apply Complex.ext <;> simp [h]
      rw [he]; exact hbound z.re (by linarith [hmem.1.2]) (-T) (by simp)
    · have he : z = (-1/2:ℂ)+z.im*I := by apply Complex.ext <;> simp [h]
      rw [he]; simpa using LeanLab.PNTPort.ZetaZeros.zeta_left_ne z.im
    · have he : z = (z.re:ℂ)+T*I := by apply Complex.ext <;> simp [h]
      rw [he]; exact hbound z.re (by linarith [hmem.1.2]) T (by simp)
    · exact riemannZeta_ne_zero_of_one_lt_re (by linarith)
  have hcentral : RectangleIntegral' (fK x) ⟨-1/2,-T⟩ ⟨c,T⟩ = Q := by
    have hrect := perron_rect_explicit197 hx0 hc hT0 hbd
    have hset : (LeanLab.PNTPort.ExplicitPsi1.zeros_rect_finite c T).toFinset =
        hfin.toFinset := by
      ext z
      simp only [Set.Finite.mem_toFinset]
      rw [perron_zeros_rect197 hc hT0.le]
    rw [hset] at hrect
    rw [hrect]
    dsimp [Q]
    simp only [zetaMult, mul_div_assoc]
    ring
  have hr : ‖r‖ ≤ 1 := by
    norm_num [r, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simpa [mul_inv, mul_comm] using (inv_le_one₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mpr
      (show 1 ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
  have hs : ‖s‖ ≤ 1 := by
    have he : s = r / I := by dsimp [r,s]; field_simp
    rw [he, norm_div, norm_I, div_one]
    exact hr
  have hP : perronPsi x c T = r * V c := perronPsi_eq_logDeriv197 hc
  have hK : ∀ K : ℕ, 1 ≤ K →
      ‖perronPsi x c T - (Q + (TrivU x K:ℂ))‖ ≤
        ‖V (-2*(K:ℝ)-1/2)‖ + 2*(39*B')*(x*Real.log T^2/T) := by
    intro K hK
    let a : ℝ := -2*(K:ℝ)-1/2
    have ha : a ≤ 0 := by dsimp [a]; have := Nat.cast_nonneg (α:=ℝ) K; linarith
    have hi (y:ℝ) (hy:y∈({T,-T}:Set ℝ)) := (hhor a ha y hy).1
    have hi0 (y:ℝ) (hy:y∈({T,-T}:Set ℝ)) := (hhor (-1/2) (by norm_num) y hy).1
    have hadj (y:ℝ) (hy:y∈({T,-T}:Set ℝ)) : H a (-1/2) y + H (-1/2) c y = H a c y := by
      exact intervalIntegral.integral_add_adjacent_intervals ((hi y hy).trans (hi0 y hy).symm) (hi0 y hy)
    have hl := perron_rect_left197 hx0 hK hT0
    rw [perron_triv_sum197] at hl
    rw [perron_rect_decomp197] at hl hcentral
    change r*(V (-1/2)-V a)+s*(H a (-1/2) (-T)-H a (-1/2) T) = _ at hl
    change r*(V c-V (-1/2))+s*(H (-1/2) c (-T)-H (-1/2) c T) = Q at hcentral
    have heq : perronPsi x c T - (Q+(TrivU x K:ℂ)) =
        r*V a-s*(H a c (-T)-H a c T) := by
      rw [hP]
      linear_combination hcentral + hl - s*(hadj (-T) (by simp)) + s*(hadj T (by simp))
    rw [heq]
    calc
      _ ≤ ‖r*V a‖ + ‖s*(H a c (-T)-H a c T)‖ := norm_sub_le _ _
      _ ≤ ‖V a‖ + (‖H a c (-T)‖+‖H a c T‖) := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hr)
          ((mul_le_of_le_one_left (norm_nonneg _) hs).trans (norm_sub_le _ _))
      _ ≤ _ := by
        have h1 := (hhor a ha (-T) (by simp)).2
        have h2 := (hhor a ha T (by simp)).2
        change ‖H a c (-T)‖ ≤ _ at h1
        change ‖H a c T‖ ≤ _ at h2
        linarith
  have hU : Tendsto (fun K:ℕ => (TrivU x K:ℂ)) atTop (nhds (TrivInf x:ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (trivU_tendsto x hx1)
  have hleft := perron_left_edge_limit197 hx1 hT0
  have hlim1 : Tendsto (fun K:ℕ => ‖perronPsi x c T - (Q+(TrivU x K:ℂ))‖) atTop
      (nhds ‖perronPsi x c T - (Q+(TrivInf x:ℂ))‖) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.add hU)).norm
  have hlim2 : Tendsto (fun K:ℕ => ‖V (-2*(K:ℝ)-1/2)‖ + 2*(39*B')*(x*Real.log T^2/T)) atTop
      (nhds (0 + 2*(39*B')*(x*Real.log T^2/T))) := by
    simpa only [norm_zero] using hleft.norm.add_const (2*(39*B')*(x*Real.log T^2/T))
  have hfinal : ‖perronPsi x c T - (Q+(TrivInf x:ℂ))‖ ≤ 0 + 2*(39*B')*(x*Real.log T^2/T) :=
    le_of_tendsto_of_tendsto hlim1 hlim2 (Filter.eventually_atTop.2 ⟨1,hK⟩)
  have hconst : 2 * (39 * B') * (x * Real.log T ^ 2 / T) ≤
      (2 * (39 * Cl) + 2) * (1 + B) * (x * Real.log T ^ 2 / T) := by
    have h0 : 0 ≤ x * Real.log T ^ 2 / T := by positivity
    have h1 : B' = Cl * (1 + B) := hB'def
    have h2 : 2 * (39 * B') ≤ (2 * (39 * Cl) + 2) * (1 + B) := by
      rw [h1]; nlinarith [hClpos.le, hB, mul_nonneg hClpos.le hB]
    exact mul_le_mul_of_nonneg_right h2 h0
  have hfin2 : ‖perronPsi x c T - (Q+(TrivInf x:ℂ))‖ ≤
      2 * (39 * B') * (x * Real.log T ^ 2 / T) := by
    simpa using hfinal
  exact (hfin2.trans hconst) |> fun h => by
    simpa [c,Q,TrivInf,zpow_neg,sub_eq_add_neg, mul_assoc] using h

/-- The sharp truncated explicit formula for `riemannZeta` at a good height, valid at **every** height
`5 <= T` (the `T <= x` restriction of `Decomp1529b2.explicit_formula_good266` is dropped: there it
only compared `log T` with `log x`). -/
private theorem explicit_gen508 :
    ∃ A : ℝ, 0 < A ∧ ∀ {x T B : ℝ}, 2 ≤ x → 5 ≤ T → 0 ≤ B →
      (∀ n : ℕ, (n : ℝ) ≠ x) →
      (∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T, -T} : Set ℝ),
        riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
          ‖deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I)‖ ≤ B * Real.log T ^ 2) →
      ∀ hfin : (zetaZeros T).Finite,
      ‖(Chebyshev.psi x : ℂ) - x +
          ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        A * (1 + B) * (x * Real.log x ^ 2 / T + Real.log x + x * Real.log T ^ 2 / T) := by
  obtain ⟨C, hCpos, hcont⟩ := contour_gen
  refine ⟨432 + 2 * C + 2 * (|Real.log (2 * Real.pi)| + 1) + 1, by positivity, ?_⟩
  intro x T B hx hT hB hxn hstrip hfin
  set K : ℝ := |Real.log (2 * Real.pi)| + 1 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set a : ℝ := x * Real.log x ^ 2 / T with hadef
  set b : ℝ := Real.log x with hbdef
  set cc : ℝ := x * Real.log T ^ 2 / T with hccdef
  have ha0 : 0 ≤ a := by rw [hadef]; exact div_nonneg (by positivity) hT0.le
  have hb0 : 0 ≤ b := by rw [hbdef]; linarith [Real.log_pos (by linarith : (1:ℝ) < x)]
  have hc0 : 0 ≤ cc := by rw [hccdef]; exact div_nonneg (by positivity) hT0.le
  have hsum0 : 0 ≤ a + b + cc := by linarith
  have hbhalf : (1 / 2 : ℝ) ≤ b := by
    rw [hbdef]
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  have hper := perron_error_arbitrary266 (x := x) (T := T) hx (by linarith) hxn
  have hcontb := hcont hx hT hB hstrip hfin
  have hw : 1 / 2 ≤ 1 - x ^ (-2 : ℤ) := by
    have hs : 2 ≤ x ^ 2 := by nlinarith
    have hi : (x ^ 2)⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
    simp only [zpow_neg, zpow_ofNat] at *
    norm_num at hi
    linarith
  have hw1 : 1 - x ^ (-2 : ℤ) ≤ 1 := by
    have : 0 ≤ x ^ (-2 : ℤ) := by positivity
    linarith
  have hcorr : |Real.log (1 - x ^ (-2 : ℤ))| ≤ 1 := by
    have hlo := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 - x ^ (-2 : ℤ))
    have hi : (1 - x ^ (-2 : ℤ))⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hw
    have hhi := Real.log_nonpos (by linarith : 0 ≤ 1 - x ^ (-2 : ℤ)) hw1
    rw [abs_of_nonpos hhi]
    norm_num only [one_div, inv_inv] at hi
    linarith
  have hcorrection : ‖(Real.log (2 * Real.pi) : ℂ) +
      (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ))‖ ≤ K := by
    rw [hKdef]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖(1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ))‖ ≤ 1 / 2 := by
      have hval : ‖(1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ))‖ =
          (1 / 2) * |Real.log (1 - x ^ (-2 : ℤ))| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      rw [hval]
      nlinarith [hcorr]
    have h1 : ‖(Real.log (2 * Real.pi) : ℂ)‖ = |Real.log (2 * Real.pi)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    linarith
  set Z : ℂ := ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ with hZdef
  have heq : (Chebyshev.psi x : ℂ) - x + Z =
      ((Chebyshev.psi x : ℂ) - perronPsi x (1 + 1 / Real.log x) T) +
        (perronPsi x (1 + 1 / Real.log x) T -
          ((x : ℂ) - Z - Real.log (2 * Real.pi) -
            (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ)))) -
        ((Real.log (2 * Real.pi) : ℂ) + (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ))) := by
    ring
  -- the arithmetic bookkeeping
  set A : ℝ := 432 + 2 * C + 2 * K + 1 with hAdef
  have hA432 : (432 : ℝ) ≤ A := by rw [hAdef]; nlinarith [hCpos.le, hK0]
  have hAC : C ≤ A := by rw [hAdef]; nlinarith [hCpos.le, hK0]
  have hA2K : 2 * K ≤ A := by rw [hAdef]; nlinarith [hCpos.le, hK0]
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ 1 + B := by linarith
  have hAB : (1 / 2 : ℝ) ≤ (1 + B) * (a + b + cc) := by
    have h1 : (1 : ℝ) ≤ 1 + B := by linarith
    have h2 : (1 / 2 : ℝ) ≤ a + b + cc := by linarith
    calc (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
      _ ≤ (1 + B) * (a + b + cc) := mul_le_mul h1 h2 (by norm_num) (by linarith)
  have htotal : 432 * (a + b) + C * (1 + B) * cc + K ≤ A * (1 + B) * (a + b + cc) := by
    have h1B : (1 : ℝ) ≤ 1 + B := by linarith
    have e1 : 432 * (a + b) ≤ 432 * (1 + B) * (a + b + cc) := by
      have h : a + b ≤ a + b + cc := by linarith
      have h2 : 432 * (a + b) ≤ 432 * (a + b + cc) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      have h3 : 432 * (a + b + cc) ≤ 432 * (1 + B) * (a + b + cc) := by
        have h4 : (432 : ℝ) ≤ 432 * (1 + B) := by nlinarith
        calc 432 * (a + b + cc) ≤ (432 * (1 + B)) * (a + b + cc) :=
              mul_le_mul_of_nonneg_right h4 hsum0
          _ = 432 * (1 + B) * (a + b + cc) := by ring
      linarith
    have e2 : C * (1 + B) * cc ≤ C * (1 + B) * (a + b + cc) := by
      have h : cc ≤ a + b + cc := by linarith
      apply mul_le_mul_of_nonneg_left h
      positivity
    have e3 : K ≤ 2 * K * (1 + B) * (a + b + cc) := by
      have h2 : (1 : ℝ) ≤ 2 * (1 + B) * (a + b + cc) := by
        have h3 : (1 / 2 : ℝ) ≤ a + b + cc := by linarith
        nlinarith [hB0, h3]
      calc K ≤ K * 1 := le_of_eq (mul_one K).symm
        _ ≤ K * (2 * (1 + B) * (a + b + cc)) := mul_le_mul_of_nonneg_left h2 hK0
        _ = 2 * K * (1 + B) * (a + b + cc) := by ring
    have hsum : 432 * (1 + B) * (a + b + cc) + C * (1 + B) * (a + b + cc) +
        2 * K * (1 + B) * (a + b + cc) =
        (432 + C + 2 * K) * (1 + B) * (a + b + cc) := by ring
    have hle : (432 + C + 2 * K) * (1 + B) * (a + b + cc) ≤
        A * (1 + B) * (a + b + cc) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_right _ hB0
      rw [hAdef]; linarith
    linarith [e1, e2, e3, hsum, hle]
  set T1 : ℂ := (Chebyshev.psi x : ℂ) - perronPsi x (1 + 1 / Real.log x) T with hT1
  set T2 : ℂ := perronPsi x (1 + 1 / Real.log x) T -
    ((x : ℂ) - Z - Real.log (2 * Real.pi) - (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ))) with hT2
  set T3 : ℂ := (Real.log (2 * Real.pi) : ℂ) + (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ)) with hT3
  have hper1 : ‖T1‖ ≤ 432 * (a + b) := by
    have h1 : 432 * (x * Real.log x ^ 2 / T + Real.log x) = 432 * (a + b) := by
      rw [hadef, hbdef]
    rw [h1] at hper
    simpa [hT1] using hper
  have hcont1 : ‖T2‖ ≤ C * (1 + B) * cc := by
    have h2 : C * (1 + B) * (x * Real.log T ^ 2 / T) = C * (1 + B) * cc := by rw [hccdef]
    rw [h2] at hcontb
    simpa [hT2] using hcontb
  have hcorr1 : ‖T3‖ ≤ K := by simpa [hT3] using hcorrection
  have hgoal : A * (1 + B) * (x * Real.log x ^ 2 / T + Real.log x + x * Real.log T ^ 2 / T)
      = A * (1 + B) * (a + b + cc) := by rw [hadef, hbdef, hccdef]
  rw [heq, hgoal]
  have hstep : ‖T1 + T2 - T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := by
    refine (norm_sub_le _ _).trans ?_
    exact add_le_add (norm_add_le _ _) le_rfl
  exact hstep.trans (by linarith [hper1, hcont1, hcorr1, htotal])

/-! ## Part 2: the trivial-character bound

Everything below is proved in this file. The ingredients are
`PNTPort.ZetaZeros.good_height` (a good height in `[T, T+1]` with `riemannZeta'/riemannZeta` bounds on `1/2 ≤ Re ≤ 2`),
`PNTPort.ExplicitPsi1.fiber_count` (zeros in a unit window, `O(log n)` with multiplicity),
`PNTPort.ZetaZeros.digamma_strip`, and `explicit_gen508` above (the sharp truncated formula at a
good height, valid for every `T ≥ 5`).
-/

open LeanLab.BhowmikGrimmelt2026 in
/-- Under `ZeroBound Θ` a strip zero of `riemannZeta` has real part in `[1 - Θ, Θ]`: the functional
equation reflects `ρ` to `1 - ρ`, which is again a strip zero. -/
private theorem zero_re_ge {Θ : ℝ} (hZ : ZeroBound Θ) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : 1 - Θ ≤ ρ.re := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hnat : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
    intro n h
    have hc := congr_arg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hc
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hzero1 : riemannZeta (1 - ρ) = 0 := by
    rw [riemannZeta_one_sub hnat hρ1, hρ, mul_zero]
  have hb := hZ 1 (1 : DirichletCharacter ℂ 1) (1 - ρ) (by simpa using hzero1)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  simp only [Complex.sub_re, Complex.one_re] at hb
  linarith

/-- Telescoping step: `log n / n ≤ (log n)² - (log (n-1))²`, because
`log n - log (n-1) = ∫ ≥ 1/n` and `log (n-1) ≥ 0`. -/
private lemma log_div_le_sq_sub (n : ℕ) (hn : 2 ≤ n) :
    Real.log n / n ≤ Real.log n ^ 2 - Real.log (n - 1) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hprev : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hlog2 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog1 : 0 ≤ Real.log ((n : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hdiff : 1 / (n : ℝ) ≤ Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) := by
    rw [← Real.log_div (ne_of_gt hn0) (ne_of_gt hprev)]
    have hx : 0 < (n : ℝ) / ((n : ℝ) - 1) := by positivity
    have h := Real.one_sub_inv_le_log_of_pos hx
    have he : 1 - ((n : ℝ) / ((n : ℝ) - 1))⁻¹ = 1 / (n : ℝ) := by
      rw [inv_div]
      have h1 : (1 : ℝ) = (n : ℝ) / (n : ℝ) := (div_self (ne_of_gt hn0)).symm
      rw [h1, div_sub_div_same]
      congr 1
      ring
    rwa [he] at h
  have hkey : Real.log (n : ℝ) ^ 2 - Real.log ((n : ℝ) - 1) ^ 2 =
      (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) *
        (Real.log (n : ℝ) + Real.log ((n : ℝ) - 1)) := by ring
  rw [hkey]
  have hd0 : 0 ≤ Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) :=
    le_trans (le_of_lt (one_div_pos.mpr hn0)) hdiff
  have hsum : Real.log (n : ℝ) ≤ Real.log (n : ℝ) + Real.log ((n : ℝ) - 1) := by linarith
  calc Real.log (n : ℝ) / n = (1 / (n : ℝ)) * Real.log (n : ℝ) := by ring
    _ ≤ (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hdiff hlog2
    _ ≤ (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) *
          (Real.log (n : ℝ) + Real.log ((n : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hsum hd0

/-- `∑_{n = 2}^{N} log n / n ≤ (log N)²`. -/
private lemma sum_log_div_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / n ≤ Real.log N ^ 2 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have he : Finset.Icc 2 N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    rw [he]
    simp only [Finset.sum_empty]
    positivity
  · induction N, hN using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hs : Real.log 2 / 2 ≤ Real.log 2 ^ 2 := by nlinarith
      exact hs
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1)]
      have hstep := log_div_le_sq_sub (m + 1) (by omega)
      have hstep' : Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1) ≤
          Real.log ((m : ℝ) + 1) ^ 2 - Real.log (m : ℝ) ^ 2 := by
        have h := hstep
        rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring] at h
        rwa [show ((m : ℝ) + 1 - 1) = (m : ℝ) by ring] at h
      push_cast at ih ⊢
      linarith

open LeanLab.BhowmikGrimmelt2026 in
/-- Zeros of `riemannZeta` in the open strip with `|Im ρ| ≤ T`, weighted by `1/‖ρ‖`: `O(1 + log² T)`.
The zeros with `|Im ρ| ≤ 4` contribute a constant (they are finitely many, and `|ρ| ≥ 1 - Θ`),
the rest are counted in unit windows by `PNTPort.ExplicitPsi1.fiber_count`. -/
private theorem zero_recip_bound {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ hfin : (zetaZeros T).Finite,
      (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) ≤ C * (1 + Real.log (T + 2) ^ 2) := by
  obtain ⟨C1, hC1, hfib⟩ := LeanLab.PNTPort.ExplicitPsi1.fiber_count
  obtain ⟨Z4, hZ4⟩ := character_zero_finset504 (q := 1) (1 : DirichletCharacter ℂ 1) (4 : ℝ)
  have hZ4mem : ∀ ρ : ℂ, ρ ∈ Z4 ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 4 := by
    intro ρ
    rw [hZ4]
    simp
  have hth : (0 : ℝ) < 1 - Θ := by linarith
  set K4 : ℝ := ∑ ρ ∈ Z4, (zetaMult ρ : ℝ) with hK4def
  have hK4 : 0 ≤ K4 := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨K4 / (1 - Θ) + 8 * C1 + 1, by positivity, fun T hT hfin => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set s := hfin.toFinset with hs
  have hsZ : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
    intro ρ hρ
    rw [hs, Set.Finite.mem_toFinset] at hρ
    exact hρ
  have hsmall : ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 4), (zetaMult ρ : ℝ) / ‖ρ‖ ≤ K4 / (1 - Θ) := by
    have hsub : s.filter (fun ρ => |ρ.im| ≤ 4) ⊆ Z4 := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rw [hZ4mem]
      obtain ⟨hz, h0, h1, _⟩ := hsZ ρ hρ.1
      exact ⟨hz, h0, h1, hρ.2⟩
    calc ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 4), (zetaMult ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 4), (zetaMult ρ : ℝ) / (1 - Θ) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [Finset.mem_filter] at hρ
          obtain ⟨hz, h0, h1, _⟩ := hsZ ρ hρ.1
          have hge : (1 - Θ) ≤ ‖ρ‖ :=
            (zero_re_ge hZ hz h0 h1).trans (le_trans (le_abs_self ρ.re) (Complex.abs_re_le_norm ρ))
          exact div_le_div_of_nonneg_left (by positivity) hth hge
      _ = (∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 4), (zetaMult ρ : ℝ)) / (1 - Θ) := by
          rw [Finset.sum_div]
      _ ≤ (∑ ρ ∈ Z4, (zetaMult ρ : ℝ)) / (1 - Θ) := by
          apply div_le_div_of_nonneg_right _ hth.le
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = K4 / (1 - Θ) := by rw [hK4def]
  have hbig : ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.im| ≤ 4), (zetaMult ρ : ℝ) / ‖ρ‖ ≤
      8 * C1 * Real.log (T + 2) ^ 2 := by
    set N := ⌈T⌉₊ with hN
    set u := s.filter (fun ρ => ¬ |ρ.im| ≤ 4) with hu
    have hmaps : ∀ ρ ∈ u, ⌈|ρ.im|⌉₊ ∈ Finset.Icc 5 N := by
      intro ρ hρ
      rw [hu, Finset.mem_filter] at hρ
      obtain ⟨hρs, hbig4⟩ := hρ
      obtain ⟨_, _, _, himT⟩ := hsZ ρ hρs
      rw [Finset.mem_Icc]
      refine ⟨?_, Nat.ceil_mono himT⟩
      have h4 : (4 : ℝ) < |ρ.im| := not_le.mp hbig4
      have h45 : (4 : ℕ) < ⌈|ρ.im|⌉₊ := Nat.lt_ceil.mpr h4
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun ρ => (zetaMult ρ : ℝ) / ‖ρ‖)]
    have hB : ∀ n ∈ Finset.Icc 5 N,
        ∑ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), (zetaMult ρ : ℝ) / ‖ρ‖ ≤
          4 * C1 * Real.log n / ((n : ℝ) - 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hd : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hu' : ∀ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n),
          riemannZeta ρ = 0 ∧ (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρu, hceil⟩ := hρ
        rw [hu, Finset.mem_filter] at hρu
        have hc := (Nat.ceil_eq_iff (by omega)).mp hceil
        rw [Nat.cast_sub (by omega)] at hc
        push_cast at hc
        exact ⟨(hsZ ρ hρu.1).1, hc⟩
      calc ∑ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), (zetaMult ρ : ℝ) / ‖ρ‖
          ≤ ∑ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), (zetaMult ρ : ℝ) / ((n : ℝ) - 1) := by
            apply Finset.sum_le_sum
            intro ρ hρ
            obtain ⟨_, hlo, _⟩ := hu' ρ hρ
            have hge : ((n : ℝ) - 1) ≤ ‖ρ‖ := hlo.le.trans (Complex.abs_im_le_norm ρ)
            exact div_le_div_of_nonneg_left (by positivity) hd hge
        _ = (∑ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), (zetaMult ρ : ℝ)) / ((n : ℝ) - 1) := by
            rw [Finset.sum_div]
        _ ≤ 4 * C1 * Real.log n / ((n : ℝ) - 1) := by
            apply div_le_div_of_nonneg_right (hfib n hn.1 _ hu') hd.le
    calc ∑ n ∈ Finset.Icc 5 N, ∑ ρ ∈ u.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), (zetaMult ρ : ℝ) / ‖ρ‖
        ≤ ∑ n ∈ Finset.Icc 5 N, 4 * C1 * Real.log n / ((n : ℝ) - 1) := Finset.sum_le_sum hB
      _ ≤ ∑ n ∈ Finset.Icc 5 N, 8 * C1 * (Real.log n / n) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn5 : 5 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn5r : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
          have hn0 : (0 : ℝ) < (n : ℝ) := by
            have : (0 : ℕ) < n := by omega
            exact_mod_cast this
          have hm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
          have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
          have hkey : Real.log n / ((n : ℝ) - 1) ≤ 2 * (Real.log n / n) := by
            rw [div_le_iff₀ hm1]
            rw [show 2 * (Real.log n / n) * ((n : ℝ) - 1) = 2 * Real.log n * ((n : ℝ) - 1) / n
              by ring]
            rw [le_div_iff₀ hn0]
            nlinarith [mul_nonneg hlog (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2), hn5r]
          calc 4 * C1 * Real.log n / ((n : ℝ) - 1)
              = 4 * C1 * (Real.log n / ((n : ℝ) - 1)) := by ring
            _ ≤ 4 * C1 * (2 * (Real.log n / n)) := by
                apply mul_le_mul_of_nonneg_left hkey
                positivity
            _ = 8 * C1 * (Real.log n / n) := by ring
      _ ≤ 8 * C1 * (∑ n ∈ Finset.Icc 2 N, Real.log n / n) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
          · intro i hi _
            have h2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
            have hlog : (0 : ℝ) ≤ Real.log i :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ i))
            have hi0 : (0 : ℝ) < (i : ℝ) := by positivity
            exact mul_nonneg (mul_nonneg (by norm_num) hC1.le) (div_nonneg hlog hi0.le)
      _ ≤ 8 * C1 * Real.log N ^ 2 := by
          have hsum := sum_log_div_le N
          have hC10 : (0 : ℝ) ≤ C1 := hC1.le
          nlinarith [hsum, sq_nonneg (Real.log N)]
      _ ≤ 8 * C1 * Real.log (T + 2) ^ 2 := by
          have hNle : (N : ℝ) ≤ T + 2 := by
            have h1 := Nat.ceil_lt_add_one hT0
            push_cast at h1
            linarith
          have hN1 : (1 : ℝ) ≤ N := by
            have h : ⌈(1 : ℝ)⌉₊ ≤ ⌈T⌉₊ := Nat.ceil_mono hT
            have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by simp
            rw [h1] at h
            exact_mod_cast h
          have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
          have hlogm : Real.log N ≤ Real.log (T + 2) := Real.log_le_log (by linarith) hNle
          have hsq : Real.log N ^ 2 ≤ Real.log (T + 2) ^ 2 :=
            pow_le_pow_left₀ hlogN hlogm 2
          have hC10 : (0 : ℝ) ≤ C1 := hC1.le
          nlinarith [hsq]
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.im| ≤ 4)]
  have hlog2 : 0 ≤ Real.log (T + 2) ^ 2 := sq_nonneg _
  have hK40 : 0 ≤ K4 / (1 - Θ) := div_nonneg hK4 hth.le
  have hC1l : 0 ≤ C1 := hC1.le
  nlinarith [hsmall, hbig, hlog2, hK40]

/-- The horizontal bound on `[-1/2, 2] + iT` from the bound on `[1/2, 2] + iT`: the functional
equation in logarithmic-derivative form handles `-1/2 ≤ Re s ≤ 1/2`, and the lower half-segment
follows by conjugation. The returned constant is added to the input constant, uniformly in `T`. -/
private theorem strip_all :
    ∃ KK : ℝ, 0 < KK ∧ ∀ (T B : ℝ), 5 ≤ T → 0 ≤ B →
      (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
        riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) /
          riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ B * Real.log T ^ 2) →
      ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2, ∀ y ∈ ({T, -T} : Set ℝ),
        riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I) ≠ 0 ∧
          ‖deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (B + KK) * Real.log T ^ 2 := by
  obtain ⟨K, hK, hKbd⟩ := LeanLab.PNTPort.ZetaZeros.digamma_strip
  refine ⟨2 * K + 8, by positivity, ?_⟩
  intro T B hT hB hstrip
  have hT0 : (0 : ℝ) < T := by linarith
  have hLT1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hLT2 : (1 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
  have hlog3 : Real.log (T + 3) ≤ 2 * Real.log T := by
    have h2 : T + 3 ≤ T ^ 2 := by nlinarith
    calc Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h2
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hstrip' : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B * Real.log T ^ 2 := by
    intro σ hσ
    have h := hstrip σ hσ
    have he : ((σ : ℂ) + Complex.I * (T : ℂ)) = ((σ : ℂ) + (T : ℂ) * Complex.I) := by ring
    rw [he] at h
    exact h
  have hmain : ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2,
      riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ (B + (2 * K + 8)) * Real.log T ^ 2 := by
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    obtain ⟨hσlo, hσhi⟩ := hσ
    have hL2 : (0 : ℝ) ≤ Real.log T ^ 2 := sq_nonneg _
    by_cases hhalf : (1 / 2 : ℝ) ≤ σ
    · obtain ⟨h1, h2⟩ := hstrip' σ ⟨hhalf, hσhi⟩
      refine ⟨h1, h2.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (by linarith) hL2
    · have hlt : σ < 1 / 2 := lt_of_not_ge hhalf
      have h1lo : (1 / 2 : ℝ) ≤ 1 - σ := by linarith
      have h1hi : (1 - σ) ≤ 2 := by linarith
      set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hS
      have hsre : s.re = σ := by simp [hS]
      have hsim : s.im = T := by simp [hS]
      have hconj : (1 - s) = (starRingEnd ℂ) (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp [hsre, hsim]
      have hzs : riemannZeta s ≠ 0 := by
        intro hz0
        have hnotnat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
          intro n h
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            have hi : s.im = (0 : ℂ).im := by rw [h]; simp
            rw [hsim] at hi
            simp at hi
            linarith
          · have hc := congr_arg Complex.re h
            simp only [Complex.neg_re, Complex.natCast_re] at hc
            rw [hsre] at hc
            have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
        have hs1 : s ≠ 1 := by
          intro h
          have hc := congr_arg Complex.im h
          rw [hsim] at hc
          simp at hc
          linarith
        have hfe := riemannZeta_one_sub hnotnat hs1
        have h1s : riemannZeta (1 - s) = 0 := by
          rw [hfe, hz0, mul_zero]
        have hwne : riemannZeta (1 - s) ≠ 0 := by
          rw [hconj, riemannZeta_conj]
          simpa using (hstrip' (1 - σ) ⟨h1lo, h1hi⟩).1
        exact hwne h1s
      have hint : ∀ n : ℤ, s ≠ n := by
        intro n h
        have hc := congr_arg Complex.im h
        simp only [Complex.intCast_im, hsim] at hc
        linarith
      have hFE := logDeriv_riemannZeta_one_sub hint hzs
      rw [logDeriv_apply, logDeriv_apply] at hFE
      have h1w : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ B * Real.log T ^ 2 := by
        rw [hconj]
        have hc := logDerivZeta_conj (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I)
        simp only [Pi.div_apply] at hc ⊢
        rw [hc, Complex.norm_conj]
        exact (hstrip' (1 - σ) ⟨h1lo, h1hi⟩).2
      have h3 : ‖Complex.digamma s‖ ≤ K * Real.log (T + 3) + 2 := by
        have h := hKbd T (by linarith) σ (by linarith) hσhi
        have he : ((σ : ℂ) + (T : ℂ) * Complex.I) = s := by rw [hS]
        rw [he] at h
        exact h
      have h4 : ‖(Real.pi : ℂ) / 2 * Complex.tan (Real.pi * s / 2)‖ ≤ 4 := by
        have e : Real.pi * s / 2 =
            ((Real.pi * σ / 2 : ℝ) : ℂ) + ((Real.pi * T / 2 : ℝ) : ℂ) * Complex.I := by
          rw [hS]; push_cast; ring
        rw [e, norm_mul]
        have ht' := LeanLab.PNTPort.ZetaZeros.norm_tan_le (x := Real.pi * σ / 2)
          (y := Real.pi * T / 2) (by nlinarith [Real.pi_gt_three])
        have hp : ‖(Real.pi : ℂ) / 2‖ ≤ 2 := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          norm_num
          linarith [Real.pi_lt_four]
        calc _ ≤ 2 * 2 := mul_le_mul hp ht' (norm_nonneg _) (by norm_num)
          _ = 4 := by norm_num
      refine ⟨hzs, ?_⟩
      rw [hFE]
      have hstep : ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) +
          Complex.log (2 * Real.pi) - Complex.digamma s +
          Real.pi / 2 * Complex.tan (Real.pi * s / 2)‖ ≤
          B * Real.log T ^ 2 + 2 + (K * Real.log (T + 3) + 2) + 4 := by
        have htri : ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) +
            Complex.log (2 * Real.pi) - Complex.digamma s +
            Real.pi / 2 * Complex.tan (Real.pi * s / 2)‖ ≤
            ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))‖ +
              ‖Complex.log (2 * Real.pi)‖ + ‖Complex.digamma s‖ +
              ‖Real.pi / 2 * Complex.tan (Real.pi * s / 2)‖ := by
          have h1 := norm_add_le (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) +
            Complex.log (2 * Real.pi) - Complex.digamma s)
            (Real.pi / 2 * Complex.tan (Real.pi * s / 2))
          have h2 := norm_sub_le (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) +
            Complex.log (2 * Real.pi)) (Complex.digamma s)
          have h3 := norm_add_le (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)))
            (Complex.log (2 * Real.pi))
          have h4' : (0:ℝ) ≤ ‖Complex.digamma s‖ := norm_nonneg _
          have h5' : (0:ℝ) ≤ ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))‖ := norm_nonneg _
          linarith
        have hn : ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))‖ ≤ B * Real.log T ^ 2 := by
          rw [norm_neg]; exact h1w
        have hl : ‖Complex.log (2 * Real.pi)‖ ≤ 2 :=
          LeanLab.PNTPort.ExplicitPsi1.Trivial.norm_log_two_pi_le
        linarith [htri, hn, hl, h3, h4]
      have hfin : B * Real.log T ^ 2 + 2 + (K * Real.log (T + 3) + 2) + 4 ≤
          (B + (2 * K + 8)) * Real.log T ^ 2 := by
        have hK1 : K * Real.log (T + 3) ≤ 2 * K * Real.log T := by
          have := mul_le_mul_of_nonneg_left hlog3 hK.le
          linarith
        have hLTle : Real.log T ≤ Real.log T ^ 2 := by nlinarith
        have hK2 : 2 * K * Real.log T ≤ 2 * K * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_left hLTle (by linarith : (0 : ℝ) ≤ 2 * K)
        nlinarith [hK1, hK2, hLT2, hB, hL2, hK]
      exact hstep.trans hfin
  intro σ hσ y hy
  rcases hy with rfl | rfl
  · simpa using hmain σ hσ
  · obtain ⟨h1, h2⟩ := hmain σ hσ
    have he : ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) =
        (starRingEnd ℂ) ((σ : ℂ) + (T : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    refine ⟨?_, ?_⟩
    · intro h
      rw [he, riemannZeta_conj] at h
      exact h1 (by simpa using h)
    · have hc := logDerivZeta_conj ((σ : ℂ) + (T : ℂ) * Complex.I)
      simp only [Pi.div_apply] at hc ⊢
      rw [he, hc, Complex.norm_conj]
      exact h2

/-- The change of `t ↦ t^ρ` over a short interval: `‖(n+δ)^ρ - n^ρ‖ ≤ ‖ρ‖ δ n^{Re ρ - 1}`
for `Re ρ ≤ 1` (mean value theorem). -/
private lemma cpow_sub_le {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) :
    ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ ρ - (n : ℂ) ^ ρ‖ ≤ ‖ρ‖ * δ * (n : ℝ) ^ (ρ.re - 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have ha : (0 : ℝ) ≤ -(ρ.re - 1) := by linarith
  have hbound : ∀ t ∈ Set.Ico (n : ℝ) ((n : ℝ) + δ),
      ‖ρ * ((t : ℂ)) ^ (ρ - 1)‖ ≤ ‖ρ‖ * (n : ℝ) ^ (ρ.re - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hn0 ht.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    have hmono : t ^ (ρ.re - 1) ≤ (n : ℝ) ^ (ρ.re - 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) ^ (-(ρ.re - 1)) := Real.rpow_pos_of_pos hn0 _
      rw [show ρ.re - 1 = -(-(ρ.re - 1)) by ring, Real.rpow_neg (le_of_lt ht0),
        Real.rpow_neg (le_of_lt hn0)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos ht0 _) hpos).mpr ?_
      exact Real.rpow_le_rpow (le_of_lt hn0) ht.1 ha
    have hpos2 : (0 : ℝ) ≤ t ^ (ρ.re - 1) := Real.rpow_nonneg (le_of_lt ht0) _
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg ρ)
  have hderiv : ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ) + δ),
      HasDerivWithinAt (fun u : ℝ => ((u : ℂ)) ^ ρ) (ρ * ((t : ℂ)) ^ (ρ - 1))
        (Set.Icc (n : ℝ) ((n : ℝ) + δ)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hn0 ht.1
    have hne : ρ ≠ 0 := by
      intro h
      rw [h] at hre0
      simp at hre0
    have hmem : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht0
    have h1 : HasDerivAt (fun z : ℂ => z ^ ρ) (ρ * (t : ℂ) ^ (ρ - 1) * 1) (t : ℂ) :=
      (hasDerivAt_id (t : ℂ)).cpow_const hmem
    have h2 : HasDerivAt (fun u : ℝ => ((u : ℂ)) ^ ρ) (ρ * (t : ℂ) ^ (ρ - 1) * 1) t :=
      h1.comp_ofReal
    have h3 : HasDerivAt (fun u : ℝ => ((u : ℂ)) ^ ρ) (ρ * (t : ℂ) ^ (ρ - 1)) t := by
      simpa using h2
    exact h3.hasDerivWithinAt
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => ((u : ℂ)) ^ ρ)
    (f' := fun t : ℝ => ρ * ((t : ℂ)) ^ (ρ - 1)) (C := ‖ρ‖ * (n : ℝ) ^ (ρ.re - 1))
    (a := (n : ℝ)) (b := (n : ℝ) + δ) hderiv hbound ((n : ℝ) + δ)
    (Set.right_mem_Icc.mpr (by linarith))
  have hdist : ((n : ℝ) + δ) - (n : ℝ) = δ := by ring
  rw [hdist] at hMVT
  calc ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ ρ - (n : ℂ) ^ ρ‖
      = ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ ρ - (((n : ℝ)) : ℂ) ^ ρ‖ := by norm_num
    _ ≤ ‖ρ‖ * (n : ℝ) ^ (ρ.re - 1) * δ := hMVT
    _ = ‖ρ‖ * δ * (n : ℝ) ^ (ρ.re - 1) := by ring

set_option maxHeartbeats 4000000 in
open LeanLab.BhowmikGrimmelt2026 in
/-- The leaf `principal_psi_zero_bound508` for the Riemann zeta function: for a height
`T ∈ [X, 2X]` and the zero list up to `T`, the truncated explicit formula at `n ≤ X` has error
`O((log X)²)`. -/
private theorem zeta_psi_zero_bound {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)),
      ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 1 ≤ n → n ≤ X →
        ‖(∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m : ℂ)) - (n : ℂ) +
          ∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨A, hA, hexp⟩ := explicit_gen508
  obtain ⟨Cg, hCg, hgood⟩ := LeanLab.PNTPort.ZetaZeros.good_height
  obtain ⟨Cr, hCr, hrecip⟩ := zero_recip_bound hΘ hZ
  obtain ⟨C1, hC1, hcount⟩ := LeanLab.PNTPort.ZetaZeros.zero_count_two
  obtain ⟨Cfib, hCfib, hfib⟩ := LeanLab.PNTPort.ExplicitPsi1.fiber_count
  obtain ⟨KK, hKK, hstripall⟩ := strip_all
  set Btot : ℝ := Cg + KK with hBtot
  have hBtot0 : 0 ≤ Btot := by rw [hBtot]; linarith
  set KC : ℝ := 3000 * (A * (1 + Btot) + Cr + C1 + Cfib + 1) with hKC
  have hKCpos : 0 < KC := by rw [hKC]; positivity
  refine ⟨KC, hKCpos.le, ?_⟩
  intro X hX T hT Z hZchar n hn1 hnX
  rw [Set.mem_Icc] at hT
  obtain ⟨hTX, hT2X⟩ := hT
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnRX : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogX2 : 0 ≤ Real.log X ^ 2 := sq_nonneg _
  have hlogXge : (0.48 : ℝ) < Real.log X ^ 2 := by
    have h2 := Real.log_two_gt_d9
    have hle : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
    nlinarith
  have hA0 : 0 < A := hA
  have hsub : (∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m : ℂ)) =
      ((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) := by
    rw [Chebyshev.psi_eq_sum_range, show ⌊(n : ℝ)⌋₊ = n from Nat.floor_natCast n]
    push_cast
    rfl
  rw [hsub]
  -- the leaf's zero list is the strip zero set at height `T`
  have hZC : (Z : Set ℂ) = zetaZeros T := by
    ext ρ
    rw [LeanLab.DERZ1997.Decomp1529a.zetaZeros]
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    exact hZchar ρ
  by_cases hmain : 5 ≤ T ∧ 3 ≤ n
  · -- the truncated explicit formula at a good height
    obtain ⟨hT5, hn3⟩ := hmain
    have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hX3 : (3 : ℝ) ≤ (X : ℝ) := le_trans hnR3 hnRX
    have hlogX1 : (1 : ℝ) ≤ Real.log X := by
      have h3 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX3
      have := Real.log_three_gt_d9
      linarith
    have hlogTle : Real.log T ≤ 2 * Real.log X := by
      have h2 : T ≤ 2 * (X : ℝ) := hT2X
      have hpos : (0 : ℝ) < T := by linarith
      calc Real.log T ≤ Real.log (2 * (X : ℝ)) := Real.log_le_log hpos h2
        _ = Real.log 2 + Real.log X := Real.log_mul (by norm_num) (by linarith)
        _ ≤ 2 * Real.log X := by
            have h2' : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
            linarith
    obtain ⟨H, hHI, hHg⟩ := hgood T hT5
    rw [Set.mem_Icc] at hHI
    obtain ⟨hHT, hHle⟩ := hHI
    have hH5 : 5 ≤ H := le_trans hT5 hHT
    have hH0 : (0 : ℝ) < H := by linarith
    have hHgeT : T ≤ H := hHT
    have hlogHge : Real.log T ≤ Real.log H := Real.log_le_log (by linarith) hHgeT
    have hlog0T : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hHg' : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
        riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) /
          riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))‖ ≤ Cg * Real.log H ^ 2 := by
      intro σ hσ
      obtain ⟨h1, h2⟩ := hHg σ hσ
      exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0T hlogHge 2) hCg.le)⟩
    have hstripH := hstripall H Cg hH5 hCg.le hHg'
    rw [show Cg + KK = Btot from (hBtot).symm] at hstripH
    obtain ⟨ZH, hZcharH⟩ := character_zero_finset504 (q := 1) (1 : DirichletCharacter ℂ 1) H
    have hZmemH : ∀ ρ : ℂ, ρ ∈ ZH ↔
        riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ H := by
      intro ρ
      rw [hZcharH]
      simp
    have hfinH : (zetaZeros H).Finite := LeanLab.DERZ1997.Decomp1529a.zetaZeros_finite H
    have hfinHtf : hfinH.toFinset = ZH := by
      ext ρ
      rw [Set.Finite.mem_toFinset]
      simp only [LeanLab.DERZ1997.Decomp1529a.zetaZeros, Set.mem_setOf_eq]
      exact (hZmemH ρ).symm
    have hZsub : Z ⊆ ZH := by
      intro ρ hρ
      rw [hZmemH]
      have hρ' : ρ ∈ zetaZeros T := by rw [← hZC]; exact hρ
      rw [LeanLab.DERZ1997.Decomp1529a.zetaZeros] at hρ'
      obtain ⟨h1, h2, h3, h4⟩ := hρ'
      exact ⟨h1, h2, h3, le_trans h4 hHT⟩
    set MH : ℝ := ∑ ρ ∈ ZH, ((zetaMult ρ : ℝ)) with hMH
    have hMH0 : 0 ≤ MH := Finset.sum_nonneg (fun _ _ => by positivity)
    -- structural equality of the leaf expression
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set δ : ℝ := min (1 / 2) (ε / (2 * (1 + (n : ℝ) ^ (Θ - 1) * MH))) with hδdef
    have hnpow : (0 : ℝ) < (n : ℝ) ^ (Θ - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hden : (0 : ℝ) < 2 * (1 + (n : ℝ) ^ (Θ - 1) * MH) := by
      have : 0 ≤ (n : ℝ) ^ (Θ - 1) * MH := mul_nonneg hnpow.le hMH0
      linarith
    have hδ0 : 0 < δ := by
      rw [hδdef]
      exact lt_min (by norm_num) (div_pos hε hden)
    have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
    have hδeps : δ ≤ ε / (2 * (1 + (n : ℝ) ^ (Θ - 1) * MH)) := min_le_right _ _
    have hδkey : δ * (1 + (n : ℝ) ^ (Θ - 1) * MH) ≤ ε / 2 := by
      have h1 : δ * (1 + (n : ℝ) ^ (Θ - 1) * MH) ≤
          (ε / (2 * (1 + (n : ℝ) ^ (Θ - 1) * MH))) * (1 + (n : ℝ) ^ (Θ - 1) * MH) := by
        apply mul_le_mul_of_nonneg_right hδeps
        have : 0 ≤ (n : ℝ) ^ (Θ - 1) * MH := mul_nonneg hnpow.le hMH0
        linarith
      have h2 : (ε / (2 * (1 + (n : ℝ) ^ (Θ - 1) * MH))) * (1 + (n : ℝ) ^ (Θ - 1) * MH) = ε / 2 := by
        field_simp
      linarith [h1, h2.le, h2.ge]
    have hx2 : (2 : ℝ) ≤ (n : ℝ) + δ := by linarith
    have hxnat : ∀ m : ℕ, (m : ℝ) ≠ (n : ℝ) + δ := by
      intro m hm
      rcases lt_trichotomy m n with hmn | hmn | hmn
      · have h1 : (m : ℝ) + 1 ≤ (n : ℝ) := by
          have : m + 1 ≤ n := by omega
          exact_mod_cast this
        linarith [hδ0]
      · subst hmn
        linarith [hδ0]
      · have h1 : (n : ℝ) + 1 ≤ (m : ℝ) := by
          have : n + 1 ≤ m := by omega
          exact_mod_cast this
        linarith [hδ0]
    have hpsi : Chebyshev.psi ((n : ℝ) + δ) = Chebyshev.psi (n : ℝ) := by
      rw [Chebyshev.psi_eq_sum_range, Chebyshev.psi_eq_sum_range]
      have hfl : ⌊(n : ℝ) + δ⌋₊ = n := by
        rw [Nat.floor_eq_iff (by linarith)]
        constructor
        · linarith
        · push_cast
          linarith
      rw [hfl, show ⌊(n : ℝ)⌋₊ = n from Nat.floor_natCast n]
    have hexpapp := hexp (x := (n : ℝ) + δ) (T := H) (B := Btot)
      (by linarith) hH5 hBtot0 hxnat hstripH hfinH
    rw [hfinHtf] at hexpapp
    -- the formula bound, in terms of `log X`
    have hc1 : (n : ℝ) + δ ≤ (X : ℝ) + 1 := by linarith
    have hxpos : (0 : ℝ) < (n : ℝ) + δ := by linarith
    have hHX : (X : ℝ) ≤ H := le_trans hTX hHT
    have hTH : T ≤ H := hHT
    have hlogH : Real.log H ≤ 2 * Real.log X := by
      have h2 : H ≤ 2 * (X : ℝ) + 1 := by linarith
      have h3 : 2 * (X : ℝ) + 1 ≤ (X : ℝ) ^ 2 := by nlinarith
      calc Real.log H ≤ Real.log ((X : ℝ) ^ 2) := Real.log_le_log hH0 (le_trans h2 h3)
        _ = 2 * Real.log X := by rw [Real.log_pow]; norm_num
    have hlogx : Real.log ((n : ℝ) + δ) ≤ 2 * Real.log X := by
      have h2 : (n : ℝ) + δ ≤ 2 * (X : ℝ) := by linarith
      calc Real.log ((n : ℝ) + δ) ≤ Real.log (2 * (X : ℝ)) :=
            Real.log_le_log hxpos h2
        _ = Real.log 2 + Real.log X := Real.log_mul (by norm_num) (by linarith)
        _ ≤ 2 * Real.log X := by
            have h2' : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
            linarith
    have hS1 : ‖(Chebyshev.psi ((n : ℝ) + δ) : ℂ) - (((n : ℝ) + δ : ℝ) : ℂ) +
        ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ‖ ≤
        (A * (1 + Btot) * 20) * Real.log X ^ 2 := by
      refine hexpapp.trans ?_
      have hY1 : ((n : ℝ) + δ) * Real.log ((n : ℝ) + δ) ^ 2 / H ≤ 8 * Real.log X ^ 2 := by
        have hl : Real.log ((n : ℝ) + δ) ^ 2 ≤ (2 * Real.log X) ^ 2 := by
          have h0 : 0 ≤ Real.log ((n : ℝ) + δ) := Real.log_nonneg (by linarith)
          exact pow_le_pow_left₀ h0 hlogx 2
        have hr : ((n : ℝ) + δ) / H ≤ 2 := by
          rw [div_le_iff₀ hH0]; linarith
        calc ((n : ℝ) + δ) * Real.log ((n : ℝ) + δ) ^ 2 / H
            = (((n : ℝ) + δ) / H) * Real.log ((n : ℝ) + δ) ^ 2 := by ring
          _ ≤ 2 * (2 * Real.log X) ^ 2 :=
              mul_le_mul hr hl (by positivity) (by norm_num)
          _ = 8 * Real.log X ^ 2 := by ring
      have hY2 : Real.log ((n : ℝ) + δ) ≤ 2 * Real.log X ^ 2 := by
        have h1 : Real.log X ≤ Real.log X ^ 2 := by nlinarith
        linarith
      have hY3 : ((n : ℝ) + δ) * Real.log H ^ 2 / H ≤ 8 * Real.log X ^ 2 := by
        have hl : Real.log H ^ 2 ≤ (2 * Real.log X) ^ 2 := by
          have h0 : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
          exact pow_le_pow_left₀ h0 hlogH 2
        have hr : ((n : ℝ) + δ) / H ≤ 2 := by
          rw [div_le_iff₀ hH0]; linarith
        calc ((n : ℝ) + δ) * Real.log H ^ 2 / H
            = (((n : ℝ) + δ) / H) * Real.log H ^ 2 := by ring
          _ ≤ 2 * (2 * Real.log X) ^ 2 :=
              mul_le_mul hr hl (by positivity) (by norm_num)
          _ = 8 * Real.log X ^ 2 := by ring
      have hsum3 : ((n : ℝ) + δ) * Real.log ((n : ℝ) + δ) ^ 2 / H +
          Real.log ((n : ℝ) + δ) + ((n : ℝ) + δ) * Real.log H ^ 2 / H ≤
          20 * Real.log X ^ 2 := by linarith
      have hAB : 0 ≤ A * (1 + Btot) := by positivity
      calc A * (1 + Btot) * (((n : ℝ) + δ) * Real.log ((n : ℝ) + δ) ^ 2 / H +
            Real.log ((n : ℝ) + δ) + ((n : ℝ) + δ) * Real.log H ^ 2 / H)
          ≤ A * (1 + Btot) * (20 * Real.log X ^ 2) := by
            apply mul_le_mul_of_nonneg_left hsum3 hAB
        _ = (A * (1 + Btot) * 20) * Real.log X ^ 2 := by ring
    -- the band between the two heights
    have hbandcount : ∀ s : Finset ℂ,
        (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ T < |ρ.im| ∧ |ρ.im| ≤ H) →
        ∑ ρ ∈ s, (zetaMult ρ : ℝ) ≤ 16 * Cfib * Real.log T := by
      intro s hs
      have hT0 : (0 : ℝ) ≤ T := by linarith
      have hceilpos : ((⌈T⌉₊ : ℝ)) - 1 < T := by
        have h := Nat.ceil_lt_add_one hT0
        have h2 : ((⌈T⌉₊ : ℝ)) < T + 1 := by exact_mod_cast h
        linarith
      have hTceil : T ≤ ((⌈T⌉₊ : ℝ)) := Nat.le_ceil T
      have hN1 : 5 ≤ ⌈T⌉₊ := by
        have h : ⌈(5 : ℝ)⌉₊ ≤ ⌈T⌉₊ := Nat.ceil_mono hT5
        simpa using h
      have hs1 : ∀ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ ((⌈T⌉₊ : ℝ))),
          riemannZeta ρ = 0 ∧ ((⌈T⌉₊ : ℝ)) - 1 < |ρ.im| ∧ |ρ.im| ≤ ((⌈T⌉₊ : ℝ)) := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρs, hle⟩ := hρ
        obtain ⟨hz, hlo, _⟩ := hs ρ hρs
        exact ⟨hz, lt_trans hceilpos hlo, hle⟩
      have hs2 : ∀ ρ ∈ s.filter (fun ρ => ¬ |ρ.im| ≤ ((⌈T⌉₊ : ℝ))),
          riemannZeta ρ = 0 ∧ ((⌈T⌉₊ + 1 : ℕ) : ℝ) - 1 < |ρ.im| ∧
            |ρ.im| ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ) := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρs, hgt⟩ := hρ
        obtain ⟨hz, _, hle⟩ := hs ρ hρs
        have hgt' : ((⌈T⌉₊ : ℝ)) < |ρ.im| := not_le.mp hgt
        refine ⟨hz, by push_cast; linarith, ?_⟩
        have h2 : H ≤ T + 1 := by linarith
        have h3 : T + 1 ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
        linarith
      have hc1 := hfib ⌈T⌉₊ hN1 _ hs1
      have hc2 := hfib (⌈T⌉₊ + 1) (by omega) _ hs2
      have hunion : s.filter (fun ρ => |ρ.im| ≤ ((⌈T⌉₊ : ℝ))) ∪
          s.filter (fun ρ => ¬ |ρ.im| ≤ ((⌈T⌉₊ : ℝ))) = s := by
        ext ρ
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hp : |ρ.im| ≤ ((⌈T⌉₊ : ℝ))
          · exact Or.inl ⟨h, hp⟩
          · exact Or.inr ⟨h, hp⟩
      have hdisj : Disjoint (s.filter (fun ρ => |ρ.im| ≤ ((⌈T⌉₊ : ℝ))))
          (s.filter (fun ρ => ¬ |ρ.im| ≤ ((⌈T⌉₊ : ℝ)))) := by
        rw [Finset.disjoint_left]
        intro a ha ha'
        rw [Finset.mem_filter] at ha ha'
        exact ha'.2 ha.2
      rw [← hunion, Finset.sum_union hdisj]
      have hl1 : Real.log ((⌈T⌉₊ : ℝ)) ≤ 2 * Real.log T := by
        have h2 : ((⌈T⌉₊ : ℝ)) ≤ T + 1 := by
          have h := Nat.ceil_lt_add_one hT0
          have h2 : ((⌈T⌉₊ : ℝ)) < T + 1 := by exact_mod_cast h
          linarith
        have h3 : T + 1 ≤ T ^ 2 := by nlinarith
        calc Real.log ((⌈T⌉₊ : ℝ)) ≤ Real.log (T ^ 2) :=
              Real.log_le_log (by linarith) (le_trans h2 h3)
          _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
      have hl2 : Real.log (((⌈T⌉₊ + 1 : ℕ) : ℝ)) ≤ 2 * Real.log T := by
        have hcast : (((⌈T⌉₊ + 1 : ℕ) : ℝ)) = ((⌈T⌉₊ : ℝ)) + 1 := by push_cast; ring
        rw [hcast]
        have h2 : ((⌈T⌉₊ : ℝ)) + 1 ≤ T + 2 := by
          have hh : ((⌈T⌉₊ : ℝ)) < T + 1 := by exact_mod_cast Nat.ceil_lt_add_one hT0
          linarith
        have h3 : T + 2 ≤ T ^ 2 := by nlinarith
        calc Real.log (((⌈T⌉₊ : ℝ)) + 1) ≤ Real.log (T ^ 2) :=
              Real.log_le_log (by linarith) (le_trans h2 h3)
          _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
      have hlogT1 : (1 : ℝ) ≤ Real.log T := by
        have h2 : Real.exp 1 ≤ T := by
          have := Real.exp_one_lt_d9
          linarith
        rw [Real.le_log_iff_exp_le (by linarith)]
        linarith
      have hc1' : ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ ((⌈T⌉₊ : ℝ))),
          (zetaMult ρ : ℝ) ≤ 8 * Cfib * Real.log T := by
        refine le_trans hc1 ?_
        calc 4 * Cfib * Real.log ((⌈T⌉₊ : ℝ))
            ≤ 4 * Cfib * (2 * Real.log T) := by
              apply mul_le_mul_of_nonneg_left hl1; positivity
          _ = 8 * Cfib * Real.log T := by ring
      have hc2' : ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.im| ≤ ((⌈T⌉₊ : ℝ))),
          (zetaMult ρ : ℝ) ≤ 8 * Cfib * Real.log T := by
        refine le_trans hc2 ?_
        calc 4 * Cfib * Real.log ((⌈T⌉₊ + 1 : ℕ) : ℝ)
            ≤ 4 * Cfib * (2 * Real.log T) := by
              apply mul_le_mul_of_nonneg_left hl2; positivity
          _ = 8 * Cfib * Real.log T := by ring
      linarith [hc1', hc2']
    have hband : ‖∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
        ∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ 16 * Cfib * Real.log T := by
      have hsd : ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ +
          ∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ =
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ :=
        Finset.sum_sdiff hZsub
      rw [← hsd, add_sub_cancel_right]
      have hsub : ∀ ρ ∈ ZH \ Z, riemannZeta ρ = 0 ∧ T < |ρ.im| ∧ |ρ.im| ≤ H := by
        intro ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨hρH, hρZ⟩ := hρ
        obtain ⟨hz, h0, h1, him⟩ := (hZmemH ρ).mp hρH
        have hTlt : T < |ρ.im| := by
          by_contra hcon
          exact hρZ (by rw [hZchar ρ]; exact ⟨hz, h0, h1, not_lt.mp hcon⟩)
        exact ⟨hz, hTlt, him⟩
      have hcount' := hbandcount _ hsub
      have hperp : ∀ ρ ∈ ZH \ Z,
          ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) * 1 := by
        intro ρ hρ
        have hsubρ := hsub ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨hρH, hρZ'⟩ := hρ
        obtain ⟨hz, h0, h1, him⟩ := (hZmemH ρ).mp hρH
        obtain ⟨_, hTlt, _⟩ := hsubρ
        have hrele : ρ.re ≤ Θ := hZ 1 (1 : DirichletCharacter ℂ 1) ρ (by simpa using hz) h0 h1
        have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
        have hnorm : ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ (ρ.re) := by
          have h := Complex.norm_cpow_eq_rpow_re_of_pos hn0 ρ
          simpa using h
        have hrho : (0 : ℝ) < ‖ρ‖ := by
          by_contra hcon
          have hz0 : ‖ρ‖ = 0 := le_antisymm (le_of_not_gt hcon) (norm_nonneg _)
          have : ρ = 0 := norm_eq_zero.mp hz0
          rw [this] at h0
          simp at h0
        have h1' : ‖ρ‖ > T := lt_of_lt_of_le hTlt (Complex.abs_im_le_norm ρ)
        rw [norm_div, norm_mul, hnorm, Complex.norm_natCast]
        have hpow : (n : ℝ) ^ (ρ.re) ≤ (X : ℝ) ^ Θ := by
          have h1 : (n : ℝ) ^ (ρ.re) ≤ (n : ℝ) ^ Θ :=
            Real.rpow_le_rpow_of_exponent_le hnR1 hrele
          have h2 : (n : ℝ) ^ Θ ≤ (X : ℝ) ^ Θ := Real.rpow_le_rpow (by linarith) hnRX (by linarith)
          linarith
        have h2' : ((zetaMult ρ : ℝ) * (n : ℝ) ^ ρ.re) / ‖ρ‖ ≤
            (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) := by
          have h3 : ((zetaMult ρ : ℝ)) * (n : ℝ) ^ ρ.re ≤ ((zetaMult ρ : ℝ)) * (X : ℝ) ^ Θ :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          have hTpos : (0 : ℝ) < T := by linarith
          have hTR : (1 : ℝ) ≤ ‖ρ‖ / T := (le_div_iff₀ hTpos).mpr (by simpa using h1'.le)
          have hB0 : (0 : ℝ) ≤ (X : ℝ) ^ Θ := Real.rpow_nonneg (by linarith) Θ
          have hz0 : (0 : ℝ) ≤ (zetaMult ρ : ℝ) := by positivity
          have hnn : (0 : ℝ) ≤ (zetaMult ρ : ℝ) * (X : ℝ) ^ Θ := mul_nonneg hz0 hB0
          have hmono : (zetaMult ρ : ℝ) * (X : ℝ) ^ Θ ≤
              ((zetaMult ρ : ℝ) * (X : ℝ) ^ Θ) * (‖ρ‖ / T) := by
            have : ((zetaMult ρ : ℝ) * (X : ℝ) ^ Θ) * 1 ≤
                ((zetaMult ρ : ℝ) * (X : ℝ) ^ Θ) * (‖ρ‖ / T) :=
              mul_le_mul_of_nonneg_left hTR hnn
            simpa using this
          have he : (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) * ‖ρ‖ =
              ((zetaMult ρ : ℝ) * (X : ℝ) ^ Θ) * (‖ρ‖ / T) := by ring
          rw [div_le_iff₀ hrho, he]
          exact le_trans h3 hmono
        calc ((zetaMult ρ : ℝ)) * (n : ℝ) ^ ρ.re / ‖ρ‖
            ≤ (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) := h2'
          _ = (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) * 1 := by ring
      have hsumperp : ∑ ρ ∈ ZH \ Z, ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
          ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) * 1 :=
        Finset.sum_le_sum hperp
      have hfac : ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) * 1 =
          ((X : ℝ) ^ Θ / T) * ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ _
        ring
      have hfac1 : (X : ℝ) ^ Θ / T ≤ 1 := by
        rw [div_le_one (by linarith)]
        have hle : (X : ℝ) ^ Θ ≤ (X : ℝ) := by
          calc (X : ℝ) ^ Θ ≤ (X : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = (X : ℝ) := Real.rpow_one _
        exact hle.trans hTX
      calc ‖∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖
          ≤ ∑ ρ ∈ ZH \ Z, ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℝ) * ((X : ℝ) ^ Θ / T) * 1 := hsumperp
        _ = ((X : ℝ) ^ Θ / T) * ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℝ) := hfac
        _ ≤ 1 * ∑ ρ ∈ ZH \ Z, (zetaMult ρ : ℝ) := by
            apply mul_le_mul_of_nonneg_right hfac1
            exact Finset.sum_nonneg (fun _ _ => by positivity)
        _ ≤ 16 * Cfib * Real.log T := by
            rw [one_mul]; exact hcount'
    -- the base change
    have hbase : ‖∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
        ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ‖ ≤
        δ * (n : ℝ) ^ (Θ - 1) * MH := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ ρ ∈ ZH, ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ‖ ≤
          (zetaMult ρ : ℝ) * (δ * (n : ℝ) ^ (Θ - 1)) := by
        intro ρ hρ
        obtain ⟨hz, h0, h1, him⟩ := (hZmemH ρ).mp hρ
        have hrele : ρ.re ≤ Θ := hZ 1 (1 : DirichletCharacter ℂ 1) ρ (by simpa using hz) h0 h1
        have hre1 : ρ.re ≤ 1 := le_trans hrele (by linarith)
        have hcp := cpow_sub_le h0 hre1 hn1 hδ0
        have hrho : (0 : ℝ) < ‖ρ‖ := by
          by_contra hcon
          have hz0 : ‖ρ‖ = 0 := le_antisymm (le_of_not_gt hcon) (norm_nonneg _)
          have : ρ = 0 := norm_eq_zero.mp hz0
          rw [this] at h0
          simp at h0
        have hkey : (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
            (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ =
            ((zetaMult ρ : ℂ) / ρ) * ((n : ℂ) ^ ρ - ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ) := by
          field_simp
          try ring
        rw [hkey, norm_mul, norm_div, Complex.norm_natCast]
        have hpowle : (n : ℝ) ^ (ρ.re - 1) ≤ (n : ℝ) ^ (Θ - 1) :=
          Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
        have h1' : ‖(n : ℂ) ^ ρ - ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ‖ ≤
            ‖ρ‖ * δ * (n : ℝ) ^ (Θ - 1) := by
          have hxx : ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ ρ - (n : ℂ) ^ ρ‖ ≤
              ‖ρ‖ * δ * (n : ℝ) ^ (ρ.re - 1) := hcp
          calc ‖(n : ℂ) ^ ρ - ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ‖
              = ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ ρ - (n : ℂ) ^ ρ‖ := norm_sub_rev _ _
            _ ≤ ‖ρ‖ * δ * (n : ℝ) ^ (ρ.re - 1) := hxx
            _ ≤ ‖ρ‖ * δ * (n : ℝ) ^ (Θ - 1) := by
                apply mul_le_mul_of_nonneg_left hpowle
                positivity
        calc ((zetaMult ρ : ℝ) / ‖ρ‖) *
              ‖(n : ℂ) ^ ρ - ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ‖
            ≤ ((zetaMult ρ : ℝ) / ‖ρ‖) * (‖ρ‖ * δ * (n : ℝ) ^ (Θ - 1)) := by
              apply mul_le_mul _ h1' (norm_nonneg _) (by positivity)
              exact le_refl _
          _ = (zetaMult ρ : ℝ) * (δ * (n : ℝ) ^ (Θ - 1)) := by
              field_simp
      calc ‖∑ ρ ∈ ZH, ((zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
            (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ)‖
          ≤ ∑ ρ ∈ ZH, ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
            (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ ZH, (zetaMult ρ : ℝ) * (δ * (n : ℝ) ^ (Θ - 1)) := Finset.sum_le_sum hterm
        _ = δ * (n : ℝ) ^ (Θ - 1) * MH := by
            rw [hMH, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ρ _
            ring
    -- assemble
    have hdecomp : ((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ) +
        ∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ =
        ((Chebyshev.psi ((n : ℝ) + δ) : ℝ) : ℂ) - (((n : ℝ) + δ : ℝ) : ℂ) +
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ +
        (δ : ℂ) + (∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ) +
        (∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ) := by
      rw [hpsi]
      push_cast
      ring
    rw [hdecomp]
    have hlogx2 : Real.log X ^ 2 ≤ 2 * Real.log X ^ 2 := by linarith
    have ht1 : ‖(δ : ℂ)‖ = δ := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    have htri : ‖((Chebyshev.psi ((n : ℝ) + δ) : ℝ) : ℂ) - (((n : ℝ) + δ : ℝ) : ℂ) +
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ +
        (δ : ℂ) + (∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ) +
        (∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ)‖ ≤
        (A * (1 + Btot) * 20) * Real.log X ^ 2 + δ + 16 * Cfib * Real.log T +
          δ * (n : ℝ) ^ (Θ - 1) * MH := by
      have h1 := norm_add_le (((Chebyshev.psi ((n : ℝ) + δ) : ℝ) : ℂ) - (((n : ℝ) + δ : ℝ) : ℂ) +
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ + (δ : ℂ) +
          (∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
            ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ))
        (∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ)
      have h2 := norm_add_le (((Chebyshev.psi ((n : ℝ) + δ) : ℝ) : ℂ) - (((n : ℝ) + δ : ℝ) : ℂ) +
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ + (δ : ℂ))
        (∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ)
      have h3 := norm_add_le (((Chebyshev.psi ((n : ℝ) + δ) : ℝ) : ℂ) - (((n : ℝ) + δ : ℝ) : ℂ) +
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ) (δ : ℂ)
      have h4 : (0:ℝ) ≤ ‖(∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ)‖ := norm_nonneg _
      have h5 : (0:ℝ) ≤ ‖(∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * ((((n : ℝ) + δ : ℝ)) : ℂ) ^ ρ / ρ)‖ := norm_nonneg _
      have h6 : (0:ℝ) ≤ ‖(δ : ℂ)‖ := norm_nonneg _
      have hband' : ‖(∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
          ∑ ρ ∈ ZH, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ 16 * Cfib * Real.log T := by
        rw [norm_sub_rev]; exact hband
      linarith [h1, h2, h3, h4, h5, h6, ht1, hS1, hband', hbase]
    have hlogT1 : (1 : ℝ) ≤ Real.log T := by
      have h2 : Real.exp 1 ≤ T := by
        have := Real.exp_one_lt_d9
        linarith
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith
    have hTlog : 16 * Cfib * Real.log T ≤ 32 * Cfib * Real.log X ^ 2 := by
      have h1 : Real.log T ≤ 2 * Real.log X := hlogTle
      have h2 : Real.log X ≤ Real.log X ^ 2 := by nlinarith
      nlinarith [hCfib, hlogT1, h1, h2]
    have hKCbig : (A * (1 + Btot) * 20) * Real.log X ^ 2 + 16 * Cfib * Real.log T ≤
        (1000 * (A * (1 + Btot)) + 32 * Cfib) * Real.log X ^ 2 := by
      have hP0 : 0 ≤ A * (1 + Btot) := by positivity
      have hPL : 0 ≤ A * (1 + Btot) * Real.log X ^ 2 := mul_nonneg hP0 hlogX2
      nlinarith [hPL, hTlog]
    have hdels : δ ≤ ε / 2 := by
      have h : 1 ≤ 1 + (n : ℝ) ^ (Θ - 1) * MH := by
        have : 0 ≤ (n : ℝ) ^ (Θ - 1) * MH := mul_nonneg hnpow.le hMH0
        linarith
      nlinarith [hδkey, hδ0, h]
    have hdelta : δ * (n : ℝ) ^ (Θ - 1) * MH ≤ ε / 2 := by
      have h : δ * ((n : ℝ) ^ (Θ - 1) * MH) ≤ ε / 2 := by
        nlinarith [hδkey, hMH0, hnpow.le]
      linarith [h]
    have hfinal : (A * (1 + Btot) * 20) * Real.log X ^ 2 + δ + 16 * Cfib * Real.log T +
        δ * (n : ℝ) ^ (Θ - 1) * MH ≤ KC * Real.log X ^ 2 + ε := by
      rw [hKC]
      have hA0 : 0 ≤ A * (1 + Btot) := by positivity
      have hCfib0 : 0 ≤ Cfib := hCfib.le
      nlinarith [hKCbig, hdels, hdelta, hlogX2, hlogXge, hA0, hCfib0]
    exact htri.trans hfinal
  · -- the crude case: `n ≤ 4`, and the zero sum is bounded by the reciprocal sum
    have hn4 : n ≤ 4 := by
      rcases not_and_or.mp hmain with h | h
      · have hlt : T < 5 := not_le.mp h
        have hX4 : X ≤ 4 := by
          have h1 : (X : ℝ) ≤ T := hTX
          have h2 : (X : ℝ) < 5 := by linarith
          by_contra hcon
          push_neg at hcon
          have h3 : (5 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcon
          linarith
        omega
      · omega
    have hnR4 : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hfinT : (zetaZeros T).Finite := LeanLab.DERZ1997.Decomp1529a.zetaZeros_finite T
    have hZtf : hfinT.toFinset = Z := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset, ← hZC]
    have hpow4 : (4 : ℝ) ^ Θ ≤ 4 := by
      have h1 : (4 : ℝ) ^ Θ ≤ (4 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : Θ ≤ 1)
      rwa [Real.rpow_one] at h1
    have hZrec : ∑ ρ ∈ Z, ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
        4 * (Cr * (1 + Real.log (T + 2) ^ 2)) := by
      rw [← hZtf]
      have hsZ : ∀ ρ ∈ hfinT.toFinset,
          riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
        intro ρ hρ
        rw [Set.Finite.mem_toFinset] at hρ
        exact hρ
      calc ∑ ρ ∈ hfinT.toFinset, ‖(zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖
          ≤ ∑ ρ ∈ hfinT.toFinset, (4 * ((zetaMult ρ : ℝ) / ‖ρ‖)) := by
            apply Finset.sum_le_sum
            intro ρ hρ
            obtain ⟨hz, h0, h1, him⟩ := hsZ ρ hρ
            have hrele : ρ.re ≤ Θ := hZ 1 (1 : DirichletCharacter ℂ 1) ρ (by simpa using hz) h0 h1
            have hrho : (0 : ℝ) < ‖ρ‖ := by
              by_contra hcon
              have hz0 : ‖ρ‖ = 0 := le_antisymm (le_of_not_gt hcon) (norm_nonneg _)
              have hzero : ρ = 0 := norm_eq_zero.mp hz0
              rw [hzero] at h0
              simp at h0
            have hnorm : ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ (ρ.re) := by
              have h := Complex.norm_cpow_eq_rpow_re_of_pos hnpos ρ
              simpa using h
            rw [norm_div, norm_mul, hnorm, Complex.norm_natCast]
            have hpow : (n : ℝ) ^ (ρ.re) ≤ 4 := by
              have hre34 : ρ.re ≤ 3 / 4 := by linarith
              have hA : (n : ℝ) ^ (ρ.re) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) :=
                Real.rpow_le_rpow_of_exponent_le hnR1 hre34
              have hB : (n : ℝ) ^ ((3 : ℝ) / 4) ≤ (4 : ℝ) ^ ((3 : ℝ) / 4) :=
                Real.rpow_le_rpow (le_of_lt hnpos) hnR4 (by norm_num)
              have hC : (4 : ℝ) ^ ((3 : ℝ) / 4) ≤ (4 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              have hD : (4 : ℝ) ^ (1 : ℝ) = 4 := Real.rpow_one 4
              linarith
            have hstep : ((zetaMult ρ : ℝ)) * (n : ℝ) ^ ρ.re / ‖ρ‖ ≤
                (4 * ((zetaMult ρ : ℝ) / ‖ρ‖)) := by
              rw [show (4 * ((zetaMult ρ : ℝ) / ‖ρ‖)) =
                ((zetaMult ρ : ℝ) * 4) / ‖ρ‖ by ring]
              apply div_le_div_of_nonneg_right _ hrho.le
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
            exact hstep
        _ = 4 * ∑ ρ ∈ hfinT.toFinset, ((zetaMult ρ : ℝ) / ‖ρ‖) := by
            rw [Finset.mul_sum]
        _ ≤ 4 * (Cr * (1 + Real.log (T + 2) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left (hrecip T (by linarith) hfinT) (by norm_num)
    have hpsi10 : Chebyshev.psi (n : ℝ) ≤ 10 := by
      rw [Chebyshev.psi_eq_sum_Icc, show ⌊(n : ℝ)⌋₊ = n from Nat.floor_natCast n]
      have hle : ∑ m ∈ Finset.Icc 0 n, ArithmeticFunction.vonMangoldt m ≤
          ∑ m ∈ Finset.Icc 0 4, ArithmeticFunction.vonMangoldt m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Icc] at hm ⊢
          omega
        · intro i _ _; exact ArithmeticFunction.vonMangoldt_nonneg
      have h2 : ∑ m ∈ Finset.Icc 0 4, ArithmeticFunction.vonMangoldt m ≤ 10 := by
        have hterm : ∀ m ∈ Finset.Icc 0 4, ArithmeticFunction.vonMangoldt m ≤ 2 := by
          intro m hm
          have hmle : m ≤ 4 := (Finset.mem_Icc.mp hm).2
          have h1 : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log
          have h2 : Real.log (m : ℝ) ≤ 2 := by
            rcases Nat.eq_zero_or_pos m with hm0 | hm0
            · subst hm0; simp
            · have hm1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
              have hm4 : (m : ℝ) ≤ 4 := by exact_mod_cast hmle
              have h3 : Real.log (m : ℝ) ≤ Real.log 4 := Real.log_le_log hm1 hm4
              have h4 : Real.log 4 < 2 := by
                have h5 : Real.log 4 = 2 * Real.log 2 := by
                  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
                have h6 := Real.log_two_lt_d9
                linarith
              linarith
          linarith
        calc ∑ m ∈ Finset.Icc 0 4, ArithmeticFunction.vonMangoldt m ≤
              ∑ _m ∈ Finset.Icc 0 4, (2 : ℝ) := Finset.sum_le_sum hterm
          _ = 10 := by norm_num
      linarith
    have hlogbound : 1 + Real.log (T + 2) ^ 2 ≤ 9 * (1 + Real.log X ^ 2) := by
      have hpos : (0 : ℝ) < T + 2 := by linarith
      have h2 : T + 2 ≤ 2 * (X : ℝ) + 2 := by linarith
      have h3 : 2 * (X : ℝ) + 2 ≤ (X : ℝ) ^ 3 := by
        have h1 : (2 : ℝ) ≤ (X : ℝ) := hX2
        nlinarith [h1, sq_nonneg ((X : ℝ) - 2), mul_nonneg (by linarith : (0:ℝ) ≤ (X:ℝ))
          (sq_nonneg ((X : ℝ) - 2))]
      have h1 : Real.log (T + 2) ≤ 3 * Real.log X := by
        have h4 : Real.log (T + 2) ≤ Real.log ((X : ℝ) ^ 3) :=
          Real.log_le_log hpos (le_trans h2 h3)
        have h5 : Real.log ((X : ℝ) ^ 3) = 3 * Real.log X := by
          rw [Real.log_pow]; norm_num
        rw [h5] at h4
        linarith
      have h0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
      have hLX : 0 ≤ Real.log X := hlogX0
      nlinarith [h1, h0, hLX, sq_nonneg (Real.log X)]
    have htri : ‖((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ) +
        ∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
        14 + 4 * (Cr * (1 + Real.log (T + 2) ^ 2)) := by
      have h1 : ‖((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ)‖ ≤ 14 := by
        have he : ((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ) =
            ((Chebyshev.psi (n : ℝ) - (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
        rw [he, Complex.norm_real, Real.norm_eq_abs]
        have h2 : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ |Chebyshev.psi (n : ℝ)| + |(n : ℝ)| :=
          abs_sub _ _
        have h3 : |Chebyshev.psi (n : ℝ)| ≤ 10 := by
          rw [abs_of_nonneg (Chebyshev.psi_nonneg _)]; exact hpsi10
        have h4 : |(n : ℝ)| = (n : ℝ) := abs_of_pos hnpos
        rw [h4] at h2
        linarith
      have h2 : ‖∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
          4 * (Cr * (1 + Real.log (T + 2) ^ 2)) :=
        (norm_sum_le _ _).trans hZrec
      have := norm_add_le (((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ))
        (∑ ρ ∈ Z, (zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ)
      linarith [this, h1, h2]
    have hfin2 : 14 + 4 * (Cr * (1 + Real.log (T + 2) ^ 2)) ≤ KC * Real.log X ^ 2 := by
      rw [hKC]
      have hCr0 : 0 ≤ Cr := hCr.le
      have hL0 : (0 : ℝ) ≤ Real.log X ^ 2 := by linarith
      have hL48 : (0.48 : ℝ) ≤ Real.log X ^ 2 := by linarith
      have hAB0 : (0 : ℝ) ≤ A * (1 + Btot) := by positivity
      have hABL : (0 : ℝ) ≤ A * (1 + Btot) * Real.log X ^ 2 := mul_nonneg hAB0 hL0
      have hC1L : (0 : ℝ) ≤ C1 * Real.log X ^ 2 := mul_nonneg hC1.le hL0
      have hCfibL : (0 : ℝ) ≤ Cfib * Real.log X ^ 2 := mul_nonneg hCfib.le hL0
      have hCrL : (0 : ℝ) ≤ Cr * Real.log X ^ 2 := mul_nonneg hCr0 hL0
      have hLsq : (0 : ℝ) ≤ Real.log X ^ 2 * Real.log X ^ 2 := mul_nonneg hL0 hL0
      nlinarith [hlogbound, hL48, hCr0, hL0, hABL, hC1L, hCfibL, hCrL, hLsq]
    exact htri.trans hfin2

open LeanLab.BhowmikGrimmelt2026 in
/-- `χ = 1` primitive forces `q = 1`; there the statement is the zeta case, the `L`-function being
`riemannZeta` and the multiplicities agreeing. -/
private theorem principal_from_zeta {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ = 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) - (n : ℂ) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, hC, hzeta⟩ := zeta_psi_zero_bound hΘ hZ
  refine ⟨C, hC, ?_⟩
  intro X hX q _ hqQ χ hprim hχ1 T hT Z hZchar n hn1 hnX
  have hq1 : q = 1 := by
    have h := (DirichletCharacter.isPrimitive_def χ).mp hprim
    rw [hχ1, DirichletCharacter.conductor_one] at h
    exact h.symm
  subst hq1
  subst hχ1
  have hone : ∀ x : ZMod 1, IsUnit x := fun x => by
    rw [Subsingleton.elim x 1]
    exact isUnit_one
  have hsum : (∑ m ∈ Finset.range (n + 1),
      (ArithmeticFunction.vonMangoldt m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1)) =
      ∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m : ℂ) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [MulChar.one_apply (hone _), mul_one]
  have hmult : ∀ ρ : ℂ, mult (1 : DirichletCharacter ℂ 1) ρ =
      LeanLab.DERZ1997.Decomp1529a.zetaMult ρ := by
    intro ρ
    unfold mult LeanLab.DERZ1997.Decomp1529a.zetaMult
    rw [DirichletCharacter.LFunction_modOne_eq]
  have hZchar' : ∀ ρ : ℂ, ρ ∈ Z ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
    intro ρ
    rw [hZchar ρ]
    simp only [DirichletCharacter.LFunction_modOne_eq]
  have hsum2 : (∑ ρ ∈ Z, (mult (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (n : ℂ) ^ ρ / ρ) =
      ∑ ρ ∈ Z, (LeanLab.DERZ1997.Decomp1529a.zetaMult ρ : ℂ) * (n : ℂ) ^ ρ / ρ := by
    apply Finset.sum_congr rfl
    intro ρ _
    rw [hmult ρ]
  rw [hsum, hsum2]
  exact hzeta X hX T hT Z hZchar' n hn1 hnX

end PrimitivePsiZeroAux508

/-- Step 3, the proved error estimate for the trivial character: for `χ = 1` primitive, a
height `T` of the size of `X` and the zero list `Z` up to that height, the twisted von
Mangoldt sum up to `n` minus `n` plus the zero sum `∑ ρ ∈ Z, mult χ ρ * n ^ ρ / ρ` has size at
most `C * (log X)²`, again with a constant independent of everything but the hypothesis on the
zeros. The main term of the explicit formula is `n` here, which is the whole difference from
step 2: the leaf takes `T` and `Z` as given instead of producing them. -/
theorem principal_psi_zero_bound508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ = 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) - (n : ℂ) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  exact principal_from_zeta hΘ hZ

end LeanLab.BhowmikGrimmelt2026
