module

public import Mathlib

/-!
# Ramaré-Saouter 2003, cited parts of Theorem 4

Theorem 4 of Ramaré-Saouter 2003, stated as `Theorem4Fm` in `Theorem3Smooth.lean`, is proved in
the paper from five inputs: RH verified to height `T0`, Lemma 1 for `N(T)` from Rosser,
the explicit formula Lemma 4, the Brun-Titchmarsh inequality of Montgomery and Vaughan through
Lemma 5, and Schoenfeld's `ψ - θ` bounds (11) through the step (12).

This file proves the two prime-counting steps outright from their named cited inputs:

* `lemma5`, Lemma 5 as printed on p. 16, conditional on `MVBrunTitchmarsh`, Montgomery and
  Vaughan 1973 Theorem 2. The printed statement needs the extra hypothesis `1 < u X`: for
  `0 < u X ≤ 1` the right side is not positive while the left side is `log p` whenever the
  short interval holds a prime `p`. In Theorem 4, `u √Y ≥ α2 ≥ 1`, so `u X` is huge and the
  gap is harmless.
* `step12`, the pointwise inequality before (12) on p. 19, conditional on `SchoenfeldPT` with
  any constants `cl`, `cu` satisfying `1.0001006 cu - cl ≤ 0.0028`; the printed constants
  `0.998697`, `1.001093` of (11) satisfy it, `step12_printed`.
* `step10` and `step10_alpha4`, the inequality (10) on p. 18, conditional on `MVBrunTitchmarsh`,
  for any continuous `f ≥ 0` on `[0, 1]`. `bound_alpha4`, Proved outright, replaces the paper's
  `log X/log(uX) ≤ log Y/log(uY)`, which is reversed, by the bound actually needed.

AI wrote the Lean code.
-/

@[expose] public section


namespace LeanLab.RamareSaouter2003.Thm4Parts

open Real Chebyshev Finset

/-- **Montgomery-Vaughan 1973, Theorem 2.** For real `x > 0` and `y > 1`, the number of primes
in `]x, x + y]` is less than `2 y / log y`. A cited input, not proved here. -/
def MVBrunTitchmarsh : Prop :=
  ∀ x y : ℝ, 0 < x → 1 < y →
    ((((Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℕ) : ℝ) < 2 * y / Real.log y

/-- **Schoenfeld's bounds (11)**, with constants `cl` and `cu`:
`ψ(Z) - θ(Z) ≥ cl √Z` for `Z ≥ 121` and `ψ(Z) - θ(Z) ≤ cu √Z + 3 Z^(1/3)` for `Z > 0`.
A cited input, not proved here; the paper uses `cl = 0.998697`, `cu = 1.001093`. -/
def SchoenfeldPT (cl cu : ℝ) : Prop :=
  (∀ Z : ℝ, 121 ≤ Z → cl * √Z ≤ ψ Z - θ Z) ∧
    (∀ Z : ℝ, 0 < Z → ψ Z - θ Z ≤ cu * √Z + 3 * Z ^ (1 / 3 : ℝ))

/-- `θ z - θ x` is the sum of `log p` over the primes in `]⌊x⌋, ⌊z⌋]`. -/
theorem theta_sub_eq {x z : ℝ} (hxz : x ≤ z) :
    θ z - θ x = ∑ p ∈ (Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log p := by
  have hf : ⌊x⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono hxz
  simp only [theta, sum_filter]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hf]
  ring

/-- `θ z - θ x ≤ (number of primes in ]⌊x⌋, ⌊z⌋]) · log z`. -/
theorem theta_sub_le {x z : ℝ} (hxz : x ≤ z) (hz : 1 ≤ z) :
    θ z - θ x ≤ (((Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime).card : ℝ) * Real.log z := by
  rw [theta_sub_eq hxz]
  have : ∀ p ∈ (Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log p ≤ Real.log z := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have hpz : (p : ℝ) ≤ z := by
      have := Nat.floor_le (show (0 : ℝ) ≤ z by linarith)
      have h2 : (p : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hp.1.2
      linarith
    exact Real.log_le_log (by linarith) hpz
  calc ∑ p ∈ (Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log p
      ≤ ∑ _p ∈ (Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log z := sum_le_sum this
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- `e^u - 1 ≤ u + 0.75 u²` for `0 ≤ u ≤ 1`. -/
theorem exp_sub_one_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : Real.exp u - 1 ≤ u + 0.75 * u ^ 2 := by
  have := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at this
  norm_num at this
  linarith

theorem log_ge_five {X : ℝ} (hX : 10 ^ 12 ≤ X) : 5 ≤ Real.log X := by
  have he : Real.exp 5 ≤ X := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    have : Real.exp 1 ^ 5 ≤ 2.7182818286 ^ 5 := pow_le_pow_left₀ h0 h1.le 5
    linarith [show (2.7182818286 : ℝ) ^ 5 ≤ 10 ^ 12 by norm_num]
  calc (5 : ℝ) = Real.log (Real.exp 5) := (Real.log_exp 5).symm
    _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 5) he

/-- **Lemma 5 of Ramaré-Saouter 2003**, as printed on p. 16, plus the hypothesis `1 < u X`
which the printed statement lacks but needs. Proved conditional on `MVBrunTitchmarsh`.
The proof is shorter than the printed chain: `log (e^u - 1) ≥ log u` replaces the step with
`1.00005`, and `e^u - 1 ≤ u + 0.75 u²` gives the room for `Y ≤ 1.0001 X`. -/
theorem lemma5 (hMV : MVBrunTitchmarsh) {X u δ t : ℝ} (hX : 10 ^ 12 ≤ X) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 0.0001) (hu0 : 0 < u) (hu : u ≤ 0.0001) (huX : 1 < u * X)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    θ (X * Real.exp u * (1 + δ * t)) - θ (X * (1 + δ * t)) ≤
      2.0004 * u * X * (Real.log X / Real.log (u * X)) := by
  set Y := X * (1 + δ * t) with hYdef
  have hXpos : 0 < X := by linarith
  have hdt0 : 0 ≤ δ * t := mul_nonneg hδ0 ht0
  have hdt1 : δ * t ≤ 0.0001 := by nlinarith
  have hY1 : X ≤ Y := by nlinarith
  have hY2 : Y ≤ 1.0001 * X := by nlinarith
  have hYpos : 0 < Y := by linarith
  set E := Real.exp u - 1 with hEdef
  have hE1 : u ≤ E := by have := Real.add_one_le_exp u; linarith
  have hE2 : E ≤ u + 0.75 * u ^ 2 := exp_sub_one_le hu0.le (by linarith)
  have hE3 : E ≤ 1.000075 * u := by nlinarith
  have hEpos : 0 < E := by linarith
  set y := Y * E with hydef
  have hy1 : 1 < y := by
    have : u * X ≤ Y * E := by nlinarith
    linarith
  have hYy : Y + y = X * Real.exp u * (1 + δ * t) := by
    simp only [hydef, hEdef, hYdef]; ring
  -- MV
  have hcount := hMV Y y hYpos hy1
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hth := theta_sub_le (x := Y) (z := Y + y) (by linarith) (by linarith)
  rw [hYy] at hth hcount
  -- logs
  set L := Real.log X with hL
  set l := Real.log u with hl
  set LY := Real.log Y with hLY
  have hL4 : 5 ≤ L := log_ge_five hX
  have hLuX : Real.log (u * X) = l + L := Real.log_mul hu0.ne' hXpos.ne'
  have hLuXpos : 0 < l + L := by rw [← hLuX]; exact Real.log_pos huX
  have hLYL : L ≤ LY := Real.log_le_log hXpos hY1
  have hlogYE : Real.log (X * Real.exp u * (1 + δ * t)) = LY + u := by
    rw [show X * Real.exp u * (1 + δ * t) = Y * Real.exp u by simp only [hYdef]; ring,
      Real.log_mul hYpos.ne' (Real.exp_pos u).ne', Real.log_exp]
  have hlogy' : Real.log y = LY + Real.log E := Real.log_mul hYpos.ne' hEpos.ne'
  have hlE : l ≤ Real.log E := Real.log_le_log hu0 hE1
  have hlneg : l < 0 := Real.log_neg hu0 (by linarith)
  -- the chain
  have hcnt0 : (0 : ℝ) ≤ (((Ioc ⌊Y⌋₊ ⌊X * Real.exp u * (1 + δ * t)⌋₊).filter Nat.Prime).card : ℝ) :=
    Nat.cast_nonneg _
  have hLYu : 0 ≤ LY + u := by linarith
  have step1 : θ (X * Real.exp u * (1 + δ * t)) - θ Y ≤ 2 * y / Real.log y * (LY + u) := by
    rw [hlogYE] at hth
    calc _ ≤ _ := hth
      _ ≤ 2 * y / Real.log y * (LY + u) := mul_le_mul_of_nonneg_right hcount.le hLYu
  have step2 : 2 * y / Real.log y * (LY + u) ≤ 2 * y * (L + u) / (l + L) := by
    rw [hlogy']
    have hden1 : 0 < LY + l := by linarith
    have hden2 : 0 < LY + Real.log E := by linarith
    have hy0 : 0 < y := by linarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hden2 hLuXpos]
    -- 2y (LY+u) (l+L) ≤ 2y (L+u) (LY + log E)
    have key : (LY + u) * (l + L) ≤ (L + u) * (LY + Real.log E) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hLYL) (show 0 ≤ u - l by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left key (show 0 ≤ 2 * y by linarith)]
  have step3 : 2 * y * (L + u) ≤ 2.0004 * u * X * L := by
    have h1 : y ≤ 1.0001 * X * (1.000075 * u) := by
      simp only [hydef]
      exact mul_le_mul hY2 hE3 hEpos.le (by positivity)
    have h2 : L + u ≤ 1.00002 * L := by linarith
    have hy0 : 0 ≤ y := by linarith
    have hL0 : 0 ≤ L := by linarith
    calc 2 * y * (L + u) ≤ 2 * y * (1.00002 * L) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ 2 * (1.0001 * X * (1.000075 * u)) * (1.00002 * L) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
      _ = 2.0003900220003 * (u * X * L) := by ring
      _ ≤ 2.0004 * u * X * L := by
          have : 0 ≤ u * X * L := by positivity
          linarith
  calc θ (X * Real.exp u * (1 + δ * t)) - θ Y ≤ 2 * y * (L + u) / (l + L) := step1.trans step2
    _ ≤ 2.0004 * u * X * L / (l + L) := div_le_div_of_nonneg_right step3 hLuXpos.le
    _ = 2.0004 * u * X * (L / Real.log (u * X)) := by rw [hLuX]; ring

/-- The rpow bound used in the step (12): `3 A^(1/3) ≤ 0.0297 √X` when `A ≤ 1.0003 X` and
`X ≥ 1.99 · 10^12`. -/
theorem cube_root_le {A X : ℝ} (hA0 : 0 < A) (hA : A ≤ 1.0003 * X) (hX : 199 * 10 ^ 10 ≤ X) :
    3 * A ^ (1 / 3 : ℝ) ≤ 0.0297 * √X := by
  have hXpos : 0 < X := by linarith
  set s := A ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hA0.le _
  have hs3 : s ^ 3 = A := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  set r := √X with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = X := Real.sq_sqrt hXpos.le
  -- s^6 = A^2 ≤ (0.0099 r)^6 = 0.0099^6 X^3
  have h6 : s ^ 6 ≤ (0.0099 * r) ^ 6 := by
    have e1 : s ^ 6 = A ^ 2 := by rw [← hs3]; ring
    have e2 : (0.0099 * r) ^ 6 = 0.0099 ^ 6 * X ^ 3 := by rw [← hr2]; ring
    rw [e1, e2]
    have hA2 : A ^ 2 ≤ (1.0003 * X) ^ 2 := pow_le_pow_left₀ hA0.le hA 2
    have : (1.0003 * X) ^ 2 ≤ 0.0099 ^ 6 * X ^ 3 := by
      have hX2 : 0 ≤ X ^ 2 := by positivity
      have : (1.0003 : ℝ) ^ 2 ≤ 0.0099 ^ 6 * X := by nlinarith
      nlinarith
    linarith
  have : s ≤ 0.0099 * r :=
    (pow_le_pow_iff_left₀ hs0 (by positivity) (by norm_num : (6 : ℕ) ≠ 0)).1 h6
  linarith

/-- **The step before (12), p. 19**, pointwise in `t`. Proved conditional on `SchoenfeldPT cl cu`
for any constants with `1.0001006 cu - cl ≤ 0.0028`, and `0 ≤ cu`. Here `X ≥ 1.99 · 10^12`,
which holds in Theorem 4 since `X ≥ 0.999 Y ≥ 1.998 · 10^12`. -/
theorem step12 {cl cu : ℝ} (hS : SchoenfeldPT cl cu) (hcu : 0 ≤ cu)
    (hc : 1.0001006 * cu - cl ≤ 0.0028) {X u δ t : ℝ} (hX : 199 * 10 ^ 10 ≤ X)
    (hu0 : 0 ≤ u) (hu : u ≤ 0.0001) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.0001)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -(0.0325 * √X) ≤ θ (Real.exp u * (1 + δ * t) * X) - θ ((1 + δ * t) * X) -
      (ψ (Real.exp u * (1 + δ * t) * X) - ψ ((1 + δ * t) * X)) := by
  have hXpos : 0 < X := by linarith
  have hdt0 : 0 ≤ δ * t := mul_nonneg hδ0 ht0
  have hdt1 : δ * t ≤ 0.0001 := by nlinarith
  set B := (1 + δ * t) * X with hB
  set A := Real.exp u * (1 + δ * t) * X with hAdef
  have hB1 : X ≤ B := by nlinarith
  have heu1 : 1 ≤ Real.exp u := Real.one_le_exp hu0
  have heu2 : Real.exp u ≤ 1.000101 := by
    have := exp_sub_one_le hu0 (by linarith); nlinarith
  have hAB : A = Real.exp u * B := by simp only [hAdef, hB]; ring
  have hBpos : 0 < B := by linarith
  have hA0 : 0 < A := by rw [hAB]; positivity
  have hA1 : A ≤ 1.0002011 * X := by
    rw [hAB]
    have : Real.exp u * B ≤ 1.000101 * (1.0001 * X) :=
      mul_le_mul heu2 (by nlinarith) hBpos.le (by norm_num)
    linarith
  have hlow := hS.1 B (by linarith)
  have hup := hS.2 A hA0
  have hsB : √X ≤ √B := Real.sqrt_le_sqrt hB1
  have hsA : √A ≤ 1.0001006 * √X := by
    have : A ≤ (1.0001006 * √X) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hXpos.le]; nlinarith
    calc √A ≤ √((1.0001006 * √X) ^ 2) := Real.sqrt_le_sqrt this
      _ = 1.0001006 * √X := Real.sqrt_sq (by positivity)
  have hcube := cube_root_le hA0 (by linarith) hX
  have hsX : 0 ≤ √X := Real.sqrt_nonneg _
  -- θ(A) - θ(B) - (ψ(A) - ψ(B)) = (ψ B - θ B) - (ψ A - θ A)
  have hcl : cl * √X ≤ cl * √B ∨ cl < 0 := by
    rcases le_or_gt 0 cl with h | h
    · exact Or.inl (mul_le_mul_of_nonneg_left hsB h)
    · exact Or.inr h
  rcases hcl with hcl | hcl
  · nlinarith [mul_le_mul_of_nonneg_left hsA hcu]
  · -- cl < 0: then ψ B - θ B ≥ 0 suffices
    have hpt : 0 ≤ ψ B - θ B := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      exact sum_nonneg fun n _ => by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsA hcu]

/-- `step12` with the printed constants of (11). -/
theorem step12_printed (hS : SchoenfeldPT 0.998697 1.001093) {X u δ t : ℝ}
    (hX : 199 * 10 ^ 10 ≤ X) (hu0 : 0 ≤ u) (hu : u ≤ 0.0001) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.0001)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -(0.0325 * √X) ≤ θ (Real.exp u * (1 + δ * t) * X) - θ ((1 + δ * t) * X) -
      (ψ (Real.exp u * (1 + δ * t) * X) - ψ ((1 + δ * t) * X)) :=
  step12 hS (by norm_num) (by norm_num) hX hu0 hu hδ0 hδ ht0 ht1


/-- The integrand of Theorem 4's proof, `θ(X e^u (1 + δ t)) - θ(X (1 + δ t))`. -/
noncomputable def Dθ (X u δ t : ℝ) : ℝ :=
  θ (X * Real.exp u * (1 + δ * t)) - θ (X * (1 + δ * t))

theorem theta_affine_mono {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) :
    Monotone (fun t : ℝ => θ (c * (1 + δ * t))) := by
  intro s t hst
  apply Chebyshev.theta_mono
  have : δ * s ≤ δ * t := mul_le_mul_of_nonneg_left hst hδ
  nlinarith

theorem Dθ_mul_intervalIntegrable {X u δ : ℝ} {f : ℝ → ℝ} (hX : 0 ≤ X) (hδ : 0 ≤ δ)
    {a b : ℝ} (hf : ContinuousOn f (Set.uIcc a b)) :
    IntervalIntegrable (fun t => Dθ X u δ t * f t) MeasureTheory.volume a b := by
  have h1 := (theta_affine_mono (c := X * Real.exp u) (by positivity) hδ).intervalIntegrable
    (μ := MeasureTheory.volume) (a := a) (b := b)
  have h2 := (theta_affine_mono (c := X) hX hδ).intervalIntegrable
    (μ := MeasureTheory.volume) (a := a) (b := b)
  exact (h1.sub h2).mul_continuousOn hf

/-- **The first inequality of (10), p. 18**, before the step with `α4`: with
`B = 2.0004 u X log X / log(u X)` from Lemma 5,
`∫_0^1 Dθ f ≤ (θ(X e^u (1 + δ(1 - a))) - θ(X (1 + δ a))) ∫_a^(1-a) f + B (∫_0^a f + ∫_(1-a)^1 f)`.
The paper's `Y` and `Y'` are `X e^u (1 + δ(1 - a))` and `X (1 + δ a)`.
Proved conditional on `MVBrunTitchmarsh`. -/
theorem step10 (hMV : MVBrunTitchmarsh) {X u δ a : ℝ} {f : ℝ → ℝ} (hX : 10 ^ 12 ≤ X)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.0001) (hu0 : 0 < u) (hu : u ≤ 0.0001) (huX : 1 < u * X)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t) :
    ∫ t in (0 : ℝ)..1, Dθ X u δ t * f t ≤
      (θ (X * Real.exp u * (1 + δ * (1 - a))) - θ (X * (1 + δ * a))) *
          (∫ t in a..(1 - a), f t) +
        2.0004 * u * X * (Real.log X / Real.log (u * X)) *
          ((∫ t in (0 : ℝ)..a, f t) + ∫ t in (1 - a)..1, f t) := by
  have hXpos : 0 < X := by linarith
  set B := 2.0004 * u * X * (Real.log X / Real.log (u * X)) with hB
  set C := θ (X * Real.exp u * (1 + δ * (1 - a))) - θ (X * (1 + δ * a)) with hC
  have sub : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ 1 → ContinuousOn f (Set.uIcc c d) := by
    intro c d hc hcd hd
    apply hf.mono
    intro x hx
    rw [Set.uIcc_of_le hcd] at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have s1 := sub (le_refl 0) ha0 (by linarith : a ≤ 1)
  have s2 := sub ha0 (by linarith : a ≤ 1 - a) (by linarith : 1 - a ≤ 1)
  have s3 := sub (by linarith : 0 ≤ 1 - a) (by linarith : 1 - a ≤ 1) (le_refl 1)
  have i1 := Dθ_mul_intervalIntegrable (u := u) hXpos.le hδ0 s1
  have i2 := Dθ_mul_intervalIntegrable (u := u) hXpos.le hδ0 s2
  have i3 := Dθ_mul_intervalIntegrable (u := u) hXpos.le hδ0 s3
  have j1 : IntervalIntegrable f MeasureTheory.volume 0 a := s1.intervalIntegrable
  have j2 : IntervalIntegrable f MeasureTheory.volume a (1 - a) := s2.intervalIntegrable
  have j3 : IntervalIntegrable f MeasureTheory.volume (1 - a) 1 := s3.intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have hL5 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Dθ X u δ t * f t ≤ B * f t := by
    intro t ht
    exact mul_le_mul_of_nonneg_right (lemma5 hMV hX hδ0 hδ hu0 hu huX ht.1 ht.2) (hf0 t ht)
  have e1 : ∫ t in (0 : ℝ)..a, Dθ X u δ t * f t ≤ B * ∫ t in (0 : ℝ)..a, f t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha0 i1 (j1.const_mul B)
      (fun t ht => hL5 t ⟨ht.1, by linarith [ht.2]⟩)
  have e3 : ∫ t in (1 - a)..1, Dθ X u δ t * f t ≤ B * ∫ t in (1 - a)..1, f t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith) i3 (j3.const_mul B)
      (fun t ht => hL5 t ⟨by linarith [ht.1], ht.2⟩)
  have e2 : ∫ t in a..(1 - a), Dθ X u δ t * f t ≤ C * ∫ t in a..(1 - a), f t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) i2 (j2.const_mul C) ?_
    intro t ht
    have hft := hf0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    apply mul_le_mul_of_nonneg_right _ hft
    have m1 := theta_affine_mono (c := X * Real.exp u) (by positivity) hδ0 ht.2
    have m2 := theta_affine_mono (c := X) hXpos.le hδ0 ht.1
    simp only at m1 m2
    simp only [Dθ, hC]
    linarith
  linarith

theorem log_ge_28 {Y : ℝ} (hY : 2 * 10 ^ 12 ≤ Y) : 28 ≤ Real.log Y := by
  have he : Real.exp 28 ≤ Y := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 28 = Real.exp 1 ^ 28 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    have : Real.exp 1 ^ 28 ≤ 2.7182818286 ^ 28 := pow_le_pow_left₀ h0 h1.le 28
    linarith [show (2.7182818286 : ℝ) ^ 28 ≤ 2 * 10 ^ 12 by norm_num]
  calc (28 : ℝ) = Real.log (Real.exp 28) := (Real.log_exp 28).symm
    _ ≤ Real.log Y := Real.log_le_log (Real.exp_pos 28) he

/-- **The step with `α4` in (10), p. 18.** The paper writes `log X/log(uX) ≤ log Y/log(uY)`,
which is reversed: `s ↦ s/(s + log u)` decreases since `log u < 0`. What holds, and suffices
for the printed constant `2.001`, is `2.0004 log X/log(uX) ≤ 2.001/α4`, using only
`X ≤ Y ≤ 1.00021 X`, `Y ≥ 2 · 10^12` and `Y^α4 ≤ u Y`. Proved outright. -/
theorem bound_alpha4 {X Y u α4 : ℝ} (hu0 : 0 < u) (hXY : X ≤ Y) (hYX : Y ≤ 1.00021 * X)
    (hY : 2 * 10 ^ 12 ≤ Y) (hα4 : 1 / 2 ≤ α4) (h4 : Y ^ α4 ≤ u * Y) (huX : 1 < u * X) :
    2.0004 * (Real.log X / Real.log (u * X)) ≤ 2.001 / α4 := by
  have hYpos : 0 < Y := by linarith
  have hXpos : 0 < X := by nlinarith
  have hα4pos : 0 < α4 := by linarith
  have hLY := log_ge_28 hY
  have hl4 : α4 * Real.log Y ≤ Real.log (u * Y) := by
    rw [← Real.log_rpow hYpos]
    exact Real.log_le_log (Real.rpow_pos_of_pos hYpos _) h4
  have hlk : Real.log (u * Y) - Real.log (u * X) ≤ 0.00021 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : u * Y / (u * X) ≤ 1.00021 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hp : 0 < u * Y / (u * X) := by positivity
    have := Real.log_le_sub_one_of_pos hp
    linarith
  have hLX : Real.log X ≤ Real.log Y := Real.log_le_log hXpos hXY
  have hluX : 0 < Real.log (u * X) := Real.log_pos huX
  have h14 : 14 ≤ α4 * Real.log Y := by nlinarith
  rw [mul_div_assoc', div_le_div_iff₀ hluX hα4pos]
  nlinarith

/-- **(10) of p. 18 as printed**, with `Y = X e^u (1 + δ(1 - a))` and `Y' = X (1 + δ a)`:
`∫_0^1 Dθ f ≤ (θ(Y) - θ(Y')) ∫_a^(1-a) f + (2.001/α4) u X (∫_0^a f + ∫_(1-a)^1 f)`.
Proved conditional on `MVBrunTitchmarsh`. -/
theorem step10_alpha4 (hMV : MVBrunTitchmarsh) {X u δ a α4 : ℝ} {f : ℝ → ℝ}
    (hX : 10 ^ 12 ≤ X) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.0001) (hu0 : 0 < u) (hu : u ≤ 0.0001)
    (huX : 1 < u * X) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t)
    (hY : 2 * 10 ^ 12 ≤ X * Real.exp u * (1 + δ * (1 - a))) (hα4 : 1 / 2 ≤ α4)
    (h4 : (X * Real.exp u * (1 + δ * (1 - a))) ^ α4 ≤ u * (X * Real.exp u * (1 + δ * (1 - a)))) :
    ∫ t in (0 : ℝ)..1, Dθ X u δ t * f t ≤
      (θ (X * Real.exp u * (1 + δ * (1 - a))) - θ (X * (1 + δ * a))) *
          (∫ t in a..(1 - a), f t) +
        2.001 / α4 * u * X * ((∫ t in (0 : ℝ)..a, f t) + ∫ t in (1 - a)..1, f t) := by
  have h10 := step10 hMV hX hδ0 hδ hu0 hu huX ha0 ha hf hf0
  have hXpos : 0 < X := by linarith
  have hsub : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ 1 → 0 ≤ ∫ t in c..d, f t := by
    intro c d hc hcd hd
    exact intervalIntegral.integral_nonneg hcd (fun t ht => hf0 t ⟨by linarith [ht.1],
      by linarith [ht.2]⟩)
  have hv : 0 ≤ (∫ t in (0 : ℝ)..a, f t) + ∫ t in (1 - a)..1, f t :=
    add_nonneg (hsub le_rfl ha0 (by linarith)) (hsub (by linarith) (by linarith) le_rfl)
  have heu1 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
  have heu2 : Real.exp u ≤ 1.000101 := by
    have := exp_sub_one_le hu0.le (by linarith); nlinarith
  have hda : 0 ≤ δ * (1 - a) := mul_nonneg hδ0 (by linarith)
  have hda1 : δ * (1 - a) ≤ 0.0001 := by nlinarith
  have hXY : X ≤ X * Real.exp u * (1 + δ * (1 - a)) := by
    have : 1 ≤ Real.exp u * (1 + δ * (1 - a)) := by nlinarith
    nlinarith
  have hYX : X * Real.exp u * (1 + δ * (1 - a)) ≤ 1.00021 * X := by
    have : Real.exp u * (1 + δ * (1 - a)) ≤ 1.00021 := by nlinarith
    nlinarith
  have hb := bound_alpha4 hu0 hXY hYX hY hα4 h4 huX
  have huX0 : 0 ≤ u * X := by positivity
  have : 2.0004 * u * X * (Real.log X / Real.log (u * X)) ≤ 2.001 / α4 * u * X := by
    have := mul_le_mul_of_nonneg_left hb huX0
    linarith [show 2.0004 * u * X * (Real.log X / Real.log (u * X)) =
      u * X * (2.0004 * (Real.log X / Real.log (u * X))) by ring,
      show 2.001 / α4 * u * X = u * X * (2.001 / α4) by ring]
  nlinarith [mul_le_mul_of_nonneg_right this hv]

end LeanLab.RamareSaouter2003.Thm4Parts

