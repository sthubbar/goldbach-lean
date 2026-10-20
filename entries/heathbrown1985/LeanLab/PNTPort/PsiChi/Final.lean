module

public import LeanLab.PNTPort.PsiChi.Unsmooth
public import LeanLab.PNTPort.StrongPNT.Bridge

/-!
# `ψ(x, χ) ≪ x exp(-c √log x)` for non-principal `χ` mod `N ≤ (log x)^A`

Lab proof, unit U-5208, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics,
Siegel-Walfisz for non-principal characters, ineffective through Siegel's theorem; no cited input.

Helper lemmas here; the main theorem `psiChi_nonprincipal_bound` chooses `T = exp(√log x)`,
`ε = exp(-δ √log x)` in `smoothed_psiChi_bound`, puts the exceptional zero left of the line by
`zeros_classical_or_siegel` with Siegel exponent `1/(4A)`, and unsmooths with the `q = 1` prime
number theorem `psi_explicit_strong` of the StrongPNT port.
-/

@[expose] public section


open Set Function Filter Complex Real Finset

open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

namespace LeanLab.PNTPort.PsiChi

open LeanLab.PNTPort.DirichletZF

lemma sq_le_exp {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) : u ^ 2 ≤ 2 / a ^ 2 * Real.exp (a * u) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := a * u) (by positivity)
  have hau : 0 ≤ a * u := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

lemma norm_psiChi_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) :
    ‖BV.psiChi x χ‖ ≤ Chebyshev.psi x := by
  unfold BV.psiChi Chebyshev.psi
  have e : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by ext n; simp; omega
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)

lemma log_Bt_exp_ge {N : ℕ} [NeZero N] (u : ℝ) : u ≤ Real.log (Bt N (Real.exp u)) := by
  have hB : Real.exp u ≤ Bt N (Real.exp u) := by
    unfold Bt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hZ := one_le_Z
    have he := Real.exp_pos u
    rw [abs_of_pos he]
    have : Real.exp u ≤ 2 * N * (Real.exp u + 3) := by nlinarith
    nlinarith
  calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos u) hB

lemma log_Bt_exp_le {N : ℕ} [NeZero N] {A u x : ℝ} (hA : 0 < A) (hu : 1 ≤ u)
    (hx : Real.log x = u ^ 2) (hN : (N : ℝ) ≤ Real.log x ^ A) :
    Real.log (Bt N (Real.exp u)) ≤ (Real.log (8 * Z) + 2 * A + 1) * u := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hZ := one_le_Z
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp (by linarith)
  have hB : Bt N (Real.exp u) ≤ 8 * Z * N * Real.exp u := by
    unfold Bt
    rw [abs_of_pos (Real.exp_pos u)]
    have h3 : Real.exp u + 3 ≤ 4 * Real.exp u := by linarith
    have hNZ : 0 ≤ 2 * (N : ℝ) * Z := by positivity
    calc 2 * (N : ℝ) * (Real.exp u + 3) * Z = (2 * N * Z) * (Real.exp u + 3) := by ring
      _ ≤ (2 * N * Z) * (4 * Real.exp u) := mul_le_mul_of_nonneg_left h3 hNZ
      _ = 8 * Z * N * Real.exp u := by ring
  have hlx : 0 < Real.log x := by rw [hx]; nlinarith
  have hlogN : Real.log N ≤ 2 * A * u := by
    have h1 : Real.log N ≤ Real.log (Real.log x ^ A) := Real.log_le_log (by linarith) hN
    rw [Real.log_rpow hlx, hx, Real.log_pow] at h1
    have h2 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
    push_cast at h1
    nlinarith
  have hl8 : 0 ≤ Real.log (8 * Z) := Real.log_nonneg (by linarith)
  calc Real.log (Bt N (Real.exp u)) ≤ Real.log (8 * Z * N * Real.exp u) :=
        Real.log_le_log (lt_trans one_pos (one_lt_Bt _)) hB
    _ = Real.log (8 * Z) + Real.log N + u := by
        rw [Real.log_mul (by positivity) (Real.exp_pos u).ne', Real.log_exp,
          Real.log_mul (by positivity) (by linarith)]
    _ ≤ Real.log (8 * Z) * u + 2 * A * u + u := by nlinarith
    _ = _ := by ring

lemma psi_window {cP KP : ℝ} (hcP : 0 < cP)
    (hP : ∀ y : ℝ, 2 ≤ y → |Chebyshev.psi y - y| ≤ KP * y * Real.exp (-cP * Real.sqrt (Real.log y)))
    {x ε : ℝ} (hx : 4 ≤ x) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Chebyshev.psi (x * (1 + 2 * ε)) - Chebyshev.psi (x * (1 - ε)) ≤
      3 * ε * x + 3 * KP * x * Real.exp (-(cP / 2) * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hKP : 0 ≤ KP := by
    have h2 := hP 2 le_rfl
    have hψ : Chebyshev.psi 2 = Real.log 2 := by
      rw [Chebyshev.psi, show ⌊(2 : ℝ)⌋₊ = 2 by norm_num]
      rw [show Finset.Ioc 0 2 = {1, 2} by decide]
      simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    rw [hψ] at h2
    have hl : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have : 0 < |Real.log 2 - 2| := by rw [abs_pos]; linarith
    by_contra hneg; push_neg at hneg
    have : KP * 2 * Real.exp (-cP * Real.sqrt (Real.log 2)) < 0 := by
      have := Real.exp_pos (-cP * Real.sqrt (Real.log 2)); nlinarith
    linarith
  set y₁ := x * (1 + 2 * ε)
  set y₂ := x * (1 - ε)
  have hy₂ : 2 ≤ y₂ := by nlinarith
  have hy₁ : x ≤ y₁ := by nlinarith
  have hy₁2 : 2 ≤ y₁ := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set E := Real.exp (-(cP / 2) * Real.sqrt (Real.log x)) with hE
  have hE1 : Real.exp (-cP * Real.sqrt (Real.log y₁)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y₁) :=
      Real.sqrt_le_sqrt (Real.log_le_log hx0 hy₁)
    have hs := Real.sqrt_nonneg (Real.log x)
    nlinarith
  have hE2 : Real.exp (-cP * Real.sqrt (Real.log y₂)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have hl2 : Real.log x / 4 ≤ Real.log y₂ := by
      have h1 : x / 2 ≤ y₂ := by nlinarith
      have h2 : Real.log (x / 2) ≤ Real.log y₂ := Real.log_le_log (by positivity) h1
      rw [Real.log_div hx0.ne' (by norm_num)] at h2
      have h3 : 2 * Real.log 2 ≤ Real.log x := by
        rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num; linarith)
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    have : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log y₂) := by
      have : Real.sqrt (Real.log x / 4) = Real.sqrt (Real.log x) / 2 := by
        rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [← this]; exact Real.sqrt_le_sqrt hl2
    nlinarith
  have h1 := hP y₁ hy₁2
  have h2 := hP y₂ hy₂
  rw [abs_le] at h1 h2
  have hy₁le : y₁ ≤ 2 * x := by nlinarith
  have hy₂le : y₂ ≤ x := by nlinarith
  have hy₂0 : 0 ≤ y₂ := by linarith
  have a1 : KP * y₁ * Real.exp (-cP * Real.sqrt (Real.log y₁)) ≤ KP * (2 * x) * E := by
    gcongr
  have a2 : KP * y₂ * Real.exp (-cP * Real.sqrt (Real.log y₂)) ≤ KP * x * E := by
    gcongr
  have : y₁ - y₂ = 3 * ε * x := by ring
  nlinarith

lemma KP_nonneg {cP KP : ℝ}
    (hP : ∀ y : ℝ, 2 ≤ y → |Chebyshev.psi y - y| ≤ KP * y * Real.exp (-cP * Real.sqrt (Real.log y))) :
    0 ≤ KP := by
  have h2 := hP 2 le_rfl
  have hψ : Chebyshev.psi 2 = Real.log 2 := by
    rw [Chebyshev.psi, show ⌊(2 : ℝ)⌋₊ = 2 by norm_num]
    rw [show Finset.Ioc 0 2 = {1, 2} by decide]
    simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rw [hψ] at h2
  have hl : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have : 0 < |Real.log 2 - 2| := by rw [abs_pos]; linarith
  by_contra hneg; push_neg at hneg
  have : KP * 2 * Real.exp (-cP * Real.sqrt (Real.log 2)) < 0 := by
    have := Real.exp_pos (-cP * Real.sqrt (Real.log 2)); nlinarith
  linarith


lemma piece1 {C A₁ a u x cF : ℝ} (hC : 0 < C) (hA₁ : 1 ≤ A₁) (ha24 : a ≤ 1 / 24)
    (hu0 : 0 ≤ u) (hx0 : 0 < x) (hcFa : cF ≤ a) (hcF : 0 < cF) :
    C / (2 * π) * Real.exp (2 * a * u) * (2 * Real.exp 1 * (u ^ 2 + A₁) * x / Real.exp u) ≤
      C * Real.exp 1 / π * (32 + A₁) * x * Real.exp (-cF * u) := by
  have hq : u ^ 2 ≤ 32 * Real.exp (u / 4) := by
    have := sq_le_exp (a := 1 / 4) (by norm_num) hu0
    have e : (2 : ℝ) / (1 / 4) ^ 2 = 32 := by norm_num
    rw [e, show (1 / 4 : ℝ) * u = u / 4 by ring] at this; exact this
  have he4 : 1 ≤ Real.exp (u / 4) := Real.one_le_exp (by positivity)
  have hA₁e : A₁ ≤ A₁ * Real.exp (u / 4) := le_mul_of_one_le_right (by linarith) he4
  have hpoly : u ^ 2 + A₁ ≤ (32 + A₁) * Real.exp (u / 4) := by linarith
  have hexp : Real.exp (2 * a * u) * Real.exp (u / 4) / Real.exp u ≤ Real.exp (-cF * u) := by
    rw [← Real.exp_add, ← Real.exp_sub]; apply Real.exp_le_exp.mpr
    have h1 : 2 * a * u ≤ u / 12 := by nlinarith
    have h2 : cF * u ≤ a * u := mul_le_mul_of_nonneg_right hcFa hu0
    have h3 : a * u ≤ u / 24 := by nlinarith
    linarith
  have hpi := Real.pi_pos
  calc C / (2 * π) * Real.exp (2 * a * u) * (2 * Real.exp 1 * (u ^ 2 + A₁) * x / Real.exp u)
      = C * Real.exp 1 / π * x * ((u ^ 2 + A₁) * (Real.exp (2 * a * u) / Real.exp u)) := by
        field_simp
    _ ≤ C * Real.exp 1 / π * x * ((32 + A₁) * Real.exp (u / 4) *
          (Real.exp (2 * a * u) / Real.exp u)) := by gcongr
    _ = C * Real.exp 1 / π * (32 + A₁) * x *
          (Real.exp (2 * a * u) * Real.exp (u / 4) / Real.exp u) := by ring
    _ ≤ C * Real.exp 1 / π * (32 + A₁) * x * Real.exp (-cF * u) := by gcongr

lemma piece2 {C K Lam a u x cF κ LT : ℝ} (hC : 0 < C) (hK : 0 < K) (ha : 0 < a)
    (hu0 : 0 ≤ u) (hx0 : 0 < x) (hcFa : cF ≤ a) (hLT2 : LT ^ 2 ≤ Lam ^ 2 * (2 / a ^ 2) * Real.exp (a * u))
    (hk : 4 * a * u ≤ κ * u ^ 2 / LT) :
    C / (2 * π) * Real.exp (2 * a * u) * (4 * π * (K * LT ^ 2) * (x * Real.exp (-(κ * u ^ 2 / LT)))) ≤
      4 * C * K * Lam ^ 2 / a ^ 2 * x * Real.exp (-cF * u) := by
  have hexp : Real.exp (2 * a * u) * Real.exp (a * u) * Real.exp (-(κ * u ^ 2 / LT)) ≤
      Real.exp (-cF * u) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr
    have h2 : cF * u ≤ a * u := mul_le_mul_of_nonneg_right hcFa hu0
    linarith
  have hpi := Real.pi_pos
  calc C / (2 * π) * Real.exp (2 * a * u) * (4 * π * (K * LT ^ 2) * (x * Real.exp (-(κ * u ^ 2 / LT))))
      = 2 * C * K * x * (LT ^ 2 * (Real.exp (2 * a * u) * Real.exp (-(κ * u ^ 2 / LT)))) := by
        field_simp; ring
    _ ≤ 2 * C * K * x * (Lam ^ 2 * (2 / a ^ 2) * Real.exp (a * u) *
          (Real.exp (2 * a * u) * Real.exp (-(κ * u ^ 2 / LT)))) := by gcongr
    _ = 4 * C * K * Lam ^ 2 / a ^ 2 * x *
          (Real.exp (2 * a * u) * Real.exp (a * u) * Real.exp (-(κ * u ^ 2 / LT))) := by ring
    _ ≤ 4 * C * K * Lam ^ 2 / a ^ 2 * x * Real.exp (-cF * u) := by gcongr

lemma piece3 {C K Lam a u x cF LT : ℝ} (hC : 0 < C) (hK : 0 < K) (ha : 0 < a) (ha24 : a ≤ 1 / 24)
    (hu0 : 0 ≤ u) (hx0 : 0 < x) (hcFa : cF ≤ a)
    (hLT2 : LT ^ 2 ≤ Lam ^ 2 * (2 / a ^ 2) * Real.exp (a * u)) :
    C / (2 * π) * Real.exp (2 * a * u) * (3 * Real.exp 1 * (K * LT ^ 2) * x / Real.exp u ^ 2) ≤
      3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) * x * Real.exp (-cF * u) := by
  have hexp : Real.exp (2 * a * u) * Real.exp (a * u) / Real.exp u ^ 2 ≤ Real.exp (-cF * u) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sub]; apply Real.exp_le_exp.mpr
    have h2 : cF * u ≤ a * u := mul_le_mul_of_nonneg_right hcFa hu0
    have h3 : a * u ≤ u / 24 := by nlinarith
    push_cast; linarith
  have hpi := Real.pi_pos
  calc C / (2 * π) * Real.exp (2 * a * u) * (3 * Real.exp 1 * (K * LT ^ 2) * x / Real.exp u ^ 2)
      = 3 * Real.exp 1 * C * K / (2 * π) * x * (LT ^ 2 * (Real.exp (2 * a * u) / Real.exp u ^ 2)) := by
        field_simp
    _ ≤ 3 * Real.exp 1 * C * K / (2 * π) * x * (Lam ^ 2 * (2 / a ^ 2) * Real.exp (a * u) *
          (Real.exp (2 * a * u) / Real.exp u ^ 2)) := by gcongr
    _ = 3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) * x *
          (Real.exp (2 * a * u) * Real.exp (a * u) / Real.exp u ^ 2) := by field_simp
    _ ≤ 3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) * x * Real.exp (-cF * u) := by gcongr

set_option maxHeartbeats 4000000 in
/-- **Siegel-Walfisz for non-principal characters.** For every `A > 0` there are `c > 0` and `K`
with `‖ψ(x, χ)‖ ≤ K x exp(-c √log x)` for every `x ≥ 2`, every modulus `N ≤ (log x)^A` and every
non-principal `χ` mod `N`. Ineffective, through Siegel's theorem. -/
theorem psiChi_nonprincipal_bound : ∀ A : ℝ, 0 < A → ∃ c K : ℝ, 0 < c ∧
    ∀ x : ℝ, 2 ≤ x → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (N : ℝ) ≤ Real.log x ^ A →
      ‖BV.psiChi x χ‖ ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  intro A hA
  obtain ⟨ν, hν, hν0, hνs, hνm⟩ := SmoothExistence
  have hν1 : ContDiff ℝ 1 ν := hν.of_le (by simp)
  have hνpos : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ hν0 x
  have hνm' : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  set ε' := 1 / (4 * A) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨c, cS, hc, hcS, hzer⟩ := zeros_classical_or_siegel ε' hε'0
  obtain ⟨κ, K, A₁, C, hκ, hK, hA₁, hC, hsm⟩ := smoothed_psiChi_bound hν1 hνpos hνs hνm' c hc
  obtain ⟨cP, hcP, KP, hP⟩ := psi_explicit_strong
  have hKP := KP_nonneg hP
  set Lam := Real.log (8 * Z) + 2 * A + 1 with hLamdef
  have hl8 : 0 ≤ Real.log (8 * Z) := Real.log_nonneg (by linarith [one_le_Z])
  have hLam : 1 ≤ Lam := by rw [hLamdef]; linarith
  set a := min (κ / (4 * Lam)) (1 / 24) with hadef
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha24 : a ≤ 1 / 24 := min_le_right _ _
  have haκ : a ≤ κ / (4 * Lam) := min_le_left _ _
  set cF := min a (cP / 2) with hcFdef
  have hcF : 0 < cF := lt_min ha (by positivity)
  have hcFa : cF ≤ a := min_le_left _ _
  have hcFP : cF ≤ cP / 2 := min_le_right _ _
  set U₀ := max (max 2 (1 / (2 * a))) ((2 * κ / cS) ^ 2) with hU₀
  have hU₀2 : 2 ≤ U₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  set Kbig := 3 + 3 * KP + C * Real.exp 1 / π * (32 + A₁) + 4 * C * K * Lam ^ 2 / a ^ 2 +
    3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) with hKbig
  have hKbig0 : 0 ≤ Kbig := by positivity
  set Ksmall := (Real.log 4 + 4) * Real.exp (cF * U₀) with hKsmall
  have hKsmall0 : 0 ≤ Ksmall := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨cF, Kbig + Ksmall, hcF, fun x hx N _ χ hχ hN ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set u := Real.sqrt (Real.log x) with hudef
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : Real.log x = u ^ 2 := (Real.sq_sqrt hlx).symm
  set E := Real.exp (-cF * u) with hE
  have hEpos : 0 < E := Real.exp_pos _
  by_cases hU : u < U₀
  · -- small x: Chebyshev
    have h1 := norm_psiChi_le χ x
    have h2 := Chebyshev.psi_le_const_mul_self hx0.le
    have h3 : 1 ≤ Real.exp (cF * U₀) * E := by
      rw [hE, ← Real.exp_add]; apply Real.one_le_exp; nlinarith
    have h4 : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
    calc ‖BV.psiChi x χ‖ ≤ (Real.log 4 + 4) * x := h1.trans h2
      _ ≤ (Real.log 4 + 4) * x * (Real.exp (cF * U₀) * E) := le_mul_of_one_le_right (by positivity) h3
      _ = Ksmall * x * E := by rw [hKsmall]; ring
      _ ≤ (Kbig + Ksmall) * x * E := by
          have : 0 ≤ Kbig * x * E := by positivity
          nlinarith
  push_neg at hU
  have hu2' : 2 ≤ u := hU₀2.trans hU
  have hu1 : 1 ≤ u := by linarith
  have hx4 : 4 ≤ x := by
    have h4 : Real.exp 4 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by rw [hu2]; nlinarith)
    have : Real.exp 4 ≤ x := by rwa [Real.exp_log hx0] at h4
    have := Real.add_one_le_exp (4 : ℝ); linarith
  set T := Real.exp u with hT
  have hT1 : 1 ≤ T := Real.one_le_exp hu0
  set ε := Real.exp (-(2 * a) * u) with hεdef
  have hεpos : 0 < ε := Real.exp_pos _
  have hε2 : ε ≤ 1 / 2 := by
    have h2au : 1 ≤ 2 * a * u := by
      have : 1 / (2 * a) ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hU
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have : ε ≤ Real.exp (-1) := by rw [hεdef]; apply Real.exp_le_exp.mpr; nlinarith
    have he : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9; norm_num; linarith
    linarith
  set LT := Real.log (Bt N T) with hLTdef
  have hLTge : u ≤ LT := log_Bt_exp_ge u
  have hLTle : LT ≤ Lam * u := log_Bt_exp_le hA hu1 hu2 hN
  have hLTpos : 0 < LT := by linarith
  -- the zero hypothesis
  have hfar : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) ∨ ρ.re ≤ 1 - 2 * κ / LT := by
    intro ρ hρ
    rcases hzer N χ hχ ρ hρ with h | h
    · exact Or.inl h
    right
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hNε : (N : ℝ) ^ ε' ≤ Real.sqrt u := by
      have hlx0 : 0 ≤ Real.log x := hlx
      calc (N : ℝ) ^ ε' ≤ (Real.log x ^ A) ^ ε' := Real.rpow_le_rpow hN0.le hN hε'0.le
        _ = Real.log x ^ (A * ε') := (Real.rpow_mul hlx0 A ε').symm
        _ = Real.log x ^ ((1 : ℝ) / 4) := by rw [hε']; field_simp
        _ = Real.sqrt u := by
            rw [hu2, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
    have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
    have hNε' : 1 / Real.sqrt u ≤ (N : ℝ) ^ (-ε') := by
      rw [Real.rpow_neg hN0.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hNε
    have hsq : 2 * κ / cS ≤ Real.sqrt u := by
      apply Real.le_sqrt_of_sq_le
      exact le_trans (le_max_right _ _) hU
    have key : 2 * κ / LT ≤ cS * (N : ℝ) ^ (-ε') := by
      have e1 : 2 * κ / LT ≤ 2 * κ / u := div_le_div_of_nonneg_left (by positivity) (by linarith) hLTge
      have e2 : 2 * κ / u ≤ cS * (1 / Real.sqrt u) := by
        have hsq2 : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
        rw [div_le_iff₀ (by linarith), mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hsu]
        rw [div_le_iff₀ hcS] at hsq
        nlinarith
      have e3 : cS * (1 / Real.sqrt u) ≤ cS * (N : ℝ) ^ (-ε') := mul_le_mul_of_nonneg_left hNε' hcS.le
      linarith
    linarith
  have hS := hsm N χ hχ x ε T (by linarith) hεpos (by linarith) hT1 hfar
  have hUn := unsmooth_le hνpos hνs hνm' χ hx0 hεpos (by linarith)
  have hW := psi_window hcP hP hx4 hεpos hε2
  -- the six pieces
  have hεinv : C / (2 * π * ε) = C / (2 * π) * Real.exp (2 * a * u) := by
    rw [hεdef, div_mul_eq_div_div, div_eq_mul_inv (C / (2 * π)), ← Real.exp_neg]; ring_nf
  have hCpi : 0 ≤ C / (2 * π) := by positivity
  have p1 : C / (2 * π * ε) * (2 * Real.exp 1 * (Real.log x + A₁) * x / T) ≤
      C * Real.exp 1 / π * (32 + A₁) * x * E := by
    rw [hεinv, hu2, hT]; exact piece1 hC hA₁ ha24 hu0 hx0 hcFa hcF
  have hLT2 : LT ^ 2 ≤ Lam ^ 2 * (2 / a ^ 2) * Real.exp (a * u) := by
    have h1 : LT ^ 2 ≤ (Lam * u) ^ 2 := by gcongr
    have h2 := sq_le_exp ha hu0
    calc LT ^ 2 ≤ Lam ^ 2 * u ^ 2 := by rw [← mul_pow]; exact h1
      _ ≤ Lam ^ 2 * (2 / a ^ 2 * Real.exp (a * u)) := by gcongr
      _ = _ := by ring
  have hk : 4 * a * u ≤ κ * u ^ 2 / LT := by
    rw [le_div_iff₀ hLTpos]
    have h4 : 4 * a * Lam ≤ κ := by
      have := haκ; rw [le_div_iff₀ (by positivity)] at this; linarith
    have h5 : LT * (4 * a * u) ≤ (Lam * u) * (4 * a * u) :=
      mul_le_mul_of_nonneg_right hLTle (by positivity)
    have h6 : (Lam * u) * (4 * a * u) = (4 * a * Lam) * u ^ 2 := by ring
    have h7 : (4 * a * Lam) * u ^ 2 ≤ κ * u ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
    linarith
  have p2 : C / (2 * π * ε) * (4 * π * (K * LT ^ 2) * x ^ (1 - κ / LT)) ≤
      4 * C * K * Lam ^ 2 / a ^ 2 * x * E := by
    rw [hεinv]
    have hrp : x ^ (1 - κ / LT) = x * Real.exp (-(κ * u ^ 2 / LT)) := by
      rw [Real.rpow_def_of_pos hx0, mul_sub, mul_one, Real.exp_sub, Real.exp_log hx0, hu2,
        Real.exp_neg]
      ring_nf
    rw [hrp]; exact piece2 hC hK ha hu0 hx0 hcFa hLT2 hk
  have p3 : C / (2 * π * ε) * (3 * Real.exp 1 * (K * LT ^ 2) * x / T ^ 2) ≤
      3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) * x * E := by
    rw [hεinv, hT]; exact piece3 hC hK ha ha24 hu0 hx0 hcFa hLT2
  have p4 : 3 * ε * x ≤ 3 * x * E := by
    have hεE : ε ≤ E := by
      rw [hεdef, hE]; apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hcFa hu0
      have : 0 ≤ a * u := by positivity
      linarith
    have h := mul_le_mul_of_nonneg_left hεE (by positivity : (0 : ℝ) ≤ 3 * x)
    linarith
  have p5 : 3 * KP * x * Real.exp (-(cP / 2) * u) ≤ 3 * KP * x * E := by
    have hPE : Real.exp (-(cP / 2) * u) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hcFP hu0
      linarith
    exact mul_le_mul_of_nonneg_left hPE (by positivity)
  have htri : ‖BV.psiChi x χ‖ ≤
      ‖BV.psiChi x χ - ∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 ν ε (n / x)‖ +
        ‖∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 ν ε (n / x)‖ := norm_le_norm_sub_add _ _
  rw [mul_add, mul_add] at hS
  have hSb : ‖∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 ν ε (n / x)‖ ≤
      C * Real.exp 1 / π * (32 + A₁) * x * E + 4 * C * K * Lam ^ 2 / a ^ 2 * x * E +
        3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) * x * E := by
    refine hS.trans ?_
    exact add_le_add (add_le_add p1 p2) p3
  have hUb : ‖BV.psiChi x χ - ∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 ν ε (n / x)‖ ≤
      3 * x * E + 3 * KP * x * E := by
    refine hUn.trans (hW.trans ?_)
    exact add_le_add p4 p5
  have hx1 : 0 ≤ Ksmall * x * E := by positivity
  calc ‖BV.psiChi x χ‖ ≤ (3 * x * E + 3 * KP * x * E) + (C * Real.exp 1 / π * (32 + A₁) * x * E +
        4 * C * K * Lam ^ 2 / a ^ 2 * x * E + 3 * Real.exp 1 * C * K * Lam ^ 2 / (π * a ^ 2) * x * E) :=
        htri.trans (add_le_add hUb hSb)
    _ = Kbig * x * E := by rw [hKbig]; ring
    _ ≤ (Kbig + Ksmall) * x * E := by linarith

end LeanLab.PNTPort.PsiChi
