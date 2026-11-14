module

public import Mathlib

/-!
Li-Liu, arXiv 2610.15784, Section 5, Lemma 5.1, display (43), read by WebFetch on
arxiv.org/html/2610.15784, 2026-10-21.

Paper, Lemma 5.1: let w be real, continuous, 1-periodic with w(t + 1/2) = -w(t). Then for every
positive integer L,
  (43)  ∫_0^1 exp(∑_{ν=1}^{L} [w(2^ν α) - log cosh w(2^ν α)]) dα = 1.
The proof: h(t) = e^{w(t)}/cosh w(t) has h(t) + h(t + 1/2) = 2, and the integrals I_ℓ of
products over ν = 0, ..., ℓ - 1 satisfy I_{ℓ+1} = I_ℓ by splitting [0,1] at 1/2.

Here: `int_prod_eq_one`, the product form for any continuous 1-periodic h with
h(t) + h(t + 1/2) = 2, ν = 0, ..., L - 1; `int_prod_Icc_eq_one`, ν = 1, ..., L; `lemma51`,
display (43) for every L, including L = 0. All PROVED unconditional.

Unit U-1420, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1420Lemma51

open Set Real Finset intervalIntegral

/-- `Q_L(β) = ∏_{ν=0}^{L-1} h(2^ν β)`. -/
noncomputable def Q (h : ℝ → ℝ) (L : ℕ) (β : ℝ) : ℝ := ∏ ν ∈ range L, h (2 ^ ν * β)

section
variable {h : ℝ → ℝ}

lemma Q_cont (hc : Continuous h) (L : ℕ) : Continuous (Q h L) :=
  continuous_finsetProd _ fun _ _ => hc.comp (continuous_const.mul continuous_id)

lemma Q_periodic (hp : Function.Periodic h 1) (L : ℕ) : Function.Periodic (Q h L) 1 := by
  intro β
  unfold Q
  refine Finset.prod_congr rfl fun ν _ => ?_
  have := (hp.nat_mul (2 ^ ν)) (2 ^ ν * β)
  rw [mul_add, mul_one]
  simpa [Nat.cast_pow] using this

lemma Q_succ (L : ℕ) (β : ℝ) : Q h (L + 1) β = h β * Q h L (2 * β) := by
  unfold Q
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun ν _ => ?_
    rw [pow_succ, mul_assoc]

/-- For a continuous 1-periodic `F`, `∫_0^1 F(2x) dx = ∫_0^1 F`. -/
lemma int_comp_two {F : ℝ → ℝ} (hc : Continuous F) (hp : Function.Periodic F 1) :
    ∫ x in (0 : ℝ)..1, F (2 * x) = ∫ x in (0 : ℝ)..1, F x := by
  rw [intervalIntegral.integral_comp_mul_left F two_ne_zero]
  rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * 1 = 2 by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h12 := hp.intervalIntegral_add_eq 1 0
  rw [show (1 : ℝ) + 1 = 2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at h12
  rw [h12, smul_eq_mul]
  ring

/-- The step of the proof of Lemma 5.1: `∫_0^1 h(x) F(2x) dx = ∫_0^1 F`. -/
lemma int_step (hhc : Continuous h) (hs : ∀ t, h t + h (t + 1 / 2) = 2) {F : ℝ → ℝ}
    (hc : Continuous F) (hp : Function.Periodic F 1) :
    ∫ x in (0 : ℝ)..1, h x * F (2 * x) = ∫ x in (0 : ℝ)..1, F x := by
  have hG : Continuous fun x => h x * F (2 * x) :=
    hhc.mul (hc.comp (continuous_const.mul continuous_id))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  have hshift := intervalIntegral.integral_comp_add_right (fun x => h x * F (2 * x))
    (a := 0) (b := 1 / 2) (1 / 2)
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 by norm_num, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
    at hshift
  rw [← hshift]
  have hF : ∀ x, F (2 * (x + 1 / 2)) = F (2 * x) := by
    intro x; rw [show 2 * (x + 1 / 2) = 2 * x + 1 by ring, hp]
  simp only [hF]
  have hG2 : Continuous fun x => h (x + 1 / 2) * F (2 * x) := by fun_prop
  rw [← intervalIntegral.integral_add (hG.intervalIntegrable 0 (1 / 2))
    (hG2.intervalIntegrable 0 (1 / 2))]
  have : ∀ x, h x * F (2 * x) + h (x + 1 / 2) * F (2 * x) = 2 * F (2 * x) := by
    intro x; rw [← add_mul, hs]
  simp only [this]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left F two_ne_zero]
  rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * (1 / 2) = 1 by ring, smul_eq_mul]
  ring

/-- Lemma 5.1, product form, `ν = 0, ..., L-1`: `∫_0^1 ∏_{ν<L} h(2^ν α) dα = 1`. -/
theorem int_prod_eq_one (hc : Continuous h) (hp : Function.Periodic h 1)
    (hs : ∀ t, h t + h (t + 1 / 2) = 2) (L : ℕ) : ∫ x in (0 : ℝ)..1, Q h L x = 1 := by
  induction L with
  | zero => simp [Q]
  | succ L ih =>
    simp only [Q_succ]
    rw [int_step hc hs (Q_cont hc L) (Q_periodic hp L), ih]

lemma prod_Icc_eq (L : ℕ) (α : ℝ) :
    ∏ ν ∈ Icc 1 L, h (2 ^ ν * α) = Q h L (2 * α) := by
  unfold Q
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_range_succ, ih, pow_succ, mul_assoc]

/-- Lemma 5.1, product form, `ν = 1, ..., L`. -/
theorem int_prod_Icc_eq_one (hc : Continuous h) (hp : Function.Periodic h 1)
    (hs : ∀ t, h t + h (t + 1 / 2) = 2) (L : ℕ) :
    ∫ x in (0 : ℝ)..1, ∏ ν ∈ Icc 1 L, h (2 ^ ν * x) = 1 := by
  simp only [prod_Icc_eq]
  rw [int_comp_two (Q_cont hc L) (Q_periodic hp L), int_prod_eq_one hc hp hs]

end

/-- **Lemma 5.1, display (43), PROVED.** For `w` real, continuous, 1-periodic with
`w(t + 1/2) = -w(t)`, and every `L`,
`∫_0^1 exp(∑_{ν=1}^{L} [w(2^ν α) - log cosh w(2^ν α)]) dα = 1`. -/
theorem lemma51 {w : ℝ → ℝ} (hc : Continuous w) (hp : Function.Periodic w 1)
    (ha : ∀ t, w (t + 1 / 2) = -w t) (L : ℕ) :
    ∫ α in (0 : ℝ)..1,
      Real.exp (∑ ν ∈ Icc 1 L, (w (2 ^ ν * α) - Real.log (Real.cosh (w (2 ^ ν * α))))) = 1 := by
  set h : ℝ → ℝ := fun t => Real.exp (w t - Real.log (Real.cosh (w t))) with hh
  have hhc : Continuous h :=
    Real.continuous_exp.comp (hc.sub ((Real.continuous_cosh.comp hc).log
      fun _ => (Real.cosh_pos _).ne'))
  have hhp : Function.Periodic h 1 := by intro t; simp only [hh, hp t]
  have hform : ∀ t, h t = Real.exp (w t) / Real.cosh (w t) := by
    intro t; simp only [hh]; rw [Real.exp_sub, Real.exp_log (Real.cosh_pos _)]
  have hhs : ∀ t, h t + h (t + 1 / 2) = 2 := by
    intro t
    rw [hform, hform, ha, Real.cosh_neg, ← add_div, Real.cosh_eq]
    have := Real.cosh_pos (w t)
    rw [Real.cosh_eq] at this
    field_simp
  have := int_prod_Icc_eq_one hhc hhp hhs L
  refine Eq.trans (intervalIntegral.integral_congr fun α _ => ?_) this
  simp only [hh]
  rw [Real.exp_sum]

end LeanLab.Linnik.U1420Lemma51
