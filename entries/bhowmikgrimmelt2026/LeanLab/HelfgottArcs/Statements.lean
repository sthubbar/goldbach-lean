module

public import Mathlib
public import LeanLab.GRHComputations.Statements

/-!
Helfgott's minor and major arc bounds for the ternary Goldbach problem.
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4, Main Theorem,
  equations 1.1 to 1.4.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Theorems 1.1, 1.2,
  Corollary 1.3, Theorem 1.4, and the GRH input of section 1.2 from Platt.
Statements read from the v4 PDFs through a fetch tool that quotes at most 125 characters
at a time; the constants were read twice. QUESTIONS for VERIFY are listed in STATEMENTS.md.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HelfgottArcs
open LeanLab.GRHComputations
open scoped ArithmeticFunction

/-! ### Notation of both papers -/

/-- `e(t) = exp(2πit)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The Fourier transform, normalized as in 1305.2897: `f̂(t) = ∫ e(-xt) f(x) dx`. -/
noncomputable def fhat (f : ℝ → ℝ) (t : ℝ) : ℂ := ∫ y : ℝ, e (-(y * t)) * (f y : ℂ)

/-- Multiplicative convolution `(f *_M g)(t) = ∫_0^∞ f(y) g(t/y) dy/y`. -/
noncomputable def mconv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), f y * g (t / y) / y

/-- Equation 1.1 of 1205.5252: `S_η(α, x) = Σ Λ(n) e(αn) η(n/x)`. -/
noncomputable def S (η : ℝ → ℝ) (α x : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * e (α * n) * (η (n / x) : ℂ)

/-- Equation 1.8 of 1305.2897, the twisted sum `Σ Λ(n) χ(n) e(δn/x) η(n/x)`. -/
noncomputable def Schi {q : ℕ} (η : ℝ → ℝ) (χ : DirichletCharacter ℂ q) (δ x : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * e (δ * n / x) * (η (n / x) : ℂ)

/-! ### Weights. Weights live on `(0, ∞)`, as in "η : ℝ⁺ → ℂ"; we extend them by 0. -/

/-- Equation 1.4 of 1205.5252: `η₂(t) = 4 max(log 2 - |log 2t|, 0)`. -/
noncomputable def eta2 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

/-- `η₁ = 2 · 1_[1/2, 1]`. -/
noncomputable def eta1 (t : ℝ) : ℝ := Set.indicator (Set.Icc (1 / 2 : ℝ) 1) (fun _ => 2) t

/-- `η_♥(t) = e^{-t²/2}`. -/
noncomputable def etaHeart (t : ℝ) : ℝ := if 0 < t then Real.exp (-(t ^ 2) / 2) else 0

/-- `t² e^{-t²/2}`, the weight of Theorem 1.2. -/
noncomputable def etaT2 (t : ℝ) : ℝ := if 0 < t then t ^ 2 * Real.exp (-(t ^ 2) / 2) else 0

/-- `h(t) = t²(2-t)³ e^{t-1/2}` on `[0, 2]`, 0 elsewhere. -/
noncomputable def hfun (t : ℝ) : ℝ :=
  if 0 ≤ t ∧ t ≤ 2 then t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) else 0

/-- `F_H(y) = sin(H log y) / (π log y)`. -/
noncomputable def FH (H y : ℝ) : ℝ := Real.sin (H * Real.log y) / (Real.pi * Real.log y)

/-- `η₊(t) = h_H(t) t e^{-t²/2}` with `h_H = h *_M F_H`, `H = 200`. -/
noncomputable def etaPlus (t : ℝ) : ℝ :=
  if 0 < t then mconv hfun (FH 200) t * t * Real.exp (-(t ^ 2) / 2) else 0

/-! ### P0013, minor arcs -/

/-- Equation 1.3: `δ₀ = max(2, |δ|/4)`. -/
noncomputable def delta0 (δ : ℝ) : ℝ := max 2 (|δ| / 4)

/-- Equation 1.3: `R_{x,t}`. -/
noncomputable def R (x t : ℝ) : ℝ :=
  0.27125 * Real.log (1 + Real.log (4 * t) /
    (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t)))) + 0.41415

/-- Equation 1.3: `L_{x,δ,q}`. -/
noncomputable def L (x δ : ℝ) (q : ℕ) : ℝ :=
  min ((Real.log (δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) + 80 / 9) /
      ((Nat.totient q : ℝ) / q))
    (5 / 6 * Real.log x + 50 / 9)
  + Real.log ((q : ℝ) ^ ((80 : ℝ) / 9) * δ ^ ((16 : ℝ) / 9)) + 111 / 5

/-- The hypotheses of the Main Theorem: `x ≥ 2.16 · 10^20`, `2α = a/q + δ/x`, `q ≤ Q`,
`gcd(a, q) = 1`, `|δ/x| ≤ 1/(qQ)`, `Q = (3/4) x^{2/3}`. Note `2α`, as printed. -/
def MinorHyp (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) : Prop :=
  2.16e20 ≤ x ∧ 1 ≤ q ∧ 2 * α = a / q + δ / x ∧ (q : ℝ) ≤ 3 / 4 * x ^ ((2 : ℝ) / 3) ∧
    Int.gcd a q = 1 ∧ |δ / x| ≤ 1 / (q * (3 / 4 * x ^ ((2 : ℝ) / 3)))

/-- Bound 1.2, for `q ≤ x^{1/3}/6`. -/
noncomputable def minorBoundSmall (x δ : ℝ) (q : ℕ) : ℝ :=
  let d := delta0 δ
  (R x (d * q) * Real.log (d * q) + 0.5) / Real.sqrt (d * Nat.totient q) * x
    + 2.5 * x / Real.sqrt (d * q) + 2 * x / (d * q) * L x d q + 3.2 * x ^ ((5 : ℝ) / 6)

/-- The bound for `q > x^{1/3}/6`. -/
noncomputable def minorBoundLarge (x : ℝ) : ℝ :=
  0.2727 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) + 1218 * x ^ ((2 : ℝ) / 3) * Real.log x

/-! ### P0014, major arcs -/

/-- The GRH input as 1305.2897 section 1.2 states it: odd `q ≤ 3 · 10^5` to height
`10^8/q`, even `q ≤ 4 · 10^5` to height `max(10^8/q, 200 + 7.5 · 10^7/q)`. -/
def HelfgottInput : Prop :=
  ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      ((¬ Even q ∧ q ≤ 300000 ∧ |s.im| ≤ 10 ^ 8 / (q : ℝ)) ∨
        (Even q ∧ q ≤ 400000 ∧ |s.im| ≤ max (10 ^ 8 / (q : ℝ)) (200 + 7.5e7 / (q : ℝ)))) → s.re = 1 / 2

/-- Major arcs conclusion: `S = I_{q=1} η̂(-δ) x + E x` with `|E| ≤ B`. -/
def MajorShape {q : ℕ} (η : ℝ → ℝ) (χ : DirichletCharacter ℂ q) (δ x B : ℝ) : Prop :=
  ‖Schi η χ δ x - (if q = 1 then fhat η (-δ) * x else 0)‖ ≤ B * x

/-! ### Links, no unproved step -/

/-- Platt's verification, P0065, contains the input Helfgott cites. -/
theorem helfgottInput_of_platt (h : GRHCheck 400000 t0) : HelfgottInput := by
  unfold HelfgottInput
  intro q _ χ hχ s hs h0 h1 hcase
  rcases hcase with ⟨hodd, hq, him⟩ | ⟨hev, hq, him⟩
  · refine h q (hq.trans (by norm_num)) χ hχ s hs h0 h1 (him.trans ?_)
    unfold t0
    rw [if_neg hodd]
    exact le_max_left _ _
  · refine h q hq χ hχ s hs h0 h1 (him.trans (le_of_eq ?_))
    unfold t0
    rw [if_pos hev, add_comm]

/-- GRH implies the input. -/
theorem helfgottInput_of_GRH (hG : LeanLab.DERZ1997.GRH) : HelfgottInput :=
  helfgottInput_of_platt (grhCheck_of_GRH hG 400000 t0)

/-- The minor arcs `x₀` exceeds the major arcs thresholds. -/
theorem x0_ge : (10 : ℝ) ^ 12 ≤ 2.16e20 := by norm_num

open MeasureTheory Set

/-- The integrand of `η₁ *_M η₁` is `4/y` on `[max(1/2, t), min(1, 2t)]`. -/
theorem eta1_integrand (t : ℝ) (ht : 0 < t) :
    EqOn (fun y => eta1 y * eta1 (t / y) / y)
      ((Icc (max (1 / 2) t) (min 1 (2 * t))).indicator (fun y => 4 * y⁻¹)) (Ioi 0) := by
  intro y hy
  have hy : 0 < y := hy
  simp only [eta1, indicator, mem_Icc]
  have key : (1 / 2 ≤ t / y ∧ t / y ≤ 1) ↔ (t ≤ y ∧ y ≤ 2 * t) := by
    rw [le_div_iff₀ hy, div_le_iff₀ hy]
    constructor
    · rintro ⟨a, b⟩; constructor <;> linarith
    · rintro ⟨a, b⟩; constructor <;> linarith
  simp only [key]
  split_ifs <;>
    simp only [max_le_iff, le_min_iff] at * <;>
    first | (exfalso; tauto) | (field_simp; ring) | simp

/-- `∫_{y>0} 1_[a,b](y) · 4/y dy = 4 log(b/a)` for `0 < a ≤ b`, and `0` if `b < a`. -/
theorem integral_four_inv (a b : ℝ) (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), (Icc a b).indicator (fun y => 4 * y⁻¹) y =
      if a ≤ b then 4 * Real.log (b / a) else 0 := by
  rw [setIntegral_indicator measurableSet_Icc]
  have hs : Ioi (0 : ℝ) ∩ Icc a b = Icc a b :=
    inter_eq_right.mpr (fun y hy => lt_of_lt_of_le ha hy.1)
  rw [hs]
  split_ifs with hab
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab)]
  · rw [Icc_eq_empty hab]; simp

/-- `η₁ *_M η₁ = η₂` on `(0, ∞)`. -/
theorem eta2_eq_mconv (t : ℝ) (ht : 0 < t) : mconv eta1 eta1 t = eta2 t := by
  unfold mconv
  rw [setIntegral_congr_fun measurableSet_Ioi (eta1_integrand t ht),
    integral_four_inv _ _ (lt_max_of_lt_left (by norm_num))]
  unfold eta2
  rw [if_pos ht]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt t (1 / 2) with h | h
  · rw [max_eq_left h]
    have hlog : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    rw [abs_of_nonpos hlog]
    rcases le_or_gt (1 / 4) t with h4 | h4
    · rw [min_eq_right (by linarith), if_pos (by linarith)]
      have : Real.log (2 * t / (1 / 2)) = Real.log 2 + Real.log (2 * t) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
      have h5 : Real.log (1 / 2) ≤ Real.log (2 * t) :=
        Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h5
      rw [this, max_eq_left (by linarith)]; ring
    · rw [min_eq_right (by linarith), if_neg (by linarith)]
      have : Real.log (2 * t) ≤ Real.log (1 / 2) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at this
      rw [max_eq_right (by linarith)]; ring
  · rw [max_eq_right h.le]
    have hlog : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg hlog, min_eq_left (by linarith)]
    rcases le_or_gt t 1 with h1 | h1
    · rw [if_pos h1]
      rw [Real.log_div (by norm_num) (by linarith), Real.log_one,
        Real.log_mul (by norm_num) (by linarith), max_eq_left]
      · ring
      · linarith [Real.log_nonpos ht.le h1]
    · rw [if_neg (by linarith)]
      have : Real.log 2 < Real.log (2 * t) := Real.log_lt_log (by norm_num) (by linarith)
      rw [max_eq_right (by linarith)]; ring

end LeanLab.HelfgottArcs
