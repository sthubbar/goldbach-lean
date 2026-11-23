module

public import LeanLab.ChenExplicit.Section9
public import LeanLab.ChenExplicit.GammaBounds
public import LeanLab.ChenExplicit.FIntegral
public import LeanLab.ChenExplicit.BJSCbar
public import LeanLab.ChenExplicit.TwinCNumeric

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0923.
P0009 BJS 2022, Section 9 with corrected constants, at `log log X₂ = 32.8`: the margins of
Section9.lean with `g = e^γ`, `T = twinC`, `c̄`, `LX = e^{32.8}` and the `F(c)` integral
discharged from proved lab lemmas. What stays a hypothesis: `ε₁ ≤ 1/57`, `ε₂ ≤ 1/51`,
`m(X₃) ≤ 2·10⁻¹¹`, and the X₂-only constants `l₁, l₁*, l, l*, c₄, c₄* ≤ 10⁻²⁰` and `a(X₂) ≤ 10⁻¹⁸`, all
TESTED in Python, numerics/section9_corrected_U0920.out; and the factor `w ≤ log N`.
These margins say the corrected Section 9 inequality holds at `exp(exp(32.8))`; Theorems 44, 50
and 51 themselves remain cited, so Chen at that threshold stays CONDITIONAL on them.
-/

@[expose] public section

open Real Finset

noncomputable section
namespace LeanLab.ChenExplicit.Section9

lemma g_ge : (1.781 : ℝ) ≤ exp eulerMascheroniConstant := by
  have hγ := Gamma.gamma_gt
  have h := Real.sum_le_exp_of_nonneg (x := (0.57720 : ℝ)) (by norm_num) 7
  have h2 : exp (0.57720 : ℝ) ≤ exp eulerMascheroniConstant := exp_le_exp.mpr hγ.le
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

lemma g_le : exp eulerMascheroniConstant ≤ (1.7812 : ℝ) := by
  have hγ := Gamma.gamma_lt
  have h := Real.exp_bound' (x := (0.57722 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  have h2 : exp eulerMascheroniConstant ≤ exp (0.57722 : ℝ) := exp_le_exp.mpr hγ.le
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

lemma LX_ge : (10 : ℝ) ^ 14 ≤ exp (328 / 10) := by
  have e : exp (328 / 10 : ℝ) = exp 1 ^ 32 * exp (8 / 10) := by
    rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 32
  have h2 : (1.8 : ℝ) ≤ exp (8 / 10) := by have := add_one_le_exp (8 / 10 : ℝ); linarith
  rw [e]
  have h3 : (2.7182818283 : ℝ) ^ 32 * 1.8 ≤ exp 1 ^ 32 * exp (8 / 10) :=
    mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (10 : ℝ) ^ 14 ≤ (2.7182818283 : ℝ) ^ 32 * 1.8 := by norm_num
  linarith

lemma I_le (LX : ℝ) (hLX : 10 ^ 14 ≤ LX) :
    ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t ≤ 0.1476 := by
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt.I3_le

/-- **Section 9 case (b), corrected, at `X₂ = exp(exp 32.8)`**, every analytic input discharged
except the stated numeric ones. -/
theorem margin_b_X2 (e1 e2 m a c4s w l1s ls L : ℝ)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (ha : 0 ≤ a ∧ a ≤ 1 / 10 ^ 18) (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hL : exp (328 / 10) ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb (exp eulerMascheroniConstant) twinC e1 a c4s w L (exp (328 / 10)) -
      cQb (exp eulerMascheroniConstant) twinC e1 l1s ls L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 :=
  margin_b _ _ e1 e2 _ m a c4s w l1s ls L _ g_ge g_le (by have := twinC_ge_065; norm_num at this ⊢; linarith)
    he1 he2 ⟨by have := BJS.cbar_gt; linarith, by have := BJS.cbar_lt; norm_num at this ⊢; linarith⟩
    hm ha hc4 hw hl1 hls LX_ge hL (I_le _ LX_ge)

/-- **Section 9 case (a), corrected, at `X₂ = exp(exp 32.8)`.** -/
theorem margin_a_X2 (e2 m c4 l1 l L : ℝ)
    (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20)
    (hL : exp (328 / 10) ≤ L) :
    1 / 10 ≤ cAa (exp eulerMascheroniConstant) twinC c4 L -
      cQa (exp eulerMascheroniConstant) twinC l1 l L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 :=
  margin_a _ _ e2 _ m c4 l1 l L _ g_ge g_le (by have := twinC_ge_065; norm_num at this ⊢; linarith)
    he2 ⟨by have := BJS.cbar_gt; linarith, by have := BJS.cbar_lt; norm_num at this ⊢; linarith⟩
    hm hc4 hl1 hls LX_ge hL

end LeanLab.ChenExplicit.Section9
