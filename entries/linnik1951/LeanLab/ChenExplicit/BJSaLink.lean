module

public import LeanLab.ChenExplicit.Section9Link
public import LeanLab.ChenExplicit.BJSaX2

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0803Z-19871, unit U-0930.
P0009 BJS 2022, Section 9 case (b) at X₂ = exp(exp 32.8) with a(X₂) of (138) discharged by
BJSaX2.lean: the `a` hypothesis of `margin_b_X2` is now PROVED, given the `c₂` term of (139)
in [0, 10⁻²⁰]. What stays a hypothesis: ε₁, ε₂, m(X₃), whose brackets BJSEps328.lean and
BJSmX3.lean prove, and the X₂-only constants c₄*, l₁*, l*, the c₂ term, and w ≤ log N.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Section9

theorem margin_b_X2_a (e1 e2 m c2s c4s w l1s ls L : ℝ)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hc2 : 0 ≤ c2s ∧ c2s ≤ 1e-20) (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hL : exp (328 / 10) ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb (exp eulerMascheroniConstant) twinC e1
        (BJSaX2.aX2 (exp eulerMascheroniConstant) twinC c2s) c4s w L (exp (328 / 10)) -
      cQb (exp eulerMascheroniConstant) twinC e1 l1s ls L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 := by
  have hg0 : 0 ≤ exp eulerMascheroniConstant := (exp_pos _).le
  have hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith
  have ha1 := BJSaX2.aX2_le hg0 g_le hT hc2.2
  have ha0 := BJSaX2.aX2_nonneg hg0 g_le hT hc2.1
  exact margin_b_X2 e1 e2 m _ c4s w l1s ls L he1 he2 hm
    ⟨ha0, by norm_num at ha1 ⊢; linarith⟩ hc4 hw hl1 hls hL


end LeanLab.ChenExplicit.Section9
