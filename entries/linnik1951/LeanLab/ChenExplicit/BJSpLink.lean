module

public import LeanLab.ChenExplicit.BJSaLink
public import LeanLab.ChenExplicit.BJSpX2
public import LeanLab.ChenExplicit.BJSc2X2
public import LeanLab.ChenExplicit.BJSl1X2

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 BJS 2022, Section 9 at X₂ = exp(exp 32.8): the margins of Section9Link.lean and
BJSaLink.lean with c₄(X₂), l(X₂) of (134), (156) and c₄*(X₂), l*(X₂) of (135), (157)
discharged by BJSpX2.lean, which PROVES each ≤ 10⁻²⁰ from Lemma 31 (87) and (99), and in
`margin_b_X2_pc` also the c₂ term of (139), by BJSc2X2.lean.
What stays a hypothesis: ε₁ ≤ 1/57, ε₂ ≤ 1/51, m(X₃) ≤ 2·10⁻¹¹, whose brackets BJSEps328.lean
and BJSmX3.lean prove; l₁, l₁* of (158), (159), which carry the sieve constants k_{α₂}, C₁(ε),
h(k); the c₂ term of (139); and w ≤ log N. Theorems 44, 50 and 51 stay cited, so Chen at
this threshold stays CONDITIONAL on them. Goldbach is open.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Section9

/-- **Section 9 case (a), corrected, at exp(exp 32.8)**, with c₄ and l PROVED. -/
theorem margin_a_X2_p (e2 m l1 L : ℝ)
    (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hL : exp (328 / 10) ≤ L) :
    1 / 10 ≤ cAa (exp eulerMascheroniConstant) twinC (BJSp.c4 BJSp.nu) L -
      cQa (exp eulerMascheroniConstant) twinC l1 (BJSp.l BJSp.nu) L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 := by
  have g := BJSp.nu_good
  have c1 := BJSp.c4_le g; have c0 := BJSp.c4_nonneg g
  have l1' := BJSp.l_le g; have l0 := BJSp.l_nonneg g
  exact margin_a_X2 e2 m _ l1 _ L he2 hm ⟨c0, by norm_num at c1 ⊢; linarith⟩ hl1
    ⟨l0, by norm_num at l1' ⊢; linarith⟩ hL

/-- **Section 9 case (b), corrected, at exp(exp 32.8)**, with a(X₂), c₄* and l* PROVED. -/
theorem margin_b_X2_p (e1 e2 m c2s w l1s L : ℝ)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hc2 : 0 ≤ c2s ∧ c2s ≤ 1e-20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hL : exp (328 / 10) ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb (exp eulerMascheroniConstant) twinC e1
        (BJSaX2.aX2 (exp eulerMascheroniConstant) twinC c2s) (BJSp.c4 BJSp.nuS) w L
        (exp (328 / 10)) -
      cQb (exp eulerMascheroniConstant) twinC e1 l1s (BJSp.l BJSp.nuS) L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 := by
  have g := BJSp.nuS_good
  have c1 := BJSp.c4_le g; have c0 := BJSp.c4_nonneg g
  have l1' := BJSp.l_le g; have l0 := BJSp.l_nonneg g
  exact margin_b_X2_a e1 e2 m c2s _ w l1s _ L he1 he2 hm hc2
    ⟨c0, by norm_num at c1 ⊢; linarith⟩ hw hl1 ⟨l0, by norm_num at l1' ⊢; linarith⟩ hL

/-- **Section 9 case (b), corrected, at exp(exp 32.8)**, with a(X₂) including its c₂ term of
(139), c₄* and l* all PROVED, BJSc2X2.lean. Left as hypotheses: ε₁, ε₂, m(X₃), l₁* and w ≤ log N. -/
theorem margin_b_X2_pc (e1 e2 m w l1s L : ℝ)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hL : exp (328 / 10) ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb (exp eulerMascheroniConstant) twinC e1
        (BJSaX2.aX2 (exp eulerMascheroniConstant) twinC BJSc.c2term) (BJSp.c4 BJSp.nuS) w L
        (exp (328 / 10)) -
      cQb (exp eulerMascheroniConstant) twinC e1 l1s (BJSp.l BJSp.nuS) L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 :=
  margin_b_X2_p e1 e2 m _ w l1s L he1 he2 hm BJSc.c2term_bounds hw hl1 hL

lemma g0 : 0 ≤ exp eulerMascheroniConstant := (exp_pos _).le

/-- **Section 9 case (a), corrected, at exp(exp 32.8), every X₂-only constant PROVED**:
c₄, l of (134), (156) and l₁ of (158) with C₁(ε) = 106. Left: ε₂ ≤ 1/51 and m(X₃) ≤ 2·10⁻¹¹. -/
theorem margin_a_X2_all (e2 m L : ℝ)
    (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11) (hL : exp (328 / 10) ≤ L) :
    1 / 10 ≤ cAa (exp eulerMascheroniConstant) twinC (BJSp.c4 BJSp.nu) L -
      cQa (exp eulerMascheroniConstant) twinC (BJSl.l1 (exp eulerMascheroniConstant) 106 BJSp.nu)
        (BJSp.l BJSp.nu) L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 := by
  obtain ⟨a, b⟩ := BJSl.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106) (by norm_num : (106:ℝ) ≤ 1e6) BJSp.nu_good
  exact margin_a_X2_p e2 m _ L he2 hm ⟨a, by norm_num at b ⊢; linarith⟩ hL

/-- **Section 9 case (b), corrected, at exp(exp 32.8), every X₂-only constant PROVED**:
a(X₂) with its c₂ term, c₄*, l*, l₁* with C₁(ε) = 106. Left: ε₁ ≤ 1/57, ε₂ ≤ 1/51,
m(X₃) ≤ 2·10⁻¹¹ and the factor w ≤ log N of Theorem 44 (b). -/
theorem margin_b_X2_all (e1 e2 m w L : ℝ)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hw : 0 ≤ w ∧ w ≤ L) (hL : exp (328 / 10) ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb (exp eulerMascheroniConstant) twinC e1
        (BJSaX2.aX2 (exp eulerMascheroniConstant) twinC BJSc.c2term) (BJSp.c4 BJSp.nuS) w L
        (exp (328 / 10)) -
      cQb (exp eulerMascheroniConstant) twinC e1
        (BJSl.l1 (exp eulerMascheroniConstant) 106 BJSp.nuS) (BJSp.l BJSp.nuS) L
        (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC e2 BJS.cbar m L / 2 := by
  obtain ⟨a, b⟩ := BJSl.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106) (by norm_num : (106:ℝ) ≤ 1e6) BJSp.nuS_good
  exact margin_b_X2_pc e1 e2 m w _ L he1 he2 hm hw ⟨a, by norm_num at b ⊢; linarith⟩ hL


end LeanLab.ChenExplicit.Section9
