module

public import LeanLab.ChenExplicit.Assembly
public import LeanLab.ChenExplicit.BJSEpsM

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 BJS 2022 Theorem 3 at a general threshold exp(exp t), t ≥ 32.7, and at t = 32.8 with
the corrected Section 9 constants. The proof of `BJS3At_of_sieveBounds` is Assembly.lean's
`BJS3_of_sieveBounds` with the threshold as a parameter, run 20261016T1803Z-2621.

`chen_328` is CONDITIONAL ON BJS Theorems 44, 50, 51 with their constants as CORRECTED per
FINDINGS F-0020, F-0021, F-0022, for any split of the even N into the paper's case (a),
k₁ < K_δ(x₁), and case (b), and any factor w(N) ∈ [0, log N] of Theorem 44 (b). Every numeric
input of Section 9 is PROVED in this lab: BJSEpsM.lean `margin_a_final`, `margin_b_final`.
So: if the three sieve theorems hold as corrected, every even N > exp(exp 32.8) has more than
2·10⁻⁴ U_N N / log² N representations as a prime plus a number with at most two prime factors.
The paper's own threshold exp(exp 32.7) does not follow from its printed argument, FINDING
F-0023. Theorems 44, 50, 51 remain cited, not proved. Goldbach is open; Chen's theorem itself is
not in doubt, only the explicit threshold.
-/

@[expose] public section

open Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

/-- BJS Theorem 3 at threshold exp(exp t). -/
def BJS3At (t : ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 < chenCount N

def Thm44At (t : ℝ) (cA : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → cA N * mainTerm N < SA N (zN N)

def Thm50At (t : ℝ) (cQ : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → (sumSAq N (zN N) (yN N) : ℝ) < cQ N * mainTerm N

def Thm51At (t : ℝ) (cB : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → (SB N (zN N) (yN N) : ℝ) < cB N * mainTerm N

def MarginAt (t : ℝ) (cA cQ cB : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → 2 / 10000 + 1 / 10 ^ 12 ≤ cA N - cQ N / 2 - cB N / 2

theorem BJS3At_of_sieveBounds (t : ℝ) (ht : 327 / 10 ≤ t) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginAt t cA cQ cB) :
    BJS3At t := by
  intro N hEven hNt
  have hN : exp (exp (327 / 10)) < (N : ℝ) :=
    lt_of_le_of_lt (exp_le_exp.mpr (exp_le_exp.mpr ht)) hNt
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp (327 / 10) < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_32_7_gt
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  have h1 := hA N hEven hNt
  have h2 := hQ N hEven hNt
  have h3 := hB N hEven hNt
  have hmN := hm N hEven hNt
  have hU := U_ge N
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 < mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  -- the error terms of Lemma 37
  have hE : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * mainTerm N := by
    have hbig := big_exp L hL.le
    have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
      rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
    have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
    have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
    have hM : 1 / 1000 * exp L / L ^ 2 ≤ mainTerm N := by
      simp only [mainTerm]; rw [← hLdef, ← hNe]
      apply div_le_div_of_nonneg_right _ hL2.le
      rw [hNe]; exact mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h7 := exp_pos (7 * L / 8)
    have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
      rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
        exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
    linarith
  have hfin := mul_le_mul_of_nonneg_right hmN hM0.le
  have hgoal : (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 = 2 / 10000 * mainTerm N := by
    simp only [mainTerm]; ring
  rw [hgoal]
  nlinarith


open Section9 BJSEm

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.8): case (a) or case (b). -/
def cA328 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAa gE twinC (BJSp.c4 BJSp.nu) (Real.log N)
  else cAb gE twinC (eps B1) (BJSaX2.aX2 gE twinC BJSc.c2term) (BJSp.c4 BJSp.nuS) (w N)
    (Real.log N) (exp (328 / 10))

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.8), C₁(ε) = 106. -/
def cQ328 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQa gE twinC (BJSl.l1 gE 106 BJSp.nu) (BJSp.l BJSp.nu) (Real.log N) (exp (328 / 10))
  else cQb gE twinC (eps B1) (BJSl.l1 gE 106 BJSp.nuS) (BJSp.l BJSp.nuS) (Real.log N)
    (exp (328 / 10))

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}. -/
def cB328 (N : ℕ) : ℝ := cB gE twinC (eps B2) BJS.cbar (BJSm.mX3 vS) (Real.log N)

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.8)**, PROVED. -/
theorem margin_328 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (328 / 10) (cA328 caseA w) (cQ328 caseA) cB328 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : exp (328 / 10) ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA328 cQ328 cB328
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_a_final (Real.log N) hL
    linarith
  · simp only [hc, ite_false]
    exact margin_b_final (w N) (Real.log N) (hw N) hL

/-- **BJS Theorem 3 at exp(exp 32.8), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_328 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (328 / 10) (cA328 caseA w)) (hQ : Thm50At (328 / 10) (cQ328 caseA))
    (hB : Thm51At (328 / 10) cB328) : BJS3At (328 / 10) :=
  BJS3At_of_sieveBounds _ (by norm_num) _ _ _ hA hQ hB (margin_328 caseA w hw)


end LeanLab.ChenExplicit
