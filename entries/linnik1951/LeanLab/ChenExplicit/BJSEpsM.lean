module

public import LeanLab.ChenExplicit.BJSEps328
public import LeanLab.ChenExplicit.BJSmX3
public import LeanLab.ChenExplicit.BJSpLink

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 BJS 2022, arXiv 2207.09452 v6, read in Claude in Chrome: (121)
ε_i(X₂, δ) = 1/(p̄ - 2), with p̄ the largest prime such that log^δ x_i(X₂) ≥ ∏_{2<p≤p̄} p;
and Lemma 32 m(X₃) with v'₀(X₃) the max of (72). At log log X₂ = 32.8, δ = 1.476,
X₃ = X₂^{1/8}, x₂ read at X₃ per FINDING F-0022.

PROVED: p̄₁ = 59 so ε₁ = 1/57 exactly, and p̄₂ = 53 so ε₂ = 1/51 exactly, from the primorial
brackets of BJSEps328.lean; the supremum of (72) is at most 2.7·10⁻¹³ and m(X₃) ∈ [0, 2·10⁻¹¹]
from BJSmX3.lean. With these, `margin_a_final` has no hypothesis left beyond log N ≥ log X₂,
and `margin_b_final` only the factor w ≤ log N of Theorem 44 (b). Both stay CONDITIONAL ON
Theorems 44, 50 and 51 of BJS as corrected per F-0020 to F-0022, which remain cited.
Goldbach is open; this concerns the explicit constant in Chen's theorem.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSEm

open LeanLab.ChenExplicit.BJS

/-- p̄ of (121) for the bound B = log^δ x_i(X₂). -/
def pbar (B : ℝ) : ℕ := sSup {p : ℕ | p.Prime ∧ (oddPrimorial p : ℝ) ≤ B}

/-- (121) ε_i = 1/(p̄ - 2). -/
def eps (B : ℝ) : ℝ := 1 / ((pbar B : ℝ) - 2)

lemma oddPrimorial_mono {p q : ℕ} (h : p ≤ q) : oddPrimorial p ≤ oddPrimorial q := by
  unfold oddPrimorial
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩
  · intro x hx _
    exact (Finset.mem_filter.mp hx).2.1.one_lt.le

lemma pbar_eq (B : ℝ) (q r : ℕ) (hq : q.Prime) (hqB : (oddPrimorial q : ℝ) ≤ B)
    (hrB : B < oddPrimorial r) (hgap : ∀ p, q < p → p < r → ¬ p.Prime) : pbar B = q := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨hq, hqB⟩, ?_⟩
  rintro p ⟨hp, hpB⟩
  by_contra hc
  push Not at hc
  have hpr : p < r := by
    by_contra h2
    push Not at h2
    have := oddPrimorial_mono h2
    have : (oddPrimorial r : ℝ) ≤ oddPrimorial p := by exact_mod_cast this
    linarith
  exact hgap p hc hpr hp

theorem oddPrimorial_61 : oddPrimorial 61 = 58644190679703485491635 := by
  unfold oddPrimorial; decide

/-- log^δ x₁(X₂). -/
def B1 : ℝ := (exp (328 / 10) - 5 * (328 / 10)) ^ (1.476 : ℝ)
/-- log^δ x₂(X₃), X₃ = X₂^{1/8}. -/
def B2 : ℝ := (exp (328 / 10) / 8 - 15 * (328 / 10 - 3 * log 2)) ^ (1.476 : ℝ)

lemma B1_lt : B1 < oddPrimorial 61 := by
  unfold B1
  have hE := BJS328.exp_big' (328 / 10) (by norm_num)
  have hpos : 0 < exp (328 / 10) - 5 * (328 / 10 : ℝ) := by linarith
  have hl : log (exp (328 / 10) - 5 * (328 / 10 : ℝ)) ≤ 328 / 10 := by
    have := log_le_log hpos (show exp (328 / 10) - 5 * (328 / 10 : ℝ) ≤ exp (328 / 10) by linarith)
    rwa [log_exp] at this
  rw [rpow_def_of_pos hpos, oddPrimorial_61]
  have h1 : exp (log (exp (328 / 10) - 5 * (328 / 10 : ℝ)) * 1.476) ≤ exp 49 :=
    exp_le_exp.mpr (by nlinarith)
  have h2 : exp (49 : ℝ) = exp 1 ^ 49 := by rw [exp_one_pow]; norm_num
  have h3 : exp 1 ^ 49 ≤ (2.7182818286 : ℝ) ^ 49 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 49
  have h4 : (2.7182818286 : ℝ) ^ 49 < 58644190679703485491635 := by norm_num
  push_cast; linarith

theorem pbar1_eq : pbar B1 = 59 := by
  apply pbar_eq B1 59 61 (by norm_num) (by have := BJS328.pbar1_328; simpa [B1] using this) B1_lt
  intro p h1 h2
  interval_cases p; norm_num

theorem pbar2_eq : pbar B2 = 53 := by
  obtain ⟨a, b⟩ := BJS328.pbar2_328
  apply pbar_eq B2 53 59 (by norm_num) (by simpa [B2] using a) (by simpa [B2] using b)
  intro p h1 h2
  interval_cases p <;> norm_num

theorem eps1_eq : eps B1 = 1 / 57 := by unfold eps; rw [pbar1_eq]; norm_num
theorem eps2_eq : eps B2 = 1 / 51 := by unfold eps; rw [pbar2_eq]; norm_num

/-! ## m(X₃) with v'₀(X₃) the supremum of (72) -/

/-- v'₀(X₃), the max of (72) over y ≥ x₂(X₃), Y = log y. -/
def vS : ℝ := ⨆ Y : Set.Ici BJSm.ℓ, BJSm.φ Y

lemma phi_nonneg {Y : ℝ} (hY : BJSm.ℓ ≤ Y) : 0 ≤ BJSm.φ Y := by
  have hY0 : 0 < Y := BJSm.ℓ_pos.trans_le hY
  have hb : 0 < BJSm.β0 := by unfold BJSm.β0; have := BJSm.ν_le; linarith
  unfold BJSm.φ
  positivity

lemma vS_bounds : 0 ≤ vS ∧ vS ≤ 2.7 / 10 ^ 13 := by
  have : Nonempty (Set.Ici BJSm.ℓ) := ⟨⟨BJSm.ℓ, Set.mem_Ici.mpr le_rfl⟩⟩
  have hb : BddAbove (Set.range fun Y : Set.Ici BJSm.ℓ => BJSm.φ Y) :=
    ⟨2.7 / 10 ^ 13, by rintro _ ⟨Y, rfl⟩; exact BJSm.phi_le Y Y.2⟩
  exact ⟨(phi_nonneg le_rfl).trans (le_ciSup hb ⟨BJSm.ℓ, Set.mem_Ici.mpr le_rfl⟩),
    ciSup_le fun Y => BJSm.phi_le Y Y.2⟩

lemma mX3_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ BJSm.mX3 v := by
  have hΛ := BJSm.Λ3_ge
  have hℓ := BJSm.ℓ_pos
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ BJSm.ℓ := by
    have := BJSm.ℓ_bounds.1; nlinarith
  have h6 : 6 / BJSm.ℓ < 1 := by rw [div_lt_one hℓ]; norm_num at hℓ13; linarith
  have hq : 0 ≤ 1 / ((1 - 6 / BJSm.ℓ) * BJSm.Λ3) := by
    apply div_nonneg (by norm_num); apply mul_nonneg (by linarith) (by linarith)
  have hlog : 0 < log BJSm.Λ3 := log_pos (by linarith)
  have hΛ0 : 0 < BJSm.Λ3 := by linarith
  unfold BJSm.mX3 BJSm.v0
  set q := 1 / ((1 - 6 / BJSm.ℓ) * BJSm.Λ3)
  positivity

/-! ## The corrected Section 9 margins with every numeric input PROVED -/

open Section9 in
/-- **Section 9 case (a), corrected, at X₂ = exp(exp 32.8)**: every numeric input PROVED.
CONDITIONAL ON Theorems 44 (a), 50 (a), 51 as corrected, whose constants these are. -/
theorem margin_a_final (L : ℝ) (hL : exp (328 / 10) ≤ L) :
    1 / 10 ≤ cAa (exp eulerMascheroniConstant) twinC (BJSp.c4 BJSp.nu) L -
      cQa (exp eulerMascheroniConstant) twinC (BJSl.l1 (exp eulerMascheroniConstant) 106 BJSp.nu)
        (BJSp.l BJSp.nu) L (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC (eps B2) BJS.cbar (BJSm.mX3 vS) L / 2 := by
  obtain ⟨v0, v1⟩ := vS_bounds
  exact margin_a_X2_all _ _ L ⟨by rw [eps2_eq]; norm_num, by rw [eps2_eq]⟩
    ⟨mX3_nonneg v0, BJSm.m_le _ v0 v1⟩ hL

open Section9 in
/-- **Section 9 case (b), corrected, at X₂ = exp(exp 32.8)**: every numeric input PROVED;
left only the factor w ≤ log N of Theorem 44 (b). CONDITIONAL ON Theorems 44 (b), 50 (b), 51
as corrected. -/
theorem margin_b_final (w L : ℝ) (hw : 0 ≤ w ∧ w ≤ L) (hL : exp (328 / 10) ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb (exp eulerMascheroniConstant) twinC (eps B1)
        (BJSaX2.aX2 (exp eulerMascheroniConstant) twinC BJSc.c2term) (BJSp.c4 BJSp.nuS) w L
        (exp (328 / 10)) -
      cQb (exp eulerMascheroniConstant) twinC (eps B1)
        (BJSl.l1 (exp eulerMascheroniConstant) 106 BJSp.nuS) (BJSp.l BJSp.nuS) L
        (exp (328 / 10)) / 2 -
      cB (exp eulerMascheroniConstant) twinC (eps B2) BJS.cbar (BJSm.mX3 vS) L / 2 := by
  obtain ⟨v0, v1⟩ := vS_bounds
  exact margin_b_X2_all _ _ _ w L ⟨by rw [eps1_eq]; norm_num, by rw [eps1_eq]⟩
    ⟨by rw [eps2_eq]; norm_num, by rw [eps2_eq]⟩ ⟨mX3_nonneg v0, BJSm.m_le _ v0 v1⟩ hw hL


end LeanLab.ChenExplicit.BJSEm
