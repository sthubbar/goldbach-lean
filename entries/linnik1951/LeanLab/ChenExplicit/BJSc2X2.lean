module

public import LeanLab.ChenExplicit.BJSpX2
public import LeanLab.ChenExplicit.BJSaX2

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 BJS 2022, arXiv 2207.09452 v6, read in Claude in Chrome: Lemma 33 c₁(X₂), c(X₂) with
display (97); (127) c₂(X₂); and the first max of (139), the c₂ term of a₁(X₂). At
X₂ = exp(exp 32.8), δ = 1.476, R₁ = 2.0452.

PROVED: c₁(X₂) ≤ 10⁻³⁰, c₂(X₂) ≤ 10⁻²⁷, and the c₂ term of (139) ≤ 10⁻²⁰, so BJSaLink.lean's
last X₂-only analytic hypothesis besides l₁, l₁* is discharged. Reading choices, as in
BJSpX2.lean: y ≥ x₁(X₂) is written L = log y; y^{-a} = exp(-a L), Q₁(y) = L¹⁰,
y^{2/3} = exp(2L/3); the max over y is the supremum over L ≥ log x₁(X₂). In (139) N is written
t = log log N, as in BJSaX2.lean, with log^{10} x₁(N) = (exp t - 5t)^{10}.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSc

open BJSp

/-- (97) the bracket of c₁(X₂) at y = exp L, with 1/(2R₁ log Q₁(y)) for the exponent. -/
def br1 (L : ℝ) : ℝ :=
  3.2e-8 / L ^ 6 + L ^ 2 * ((1 - 1 / (2 * R1 * log (L ^ 10)))⁻¹ *
    exp (-(1 / (2 * R1 * log (L ^ 10)) * L)) +
    L ^ 10 * (1.02 / √(exp L) + 3 / exp (2 / 3 * L)) +
    9.4 * L ^ (1.515 : ℝ) * exp (-(0.8274 * √L)))

def c1 : ℝ := ⨆ L : Set.Ici Lx, br1 L

/-- Lemma 33, c(X₂). -/
def c : ℝ := c1 * (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) + 1 / LX ^ 2

/-- (127) c₂(X₂), with log log X₂ = 32.8. -/
def c2 : ℝ := c + 1.3841 * LX ^ 4 / (exp LX * 32.8)

/-- The bracket of the first max of (139) at N = exp(exp t). -/
def c2f (t : ℝ) : ℝ :=
  c2 / ((exp t) ^ (2 - δ) * log t) *
    (1.3841 * (10 * log (exp t - 5 * t)) / log (10 * log (exp t - 5 * t)))

/-- The c₂ term of (139). -/
def c2term : ℝ := sSup (c2f '' Set.Ici 32.8)

section Bounds
variable {L : ℝ} (hL : 1e14 ≤ L)
include hL

lemma br1_le : br1 L ≤ 1e-30 := by
  have hp := L_pos hL
  have hs1 := sqrtL_ge hL
  set s := √L with hs
  have hsL : L = s ^ 2 := (sq_sqrt hp.le).symm
  have hlog := logL_le hL
  have hlog1 : 1 ≤ log L := by
    rw [le_log_iff_exp_le hp]; have := exp_one_lt_d9; linarith
  have hl10 : log (L ^ 10) = 10 * log L := by rw [log_pow]; norm_num
  set ν := 1 / (2 * R1 * log (L ^ 10)) with hν
  have hνe : ν = 1 / (40.904 * log L) := by rw [hν, hl10]; unfold R1; ring
  have hν0 : 0 < ν := by rw [hνe]; positivity
  have hν2 : ν ≤ 1 / 2 := by
    rw [hνe, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinv : (1 - ν)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  -- ν L ≥ s / 81.808
  have hden : 40.904 * log L ≤ 81.808 * s := by
    have : 2 * √L = 2 * s := by rw [hs]
    linarith
  have hs0 : 0 < s := by linarith
  have hνL : s / 81.808 ≤ ν * L := by
    have e1 : ν * L = L / (40.904 * log L) := by rw [hνe]; field_simp
    have e2 : s / 81.808 = L / (81.808 * s) := by
      rw [hsL]; field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_left hp.le (by positivity) hden
  -- term 1
  have t1 : L ^ 2 * ((1 - ν)⁻¹ * exp (-(ν * L))) ≤ 1e-33 := by
    have hE : (s / 81.808) ^ 16 / 20922789888000 ≤ exp (ν * L) := by
      have := pow_div_factorial_le_exp (x := s / 81.808) (by positivity) 16
      have h2 := exp_le_exp.mpr hνL
      simp [Nat.factorial] at this; linarith
    rw [exp_neg]
    have hEp := exp_pos (ν * L)
    have : L ^ 2 * ((1 - ν)⁻¹ * (exp (ν * L))⁻¹) ≤ L ^ 2 * (2 * (exp (ν * L))⁻¹) := by
      gcongr
    refine this.trans ?_
    rw [← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ hEp]
    have h12 : (1e7 : ℝ) ^ 12 ≤ s ^ 12 := pow_le_pow_left₀ (by norm_num) hs1 12
    have e : (s / 81.808) ^ 16 / 20922789888000 = s ^ 16 / (81.808 ^ 16 * 20922789888000) := by ring
    rw [e] at hE
    have hL2 : L ^ 2 = s ^ 4 := by rw [hsL]; ring
    rw [hL2]
    have : s ^ 16 = s ^ 4 * s ^ 12 := by ring
    rw [this] at hE
    have h4 : 0 < s ^ 4 := by positivity
    have k : 2e33 * (81.808 ^ 16 * 20922789888000) ≤ s ^ 12 := by
      have : 2e33 * (81.808 ^ 16 * 20922789888000) ≤ (1e7 : ℝ) ^ 12 := by norm_num
      linarith
    have k2 : s ^ 4 * 2 ≤ 1e-33 * (s ^ 4 * s ^ 12 / (81.808 ^ 16 * 20922789888000)) := by
      rw [show 1e-33 * (s ^ 4 * s ^ 12 / (81.808 ^ 16 * 20922789888000)) =
        s ^ 4 * (s ^ 12 / (2e33 * (81.808 ^ 16 * 20922789888000))) * 2 by ring]
      have : 1 ≤ s ^ 12 / (2e33 * (81.808 ^ 16 * 20922789888000)) := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      nlinarith
    nlinarith
  -- term 2
  have t2 : L ^ 2 * (L ^ 10 * (1.02 / √(exp L) + 3 / exp (2 / 3 * L))) ≤ 1e-33 := by
    have e1 : √(exp L) = exp (L / 2) := (exp_half L).symm
    have h23 : exp (L / 2) ≤ exp (2 / 3 * L) := exp_le_exp.mpr (by linarith)
    have hE : (L / 2) ^ 16 / 20922789888000 ≤ exp (L / 2) := by
      have := pow_div_factorial_le_exp (x := L / 2) (by positivity) 16
      simpa [Nat.factorial] using this
    have hb : 1.02 / √(exp L) + 3 / exp (2 / 3 * L) ≤ 4.02 / exp (L / 2) := by
      rw [e1]
      have : 3 / exp (2 / 3 * L) ≤ 3 / exp (L / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (exp_pos _) h23
      have e2 : 4.02 / exp (L / 2) = 1.02 / exp (L / 2) + 3 / exp (L / 2) := by ring
      linarith
    have : L ^ 2 * (L ^ 10 * (1.02 / √(exp L) + 3 / exp (2 / 3 * L))) ≤
        L ^ 2 * (L ^ 10 * (4.02 / exp (L / 2))) := by gcongr
    refine this.trans ?_
    rw [show L ^ 2 * (L ^ 10 * (4.02 / exp (L / 2))) = 4.02 * L ^ 12 / exp (L / 2) by ring]
    rw [div_le_iff₀ (exp_pos _)]
    have e : (L / 2) ^ 16 / 20922789888000 = L ^ 16 / (2 ^ 16 * 20922789888000) := by ring
    rw [e] at hE
    have h4 : (1e14 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    have : L ^ 16 = L ^ 12 * L ^ 4 := by ring
    rw [this] at hE
    have := pow_pos hp 12
    nlinarith
  -- term 3
  have t3 : L ^ 2 * (9.4 * L ^ (1.515 : ℝ) * exp (-(0.8274 * s))) ≤ 1e-33 := by
    have hr : L ^ (1.515 : ℝ) ≤ L ^ 2 := by
      have := rpow_le_rpow_of_exponent_le (x := L) (by linarith) (show (1.515 : ℝ) ≤ 2 by norm_num)
      simpa using this
    have hE : (0.8274 * s) ^ 16 / 20922789888000 ≤ exp (0.8274 * s) := by
      have := pow_div_factorial_le_exp (x := 0.8274 * s) (by positivity) 16
      simpa [Nat.factorial] using this
    rw [exp_neg]
    have hEp := exp_pos (0.8274 * s)
    have : L ^ 2 * (9.4 * L ^ (1.515 : ℝ) * (exp (0.8274 * s))⁻¹) ≤
        L ^ 2 * (9.4 * L ^ 2 * (exp (0.8274 * s))⁻¹) := by gcongr
    refine this.trans ?_
    rw [show L ^ 2 * (9.4 * L ^ 2 * (exp (0.8274 * s))⁻¹) = 9.4 * L ^ 4 / exp (0.8274 * s) by
      field_simp]
    rw [div_le_iff₀ hEp]
    have hL4 : L ^ 4 = s ^ 8 := by rw [hsL]; ring
    rw [hL4]
    have e : (0.8274 * s) ^ 16 / 20922789888000 = s ^ 8 * (0.8274 ^ 16 * s ^ 8 / 20922789888000) := by ring
    rw [e] at hE
    have h8 : (1e7 : ℝ) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by norm_num) hs1 8
    have := pow_pos (show 0 < s by linarith) 8
    nlinarith
  have t0 : 3.2e-8 / L ^ 6 ≤ 1e-33 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1e14 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
    nlinarith
  unfold br1
  rw [← hν]
  have : L ^ 2 * ((1 - ν)⁻¹ * exp (-(ν * L)) + L ^ 10 * (1.02 / √(exp L) + 3 / exp (2 / 3 * L)) +
      9.4 * L ^ (1.515 : ℝ) * exp (-(0.8274 * s))) =
      L ^ 2 * ((1 - ν)⁻¹ * exp (-(ν * L))) +
      L ^ 2 * (L ^ 10 * (1.02 / √(exp L) + 3 / exp (2 / 3 * L))) +
      L ^ 2 * (9.4 * L ^ (1.515 : ℝ) * exp (-(0.8274 * s))) := by ring
  rw [this]
  linarith

lemma br1_nonneg : 0 ≤ br1 L := by
  have hp := L_pos hL
  have hlog1 : 1 ≤ log L := by
    rw [le_log_iff_exp_le hp]; have := exp_one_lt_d9; linarith
  have hl10 : log (L ^ 10) = 10 * log L := by rw [log_pow]; norm_num
  have hν2 : 1 / (2 * R1 * log (L ^ 10)) ≤ 1 / 2 := by
    rw [hl10, div_le_div_iff₀ (by unfold R1; positivity) (by norm_num)]; unfold R1; linarith
  have : 0 ≤ (1 - 1 / (2 * R1 * log (L ^ 10)))⁻¹ := inv_nonneg.mpr (by linarith)
  unfold br1
  positivity

end Bounds

lemma c1_le : c1 ≤ 1e-30 := by
  have : Nonempty (Set.Ici Lx) := ⟨⟨Lx, Set.mem_Ici.mpr le_rfl⟩⟩
  exact ciSup_le fun L => br1_le (Lx_ge.trans L.2)

lemma c1_nonneg : 0 ≤ c1 := by
  have hb : BddAbove (Set.range fun L : Set.Ici Lx => br1 L) :=
    ⟨1e-30, by rintro _ ⟨L, rfl⟩; exact br1_le (Lx_ge.trans L.2)⟩
  exact (br1_nonneg Lx_ge).trans (le_ciSup hb ⟨Lx, Set.mem_Ici.mpr le_rfl⟩)

lemma c_le : c ≤ 1e-28 := by
  unfold c
  have f := fac_le; have f0 := fac_nonneg; have a := c1_le; have b := c1_nonneg
  have h := LX_ge
  have t : 1 / LX ^ 2 ≤ 6e-29 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have : c1 * (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) ≤ 1e-30 * 3 :=
    mul_le_mul a f f0 (by norm_num)
  linarith

lemma c_nonneg : 0 ≤ c := by
  unfold c
  have f0 := fac_nonneg; have b := c1_nonneg; have h := LX_ge
  have : 0 < LX := by linarith
  positivity

lemma c2tail_le : 1.3841 * LX ^ 4 / (exp LX * 32.8) ≤ 1e-30 := by
  have h := LX_ge
  have hp : 0 < LX := by linarith
  have hE : LX ^ 8 / 40320 ≤ exp LX := by
    have := pow_div_factorial_le_exp (x := LX) hp.le 8
    simpa [Nat.factorial] using this
  rw [div_le_iff₀ (by positivity)]
  have h2 : (1.4e14 : ℝ) ^ 4 ≤ LX ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
  have : LX ^ 8 = LX ^ 4 * LX ^ 4 := by ring
  rw [this] at hE
  have := pow_pos hp 4
  nlinarith

/-- **(127) c₂(X₂) ≤ 10⁻²⁷.** -/
theorem c2_le : c2 ≤ 1e-27 := by
  unfold c2; have := c_le; have := c2tail_le; linarith

theorem c2_nonneg : 0 ≤ c2 := by
  unfold c2; have := c_nonneg; have h := LX_ge
  have : 0 < LX := by linarith
  have : 0 ≤ 1.3841 * LX ^ 4 / (exp LX * 32.8) := by positivity
  linarith

lemma c2f_le {t : ℝ} (ht : 32.8 ≤ t) : c2f t ≤ 1e-20 := by
  have hl := BJSaX2.logLx_le ht; have hl2 := BJSaX2.logLx_ge ht
  have hlt := BJSaX2.logt_ge ht
  have hc := c2_le; have hc0 := c2_nonneg
  -- (exp t)^(2-δ) ≥ t
  have hr : t ≤ (exp t) ^ (2 - δ) := by
    rw [← exp_mul]
    have := pow_div_factorial_le_exp (x := t * (2 - δ)) (by unfold δ; nlinarith) 2
    simp [Nat.factorial] at this
    unfold δ at this ⊢; nlinarith
  have hA : 1 ≤ log (10 * log (exp t - 5 * t)) := by
    rw [le_log_iff_exp_le (by linarith)]; have := exp_one_lt_d9; linarith
  have hd : 0 < (exp t) ^ (2 - δ) * log t := by
    apply mul_pos (by linarith) (by linarith)
  unfold c2f
  have hB : 1.3841 * (10 * log (exp t - 5 * t)) / log (10 * log (exp t - 5 * t)) ≤ 13.841 * t := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hB0 : 0 ≤ 1.3841 * (10 * log (exp t - 5 * t)) / log (10 * log (exp t - 5 * t)) := by
    apply div_nonneg (by nlinarith) (by linarith)
  have hC : c2 / ((exp t) ^ (2 - δ) * log t) ≤ c2 / (t * 3.4657) :=
    div_le_div_of_nonneg_left hc0 (by positivity) (mul_le_mul hr hlt (by norm_num) (by linarith))
  have hC0 : 0 ≤ c2 / ((exp t) ^ (2 - δ) * log t) := div_nonneg hc0 hd.le
  calc c2 / ((exp t) ^ (2 - δ) * log t) *
        (1.3841 * (10 * log (exp t - 5 * t)) / log (10 * log (exp t - 5 * t)))
      ≤ c2 / (t * 3.4657) * (13.841 * t) := mul_le_mul hC hB hB0 (by positivity)
    _ = c2 * (13.841 / 3.4657) := by field_simp
    _ ≤ 1e-27 * 4 := mul_le_mul hc (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 1e-20 := by norm_num

lemma c2f_nonneg {t : ℝ} (ht : 32.8 ≤ t) : 0 ≤ c2f t := by
  have hl2 := BJSaX2.logLx_ge ht; have hlt := BJSaX2.logt_ge ht
  have hc0 := c2_nonneg
  have hA : 1 ≤ log (10 * log (exp t - 5 * t)) := by
    rw [le_log_iff_exp_le (by linarith)]; have := exp_one_lt_d9; linarith
  unfold c2f
  apply mul_nonneg (div_nonneg hc0 (mul_nonneg (by positivity) (by linarith)))
  exact div_nonneg (by nlinarith) (by linarith)

/-- **The c₂ term of (139) is in [0, 10⁻²⁰].** -/
theorem c2term_bounds : 0 ≤ c2term ∧ c2term ≤ 1e-20 := by
  have hne : (c2f '' Set.Ici 32.8).Nonempty := ⟨_, ⟨32.8, Set.mem_Ici.mpr le_rfl, rfl⟩⟩
  have hb : BddAbove (c2f '' Set.Ici 32.8) := ⟨1e-20, by
    rintro _ ⟨t, ht, rfl⟩; exact c2f_le ht⟩
  refine ⟨(c2f_nonneg (le_refl _)).trans (le_csSup hb ⟨32.8, Set.mem_Ici.mpr le_rfl, rfl⟩), ?_⟩
  exact csSup_le hne (by rintro _ ⟨t, ht, rfl⟩; exact c2f_le ht)


end LeanLab.ChenExplicit.BJSc
