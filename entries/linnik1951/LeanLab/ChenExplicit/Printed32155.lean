module

public import LeanLab.ChenExplicit.AssemblyT32155

/-!
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T0103Z-19411, unit U-1310, track T2 FRONTIER.
P0009 BJS 2022, arXiv 2207.09452 v6, /home/claude/ctx/P0009.txt: Chen at exp(exp 32.155) from the
PRINTED Theorems 44, 50, 51, with α₁ = α₂ = α₃ = αP = 1.09·10⁻⁵ as a parameter.

Printed3225.chen_3225_printed rests on Theorems 44, 50, 51 as printed, u₀ = 10⁹, ε = 1.452·10⁻⁷,
C₁ = 106, C₂ = 107, at α = 10⁻⁵. Below log log X₂ ≈ 32.236 the printed u₀ condition
N^α / (log¹⁰ x₁ log^2.5 N) ≥ exp(u₀(1 + 9·10⁻⁷/log u₀)) of Theorems 44 and 50, p. 42 and p. 51,
and 3¹⁰ N^α₃ / log¹⁰ N ≥ the same of Theorem 51, p. 56, fail at α = 10⁻⁵. The three theorems take
α₁ > 0, 0 < α₂ < 1/24, 0 < α₃ < 1/6 as free parameters, so here α = 1.09·10⁻⁵, above
α_min(32.155) ≈ 1.0846·10⁻⁵, numerics/alpha_scan_U1310.py.

* `ccA`, `kA`, `l2A`, `l1A`, `cAaA`, `cAbA`, `cQaA`, `cQbA`, `cBA`: the corrected Section 9 constants with
  α and ε as arguments; at α = 10⁻⁵ they are the chain's constants by rfl, `*_eqU`, `*_eqP`.
* Numeric bounds at α = αP, ε = 1.452·10⁻⁷, log X₂ ≥ 9·10¹³, all PROVED: `fS_c_ge` with 0.5493035
  in place of 0.54930376, `Lam_le` with 3.5836698 in place of 3.583658, `l1A_bounds`, `cB_le`.
* `margin_bA`, `margin_aA`, `margin_32155_printed`: the Section 9 margin, PROVED unconditional,
  case (b) slack about 2.5·10⁻⁵ over 2·10⁻⁴ + 10⁻¹² by the model of the Lean bounds.
* `u0cond_44_50_A`, `u0cond_51_A`, `ranges_A`: the printed u₀ = 10⁹ conditions at α = αP for every
  log N ≥ 9.21·10¹³, PROVED.
* `chen_32155_printed`: CONDITIONAL ON Thm44At, Thm50At, Thm51At at t = 32.155 with the printed
  u₀ = 10⁹, ε = 1.452·10⁻⁷, C₁ = 106, C₂ = 107, α₁ = α₂ = α₃ = 1.09·10⁻⁵, corrected per F-0020 to F-0022,
  δ₁ = 1.5026 for 44 and 50, δ₂ = 1.47088 and ε₀ = 1.45·10⁻⁴ for 51, the X₂-only constants of
  AssemblyT32155. No Lemma 17 input.
Chen's theorem is not in doubt; Goldbach is open.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Printed32155

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.Section9U8 LeanLab.ChenExplicit.Section9F9

/-- α₁ = α₂ = α₃ = 1.09·10⁻⁵. -/
abbrev αP : ℝ := 109 / 10 ^ 7

/-! ### The constants with α and ε as arguments -/

/-- `c_{α₁,X₂}`, (136), with `log log X₂ = ll`. -/
def ccA (a ll LX : ℝ) : ℝ := 4 - 8 * a - 160 * ll / LX

/-- `k_{α₂} = 8(1/6 - α₂)`, (155). -/
def kA (a : ℝ) : ℝ := 8 * (1 / 6 - a)

/-- `l₂(X₂)`, (160). -/
def l2A (a e g LX : ℝ) : ℝ :=
  exp (LX / 8) / (exp (LX / 8) - 1) *
    (g / 4 * ((log 6 + log ((3 - 8 * a) / (3 - 18 * a))) / (1 / 2 - a) + 512 / (kA a * LX ^ 2)) +
      (log (8 / 3) + 64 / LX ^ 2) * e * 106 * exp 2 * h (kA a))

/-- `l₁(X₂)`, (158), (159), at X₂ = exp(exp 32.155). -/
def l1A (a e g C1 ν : ℝ) : ℝ :=
  BJSp32155.LX ^ 2 / exp BJSp32155.LX * (2 * g / kA a + e * C1 * exp 2 * h (kA a)) *
    (exp (BJSp32155.LX / 8) / (exp (BJSp32155.LX / 8) - 1) * (log (8 / 3) + 64 / BJSp32155.LX ^ 2) *
      (1.3841 / 32.155) + BJSp32155.p ν * exp BJSp32155.LX / BJSp32155.LX ^ 4)

/-- Theorem 44 (a), corrected per F-0020. -/
def cAaA (a e g T c4 L : ℝ) : ℝ :=
  8 * (1 - 32.02 / L ^ 2) * (fS g (4 - 8 * a) - 107 * e * exp 2 * h (4 - 8 * a) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L))

/-- Theorem 44 (b), corrected. -/
def cAbA (a e ll g T e1 aa c4s w L LX : ℝ) : ℝ :=
  8 * (1 + 32.02 / L ^ 2) * (fS g (ccA a ll LX) - e1 * (1 - fS g (ccA a ll LX)) -
    (1 + e1) * e * 107 * exp 2 * h (ccA a ll LX) -
    (3 * e1 + aa) * (max (1 - fS g (ccA a ll LX)) (FS g (ccA a ll LX) - 1) +
      e * 107 * exp 2 * h (ccA a ll LX)) -
    aa - 64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w)

/-- Theorem 50 (a), with the factor of F-0021. -/
def cQaA (a e g T l1 l L LX : ℝ) : ℝ :=
  8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2A a e g LX) + l * (g / (2 * T))

/-- Theorem 50 (b). -/
def cQbA (a e g T e1 l1s ls L LX : ℝ) : ℝ :=
  8.0004 * (1 + 32.02 / L ^ 2) * (1 + e1) * (l1s + l2A a e g LX) + ls * (g / (2 * T))

/-- Theorem 51, corrected per F-0022. -/
def cBA (a e e0 g T e2 cb m L : ℝ) : ℝ :=
  1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) *
      (2 / (1 / 2 - a) * g + 3 * e * 106 * exp 2 * h (3 / 2 - 3 * a)) * (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) +
    g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)))

/-! ### Faithfulness: at α = 10⁻⁵ these are the chain's constants -/

theorem ccA_eq (ll LX : ℝ) : ccA α ll LX = ccP ll LX := rfl
theorem l2A_eqU (g LX : ℝ) : l2A α εU g LX = l2U g LX := rfl
theorem l2A_eqP (g LX : ℝ) : l2A α Section9.ε g LX = Section9.l2 g LX := rfl
theorem l1A_eqU (g C1 ν : ℝ) : l1A α εU g C1 ν = BJSl32155.l1 g C1 ν := rfl
theorem cAaA_eqU (g T c4 L : ℝ) : cAaA α εU g T c4 L = cAaU g T c4 L := rfl
theorem cAaA_eqP (g T c4 L : ℝ) : cAaA α Section9.ε g T c4 L = Section9.cAa g T c4 L := rfl
theorem cAbA_eqU (ll g T e1 aa c4s w L LX : ℝ) :
    cAbA α εU ll g T e1 aa c4s w L LX = cAbPU ll g T e1 aa c4s w L LX := rfl
theorem cAbA_eqP (ll g T e1 aa c4s w L LX : ℝ) :
    cAbA α Section9.ε ll g T e1 aa c4s w L LX = F0023.cAbP ll g T e1 aa c4s w L LX := rfl
theorem cQaA_eqU (g T l1 l L LX : ℝ) : cQaA α εU g T l1 l L LX = cQaU g T l1 l L LX := rfl
theorem cQbA_eqU (g T e1 l1s ls L LX : ℝ) :
    cQbA α εU g T e1 l1s ls L LX = cQbU g T e1 l1s ls L LX := rfl
theorem cBA_eqU (e0 g T e2 cb m L : ℝ) : cBA α εU e0 g T e2 cb m L = cBPU e0 g T e2 cb m L := rfl
theorem cBA_eqP (e0 g T e2 cb m L : ℝ) :
    cBA α Section9.ε e0 g T e2 cb m L = F0023.cBP e0 g T e2 cb m L := rfl

/-! ### Numeric bounds at α = αP, ε = 1.452·10⁻⁷ -/

lemma kA_bounds : 1.3 ≤ kA αP ∧ kA αP ≤ 2 := by unfold kA; norm_num

lemma cc_bounds (LX : ℝ) (hLX : 9 * 10 ^ 13 ≤ LX) :
    3.9999 ≤ ccA αP (32155 / 1000) LX ∧ ccA αP (32155 / 1000) LX ≤ 3.9999128 := by
  unfold ccA
  have hpos : 0 < 160 * (32155 / 1000) / LX := by positivity
  have hx : 160 * (32155 / 1000) / LX ≤ 10 ^ (-10 : ℤ) := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  norm_num at hx ⊢; constructor <;> linarith

lemma log_cm1_ge (LX : ℝ) (hLX : 9 * 10 ^ 13 ≤ LX) :
    1.09858322 ≤ log (ccA αP (32155 / 1000) LX - 1) := by
  unfold ccA
  have hx : 160 * (32155 / 1000) / LX ≤ 10 ^ (-10 : ℤ) := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  have hpos : 0 < 160 * (32155 / 1000) / LX := by positivity
  set d := 160 * (32155 / 1000) / LX
  have e : 4 - 8 * αP - d - 1 = 3 * (1 - (8 * αP + d) / 3) := by ring
  rw [e, log_mul (by norm_num) (by norm_num at hx ⊢; nlinarith)]
  have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 - (8 * αP + d) / 3) (by norm_num at hx ⊢; nlinarith)
  have l3 := log_three_gt_d9
  have h2 : 1 - (1 - (8 * αP + d) / 3)⁻¹ ≥ -0.000029068 := by
    have hy : 0.99997 ≤ 1 - (8 * αP + d) / 3 := by norm_num at hx ⊢; nlinarith
    have : (1 - (8 * αP + d) / 3)⁻¹ ≤ 1 + 0.000029068 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      have : (8 * αP + d) / 3 ≤ 0.0000290667 + 0.0000000001 := by norm_num at hx ⊢; nlinarith
      rw [inv_eq_one_div, div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  norm_num at l3 ⊢; linarith

lemma fS_c_ge (g LX : ℝ) (hg : 0 ≤ g) (hLX : 9 * 10 ^ 13 ≤ LX) :
    g * 0.5493035 ≤ fS g (ccA αP (32155 / 1000) LX) := by
  unfold fS
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  have hl := log_cm1_ge LX hLX
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hl hg, mul_le_mul_of_nonneg_left c2 hg]

lemma fS_c_le (g LX : ℝ) (hg : 0 ≤ g) (hLX : 9 * 10 ^ 13 ≤ LX) :
    fS g (ccA αP (32155 / 1000) LX) ≤ g * 0.5494 := by
  unfold fS
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  have hl : log (ccA αP (32155 / 1000) LX - 1) ≤ log 3 := log_le_log (by linarith) (by linarith)
  have l3 := log_three_lt_d9
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ log (ccA αP (32155 / 1000) LX - 1) := log_nonneg (by linarith)
  norm_num at l3 ⊢
  nlinarith

lemma fS_a_ge (g : ℝ) (hg : 0 ≤ g) : g * 0.5493035 ≤ fS g (4 - 8 * αP) := by
  unfold fS
  have e : (4 - 8 * αP - 1 : ℝ) = 3 * (1 - 8 * αP / 3) := by ring
  rw [e, log_mul (by norm_num) (by norm_num)]
  have h1 := Real.one_sub_inv_le_log_of_pos (x := (1 - 8 * αP / 3 : ℝ)) (by norm_num)
  have l3 := log_three_gt_d9
  norm_num at h1 l3 ⊢
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma hI_A (LX : ℝ) (hLX : 9 * 10 ^ 13 ≤ LX) :
    ∫ t in (2 : ℝ)..(ccA αP (32155 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma mbar_le (g LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hLX : 9 * 10 ^ 13 ≤ LX) :
    max (1 - fS g (ccA αP (32155 / 1000) LX)) (FS g (ccA αP (32155 / 1000) LX) - 1) ≤ 0.02177 := by
  have h1 := fS_c_ge g LX (by linarith) hLX
  have hI := hI_A LX hLX
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  apply max_le
  · nlinarith
  · unfold FS
    have hgc : 2 * g / ccA αP (32155 / 1000) LX ≤ 2 * 1.7812 / 3.9999 := by
      apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) c1
    have hgc0 : 0 ≤ 2 * g / ccA αP (32155 / 1000) LX := div_nonneg (by linarith) (by linarith)
    have : 2 * g / ccA αP (32155 / 1000) LX *
        (1 + ∫ t in (2 : ℝ)..(ccA αP (32155 / 1000) LX - 1), log (t - 1) / t) ≤
        2 * 1.7812 / 3.9999 * (1 + 0.14725) := by
      rcases le_total 0 (1 + ∫ t in (2 : ℝ)..(ccA αP (32155 / 1000) LX - 1), log (t - 1) / t) with hp | hp
      · exact mul_le_mul hgc (by linarith) hp (by norm_num)
      · have : 2 * g / ccA αP (32155 / 1000) LX *
            (1 + ∫ t in (2 : ℝ)..(ccA αP (32155 / 1000) LX - 1), log (t - 1) / t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hgc0 hp
        have : (0 : ℝ) ≤ 2 * 1.7812 / 3.9999 * (1 + 0.14725) := by norm_num
        linarith
    norm_num at this ⊢; linarith

lemma cAb_ge (g T e1 aa c4s w L LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (ha : 0 ≤ aa ∧ aa ≤ 1 / 10 ^ 18)
    (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L) :
    8 * ((58 / 57) * (0.5493035 * g) - 1 / 57 - (58 / 57) * Section9.ε * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + Section9.ε * 107 * 0.1016) - 3 / 10 ^ 18) ≤
      cAbA αP Section9.ε (32155 / 1000) g T e1 aa c4s w L LX := by
  unfold cAbA
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  set X := fS g (ccA αP (32155 / 1000) LX) with hX
  set H := exp 2 * h (ccA αP (32155 / 1000) LX) with hH
  set Mb := max (1 - fS g (ccA αP (32155 / 1000) LX)) (FS g (ccA αP (32155 / 1000) LX) - 1) with hMb
  have hXl : g * 0.5493035 ≤ X := fS_c_ge g LX (by linarith) hLX
  have hXu : X ≤ g * 0.5494 := fS_c_le g LX (by linarith) hLX
  have hH1 : H ≤ 0.1016 := h_le _ c1
  have hH0 : 0 ≤ H := by have := h_nonneg (ccA αP (32155 / 1000) LX) (by linarith); positivity
  have hM : Mb ≤ 0.02177 := mbar_le g LX hg1 hg2 hLX
  have hM0 : 0 ≤ Mb := le_trans (by nlinarith) (le_max_left _ _)
  have hL0 : 0 < L := by linarith
  have eq1 : (1 + e1) * Section9.ε * 107 * exp 2 * h (ccA αP (32155 / 1000) LX) =
      (1 + e1) * Section9.ε * 107 * H := by rw [hH]; ring
  have eq2 : Section9.ε * 107 * exp 2 * h (ccA αP (32155 / 1000) LX) = Section9.ε * 107 * H := by
    rw [hH]; ring
  rw [eq1, eq2]
  have t1 : e1 * (1 - X) ≤ 1 / 57 * (1 - X) :=
    mul_le_mul_of_nonneg_right he1.2 (by nlinarith)
  have t2 : (1 + e1) * Section9.ε * 107 * H ≤ (58 / 57) * Section9.ε * 107 * 0.1016 := by
    have : (1 + e1) * (Section9.ε * 107) ≤ (58 / 57) * (Section9.ε * 107) :=
      mul_le_mul_of_nonneg_right (by linarith [he1.2]) (by norm_num)
    have := mul_le_mul this hH1 hH0 (by norm_num)
    linarith
  have t3 : (3 * e1 + aa) * (Mb + Section9.ε * 107 * H) ≤
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + Section9.ε * 107 * 0.1016) := by
    apply mul_le_mul (by linarith [he1.2, ha.2]) (by nlinarith) (by positivity)
      (by norm_num)
  have s1 := small_div29 64.04 L (by norm_num) (by norm_num) (hLX.trans hL)
  have s2 := small_div29 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hd0 : 0 ≤ 32.02 / L ^ 2 := by positivity
  have t4 : 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w ≤ 1 / 10 ^ 20 := by
    have i1 : (1 + 32.02 / L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have i0 : 0 ≤ (1 + 32.02 / L ^ 2)⁻¹ := by positivity
    have i2 : g / (2 * T) ≤ 1.4 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have i20 : 0 ≤ g / (2 * T) := div_nonneg (by linarith) (by linarith)
    have i3 : c4s / L * w ≤ 1 / 10 ^ 20 := by
      have : c4s / L * w ≤ c4s / L * L :=
        mul_le_mul_of_nonneg_left hw.2 (div_nonneg hc4.1 hL0.le)
      rw [div_mul_cancel₀ _ hL0.ne'] at this
      linarith [hc4.2]
    have i30 : 0 ≤ c4s / L * w := mul_nonneg (div_nonneg hc4.1 hL0.le) hw.1
    have : (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) ≤ 1 * 1.4 := mul_le_mul i1 i2 i20 (by norm_num)
    have : (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L * w) ≤ 1.4 * (1 / 10 ^ 20) :=
      mul_le_mul (by linarith) i3 i30 (by norm_num)
    have e : 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w =
        1 / 8 * ((1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L * w)) := by ring
    rw [e]; nlinarith
  set B := X - e1 * (1 - X) - (1 + e1) * Section9.ε * 107 * H - (3 * e1 + aa) * (Mb + Section9.ε * 107 * H) -
    aa - 64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w with hB
  have hBl : (58 / 57) * (0.5493035 * g) - 1 / 57 - (58 / 57) * Section9.ε * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + Section9.ε * 107 * 0.1016) - 3 / 10 ^ 18 ≤ B := by
    rw [hB]; linarith
  have hB0 : 0 ≤ B := by norm_num at hBl; linarith
  calc 8 * ((58 / 57) * (0.5493035 * g) - 1 / 57 - (58 / 57) * Section9.ε * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + Section9.ε * 107 * 0.1016) - 3 / 10 ^ 18) ≤ 8 * 1 * B := by
        linarith
    _ ≤ 8 * (1 + 32.02 / L ^ 2) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0; linarith

lemma cAa_ge (g T c4 L : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20) (hL : 9 * 10 ^ 13 ≤ L) :
    8 * (1 - 1 / 10 ^ 26) * (0.5493035 * g - 107 * Section9.ε * 0.1016 - 1 / 10 ^ 20) ≤
      cAaA αP Section9.ε g T c4 L := by
  unfold cAaA
  have hX := fS_a_ge g (by linarith)
  have hH1 : exp 2 * h (4 - 8 * αP) ≤ 0.1016 := h_le _ (by norm_num)
  have hH0 : 0 ≤ exp 2 * h (4 - 8 * αP) := by
    have := h_nonneg (4 - 8 * αP) (by norm_num); positivity
  have s2 := small_div29 32.02 L (by norm_num) (by norm_num) hL
  have hd0 : 0 ≤ 32.02 / L ^ 2 := by positivity
  have hL0 : 0 < L := by linarith
  have e : 107 * Section9.ε * exp 2 * h (4 - 8 * αP) = 107 * Section9.ε * (exp 2 * h (4 - 8 * αP)) := by
    ring
  rw [e]
  have t4 : 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) ≤ 1 / 10 ^ 20 := by
    have i1 : (1 - 32.02 / L ^ 2)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by norm_num at s2 ⊢; linarith) (by norm_num)]; norm_num at s2 ⊢; linarith
    have i0 : 0 ≤ (1 - 32.02 / L ^ 2)⁻¹ := inv_nonneg.mpr (by norm_num at s2 ⊢; linarith)
    have i2 : g / (2 * T) ≤ 1.4 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have i20 : 0 ≤ g / (2 * T) := div_nonneg (by linarith) (by linarith)
    have i3 : c4 / L ≤ 1 / 10 ^ 20 := by
      have := small_div9 c4 L hc4.1 (by linarith [hc4.2]) hL
      have : c4 / L ≤ c4 := div_le_self hc4.1 (by linarith)
      linarith [hc4.2]
    have i30 : 0 ≤ c4 / L := div_nonneg hc4.1 hL0.le
    have : (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) ≤ 2 * 1.4 := mul_le_mul i1 i2 i20 (by norm_num)
    have : (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) ≤ 2.8 * (1 / 10 ^ 20) :=
      mul_le_mul (by linarith) i3 i30 (by norm_num)
    have e : 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) =
        1 / 8 * ((1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L)) := by ring
    rw [e]; nlinarith
  set B := fS g (4 - 8 * αP) - 107 * Section9.ε * (exp 2 * h (4 - 8 * αP)) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) with hB
  have hBl : 0.5493035 * g - 107 * Section9.ε * 0.1016 - 1 / 10 ^ 20 ≤ B := by
    rw [hB]
    have := mul_le_mul_of_nonneg_left hH1 (by norm_num : (0:ℝ) ≤ 107 * Section9.ε)
    linarith
  have hB0 : 0 ≤ 0.5493035 * g - 107 * Section9.ε * 0.1016 - 1 / 10 ^ 20 := by norm_num; linarith
  calc 8 * (1 - 1 / 10 ^ 26) * (0.5493035 * g - 107 * Section9.ε * 0.1016 - 1 / 10 ^ 20)
      ≤ 8 * (1 - 32.02 / L ^ 2) * (0.5493035 * g - 107 * Section9.ε * 0.1016 - 1 / 10 ^ 20) := by
        apply mul_le_mul_of_nonneg_right _ hB0; norm_num at s2 ⊢; linarith
    _ ≤ 8 * (1 - 32.02 / L ^ 2) * B := by
        apply mul_le_mul_of_nonneg_left hBl; norm_num at s2 ⊢; linarith

lemma Lam_le : (log 6 + log ((3 - 8 * αP) / (3 - 18 * αP))) / (1 / 2 - αP) ≤ 3.5836698 := by
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  have hr := log_le_sub_one_of_pos (x := (3 - 8 * αP) / (3 - 18 * αP)) (by norm_num)
  have := log_two_lt_d9; have := log_three_lt_d9
  rw [h6, div_le_iff₀ (by norm_num)]
  norm_num at *; linarith

lemma Lam_nonneg : 0 ≤ (log 6 + log ((3 - 8 * αP) / (3 - 18 * αP))) / (1 / 2 - αP) := by
  apply div_nonneg _ (by norm_num)
  have : 0 ≤ log ((3 - 8 * αP) / (3 - 18 * αP)) :=
    log_nonneg (by rw [le_div_iff₀ (by norm_num)]; norm_num)
  have : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
  linarith

lemma kA_ge1 : 1 ≤ kA αP := by unfold kA; norm_num

lemma kA_pos : 0 < kA αP := by unfold kA; norm_num

lemma hkA : exp 2 * h (kA αP) = 1 := h_low _ kA_ge1 kA_bounds.2

lemma l2A_nonneg (g LX : ℝ) (hg : 0 ≤ g) (hLX : 9 * 10 ^ 13 ≤ LX) : 0 ≤ l2A αP Section9.ε g LX := by
  unfold l2A
  have hE := add_one_le_exp (LX / 8)
  have h1 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
  have h2 := Lam_nonneg
  have hk := kA_bounds
  have h3 : 0 ≤ 512 / (kA αP * LX ^ 2) :=
    div_nonneg (by norm_num) (mul_nonneg kA_pos.le (sq_nonneg _))
  have h4 : 0 ≤ h (kA αP) := h_nonneg _ kA_pos.le
  have h80 := log83_nonneg
  have h5 : 0 ≤ 64 / LX ^ 2 := by positivity
  apply mul_nonneg h1
  apply add_nonneg
  · exact mul_nonneg (by linarith) (add_nonneg h2 h3)
  · have he : (0:ℝ) ≤ Section9.ε := by norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg h80 h5) he) (by norm_num))
      (exp_pos 2).le) h4

lemma l2_le (g LX : ℝ) (hg : 0 ≤ g) (hLX : 9 * 10 ^ 13 ≤ LX) :
    l2A αP Section9.ε g LX ≤ (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836699 + 0.98084 * Section9.ε * 106) := by
  unfold l2A
  have e : (log (8 / 3) + 64 / LX ^ 2) * Section9.ε * 106 * exp 2 * h (kA αP) =
      (log (8 / 3) + 64 / LX ^ 2) * Section9.ε * 106 * (exp 2 * h (kA αP)) := by ring
  rw [e, hkA, mul_one]
  have hk := kA_bounds
  have hL2 : (8.1 * 10 ^ 27 : ℝ) ≤ LX ^ 2 := by nlinarith
  have hs1 : 512 / (kA αP * LX ^ 2) ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ (mul_pos kA_pos (by positivity))]
    have := mul_le_mul hk.1 hL2 (by norm_num) kA_pos.le
    norm_num at this ⊢; linarith
  have hs2 : 64 / LX ^ 2 ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hs10 : 0 ≤ 512 / (kA αP * LX ^ 2) :=
    div_nonneg (by norm_num) (mul_nonneg kA_pos.le (sq_nonneg _))
  have hL := Lam_le
  have hL0 := Lam_nonneg
  have h8 := log83_le
  have h80 := log83_nonneg
  have hr := r8_le9 LX hLX
  have hs20 : 0 ≤ 64 / LX ^ 2 := by positivity
  have hpos : 0 ≤ g / 4 * ((log 6 + log ((3 - 8 * αP) / (3 - 18 * αP))) / (1 / 2 - αP) +
      512 / (kA αP * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * Section9.ε * 106 :=
    add_nonneg (mul_nonneg (by linarith) (add_nonneg hL0 hs10))
      (mul_nonneg (mul_nonneg (add_nonneg h80 hs20) (by norm_num)) (by norm_num))
  have hin : g / 4 * ((log 6 + log ((3 - 8 * αP) / (3 - 18 * αP))) / (1 / 2 - αP) +
      512 / (kA αP * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * Section9.ε * 106 ≤
      g / 4 * 3.5836699 + 0.98084 * Section9.ε * 106 := by
    have a1 : g / 4 * ((log 6 + log ((3 - 8 * αP) / (3 - 18 * αP))) / (1 / 2 - αP) +
        512 / (kA αP * LX ^ 2)) ≤ g / 4 * 3.5836699 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have a2 : (log (8 / 3) + 64 / LX ^ 2) * Section9.ε * 106 ≤ 0.98084 * Section9.ε * 106 := by
      have : log (8 / 3) + 64 / LX ^ 2 ≤ 0.98084 := by norm_num at hs2 h8 ⊢; linarith
      have := mul_le_mul_of_nonneg_right this (by norm_num : (0:ℝ) ≤ Section9.ε * 106)
      linarith
    linarith
  calc exp (LX / 8) / (exp (LX / 8) - 1) * _ ≤ (1 + 1 / 10 ^ 12) *
        (g / 4 * ((log 6 + log ((3 - 8 * αP) / (3 - 18 * αP))) / (1 / 2 - αP) +
        512 / (kA αP * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * Section9.ε * 106) :=
        mul_le_mul_of_nonneg_right hr hpos
    _ ≤ _ := mul_le_mul_of_nonneg_left hin (by norm_num)

lemma cQb_le (g T e1 l1s ls L LX : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T) (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L) :
    cQbA αP Section9.ε g T e1 l1s ls L LX ≤ 8.0004 * (1 + 1 / 10 ^ 26) * (1 + 1 / 57) *
      (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836699 + 0.98084 * Section9.ε * 106)) +
      1 / 10 ^ 20 * (g / 1.3) := by
  unfold cQbA
  have s1 := small_div29 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hl2 := l2_le g LX hg hLX
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have hl2n := l2A_nonneg g LX hg hLX
  have p1 : 8.0004 * (1 + 32.02 / L ^ 2) * (1 + e1) * (l1s + l2A αP Section9.ε g LX) ≤
      8.0004 * (1 + 1 / 10 ^ 26) * (1 + 1 / 57) *
        (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836699 + 0.98084 * Section9.ε * 106)) := by
    have := hl1.1
    have : 0 ≤ 32.02 / L ^ 2 := by positivity
    gcongr
    all_goals first | exact he1.2 | exact hl1.2 | linarith
  have p2 : ls * (g / (2 * T)) ≤ 1 / 10 ^ 20 * (g / 1.3) :=
    mul_le_mul hls.2 hT' (div_nonneg hg (by linarith)) (by norm_num)
  linarith

lemma cQa_le (g T l1 l L LX : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L) :
    cQaA αP Section9.ε g T l1 l L LX ≤ 8.0004 * (1 + 1 / 10 ^ 26) *
      (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836699 + 0.98084 * Section9.ε * 106)) +
      1 / 10 ^ 20 * (g / 1.3) := by
  unfold cQaA
  have s1 := small_div29 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hl2 := l2_le g LX hg hLX
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have hl2n := l2A_nonneg g LX hg hLX
  have p1 : 8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2A αP Section9.ε g LX) ≤
      8.0004 * (1 + 1 / 10 ^ 26) *
        (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836699 + 0.98084 * Section9.ε * 106)) := by
    have := hl1.1
    have : 0 ≤ 32.02 / L ^ 2 := by positivity
    gcongr
    all_goals first | exact hl1.2 | linarith
  have p2 : l * (g / (2 * T)) ≤ 1 / 10 ^ 20 * (g / 1.3) :=
    mul_le_mul hls.2 hT' (div_nonneg hg (by linarith)) (by norm_num)
  linarith

lemma cB_le (g T e2 cb m L : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 381 / 10 ^ 12) (hL : 9 * 10 ^ 13 ≤ L) :
    cBA αP Section9.ε At32155.ee0 g T e2 cb m L ≤
      1.00005 * (1 + 1 / 51) * (1 + 1 / 10 ^ 26) * (2 / (1 / 2 - αP) * g + 3 * Section9.ε * 106) *
        (1 + At32155.ee0 + 1 / 10 ^ 12) * (0.363084 + 1 / 10 ^ 11) +
      g / 1.3 * (320 * (381 / 10 ^ 12) * (1 + At32155.ee0) / (3 * (145 / 1000000 / (1 + 145 / 1000000))) +
        1 / 10 ^ 12) := by
  unfold cBA
  have hk : exp 2 * h (3 / 2 - 3 * αP) = 1 := h_low _ (by norm_num) (by norm_num)
  have e : 3 * Section9.ε * 106 * exp 2 * h (3 / 2 - 3 * αP) =
      3 * Section9.ε * 106 * (exp 2 * h (3 / 2 - 3 * αP)) := by ring
  rw [e, hk, mul_one]
  have s1 := small_div29 4.51 L (by norm_num) (by norm_num) hL
  have s2 := small_div9 9 L (by norm_num) (by norm_num) hL
  have s3 := small_div29 36 L (by norm_num) (by norm_num) hL
  have s4 := small_div29 64 L (by norm_num) (by norm_num) hL
  have s5 := small_div29 27 L (by norm_num) (by norm_num) hL
  have hl1 := At32155.log1e0_leP
  have hl0 := At32155.log1e0_geP
  have hq : (0:ℝ) < 145 / 1000000 / (1 + 145 / 1000000) := by norm_num
  have hlp : 0 < log (1 + At32155.ee0) := lt_of_lt_of_le hq hl0
  have s6 : 10 * log (1 + At32155.ee0) / L ≤ 1 / 10 ^ 12 :=
    small_div9 _ L (by positivity)
      (le_trans (mul_le_mul_of_nonneg_left hl1 (by norm_num)) (by norm_num)) hL
  have h83 := log83_le
  have h83n := log83_nonneg
  have hA4 : cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + At32155.ee0) / L + 27 / L ^ 2) ≤
      0.363084 + 1 / 10 ^ 11 := by
    have : (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + At32155.ee0) / L + 27 / L ^ 2) ≤ 1 * (2 / 10 ^ 12) := by
      apply mul_le_mul (by norm_num at s4 h83 ⊢; linarith) (by norm_num at s5 s6 ⊢; linarith)
        (by positivity) (by norm_num)
    norm_num at this s3 ⊢; linarith
  have hA4n : 0 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + At32155.ee0) / L + 27 / L ^ 2) := by
    have := hcb.1; positivity
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have tl := At32155.tail_leP L hL
  have hX : 320 * m * (1 + At32155.ee0) / (3 * log (1 + At32155.ee0)) ≤
      320 * (381 / 10 ^ 12) * (1 + At32155.ee0) / (3 * (145 / 1000000 / (1 + 145 / 1000000))) := by
    apply div_le_div₀ (by norm_num) (by nlinarith [hm.2]) (by positivity) (by linarith)
  have hXn : 0 ≤ 320 * m * (1 + At32155.ee0) / (3 * log (1 + At32155.ee0)) +
      0.13 * (1 + At32155.ee0) * L ^ 5 / (exp (L / 8) * log (1 + At32155.ee0)) := by
    have := hm.1; have := exp_pos (L / 8); positivity
  have part2 : g / (2 * T) * (320 * m * (1 + At32155.ee0) / (3 * log (1 + At32155.ee0)) +
      0.13 * (1 + At32155.ee0) * L ^ 5 / (exp (L / 8) * log (1 + At32155.ee0))) ≤
      g / 1.3 * (320 * (381 / 10 ^ 12) * (1 + At32155.ee0) / (3 * (145 / 1000000 / (1 + 145 / 1000000))) +
        1 / 10 ^ 12) :=
    mul_le_mul hT' (by linarith) hXn (by positivity)
  have part1 : 1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) * (2 / (1 / 2 - αP) * g + 3 * Section9.ε * 106) *
      (1 + At32155.ee0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + At32155.ee0) / L + 27 / L ^ 2)) ≤
      1.00005 * (1 + 1 / 51) * (1 + 1 / 10 ^ 26) * (2 / (1 / 2 - αP) * g + 3 * Section9.ε * 106) *
        (1 + At32155.ee0 + 1 / 10 ^ 12) * (0.363084 + 1 / 10 ^ 11) := by
    have h45 : 0 ≤ 4.51 / L ^ 2 := by positivity
    have hLp : 0 < L := by linarith
    have h9 : 0 ≤ 9 / L := by positivity
    gcongr
    · linarith [he2.2]
  linarith

/-! ### l₁ at α = αP and the printed ε -/

lemma h_kA' : h (kA αP) = exp (-2) := by
  unfold Section9.h; rw [ite_eq_left_iff.mpr (fun hh => absurd kA_bounds.2 hh)]

lemma A_le {g C1 : ℝ} (hg : g ≤ 1.7812) (hC0 : 0 ≤ C1) (hC : C1 ≤ 1e6) :
    2 * g / kA αP + Section9.ε * C1 * exp 2 * h (kA αP) ≤ 3 := by
  rw [h_kA']
  have e : Section9.ε * C1 * exp 2 * exp (-2) = Section9.ε * C1 := by
    rw [mul_assoc, ← exp_add]; norm_num
  rw [e]
  have h1 : 2 * g / kA αP ≤ 2.7 := by
    rw [div_le_iff₀ kA_pos]; unfold kA; norm_num; linarith
  have h2 : Section9.ε * C1 ≤ 0.2 := by norm_num; nlinarith
  linarith

lemma A_nonneg {g C1 : ℝ} (hg0 : 0 ≤ g) (hC0 : 0 ≤ C1) :
    0 ≤ 2 * g / kA αP + Section9.ε * C1 * exp 2 * h (kA αP) := by
  rw [h_kA']
  exact add_nonneg (div_nonneg (by linarith) kA_pos.le)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) (exp_pos _).le) (exp_pos _).le)

/-- **l₁(X₂), l₁*(X₂) ∈ [0, 10⁻²⁰] at α₂ = αP and the printed ε**, for 0 ≤ g ≤ 1.7812, 0 ≤ C₁ ≤ 10⁶. -/
theorem l1A_bounds {g C1 ν : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (hC0 : 0 ≤ C1) (hC : C1 ≤ 1e6)
    (hν : BJSp32155.Good ν) : 0 ≤ l1A αP Section9.ε g C1 ν ∧ l1A αP Section9.ε g C1 ν ≤ 1e-20 := by
  have hX := BJSp32155.LX_ge
  have hp : 0 < BJSp32155.LX := by linarith
  have hA := A_le hg hC0 hC; have hA0 := A_nonneg (C1 := C1) hg0 hC0
  have hB := BJSl32155.B1_le; have hB0 := BJSl32155.B1_nonneg
  have hP := BJSp32155.p_le hν; have hP0 := BJSp32155.p_nonneg hν
  have hR := BJSl32155.LXexp_le
  have hR0 : 0 ≤ BJSp32155.LX ^ 2 / exp BJSp32155.LX := by positivity
  have k : BJSp32155.LX ^ 2 / exp BJSp32155.LX * (BJSp32155.p ν * exp BJSp32155.LX / BJSp32155.LX ^ 4) =
      BJSp32155.p ν / BJSp32155.LX ^ 2 := by
    field_simp
  have e : l1A αP Section9.ε g C1 ν =
      (2 * g / kA αP + Section9.ε * C1 * exp 2 * h (kA αP)) *
        (BJSp32155.LX ^ 2 / exp BJSp32155.LX * (exp (BJSp32155.LX / 8) / (exp (BJSp32155.LX / 8) - 1) *
          (log (8 / 3) + 64 / BJSp32155.LX ^ 2) * (1.3841 / 32.155))) +
      (2 * g / kA αP + Section9.ε * C1 * exp 2 * h (kA αP)) *
        (BJSp32155.p ν / BJSp32155.LX ^ 2) := by
    unfold l1A
    linear_combination (2 * g / kA αP + Section9.ε * C1 * exp 2 * h (kA αP)) * k
  set A := 2 * g / kA αP + Section9.ε * C1 * exp 2 * h (kA αP)
  set B1 := exp (BJSp32155.LX / 8) / (exp (BJSp32155.LX / 8) - 1) * (log (8 / 3) + 64 / BJSp32155.LX ^ 2) *
    (1.3841 / 32.155)
  have hq : BJSp32155.p ν / BJSp32155.LX ^ 2 ≤ 1e-24 := by
    rw [div_le_iff₀ (by positivity)]
    have : (100 : ℝ) ≤ BJSp32155.LX ^ 2 := by nlinarith
    nlinarith
  have hq0 : 0 ≤ BJSp32155.p ν / BJSp32155.LX ^ 2 := by positivity
  have t1 : BJSp32155.LX ^ 2 / exp BJSp32155.LX * B1 ≤ 1e-30 := by nlinarith
  rw [e]
  constructor
  · positivity
  · have := mul_le_mul hA t1 (by positivity) (by norm_num : (0:ℝ) ≤ 3)
    have := mul_le_mul hA hq hq0 (by norm_num : (0:ℝ) ≤ 3)
    linarith

/-! ### The Section 9 margin at α = αP, printed ε -/

/-- **Case (b) at log log X₂ = 32.155, α = 1.09·10⁻⁵, ε = 1.452·10⁻⁷, ε₀ = 1.45·10⁻⁴**, PROVED from
the stated numeric inputs; Lean-side slack about 2.5·10⁻⁵, numerics/alpha_scan_U1310.py section F. -/
theorem margin_bA (g T e1 e2 cb m aa c4s w l1s ls L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 381 / 10 ^ 12)
    (ha : 0 ≤ aa ∧ aa ≤ 1 / 10 ^ 18) (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAbA αP Section9.ε (32155 / 1000) g T e1 aa c4s w L LX - cQbA αP Section9.ε g T e1 l1s ls L LX / 2 -
        cBA αP Section9.ε At32155.ee0 g T e2 cb m L / 2 := by
  have hA := cAb_ge g T e1 aa c4s w L LX hg1 hg2 hT he1 ha hc4 hw hLX hL
  have hQ := cQb_le g T e1 l1s ls L LX (by linarith) hT he1 hl1 hls hLX hL
  have hB := cB_le g T e2 cb m L (by linarith) hT he2 hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith

/-- **Case (a) at α = αP, printed ε**, PROVED from the stated numeric inputs; about 0.1244 ≥ 1/10. -/
theorem margin_aA (g T e2 cb m c4 l1 l L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 381 / 10 ^ 12)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L) :
    1 / 10 ≤ cAaA αP Section9.ε g T c4 L - cQaA αP Section9.ε g T l1 l L LX / 2 -
      cBA αP Section9.ε At32155.ee0 g T e2 cb m L / 2 := by
  have hA := cAa_ge g T c4 L hg1 hg2 hT hc4 (hLX.trans hL)
  have hQ := cQa_le g T l1 l L LX (by linarith) hT hl1 hls hLX hL
  have hB := cB_le g T e2 cb m L (by linarith) hT he2 hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith

/-! ### Assembly at X₂ = exp(exp 32.155) with the X₂-only constants of AssemblyT32155 -/

/-- l₁, l₁* at α₂ = αP and the printed ε. -/
abbrev l1aA : ℝ := l1A αP Section9.ε AT32155.gE 106 BJSp32155.nu
abbrev l1SA : ℝ := l1A αP Section9.ε AT32155.gE 106 BJSp32155.nuS

open Classical in
/-- Theorem 44's corrected constant at the printed u₀, ε and α₁ = αP, X₂ = exp(exp 32.155). -/
def cA32155P (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAaA αP Section9.ε AT32155.gE twinC AT32155.c4a (Real.log N)
  else cAbA αP Section9.ε (32155 / 1000) AT32155.gE twinC AT32155.e1 AT32155.aS AT32155.c4S (w N)
    (Real.log N) AT32155.LX

open Classical in
/-- Theorem 50's corrected constant at the printed u₀, ε and α₂ = αP. -/
def cQ32155P (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQaA αP Section9.ε AT32155.gE twinC l1aA AT32155.la (Real.log N) AT32155.LX
  else cQbA αP Section9.ε AT32155.gE twinC AT32155.e1 l1SA AT32155.lS (Real.log N) AT32155.LX

/-- Theorem 51's corrected constant at the printed u₀, ε and α₃ = αP, ε₀ = 1.45·10⁻⁴. -/
def cB32155P (N : ℕ) : ℝ :=
  cBA αP Section9.ε At32155.ee0 AT32155.gE twinC AT32155.e2 BJS.cbar AT32155.mm (Real.log N)

lemma hl1aA : 0 ≤ l1aA ∧ l1aA ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := l1A_bounds (C1 := 106) AT32155.g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp32155.nu_good
  exact ⟨a, le_trans b (by norm_num)⟩

lemma hl1SA : 0 ≤ l1SA ∧ l1SA ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := l1A_bounds (C1 := 106) AT32155.g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp32155.nuS_good
  exact ⟨a, le_trans b (by norm_num)⟩

/-- **The Section 9 margin at exp(exp 32.155) with the printed constants and α = αP**, PROVED. -/
theorem margin_32155_printed (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (32155 / 1000) (cA32155P caseA w) (cQ32155P caseA) cB32155P := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : AT32155.LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA32155P cQ32155P cB32155P
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aA AT32155.gE twinC AT32155.e2 BJS.cbar AT32155.mm AT32155.c4a l1aA AT32155.la
      (Real.log N) AT32155.LX g_ge g_le AT32155.hT AT32155.he2 AT32155.hcb BJSm32155.mX3_vS_bounds
      AT32155.hc4a hl1aA AT32155.hla AT32155.LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bA AT32155.gE twinC AT32155.e1 AT32155.e2 BJS.cbar AT32155.mm AT32155.aS AT32155.c4S
      (w N) l1SA AT32155.lS (Real.log N) AT32155.LX g_ge g_le AT32155.hT AT32155.he1 AT32155.he2
      AT32155.hcb BJSm32155.mX3_vS_bounds AT32155.ha AT32155.hc4S (hw N) hl1SA AT32155.hlS
      AT32155.LX_ge hL

/-! ### The range conditions at the printed u₀ = 10⁹ and α = αP -/

lemma log1e9_ge1 : (1 : ℝ) ≤ log 1000000000 := by
  have he : exp 1 ≤ (1000000000 : ℝ) := by have := exp_one_lt_d9; linarith
  have := Real.log_le_log (exp_pos 1) he
  rwa [Real.log_exp] at this

lemma log1e14_le : log ((10 : ℝ) ^ 14) ≤ 33 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have e : exp (33 : ℝ) = exp 1 ^ 33 := by rw [← exp_nat_mul]; norm_num
  have he := exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ 33 ≤ exp 1 ^ 33 := pow_le_pow_left₀ (by norm_num) he.le 33
  have : (10 : ℝ) ^ 14 ≤ 2.7182818283 ^ 33 := by norm_num
  rw [e]; linarith

lemma log_le_lin14 (L : ℝ) (hL : 0 < L) : log L ≤ 33 + L / 10 ^ 14 := by
  have hc : (0 : ℝ) < 10 ^ 14 := by positivity
  have h1 : log (L / 10 ^ 14) ≤ L / 10 ^ 14 - 1 := log_le_sub_one_of_pos (div_pos hL hc)
  have h2 : log (L / 10 ^ 14) = log L - log ((10 : ℝ) ^ 14) := log_div hL.ne' hc.ne'
  have h3 := log1e14_le
  rw [h2] at h1
  generalize log ((10 : ℝ) ^ 14) = a at h1 h3
  linarith

lemma rhs_le9 : (1000000000 : ℝ) * (1 + 9e-7 / log 1000000000) ≤ 1000000000 + 900 := by
  have h6 : 9e-7 / log (1000000000 : ℝ) ≤ 9e-7 := div_le_self (by norm_num) log1e9_ge1
  nlinarith

/-- **Theorems 44 and 50, the u₀ condition at the printed u₀ = 10⁹, α = αP = 1.09·10⁻⁵**, in logs,
every `L = log N ≥ 9.21·10¹³` and `1 ≤ lx₁ ≤ L`, pp. 42, 51. -/
theorem u0cond_44_50_A (L lx1 : ℝ) (hL : 9.21 * 10 ^ 13 ≤ L) (hx1 : 1 ≤ lx1) (hx1L : lx1 ≤ L) :
    1000000000 * (1 + 9e-7 / log 1000000000) ≤ αP * L - 10 * log lx1 - 2.5 * log L := by
  have hL0 : 0 < L := by linarith
  have h1 : log lx1 ≤ log L := log_le_log (by linarith) hx1L
  have h2 := log_le_lin14 L hL0
  have hm := rhs_le9
  simp only [αP]
  nlinarith

/-- **Theorem 51's condition at u₀ = 10⁹, α₃ = αP**, `log 3¹⁰ + α₃ L − 10 log L ≥ u₀(1 + 9·10⁻⁷/log u₀)`,
p. 56. -/
theorem u0cond_51_A (L : ℝ) (hL : 9.21 * 10 ^ 13 ≤ L) :
    1000000000 * (1 + 9e-7 / log 1000000000) ≤ 10 * log 3 + αP * L - 10 * log L := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin14 L hL0
  have h3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
  have hm := rhs_le9
  simp only [αP]
  nlinarith

/-- **The other ranges at `L ≥ 9.21·10¹³`, α = αP, printed ε**: (140), α₂ < 1/24, α₃ < 1/6,
`N^{1/2−α₁}/log²⁰ N ≥ z²` in logs, `log z > 4000` of Lemma 18, and `ε ≤ 1/74` of Theorem 6. -/
theorem ranges_A (L : ℝ) (hL : 9.21 * 10 ^ 13 ≤ L) :
    8 * αP + 160 * log L / L < 1 ∧ 0 < αP ∧ αP < 1 / 24 ∧ αP < 1 / 6 ∧
      L / 4 ≤ (1 / 2 - αP) * L - 20 * log L ∧ 4000 < L / 8 ∧ Section9.ε ≤ 1 / 74 := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin14 L hL0
  refine ⟨?_, by norm_num, by norm_num, by norm_num, ?_, by linarith, by norm_num⟩
  · have hlog : log L ≤ L / 1000 := by nlinarith
    have : 160 * log L / L ≤ 160 / 1000 := by
      rw [div_le_iff₀ hL0]; nlinarith
    simp only [αP]; norm_num; linarith
  · simp only [αP]; nlinarith

lemma logN_ge {N : ℕ} (hN : exp (exp (32155 / 1000)) < (N : ℝ)) : AT32155.LX ≤ Real.log N := by
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  exact ((Real.lt_log_iff_exp_lt hpos).mpr hN).le

/-- **Chen at exp(exp 32.155) from the printed Theorems 44, 50, 51 at α = 1.09·10⁻⁵**, with the
u₀ = 10⁹ range conditions. CONDITIONAL ON Thm44At, Thm50At, Thm51At at t = 32.155 with the printed
ε = 1.452·10⁻⁷, u₀ = 10⁹, C₁ = 106, C₂ = 107, α₁ = α₂ = α₃ = 1.09·10⁻⁵, corrected per F-0020 to F-0022. -/
theorem chen_32155_printed (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (32155 / 1000) (cA32155P caseA w)) (hQ : Thm50At (32155 / 1000) (cQ32155P caseA))
    (hB : Thm51At (32155 / 1000) cB32155P) :
    BJS3At (32155 / 1000) ∧
    (∀ N : ℕ, exp (exp (32155 / 1000)) < (N : ℝ) →
      (∀ lx1 : ℝ, 1 ≤ lx1 → lx1 ≤ Real.log N →
        1000000000 * (1 + 9e-7 / log 1000000000) ≤
          αP * Real.log N - 10 * log lx1 - 2.5 * log (Real.log N)) ∧
      1000000000 * (1 + 9e-7 / log 1000000000) ≤
        10 * log 3 + αP * Real.log N - 10 * log (Real.log N)) := by
  refine ⟨BJS3At_of_sieveBounds32 _ (by norm_num) _ _ _ hA hQ hB (margin_32155_printed caseA w hw), ?_⟩
  intro N hN
  have h9 : (9.21 : ℝ) * 10 ^ 13 ≤ Real.log N := le_trans BJSm32155.exp32155_ge (logN_ge hN)
  exact ⟨fun lx1 h1 h2 => u0cond_44_50_A _ lx1 h9 h1 h2, u0cond_51_A _ h9⟩

/-- Vacuity of the range lemmas: L = 9.21·10¹³ meets their hypothesis, and lx₁ = L as well. -/
example : (9.21 : ℝ) * 10 ^ 13 ≤ 9.21 * 10 ^ 13 ∧ (1 : ℝ) ≤ 9.21 * 10 ^ 13 := ⟨le_rfl, by norm_num⟩

end LeanLab.ChenExplicit.Printed32155
