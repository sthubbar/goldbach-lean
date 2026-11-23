module

public import LeanLab.ChenExplicit.Section9F9
public import LeanLab.ChenExplicit.FIntegral5

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 3 of gen/port3220_U6718.py, the 3216 file below ported to log log X₂ = 32.155, δ₁ = 1.5026, δ₂ = 1.47088, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, ν ℓ ≥ 145.7 so m(X₃) ≤ 3.81·10⁻¹⁰, ε₀ = 1.45·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3216 one, itself a port; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 2 of gen/port3220_U6718.py, the 3220 file below ported to log log X₂ = 32.16, δ₁ = 1.5024, δ₂ = 1.4707, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, the Siegel term of (87) ≤ 10⁻²³ and p(X₂) ≤ 10⁻²², ν ℓ ≥ 146.3 so m(X₃) ≤ 2.17·10⁻¹⁰, ε₀ = 1.1·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3220 one; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: a scripted port by gen/port3220_U6718.py of the 3225 file of U-6713 to log log X₂ = 32.2, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷, δ₁ = 1.5005 for Theorems 44 and 50 and δ₂ = 1.4688 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 1.1·10⁻¹¹ with ν ℓ ≥ 152, ν(x₁) log x₁ ≥ 130, the Siegel term of (87) ≤ 3·10⁻²⁵, p(X₂) ≤ 10⁻²⁴ unchanged, and the floor log X₂ ≥ 10¹⁴ lowered to 9·10¹³ through Section9F9.lean. The 3225 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2: a scripted port by gen/port3225_U6713.py of the 3230 file of cloud46 U-6602 to log log X₂ = 32.25, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷ through Section9U8.lean, δ₁ = 1.4985 for Theorems 44 and 50 and δ₂ = 1.4665 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹ with ν ℓ ≥ 158; ν(x₁) log x₁ ≥ 135 in place of 145, so the Siegel term of (87) is bounded by 10⁻²⁶ in place of 10⁻³⁰, p(X₂) ≤ 10⁻²⁴ unchanged. Numeric lemmas retightened by the HAND table of the script. The 3230 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1618Z-cloud46, unit U-6602, track T2: a scripted port by gen/port3230_U6602.py of the 3270 file of cloud42 U-6403 to log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.464 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 3270 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6403, track T1: a scripted port by gen/port3230_U6403.py of the 32.716 file of PC U-1045 to the printed log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.445 for Theorem 51, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 32.716 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-19, run 20261019T0903Z-22821, built in the cloud workspace for the PC lab,
unit U-1045, track T2. A scripted port of At3272.lean, PC run 20261019T0703Z-249, U-1041, itself a port
of At3273.lean of U-0988.
Changes against At3272.lean, all checked by the build: log log X₂ = 32.3; ε₀ = 1.37·10⁻⁴ → 2·10⁻⁵,
the optimum for the larger m; the m(X₃) hypothesis 3.4·10⁻¹⁰ → 10⁻¹¹, proved in BJSm3230.lean.
Lean-side case (b) slack about 3.7·10⁻⁴ at g = 1.781, by exact rational arithmetic on the bounds.
P0009 BJS 2022, arXiv 2207.09452v6, Section 9 with Theorems 44 (b), 50 (b), 51 CORRECTED per
F-0020 to F-0022, case (b), at log log X₂ = 32.3.

This file is Section9.lean's case (b) proof on the parametrized definitions `cAbP`, `cBP` of
F0023.lean, which `cAb_eq`, `cB_eq` there tie by rfl to the VERIFIED Section9 forms.

PROVED: `margin_bP`, case (b) at least 2·10⁻⁴ + 10⁻¹² at log log X₂ = 32.3, for every
log N ≥ log X₂, CONDITIONAL ON the numeric inputs as hypotheses: ε₁ ≤ 1/57, ε₂ ≤ 1/51,
m(X₃) ≤ 10⁻¹¹, the X₂-only constants a ≤ 10⁻¹⁸ and c₄*, l₁*, l* ≤ 10⁻²⁰, w ≤ log N, and the
integral bound; AssemblyT3230.lean discharges every one. Chen's theorem is not in doubt; Goldbach is open.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.At32155

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.Section9U8 LeanLab.ChenExplicit.Section9F9

/-- `ε₀ = 1.45·10⁻⁴` at log log X₂ = 32.155. -/
abbrev ee0 : ℝ := 145 / 1000000

lemma log_cm1_geP (LX : ℝ) (hLX : 9 * 10 ^ 13 ≤ LX) : 1.09858558 ≤ log (ccP (32155 / 1000) LX - 1) := by
  unfold ccP
  have hx : 160 * (32155 / 1000) / LX ≤ 10 ^ (-10 : ℤ) := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  have hpos : 0 < 160 * (32155 / 1000) / LX := by positivity
  set d := 160 * (32155 / 1000) / LX
  have e : 4 - 8 * α - d - 1 = 3 * (1 - (8 * α + d) / 3) := by ring
  rw [e, log_mul (by norm_num) (by norm_num at hx ⊢; nlinarith)]
  have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 - (8 * α + d) / 3) (by norm_num at hx ⊢; nlinarith)
  have l3 := log_three_gt_d9
  have h2 : 1 - (1 - (8 * α + d) / 3)⁻¹ ≥ -0.0000267 := by
    have hy : 0.99997 ≤ 1 - (8 * α + d) / 3 := by norm_num at hx ⊢; nlinarith
    have : (1 - (8 * α + d) / 3)⁻¹ ≤ 1 + 0.0000267 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      have : (8 * α + d) / 3 ≤ 0.0000266667 + 0.0000000001 := by norm_num at hx ⊢; nlinarith
      rw [inv_eq_one_div, div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  norm_num at l3 ⊢; linarith

lemma cc_boundsP (LX : ℝ) (hLX : 9 * 10 ^ 13 ≤ LX) : 3.9999 ≤ ccP (32155 / 1000) LX ∧ ccP (32155 / 1000) LX ≤ 3.99992 := by
  unfold ccP
  have hpos : 0 < 160 * (32155 / 1000) / LX := by positivity
  have hx : 160 * (32155 / 1000) / LX ≤ 10 ^ (-10 : ℤ) := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  norm_num at hx ⊢; constructor <;> linarith

lemma fS_c_geP (g LX : ℝ) (hg : 0 ≤ g) (hLX : 9 * 10 ^ 13 ≤ LX) :
    g * 0.54930376 ≤ fS g (ccP (32155 / 1000) LX) := by
  unfold fS
  obtain ⟨c1, c2⟩ := cc_boundsP LX hLX
  have hl := log_cm1_geP LX hLX
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hl hg, mul_le_mul_of_nonneg_left c2 hg]


lemma fS_c_leP (g LX : ℝ) (hg : 0 ≤ g) (hLX : 9 * 10 ^ 13 ≤ LX) : fS g (ccP (32155 / 1000) LX) ≤ g * 0.5494 := by
  unfold fS
  obtain ⟨c1, c2⟩ := cc_boundsP LX hLX
  have hl : log (ccP (32155 / 1000) LX - 1) ≤ log 3 := log_le_log (by linarith) (by linarith)
  have l3 := log_three_lt_d9
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ log (ccP (32155 / 1000) LX - 1) := log_nonneg (by linarith)
  norm_num at l3 ⊢
  nlinarith


lemma log1e0_geP : 145 / 1000000 / (1 + 145 / 1000000) ≤ log (1 + ee0) := by
  have := Real.one_sub_inv_le_log_of_pos (x := 1 + ee0) (by norm_num)
  have e : 1 - (1 + ee0)⁻¹ = 145 / 1000000 / (1 + 145 / 1000000) := by norm_num
  linarith

lemma log1e0_leP : log (1 + ee0) ≤ 145 / 1000000 := by
  have := log_le_sub_one_of_pos (x := 1 + ee0) (by norm_num); norm_num at this ⊢; linarith

lemma tail_leP (L : ℝ) (hL : 9 * 10 ^ 13 ≤ L) :
    0.13 * (1 + ee0) * L ^ 5 / (exp (L / 8) * log (1 + ee0)) ≤ 1 / 10 ^ 12 := by
  have hE := pow_div_factorial_le_exp (x := L / 8) (by positivity) 7
  have hf : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hf] at hE
  have hlg := log1e0_geP
  have hq : (0:ℝ) < 145 / 1000000 / (1 + 145 / 1000000) := by norm_num
  have hlg0 : 0 < log (1 + ee0) := lt_of_lt_of_le hq hlg
  have hEp : 0 < exp (L / 8) := exp_pos _
  rw [div_le_iff₀ (by positivity)]
  have h1 : (L / 8) ^ 7 / 5040 * (145 / 1000000 / (1 + 145 / 1000000)) ≤ exp (L / 8) * log (1 + ee0) :=
    mul_le_mul hE hlg (by positivity) hEp.le
  have h2 : 0.13 * (1 + ee0) * L ^ 5 ≤ 1 / 10 ^ 12 * ((L / 8) ^ 7 / 5040 * (145 / 1000000 / (1 + 145 / 1000000))) := by
    have hL2 : (8 * 10 ^ 27 : ℝ) ≤ L ^ 2 := by nlinarith
    have : (L / 8) ^ 7 / 5040 * (145 / 1000000 / (1 + 145 / 1000000)) =
        L ^ 5 * L ^ 2 * (1 / (8 ^ 7 * 5040) * (145 / 1000000 / (1 + 145 / 1000000))) := by ring
    rw [this]
    have hL5 : 0 ≤ L ^ 5 := by positivity
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hL2 hL5]
  nlinarith


lemma cB_leP (g T e2 cb m L : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 381 / 10 ^ 12) (hL : 9 * 10 ^ 13 ≤ L) :
    cBPU ee0 g T e2 cb m L ≤
      1.00005 * (1 + 1 / 51) * (1 + 1 / 10 ^ 26) * (2 / (1 / 2 - α) * g + 3 * εU * 106) *
        (1 + ee0 + 1 / 10 ^ 12) * (0.363084 + 1 / 10 ^ 11) +
      g / 1.3 * (320 * (381 / 10 ^ 12) * (1 + ee0) / (3 * (145 / 1000000 / (1 + 145 / 1000000))) +
        1 / 10 ^ 12) := by
  unfold cBPU
  have hk : exp 2 * h (3 / 2 - 3 * α) = 1 := h_low _ (by norm_num) (by norm_num)
  have e : 3 * εU * 106 * exp 2 * h (3 / 2 - 3 * α) = 3 * εU * 106 * (exp 2 * h (3 / 2 - 3 * α)) := by
    ring
  rw [e, hk, mul_one]
  have s1 := small_div29 4.51 L (by norm_num) (by norm_num) hL
  have s2 := small_div9 9 L (by norm_num) (by norm_num) hL
  have s3 := small_div29 36 L (by norm_num) (by norm_num) hL
  have s4 := small_div29 64 L (by norm_num) (by norm_num) hL
  have s5 := small_div29 27 L (by norm_num) (by norm_num) hL
  have hl1 := log1e0_leP
  have hl0 := log1e0_geP
  have hq : (0:ℝ) < 145 / 1000000 / (1 + 145 / 1000000) := by norm_num
  have hlp : 0 < log (1 + ee0) := lt_of_lt_of_le hq hl0
  have s6 : 10 * log (1 + ee0) / L ≤ 1 / 10 ^ 12 :=
    small_div9 _ L (by positivity)
      (le_trans (mul_le_mul_of_nonneg_left hl1 (by norm_num)) (by norm_num)) hL
  have h83 := log83_le
  have h83n := log83_nonneg
  have hA4 : cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + ee0) / L + 27 / L ^ 2) ≤
      0.363084 + 1 / 10 ^ 11 := by
    have : (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + ee0) / L + 27 / L ^ 2) ≤ 1 * (2 / 10 ^ 12) := by
      apply mul_le_mul (by norm_num at s4 h83 ⊢; linarith) (by norm_num at s5 s6 ⊢; linarith)
        (by positivity) (by norm_num)
    norm_num at this s3 ⊢; linarith
  have hA4n : 0 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + ee0) / L + 27 / L ^ 2) := by
    have := hcb.1; positivity
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have tl := tail_leP L hL
  have hX : 320 * m * (1 + ee0) / (3 * log (1 + ee0)) ≤
      320 * (381 / 10 ^ 12) * (1 + ee0) / (3 * (145 / 1000000 / (1 + 145 / 1000000))) := by
    apply div_le_div₀ (by norm_num) (by nlinarith [hm.2]) (by positivity) (by linarith)
  have hXn : 0 ≤ 320 * m * (1 + ee0) / (3 * log (1 + ee0)) +
      0.13 * (1 + ee0) * L ^ 5 / (exp (L / 8) * log (1 + ee0)) := by
    have := hm.1; have := exp_pos (L / 8); positivity
  have part2 : g / (2 * T) * (320 * m * (1 + ee0) / (3 * log (1 + ee0)) +
      0.13 * (1 + ee0) * L ^ 5 / (exp (L / 8) * log (1 + ee0))) ≤
      g / 1.3 * (320 * (381 / 10 ^ 12) * (1 + ee0) / (3 * (145 / 1000000 / (1 + 145 / 1000000))) +
        1 / 10 ^ 12) :=
    mul_le_mul hT' (by linarith) hXn (by positivity)
  have part1 : 1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) * (2 / (1 / 2 - α) * g + 3 * εU * 106) *
      (1 + ee0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + ee0) / L + 27 / L ^ 2)) ≤
      1.00005 * (1 + 1 / 51) * (1 + 1 / 10 ^ 26) * (2 / (1 / 2 - α) * g + 3 * εU * 106) *
        (1 + ee0 + 1 / 10 ^ 12) * (0.363084 + 1 / 10 ^ 11) := by
    have h45 : 0 ≤ 4.51 / L ^ 2 := by positivity
    have hLp : 0 < L := by linarith
    have h9 : 0 ≤ 9 / L := by positivity
    gcongr
    · linarith [he2.2]
  linarith


lemma mbar_leP (g LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hLX : 9 * 10 ^ 13 ≤ LX)
    (hI : ∫ t in (2 : ℝ)..(ccP (32155 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725) :
    max (1 - fS g (ccP (32155 / 1000) LX)) (FS g (ccP (32155 / 1000) LX) - 1) ≤ 0.02177 := by
  have h1 := fS_c_geP g LX (by linarith) hLX
  obtain ⟨c1, c2⟩ := cc_boundsP LX hLX
  apply max_le
  · nlinarith
  · unfold FS
    have hgc : 2 * g / ccP (32155 / 1000) LX ≤ 2 * 1.7812 / 3.9999 := by
      apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) c1
    have hgc0 : 0 ≤ 2 * g / ccP (32155 / 1000) LX := div_nonneg (by linarith) (by linarith)
    have : 2 * g / ccP (32155 / 1000) LX * (1 + ∫ t in (2 : ℝ)..(ccP (32155 / 1000) LX - 1), log (t - 1) / t) ≤
        2 * 1.7812 / 3.9999 * (1 + 0.14725) := by
      rcases le_total 0 (1 + ∫ t in (2 : ℝ)..(ccP (32155 / 1000) LX - 1), log (t - 1) / t) with hp | hp
      · exact mul_le_mul hgc (by linarith) hp (by norm_num)
      · have : 2 * g / ccP (32155 / 1000) LX * (1 + ∫ t in (2 : ℝ)..(ccP (32155 / 1000) LX - 1), log (t - 1) / t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hgc0 hp
        have : (0 : ℝ) ≤ 2 * 1.7812 / 3.9999 * (1 + 0.14725) := by norm_num
        linarith
    norm_num at this ⊢; linarith

set_option maxHeartbeats 1000000 in
lemma cAb_geP (g T e1 a c4s w L LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (ha : 0 ≤ a ∧ a ≤ 1 / 10 ^ 18)
    (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L)
    (hI : ∫ t in (2 : ℝ)..(ccP (32155 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725) :
    8 * ((58 / 57) * (0.54930376 * g) - 1 / 57 - (58 / 57) * εU * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + εU * 107 * 0.1016) - 3 / 10 ^ 18) ≤
      cAbPU (32155 / 1000) g T e1 a c4s w L LX := by
  unfold cAbPU
  obtain ⟨c1, c2⟩ := cc_boundsP LX hLX
  set X := fS g (ccP (32155 / 1000) LX) with hX
  set H := exp 2 * h (ccP (32155 / 1000) LX) with hH
  set Mb := max (1 - fS g (ccP (32155 / 1000) LX)) (FS g (ccP (32155 / 1000) LX) - 1) with hMb
  have hXl : g * 0.54930376 ≤ X := fS_c_geP g LX (by linarith) hLX
  have hXu : X ≤ g * 0.5494 := fS_c_leP g LX (by linarith) hLX
  have hH1 : H ≤ 0.1016 := h_le _ c1
  have hH0 : 0 ≤ H := by have := h_nonneg (ccP (32155 / 1000) LX) (by linarith); positivity
  have hM : Mb ≤ 0.02177 := mbar_leP g LX hg1 hg2 hLX hI
  have hM0 : 0 ≤ Mb := le_trans (by nlinarith) (le_max_left _ _)
  have hL0 : 0 < L := by linarith
  have eq1 : (1 + e1) * εU * 107 * exp 2 * h (ccP (32155 / 1000) LX) = (1 + e1) * εU * 107 * H := by rw [hH]; ring
  have eq2 : εU * 107 * exp 2 * h (ccP (32155 / 1000) LX) = εU * 107 * H := by rw [hH]; ring
  rw [eq1, eq2]
  have t1 : e1 * (1 - X) ≤ 1 / 57 * (1 - X) :=
    mul_le_mul_of_nonneg_right he1.2 (by nlinarith)
  have t2 : (1 + e1) * εU * 107 * H ≤ (58 / 57) * εU * 107 * 0.1016 := by
    have : (1 + e1) * (εU * 107) ≤ (58 / 57) * (εU * 107) :=
      mul_le_mul_of_nonneg_right (by linarith [he1.2]) (by norm_num)
    have := mul_le_mul this hH1 hH0 (by norm_num)
    linarith
  have t3 : (3 * e1 + a) * (Mb + εU * 107 * H) ≤ (3 / 57 + 1 / 10 ^ 18) * (0.02177 + εU * 107 * 0.1016) := by
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
  set B := X - e1 * (1 - X) - (1 + e1) * εU * 107 * H - (3 * e1 + a) * (Mb + εU * 107 * H) - a -
    64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w with hB
  have hBl : (58 / 57) * (0.54930376 * g) - 1 / 57 - (58 / 57) * εU * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + εU * 107 * 0.1016) - 3 / 10 ^ 18 ≤ B := by
    rw [hB]; linarith
  have hB0 : 0 ≤ B := by linarith
  calc 8 * ((58 / 57) * (0.54930376 * g) - 1 / 57 - (58 / 57) * εU * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02177 + εU * 107 * 0.1016) - 3 / 10 ^ 18) ≤ 8 * 1 * B := by
        linarith
    _ ≤ 8 * (1 + 32.02 / L ^ 2) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0; linarith


/-- **Section 9, case (b), corrected constants, at log log X₂ = 32.155, ε₀ = 1.45·10⁻⁴:**
`cA - cQ/2 - cB/2 ≥ 2·10⁻⁴ + 10⁻¹²` from the stated numeric inputs. Lean-side margin about
`3.7·10⁻⁴` with these input bounds. -/
theorem margin_bP (g T e1 e2 cb m a c4s w l1s ls L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 381 / 10 ^ 12)
    (ha : 0 ≤ a ∧ a ≤ 1 / 10 ^ 18) (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L)
    (hI : ∫ t in (2 : ℝ)..(ccP (32155 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAbPU (32155 / 1000) g T e1 a c4s w L LX - cQbU g T e1 l1s ls L LX / 2 - cBPU ee0 g T e2 cb m L / 2 := by
  have hA := cAb_geP g T e1 a c4s w L LX hg1 hg2 hT he1 ha hc4 hw hLX hL hI
  have hQ := cQb_leU9 g T e1 l1s ls L LX (by linarith) hT he1 hl1 hls hLX hL
  have hB := cB_leP g T e2 cb m L (by linarith) hT he2 hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith
/-- **Section 9, case (a), at ε₀ = 1.45·10⁻⁴**, from the stated numeric inputs; about `0.1247 ≥ 1/10`.
Case (a) does not involve log log X₂ except through log X₂ ≥ 9·10¹³. -/
theorem margin_aP (g T e2 cb m c4 l1 l L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 381 / 10 ^ 12)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20)
    (hLX : 9 * 10 ^ 13 ≤ LX) (hL : LX ≤ L) :
    1 / 10 ≤ cAaU g T c4 L - cQaU g T l1 l L LX / 2 - cBPU ee0 g T e2 cb m L / 2 := by
  have hA := cAa_geU9 g T c4 L hg1 hg2 hT hc4 (hLX.trans hL)
  have hQ := cQa_leU9 g T l1 l L LX (by linarith) hT hl1 hls hLX hL
  have hB := cB_leP g T e2 cb m L (by linarith) hT he2 hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith


end LeanLab.ChenExplicit.At32155
