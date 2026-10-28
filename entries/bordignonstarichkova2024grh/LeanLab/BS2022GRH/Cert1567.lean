module

public import LeanLab.BS2022GRH.ChenThresholdGRH
public import LeanLab.BS2022GRH.QG

/-!
BS2022GRH, P0021, idea I-0088, unit U-1567, run 20261027T0004Z-17012: the two numeric certificates
of `ChenThresholdGRH.chenThreshold13375_of_leaves`.

* `bracket13375_holds : Bracket13375`, PROVED here, fully. At α = 0.00256, A = 10,
  ε = 1/8349, C₁ = 112, C₂ = 114, ε₁ = 10⁻²⁰, X₂ = exp(exp 13.375) and every N ≥ X₂, the
  combination 8·B5 − ½·8·B6 − ½·B7 of the journal's exact brackets, pp. 1228, 1231, 1234-1235, is
  at least K3J − 10⁻⁵. The proof compares each bracket with its K3J piece symbolically, so e^γ
  and the logs of K3J cancel; only the correction factors are bounded. The binding one is the
  li factor of Theorem 7, log Y · li(Y)/Y ≤ 1 + 1/(0.999² log Y) + 10⁻²⁹ at log Y = e^{13.375}/3,
  through one integration by parts; it costs about 6.1·10⁻⁶ of the 10⁻⁵.
* `Eps1500`, ε(1500) < 1/8349, was OPEN in this unit; it is PROVED in `Cert1575`. The lab's
  unproved placeholder `eps1500_cert` is removed from this copy.
* `chenThreshold13375_of_deep`: the threshold, CONDITIONAL ON `Thm5J`, `Thm6J`, `Thm7J`,
  `LinearSieveT4 (1/8349) 112 114` and `Eps1500`; `Bracket13375` is discharged.

AI-written Lean code, Claude, unit U-1567. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Cert1567
open Real MeasureTheory LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

/-! ### Polynomial against exponential at L ≥ 643700 -/

/-- `L¹² ≤ 10⁻³⁰ e^{cL}` for `c ≥ 1/48`, through `e^{L/48} ≥ (L/48)⁴⁰/40!`. -/
lemma tinyA {L c : ℝ} (hL : 643700 ≤ L) (hc : 1 / 48 ≤ c) : L ^ 12 ≤ 1e-30 * exp (L * c) := by
  have hL0 : 0 < L := by linarith
  have h1 : exp (L / 48) ≤ exp (L * c) := exp_le_exp.2 (by nlinarith)
  have h2 := Real.pow_div_factorial_le_exp (x := L / 48) (by positivity) 40
  have hp : (643700 : ℝ) ^ 28 ≤ L ^ 28 := pow_le_pow_left₀ (by norm_num) hL 28
  have hn : (48 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ) ≤ 1e-30 * 643700 ^ 28 := by
    norm_num [Nat.factorial]
  have hF : (0 : ℝ) < (48 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ) := by positivity
  have hq : 1 ≤ 1e-30 * L ^ 28 / ((48 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ)) := by
    rw [le_div_iff₀ hF]; linarith
  have e : (L / 48) ^ 40 / (Nat.factorial 40 : ℝ)
      = L ^ 12 * L ^ 28 / ((48 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ)) := by
    rw [div_pow, div_div]; ring
  calc L ^ 12 = L ^ 12 * 1 := by ring
    _ ≤ L ^ 12 * (1e-30 * L ^ 28 / ((48 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ))) :=
        mul_le_mul_of_nonneg_left hq (pow_nonneg hL0.le 12)
    _ = 1e-30 * ((L / 48) ^ 40 / (Nat.factorial 40 : ℝ)) := by rw [e]; ring
    _ ≤ 1e-30 * exp (L * c) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith

/-- `L² ≤ 10⁻³⁰ e^{cL}` for `c ≥ 1/3000`. -/
lemma tinyB {L c : ℝ} (hL : 643700 ≤ L) (hc : 1 / 3000 ≤ c) : L ^ 2 ≤ 1e-30 * exp (L * c) := by
  have hL0 : 0 < L := by linarith
  have h1 : exp (L / 3000) ≤ exp (L * c) := exp_le_exp.2 (by nlinarith)
  have h2 := Real.pow_div_factorial_le_exp (x := L / 3000) (by positivity) 40
  have hp : (643700 : ℝ) ^ 38 ≤ L ^ 38 := pow_le_pow_left₀ (by norm_num) hL 38
  have hn : (3000 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ) ≤ 1e-30 * 643700 ^ 38 := by
    norm_num [Nat.factorial]
  have hF : (0 : ℝ) < (3000 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ) := by positivity
  have hq : 1 ≤ 1e-30 * L ^ 38 / ((3000 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ)) := by
    rw [le_div_iff₀ hF]; linarith
  have e : (L / 3000) ^ 40 / (Nat.factorial 40 : ℝ)
      = L ^ 2 * L ^ 38 / ((3000 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ)) := by
    rw [div_pow, div_div]; ring
  calc L ^ 2 = L ^ 2 * 1 := by ring
    _ ≤ L ^ 2 * (1e-30 * L ^ 38 / ((3000 : ℝ) ^ 40 * (Nat.factorial 40 : ℝ))) :=
        mul_le_mul_of_nonneg_left hq (pow_nonneg hL0.le 2)
    _ = 1e-30 * ((L / 3000) ^ 40 / (Nat.factorial 40 : ℝ)) := by rw [e]; ring
    _ ≤ 1e-30 * exp (L * c) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith

lemma pow_le_12 {L : ℝ} (hL : 1 ≤ L) {k : ℕ} (hk : k ≤ 12) : L ^ k ≤ L ^ 12 :=
  pow_le_pow_right₀ hL hk

/-- `L^k / E ≤ 10⁻³⁰` from `L¹² ≤ 10⁻³⁰ E`. -/
lemma small_div {L E : ℝ} (hL : 1 ≤ L) {k : ℕ} (hk : k ≤ 12) (hE : 0 < E)
    (h : L ^ 12 ≤ 1e-30 * E) : L ^ k / E ≤ 1e-30 := by
  rw [div_le_iff₀ hE]; linarith [pow_le_12 hL hk]

/-! ### Constants -/

lemma L_ge : (643700 : ℝ) ≤ exp 13.375 := Journal.exp13375_ge

lemma X_ge : (4e18 : ℝ) ≤ exp (exp 13.375) := X2_ranges.1

lemma log2_bounds : (0.6931471 : ℝ) ≤ log 2 ∧ log 2 ≤ 0.6931472 := by
  have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma g_bounds' : (1.7810699 : ℝ) ≤ exp eulerMascheroniConstant ∧
    exp eulerMascheroniConstant ≤ 1.7810725 :=
  ⟨LeanLab.Helfgott2013.GammaFine.exp_gamma_gt.le, LeanLab.Helfgott2013.GammaFine.exp_gamma_lt.le⟩

lemma cb_bounds : (0.363 : ℝ) ≤ LeanLab.ChenExplicit.BJS.cbar ∧
    LeanLab.ChenExplicit.BJS.cbar ≤ 0.363084 := by
  have h1 := LeanLab.ChenExplicit.BJS.cbar_gt; have h2 := LeanLab.ChenExplicit.BJS.cbar_lt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `q_G(X) ≥ 0.16` on `X ≥ 4·10¹⁸`. -/
lemma qG_ge (X : ℝ) (hX : 4e18 ≤ X) : 0.16 ≤ qG X := by
  have hX0 : 0 < X := by linarith
  have hl : 42.83 ≤ log X := le_trans logX_bounds.1 (log_le_log (by norm_num) hX)
  have hll : 0 ≤ log (log X) := log_nonneg (by linarith)
  have h4 : 0 < X ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hX0 _
  have hs : 2e9 ≤ √X := by rw [← sqrtX]; exact Real.sqrt_le_sqrt hX
  unfold qG
  set l := log X
  have hl0 : 0 < l := by linarith
  have t1 : 0 ≤ 12.683 / l := div_nonneg (by norm_num) hl0.le
  have t2 : 0 ≤ 254.980 / l ^ 2 := div_nonneg (by norm_num) (by positivity)
  have t3 : 0 ≤ 2607.854 / l ^ 3 := div_nonneg (by norm_num) (by positivity)
  have t4 : 0 ≤ 11605.056 / l ^ 4 := div_nonneg (by norm_num) (by positivity)
  have t5 : 0 ≤ 1.314 * l / X ^ ((1 : ℝ) / 4) := div_nonneg (by positivity) h4.le
  have t6 : 0 ≤ 0.092 * log l / X ^ ((1 : ℝ) / 4) := div_nonneg (by positivity) h4.le
  have t7 : 0 ≤ 60.883 / X ^ ((1 : ℝ) / 4) := div_nonneg (by norm_num) h4.le
  have t8 : 0 ≤ 8.250 * log l / (X ^ ((1 : ℝ) / 4) * l) :=
    div_nonneg (by positivity) (by positivity)
  have t9 : 0 ≤ 939.260 / (X ^ ((1 : ℝ) / 4) * l) := div_nonneg (by norm_num) (by positivity)
  have tn : 237.934 / (√X * l) ≤ 0.005 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma qG_le1 (X : ℝ) (hX : 4e18 ≤ X) : qG X ≤ 1 := by linarith [qG_le_all X hX]

/-- `(e^{-γ} C₂)⁻¹ ≤ 3`. -/
lemma invTw_bounds : 0 ≤ invTw ∧ invTw ≤ 3 := by
  have hg := LeanLab.Helfgott2013.GammaFine.exp_gamma_lt
  have ht := LeanLab.ChenExplicit.twinC_ge_065
  unfold invTw
  have he : (1 / 1.7810725 : ℝ) ≤ exp (-eulerMascheroniConstant) := by
    rw [exp_neg, one_div]; exact inv_anti₀ (exp_pos _) hg.le
  have hp : (0.36 : ℝ) ≤ exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC := by
    have : (1 / 1.7810725 : ℝ) * (65 / 100) ≤
        exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC :=
      mul_le_mul he ht (by norm_num) (exp_pos _).le
    norm_num at this ⊢; linarith
  constructor
  · exact inv_nonneg.2 (by linarith)
  · have := inv_anti₀ (by norm_num) hp; norm_num at this ⊢; linarith

/-- `c_G(X₂) ≤ 1` at `X₂ = exp(exp 13.375)`. -/
lemma cGJ_le : cGJ (exp (exp 13.375)) ≤ 1 := by
  have hq := qG_le_all _ X_ge
  have hX := X_ge
  unfold cGJ pGJ
  rw [log_exp, log_exp]
  have hs : 1 ≤ √(exp (exp 13.375)) := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by linarith)
  have : 0.85 / (√(exp (exp 13.375)) * 13.375) ≤ 0.85 / 13.375 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  norm_num at this ⊢; linarith

lemma kA_val : kA 0.00256 = 8 * (1 / 6 - 0.00256) := rfl

lemma e2h' (x : ℝ) : x * exp 2 * hS (kA 0.00256) = x := by
  have : exp 2 * hS (kA 0.00256) = 1 := by
    unfold hS kA
    rw [if_pos (by norm_num), ← exp_add]; norm_num
  rw [mul_assoc, this, mul_one]

/-- `δ = 0.62 L / e^{L/16} ≤ 10⁻²⁹`. -/
lemma delta_small {L : ℝ} (hL : 643700 ≤ L) :
    0 ≤ 0.62 * L / exp (L * (1 / 16)) ∧ 0.62 * L / exp (L * (1 / 16)) ≤ 1e-29 := by
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have h := small_div hL1 (k := 1) (by norm_num) (exp_pos _) (tinyA hL (c := 1 / 16) (by norm_num))
  rw [pow_one] at h
  constructor
  · exact div_nonneg (by linarith) (exp_pos _).le
  · rw [mul_div_assoc]; nlinarith

/-- `rX(X₂) = e^{L/8}/(e^{L/8} − 1) ∈ [1, 1 + 10⁻²⁹]`. -/
lemma rX_bounds {L : ℝ} (hL : 643700 ≤ L) : 1 ≤ rX (exp L) ∧ rX (exp L) ≤ 1 + 1e-29 := by
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hE := tinyA hL (c := 1 / 8) (by norm_num)
  have h12 : 1 ≤ L ^ 12 := one_le_pow₀ hL1
  unfold rX
  rw [← Real.exp_mul]
  set E := exp (L * (1 / 8))
  have hE1 : 1e30 ≤ E := by linarith
  have hpos : 0 < E - 1 := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; nlinarith

/-! ### Theorem 5's bracket -/

theorem b5_ge (n : ℕ) (hn : exp (exp 13.375) ≤ (n : ℝ)) :
    8 * (2 * exp eulerMascheroniConstant * log (3 - 8 * 0.00256) / (4 - 8 * 0.00256)
      - 1 / 8349 * 114 * 3 * exp (8 * 0.00256 - 2) / (4 - 8 * 0.00256)) - 1e-8
    ≤ 8 * B5J 0.00256 10 (1 / 8349) 114 (exp (exp 13.375)) n := by
  have hL := L_ge
  have hc := cGJ_le
  obtain ⟨hI0, hI3⟩ := invTw_bounds
  obtain ⟨hg1, hg2⟩ := g_bounds'
  set L := exp (13.375 : ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogn : L ≤ log (n : ℝ) := by
    rw [← log_exp L]; exact log_le_log (exp_pos _) hn
  obtain ⟨hd0, hd1⟩ := delta_small hL
  unfold B5J
  have e8 : log (n : ℝ) ^ ((10 : ℝ) - 2) = log (n : ℝ) ^ (8 : ℕ) := by
    rw [show ((10 : ℝ) - 2) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [log_exp, ← Real.exp_mul, e8]
  set δ := 0.62 * L / exp (L * (1 / 16))
  set g := exp eulerMascheroniConstant
  set c := cGJ (exp L)
  set T := 2 * g * log (3 - 8 * 0.00256) / (4 - 8 * 0.00256)
    - 1 / 8349 * 114 * (3 * exp (8 * 0.00256 - 2) / (4 - 8 * 0.00256)) with hT
  have hlog3 : log (3 - 8 * 0.00256 : ℝ) ≤ 3 - 8 * 0.00256 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hTle : T ≤ 2 := by
    have h1 : 2 * g * log (3 - 8 * 0.00256) ≤ 2 * 1.7810725 * (3 - 8 * 0.00256 - 1) := by
      have hl0 : 0 ≤ log (3 - 8 * 0.00256 : ℝ) := log_nonneg (by norm_num)
      have := mul_le_mul hg2 hlog3 hl0 (by norm_num)
      linarith
    have h2 : 0 ≤ 1 / 8349 * 114 * (3 * exp (8 * 0.00256 - 2) / (4 - 8 * 0.00256) : ℝ) := by
      positivity
    have h3 : 2 * g * log (3 - 8 * 0.00256) / (4 - 8 * 0.00256) ≤
        2 * 1.7810725 * (3 - 8 * 0.00256 - 1) / (4 - 8 * 0.00256) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    rw [hT]; linarith
  have hδT : δ * T ≤ δ * 2 := mul_le_mul_of_nonneg_left hTle hd0
  -- the negligible term
  have hinv : (1 - δ)⁻¹ ≤ 2 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (show (1 / 2 : ℝ) ≤ 1 - δ by linarith)
    norm_num at this; linarith
  have hinv0 : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.2 (by linarith)
  have ha0 : 0 ≤ 1 / 8 * (1 - δ)⁻¹ * invTw := mul_nonneg (by linarith) hI0
  have ha1 : 1 / 8 * (1 - δ)⁻¹ * invTw ≤ 0.75 := by
    have := mul_le_mul hinv hI3 hI0 (by norm_num); linarith
  have hac : 1 / 8 * (1 - δ)⁻¹ * invTw * c ≤ 0.75 := by
    have := mul_le_mul_of_nonneg_left hc ha0; linarith
  have hD : (1e40 : ℝ) ≤ log (n : ℝ) ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num) (le_trans hL hlogn) 8
    linarith [show (1e40 : ℝ) ≤ 643700 ^ 8 by norm_num]
  have htiny : 1 / 8 * (1 - δ)⁻¹ * invTw * c / log (n : ℝ) ^ 8 ≤ 1e-40 := by
    calc _ ≤ 0.75 / log (n : ℝ) ^ 8 := div_le_div_of_nonneg_right hac (by linarith)
      _ ≤ 0.75 / 1e40 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD
      _ ≤ 1e-40 := by norm_num
  have eT : 2 * g * log (3 - 8 * 0.00256) / (4 - 8 * 0.00256)
      - 1 / 8349 * 114 * 3 * exp (8 * 0.00256 - 2) / (4 - 8 * 0.00256) = T := by rw [hT]; ring
  rw [eT]
  linarith

/-! ### Theorem 6's bracket -/

set_option maxHeartbeats 1000000 in
theorem b6_le (n : ℕ) (hn : exp (exp 13.375) ≤ (n : ℝ)) :
    B6J 0.00256 10 (1 / 8349) 112 (exp (exp 13.375)) n ≤
      (1 + 5e-5) * (exp eulerMascheroniConstant / 4 *
        (log 6 + log ((3 - 8 * 0.00256) / (3 - 18 * 0.00256))) / (1 / 2 - 0.00256)
        + log (8 / 3) * (1 / 8349) * 112) + 2e-9 := by
  have hL := L_ge
  have hc := cGJ_le
  obtain ⟨hI0, hI3⟩ := invTw_bounds
  obtain ⟨hg1, hg2⟩ := g_bounds'
  set L := exp (13.375 : ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogn : L ≤ log (n : ℝ) := by
    rw [← log_exp L]; exact log_le_log (exp_pos _) hn
  obtain ⟨hd0, hd1⟩ := delta_small hL
  obtain ⟨hr1, hr2⟩ := rX_bounds hL
  unfold B6J l1J l2J l3J
  simp only [e2h']
  have e7 : log (n : ℝ) ^ ((10 : ℝ) - 3) = log (n : ℝ) ^ (7 : ℕ) := by
    rw [show ((10 : ℝ) - 3) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e9 : log (n : ℝ) ^ ((10 : ℝ) - 1) = log (n : ℝ) ^ (9 : ℕ) := by
    rw [show ((10 : ℝ) - 1) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [log_exp, ← Real.exp_mul, e7, e9]
  set δ := 0.62 * L / exp (L * (1 / 16))
  set g := exp eulerMascheroniConstant
  set c := cGJ (exp L)
  set r := rX (exp L)
  set P := log 6 + log ((3 - 8 * 0.00256) / (3 - 18 * 0.00256) : ℝ) with hP
  have hl6 := log6_le
  have hlr := Journal.logr256_le
  have hl83 := log83_le
  have hl60 : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
  have hlr0 : 0 ≤ log ((3 - 8 * 0.00256) / (3 - 18 * 0.00256) : ℝ) := log_nonneg (by norm_num)
  have hl830 : 0 ≤ log (8 / 3 : ℝ) := log_nonneg (by norm_num)
  have hP0 : 0 ≤ P := by rw [hP]; linarith
  have hP1 : P ≤ 1.8004 := by rw [hP]; linarith
  have hk : kA 0.00256 = 12308 / 9375 := by rw [kA_val]; norm_num
  rw [hk]
  set M6 := g / 4 * P / (1 / 2 - 0.00256) + log (8 / 3) * (1 / 8349) * 112 with hM6
  have eM6 : g / 4 * P / (1 / 2 - 0.00256) = g * P * (3125 / 6218) := by ring
  have hgP0 : 0 ≤ g * P := mul_nonneg (by linarith) hP0
  have hM60 : 0 ≤ M6 := by rw [hM6, eM6]; linarith
  have hgP : g * P ≤ 1.7810725 * 1.8004 := mul_le_mul hg2 hP1 hP0 (by norm_num)
  have hM62 : M6 ≤ 2 := by rw [hM6, eM6]; linarith
  have hL2 : (410000000000 : ℝ) ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hL 2
    linarith only [this, show (410000000000 : ℝ) ≤ 643700 ^ 2 by norm_num]
  set E6 := g / 4 * (512 / ((12308 / 9375) * L ^ 2)) + 64 / L ^ 2 * (1 / 8349) * 112
    with hE6
  have hE60 : 0 ≤ E6 := by
    rw [hE6]
    have h1 : 0 ≤ g / 4 * (512 / ((12308 / 9375) * L ^ 2)) :=
      mul_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ 64 / L ^ 2 * (1 / 8349) * 112 := by positivity
    linarith
  have hE61 : E6 ≤ 1e-9 := by
    have h1 : 512 / ((12308 / 9375) * L ^ 2) ≤ 512 / ((12308 / 9375) * 410000000000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h2 : 64 / L ^ 2 * (1 / 8349) * 112 ≤ 3e-12 := by
      have := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 64 by norm_num)
        (show (0 : ℝ) < 410000000000 by norm_num) hL2
      calc 64 / L ^ 2 * (1 / 8349) * 112 ≤ 64 / 410000000000 * (1 / 8349) * 112 := by
            linarith
        _ ≤ 3e-12 := by norm_num
    have h3 : g / 4 * (512 / ((12308 / 9375) * L ^ 2)) ≤ 5e-10 :=
      calc _ ≤ 1.7810725 / 4 * (512 / ((12308 / 9375) * 410000000000)) :=
            mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
        _ ≤ 5e-10 := by norm_num
    rw [hE6]; linarith
  have hl1 : (1 + 5e-5) * (1 + δ) * r * (g / 4 * (P / (1 / 2 - 0.00256)
      + 512 / ((12308 / 9375) * L ^ 2)) + (log (8 / 3) + 64 / L ^ 2) * (1 / 8349) * 112)
      = (1 + 5e-5) * ((1 + δ) * r) * (M6 + E6) := by rw [hM6, hE6]; ring
  have hρ1 : 1 ≤ (1 + δ) * r := by
    have := mul_le_mul (show (1 : ℝ) ≤ 1 + δ by linarith) hr1 zero_le_one (by linarith)
    linarith
  have hρ2 : (1 + δ) * r ≤ 1 + 1e-28 := by
    have := mul_le_mul (show 1 + δ ≤ 1 + 1e-29 by linarith) hr2 (by linarith) (by norm_num)
    have h' : (1 + 1e-29 : ℝ) * (1 + 1e-29) ≤ 1 + 1e-28 := by norm_num
    linarith
  have hl1b : (1 + 5e-5) * ((1 + δ) * r) * (M6 + E6) ≤ (1 + 5e-5) * M6 + 1.1e-9 := by
    have := mul_le_mul_of_nonneg_right hρ2 (show 0 ≤ M6 + E6 by linarith)
    linarith
  -- l₂ and l₃
  have hl2 : c / 8 * (0.50007 + 1 / L) * invTw ≤ 1 := by
    have hiL : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    have hiL0 : 0 ≤ 1 / L := div_nonneg zero_le_one hL0.le
    have hk0 : 0 ≤ (0.50007 + 1 / L) * invTw := mul_nonneg (by linarith only [hiL0]) hI0
    have hk1 : (0.50007 + 1 / L) * invTw ≤ 4.6 := by
      have := mul_le_mul (show 0.50007 + 1 / L ≤ 1.50007 by linarith) hI3 hI0 (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_right hc hk0
    have e : c / 8 * (0.50007 + 1 / L) * invTw = c * ((0.50007 + 1 / L) * invTw) / 8 := by ring
    rw [e]; linarith
  have hl3 : (1 + δ) * (2 * g / (12308 / 9375) + 1 / 8349 * 112) * c ≤ 3 := by
    have eg : 2 * g / (12308 / 9375) = g * (9375 / 6154) := by ring
    have hx : 2 * g / (12308 / 9375) + 1 / 8349 * 112 ≤ 2.75 := by rw [eg]; linarith
    have hx0 : 0 ≤ 2 * g / (12308 / 9375) + 1 / 8349 * 112 := by rw [eg]; linarith
    have hk0 : 0 ≤ (1 + δ) * (2 * g / (12308 / 9375) + 1 / 8349 * 112) :=
      mul_nonneg (by linarith) hx0
    have hk1 : (1 + δ) * (2 * g / (12308 / 9375) + 1 / 8349 * 112) ≤ 3 := by
      have := mul_le_mul (show 1 + δ ≤ 1.0001 by linarith) hx hx0 (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_left hc hk0
    linarith
  have hD7 : (1e40 : ℝ) ≤ log (n : ℝ) ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num) (le_trans hL hlogn) 7
    linarith [show (1e40 : ℝ) ≤ 643700 ^ 7 by norm_num]
  have hD9 : (1e40 : ℝ) ≤ log (n : ℝ) ^ 9 := by
    have := pow_le_pow_left₀ (by norm_num) (le_trans hL hlogn) 9
    linarith [show (1e40 : ℝ) ≤ 643700 ^ 9 by norm_num]
  have ht2 : c / 8 * (0.50007 + 1 / L) * invTw / log (n : ℝ) ^ 7 ≤ 1e-40 :=
    calc _ ≤ 1 / log (n : ℝ) ^ 7 := div_le_div_of_nonneg_right hl2 (le_trans (by norm_num) hD7)
      _ ≤ 1 / 1e40 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD7
      _ = 1e-40 := by norm_num
  have ht3 : (1 + δ) * (2 * g / (12308 / 9375) + 1 / 8349 * 112) * c / log (n : ℝ) ^ 9
      ≤ 3e-40 :=
    calc _ ≤ 3 / log (n : ℝ) ^ 9 := div_le_div_of_nonneg_right hl3 (le_trans (by norm_num) hD9)
      _ ≤ 3 / 1e40 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD9
      _ = 3e-40 := by norm_num
  have eM : g / 4 * P / (1 / 2 - 0.00256) + log (8 / 3) * (1 / 8349) * 112 = M6 := by rw [hM6]
  linarith only [hl1, hl1b, ht2, ht3]

/-! ### Theorem 7's li factor, by one integration by parts -/

lemma intervalIntegrable_inv_log_sq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / log t ^ 2) volume a b := by
  have hc : ContinuousOn (fun t : ℝ => 1 / log t ^ 2) (Set.Icc a b) := by
    apply continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2)
    · intro t ht; exact pow_ne_zero 2 (log_pos (lt_of_lt_of_le ha ht.1)).ne'
    · intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  exact (hc.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable

lemma integral_inv_log_sq_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / log t ^ 2 ≤ (b - a) / log a ^ 2 := by
  have hla : 0 < log a := log_pos ha
  have := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_sq ha hab)
    (intervalIntegrable_const (c := 1 / log a ^ 2)) (fun t ht => by
      have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hla.le (log_le_log (by linarith) ht.1) 2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  rw [div_eq_mul_one_div (b - a)]; exact this

/-- `∫ₐᵇ dt/log t = b/log b − a/log a + ∫ₐᵇ dt/log² t`. -/
lemma integral_inv_log_ibp {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / log t = b / log b - a / log a + ∫ t in a..b, 1 / log t ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => t / log t) (1 / log t - 1 / log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos ht1).ne'
    have := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
    convert this using 1
    field_simp
  have hi1 := intervalIntegrable_inv_log ha hab
  have hi2 := intervalIntegrable_inv_log_sq ha hab
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at this
  linarith

/-- `li(e^T) ≤ e^T/T + e^{0.999T}/log² 2 + e^T/(0.999T)² + 2` for `T ≥ 1000`. -/
lemma li_upper {T : ℝ} (hT : 1000 ≤ T) :
    liPV (exp T) ≤ exp T / T + exp (0.999 * T) / log 2 ^ 2 + exp T / (0.999 * T) ^ 2 + 2 := by
  set Y := exp T with hY
  set w := exp (0.999 * T) with hw
  have hY2 : 2 ≤ Y := by have := add_one_le_exp T; linarith
  have hw2 : 2 ≤ w := by have := add_one_le_exp (0.999 * T); linarith
  have hwY : w ≤ Y := exp_le_exp.2 (by linarith)
  have hli := liPV_le hY2
  have hibp := integral_inv_log_ibp (a := 2) (b := Y) (by norm_num) hY2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log_sq (a := 2) (b := w) (by norm_num) hw2)
    (intervalIntegrable_inv_log_sq (a := w) (b := Y) (by linarith) hwY)
  have h1 := integral_inv_log_sq_le (a := 2) (b := w) (by norm_num) hw2
  have h2 := integral_inv_log_sq_le (a := w) (b := Y) (by linarith) hwY
  have hlY : log Y = T := log_exp T
  have hlw : log w = 0.999 * T := log_exp _
  rw [hlw] at h2
  rw [hlY] at hibp
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hT0 : 0 < 0.999 * T := by linarith
  have k1 : (w - 2) / log 2 ^ 2 ≤ w / log 2 ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have k2 : (Y - w) / (0.999 * T) ^ 2 ≤ Y / (0.999 * T) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have k3 : 0 ≤ 2 / log 2 := by positivity
  linarith

/-- **The li factor of Theorem 7** at `log Y = L/3`, `L ≥ 643700`:
`log Y · (li Y + Y^{1/2} log Y/(8π))/Y ≤ 1 + 4.6702·10⁻⁶`. -/
lemma li_factor {L : ℝ} (hL : 643700 ≤ L) :
    L * (1 / 3) * (liPV (exp (L * (1 / 3))) + exp (L * (1 / 6)) * (L * (1 / 3)) / (8 * π))
      / exp (L * (1 / 3)) ≤ 1 + 4.6702e-6 := by
  have hL0 : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have tB := tinyB hL (c := 1 / 3000) (by norm_num)
  have tA6 := tinyA hL (c := 1 / 6) (by norm_num)
  have tA3 := tinyA hL (c := 1 / 3) (by norm_num)
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL12 : L ≤ L ^ 12 := by
    have := pow_le_12 hL1 (k := 1) (by norm_num); rwa [pow_one] at this
  have hL212 : L ^ 2 ≤ L ^ 12 := pow_le_12 hL1 (by norm_num)
  have hpi : 25 ≤ 8 * π := by have := Real.pi_gt_d2; linarith
  have hl2 := log2_bounds
  have hl2ne : log 2 ≠ 0 := by linarith [hl2.1]
  have hlsq : 0.48 ≤ log 2 ^ 2 := by nlinarith [hl2.1]
  have hli := li_upper (T := L * (1 / 3)) (by linarith)
  have hYw : exp (L * (1 / 3)) = exp (0.999 * (L * (1 / 3))) * exp (L * (1 / 3000)) := by
    rw [← exp_add]; congr 1; ring
  have hYh : exp (L * (1 / 3)) = exp (L * (1 / 6)) * exp (L * (1 / 6)) := by
    rw [← exp_add]; congr 1; ring
  set T := L * (1 / 3) with hTdef
  set Y := exp T with hY
  set w := exp (0.999 * T) with hw
  set e1 := exp (L * (1 / 3000)) with he1
  set h2 := exp (L * (1 / 6)) with hh2
  have hT3 : 643700 / 3 ≤ T := by rw [hTdef]; linarith
  have hT0 : 0 < T := by linarith
  have hY0 : 0 < Y := exp_pos _
  have hw0 : 0 < w := exp_pos _
  have he0 : 0 < e1 := exp_pos _
  have hh0 : 0 < h2 := exp_pos _
  have hTL : T ≤ L := by rw [hTdef]; linarith
  have hTe : T ≤ 1e-30 * e1 := by linarith
  have hTY : T ≤ 1e-30 * Y := by linarith
  have hT2 : T ^ 2 ≤ 1e-30 * h2 := by
    have : T ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hT0.le hTL 2
    linarith
  rw [div_le_iff₀ hY0]
  have hTli : T * liPV Y ≤ Y + T * w / log 2 ^ 2 + Y / (0.998001 * T) + 2 * T := by
    have := mul_le_mul_of_nonneg_left hli hT0.le
    have e : T * (Y / T + w / log 2 ^ 2 + Y / (0.999 * T) ^ 2 + 2)
        = Y + T * w / log 2 ^ 2 + Y / (0.998001 * T) + 2 * T := by
      field_simp; ring
    linarith
  have k1 : T * w / log 2 ^ 2 ≤ 3e-30 * Y := by
    have : T * w ≤ 1e-30 * Y := by
      rw [hYw]; have := mul_le_mul_of_nonneg_right hTe hw0.le; linarith
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hlsq (show 0 ≤ 3e-30 * Y by positivity)
    linarith
  have k2 : Y / (0.998001 * T) ≤ 4.6699e-6 * Y := by
    rw [div_le_iff₀ (by positivity)]
    have hk : 1 ≤ 4.6699e-6 * (0.998001 * T) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hk hY0.le]
  have k3 : h2 * T / (8 * π) * T ≤ 1e-30 * Y / 25 := by
    have : h2 * T * T ≤ 1e-30 * Y := by
      rw [hYh]; have := mul_le_mul_of_nonneg_left hT2 hh0.le; nlinarith
    rw [show h2 * T / (8 * π) * T = h2 * T * T / (8 * π) by ring]
    exact div_le_div₀ (mul_nonneg (by norm_num) hY0.le) this (by norm_num) hpi
  have e2 : T * (liPV Y + h2 * T / (8 * π)) = T * liPV Y + h2 * T / (8 * π) * T := by ring
  linarith

/-! ### m̄ at X₂, crude but enough: m̄ ≤ 40 -/

lemma Mphi_bounds {x : ℝ} (hx : exp 3 ≤ x) : 0 ≤ Mphi x ∧ Mphi x ≤ 3 := by
  have he3 : (1 : ℝ) ≤ exp 3 := one_le_exp (by norm_num)
  have hx1 : 1 ≤ x := le_trans he3 hx
  have hl : 3 ≤ log x := (Real.le_log_iff_exp_le (by linarith)).2 hx
  have hs : 1 ≤ √x := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hx1
  unfold Mphi
  have hm1 : min (2.44 / (√x * log x)) (11 / (√x * log x ^ 2)) ≤ 2.44 / (√x * log x) :=
    min_le_left _ _
  have hm0 : 0 ≤ min (2.44 / (√x * log x)) (11 / (√x * log x ^ 2)) :=
    le_min (div_nonneg (by norm_num) (by positivity)) (div_nonneg (by norm_num) (by positivity))
  have h1 : 2.44 / (√x * log x) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h2 : 1.333 / log x ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h20 : 0 ≤ 1.333 / log x := div_nonneg (by norm_num) (by linarith)
  constructor <;> linarith

lemma exp9_le : exp (9 : ℝ) ≤ 8104 := by
  have h := Real.exp_one_lt_d9
  have e : exp (9 : ℝ) = exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : exp 1 ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := pow_le_pow_left₀ (exp_pos _).le h.le 9
  have h2 : (2.7182818286 : ℝ) ^ 9 ≤ 8104 := by norm_num
  linarith

lemma w_ge {L : ℝ} (hL : 643700 ≤ L) : (4e18 : ℝ) ≤ exp (L * (1 / 8)) :=
  exp44_ge.trans (exp_le_exp.2 (by linarith))

lemma Mphi0_bounds {L : ℝ} (hL : 643700 ≤ L) :
    0 ≤ Mphi0 (exp (L * (1 / 8))) ∧ Mphi0 (exp (L * (1 / 8))) ≤ 3 := by
  have hL0 : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hw := w_ge hL
  have hq1 := qG_le_all _ hw
  have hq0 := qG_ge _ hw
  have hl2 := log2_bounds
  unfold Mphi0
  apply Mphi_bounds
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul, log_exp]
  set q := qG (exp (L * (1 / 8)))
  have hD0 : 0 < 2 * log 2 * q * (L * (1 / 8)) := by
    have : 0 < log (2 : ℝ) := by linarith
    positivity
  have hD1 : 2 * log 2 * q * (L * (1 / 8)) ≤ 0.12 * L := by
    have : 2 * log 2 * q ≤ 2 * 0.6931472 * 0.63995 := by
      have := mul_le_mul (show 2 * log 2 ≤ 2 * 0.6931472 by linarith) hq1 (by linarith)
        (by norm_num)
      linarith
    nlinarith
  have hE := tinyA hL (c := 1 / 8 * (1 / 2)) (by norm_num)
  have hL12 : L ≤ L ^ 12 := by
    have := pow_le_12 hL1 (k := 1) (by norm_num); rwa [pow_one] at this
  have hbase : exp 9 ≤ exp (L * (1 / 8) * (1 / 2)) / (2 * log 2 * q * (L * (1 / 8))) := by
    rw [le_div_iff₀ hD0]
    have h9 := exp9_le
    have : exp 9 * (2 * log 2 * q * (L * (1 / 8))) ≤ 8104 * (0.12 * L) :=
      mul_le_mul h9 hD1 hD0.le (by norm_num)
    rw [show L * (1 / 8) * (1 / 2) = L * (1 / 8 * (1 / 2)) by ring]
    nlinarith
  have h3 : exp (3 : ℝ) = exp 9 ^ (1 / 3 : ℝ) := by rw [← Real.exp_mul]; norm_num
  rw [h3]
  exact Real.rpow_le_rpow (exp_pos _).le hbase (by norm_num)

lemma rpow_third_le {x : ℝ} (hx : 1 ≤ x) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : x ^ e ≤ x := by
  have := Real.rpow_le_rpow_of_exponent_le hx he1
  rwa [Real.rpow_one] at this

set_option maxHeartbeats 1000000 in
/-- **m̄(X₂, 10, X₂^{1/8}) ≤ 40**; the true value is about 5.8. -/
lemma mbar_le {L : ℝ} (hL : 643700 ≤ L) (hLL : log L = 13.375) :
    mbarJ (exp L) 10 (exp (L * (1 / 8))) ≤ 40 := by
  have hL0 : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hw := w_ge hL
  have hl2 := log2_bounds
  have hl20 : 0 < log (2 : ℝ) := by linarith
  obtain ⟨hM00, hM03⟩ := Mphi0_bounds hL
  have hq1 := qG_le1 _ hw
  have hq0 := qG_ge _ hw
  have hw2 : (4e18 : ℝ) ≤ 2 * exp (L * (1 / 8)) := by linarith
  have hq21 := qG_le_all _ hw2
  have hq20 := qG_ge _ hw2
  unfold mbarJ
  rw [Real.log_sqrt (exp_pos L).le]
  simp only [log_exp]
  have e11 : L ^ ((10 : ℝ) + 1) = L ^ (11 : ℕ) := by
    rw [show ((10 : ℝ) + 1) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e12 : L ^ ((10 : ℝ) + 2) = L ^ (12 : ℕ) := by
    rw [show ((10 : ℝ) + 2) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hLL, e11, e12]
  have hsN : √(exp L) = exp (L * (1 / 2)) := by rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  rw [hsN]
  set w := exp (L * (1 / 8)) with hwdef
  set M0 := Mphi0 w
  set q := qG w
  set b1 := 2 * qG (2 * w) * log 2 with hb1
  -- Mphi at √N / L¹¹
  have hM1 : 0 ≤ Mphi (exp (L * (1 / 2)) / L ^ 11) ∧ Mphi (exp (L * (1 / 2)) / L ^ 11) ≤ 3 := by
    apply Mphi_bounds
    have hE := tinyA hL (c := 1 / 2) (by norm_num)
    have he3 : exp (3 : ℝ) ≤ 21 := by
      have h := Real.exp_one_lt_d9
      have e : exp (3 : ℝ) = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have := pow_le_pow_left₀ (exp_pos 1).le h.le 3
      have h3 : (2.7182818286 : ℝ) ^ 3 ≤ 21 := by norm_num
      linarith
    have hL11 : 0 < L ^ 11 := pow_pos hL0 11
    rw [le_div_iff₀ hL11]
    have h1 : L ^ 11 * 21 ≤ L ^ 12 := by
      rw [show L ^ 12 = L ^ 11 * L by ring]
      exact mul_le_mul_of_nonneg_left (by linarith) hL11.le
    have h2 := mul_le_mul_of_nonneg_left he3 hL11.le
    have h12 : 1 ≤ L ^ 12 := one_le_pow₀ hL1
    rw [show L * (1 / 2) = L * (1 / 2) by rfl]
    linarith only [h1, h2, hE, h12]
  obtain ⟨hM10, hM13⟩ := hM1
  -- rpow pieces
  have hq13 : q ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one (by linarith) hq1 (by norm_num)
  have hq130 : 0 ≤ q ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hl23 : (2 * log 2) ^ (-(2 / 3) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hl230 : 0 ≤ (2 * log 2) ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg (by linarith) _
  have h213 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := rpow_third_le (by norm_num) (by norm_num) (by norm_num)
  have h2130 : 0 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hlog2w : log (2 * w) = log 2 + L * (1 / 8) := by
    rw [Real.log_mul (by norm_num) (exp_pos _).ne', log_exp]
  have hlw1 : 1 ≤ log (2 * w) := by rw [hlog2w]; linarith
  have hlw13 : log (2 * w) ^ (1 / 3 : ℝ) ≤ L := by
    have := rpow_third_le hlw1 (e := 1 / 3) (by norm_num) (by norm_num)
    rw [hlog2w] at this ⊢; linarith
  have hlw130 : 0 ≤ log (2 * w) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  simp only [hwdef, ← Real.exp_mul]
  rw [← hwdef]
  -- second term
  have hT2 : q ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
      ((2 : ℝ) ^ (1 / 3 : ℝ) * L ^ 11 * log (2 * w) ^ (1 / 3 : ℝ) / exp (L * (1 / 8) * (1 / 6)))
      * (1 + M0) ≤ 8e-30 := by
    have hE := tinyA hL (c := 1 / 8 * (1 / 6)) (by norm_num)
    rw [show L * (1 / 8 * (1 / 6)) = L * (1 / 8) * (1 / 6) by ring] at hE
    have hin : (2 : ℝ) ^ (1 / 3 : ℝ) * L ^ 11 * log (2 * w) ^ (1 / 3 : ℝ) ≤ 2 * L ^ 12 := by
      have hL11 : 0 ≤ L ^ 11 := pow_nonneg hL0.le 11
      have := mul_le_mul (mul_le_mul h213 (le_refl (L ^ 11)) hL11 (by norm_num)) hlw13 hlw130
        (by positivity)
      rw [show 2 * L ^ 12 = 2 * L ^ 11 * L by ring]; exact this
    have hin0 : 0 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) * L ^ 11 * log (2 * w) ^ (1 / 3 : ℝ) :=
      mul_nonneg (mul_nonneg h2130 (pow_nonneg hL0.le 11)) hlw130
    have hfr : (2 : ℝ) ^ (1 / 3 : ℝ) * L ^ 11 * log (2 * w) ^ (1 / 3 : ℝ)
        / exp (L * (1 / 8) * (1 / 6)) ≤ 2e-30 := by
      rw [div_le_iff₀ (exp_pos _)]; linarith
    have hfr0 : 0 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) * L ^ 11 * log (2 * w) ^ (1 / 3 : ℝ)
        / exp (L * (1 / 8) * (1 / 6)) := div_nonneg hin0 (exp_pos _).le
    have hA : q ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) ≤ 1 := mul_le_one₀ hq13 hl230 hl23
    have hA0 : 0 ≤ q ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) := mul_nonneg hq130 hl230
    calc _ ≤ 1 * 2e-30 * (1 + 3) :=
          mul_le_mul (mul_le_mul hA hfr hfr0 zero_le_one) (by linarith) (by linarith)
            (by norm_num)
      _ = 8e-30 := by norm_num
  -- third term
  have hT3 : L ^ 11 * (exp (L * (1 / 8) * (-(1 / 2))) + (2 * w / exp L) ^ (1 / 2 : ℝ)) / log 2
      ≤ 3e-30 := by
    have hE := tinyA hL (c := 1 / 16) (by norm_num)
    have e1 : exp (L * (1 / 8) * (-(1 / 2))) = (exp (L * (1 / 16)))⁻¹ := by
      rw [← exp_neg]; congr 1; ring
    have hs : (2 * w / exp L) ^ (1 / 2 : ℝ) ≤ (exp (L * (1 / 16)))⁻¹ := by
      rw [← Real.sqrt_eq_rpow]
      have e1 : 2 * w / exp L = 2 * exp (-(L * (7 / 8))) := by
        rw [hwdef, mul_div_assoc, ← Real.exp_sub]; congr 2; ring
      have e2 : (exp (L * (1 / 16)))⁻¹ ^ 2 = exp (-(L * (1 / 8))) := by
        rw [← exp_neg, sq, ← exp_add]; congr 1; ring
      have e3 : exp (-(L * (1 / 8))) = exp (L * (3 / 4)) * exp (-(L * (7 / 8))) := by
        rw [← exp_add]; congr 1; ring
      have h34 : 2 ≤ exp (L * (3 / 4)) := by
        have := add_one_le_exp (L * (3 / 4)); linarith
      have hsq : 2 * w / exp L ≤ (exp (L * (1 / 16)))⁻¹ ^ 2 := by
        rw [e1, e2, e3]
        exact mul_le_mul_of_nonneg_right h34 (exp_pos _).le
      calc √(2 * w / exp L) ≤ √((exp (L * (1 / 16)))⁻¹ ^ 2) := Real.sqrt_le_sqrt hsq
        _ = (exp (L * (1 / 16)))⁻¹ := Real.sqrt_sq (inv_nonneg.2 (exp_pos _).le)
    have hs0 : 0 ≤ (2 * w / exp L) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (div_nonneg (by positivity) (exp_pos _).le) _
    rw [e1]
    have hk : L ^ 11 * (exp (L * (1 / 16)))⁻¹ ≤ 1e-30 := by
      have := small_div hL1 (k := 11) (by norm_num) (exp_pos _) hE
      rwa [div_eq_mul_inv] at this
    have hsum : L ^ 11 * ((exp (L * (1 / 16)))⁻¹ + (2 * w / exp L) ^ (1 / 2 : ℝ)) ≤ 2e-30 := by
      have := mul_le_mul_of_nonneg_left hs (pow_nonneg hL0.le 11)
      linarith only [this, hk]
    calc _ ≤ 2e-30 / log 2 := div_le_div_of_nonneg_right hsum hl20.le
      _ ≤ 2e-30 / 0.6931471 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl2.1
      _ ≤ 3e-30 := by norm_num
  -- fourth term
  have hb10 : 0.2 ≤ b1 := by rw [hb1]; nlinarith
  have hb11 : b1 ≤ 1 := by
    rw [hb1]
    have := mul_le_mul (show 2 * qG (2 * w) ≤ 2 * 0.63995 by linarith) hl2.2 hl20.le
      (by norm_num)
    linarith
  have hb23 : b1 ^ (-(2 / 3) : ℝ) ≤ 5 := by
    have := Real.rpow_le_rpow_of_exponent_ge (by linarith) hb11
      (show (-1 : ℝ) ≤ -(2 / 3) by norm_num)
    rw [Real.rpow_neg_one] at this
    have h5 : b1⁻¹ ≤ 5 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 0.2) hb10; norm_num at this ⊢; linarith
    linarith
  have hb13 : b1 ^ (-(1 / 3) : ℝ) ≤ 5 := by
    have := Real.rpow_le_rpow_of_exponent_ge (by linarith) hb11
      (show (-1 : ℝ) ≤ -(1 / 3) by norm_num)
    rw [Real.rpow_neg_one] at this
    have h5 : b1⁻¹ ≤ 5 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 0.2) hb10; norm_num at this ⊢; linarith
    linarith
  have hb230 : 0 ≤ b1 ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hb130 : 0 ≤ b1 ^ (-(1 / 3) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hlw23 : 1 ≤ (L * (1 / 8)) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlw13' : 1 ≤ (L * (1 / 8)) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hll : 1 ≤ log (L / 2 - (10 + 1) * 13.375) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    linarith
  have hT4 : M0 * (b1 ^ (-(2 / 3) : ℝ) * (L ^ 11 / (exp (L * (1 / 8) * (2 / 3)) *
        (L * (1 / 8)) ^ (2 / 3 : ℝ)))
      + 0.69205 * b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * exp (L * (1 / 8) * (5 / 6)) *
        (L * (1 / 8)) ^ (1 / 3 : ℝ) * log (L / 2 - (10 + 1) * 13.375)))) ≤ 1e-28 := by
    have hE1 := tinyA hL (c := 1 / 8 * (2 / 3)) (by norm_num)
    have hE2 := tinyA hL (c := 1 / 8 * (5 / 6)) (by norm_num)
    rw [show L * (1 / 8 * (2 / 3)) = L * (1 / 8) * (2 / 3) by ring] at hE1
    rw [show L * (1 / 8 * (5 / 6)) = L * (1 / 8) * (5 / 6) by ring] at hE2
    set E1 := exp (L * (1 / 8) * (2 / 3))
    set E2 := exp (L * (1 / 8) * (5 / 6))
    have hE10 : 0 < E1 := exp_pos _
    have hE20 : 0 < E2 := exp_pos _
    have p1 : L ^ 11 / (E1 * (L * (1 / 8)) ^ (2 / 3 : ℝ)) ≤ 1e-30 := by
      calc _ ≤ L ^ 11 / E1 := div_le_div_of_nonneg_left (pow_nonneg hL0.le 11) hE10
            (le_mul_of_one_le_right hE10.le hlw23)
        _ ≤ 1e-30 := small_div hL1 (by norm_num) hE10 hE1
    have p2 : L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) * log (L / 2 - (10 + 1) * 13.375))
        ≤ 1e-30 := by
      have h1 : E2 ≤ 2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) := by
        have := le_mul_of_one_le_right hE20.le hlw13'
        linarith only [this, hE20]
      have h0 : 0 ≤ 2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) := by linarith only [h1, hE20]
      have hden : E2 ≤ 2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) * log (L / 2 - (10 + 1) * 13.375) :=
        le_trans h1 (le_mul_of_one_le_right h0 hll)
      calc _ ≤ L ^ 12 / E2 := div_le_div_of_nonneg_left (pow_nonneg hL0.le 12) hE20 hden
        _ ≤ 1e-30 := small_div hL1 (by norm_num) hE20 hE2
    have hlw0 : 0 ≤ (L * (1 / 8)) ^ (2 / 3 : ℝ) := by linarith only [hlw23]
    have hlw0' : 0 ≤ (L * (1 / 8)) ^ (1 / 3 : ℝ) := by linarith only [hlw13']
    have p10 : 0 ≤ L ^ 11 / (E1 * (L * (1 / 8)) ^ (2 / 3 : ℝ)) :=
      div_nonneg (pow_nonneg hL0.le 11) (mul_nonneg hE10.le hlw0)
    have p20 : 0 ≤ L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375)) :=
      div_nonneg (pow_nonneg hL0.le 12)
        (mul_nonneg (mul_nonneg (by linarith only [hE20]) hlw0') (by linarith only [hll]))
    have s1 : b1 ^ (-(2 / 3) : ℝ) * (L ^ 11 / (E1 * (L * (1 / 8)) ^ (2 / 3 : ℝ))) ≤ 5 * 1e-30 :=
      mul_le_mul hb23 p1 p10 (by norm_num)
    have s2' : b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375))) ≤ 5 * 1e-30 := mul_le_mul hb13 p2 p20 (by norm_num)
    have s20 : 0 ≤ b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375))) := mul_nonneg hb130 p20
    have s10 : 0 ≤ b1 ^ (-(2 / 3) : ℝ) * (L ^ 11 / (E1 * (L * (1 / 8)) ^ (2 / 3 : ℝ))) :=
      mul_nonneg hb230 p10
    have hsum : b1 ^ (-(2 / 3) : ℝ) * (L ^ 11 / (E1 * (L * (1 / 8)) ^ (2 / 3 : ℝ)))
      + 0.69205 * b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375))) ≤ 1e-29 := by
      have e : 0.69205 * b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375))) = 0.69205 * (b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 /
        (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) * log (L / 2 - (10 + 1) * 13.375)))) := by ring
      rw [e]; linarith only [s1, s2']
    have s0 : 0 ≤ b1 ^ (-(2 / 3) : ℝ) * (L ^ 11 / (E1 * (L * (1 / 8)) ^ (2 / 3 : ℝ)))
      + 0.69205 * b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375))) := by
      have e : 0.69205 * b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) *
        log (L / 2 - (10 + 1) * 13.375))) = 0.69205 * (b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 /
        (2 * E2 * (L * (1 / 8)) ^ (1 / 3 : ℝ) * log (L / 2 - (10 + 1) * 13.375)))) := by ring
      rw [e]; linarith only [s10, s20]
    have := mul_le_mul hM03 hsum s0 (by norm_num)
    linarith only [this]
  have hT1 : 2 / log 2 ≤ 2.8854 := by
    rw [div_le_iff₀ hl20]; linarith [hl2.1]
  set S := 2 / log 2 + q ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
      ((2 : ℝ) ^ (1 / 3 : ℝ) * L ^ 11 * log (2 * w) ^ (1 / 3 : ℝ) / exp (L * (1 / 8) * (1 / 6)))
      * (1 + M0)
    + L ^ 11 * (exp (L * (1 / 8) * (-(1 / 2))) + (2 * w / exp L) ^ (1 / 2 : ℝ)) / log 2
    + M0 * (b1 ^ (-(2 / 3) : ℝ) * (L ^ 11 / (exp (L * (1 / 8) * (2 / 3)) *
        (L * (1 / 8)) ^ (2 / 3 : ℝ)))
      + 0.69205 * b1 ^ (-(1 / 3) : ℝ) * (L ^ 12 / (2 * exp (L * (1 / 8) * (5 / 6)) *
        (L * (1 / 8)) ^ (1 / 3 : ℝ) * log (L / 2 - (10 + 1) * 13.375)))) with hS
  have hS3 : S ≤ 2.9 := by rw [hS]; linarith
  have h1 := mul_le_mul_of_nonneg_left hS3 (show 0 ≤ 2 * Mphi (exp (L * (1 / 2)) / L ^ 11) by
      linarith only [hM10])
  have h2 : 2 * Mphi (exp (L * (1 / 2)) / L ^ 11) * 2.9 ≤ 2 * 3 * 2.9 := by
    linarith only [hM13]
  linarith only [h1, h2]

/-! ### Theorem 7's bracket -/

set_option maxHeartbeats 1000000 in
theorem b7_le :
    B7J 0.00256 10 (1 / 8349) 112 (exp (exp 13.375)) 1e-20 ≤
      (2 * exp eulerMascheroniConstant / (1 / 2 - 0.00256) + 3 * (1 / 8349) * 112)
        * LeanLab.ChenExplicit.BJS.cbar + 1.23e-5 := by
  have hL := L_ge
  have hLL : log (exp (13.375 : ℝ)) = 13.375 := log_exp _
  obtain ⟨hI0, hI3⟩ := invTw_bounds
  obtain ⟨hg1, hg2⟩ := g_bounds'
  obtain ⟨hcb0, hcb1⟩ := cb_bounds
  set L := exp (13.375 : ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hm := mbar_le hL hLL
  have hF3 := li_factor hL
  unfold B7J
  simp only [← Real.exp_mul]
  simp only [log_exp]
  have e6 : L ^ ((10 : ℝ) - 4) = L ^ (6 : ℕ) := by
    rw [show ((10 : ℝ) - 4) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e11 : L ^ ((10 : ℝ) + 1) = L ^ (11 : ℕ) := by
    rw [show ((10 : ℝ) + 1) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e6, e11]
  set g := exp eulerMascheroniConstant
  set cb := LeanLab.ChenExplicit.BJS.cbar
  set m := mbarJ (exp L) 10 (exp (L * (1 / 8)))
  set F3 := L * (1 / 3) * (liPV (exp (L * (1 / 3))) + exp (L * (1 / 6)) * (L * (1 / 3)) / (8 * π))
    / exp (L * (1 / 3))
  -- F1
  have hF1 : 1 + 0.06 * L / exp (L * (1 / 6)) ≤ 1 + 1e-29 := by
    have := small_div hL1 (k := 1) (by norm_num) (exp_pos _) (tinyA hL (c := 1 / 6) (by norm_num))
    rw [pow_one] at this
    rw [mul_div_assoc]; linarith only [this]
  have hF10 : 1 ≤ 1 + 0.06 * L / exp (L * (1 / 6)) := by
    have : 0 ≤ 0.06 * L / exp (L * (1 / 6)) := div_nonneg (by linarith) (exp_pos _).le
    linarith
  -- F2
  have hF2 : 2 / (1 / 2 - 0.00256) * g + 3 * (1 / 8349) * 112 ≤ 7.21 := by
    have : 2 / (1 / 2 - 0.00256) * g ≤ 2 / (1 / 2 - 0.00256) * 1.7810725 :=
      mul_le_mul_of_nonneg_left hg2 (by norm_num)
    norm_num at this ⊢; linarith
  have hF20 : 0 ≤ 2 / (1 / 2 - 0.00256) * g + 3 * (1 / 8349) * 112 :=
    add_nonneg (mul_nonneg (by norm_num) (by linarith only [hg1])) (by norm_num)
  -- F4
  set s := log √(1 + 1e-20 : ℝ) with hs
  have hsq1 : (1 : ℝ) ≤ √(1 + 1e-20 : ℝ) := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs0 : 0 ≤ s := log_nonneg hsq1
  have hs1 : s ≤ 1e-20 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < √(1 + 1e-20) by linarith)
    have h2 : √(1 + 1e-20 : ℝ) ≤ 1 + 1e-20 := by
      calc √(1 + 1e-20 : ℝ) ≤ √((1 + 1e-20) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
        _ = 1 + 1e-20 := Real.sqrt_sq (by norm_num)
    linarith
  have hD : 1 ≤ (L * (1 / 3)) ^ 2 - s ^ 2 := by
    have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0 (by linarith only [hs1])
    have h3 : (2 : ℝ) ^ 2 ≤ (L * (1 / 3)) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    linarith only [hs2, h3]
  have hsD : s / ((L * (1 / 3)) ^ 2 - s ^ 2) ≤ 1e-20 :=
    le_trans (div_le_self hs0 hD) hs1
  have hsD0 : 0 ≤ s / ((L * (1 / 3)) ^ 2 - s ^ 2) := div_nonneg hs0 (by linarith)
  have hL2 : (410000000000 : ℝ) ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hL 2
    linarith only [this, show (410000000000 : ℝ) ≤ 643700 ^ 2 by norm_num]
  have i36 : 36 / L ^ 2 ≤ 36 / 410000000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
  have i64 : 64 / L ^ 2 ≤ 64 / 410000000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
  have i27 : 27 / L ^ 2 ≤ 27 / 410000000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
  have hl83 := log83_le
  have hl830 : 0 ≤ log (8 / 3 : ℝ) := log_nonneg (by norm_num)
  have hF4 : cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) *
      (s / ((L * (1 / 3)) ^ 2 - s ^ 2) + 27 / L ^ 2) ≤ cb + 1.6e-10 := by
    have hp : (log (8 / 3) + 64 / L ^ 2) * (s / ((L * (1 / 3)) ^ 2 - s ^ 2) + 27 / L ^ 2)
        ≤ (0.98083 + 64 / 410000000000) * (1e-20 + 27 / 410000000000) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    norm_num at hp i36 ⊢; linarith
  have hF40 : 0 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) *
      (s / ((L * (1 / 3)) ^ 2 - s ^ 2) + 27 / L ^ 2) := by
    have h1 : 0 ≤ log (8 / 3) + 64 / L ^ 2 := add_nonneg hl830 (by positivity)
    have h2 : 0 ≤ s / ((L * (1 / 3)) ^ 2 - s ^ 2) + 27 / L ^ 2 := add_nonneg hsD0 (by positivity)
    have h3 : 0 ≤ 36 / L ^ 2 := by positivity
    have := mul_nonneg h1 h2
    linarith only [this, h3, hcb0]
  -- the main product
  set F4 := cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) *
      (s / ((L * (1 / 3)) ^ 2 - s ^ 2) + 27 / L ^ 2)
  set F2 := 2 / (1 / 2 - 0.00256) * g + 3 * (1 / 8349) * 112
  set F1 := 1 + 0.06 * L / exp (L * (1 / 6))
  have ha0 : 0 ≤ F1 * F2 * (1 + 1e-20) :=
    mul_nonneg (mul_nonneg (by linarith only [hF10]) hF20) (by norm_num)
  have ha1 : F1 * F2 * (1 + 1e-20) ≤ F2 + 1.5e-19 := by
    have h1 := mul_le_mul_of_nonneg_right hF1 hF20
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 1 + 1e-20 by norm_num)
    linarith only [h2, hF2, hF20]
  have hmain : F1 * F2 * (1 + 1e-20) * F3 * F4 ≤ F2 * cb + 1.2229e-5 := by
    have s1 : F1 * F2 * (1 + 1e-20) * F3 ≤ F1 * F2 * (1 + 1e-20) * (1 + 4.6702e-6) :=
      mul_le_mul_of_nonneg_left hF3 ha0
    have s2 : F1 * F2 * (1 + 1e-20) * F3 * F4 ≤ F1 * F2 * (1 + 1e-20) * (1 + 4.6702e-6) * F4 :=
      mul_le_mul_of_nonneg_right s1 hF40
    have s3 : F1 * F2 * (1 + 1e-20) * (1 + 4.6702e-6) * F4 ≤
        (F2 + 1.5e-19) * (1 + 4.6702e-6) * (cb + 1.6e-10) :=
      mul_le_mul (mul_le_mul_of_nonneg_right ha1 (by norm_num)) hF4 hF40
        (mul_nonneg (by linarith only [hF20]) (by norm_num))
    have hFc : F2 * cb ≤ 7.21 * 0.363084 := mul_le_mul hF2 hcb1 (by linarith) (by norm_num)
    have s4 : (F2 + 1.5e-19) * (1 + 4.6702e-6) * (cb + 1.6e-10) ≤ F2 * cb + 1.2229e-5 := by
      linarith only [hFc, hF2, hF20, hcb1, hcb0]
    linarith only [s2, s3, s4]
  -- the second line
  have hlg : (9.9e-21 : ℝ) ≤ log (1 + 1e-20) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1e-20 by norm_num)
    norm_num at this ⊢; linarith
  have hL6 : (7e34 : ℝ) ≤ L ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num) hL 6
    linarith [show (7e34 : ℝ) ≤ 643700 ^ 6 by norm_num]
  have hPre : invTw * (1 + 1e-20) / (log (1 + 1e-20) * L ^ 6) ≤ 5e-15 := by
    have hden : 9.9e-21 * 7e34 ≤ log (1 + 1e-20) * L ^ 6 :=
      mul_le_mul hlg hL6 (by norm_num) (by linarith)
    calc _ ≤ 3 * (1 + 1e-20) / (9.9e-21 * 7e34) :=
          div_le_div₀ (by norm_num) (mul_le_mul_of_nonneg_right hI3 (by norm_num)) (by norm_num)
            hden
      _ ≤ 5e-15 := by norm_num
  have hPre0 : 0 ≤ invTw * (1 + 1e-20) / (log (1 + 1e-20) * L ^ 6) :=
    div_nonneg (mul_nonneg hI0 (by norm_num)) (mul_nonneg (by linarith) (by positivity))
  have hr1 : (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hr0 : 0 ≤ (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hmr : 0.053 * m * (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 0.053 * 40 := by
    have h1 : 0 ≤ (40 - m) * (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ) := mul_nonneg (by linarith) hr0
    linarith only [h1, hr1]
  have h8 : 0.08 * exp (L * (-(1 / 8))) * L ^ 11 ≤ 1e-30 := by
    have hE := tinyA hL (c := 1 / 8) (by norm_num)
    have e : exp (L * (-(1 / 8))) = (exp (L * (1 / 8)))⁻¹ := by rw [← exp_neg]; congr 1; ring
    have := small_div hL1 (k := 11) (by norm_num) (exp_pos _) hE
    rw [e]; rw [div_eq_mul_inv] at this; linarith only [this]
  have hsec : invTw * (1 + 1e-20) / (log (1 + 1e-20) * L ^ 6) *
      (0.053 * m * (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ) + 0.08 * exp (L * (-(1 / 8))) * L ^ 11)
      ≤ 5e-15 * 3 := by
    have hin : 0.053 * m * (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ) + 0.08 * exp (L * (-(1 / 8))) * L ^ 11
        ≤ 3 := by linarith only [hmr, h8]
    by_cases h0 : 0 ≤ 0.053 * m * (1 + 1e-20 : ℝ) ^ (-(1 / 2) : ℝ)
        + 0.08 * exp (L * (-(1 / 8))) * L ^ 11
    · exact mul_le_mul hPre hin h0 (by norm_num)
    · push Not at h0
      have := mul_le_mul_of_nonneg_left h0.le hPre0
      linarith only [this]
  have eF2 : 2 * g / (1 / 2 - 0.00256) + 3 * (1 / 8349) * 112 = F2 := by ring
  rw [eF2]
  linarith only [hmain, hsec]

/-! ### The bracket certificate and the threshold -/

/-- **`Bracket13375`, PROVED**: K3J − 10⁻⁵ ≤ 8·B5 − ½·8·B6 − ½·B7 for every N ≥ exp(exp 13.375).
The loss is about 6.2·10⁻⁶, almost all from the li factor of Theorem 7. -/
theorem bracket13375_holds : Bracket13375 := by
  intro n hn
  have h5 := b5_ge n hn
  have h6 := b6_le n hn
  have h7 := b7_le
  unfold Journal.K3J
  linarith

/-- Vacuity instance of the certificate's hypothesis: some n ≥ exp(exp 13.375) exists. -/
theorem bracket13375_nonvacuous : ∃ n : ℕ, exp (exp 13.375) ≤ (n : ℝ) := by
  obtain ⟨N, -, hN⟩ := threshold_nonvacuous; exact ⟨N, hN⟩


/-- **The GRH Chen threshold at exp(exp 13.375), CONDITIONAL** ON the cited Theorems 5, 6, 7
of P0021, the cited linear sieve Theorem 4 at ε = 1/8349 with C₁ = 112, C₂ = 114, and the OPEN
numeric certificate `Eps1500`. The bracket certificate is PROVED, `bracket13375_holds`. -/
theorem chenThreshold13375_of_deep (h5 : Thm5J) (h6 : Thm6J) (h7 : Thm7J)
    (hT4 : LinearSieveT4 (1 / 8349) 112 114) (hε : Eps1500) : ChenThreshold13375 :=
  chenThreshold13375_of_leaves h5 h6 h7 hT4 hε bracket13375_holds

end LeanLab.BS2022GRH.Cert1567

