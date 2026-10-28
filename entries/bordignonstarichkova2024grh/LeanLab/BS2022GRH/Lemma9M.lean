module

public import LeanLab.BS2022GRH.Thm7Factor

/-!
P0021, Bordignon-Starichkova 2022, arXiv 2211.08844 v1, Lemma 9, = BJS 2022 Lemma 31.
The quantity `m(X, Y, D*)` of Lemma 9, read in Claude in Chrome from
arxiv.org/html/2211.08844 on 2026-10-18, and the bound `0 ≤ m ≤ 1000` at the arguments
Theorem 7 uses, `X = N^{2/3}`, `Y = (1 + ε₁) N^{1/8}`, `D* = √N / log⁵ N`, `ε₁ = 10⁻²⁰`,
`N ≥ exp(exp 15.85)`, with `q = q_G(Y)` of Lemma 3. This removes the `m` hypothesis of
`Thm7Factor.theorem3_main_thm567`.
AI-written Lean code, Claude, run 20261018T2003Z-9206, unit U-0971. Checked only by the
Lean kernel. Binary Goldbach is OPEN; Lemma 9 itself stays cited.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

/-- `m(X, Y, D*)` of Lemma 9 with `q = q_G(Y)` passed as `q`. -/
noncomputable def mL9 (q X Y D : ℝ) : ℝ :=
  2.81 * q ^ (1 / 3 : ℝ) + 2.809 / (q ^ (2 / 3 : ℝ) * sqrt Y * log Y)
  + 1.721 * log D ^ (2 / 3 : ℝ)
      / (q ^ (1 / 3 : ℝ) * Y ^ (2 / 3 : ℝ) * log Y ^ (2 / 3 : ℝ) * log (log D))
  + 5.498 * (1 / sqrt X + 1 / sqrt Y) * Y ^ (1 / 6 : ℝ) * log D ^ (1 / 3 : ℝ)
      / log Y ^ (1 / 3 : ℝ)
  + 19.044 * D * log D ^ (1 / 3 : ℝ) / (X * Y ^ (5 / 6 : ℝ) * log Y ^ (1 / 3 : ℝ))

lemma rpow_le_self' {x a : ℝ} (hx : 1 ≤ x) (ha : a ≤ 1) : x ^ a ≤ x := by
  simpa using Real.rpow_le_rpow_of_exponent_le hx ha

lemma le_rpow_small {q a : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) (ha : a ≤ 1) : q ≤ q ^ a := by
  simpa using Real.rpow_le_rpow_of_exponent_ge h0 h1 ha

lemma m9T3 {q Y D : ℝ} (hq : 0.16 ≤ q) (hq1 : q ≤ 1) (hY : 1 ≤ Y) (hlY : 1 ≤ log Y)
    (hlD1 : 1 ≤ log D) (hlD : 1 ≤ log (log D)) (H1 : log D ≤ Y ^ (2 / 3 : ℝ)) :
    0 ≤ 1.721 * log D ^ (2 / 3 : ℝ)
      / (q ^ (1 / 3 : ℝ) * Y ^ (2 / 3 : ℝ) * log Y ^ (2 / 3 : ℝ) * log (log D)) ∧
    1.721 * log D ^ (2 / 3 : ℝ)
      / (q ^ (1 / 3 : ℝ) * Y ^ (2 / 3 : ℝ) * log Y ^ (2 / 3 : ℝ) * log (log D)) ≤ 1.721 / 0.16 := by
  have hq0 : 0 < q := by linarith
  have q13l : q ≤ q ^ (1 / 3 : ℝ) := le_rpow_small hq0 hq1 (by norm_num)
  have Y23 : 1 ≤ Y ^ (2 / 3 : ℝ) := Real.one_le_rpow hY (by norm_num)
  have lY23 : 1 ≤ log Y ^ (2 / 3 : ℝ) := Real.one_le_rpow hlY (by norm_num)
  have lD23 : log D ^ (2 / 3 : ℝ) ≤ log D := rpow_le_self' hlD1 (by norm_num)
  have lD230 : 0 ≤ log D ^ (2 / 3 : ℝ) := rpow_nonneg (by linarith) _
  set A := q ^ (1 / 3 : ℝ)
  set B := Y ^ (2 / 3 : ℝ)
  set C := log Y ^ (2 / 3 : ℝ)
  set E := log (log D)
  have a : 0.16 * B ≤ A * B := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have b : 0.16 * B * 1 ≤ A * B * C := mul_le_mul a lY23 (by norm_num) (by nlinarith)
  have c : 0.16 * B * 1 * 1 ≤ A * B * C * E := mul_le_mul b hlD (by norm_num) (by nlinarith)
  have d3 : 0.16 * B ≤ A * B * C * E := by linarith
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · have s : 1.721 * log D ^ (2 / 3 : ℝ) / (A * B * C * E) ≤ 1.721 * log D / (0.16 * B) :=
      div_le_div₀ (by linarith) (by linarith) (by linarith) d3
    refine le_trans s ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith

lemma m9T4 {X Y D : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hlY : 1 ≤ log Y) (hlD1 : 1 ≤ log D)
    (H2 : Y ^ (1 / 6 : ℝ) * log D ≤ sqrt X) (H3 : Y ^ (1 / 6 : ℝ) * log D ≤ sqrt Y) :
    0 ≤ 5.498 * (1 / sqrt X + 1 / sqrt Y) * Y ^ (1 / 6 : ℝ) * log D ^ (1 / 3 : ℝ)
      / log Y ^ (1 / 3 : ℝ) ∧
    5.498 * (1 / sqrt X + 1 / sqrt Y) * Y ^ (1 / 6 : ℝ) * log D ^ (1 / 3 : ℝ)
      / log Y ^ (1 / 3 : ℝ) ≤ 5.498 * 2 := by
  have sY : 1 ≤ sqrt Y := by rw [show (1:ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hY
  have sX : 1 ≤ sqrt X := by rw [show (1:ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hX
  have Y16 : 1 ≤ Y ^ (1 / 6 : ℝ) := Real.one_le_rpow hY (by norm_num)
  have lY13 : 1 ≤ log Y ^ (1 / 3 : ℝ) := Real.one_le_rpow hlY (by norm_num)
  have lD13 : log D ^ (1 / 3 : ℝ) ≤ log D := rpow_le_self' hlD1 (by norm_num)
  have lD130 : 0 ≤ log D ^ (1 / 3 : ℝ) := rpow_nonneg (by linarith) _
  set sx := sqrt X
  set sy := sqrt Y
  set W := Y ^ (1 / 6 : ℝ)
  set lD := log D
  set U := log D ^ (1 / 3 : ℝ)
  set V := log Y ^ (1 / 3 : ℝ)
  have i0 : 0 ≤ 1 / sx + 1 / sy :=
    add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (by linarith))
  have k0 : 0 ≤ 5.498 * (1 / sx + 1 / sy) * W := mul_nonneg (mul_nonneg (by norm_num) i0) (by linarith)
  have n0 : 0 ≤ 5.498 * (1 / sx + 1 / sy) * W * U := mul_nonneg k0 lD130
  constructor
  · exact div_nonneg n0 (by linarith)
  · have s : 5.498 * (1 / sx + 1 / sy) * W * U / V ≤ 5.498 * (1 / sx + 1 / sy) * W * U := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    refine le_trans s ?_
    have e1 : 5.498 * (1 / sx + 1 / sy) * W * U ≤ 5.498 * (1 / sx + 1 / sy) * W * lD :=
      mul_le_mul_of_nonneg_left lD13 k0
    have h : 5.498 * (1 / sx + 1 / sy) * W * lD = 5.498 * ((W * lD) / sx + (W * lD) / sy) := by ring
    have a : (W * lD) / sx ≤ 1 := by rw [div_le_one (by linarith)]; exact H2
    have b : (W * lD) / sy ≤ 1 := by rw [div_le_one (by linarith)]; exact H3
    linarith

lemma m9T5 {X Y D : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hlY : 1 ≤ log Y) (hlD1 : 1 ≤ log D)
    (hD : 0 < D) (H4 : D * log D ≤ X) :
    0 ≤ 19.044 * D * log D ^ (1 / 3 : ℝ) / (X * Y ^ (5 / 6 : ℝ) * log Y ^ (1 / 3 : ℝ)) ∧
    19.044 * D * log D ^ (1 / 3 : ℝ) / (X * Y ^ (5 / 6 : ℝ) * log Y ^ (1 / 3 : ℝ)) ≤ 19.044 := by
  have Y56 : 1 ≤ Y ^ (5 / 6 : ℝ) := Real.one_le_rpow hY (by norm_num)
  have lY13 : 1 ≤ log Y ^ (1 / 3 : ℝ) := Real.one_le_rpow hlY (by norm_num)
  have lD13 : log D ^ (1 / 3 : ℝ) ≤ log D := rpow_le_self' hlD1 (by norm_num)
  have lD130 : 0 ≤ log D ^ (1 / 3 : ℝ) := rpow_nonneg (by linarith) _
  set B := Y ^ (5 / 6 : ℝ)
  set C := log Y ^ (1 / 3 : ℝ)
  set U := log D ^ (1 / 3 : ℝ)
  have a : X * 1 ≤ X * B := mul_le_mul_of_nonneg_left Y56 (by linarith)
  have b : X * 1 * 1 ≤ X * B * C := mul_le_mul a lY13 (by norm_num) (by nlinarith)
  have d5 : X ≤ X * B * C := by linarith
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD.le) lD130) (by linarith)
  · have s : 19.044 * D * U / (X * B * C) ≤ 19.044 * D * log D / X :=
      div_le_div₀ (by nlinarith) (by nlinarith) (by linarith) d5
    refine le_trans s ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith

/-- **Crude bound for Lemma 9's m**: `0 ≤ m ≤ 1000` once the four size conditions hold. -/
theorem mL9_le {q X Y D : ℝ} (hq : 0.16 ≤ q) (hq1 : q ≤ 1) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hlY : 1 ≤ log Y) (hlD1 : 1 ≤ log D) (hlD : 1 ≤ log (log D)) (hD : 0 < D)
    (H1 : log D ≤ Y ^ (2 / 3 : ℝ)) (H2 : Y ^ (1 / 6 : ℝ) * log D ≤ sqrt X)
    (H3 : Y ^ (1 / 6 : ℝ) * log D ≤ sqrt Y) (H4 : D * log D ≤ X) :
    0 ≤ mL9 q X Y D ∧ mL9 q X Y D ≤ 1000 := by
  have hq0 : 0 < q := by linarith
  have q13 : q ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hq0.le hq1 (by norm_num)
  have q130 : 0 ≤ q ^ (1 / 3 : ℝ) := rpow_nonneg hq0.le _
  have q23l : q ≤ q ^ (2 / 3 : ℝ) := le_rpow_small hq0 hq1 (by norm_num)
  have sY : 1 ≤ sqrt Y := by rw [show (1:ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hY
  have d2 : 0.16 ≤ q ^ (2 / 3 : ℝ) * sqrt Y * log Y := by
    have a : 0.16 ≤ q ^ (2 / 3 : ℝ) := by linarith
    have b : 0.16 * 1 ≤ q ^ (2 / 3 : ℝ) * sqrt Y := mul_le_mul a sY (by norm_num) (by linarith)
    have c : 0.16 * 1 * 1 ≤ q ^ (2 / 3 : ℝ) * sqrt Y * log Y :=
      mul_le_mul b hlY (by norm_num) (by linarith)
    linarith
  have T2 : 2.809 / (q ^ (2 / 3 : ℝ) * sqrt Y * log Y) ≤ 2.809 / 0.16 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) d2
  have T20 : 0 ≤ 2.809 / (q ^ (2 / 3 : ℝ) * sqrt Y * log Y) :=
    div_nonneg (by norm_num) (by linarith)
  obtain ⟨T30, T3⟩ := m9T3 hq hq1 hY hlY hlD1 hlD H1
  obtain ⟨T40, T4⟩ := m9T4 hX hY hlY hlD1 H2 H3
  obtain ⟨T50, T5⟩ := m9T5 hX hY hlY hlD1 hD H4
  unfold mL9
  have n : (2.81 : ℝ) + 2.809 / 0.16 + 1.721 / 0.16 + 5.498 * 2 + 19.044 ≤ 1000 := by norm_num
  constructor
  · linarith
  · linarith

lemma exp_ge_sq {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / 2 ≤ exp t := by
  have := Real.pow_div_factorial_le_exp (x := t) ht 2
  norm_num [Nat.factorial] at this; exact this

lemma logL_le_small {L : ℝ} (hL : 1 ≤ L) : log L ≤ L / 1000000 + 19 := by
  have h1 : log L = log (L / 1000000) + log 1000000 := by
    rw [← log_mul (by positivity) (by norm_num)]; congr 1; ring
  have h2 := Real.log_le_sub_one_of_pos (x := L / 1000000) (by positivity)
  have h3 : log (1000000 : ℝ) ≤ 20 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.pow_div_factorial_le_exp (x := (20 : ℝ)) (by norm_num) 20
    norm_num [Nat.factorial] at this; linarith
  linarith

/-- `0.16 ≤ q_G(Y)` once `√Y ≥ 10⁵` and `log Y ≥ 1`. -/
lemma qG_ge {Y : ℝ} (hY : 0 < Y) (hlY : 1 ≤ log Y) (hsY : 100000 ≤ sqrt Y) : 0.16 ≤ qG Y := by
  unfold qG
  set l := log Y
  have hl0 : 0 ≤ l := by linarith
  have hll : 0 ≤ log l := Real.log_nonneg hlY
  have hY4 : 0 < Y ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hY _
  have t1 : 0 ≤ 12.683 / l := div_nonneg (by norm_num) hl0
  have t2 : 0 ≤ 254.980 / l ^ 2 := div_nonneg (by norm_num) (by positivity)
  have t3 : 0 ≤ 2607.854 / l ^ 3 := div_nonneg (by norm_num) (by positivity)
  have t4 : 0 ≤ 11605.056 / l ^ 4 := div_nonneg (by norm_num) (by positivity)
  have t5 : 0 ≤ 1.314 * l / Y ^ ((1 : ℝ) / 4) := div_nonneg (by positivity) hY4.le
  have t6 : 0 ≤ 0.092 * log l / Y ^ ((1 : ℝ) / 4) := div_nonneg (by positivity) hY4.le
  have t7 : 0 ≤ 60.883 / Y ^ ((1 : ℝ) / 4) := div_nonneg (by norm_num) hY4.le
  have t8 : 0 ≤ 8.250 * log l / (Y ^ ((1 : ℝ) / 4) * l) :=
    div_nonneg (by positivity) (mul_nonneg hY4.le hl0)
  have t9 : 0 ≤ 939.260 / (Y ^ ((1 : ℝ) / 4) * l) := div_nonneg (by norm_num) (mul_nonneg hY4.le hl0)
  have t10 : 237.934 / (sqrt Y * l) ≤ 0.005 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  linarith

set_option maxHeartbeats 2000000 in
/-- **Lemma 9's m at Theorem 7's arguments**, `X = N^{2/3}`, `Y = (1 + 10⁻²⁰) N^{1/8}`,
`D* = √N / log⁵ N`, `q = q_G(Y)`, for `log N ≥ 7.64·10⁶`: `0 ≤ m ≤ 1000`. -/
theorem m_at {N : ℝ} (hN : 0 < N) (hL : 7640000 ≤ log N) :
    0 ≤ mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
        ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5) ∧
    mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
        ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5) ≤ 1000 := by
  set L := log N with hLdef
  set Y := (1 + 1e-20) * N ^ (1 / 8 : ℝ) with hYdef
  set X := N ^ (2 / 3 : ℝ) with hXdef
  set D := sqrt N / L ^ 5 with hDdef
  have hL0 : 0 < L := by linarith
  have hN8 : 0 < N ^ (1 / 8 : ℝ) := rpow_pos_of_pos hN _
  have hY0 : 0 < Y := by positivity
  have hX0 : 0 < X := rpow_pos_of_pos hN _
  -- logarithms
  have lX : log X = 2 / 3 * L := log_rpow hN _
  have le0 : 0 ≤ log (1 + (1e-20 : ℝ)) := Real.log_nonneg (by norm_num)
  have le1 : log (1 + (1e-20 : ℝ)) ≤ 1e-20 := by
    have := Real.log_le_sub_one_of_pos (x := 1 + (1e-20 : ℝ)) (by norm_num); linarith
  have lY : log Y = log (1 + 1e-20) + 1 / 8 * L := by
    rw [hYdef, log_mul (by norm_num) hN8.ne', log_rpow hN]
  have lYlo : L / 8 ≤ log Y := by rw [lY]; linarith
  have lYhi : log Y ≤ L / 8 + 1e-20 := by rw [lY]; linarith
  have hsN : sqrt N = exp (L / 2) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hN]
    show exp (log N * (1 / 2)) = exp (log N / 2); ring_nf
  have lD : log D = L / 2 - 5 * log L := by
    rw [hDdef, log_div (by positivity) (by positivity), log_sqrt hN.le, log_pow]; push_cast; ring
  have hlogL := logL_le_small (L := L) (by linarith)
  have hlogL0 : 0 ≤ log L := Real.log_nonneg (by linarith)
  have lDlo : 0.49 * L ≤ log D := by rw [lD]; linarith
  have lDhi : log D ≤ L / 2 := by rw [lD]; linarith
  -- rpow and sqrt as exponentials
  have eY (a : ℝ) : Y ^ a = exp (log Y * a) := rpow_def_of_pos hY0 a
  have sY : sqrt Y = exp (log Y / 2) := by rw [sqrt_eq_rpow, eY]; ring_nf
  have sX : sqrt X = exp (L / 3) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hX0, lX]; ring_nf
  have eX : X = exp (2 / 3 * L) := by
    rw [hXdef, rpow_def_of_pos hN]
    show exp (log N * (2 / 3)) = exp (2 / 3 * log N); ring_nf
  -- sizes
  have Ybig : 4e18 ≤ Y := by
    have h := Real.pow_div_factorial_le_exp (x := L / 8) (by positivity) 4
    norm_num [Nat.factorial] at h
    have hL4 : (7640000 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    have : exp (L / 8) ≤ Y := by rw [← exp_log hY0]; exact exp_le_exp.2 lYlo
    have e : (L / 8) ^ 4 / 24 = L ^ 4 / 98304 := by ring
    nlinarith
  have hY1 : 1 ≤ Y := by linarith
  have hlY1 : 1 ≤ log Y := by linarith
  have hsY : 100000 ≤ sqrt Y := by
    rw [sY]; have := exp_ge_sq (t := log Y / 2) (by linarith)
    have : (L / 16) ^ 2 / 2 ≤ (log Y / 2) ^ 2 / 2 := by
      have h1 : L / 16 ≤ log Y / 2 := by linarith
      have := pow_le_pow_left₀ (by positivity) h1 2; linarith
    nlinarith
  have hq1 : qG Y ≤ 1 := by have := qG_le_all Y Ybig; linarith
  have hq : 0.16 ≤ qG Y := qG_ge hY0 hlY1 hsY
  have hN1 : (1 : ℝ) ≤ N := by
    by_contra h
    have := Real.log_neg hN (lt_of_not_ge h); linarith
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by norm_num)
  have hlD1 : 1 ≤ log D := by linarith
  have hlD : 1 ≤ log (log D) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hD : 0 < D := by rw [hDdef]; positivity
  have H1 : log D ≤ Y ^ (2 / 3 : ℝ) := by
    rw [eY]
    have h1 : L / 12 ≤ log Y * (2 / 3) := by linarith
    have h2 := exp_ge_sq (t := L / 12) (by positivity)
    have h3 : exp (L / 12) ≤ exp (log Y * (2 / 3)) := exp_le_exp.2 h1
    nlinarith
  have H2 : Y ^ (1 / 6 : ℝ) * log D ≤ sqrt X := by
    rw [eY, sX]
    have h1 : log Y * (1 / 6) ≤ L / 48 + 1 := by linarith
    have h2 : exp (log Y * (1 / 6)) ≤ exp (L / 48 + 1) := exp_le_exp.2 h1
    have h3 : exp (L / 3) = exp (L / 48 + 1) * exp (L * 5 / 16 - 1) := by
      rw [← exp_add]; ring_nf
    have h4 := exp_ge_sq (t := L * 5 / 16 - 1) (by linarith)
    have h5 : L / 2 ≤ exp (L * 5 / 16 - 1) := by nlinarith
    rw [h3]
    have h6 : 0 ≤ log D := by linarith
    calc exp (log Y * (1 / 6)) * log D ≤ exp (L / 48 + 1) * (L / 2) :=
          mul_le_mul h2 lDhi h6 (exp_pos _).le
      _ ≤ exp (L / 48 + 1) * exp (L * 5 / 16 - 1) := mul_le_mul_of_nonneg_left h5 (exp_pos _).le
  have H3 : Y ^ (1 / 6 : ℝ) * log D ≤ sqrt Y := by
    rw [eY, sY]
    have h3 : exp (log Y / 2) = exp (log Y * (1 / 6)) * exp (log Y / 3) := by
      rw [← exp_add]; ring_nf
    have h1 : L / 24 ≤ log Y / 3 := by linarith
    have h2 := exp_ge_sq (t := L / 24) (by positivity)
    have h4 : exp (L / 24) ≤ exp (log Y / 3) := exp_le_exp.2 h1
    have h5 : log D ≤ exp (log Y / 3) := by nlinarith
    rw [h3]; exact mul_le_mul_of_nonneg_left h5 (exp_pos _).le
  have H4 : D * log D ≤ X := by
    have hDle : D ≤ exp (L / 2) := by
      rw [hDdef, ← hsN]
      apply div_le_self (sqrt_nonneg _)
      have := one_le_pow₀ (n := 5) (by linarith : (1 : ℝ) ≤ L); exact this
    have h3 : X = exp (L / 2) * exp (L / 6) := by rw [eX, ← exp_add]; ring_nf
    have h2 := exp_ge_sq (t := L / 6) (by positivity)
    have h5 : log D ≤ exp (L / 6) := by nlinarith
    rw [h3]; exact mul_le_mul hDle h5 (by linarith) (exp_pos _).le
  exact mL9_le hq hq1 hX1 hY1 hlY1 hlD1 hlD hD H1 H2 H3 H4

/-- **Section 5.4 with the exact Theorem 5, 6 and 7 brackets**, Lemma 9's `m` now at its
actual value: margin above `0.0015 - 8·10⁻⁸ - 4·10⁻⁶ - 5·10⁻⁵`. Arithmetic only: Theorems 4
to 7 and Lemma 9 themselves stay cited, and this is CONDITIONAL ON `li ≤ ∫₂ + 2`, PROVED for the principal value li in LiPV.lean. -/
theorem theorem3_main_thm567_m {li X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N)
    (hli : li ≤ (∫ t in (2 : ℝ)..N ^ (1 / 3 : ℝ), 1 / log t) + 2) :
    (0.0015 - 8e-8 - 4e-6 - 5e-5 : ℝ) <
      K3 α0 (exp eulerMascheroniConstant) (1 / 8137) 112 114 LeanLab.ChenExplicit.BJS.cbar
      - 8 * thm5Main α0 (exp eulerMascheroniConstant) (1 / 8137) 114
      + 8 * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
      + 4 * thm6Main α0 (exp eulerMascheroniConstant) (1 / 8137) 112
      - 4 * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
      + 1 / 2 * thm7Main α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.BJS.cbar
      - 1 / 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * N ^ (1 / 8 : ℝ))) (N ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * N ^ (1 / 8 : ℝ)) (sqrt N / log N ^ 5)) li N := by
  obtain ⟨hL, hN0⟩ := logN_ge hX hN
  obtain ⟨hm0, hm⟩ := m_at hN0 hL
  exact theorem3_main_thm567 hX hN hm0 hm hli


end LeanLab.BS2022GRH
