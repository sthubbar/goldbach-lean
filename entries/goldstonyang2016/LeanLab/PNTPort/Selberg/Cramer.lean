module

public import LeanLab.PNTPort.Selberg.Sharp4b

/-!
# Cramér's mean square under RH, Gaussian form

Lab proof, unit U-6114, CLOUD 20261020T0618Z-cloud36, T2 toward IDEAS I-5100 and P0058 Lemma 1
for small `ξ`. AI wrote this file. CONDITIONAL ON RiemannHypothesis only, through
`selberg_sharp_b`. Known mathematics, Cramér 1921.

With `F(u) = e^{−u/2}(ψ(e^u) − e^u)`:

* `F_rec`: `e^{1/2} F(u) = F(u − 1) + Nw 1 (u − 1)`, where `Nw 1` is the sharp window of `Sharp4`;
* `cramer_gauss`: **under RH**, there is `M` with `∫ F(u)² e^{−(u−U)²/2} du ≤ M` for every `U ≥ 0`,
  that is `∫ (ψ(x) − x)² ω_U(x) dx ≪ e^{2U}` with a log-normal weight centred at `x = e^U`.

Proof: the recursion and `(a + b)² ≤ 2a² + 2b²` give `A(U) ≤ (2/e)(A(U − 1) + 14C)`, with
`A(U) = ∫ F² gw U` and `selberg_sharp_b` at `δ = 1`, `η = e^{−(U−1)}`; and `2/e < 1`. The base
range `0 ≤ U < 1` uses only Chebyshev's `ψ(x) ≪ x`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Filter
open LeanLab.PNTPort.Gallagher

/-- `F(u) = e^{−u/2}(ψ(e^u) − e^u)`. -/
noncomputable def Fc (u : ℝ) : ℝ :=
  Real.exp (-(u / 2)) * (Chebyshev.psi (Real.exp u) - Real.exp u)

lemma measurable_Fc : Measurable Fc := by
  have hψ : Measurable (fun x : ℝ => Chebyshev.psi x) := Chebyshev.psi_mono.measurable
  unfold Fc
  exact (Continuous.measurable (by fun_prop)).mul ((hψ.comp Real.measurable_exp).sub
    (Continuous.measurable (by fun_prop)))

lemma F_rec (u : ℝ) : Real.exp (1 / 2) * Fc u = Fc (u - 1) + Nw 1 (u - 1) := by
  unfold Fc Nw
  rw [show u - 1 + 1 = u by ring]
  have e1 : Real.exp (1 / 2) * Real.exp (-(u / 2)) = Real.exp (-((u - 1) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← mul_assoc, e1]; ring

/-- Chebyshev: `|F(u)| ≤ c e^{u/2}`. -/
lemma Fc_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ u, Fc u ^ 2 ≤ c * Real.exp u := by
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ c0 * x :=
    ⟨_, fun x hx => Chebyshev.psi_le_const_mul_self hx⟩
  refine ⟨(|c0| + 1) ^ 2, by positivity, fun u => ?_⟩
  have hx := Real.exp_pos u
  have h1 := hc0 (Real.exp u) hx.le
  have h0 : 0 ≤ Chebyshev.psi (Real.exp u) := Chebyshev.psi_nonneg _
  have hc : c0 ≤ |c0| := le_abs_self c0
  have hb : |Chebyshev.psi (Real.exp u) - Real.exp u| ≤ (|c0| + 1) * Real.exp u := by
    rw [abs_le]; constructor <;> nlinarith
  unfold Fc
  rw [mul_pow, ← Real.exp_nat_mul]
  have e : ((2 : ℕ) : ℝ) * -(u / 2) = -u := by push_cast; ring
  rw [e]
  have h2 : (Chebyshev.psi (Real.exp u) - Real.exp u) ^ 2 ≤ ((|c0| + 1) * Real.exp u) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-u) * (Chebyshev.psi (Real.exp u) - Real.exp u) ^ 2
      ≤ Real.exp (-u) * ((|c0| + 1) * Real.exp u) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (|c0| + 1) ^ 2 * Real.exp u * (Real.exp (-u) * Real.exp u) := by ring
    _ = (|c0| + 1) ^ 2 * Real.exp u := by rw [he, mul_one]

/-- Completing the square: `e^u gw U u = e^{U + 1/2} gw (U + 1) u`. -/
lemma cr_exp_mul_gw (U u : ℝ) : Real.exp u * gw U u = Real.exp (U + 1 / 2) * gw (U + 1) u := by
  unfold gw; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma gw_shift (U u : ℝ) : gw U (u + 1) = gw (U - 1) u := by unfold gw; congr 1; ring

lemma cr_integral_gw (U : ℝ) : ∫ u, gw U u = ∫ u, gw 0 u := by
  have : (fun u => gw U u) = fun u => gw 0 (u - U) := by ext u; unfold gw; congr 1; ring
  rw [this, integral_sub_right_eq_self]

lemma integrable_F2 (U : ℝ) : Integrable (fun u => Fc u ^ 2 * gw U u) := by
  obtain ⟨c, hc, hF⟩ := Fc_le
  have hdom : Integrable (fun u => c * Real.exp (U + 1 / 2) * gw (U + 1) u) :=
    (gw_integrable (U + 1)).const_mul _
  refine hdom.mono' ((measurable_Fc.pow_const 2).mul (gw_continuous U).measurable).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gw_nonneg U u))]
  calc Fc u ^ 2 * gw U u ≤ c * Real.exp u * gw U u :=
        mul_le_mul_of_nonneg_right (hF u) (gw_nonneg U u)
    _ = c * Real.exp (U + 1 / 2) * gw (U + 1) u := by rw [mul_assoc, cr_exp_mul_gw]; ring

/-- The base range: `∫ F² gw U ≤ c e^{U + 1/2} ∫ gw 0`. -/
lemma base_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ U : ℝ, U ≤ 1 → ∫ u, Fc u ^ 2 * gw U u ≤ B := by
  obtain ⟨c, hc, hF⟩ := Fc_le
  set c0 := ∫ u, gw 0 u
  have hc0 : 0 ≤ c0 := integral_nonneg (gw_nonneg 0)
  refine ⟨c * Real.exp (3 / 2) * c0, by positivity, fun U hU => ?_⟩
  have hdom : Integrable (fun u => c * Real.exp (U + 1 / 2) * gw (U + 1) u) :=
    (gw_integrable (U + 1)).const_mul _
  calc ∫ u, Fc u ^ 2 * gw U u ≤ ∫ u, c * Real.exp (U + 1 / 2) * gw (U + 1) u := by
        refine integral_mono (integrable_F2 U) hdom fun u => ?_
        calc Fc u ^ 2 * gw U u ≤ c * Real.exp u * gw U u :=
              mul_le_mul_of_nonneg_right (hF u) (gw_nonneg U u)
          _ = c * Real.exp (U + 1 / 2) * gw (U + 1) u := by rw [mul_assoc, cr_exp_mul_gw]; ring
    _ = c * Real.exp (U + 1 / 2) * c0 := by rw [integral_const_mul, cr_integral_gw]
    _ ≤ c * Real.exp (3 / 2) * c0 := by
        apply mul_le_mul_of_nonneg_right _ hc0
        apply mul_le_mul_of_nonneg_left _ hc
        exact Real.exp_le_exp.mpr (by linarith)

/-- The window at `δ = 1`: `∫ Nw(1, u)² gw V ≤ 14 C` for `V ≥ 0`. -/
lemma window_one (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ V : ℝ, 0 ≤ V →
    Integrable (fun u => Nw 1 u ^ 2 * gw V u) ∧ ∫ u, Nw 1 u ^ 2 * gw V u ≤ 14 * C := by
  obtain ⟨C, hC, h⟩ := selberg_sharp_b hRH
  refine ⟨C, hC, fun V hV => ?_⟩
  have hη0 : 0 < Real.exp (-V) := Real.exp_pos _
  have hη1 : Real.exp (-V) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  obtain ⟨hi, hb⟩ := h 1 (Real.exp (-V)) hη0 hη1 le_rfl V
  refine ⟨hi, hb.trans ?_⟩
  have e1 : Real.exp (-V) ^ 2 * Real.exp V = Real.exp (-V) := by
    rw [sq, mul_assoc, ← Real.exp_add, show -V + V = 0 by ring, Real.exp_zero, mul_one]
  have e2 : Real.exp (-V) ^ (-1 : ℝ) = Real.exp V := by
    rw [Real.rpow_neg_one, ← Real.exp_neg, neg_neg]
  have e3 : |Real.log (Real.exp (-V))| = V := by rw [Real.log_exp, abs_neg, abs_of_nonneg hV]
  rw [e1, e2, e3]
  simp only [div_one, Real.log_one, zero_add]
  have h4 : Real.exp (-V) ≤ 1 := hη1
  have h5 : Real.exp V * (V + 2) ^ 2 * Real.exp (-(2 * V)) ≤ 4 := by
    have e : Real.exp V * (V + 2) ^ 2 * Real.exp (-(2 * V)) = (V + 2) ^ 2 * Real.exp (-V) := by
      rw [mul_comm (Real.exp V), mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e]
    -- `(V + 2)² e^{−V} ≤ 4`: `(V + 2)² ≤ 4 e^V` from `e^{V/2} ≥ 1 + V/2`
    have h6 : 1 + V / 2 ≤ Real.exp (V / 2) := by linarith [Real.add_one_le_exp (V / 2)]
    have h7 : (V + 2) ^ 2 ≤ 4 * Real.exp V := by
      have : (V + 2) ^ 2 = 4 * (1 + V / 2) ^ 2 := by ring
      rw [this, show Real.exp V = Real.exp (V / 2) ^ 2 by rw [← Real.exp_nat_mul]; push_cast; ring_nf]
      have := pow_le_pow_left₀ (by linarith) h6 2
      linarith
    have := mul_le_mul_of_nonneg_right h7 (Real.exp_pos (-V)).le
    have he : Real.exp V * Real.exp (-V) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Cramér's mean square under RH, Gaussian form.** -/
theorem cramer_gauss (hRH : RiemannHypothesis) : ∃ M : ℝ, 0 ≤ M ∧ ∀ U : ℝ, 0 ≤ U →
    ∫ u, Fc u ^ 2 * gw U u ≤ M := by
  obtain ⟨C, hC, hw⟩ := window_one hRH
  obtain ⟨B, hB, hb⟩ := base_bound
  have he : 2 / Real.exp 1 ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9; linarith
  have he0 : 0 < 2 / Real.exp 1 := by positivity
  set M := B + 42 * C
  refine ⟨M, by positivity, ?_⟩
  -- the recursion step
  have step : ∀ U : ℝ, 1 ≤ U → ∫ u, Fc u ^ 2 * gw U u
      ≤ 2 / Real.exp 1 * ((∫ u, Fc u ^ 2 * gw (U - 1) u) + 14 * C) := by
    intro U hU
    obtain ⟨hiN, hbN⟩ := hw (U - 1) (by linarith)
    have hpt : ∀ u, Fc u ^ 2 * gw U u
        ≤ 2 / Real.exp 1 * (Fc (u - 1) ^ 2 * gw U u + Nw 1 (u - 1) ^ 2 * gw U u) := by
      intro u
      have hr := F_rec u
      have hE : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      have h1 : Real.exp 1 * Fc u ^ 2 ≤ 2 * (Fc (u - 1) ^ 2 + Nw 1 (u - 1) ^ 2) := by
        rw [← hE, ← mul_pow, hr]
        nlinarith [sq_nonneg (Fc (u - 1) - Nw 1 (u - 1))]
      have hg := gw_nonneg U u
      have h2 : Fc u ^ 2 ≤ 2 / Real.exp 1 * (Fc (u - 1) ^ 2 + Nw 1 (u - 1) ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos 1)]; linarith
      have := mul_le_mul_of_nonneg_right h2 hg
      linarith
    -- translation
    have t1 : ∫ u, Fc (u - 1) ^ 2 * gw U u = ∫ u, Fc u ^ 2 * gw (U - 1) u := by
      have : (fun u => Fc (u - 1) ^ 2 * gw U u) = fun u => (fun v => Fc v ^ 2 * gw (U - 1) v) (u - 1) := by
        ext u; simp only; rw [← gw_shift, show u - 1 + 1 = u by ring]
      rw [this]; exact integral_sub_right_eq_self (fun v => Fc v ^ 2 * gw (U - 1) v) 1
    have t2 : ∫ u, Nw 1 (u - 1) ^ 2 * gw U u = ∫ u, Nw 1 u ^ 2 * gw (U - 1) u := by
      have : (fun u => Nw 1 (u - 1) ^ 2 * gw U u) = fun u => (fun v => Nw 1 v ^ 2 * gw (U - 1) v) (u - 1) := by
        ext u; simp only; rw [← gw_shift, show u - 1 + 1 = u by ring]
      rw [this]; exact integral_sub_right_eq_self (fun v => Nw 1 v ^ 2 * gw (U - 1) v) 1
    have i1 : Integrable (fun u => Fc (u - 1) ^ 2 * gw U u) := by
      have : (fun u => Fc (u - 1) ^ 2 * gw U u) = fun u => (fun v => Fc v ^ 2 * gw (U - 1) v) (u - 1) := by
        ext u; simp only; rw [← gw_shift, show u - 1 + 1 = u by ring]
      rw [this]; exact (integrable_F2 (U - 1)).comp_sub_right 1
    have i2 : Integrable (fun u => Nw 1 (u - 1) ^ 2 * gw U u) := by
      have : (fun u => Nw 1 (u - 1) ^ 2 * gw U u) = fun u => (fun v => Nw 1 v ^ 2 * gw (U - 1) v) (u - 1) := by
        ext u; simp only; rw [← gw_shift, show u - 1 + 1 = u by ring]
      rw [this]; exact hiN.comp_sub_right 1
    calc ∫ u, Fc u ^ 2 * gw U u
        ≤ ∫ u, 2 / Real.exp 1 * (Fc (u - 1) ^ 2 * gw U u + Nw 1 (u - 1) ^ 2 * gw U u) :=
          integral_mono (integrable_F2 U) ((i1.add i2).const_mul _) hpt
      _ = 2 / Real.exp 1 * ((∫ u, Fc u ^ 2 * gw (U - 1) u) + ∫ u, Nw 1 u ^ 2 * gw (U - 1) u) := by
          rw [integral_const_mul, integral_add i1 i2, t1, t2]
      _ ≤ 2 / Real.exp 1 * ((∫ u, Fc u ^ 2 * gw (U - 1) u) + 14 * C) := by
          apply mul_le_mul_of_nonneg_left _ he0.le; linarith
  -- induction on `⌊U⌋`
  have hind : ∀ n : ℕ, ∀ U : ℝ, 0 ≤ U → U ≤ n + 1 → ∫ u, Fc u ^ 2 * gw U u ≤ M := by
    intro n
    induction n with
    | zero =>
      intro U _ hU
      have := hb U (by simpa using hU)
      linarith
    | succ n ih =>
      intro U hU0 hU
      rcases le_or_gt U 1 with h1 | h1
      · have := hb U h1; linarith
      · have hprev := ih (U - 1) (by linarith) (by push_cast at hU ⊢; linarith)
        have hs := step U h1.le
        have hA0 : 0 ≤ ∫ u, Fc u ^ 2 * gw (U - 1) u :=
          integral_nonneg fun u => mul_nonneg (sq_nonneg _) (gw_nonneg _ u)
        have : 2 / Real.exp 1 * ((∫ u, Fc u ^ 2 * gw (U - 1) u) + 14 * C)
            ≤ 3 / 4 * (M + 14 * C) := by
          apply mul_le_mul he (by linarith) (by positivity) (by norm_num)
        have hM : 3 / 4 * (M + 14 * C) ≤ M := by simp only [M]; nlinarith
        linarith
  intro U hU
  obtain ⟨n, hn⟩ := exists_nat_ge U
  exact hind n U hU (by linarith)

end LeanLab.PNTPort.Selberg

