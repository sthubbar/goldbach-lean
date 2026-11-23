module

public import Mathlib
public import LeanLab.DERZ1997.Statements
public import LeanLab.DERZ1997.Decomp1529a
public import LeanLab.PNTPort.DirichletZF.LogDeriv
public import LeanLab.PNTPort.ExplicitPsi1.Residues

/-!
Local character estimates for the DERZ1997 explicit formula decomposition.
These supply analytic inputs and do not assert the character explicit formula.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.DERZ1997.Character266
open Complex Set Filter Metric Topology
open LeanLab.PNTPort.DirichletZF

/-- Uniform normalized L-function setup on the enlarged disc.
Auxiliary derivation for Davenport chapter 19 pages 117 to 120. -/
theorem character_scaled_setup266 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) :
    let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t + (3 / 2 : ℂ) * z)
    let g : ℂ → ℂ := fun z => f z / f 0
    AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1) ∧ g 0 = 1 ∧ (SetOfZeros 1 g).Finite ∧
      ∀ w : ℂ, ‖w‖ ≤ 29 / 30 → ‖g w‖ ≤ 20 * Z * ((q : ℝ) * (|t| + 3)) := by
  dsimp only
  let c : ℂ := (3 : ℂ) / 2 + I * t
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * z)
  have hfA (z : ℂ) : AnalyticAt ℂ f z := by
    have hd : Differentiable ℂ f := (DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)
    exact hd.analyticAt z
  have hf0 : f 0 ≠ 0 := by
    simpa only [f, c, mul_zero, add_zero] using LFunction_c_ne_zero χ t
  have hfFinite : (SetOfZeros 1 f).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    have hsub : SetOfZeros 1 f ⊆ closedBall (0 : ℂ) 1 := fun _ hx => by
      simpa only [mem_closedBall, dist_zero_right] using hx.1
    obtain ⟨x, hxK, hacc⟩ :=
      hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 1) hsub
    have hAnalytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) 2) := fun z _ => hfA z
    have hzero : Set.EqOn f 0 (ball (0 : ℂ) 2) := by
      refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hAnalytic
        isPreconnected_ball (z₀ := x) ?_ ?_
      · simp only [mem_ball, mem_closedBall, dist_zero_right] at hxK ⊢
        linarith
      · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
        exact hacc.mono (principal_mono.mpr fun _ h => h.2)
    exact hf0 (hzero (mem_ball_self (by norm_num)))
  let g : ℂ → ℂ := fun z => f z / f 0
  have hgA : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1) := fun z _ => (hfA z).div_const
  have hg0 : g 0 = 1 := by simp [g, hf0]
  have hzeros (R : ℝ) : SetOfZeros R g = SetOfZeros R f := by
    ext z
    simp [SetOfZeros, g, hf0]
  have hgFinite : (SetOfZeros 1 g).Finite := by rw [hzeros]; exact hfFinite
  let M : ℝ := (q : ℝ) * (|t| + 3)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 3 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t]
  let B : ℝ := 20 * Z * M
  have hB : 1 < B := by dsimp [B]; nlinarith [one_le_Z]
  have hgBound : ∀ w : ℂ, ‖w‖ ≤ 29 / 30 → ‖g w‖ ≤ B := by
    intro w hw
    let s : ℂ := c + (3 / 2 : ℂ) * w
    have hre : (1 / 20 : ℝ) ≤ s.re := by
      have hh := Complex.abs_re_le_norm w
      have hn := (abs_le.mp (hh.trans hw)).1
      dsimp [s, c]
      simp only [div_ofNat_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      linarith
    have hnorm : ‖s‖ ≤ |t| + 3 := by
      calc
        _ ≤ ‖c‖ + ‖(3 / 2 : ℂ) * w‖ := norm_add_le _ _
        _ ≤ (3 / 2 + |t|) + (3 / 2) * ‖w‖ := by
          gcongr
          · dsimp [c]
            have hh := norm_add_le (3 / 2 : ℂ) (I * (t : ℂ))
            norm_num [norm_mul] at hh
            exact hh
          · rw [norm_mul]; norm_num
        _ ≤ _ := by linarith
    have hnormL : ‖f w‖ ≤ 20 * M := by
      have hh := norm_LFunction_le hχ (s := s) (by linarith : 0 < s.re)
      have hh' : ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * (|t| + 3) / (1 / 20) :=
        hh.trans (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnorm (by positivity))
          (by norm_num) hre)
      change ‖f w‖ ≤ 20 * M
      convert hh' using 1; dsimp [M, f, s]; ring
    have hden : 1 ≤ Z * ‖f 0‖ := by
      have hh : 1 / Z ≤ ‖f 0‖ := by
        simpa only [f, c, mul_zero, add_zero] using norm_LFunction_ge χ t
      simpa only [mul_comm] using (div_le_iff₀ Z_pos).mp hh
    have hpos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
    change ‖f w / f 0‖ ≤ B
    rw [norm_div, div_le_iff₀ hpos]
    calc
      ‖f w‖ ≤ 20 * M := hnormL
      _ ≤ 20 * M * (Z * ‖f 0‖) := le_mul_of_one_le_right (by positivity) hden
      _ = B * ‖f 0‖ := by dsimp [B]; ring
  exact ⟨hgA, hg0, hgFinite, hgBound⟩

/-- Conductor-uniform local partial fraction estimate on a disc reaching the critical line.
The affine coordinate maps the evaluation disc to radius eleven eighths around 3/2 plus it.
Auxiliary derivation for Davenport chapters 19 and 20, supporting P0011 page 101. -/
theorem character_scaled_local266 : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
      let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t + (3 / 2 : ℂ) * z)
      ∃ hf : (SetOfZeros (14 / 15) f).Finite, ∀ z : ℂ, ‖z‖ ≤ 11 / 12 → f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
          K * Real.log ((q : ℝ) * (|t| + 3)) := by
  let C : ℝ := 16 * (14 / 15 : ℝ) ^ 2 / (14 / 15 - 11 / 12) ^ 3 +
    1 / (((29 / 30 : ℝ) ^ 2 / (19 / 20) - 19 / 20) * Real.log ((29 / 30) / (19 / 20)))
  have hC : 0 < C := by
    have : 0 < Real.log ((29 / 30 : ℝ) / (19 / 20)) := Real.log_pos (by norm_num)
    dsimp [C]; positivity
  let D : ℝ := |Real.log (20 * Z)|
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨C * (1 + D / Real.log 3), by positivity, ?_⟩
  intro q _ χ hχ t
  dsimp only
  let c : ℂ := (3 : ℂ) / 2 + I * t
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * z)
  let g : ℂ → ℂ := fun z => f z / f 0
  have hfA (z : ℂ) : AnalyticAt ℂ f z := by
    have hd : Differentiable ℂ f := (DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)
    exact hd.analyticAt z
  have hf0 : f 0 ≠ 0 := by
    simpa only [f, c, mul_zero, add_zero] using LFunction_c_ne_zero χ t
  have hzeros (R : ℝ) : SetOfZeros R g = SetOfZeros R f := by
    ext z
    simp [SetOfZeros, g, hf0]
  obtain ⟨hgA, hg0, hgFinite, hgBound⟩ := character_scaled_setup266 χ hχ t
  have hfFinite : (SetOfZeros 1 f).Finite := by rw [← hzeros]; exact hgFinite
  let M : ℝ := (q : ℝ) * (|t| + 3)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 3 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t]
  let B : ℝ := 20 * Z * M
  have hB : 1 < B := by dsimp [B]; nlinarith [one_le_Z]
  let hf := finiteSetOfZeros_mono (by norm_num : (14 / 15 : ℝ) < 1) hfFinite
  refine ⟨hf, ?_⟩
  intro z hz hfz
  have hzmem : z ∈ closedBall (0 : ℂ) (11 / 12) \ SetOfZeros (19 / 20) g := by
    refine ⟨mem_closedBall_zero_iff.mpr hz, ?_⟩
    rw [hzeros]
    exact fun h => hfz h.2
  have key := FinalBound hB (by norm_num : (0 : ℝ) < 11 / 12)
    (by norm_num : (11 / 12 : ℝ) < 14 / 15) (by norm_num : (14 / 15 : ℝ) < 1)
    (by norm_num : (14 / 15 : ℝ) < 19 / 20) (by norm_num : (19 / 20 : ℝ) < 29 / 30)
    (by norm_num : (29 / 30 : ℝ) < 1) hgA hg0 hgFinite hgBound hzmem
  change ‖deriv g z / g z - ∑ ρ ∈
      (finiteSetOfZeros_mono (by norm_num : (14 / 15 : ℝ) < 1) hgFinite).toFinset,
      (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ ≤ C * Real.log B at key
  have hset : (finiteSetOfZeros_mono (by norm_num : (14 / 15 : ℝ) < 1) hgFinite).toFinset = hf.toFinset := by
    simp only [Set.Finite.toFinset_inj]
    exact hzeros _
  have hderiv : deriv g z / g z = deriv f z / f z := by
    have hd : deriv g z = deriv f z / f 0 := by dsimp [g]; rw [deriv_div_const]
    rw [hd]
    dsimp [g]
    field_simp
  have hord (ρ : ℂ) : analyticOrderNatAt g ρ = analyticOrderNatAt f ρ :=
    analyticOrderNatAt_fun_div_const hf0 (hfA ρ)
  rw [hset, hderiv] at key
  simp only [hord] at key
  change ‖deriv f z / f z - ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ C * Real.log B at key
  have hlogM : Real.log 3 ≤ Real.log M := Real.log_le_log (by norm_num) hM
  have hD : D ≤ D / Real.log 3 * Real.log M := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog3]
    exact mul_le_mul_of_nonneg_left hlogM (abs_nonneg _)
  have hlogB : Real.log B ≤ (1 + D / Real.log 3) * Real.log M := by
    rw [show B = (20 * Z) * M by rfl, Real.log_mul (by have := Z_pos; positivity) (by linarith)]
    have hh : Real.log (20 * Z) ≤ D := le_abs_self _
    nlinarith
  exact key.trans (by nlinarith)

/-- Jensen gives a local multiplicity count uniform in the modulus on the same enlarged disc.
Auxiliary derivation for Davenport chapter 19 pages 117 to 120. -/
theorem character_scaled_zero_count266 : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
      let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t + (3 / 2 : ℂ) * z)
      ∃ hf : (SetOfZeros (14 / 15) f).Finite,
        (∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ)) ≤
          K * Real.log ((q : ℝ) * (|t| + 3)) := by
  let D : ℝ := |Real.log (20 * Z)|
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogR : 0 < Real.log ((29 / 30 : ℝ) / (14 / 15)) := Real.log_pos (by norm_num)
  refine ⟨(1 / Real.log ((29 / 30 : ℝ) / (14 / 15))) * (1 + D / Real.log 3), by positivity, ?_⟩
  intro q _ χ hχ t
  dsimp only
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t + (3 / 2 : ℂ) * z)
  let g : ℂ → ℂ := fun z => f z / f 0
  have hfA (z : ℂ) : AnalyticAt ℂ f z := by
    have hd : Differentiable ℂ f := (DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)
    exact hd.analyticAt z
  have hf0 : f 0 ≠ 0 := by
    simpa only [f, mul_zero, add_zero] using LFunction_c_ne_zero χ t
  have hzeros (R : ℝ) : SetOfZeros R g = SetOfZeros R f := by
    ext z
    simp [SetOfZeros, g, hf0]
  obtain ⟨hgA, hg0, hgFinite, hgBound⟩ := character_scaled_setup266 χ hχ t
  have hfFinite : (SetOfZeros 1 f).Finite := by rw [← hzeros]; exact hgFinite
  let hf := finiteSetOfZeros_mono (by norm_num : (14 / 15 : ℝ) < 1) hfFinite
  refine ⟨hf, ?_⟩
  let M : ℝ := (q : ℝ) * (|t| + 3)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 3 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t]
  let B : ℝ := 20 * Z * M
  have key := ZerosBound (by norm_num : (0 : ℝ) < 14 / 15)
    (by norm_num : (14 / 15 : ℝ) < 1) (by norm_num : (14 / 15 : ℝ) < 29 / 30)
    (by norm_num : (29 / 30 : ℝ) < 1) hgA hg0 hgFinite hgBound
  push_cast at key
  change (∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (14 / 15 : ℝ) < 1) hgFinite).toFinset,
    (analyticOrderNatAt g ρ : ℝ)) ≤ 1 / Real.log ((29 / 30) / (14 / 15)) * Real.log B at key
  have hset : (finiteSetOfZeros_mono (by norm_num : (14 / 15 : ℝ) < 1) hgFinite).toFinset = hf.toFinset := by
    simp only [Set.Finite.toFinset_inj]
    exact hzeros _
  rw [hset] at key
  have hord (ρ : ℂ) : analyticOrderNatAt g ρ = analyticOrderNatAt f ρ :=
    analyticOrderNatAt_fun_div_const hf0 (hfA ρ)
  simp only [hord] at key
  have hlogM : Real.log 3 ≤ Real.log M := Real.log_le_log (by norm_num) hM
  have hD : D ≤ D / Real.log 3 * Real.log M := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog3]
    exact mul_le_mul_of_nonneg_left hlogM (abs_nonneg _)
  have hlogB : Real.log B ≤ (1 + D / Real.log 3) * Real.log M := by
    rw [show B = (20 * Z) * M by rfl, Real.log_mul (by have := Z_pos; positivity) (by linarith)]
    have hh : Real.log (20 * Z) ≤ D := le_abs_self _
    nlinarith
  exact key.trans (by nlinarith [one_div_pos.mpr hlogR])

/-- Under GRH the logarithmic derivative on real part one eighth has logarithmic growth,
uniformly in the modulus. This is a left-edge input, not an explicit formula.
Auxiliary derivation for Davenport chapter 20 page 125 and P0011 page 101. -/
theorem character_left_eighth_GRH266 (hG : LeanLab.DERZ1997.GRH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ t : ℝ, DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
          DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)‖ ≤
            K * Real.log ((q : ℝ) * (|t| + 3)) := by
  obtain ⟨A, hA, hpartial⟩ := character_scaled_local266
  obtain ⟨B, hB, hcount⟩ := character_scaled_zero_count266
  refine ⟨(2 / 3) * (A + 4 * B), by positivity, ?_⟩
  intro q _ χ hχ t
  let c : ℂ := (3 : ℂ) / 2 + I * t
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * z)
  let z : ℂ := -11 / 12
  let s : ℂ := (1 / 8 : ℂ) + I * t
  have hsz : c + (3 / 2 : ℂ) * z = s := by dsimp [c, z, s]; ring
  have hsre : s.re = 1 / 8 := by simp [s]
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro hh
    have hg := hG q χ s hh (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
    rw [hsre] at hg
    norm_num at hg
  refine ⟨hLs, ?_⟩
  obtain ⟨hf, hp⟩ := hpartial q χ hχ t
  obtain ⟨hf', hc⟩ := hcount q χ hχ t
  have hmass : (∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ)) ≤
      B * Real.log ((q : ℝ) * (|t| + 3)) := hc
  have hsep (ρ : ℂ) (hρ : ρ ∈ hf.toFinset) : (1 / 4 : ℝ) ≤ ‖z - ρ‖ := by
    have hh := hf.mem_toFinset.mp hρ
    have hr : 0 < (c + (3 / 2 : ℂ) * ρ).re := by
      have hn := Complex.abs_re_le_norm ρ
      have hlo := (abs_le.mp (hn.trans hh.1)).1
      dsimp [c]
      simp only [div_ofNat_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      linarith
    have hz : DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * ρ) = 0 := hh.2
    have hr1 : (c + (3 / 2 : ℂ) * ρ).re < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hz
    have hline := hG q χ (c + (3 / 2 : ℂ) * ρ) hz hr hr1
    have hre : ρ.re = -2 / 3 := by
      dsimp [c] at hline
      simp only [div_ofNat_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero] at hline
      norm_num at hline
      linarith
    have habs := Complex.abs_re_le_norm (z - ρ)
    have he : |(z - ρ).re| = 1 / 4 := by simp [z, hre]; norm_num
    rwa [he] at habs
  let S : ℂ := ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)
  have hsum : ‖S‖ ≤ 4 * B * Real.log ((q : ℝ) * (|t| + 3)) := by
    calc
      _ ≤ ∑ ρ ∈ hf.toFinset, ‖(analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ) / (1 / 4) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (hsep ρ hρ)
      _ = 4 * ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ) := by rw [← Finset.sum_div]; ring
      _ ≤ _ := by nlinarith
  have hfn : f z ≠ 0 := by change DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * z) ≠ 0; rwa [hsz]
  have hpart := hp z (by norm_num [z]) hfn
  have htri : ‖deriv f z / f z‖ ≤ (A + 4 * B) * Real.log ((q : ℝ) * (|t| + 3)) := by
    have hh := norm_sub_le (deriv f z / f z - S) (-S)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hh
    change ‖deriv f z / f z‖ ≤ _
    change ‖deriv f z / f z - S‖ ≤ _ at hpart
    nlinarith
  have hderiv : deriv f z = (3 / 2 : ℂ) * deriv (DirichletCharacter.LFunction χ) s := by
    have haff : HasDerivAt (fun w : ℂ => c + (3 / 2 : ℂ) * w) (3 / 2 : ℂ) z := by
      simpa only [id_eq, mul_one, add_comm] using ((hasDerivAt_id z).const_mul (3 / 2 : ℂ)).const_add c
    have hh := ((DirichletCharacter.differentiable_LFunction hχ (c + (3 / 2 : ℂ) * z)).hasDerivAt.comp z haff)
    have he : c + (3 / 2 : ℂ) * z = s := hsz
    rw [he] at hh
    simpa only [f, Function.comp_def, mul_comm] using hh.deriv
  have hfnval : f z = DirichletCharacter.LFunction χ s := by change DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * z) = _; rw [hsz]
  rw [hderiv, hfnval, mul_div_assoc, norm_mul] at htri
  norm_num only [norm_div, norm_ofNat] at htri
  change ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ _
  rw [norm_div]
  nlinarith

/-- The logarithmic loss on the positive left edge fits the allowed square-root error.
Auxiliary numerical budget for Davenport chapter 20 page 125. -/
theorem left_edge_budget266 {x L : ℝ} (hx : 2 ≤ x) (hL : 0 ≤ L) :
    x ^ (1 / 8 : ℝ) * Real.log x * L ≤ 4 * (Real.sqrt x + L ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hh := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by convert hh using 1 <;> ring
  have he : x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hs : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le (1 / 8 : ℝ))
  have hmulL := mul_le_mul_of_nonneg_right hmul hL
  nlinarith [sq_nonneg (x ^ (1 / 4 : ℝ) - L)]

/-- The unsmoothed character Perron kernel has the expected zero residue.
This applies to every nonzero point and is zero at regular points. No GRH is used.
Auxiliary derivation for Davenport chapter 19 pages 119 to 120. -/
theorem character_perron_residue266 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ ≠ 0) :
    residue (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ρ =
        -(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  have hA (z : ℂ) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Set.univ : Set ℂ) := fun z _ => hA z
  have h2 : analyticOrderAt (DirichletCharacter.LFunction χ) 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)))]
    simp
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    hU.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 2) (y := ρ)
      (by simp) (by simp) h2
  have hord : meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ =
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℤ) := by
    rw [(hA ρ).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
    simp
  apply residue_eq_of_tendsto
  have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) ρ :=
    (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx ρ).div analyticAt_id hρ
  have hl := LeanLab.PNTPort.ExplicitPsi1.tendsto_mul_logDeriv_mero (hA ρ).meromorphicAt hord
  have ht := (hl.mul (hk.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ)))).neg
  have ht' : Tendsto (fun s : ℂ => -((s - ρ) *
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      ((x : ℂ) ^ s / s))) (𝓝[≠] ρ)
      (𝓝 (-((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)))) := by
    simpa only [Int.cast_natCast] using ht
  rw [show -(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ =
    -((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) by ring]
  refine ht'.congr (fun s => ?_)
  ring

/-- The unsmoothed rectangle identity for a nonprincipal character in a positive half-plane.
The zero sum is over the exact finite rectangle. Edge estimates and GRH are separate steps.
Auxiliary derivation for Davenport chapter 19 page 120. -/
theorem character_rectangle266 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {x a b T : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a < b) (hT : 0 < T)
    (hf : (Rectangle (⟨a, -T⟩ : ℂ) ⟨b, T⟩ ∩ {s : ℂ | DirichletCharacter.LFunction χ s = 0}).Finite)
    (hbd : ∀ z ∈ RectangleBorder (⟨a, -T⟩ : ℂ) ⟨b, T⟩, DirichletCharacter.LFunction χ z ≠ 0) :
    RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ⟨a, -T⟩ ⟨b, T⟩ =
        -(∑ ρ ∈ hf.toFinset, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
          (x : ℂ) ^ ρ / ρ) := by
  classical
  let L := DirichletCharacter.LFunction χ
  let F : ℂ → ℂ := fun s => -(deriv L s / L s) * (x : ℂ) ^ s / s
  let R := Rectangle (⟨a, -T⟩ : ℂ) ⟨b, T⟩
  let P := hf.toFinset
  have hA (z : ℂ) : AnalyticAt ℂ L z := (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hre {z : ℂ} (hz : z ∈ R) : a ≤ z.re := by
    change z.re ∈ Set.uIcc a b ∧ z.im ∈ Set.uIcc (-T) T at hz
    rw [Set.uIcc_of_le hab.le] at hz
    exact hz.1.1
  have h0 {z : ℂ} (hz : z ∈ R) : z ≠ 0 := by
    intro he
    have hh := hre hz
    rw [he] at hh
    simp only [zero_re] at hh
    linarith
  have hkernel (z : ℂ) (hz : z ≠ 0) : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) z :=
    (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx z).div analyticAt_id hz
  have hF : F = (fun s => -logDeriv L s) * (fun s : ℂ => (x : ℂ) ^ s / s) := by
    funext s
    simp only [F, Pi.mul_apply, logDeriv_apply]
    ring
  have hmero (z : ℂ) : MeromorphicAt F z := by
    rw [hF]
    exact ((hA z).meromorphicAt.deriv.div (hA z).meromorphicAt).neg.mul
      ((LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx z).meromorphicAt.div analyticAt_id.meromorphicAt)
  have hgood (z : ℂ) (hz : z ∈ R) (hn : L z ≠ 0) : 0 ≤ meromorphicOrderAt F z := by
    have hh : AnalyticAt ℂ F z := by
      rw [hF]
      exact ((hA z).deriv.div (hA z) hn).neg.mul (hkernel z (h0 hz))
    exact hh.meromorphicOrderAt_nonneg
  have hU : AnalyticOnNhd ℂ L (Set.univ : Set ℂ) := fun z _ => hA z
  have h2 : analyticOrderAt L 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)))]
    simp
  have horder (z : ℂ) : meromorphicOrderAt L z = (analyticOrderNatAt L z : ℤ) := by
    have htop := hU.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 2) (y := z) (by simp) (by simp) h2
    rw [(hA z).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
    simp
  have hsimple (z : ℂ) (hz : z ∈ R) : -1 ≤ meromorphicOrderAt F z := by
    have hL : -1 ≤ meromorphicOrderAt (logDeriv L) z := by
      by_cases ho : meromorphicOrderAt L z = 0
      · exact (WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)).trans
          (meromorphicOrderAt_logDeriv_nonneg (hA z).meromorphicAt ho)
      · rw [meromorphicOrderAt_logDeriv_eq_neg_one (hA z).meromorphicAt ho
          (by rw [horder z]; simp)]
    have hML : MeromorphicAt (fun s => -logDeriv L s) z :=
      ((hA z).meromorphicAt.deriv.div (hA z).meromorphicAt).neg
    rw [hF, meromorphicOrderAt_mul hML (hkernel z (h0 hz)).meromorphicAt]
    have hneg : meromorphicOrderAt (fun s => -logDeriv L s) z =
        meromorphicOrderAt (logDeriv L) z := (meromorphicOrderAt_neg (f := logDeriv L)).symm
    rw [hneg]
    calc
      (-1 : WithTop ℤ) = -1 + 0 := by simp
      _ ≤ _ := add_le_add hL (hkernel z (h0 hz)).meromorphicOrderAt_nonneg
  have hP (z : ℂ) (hz : z ∈ R) (hp : meromorphicOrderAt F z < 0) : z ∈ P := by
    by_contra hn
    have hL : L z ≠ 0 := by
      intro he
      exact hn (hf.mem_toFinset.mpr ⟨hz, he⟩)
    exact not_lt_of_ge (hgood z hz hL) hp
  have hbR := rectangleBorder_subset_rectangle (⟨a, -T⟩ : ℂ) ⟨b, T⟩
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := F)
    (z := ⟨a, -T⟩) (w := ⟨b, T⟩) hab.le (by simp; linarith)
    (fun z _ => hmero z)
    (by
      apply Set.disjoint_left.mpr
      intro z hz hp
      exact not_lt_of_ge (hgood z (hbR hz) (hbd z hz)) hp)
    (by
      apply P.finite_toSet.subset
      intro z hz
      exact hP z hz.1 hz.2) hsimple
  change RectangleIntegral' F (⟨a, -T⟩ : ℂ) ⟨b, T⟩ = _
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt F z < 0} =
      (P : Set ℂ) ∩ {z | meromorphicOrderAt F z < 0} := by
    ext z
    constructor
    · rintro ⟨hz, hp⟩
      exact ⟨hP z hz hp, hp⟩
    · rintro ⟨hz, hp⟩
      exact ⟨(hf.mem_toFinset.mp hz).1, hp⟩
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (hmero z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' P (fun z => residue F z)]
  calc
    _ = ∑ ρ ∈ P, -((analyticOrderNatAt L ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hz := (hf.mem_toFinset.mp hρ).1
      rw [character_perron_residue266 χ hχ hx (h0 hz)]
      ring
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- Under GRH the positive-left rectangle contains exactly the sealed L-zero set.
This ports the finite unsmoothed contour identity for nonprincipal characters.
It does not bound the other three edges. Davenport chapter 19 page 120. -/
theorem character_contour_GRH266 (hG : LeanLab.DERZ1997.GRH)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder (⟨1 / 8, -T⟩ : ℂ) ⟨c, T⟩, DirichletCharacter.LFunction χ z ≠ 0)
    (hfin : (LeanLab.DERZ1997.Decomp1529a.LZeros χ T).Finite) :
    RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ⟨1 / 8, -T⟩ ⟨c, T⟩ =
        -(∑ ρ ∈ hfin.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
  classical
  have heq : Rectangle (⟨1 / 8, -T⟩ : ℂ) ⟨c, T⟩ ∩
      {s : ℂ | DirichletCharacter.LFunction χ s = 0} = LeanLab.DERZ1997.Decomp1529a.LZeros χ T := by
    ext z
    constructor
    · rintro ⟨hz, hzero⟩
      change z.re ∈ Set.uIcc (1 / 8) c ∧ z.im ∈ Set.uIcc (-T) T at hz
      rw [Set.uIcc_of_le (show (1 / 8 : ℝ) ≤ c by linarith),
        Set.uIcc_of_le (show -T ≤ T by linarith)] at hz
      have hre : 0 < z.re := by linarith [hz.1.1]
      have hre1 : z.re < 1 := by
        by_contra hn
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hzero
      exact ⟨hzero, hre, hre1, abs_le.mpr hz.2⟩
    · intro hz
      have hline := hG q χ z hz.1 hz.2.1 hz.2.2.1
      refine ⟨?_, hz.1⟩
      change z.re ∈ Set.uIcc (1 / 8) c ∧ z.im ∈ Set.uIcc (-T) T
      rw [Set.uIcc_of_le (show (1 / 8 : ℝ) ≤ c by linarith),
        Set.uIcc_of_le (show -T ≤ T by linarith)]
      exact ⟨⟨by linarith, by linarith⟩, abs_le.mp hz.2.2.2⟩
  have hf : (Rectangle (⟨1 / 8, -T⟩ : ℂ) ⟨c, T⟩ ∩
      {s : ℂ | DirichletCharacter.LFunction χ s = 0}).Finite := by rw [heq]; exact hfin
  have hset : hf.toFinset = hfin.toFinset := by
    simp only [Set.Finite.toFinset_inj]
    exact heq
  have hh := character_rectangle266 χ hχ hx (by norm_num : (0 : ℝ) < 1 / 8)
    (by linarith : (1 / 8 : ℝ) < c) hT hf hbd
  rw [hset] at hh
  exact hh

end LeanLab.DERZ1997.Character266
