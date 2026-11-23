module

public import LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122
public import LeanLab.HelfgottMajor.LogResidue669
public import LeanLab.BhowmikGrimmelt2026.RouteWindow508
public import LeanLab.PNTPort.ExplicitPsi1.CharDiscExpansion1122

/-!
# The constant `b(χ)` regrouped with the low zeros, Davenport ch. 19 p. 118

ROUTE BURST burst-20261122, session S65, unit bregroup1122. AI wrote the Lean code. Binary
Goldbach is OPEN; nothing here bears on it directly. This file proves the statement of the HARD
leaf `CharTrivial1122.b_regroup_leaf` along the cheaper route recorded in its comment.

Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 118, after display (8):
`b(χ) = O(log q) - Σ_{|γ|<1} 1/ρ`. Route used here, every step a display of Davenport:

* ch. 9, the functional equation, differentiated at `s = 0` and `s = 1`: for primitive
  `χ ≠ 1`, `b(χ) = log(2π/q) + γ - conj(L'/L(1, χ))` in both parities. This is the lab theorem
  `HelfgottMajor.LogResidue669.logDeriv_regular_limit`; `b_eq_closed_form` identifies it with
  the `b` of `b_regroup_leaf`. PROVED.
* ch. 9 again: `ρ ↦ 1 - ρ` maps the strip zeros of `L(s, χ)` onto those of `L(s, χ̄)` with the
  same multiplicity, `order_reflection`. PROVED.
* ch. 16 p. 102 display (4) at `s = 1`, `t = 0`: `L'/L(1, χ̄) = Σ_{|γ'|<1} 1/(1 - ρ') + O(log q)`.
  `local_expansion_one`, PROVED from the disc form `CharDiscExpansion1122.disc_expansion_one`,
  Landau's lemma through the lab `FinalBound`, and the multiplicity count of ch. 16 display (3),
  `strip_mult_count`.

`b_regroup` then has exactly the statement of `b_regroup_leaf`, PROVED with no LEAF.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharBRegroup1122

open Complex Filter Topology Set
open scoped Real

/-- Davenport ch. 16 p. 102 display (3) at `t = ±1`, with multiplicity: the strip zeros with
`|Im ρ| ≤ 2` have total multiplicity `O(log q)`. From the lab count
`BhowmikGrimmelt2026.zero_window_count_full508`. -/
theorem strip_mult_count : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (ψ : DirichletCharacter ℂ q), 2 ≤ q → ∀ Y : Finset ℂ,
      (∀ ρ ∈ Y, DirichletCharacter.LFunction ψ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2) →
      ∑ ρ ∈ Y, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ) ≤
        A * Real.log q := by
  obtain ⟨A, hA0, hA⟩ := BhowmikGrimmelt2026.zero_window_count_full508
  refine ⟨6 * A, by positivity, ?_⟩
  intro q _ ψ hq Y hY
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hl2 := Real.log_two_gt_d9
  have hlog3q : Real.log ((q : ℝ) * (|(1 : ℝ)| + 2)) ≤ 3 * Real.log q := by
    have : Real.log ((q : ℝ) * (|(1 : ℝ)| + 2)) = Real.log q + Real.log 3 := by
      rw [Real.log_mul (by positivity) (by norm_num)]; norm_num
    rw [this]
    have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have hlog3q' : Real.log ((q : ℝ) * (|(-1 : ℝ)| + 2)) ≤ 3 * Real.log q := by
    simpa using hlog3q
  have hsplit := Finset.sum_filter_add_sum_filter_not Y (fun ρ : ℂ => 0 ≤ ρ.im)
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ))
  have h1 : ∑ ρ ∈ Y with 0 ≤ ρ.im,
      (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ) ≤
      A * Real.log ((q : ℝ) * (|(1 : ℝ)| + 2)) := by
    apply hA q ψ 1
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, h0, h1, him⟩ := hY ρ hρ.1
    refine ⟨hz, h0, h1, ?_⟩
    rw [abs_le] at him ⊢
    constructor <;> linarith [hρ.2]
  have h2 : ∑ ρ ∈ Y with ¬ 0 ≤ ρ.im,
      (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ) ≤
      A * Real.log ((q : ℝ) * (|(-1 : ℝ)| + 2)) := by
    apply hA q ψ (-1)
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, h0, h1, him⟩ := hY ρ hρ.1
    refine ⟨hz, h0, h1, ?_⟩
    rw [abs_le] at him ⊢
    have := hρ.2
    push_neg at this
    constructor <;> linarith
  rw [← hsplit]
  have e1 := mul_le_mul_of_nonneg_left hlog3q hA0
  have e2 := mul_le_mul_of_nonneg_left hlog3q' hA0
  nlinarith

/-- The zeros of `L(s, ψ)`, `ψ ≠ 1`, in a closed disc are finitely many. -/
lemma zeros_closedBall_finite {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    (c : ℂ) (r : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction ψ ρ = 0 ∧ ‖ρ - c‖ ≤ r}.Finite := by
  have hK : IsCompact (Metric.closedBall c r) := isCompact_closedBall c r
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hψ).analyticAt z
  have hn : DirichletCharacter.LFunction ψ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (by norm_num)
  have hd := ha.preimage_zero_mem_codiscrete hn
  have := hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (Set.subset_univ _) hd)
  refine this.subset ?_
  rintro ρ ⟨hz, hr⟩
  refine ⟨Metric.mem_closedBall.2 (by rwa [dist_eq_norm]), ?_⟩
  simp [hz]

/-- A sum of `m(ρ)/(1 - ρ)` with every `‖1 - ρ‖ ≥ 1/2` is at most `2 Σ m(ρ)`. -/
lemma norm_sum_le_two_mul {f : ℂ → ℂ} (Y : Finset ℂ) (hY : ∀ ρ ∈ Y, 1 / 2 ≤ ‖1 - ρ‖) :
    ‖∑ ρ ∈ Y, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)‖ ≤
      2 * ∑ ρ ∈ Y, (analyticOrderNatAt f ρ : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have h := hY ρ hρ
  have hpos : 0 < ‖1 - ρ‖ := by linarith
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hpos]
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt f ρ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Davenport, Multiplicative Number Theory, second edition, ch. 16 p. 102 display (4) at
`s = 1`, `t = 0`, in the window form `|Im ρ| < 1` over the strip zeros, from the disc form
`CharDiscExpansion1122.disc_expansion_one` and the zero count `strip_mult_count`. -/
theorem local_expansion_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (ψ : DirichletCharacter ℂ q), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ W : Finset ℂ, (∀ ρ : ℂ, ρ ∈ W ↔ DirichletCharacter.LFunction ψ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) →
      ‖deriv (DirichletCharacter.LFunction ψ) 1 / DirichletCharacter.LFunction ψ 1 -
        ∑ ρ ∈ W, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℂ) / (1 - ρ)‖ ≤
        C * Real.log q := by
  obtain ⟨C, hC, hdisc⟩ := CharDiscExpansion1122.disc_expansion_one
  obtain ⟨A, hA, hcount⟩ := strip_mult_count
  refine ⟨C + 4 * A, by positivity, ?_⟩
  intro q _ ψ hψ hne W hW
  have hq2 : 2 ≤ q := by
    have h1 := CharTrivial1122.modulus_ne_one hne
    have := NeZero.ne q
    omega
  set f := DirichletCharacter.LFunction ψ
  set V : Finset ℂ := (zeros_closedBall_finite ψ hne (3 / 2) (29 / 25)).toFinset with hVdef
  have hV : ∀ ρ : ℂ, ρ ∈ V ↔ f ρ = 0 ∧ ‖ρ - 3 / 2‖ ≤ 29 / 25 := by
    intro ρ; rw [hVdef, Set.Finite.mem_toFinset]; rfl
  have hD := hdisc q ψ hψ hne V hV
  -- every zero of the disc lies in the open strip with `|Im ρ| ≤ 2`
  have hVstrip : ∀ ρ ∈ V, f ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 := by
    intro ρ hρ
    obtain ⟨hz, hr⟩ := (hV ρ).1 hρ
    have hre : |(ρ - 3 / 2).re| ≤ ‖ρ - 3 / 2‖ := Complex.abs_re_le_norm _
    have him : |(ρ - 3 / 2).im| ≤ ‖ρ - 3 / 2‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    norm_num at hre him
    rw [abs_le] at hre
    refine ⟨hz, by linarith [hre.1], ?_, by linarith⟩
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hne) h hz
  have hWstrip : ∀ ρ ∈ W, f ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, him⟩ := (hW ρ).1 hρ
    exact ⟨hz, h0, h1, by linarith⟩
  have hVW : ∀ ρ ∈ V \ W, 1 / 2 ≤ ‖1 - ρ‖ := by
    intro ρ hρ
    rw [Finset.mem_sdiff] at hρ
    obtain ⟨hz, h0, h1, -⟩ := hVstrip ρ hρ.1
    have him : 1 ≤ |ρ.im| := by
      by_contra h
      push_neg at h
      exact hρ.2 ((hW ρ).2 ⟨hz, h0, h1, h⟩)
    have := Complex.abs_im_le_norm (1 - ρ)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    linarith
  have hWV : ∀ ρ ∈ W \ V, 1 / 2 ≤ ‖1 - ρ‖ := by
    intro ρ hρ
    rw [Finset.mem_sdiff] at hρ
    have hz := ((hW ρ).1 hρ.1).1
    have hr : 29 / 25 < ‖ρ - 3 / 2‖ := by
      by_contra h
      push_neg at h
      exact hρ.2 ((hV ρ).2 ⟨hz, h⟩)
    have htri : ‖ρ - 3 / 2‖ ≤ ‖1 - ρ‖ + ‖(1 / 2 : ℂ)‖ := by
      have e : ρ - 3 / 2 = -(1 - ρ) - 1 / 2 := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    linarith
  have hcVW := hcount q ψ hq2 (V \ W) fun ρ hρ => hVstrip ρ (Finset.mem_sdiff.1 hρ).1
  have hcWV := hcount q ψ hq2 (W \ V) fun ρ hρ => hWstrip ρ (Finset.mem_sdiff.1 hρ).1
  have hn1 := norm_sum_le_two_mul (f := f) (V \ W) hVW
  have hn2 := norm_sum_le_two_mul (f := f) (W \ V) hWV
  have hdiff := Finset.sum_sdiff_sub_sum_sdiff (s₁ := V) (s₂ := W)
    (f := fun ρ => (analyticOrderNatAt f ρ : ℂ) / (1 - ρ))
  set SV := ∑ ρ ∈ V, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)
  set SW := ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)
  set D := deriv f 1 / f 1
  have he : D - SW = (D - SV) - ((∑ ρ ∈ W \ V, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)) -
      ∑ ρ ∈ V \ W, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)) := by
    rw [hdiff]; ring
  rw [he]
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  calc _ ≤ ‖D - SV‖ + (‖∑ ρ ∈ W \ V, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)‖ +
          ‖∑ ρ ∈ V \ W, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ)‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ C * Real.log q + (2 * (A * Real.log q) + 2 * (A * Real.log q)) := by
        gcongr
        · exact hn2.trans (by linarith)
        · exact hn1.trans (by linarith)
    _ = (C + 4 * A) * Real.log q := by ring

/-- Davenport ch. 9: `L(s, χ)` is analytic away from `s = 1`. -/
lemma analyticAt_L_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ1 : ρ ≠ 1) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {(1 : ℂ)}ᶜ := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hρ1)

/-- Davenport ch. 9: for primitive `χ` the order of `L(s, χ)` at a strip point `ρ` equals the
order of `L(s, χ̄)` at `1 - ρ`. -/
theorem order_reflection {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have ha := BhowmikGrimmelt2026.primitive_order_reflection_le508 χ hχ h0 h1
  have hb := BhowmikGrimmelt2026.primitive_order_reflection_le508 χ⁻¹ hi
    (ρ := 1 - ρ) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  rw [inv_inv, sub_sub_cancel] at hb
  exact le_antisymm hb ha

/-- Davenport ch. 9: `ρ` is a strip zero of `L(s, χ)` iff `1 - ρ` is one of `L(s, χ̄)`. -/
theorem zero_reflection {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 ↔ DirichletCharacter.LFunction χ ρ = 0 := by
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at h1
  have hρ1' : 1 - ρ ≠ 1 := by intro h; simp [sub_eq_self] at h; simp [h] at h0
  rw [← (analyticAt_L_of_ne_one χ hρ1).analyticOrderAt_ne_zero,
    ← (analyticAt_L_of_ne_one χ⁻¹ hρ1').analyticOrderAt_ne_zero, order_reflection χ hχ h0 h1]

/-- An odd character is not even, as `χ(-1)` cannot be both `1` and `-1` in `ℂ`. -/
lemma not_even_of_odd {q : ℕ} {χ : DirichletCharacter ℂ q} (h : χ.Odd) : ¬ χ.Even := by
  intro he
  have h1 : χ (-1) = 1 := he
  have h2 : χ (-1) = -1 := h
  rw [h1] at h2
  norm_num at h2

/-- Davenport ch. 19 p. 116 with ch. 9: the `b` of `CharTrivial1122.b_regroup_leaf`, defined by
parity as `L'/L(0, χ)` or as the constant term of `L'/L` at `0`, equals
`log(2π/q) + γ - conj(L'/L(1, χ))`. -/
theorem b_eq_closed_form {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (b : ℂ)
    (hb : (χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
          DirichletCharacter.LFunction χ 0) ∨
        (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) :
    b = (((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ)) -
        (starRingEnd ℂ) (logDeriv (DirichletCharacter.LFunction χ) 1) := by
  have hq : q ≠ 1 := CharTrivial1122.modulus_ne_one hne
  have hlim := HelfgottMajor.LogResidue669.logDeriv_regular_limit χ hχ hq
  rcases hb with ⟨hodd, rfl⟩ | ⟨heven, hb⟩
  · have hne' := not_even_of_odd hodd
    simp only [if_neg hne', sub_zero] at hlim
    have hL0 : DirichletCharacter.LFunction χ 0 ≠ 0 :=
      (CharTrivial1122.residue_zero_odd hχ hne hodd (x := 1) one_pos).1
    have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 0 :=
      analyticAt_L_of_ne_one χ (by norm_num)
    have hc : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) 0 := by
      have : ContinuousAt (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s) 0 :=
        (hA.deriv.continuousAt).div hA.continuousAt hL0
      have e : logDeriv (DirichletCharacter.LFunction χ) = fun s =>
          deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
        funext s; exact logDeriv_apply _ _
      rw [e]; exact this
    have h2 : Tendsto (logDeriv (DirichletCharacter.LFunction χ)) (𝓝[≠] 0)
        (𝓝 (logDeriv (DirichletCharacter.LFunction χ) 0)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have := tendsto_nhds_unique h2 hlim
    rw [← this, logDeriv_apply]
  · simp only [if_pos heven] at hlim
    have hb' : Tendsto (fun s => logDeriv (DirichletCharacter.LFunction χ) s - 1 / s)
        (𝓝[≠] 0) (𝓝 b) := by
      simpa only [logDeriv_apply] using hb
    exact tendsto_nhds_unique hb' hlim

/-- The real constant `log(2π/q) + γ` is at most `13 log q` in size once `q ≥ 2`. -/
lemma abs_closed_const_le {q : ℕ} (hq : 2 ≤ q) :
    |Real.log (2 * π / q) + Real.eulerMascheroniConstant| ≤ 13 * Real.log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hl2 := Real.log_two_gt_d9
  have hsplit : Real.log (2 * π / q) = Real.log (2 * π) - Real.log q := by
    rw [Real.log_div (by positivity) hq0.ne']
  have h2pi : Real.log (2 * π) ≤ 2 * π - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2pi0 : 0 ≤ Real.log (2 * π) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hpi := Real.pi_lt_d2
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  rw [hsplit, abs_le]
  constructor <;> nlinarith

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 118, the display
`b(χ) = O(log q) - Σ_{|γ|<1} 1/ρ` after display (8). Exactly the statement of
`CharTrivial1122.b_regroup_leaf`, PROVED. -/
theorem b_regroup : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ b : ℂ,
      ((χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
          DirichletCharacter.LFunction χ 0) ∨
        (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) →
      ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) →
      ‖b + ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
        C * Real.log q := by
  obtain ⟨C, hC, hloc⟩ := local_expansion_one
  refine ⟨13 + C, by linarith, ?_⟩
  intro q _ χ hχ hne b hb Z hZ
  have hq1 : q ≠ 1 := CharTrivial1122.modulus_ne_one hne
  have hq2 : 2 ≤ q := by have := NeZero.ne q; omega
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have hine : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  -- the reflected zero set
  set W : Finset ℂ := Z.image (fun ρ => 1 - ρ) with hWdef
  have hW : ∀ ρ : ℂ, ρ ∈ W ↔ DirichletCharacter.LFunction χ⁻¹ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 := by
    intro ρ'
    rw [hWdef, Finset.mem_image]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      obtain ⟨hz, h0, h1, him⟩ := (hZ ρ).1 hρ
      refine ⟨(zero_reflection χ hχ h0 h1).2 hz, ?_, ?_, ?_⟩
      · simp only [Complex.sub_re, Complex.one_re]; linarith
      · simp only [Complex.sub_re, Complex.one_re]; linarith
      · simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using him
    · rintro ⟨hz, h0, h1, him⟩
      have h0' : 0 < (1 - ρ').re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      have h1' : (1 - ρ').re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
      refine ⟨1 - ρ', (hZ _).2 ⟨?_, h0', h1', ?_⟩, sub_sub_cancel 1 ρ'⟩
      · rw [← zero_reflection χ hχ h0' h1', sub_sub_cancel]; exact hz
      · simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using him
  have hsum : ∑ ρ ∈ W, (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) ρ : ℂ) /
      (1 - ρ) = ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ := by
    rw [hWdef, Finset.sum_image (fun x _ y _ h => by simpa using h)]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    obtain ⟨-, h0, h1, -⟩ := (hZ ρ).1 hρ
    rw [sub_sub_cancel]
    unfold analyticOrderNatAt
    rw [order_reflection χ hχ h0 h1]
  have hloc' := hloc q χ⁻¹ hi hine W hW
  rw [hsum, HelfgottMajor.Conjugate669.logDeriv_inv_one χ hne] at hloc'
  have hbv := b_eq_closed_form χ hχ hne b hb
  rw [logDeriv_apply] at hbv
  set K : ℝ := Real.log (2 * π / q) + Real.eulerMascheroniConstant with hK
  set S : ℂ := ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ
  set D : ℂ := (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
    DirichletCharacter.LFunction χ 1)
  have he : b + S = (K : ℂ) - (D - S) := by rw [hbv]; ring
  have hKn : ‖(K : ℂ)‖ ≤ 13 * Real.log q := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_closed_const_le hq2
  rw [he]
  calc ‖(K : ℂ) - (D - S)‖ ≤ ‖(K : ℂ)‖ + ‖D - S‖ := norm_sub_le _ _
    _ ≤ 13 * Real.log q + C * Real.log q := add_le_add hKn hloc'
    _ = (13 + C) * Real.log q := by ring

end LeanLab.PNTPort.ExplicitPsi1.CharBRegroup1122
