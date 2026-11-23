module

public import LeanLab.HardyLittlewood1923.U1503LogDeriv

/-!
# Landau's expansion of `L'/L(1, ψ)` over the zeros of a disc, Davenport ch. 16 display (4)

ROUTE BURST burst-20261122, session S65, unit bregroup1122. AI wrote the Lean code. Binary
Goldbach is OPEN; nothing here bears on it directly.

Davenport, Multiplicative Number Theory, second edition, ch. 16 p. 102 display (4):
`L'/L(s, χ) = Σ_ρ 1/(s - ρ) + O(log q(|t| + 2))` over the zeros near `s`. Here it is proved in
the disc form of Landau's lemma at `s = 1`, `t = 0`: the zeros `ρ` of `L(s, ψ)` with
`‖ρ - 3/2‖ ≤ 29/25`, counted with multiplicity, for every `ψ ≠ 1` mod `q`. The proof applies the
Borel Caratheodory expansion `FinalBound` of the ported StrongPNT file to
`g(z) = L(3/2 + (29/20) z, ψ)/L(3/2, ψ)`, exactly as `HardyLittlewood1923.U1503.bc_wide` does for
its pointwise bound, and carries the zero sum of `g` back to the zeros of `L(s, ψ)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharDiscExpansion1122

open Complex Set Filter Metric Topology
open LeanLab.HardyLittlewood1923.U1503 (KW KW_pos finite_zeros_of_entire norm_lam)
open LeanLab.PNTPort.DirichletZF (Z Z_pos one_le_Z norm_LFunction_ge norm_LFunction_le)

/-- The affine change of variable `z ↦ 3/2 + (29/20) z`. -/
private lemma phi_deriv (z : ℂ) :
    HasDerivAt (fun z : ℂ => (3 / 2 : ℂ) + (29 / 20 : ℂ) * z) (29 / 20) z := by
  simpa using ((hasDerivAt_id z).const_mul (29 / 20 : ℂ)).const_add (3 / 2 : ℂ)

/-- Davenport ch. 16 p. 102 display (4), disc form at `s = 1`: for `ψ ≠ 1` mod `q`,
`‖L'/L(1, ψ) - Σ_{‖ρ - 3/2‖ ≤ 29/25} m(ρ)/(1 - ρ)‖ ≤ (20/29) KW log(60 q Z)`. -/
theorem disc_expansion_one_explicit {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (V : Finset ℂ) (hV : ∀ ρ : ℂ, ρ ∈ V ↔ DirichletCharacter.LFunction ψ ρ = 0 ∧
      ‖ρ - 3 / 2‖ ≤ 29 / 25) :
    ‖deriv (DirichletCharacter.LFunction ψ) 1 / DirichletCharacter.LFunction ψ 1 -
      ∑ ρ ∈ V, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℂ) / (1 - ρ)‖ ≤
      20 / 29 * KW * Real.log (60 * q * Z) := by
  set f := DirichletCharacter.LFunction ψ with hfdef
  have hf : Differentiable ℂ f := DirichletCharacter.differentiable_LFunction hψ
  set c : ℂ := 3 / 2 with hc
  have hN : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hZ := one_le_Z
  have hZ0 := Z_pos
  have hfc : 1 / Z ≤ ‖f c‖ := by
    have h := norm_LFunction_ge ψ 0
    simpa [hc] using h
  have hfc0 : f c ≠ 0 := by
    intro h; rw [h, norm_zero] at hfc; have : 0 < 1 / Z := by positivity
    linarith
  set φ : ℂ → ℂ := fun z => c + (29 / 20 : ℂ) * z with hφ
  set g : ℂ → ℂ := fun z ↦ f (φ z) / f c with hgdef
  have hlin : Differentiable ℂ φ := (differentiable_const c).add (differentiable_id.const_mul _)
  have hgd : Differentiable ℂ g := (hf.comp hlin).div_const _
  have hgA : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1) := fun z _ ↦ hgd.analyticAt z
  have hg0 : g 0 = 1 := by simp [hgdef, hφ, hfc0]
  have hfin := finite_zeros_of_entire hgd (by rw [hg0]; exact one_ne_zero)
  -- the bound of `g` on the disc of radius `99/100`
  set B := 60 * q * Z with hBdef
  have hB : 1 < B := by
    have : (60 : ℝ) ≤ 60 * q * Z := by nlinarith
    linarith
  have hgB : ∀ z : ℂ, ‖z‖ ≤ 99 / 100 → ‖g z‖ ≤ B := by
    intro z hz
    have hz' : ‖φ z - c‖ ≤ 29 / 20 * (99 / 100) := by
      simp only [hφ, add_sub_cancel_left, norm_mul, norm_lam]
      exact mul_le_mul_of_nonneg_left hz (by norm_num)
    obtain ⟨hre, hnorm⟩ := LeanLab.HardyLittlewood1923.U1503.wide_disc_bounds (t := 0)
      (z := φ z) (by simpa [LeanLab.PNTPort.DirichletZF.U1482.cen, hc] using hz')
    have hre0 : 0 < (φ z).re := by linarith
    have hM : ‖f (φ z)‖ ≤ 60 * q := by
      calc ‖f (φ z)‖ ≤ q * ‖φ z‖ / (φ z).re := norm_LFunction_le hψ hre0
        _ ≤ q * (|(0 : ℝ)| + 3) / (1 / 20) :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnorm (by linarith))
              (by norm_num) hre
        _ = 60 * q := by norm_num; ring
    simp only [hgdef, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.2 hfc0)]
    calc ‖f (φ z)‖ ≤ 60 * q := hM
      _ = B * (1 / Z) := by rw [hBdef]; field_simp
      _ ≤ B * ‖f c‖ := mul_le_mul_of_nonneg_left hfc (by linarith)
  -- the point `z₀` with `φ z₀ = 1`
  set z₀ : ℂ := -(10 / 29) with hz₀def
  have hφz₀ : φ z₀ = 1 := by simp only [hφ, hz₀def, hc]; ring
  have hz₀ : ‖z₀‖ ≤ 7 / 10 := by
    rw [hz₀def, norm_neg]
    have : ‖(10 / 29 : ℂ)‖ = 10 / 29 := by
      rw [show (10 / 29 : ℂ) = ((10 / 29 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [this]; norm_num
  have hf1 : f 1 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (by norm_num)
  have hgz : g z₀ ≠ 0 := by
    simp only [hgdef, hφz₀]; exact div_ne_zero hf1 hfc0
  have hmem : z₀ ∈ closedBall (0 : ℂ) (7 / 10) \ SetOfZeros (9 / 10) g :=
    ⟨mem_closedBall_zero_iff.2 hz₀, fun h ↦ hgz h.2⟩
  have hFB := FinalBound hB (by norm_num : (0 : ℝ) < 7 / 10)
    (by norm_num : (7 / 10 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 1) (by norm_num : (4 / 5 : ℝ) < 9 / 10)
    (by norm_num : (9 / 10 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) < 1) hgA hg0 hfin hgB
    hmem
  set S := (finiteSetOfZeros_mono (by norm_num : (4 / 5 : ℝ) < 1)
    hfin).toFinset with hSdef
  -- the derivative
  have hderiv : deriv g z₀ = (29 / 20 : ℂ) * deriv f 1 / f c := by
    have h2 : HasDerivAt f (deriv f 1) (φ z₀) := by
      rw [hφz₀]; exact (hf 1).hasDerivAt
    have h3 := (h2.comp z₀ (phi_deriv z₀)).div_const (f c)
    exact h3.deriv.trans (by ring)
  have hratio : deriv g z₀ / g z₀ = (29 / 20 : ℂ) * (deriv f 1 / f 1) := by
    rw [hderiv]
    simp only [hgdef, hφz₀]
    field_simp
  -- multiplicities
  have hmult : ∀ ρ : ℂ, analyticOrderNatAt g ρ = analyticOrderNatAt f (φ ρ) := by
    intro ρ
    have he : g = (fun _ => (f c)⁻¹) * (f ∘ φ) := by
      funext z; simp only [hgdef, Pi.mul_apply, Function.comp_apply]; ring
    have hcA : AnalyticAt ℂ (fun _ : ℂ => (f c)⁻¹) ρ := analyticAt_const
    have hcomp : AnalyticAt ℂ (f ∘ φ) ρ := (hf.comp hlin).analyticAt ρ
    have h0 : analyticOrderAt (fun _ : ℂ => (f c)⁻¹) ρ = 0 :=
      hcA.analyticOrderAt_eq_zero.2 (inv_ne_zero hfc0)
    have hd : deriv φ ρ ≠ 0 := by rw [(phi_deriv ρ).deriv]; norm_num
    unfold analyticOrderNatAt
    rw [he, analyticOrderAt_mul hcA hcomp, h0, zero_add,
      analyticOrderAt_comp_of_deriv_ne_zero (hlin.analyticAt ρ) hd]
  -- the zero sets correspond
  have hVS : V = S.image φ := by
    ext w
    rw [hV, Finset.mem_image]
    constructor
    · rintro ⟨hz, hr⟩
      refine ⟨(w - c) / (29 / 20 : ℂ), ?_, ?_⟩
      · rw [hSdef, Set.Finite.mem_toFinset]
        refine ⟨?_, ?_⟩
        · rw [norm_div, norm_lam, div_le_iff₀ (by norm_num)]
          rw [hc]; linarith
        · simp only [hgdef, hφ]
          rw [show c + 29 / 20 * ((w - c) / (29 / 20 : ℂ)) = w by field_simp; ring, hz,
            zero_div]
      · simp only [hφ]; field_simp; ring
    · rintro ⟨ρ, hρ, rfl⟩
      rw [hSdef, Set.Finite.mem_toFinset] at hρ
      obtain ⟨hρn, hgρ⟩ := hρ
      refine ⟨?_, ?_⟩
      · simp only [hgdef, div_eq_zero_iff] at hgρ
        exact hgρ.resolve_right hfc0
      · simp only [hφ, add_sub_cancel_left, norm_mul, norm_lam]
        nlinarith
  have hinj : Set.InjOn φ S := by
    intro x _ y _ h
    simp only [hφ, add_right_inj, mul_eq_mul_left_iff] at h
    exact h.resolve_right (by norm_num)
  have hsum : ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z₀ - ρ) =
      (29 / 20 : ℂ) * ∑ ρ ∈ V, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ) := by
    rw [hVS, Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hmult ρ]
    have e : (1 : ℂ) - φ ρ = (29 / 20 : ℂ) * (z₀ - ρ) := by
      rw [← hφz₀]; simp only [hφ]; ring
    rw [e]
    by_cases h : z₀ - ρ = 0
    · simp [h]
    · field_simp
  have hFB' : ‖(29 / 20 : ℂ) * (deriv f 1 / f 1 -
      ∑ ρ ∈ V, (analyticOrderNatAt f ρ : ℂ) / (1 - ρ))‖ ≤ KW * Real.log B := by
    rw [mul_sub, ← hratio, ← hsum]
    simpa [KW] using hFB
  rw [norm_mul, norm_lam] at hFB'
  have : 0 ≤ KW * Real.log B := mul_nonneg KW_pos.le (Real.log_nonneg hB.le)
  rw [show 20 / 29 * KW * Real.log (60 * q * Z) = 20 / 29 * (KW * Real.log B) by
    rw [hBdef]; ring]
  linarith

/-- Davenport ch. 16 p. 102 display (4), disc form at `s = 1`, in the shape of
`CharBRegroup1122.disc_expansion_one_leaf`: the error is `O(log q)` for primitive `ψ ≠ 1`. -/
theorem disc_expansion_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (ψ : DirichletCharacter ℂ q), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ V : Finset ℂ, (∀ ρ : ℂ, ρ ∈ V ↔ DirichletCharacter.LFunction ψ ρ = 0 ∧
        ‖ρ - 3 / 2‖ ≤ 29 / 25) →
      ‖deriv (DirichletCharacter.LFunction ψ) 1 / DirichletCharacter.LFunction ψ 1 -
        ∑ ρ ∈ V, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℂ) / (1 - ρ)‖ ≤
        C * Real.log q := by
  have hZ := one_le_Z
  have hK := KW_pos
  have hl2 := Real.log_two_gt_d9
  set E := Real.log (60 * Z) with hE
  have hE0 : 0 ≤ E := Real.log_nonneg (by nlinarith)
  refine ⟨20 / 29 * KW * (E / Real.log 2 + 1), by positivity, ?_⟩
  intro q _ ψ _ hne V hV
  have h := disc_expansion_one_explicit ψ hne V hV
  have hq2 : 2 ≤ q := by
    have h1 : q ≠ 1 := fun h => hne (by subst h; exact DirichletCharacter.level_one' ψ rfl)
    have := NeZero.ne q
    omega
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2'
  have hsplit : Real.log (60 * q * Z) = E + Real.log q := by
    rw [hE, show (60 : ℝ) * q * Z = 60 * Z * q by ring,
      Real.log_mul (by positivity) (by positivity)]
  have hEle : E ≤ E / Real.log 2 * Real.log q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left hlogq hE0
  refine h.trans ?_
  rw [hsplit]
  have hc : 0 ≤ 20 / 29 * KW := by positivity
  calc 20 / 29 * KW * (E + Real.log q) ≤ 20 / 29 * KW * (E / Real.log 2 * Real.log q +
        Real.log q) := mul_le_mul_of_nonneg_left (by linarith) hc
    _ = _ := by ring

end LeanLab.PNTPort.ExplicitPsi1.CharDiscExpansion1122
