module

public import LeanLab.Linnik.ExplicitFormula.Defs
public import LeanLab.Linnik.Decomp1532b
public import LeanLab.PNTPort.DirichletZF.Exceptional

/-!
# The zero sum after the explicit formula, Gallagher 1975 p.131 display 14

AI wrote the Lean code. Binary Goldbach is OPEN.
`Σ_{q ≤ P} Σ*_χ Σ_ρ m(ρ) x^(β-1) ≪ e^(-c/θ)` for `x ≥ N/P^8`, `P = N^θ`, over zeros up to height
`P^10`, given the zero gap `1 - β ≥ b/log P^5` up to height `P^5`. Inputs: the lab's log free
density `LeanLab.Linnik.Decomp1532b.gallagher_density` counting distinct zeros, the local
multiplicity bound `primitive_local_zero_order_sum`, which turns multiplicity into the factor
`(1 - β) log T + 1`, the unit window count `LeanLab.HardyLittlewood1923.U1482.zeroCountUnit` for
`β < 7/8`, and the classical region `LeanLab.PNTPort.DirichletZF.zero_free_region_all` above
height `P^5`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- The hypothesis on the zero sets in `zero_sum_density_layer`, Gallagher 1975 p.131: zeros of
`L(s, χ)` in the strip, up to height `P^10`, with the gap `b / log P^5` up to height `P^5`. -/
def ZeroSetHyp (b θ : ℝ) (N : ℕ) (S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ) : Prop :=
  ∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
    |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 10 ∧
    (|ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 → ρ.re < 1 - b / Real.log (((N : ℝ) ^ θ) ^ 5))

/-- The zero sum of display 14 restricted to the zeros whose real part satisfies `p`. -/
noncomputable def zsumP (p : ℝ → Prop) [DecidablePred p] (θ : ℝ) (N : ℕ)
    (S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ) : ℝ :=
  ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
      ∑ ρ ∈ (S k χ).filter (fun ρ => p ρ.re),
        (mult χ ρ : ℝ) * ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (ρ.re - 1)

/-- The zero gap `1 - β ≥ a / log P` for every zero in the sum, Gallagher 1975 p.131: below height
`P^5` it is the hypothesis, above it the classical region `zero_free_region_all` for `q > 1`, whose
exceptional branch sits at height `O(1)`, and `zeta_height_box_nonzero` for `q = 1`. -/
lemma gap_all (b : ℝ) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ θ : ℝ, 0 < θ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ, ZeroSetHyp b θ N S →
      ∀ k ∈ range ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
      ∀ ρ ∈ S k χ, a / Real.log ((N : ℝ) ^ θ) ≤ 1 - ρ.re := by
  open LeanLab.PNTPort.DirichletZF in
  obtain ⟨c, c', hc, hc', hzf⟩ := zero_free_region_all
  obtain ⟨bz, hbz, hzeta⟩ := LeanLab.Linnik.Decomp1532b.zeta_height_box_nonzero
  have hZ1 := LeanLab.PNTPort.DirichletZF.one_le_Z
  set Z := LeanLab.PNTPort.DirichletZF.Z with hZ
  refine ⟨min (b / 5) (min (bz / 10) (c / 12)), by positivity, fun θ hθ => ?_⟩
  set a := min (b / 5) (min (bz / 10) (c / 12)) with ha
  set M : ℝ := 8 * Z + c' + 3 with hM
  have hM1 : 1 ≤ M := by linarith
  refine ⟨⌈M ^ (1 / θ)⌉₊, fun N hN S hS k hk χ hχ ρ hρ => ?_⟩
  set n : ℝ := (N : ℝ) with hn
  have hnM : M ^ (1 / θ) ≤ n := (Nat.le_ceil _).trans (by rw [hn]; exact_mod_cast hN)
  have hM0 : 0 ≤ M := by linarith
  set P : ℝ := n ^ θ with hP
  have hPM : M ≤ P := by
    calc M = (M ^ (1 / θ)) ^ θ := by
          rw [← Real.rpow_mul hM0, one_div, inv_mul_cancel₀ hθ.ne', Real.rpow_one]
      _ ≤ P := Real.rpow_le_rpow (by positivity) hnM hθ.le
  have hP3 : 3 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  set L : ℝ := Real.log P with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  obtain ⟨hL0ρ, hre0, hre1, hT, hlow⟩ := hS k χ ρ hρ
  have haL : ∀ d : ℝ, a ≤ d → ∀ D : ℝ, 0 < D → D ≤ L → ρ.re ≤ 1 - d / D → a / L ≤ 1 - ρ.re := by
    intro d hd D hD hDL hre
    have h1 : a / L ≤ d / D := by
      have ha0 : 0 ≤ a := by positivity
      calc a / L ≤ a / D := div_le_div_of_nonneg_left ha0 hD hDL
        _ ≤ d / D := div_le_div_of_nonneg_right hd hD.le
    linarith
  by_cases him : |ρ.im| ≤ P ^ 5
  · have h := hlow him
    rw [Real.log_pow] at h
    have : a / L ≤ b / 5 / L := div_le_div_of_nonneg_right (min_le_left _ _) hL0.le
    have e : b / ((5 : ℕ) * L) = b / 5 / L := by push_cast; field_simp
    rw [e] at h
    linarith
  · push_neg at him
    have hP5 : 3 ≤ P ^ 5 := le_trans hP3 (le_self_pow₀ (by linarith) (by norm_num))
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hz : riemannZeta ρ = 0 := by
        rw [← DirichletCharacter.LFunction_modOne_eq (χ := χ)]; exact hL0ρ
      have hT2 : (2 : ℝ) ≤ P ^ 10 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num) : P ≤ P ^ 10)
      have hre : ρ.re < 1 - bz / Real.log (P ^ 10) := by
        by_contra hcon
        exact hzeta hT2 ρ (not_lt.mp hcon) hT hz
      rw [Real.log_pow] at hre
      push_cast at hre
      have e : bz / (10 * L) = (bz / 10) / L := by field_simp
      rw [e] at hre
      have : a / L ≤ bz / 10 / L :=
        div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hL0.le
      linarith
    · have hχ1 : χ ≠ 1 := by
        intro h1
        have := hχ
        rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at this
        omega
      rcases (hzf (k + 1) χ hχ1).1 ρ hL0ρ with hcl | hexc
      · -- classical region
        have hBt : Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) ρ.im) ≤ 12 * L := by
          unfold LeanLab.PNTPort.DirichletZF.Bt
          have hkP : ((k + 1 : ℕ) : ℝ) ≤ P := by
            have h1 : k + 1 ≤ ⌊P⌋₊ := Finset.mem_range.mp hk
            have h2 : ((k + 1 : ℕ) : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast h1
            exact h2.trans (Nat.floor_le (by linarith))
          have hP10 : |ρ.im| + 3 ≤ 2 * P ^ 10 := by
            have : 3 ≤ P ^ 10 := le_trans hP3 (le_self_pow₀ (by linarith) (by norm_num))
            linarith
          have hpos : 0 < 2 * (((k + 1 : ℕ) : ℝ)) * (|ρ.im| + 3) * Z := by positivity
          have hle : 2 * (((k + 1 : ℕ) : ℝ)) * (|ρ.im| + 3) * Z ≤ P ^ 12 := by
            have hZP : 8 * Z ≤ P := by linarith
            have h1 : 2 * (((k + 1 : ℕ) : ℝ)) * (|ρ.im| + 3) * Z ≤ 2 * P * (2 * P ^ 10) * Z := by
              gcongr
            have h2 : 2 * P * (2 * P ^ 10) * Z = P ^ 11 * (4 * Z) := by ring
            have h3 : P ^ 11 * (4 * Z) ≤ P ^ 11 * P := by
              gcongr; linarith
            calc _ ≤ _ := h1
              _ = _ := h2
              _ ≤ P ^ 11 * P := h3
              _ = P ^ 12 := by ring
          have := Real.log_le_log hpos hle
          rw [Real.log_pow] at this
          push_cast at this ⊢
          linarith
        have hBt0 : 0 < Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) ρ.im) :=
          Real.log_pos (LeanLab.PNTPort.DirichletZF.one_lt_Bt _)
        have hre : ρ.re ≤ 1 - (c / 12) / (Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) ρ.im) / 12) := by
          have e : (c / 12) / (Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) ρ.im) / 12) =
              c / Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) ρ.im) := by field_simp
          rw [e]; exact hcl
        exact haL (c / 12) ((min_le_right _ _).trans (min_le_right _ _)) _ (by positivity)
          (by linarith) hre
      · -- exceptional branch, at bounded height
        exfalso
        have hB : 1 ≤ Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) 0) := by
          unfold LeanLab.PNTPort.DirichletZF.Bt
          rw [← Real.log_exp 1]
          refine Real.log_le_log (Real.exp_pos 1) ?_
          have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
          push_cast at this ⊢
          simp only [abs_zero, zero_add]
          nlinarith [Real.exp_one_lt_d9]
        have h1 : c' / Real.log (LeanLab.PNTPort.DirichletZF.Bt (k + 1) 0) ≤ c' :=
          div_le_self hc'.le hB
        have h2 := hexc.2
        have h3 : P ≤ P ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
        have h4 : 0 ≤ Z := by linarith
        linarith

/-- The local multiplicity bound `m(ρ) ≤ C ((1 - β) log T + 1)` for `7/8 ≤ β < 1`, Gallagher 1975
p.131: `primitive_local_zero_order_sum` on the disc of radius `max (1 - β) (1 / log T)` about
`1 + iγ`; for `q = 1` and `|γ| < 2` the window bound `zeroCountUnit` gives an absolute constant. -/
lemma mult_local : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ T : ℝ, Real.exp 8 ≤ T → ∀ (q : ℕ) [NeZero q],
    (q : ℝ) ≤ T → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ ρ : ℂ, χ.LFunction ρ = 0 →
    7 / 8 ≤ ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
    (mult χ ρ : ℝ) ≤ C₁ * ((1 - ρ.re) * Real.log T + 1) := by
  classical
  obtain ⟨C, hC, hloc⟩ := LeanLab.Linnik.Decomp1532b.primitive_local_zero_order_sum
  obtain ⟨A, hA, hz⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨C + A * Real.log 3, by positivity, fun T hT q _ hqT χ hχ ρ hρ h78 hre1 hTρ => ?_⟩
  have hlogT : 8 ≤ Real.log T := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hT
  have hlT0 : 0 < Real.log T := by linarith
  have hu0 : 0 ≤ 1 - ρ.re := by linarith
  have hfac : 1 ≤ (1 - ρ.re) * Real.log T + 1 := by
    have := mul_nonneg hu0 hlT0.le; linarith
  by_cases hcase : χ = 1 ∧ |ρ.im| < 2
  · -- the low height zeros of `ζ`: a bounded window count
    obtain ⟨h1, hlow⟩ := hcase
    have hq1 : q = 1 := by
      have := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at this
      exact this.symm
    set t : ℝ := (⌊|ρ.im|⌋₊ : ℝ) with ht
    have ht0 : 0 ≤ t := Nat.cast_nonneg _
    have htle : t ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have htlt : |ρ.im| ≤ t + 1 := (Nat.lt_floor_add_one _).le
    have h := (hz q χ hχ t ht0).2 {ρ} (fun ρ' hρ' => by
      rw [Finset.mem_singleton] at hρ'
      subst hρ'
      exact ⟨⟨hρ, by linarith, hre1⟩, htle, htlt⟩)
    rw [Finset.sum_singleton] at h
    have hmA : (mult χ ρ : ℝ) ≤ A * Real.log 3 := by
      refine (le_of_eq_of_le rfl h).trans (mul_le_mul_of_nonneg_left ?_ hA)
      rw [hq1]
      push_cast
      refine Real.log_le_log (by linarith) ?_
      have : t < 2 := lt_of_le_of_lt htle hlow
      have : t ≤ 1 := by
        have hfl : ⌊|ρ.im|⌋₊ < 2 := by
          rw [Nat.floor_lt (abs_nonneg _)]; exact_mod_cast hlow
        rw [ht]; exact_mod_cast Nat.lt_succ_iff.mp hfl
      linarith
    have := mul_le_mul_of_nonneg_left hfac (by positivity : (0 : ℝ) ≤ A * Real.log 3)
    have h2 : 0 ≤ C * ((1 - ρ.re) * Real.log T + 1) := by positivity
    nlinarith
  · have hχt : χ = 1 → 2 ≤ |ρ.im| := by
      intro h1; by_contra hc; exact hcase ⟨h1, lt_of_not_ge hc⟩
    set r : ℝ := max (1 - ρ.re) (1 / Real.log T) with hr
    have hr_lo : 1 / Real.log T ≤ r := le_max_right _ _
    have hr_hi : r ≤ 1 / 8 := by
      refine max_le (by linarith) ?_
      rw [div_le_div_iff₀ hlT0 (by norm_num)]; linarith
    have hT2 : 2 ≤ T := le_trans (by linarith [Real.add_one_le_exp (8 : ℝ)]) hT
    have hdist : ‖ρ - (1 + Complex.I * (ρ.im : ℂ))‖ ≤ r := by
      have e : ρ - (1 + Complex.I * (ρ.im : ℂ)) = ((ρ.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      exact le_trans (by linarith) (le_max_left _ _)
    have h := hloc T hT2 q hqT χ hχ ρ.im r hTρ hχt hr_lo hr_hi {ρ} (fun ρ' hρ' => by
      rw [Finset.mem_singleton] at hρ'; subst hρ'; exact ⟨hρ, hdist⟩)
    rw [Finset.sum_singleton] at h
    have hrl : r * Real.log T ≤ (1 - ρ.re) * Real.log T + 1 := by
      have : r ≤ (1 - ρ.re) + 1 / Real.log T :=
        max_le (by have : 0 ≤ 1 / Real.log T := by positivity
                   linarith) (by linarith)
      have := mul_le_mul_of_nonneg_right this hlT0.le
      rw [add_mul, one_div, inv_mul_cancel₀ hlT0.ne'] at this
      exact this
    have h3 : (mult χ ρ : ℝ) ≤ C * ((1 - ρ.re) * Real.log T + 1) := by
      refine (le_of_eq_of_le rfl h).trans ?_
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hrl hC
    have h4 : 0 ≤ A * Real.log 3 * ((1 - ρ.re) * Real.log T + 1) := by positivity
    nlinarith

/-- A zero of a primitive `L(s, χ)` has `Re ρ < 1`: Mathlib's `LFunction_ne_zero_of_one_le_re`, and
`riemannZeta_one_ne_zero` for the junk value at the pole of `ζ`. -/
lemma dl_re_lt_one_of_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : χ.LFunction ρ = 0) : ρ.re < 1 := by
  by_contra h
  push_neg at h
  by_cases hc : χ ≠ 1 ∨ ρ ≠ 1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hc h hρ
  · push_neg at hc
    obtain ⟨h1, hr1⟩ := hc
    have hq1 : q = 1 := by
      have := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at this
      exact this.symm
    subst hq1 hr1
    rw [DirichletCharacter.LFunction_modOne_eq] at hρ
    exact riemannZeta_one_ne_zero hρ

/-- Finiteness of the zeros with `σ ≤ Re ρ`, `|Im ρ| ≤ T`, `σ > 0`, for primitive `χ`: a finite
union of the unit windows of `zeroCountUnit`. -/
lemma zeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite := by
  obtain ⟨A, -, hz⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  refine Set.Finite.subset ((Finset.range (⌊T⌋₊ + 1)).finite_toSet.biUnion
    fun j _ => (hz q χ hχ (j : ℝ) (Nat.cast_nonneg j)).1) ?_
  intro ρ hρ
  obtain ⟨h0, h1, h2⟩ := hρ
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
  refine ⟨⌊|ρ.im|⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor h2),
    ⟨h0, by linarith, dl_re_lt_one_of_zero χ hχ h0⟩, Nat.floor_le (abs_nonneg _),
    (Nat.lt_floor_add_one _).le⟩

/-- The distinct zero count with `7/8 ≤ β`, `1 - β < v`, summed over primitive characters of
modulus at most `T`: Gallagher's log free density `gallagher_density` at
`σ = max (1 - v) (7/8)`. -/
lemma distinct_count : ∃ c₃ C₃ : ℝ, 0 ≤ c₃ ∧ 0 ≤ C₃ ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ,
    (∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ |ρ.im| ≤ T) → ∀ v : ℝ, 0 ≤ v →
    ∑ k ∈ range ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (((S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v)).card : ℝ)
      ≤ C₃ * Real.exp (c₃ * (v * Real.log T)) := by
  classical
  obtain ⟨c, C, hc, hden⟩ := LeanLab.Linnik.Decomp1532b.gallagher_density
  refine ⟨c, max C 0, hc.le, le_max_right _ _, fun T hT S hS v hv => ?_⟩
  set σ : ℝ := max (1 - v) (7 / 8) with hσ
  have hσ1 : σ ≤ 1 := max_le (by linarith) (by norm_num)
  have hσ2 : 1 / 2 ≤ σ := le_trans (by norm_num) (le_max_right _ _)
  have hcard : ∀ k, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
      (((S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v)).card : ℝ) ≤
        (LeanLab.Linnik.Decomp1532b.zeroCount χ σ T : ℝ) := by
    intro k χ hχ
    unfold LeanLab.Linnik.Decomp1532b.zeroCount
    rw [← Set.ncard_coe_finset]
    refine Nat.cast_le.mpr (Set.ncard_le_ncard ?_ (zeros_finite χ hχ (by linarith) (by linarith)))
    intro ρ hρ
    rw [Finset.coe_filter] at hρ
    obtain ⟨hρS, h78, hv'⟩ := hρ
    obtain ⟨hz, hT'⟩ := hS k χ ρ hρS
    exact ⟨hz, max_le (by linarith) h78, hT'⟩
  have hsum := hden T hT σ hσ2 hσ1
  have hstep : ∑ k ∈ range ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (((S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v)).card : ℝ) ≤
      ∑ k ∈ range ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (LeanLab.Linnik.Decomp1532b.zeroCount χ σ T : ℝ) :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun χ hχ =>
      hcard k χ (Finset.mem_filter.mp hχ).2
  refine hstep.trans (hsum.trans ?_)
  have hT0 : 0 < T := by linarith
  have hpow : T ^ (c * (1 - σ)) ≤ Real.exp (c * (v * Real.log T)) := by
    rw [Real.rpow_def_of_pos hT0]
    refine Real.exp_le_exp.mpr ?_
    have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h1σ : 1 - σ ≤ v := by have := le_max_left (1 - v) (7 / 8); linarith
    have := mul_le_mul_of_nonneg_left h1σ hc.le
    nlinarith
  have hp0 : 0 ≤ T ^ (c * (1 - σ)) := Real.rpow_nonneg hT0.le _
  calc C * T ^ (c * (1 - σ)) ≤ max C 0 * T ^ (c * (1 - σ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
    _ ≤ max C 0 * Real.exp (c * (v * Real.log T)) :=
        mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

/-- The multiplicity weighted count of zeros with `7/8 ≤ β`, `1 - β < v`: Gallagher's log free
density `gallagher_density` bounds the distinct zeros by `C T^(c v)`, `T = P^10`, and
`primitive_local_zero_order_sum` bounds each multiplicity by `C (v log T + 1)`; for `q = 1` the
zeros near `1` at height below `2` are excluded by `zeta_height_box_nonzero`. -/
lemma weighted_count (b : ℝ) (hb : 0 < b) :
    ∃ c₂ C₂ : ℝ, 0 ≤ c₂ ∧ 0 ≤ C₂ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 16 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ, ZeroSetHyp b θ N S →
      ∀ v : ℝ, 0 ≤ v →
      ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v), (mult χ ρ : ℝ)
        ≤ C₂ * (v * Real.log ((N : ℝ) ^ θ) + 1) * Real.exp (c₂ * (v * Real.log ((N : ℝ) ^ θ))) := by
  obtain ⟨C₁, hC₁, hloc⟩ := mult_local
  obtain ⟨c₃, C₃, hc₃, hC₃, hcnt⟩ := distinct_count
  refine ⟨10 * c₃, 10 * C₁ * C₃, by positivity, by positivity, fun θ hθ _ => ?_⟩
  refine ⟨⌈(Real.exp 1) ^ (1 / θ)⌉₊, fun N hN S hS v hv => ?_⟩
  set n : ℝ := (N : ℝ) with hn
  have hnM : (Real.exp 1) ^ (1 / θ) ≤ n := (Nat.le_ceil _).trans (by rw [hn]; exact_mod_cast hN)
  set P : ℝ := n ^ θ with hP
  have hPe : Real.exp 1 ≤ P := by
    calc Real.exp 1 = ((Real.exp 1) ^ (1 / θ)) ^ θ := by
          rw [← Real.rpow_mul (Real.exp_pos 1).le, one_div, inv_mul_cancel₀ hθ.ne', Real.rpow_one]
      _ ≤ P := Real.rpow_le_rpow (by positivity) hnM hθ.le
  have hP1 : 1 ≤ P := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hPe
  have hP0 : 0 < P := by linarith
  set L : ℝ := Real.log P with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hPe
  set T : ℝ := P ^ 10 with hT
  have hlogT : Real.log T = 10 * L := by rw [hT, Real.log_pow]; push_cast; ring
  have hPT : P ≤ T := le_self_pow₀ hP1 (by norm_num)
  have hT8 : Real.exp 8 ≤ T := by
    have : Real.exp 8 = (Real.exp 1) ^ 10 * Real.exp (-2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [this, hT]
    have h1 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have h2 : (Real.exp 1) ^ 10 ≤ P ^ 10 := pow_le_pow_left₀ (Real.exp_pos 1).le hPe 10
    nlinarith [pow_pos (Real.exp_pos 1) 10]
  have hT2 : 2 ≤ T := le_trans (by linarith [Real.add_one_le_exp (8 : ℝ)]) hT8
  -- each multiplicity is at most `C₁ (10 v L + 1)`
  have hm : ∀ k ∈ range ⌊P⌋₊, ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
      (fun χ => χ.IsPrimitive), ∀ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v),
      (mult χ ρ : ℝ) ≤ C₁ * (v * (10 * L) + 1) := by
    intro k hk χ hχ ρ hρ
    obtain ⟨hρS, h78, hv'⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, -, hre1, hTρ, -⟩ := hS k χ ρ hρS
    have hkP : ((k + 1 : ℕ) : ℝ) ≤ P := by
      have h1 : k + 1 ≤ ⌊P⌋₊ := Finset.mem_range.mp hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le (by linarith))
    have h := hloc T hT8 (k + 1) (hkP.trans hPT) χ (Finset.mem_filter.mp hχ).2 ρ hz h78 hre1 hTρ
    rw [hlogT] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
    have : 0 ≤ 10 * L := by linarith
    nlinarith
  have hS' : ∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ |ρ.im| ≤ T :=
    fun k χ ρ hρ => ⟨(hS k χ ρ hρ).1, (hS k χ ρ hρ).2.2.2.1⟩
  have hc := hcnt T hT2 S hS' v hv
  rw [hlogT] at hc
  have hsub : range ⌊P⌋₊ ⊆ range ⌊T⌋₊ :=
    Finset.range_subset_range.mpr (Nat.floor_le_floor hPT)
  have hstep : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v), (mult χ ρ : ℝ)
      ≤ C₁ * (v * (10 * L) + 1) * ∑ k ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          (((S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v)).card : ℝ) := by
    set A : ℝ := C₁ * (v * (10 * L) + 1) with hAdef
    have hA0 : 0 ≤ A := by positivity
    set g : ℕ → ℝ := fun k => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
      (fun χ => χ.IsPrimitive),
        (((S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v)).card : ℝ) with hg
    have hg0 : ∀ k, 0 ≤ g k := fun k => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hin : ∀ k ∈ range ⌊P⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < v), (mult χ ρ : ℝ)
        ≤ A * g k := by
      intro k hk
      rw [hg]
      dsimp only
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun χ hχ => ?_
      refine (Finset.sum_le_sum fun ρ hρ => hm k hk χ hχ ρ hρ).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have h2 : ∑ k ∈ range ⌊P⌋₊, A * g k ≤ ∑ k ∈ range ⌊T⌋₊, A * g k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => mul_nonneg hA0 (hg0 k)
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hin).trans h2
  refine hstep.trans ?_
  have hA : 0 ≤ C₁ * (v * (10 * L) + 1) := by positivity
  refine (mul_le_mul_of_nonneg_left hc hA).trans ?_
  have hvL : 0 ≤ v * L := by positivity
  have e : c₃ * (v * (10 * L)) = 10 * c₃ * (v * L) := by ring
  rw [e]
  have hE : 0 ≤ Real.exp (10 * c₃ * (v * L)) := (Real.exp_pos _).le
  have : C₁ * (v * (10 * L) + 1) * C₃ ≤ 10 * C₁ * C₃ * (v * L + 1) := by
    have := mul_nonneg hC₁ hC₃
    nlinarith
  nlinarith

/-- Pointwise layer cake inequality: `e^(-λ u)` is at most the sum over layers `j < J` whose upper
end exceeds `u` of `e^(-λ (u₀ + j h))`. Elementary. -/
lemma layer_point (u u₀ h lam : ℝ) (J : ℕ) (hh : 0 < h) (hlam : 0 ≤ lam) (hu₀ : u₀ ≤ u)
    (huJ : u < u₀ + J * h) :
    Real.exp (-(lam * u)) ≤ ∑ j ∈ range J,
      if u < u₀ + (j + 1) * h then Real.exp (-(lam * (u₀ + j * h))) else 0 := by
  set j0 : ℕ := ⌊(u - u₀) / h⌋₊ with hj0
  have hq0 : 0 ≤ (u - u₀) / h := div_nonneg (by linarith) hh.le
  have hlo : (j0 : ℝ) * h ≤ u - u₀ := by
    have := Nat.floor_le hq0
    rwa [le_div_iff₀ hh] at this
  have hhi : u - u₀ < ((j0 : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one ((u - u₀) / h)
    rwa [div_lt_iff₀ hh] at this
  have hjJ : j0 < J := by
    have h1 : (j0 : ℝ) * h < J * h := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right h1 hh.le
  have hterm : Real.exp (-(lam * u)) ≤
      (if u < u₀ + (j0 + 1) * h then Real.exp (-(lam * (u₀ + j0 * h))) else 0) := by
    rw [if_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  refine hterm.trans ?_
  refine Finset.single_le_sum (f := fun j : ℕ =>
    if u < u₀ + (j + 1) * h then Real.exp (-(lam * (u₀ + j * h))) else 0)
    (fun j _ => by positivity) (Finset.mem_range.mpr hjJ)

/-- The series in the layer cake sum, Gallagher 1975 p.131: with `Λ = 1/θ - 8` large the layers
decay geometrically. Elementary. -/
lemma series_bound (a c₂ C₂ : ℝ) (ha : 0 < a) (hc₂ : 0 ≤ c₂) (hC₂ : 0 ≤ C₂) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ J : ℕ,
      ∑ j ∈ range J, Real.exp (-((1 / θ - 8) * (a + j))) *
        (C₂ * ((a + j + 1) + 1) * Real.exp (c₂ * (a + j + 1)))
        ≤ C * Real.exp (-a / θ) := by
  set K : ℝ := C₂ * (a + 2) * Real.exp (c₂ * (a + 1) + 8 * a) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K + 1, 1 / (10 + c₂), by positivity, by positivity, fun θ hθ hθle J => ?_⟩
  set t : ℝ := 1 / θ with ht
  have ht10 : 10 + c₂ ≤ t := by
    rw [ht, le_div_iff₀ hθ]
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 10 + c₂)).mp hθle
    linarith
  have hat : -a / θ = -(a * t) := by rw [ht]; ring
  set r : ℝ := Real.exp (-1) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hr2 : r ≤ 1 / 2 := by
    rw [hr, Real.exp_neg, one_div]
    refine inv_anti₀ (by norm_num) ?_
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hterm : ∀ j : ℕ, Real.exp (-((1 / θ - 8) * (a + j))) *
      (C₂ * ((a + j + 1) + 1) * Real.exp (c₂ * (a + j + 1))) ≤
      K * Real.exp (-a / θ) * r ^ j := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hpoly : a + j + 1 + 1 ≤ (a + 2) * Real.exp j := by
      have := Real.add_one_le_exp (j : ℝ)
      nlinarith
    have hrj : r ^ j = Real.exp (-(j : ℝ)) := by
      rw [hr, ← Real.exp_nat_mul]; ring_nf
    rw [hrj, hat, hK, ← ht]
    have hexp : (j : ℝ) + (c₂ * (a + j + 1) + -((t - 8) * (a + j))) ≤
        c₂ * (a + 1) + 8 * a + -(a * t) + -(j : ℝ) := by
      nlinarith
    calc Real.exp (-((t - 8) * (a + j))) * (C₂ * ((a + j + 1) + 1) * Real.exp (c₂ * (a + j + 1)))
        ≤ Real.exp (-((t - 8) * (a + j))) * (C₂ * ((a + 2) * Real.exp j) *
            Real.exp (c₂ * (a + j + 1))) := by gcongr
      _ = C₂ * (a + 2) * Real.exp ((j : ℝ) + (c₂ * (a + j + 1) + -((t - 8) * (a + j)))) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ C₂ * (a + 2) * Real.exp (c₂ * (a + 1) + 8 * a + -(a * t) + -(j : ℝ)) := by gcongr
      _ = C₂ * (a + 2) * Real.exp (c₂ * (a + 1) + 8 * a) * Real.exp (-(a * t)) *
            Real.exp (-(j : ℝ)) := by
          rw [Real.exp_add, Real.exp_add]; ring
  have hgeom : ∑ j ∈ range J, r ^ j ≤ 2 := by
    rw [Finset.range_eq_Ico]
    refine (geom_sum_Ico_le_of_lt_one hr0 hr1).trans ?_
    rw [pow_zero, div_le_iff₀ (by linarith)]
    linarith
  have he0 : 0 ≤ Real.exp (-a / θ) := (Real.exp_pos _).le
  calc ∑ j ∈ range J, Real.exp (-((1 / θ - 8) * (a + j))) *
        (C₂ * ((a + j + 1) + 1) * Real.exp (c₂ * (a + j + 1)))
      ≤ ∑ j ∈ range J, K * Real.exp (-a / θ) * r ^ j := Finset.sum_le_sum fun j _ => hterm j
    _ = K * Real.exp (-a / θ) * ∑ j ∈ range J, r ^ j := by rw [Finset.mul_sum]
    _ ≤ K * Real.exp (-a / θ) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ (2 * K + 1) * Real.exp (-a / θ) := by nlinarith

/-- Gallagher 1975 p.131 display 14, the part from zeros with `β ≥ 7/8`. Route: the local
multiplicity bound `primitive_local_zero_order_sum` gives `m(ρ) ≪ (1 - β) log T + 1`, the gap
`1 - β ≫ 1 / log P` comes from the hypothesis below height `P^5` and from
`zero_free_region_all` above it, and a layer cake sum against `gallagher_density`. -/
theorem zero_sum_high (b : ℝ) (hb : 0 < b) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ, ZeroSetHyp b θ N S →
        zsumP (fun β => 7 / 8 ≤ β) θ N S ≤ C * Real.exp (-c / θ) := by
  obtain ⟨a, ha, hgap⟩ := gap_all b hb
  obtain ⟨c₂, C₂, hc₂, hC₂, hwc⟩ := weighted_count b hb
  obtain ⟨C, θ₁, hC, hθ₁, hser⟩ := series_bound a c₂ C₂ ha hc₂ hC₂
  refine ⟨a, C, min θ₁ (1 / 16), ha, hC, lt_min hθ₁ (by norm_num), fun θ hθ hθle => ?_⟩
  have hθ16 : θ ≤ 1 / 16 := hθle.trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hgap θ hθ
  obtain ⟨N₂, hN₂⟩ := hwc θ hθ hθ16
  refine ⟨max (max N₁ N₂) 2, fun N hN S hS => ?_⟩
  have hNg := hN₁ N (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)) S hS
  have hNw := hN₂ N (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)) S hS
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  set n : ℝ := (N : ℝ) with hn
  have hn0 : 0 < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  set P : ℝ := n ^ θ with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hn0 _
  have hLdef : Real.log P = θ * Real.log n := Real.log_rpow hn0 θ
  set L : ℝ := Real.log P with hL
  have hL0 : 0 < L := by rw [hLdef]; positivity
  set x : ℝ := n / P ^ 8 with hx
  have hx0 : 0 < x := by positivity
  have hlx : Real.log x = (1 - 8 * θ) * Real.log n := by
    rw [hx, Real.log_div hn0.ne' (by positivity), Real.log_pow,
      show Real.log P = θ * Real.log n from Real.log_rpow hn0 θ]; push_cast; ring
  set lx : ℝ := Real.log x with hlxdef
  have hlx0 : 0 ≤ lx := by rw [hlx]; nlinarith
  have hΛ : lx / L = 1 / θ - 8 := by
    rw [hlx, hLdef]; field_simp
  set J : ℕ := ⌊L⌋₊ + 1 with hJ
  have hJL : L < J := by rw [hJ]; push_cast; exact Nat.lt_floor_add_one L
  -- the pointwise layer bound on each term
  have hterm : ∀ k ∈ range ⌊P⌋₊, ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
      (fun χ => χ.IsPrimitive), ∀ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re),
      (mult χ ρ : ℝ) * x ^ (ρ.re - 1) ≤ ∑ j ∈ range J,
        if 1 - ρ.re < a / L + (j + 1) * (1 / L)
        then (mult χ ρ : ℝ) * Real.exp (-(lx * (a / L + j * (1 / L)))) else 0 := by
    intro k hk χ hχ ρ hρ
    have hρS := (Finset.mem_filter.mp hρ).1
    have hρ78 := (Finset.mem_filter.mp hρ).2
    have hu0 : a / L ≤ 1 - ρ.re := hNg k hk χ (Finset.mem_filter.mp hχ).2 ρ hρS
    have huJ : 1 - ρ.re < a / L + J * (1 / L) := by
      have h1 : 1 < J * (1 / L) := by rw [mul_one_div, lt_div_iff₀ hL0]; linarith
      have h2 : 0 < a / L := div_pos ha hL0
      linarith
    have hlp := layer_point (1 - ρ.re) (a / L) (1 / L) lx J (by positivity) hlx0 hu0 huJ
    have hxr : x ^ (ρ.re - 1) = Real.exp (-(lx * (1 - ρ.re))) := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring
    rw [hxr]
    calc (mult χ ρ : ℝ) * Real.exp (-(lx * (1 - ρ.re)))
        ≤ (mult χ ρ : ℝ) * ∑ j ∈ range J, (if 1 - ρ.re < a / L + (j + 1) * (1 / L)
            then Real.exp (-(lx * (a / L + j * (1 / L)))) else 0) :=
          mul_le_mul_of_nonneg_left hlp (by positivity)
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
  have hstep1 : zsumP (fun β => 7 / 8 ≤ β) θ N S ≤ ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re), ∑ j ∈ range J,
          (if 1 - ρ.re < a / L + (j + 1) * (1 / L)
            then (mult χ ρ : ℝ) * Real.exp (-(lx * (a / L + j * (1 / L)))) else 0) := by
    unfold zsumP
    exact Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun χ hχ =>
      Finset.sum_le_sum fun ρ hρ => hterm k hk χ hχ ρ hρ
  have hswap : (∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re), ∑ j ∈ range J,
          (if 1 - ρ.re < a / L + (j + 1) * (1 / L)
            then (mult χ ρ : ℝ) * Real.exp (-(lx * (a / L + j * (1 / L)))) else 0)) =
      ∑ j ∈ range J, Real.exp (-(lx * (a / L + j * (1 / L)))) * ∑ k ∈ range ⌊P⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re ∧ 1 - ρ.re < a / L + (j + 1) * (1 / L)),
            (mult χ ρ : ℝ) := by
    have e1 : (∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re), ∑ j ∈ range J,
          (if 1 - ρ.re < a / L + (j + 1) * (1 / L)
            then (mult χ ρ : ℝ) * Real.exp (-(lx * (a / L + j * (1 / L)))) else 0)) =
        ∑ j ∈ range J, ∑ k ∈ range ⌊P⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ∑ ρ ∈ (S k χ).filter (fun ρ => 7 / 8 ≤ ρ.re),
              (if 1 - ρ.re < a / L + (j + 1) * (1 / L)
                then (mult χ ρ : ℝ) * Real.exp (-(lx * (a / L + j * (1 / L)))) else 0) := by
      exact (Finset.sum_congr rfl fun k _ =>
        (Finset.sum_congr rfl fun χ _ => Finset.sum_comm).trans Finset.sum_comm).trans
          Finset.sum_comm
    rw [e1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← Finset.sum_filter, Finset.filter_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  rw [hswap] at hstep1
  refine hstep1.trans ((Finset.sum_le_sum fun j _ => ?_).trans
    (hser θ hθ (hθle.trans (min_le_left _ _)) J))
  have hv : 0 ≤ a / L + ((j : ℝ) + 1) * (1 / L) := by positivity
  have hM := hNw (a / L + ((j : ℝ) + 1) * (1 / L)) hv
  have hvL : (a / L + ((j : ℝ) + 1) * (1 / L)) * L = a + j + 1 := by field_simp; ring
  rw [hvL] at hM
  have he : lx * (a / L + (j : ℝ) * (1 / L)) = (1 / θ - 8) * (a + j) := by
    rw [← hΛ]; field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le

/-- There are at most `q` primitive characters mod `q`: Mathlib's count `φ(q)` of all characters,
`DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`. -/
lemma card_prim_le (q : ℕ) [NeZero q] :
    (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)).card : ℝ) ≤ q := by
  have h1 := Finset.card_filter_le (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => χ.IsPrimitive)
  have h2 : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h3 : q.totient ≤ q := Nat.totient_le q
  exact_mod_cast h1.trans (h2 ▸ h3)

/-- Total multiplicity of the nontrivial zeros up to height `T`, Davenport ch. 16 in the window
form of `LeanLab.HardyLittlewood1923.U1482.zeroCountUnit`, summed over the `⌊T⌋ + 1` unit
windows. -/
lemma mult_total_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ T : ℝ, 0 ≤ T → ∀ s : Finset ℂ,
      (∀ ρ ∈ s, χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∑ ρ ∈ s, (mult χ ρ : ℝ) ≤ A * ((T + 1) * Real.log (q * (T + 2))) := by
  classical
  obtain ⟨A, hA, hz⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  refine ⟨A, hA, fun q _ χ hχ T hT s hs => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog0 : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
  have hmaps : ∀ ρ ∈ s, ⌊|ρ.im|⌋₊ ∈ range (⌊T⌋₊ + 1) := by
    intro ρ hρ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (hs ρ hρ).2.2.2))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hwin : ∀ j ∈ range (⌊T⌋₊ + 1),
      ∑ ρ ∈ s.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (mult χ ρ : ℝ) ≤ A * Real.log (q * (T + 2)) := by
    intro j hj
    have hjT : (j : ℝ) ≤ T := by
      have : j ≤ ⌊T⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hT)
    have h := (hz q χ hχ (j : ℝ) (Nat.cast_nonneg j)).2 (s.filter (fun ρ => ⌊|ρ.im|⌋₊ = j))
      (fun ρ hρ => by
        obtain ⟨hρs, hρj⟩ := Finset.mem_filter.mp hρ
        obtain ⟨h1, h2, h3, -⟩ := hs ρ hρs
        refine ⟨⟨h1, h2, h3⟩, ?_, ?_⟩
        · rw [← hρj]; exact Nat.floor_le (abs_nonneg _)
        · rw [← hρj]; exact (Nat.lt_floor_add_one _).le)
    have heq : ∑ ρ ∈ s.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (mult χ ρ : ℝ) =
        ∑ ρ ∈ s.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), LeanLab.HardyLittlewood1923.U1479.mult χ ρ := by
      rfl
    rw [heq]
    refine h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hA)
    · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      positivity
    · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  refine (Finset.sum_le_sum hwin).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ T + 1 := by
    push_cast; linarith [Nat.floor_le hT]
  have := mul_le_mul_of_nonneg_right this (mul_nonneg hA hlog0)
  nlinarith

/-- The size comparison behind `zero_sum_low`: with `P = N^θ`, `x = N / P^8`, the factor
`x^(-1/8)` beats `P^2 (P^10 + 1) log (P (P^10 + 2))` and `e^(1/θ)` for `θ` small and `N` large.
Elementary real analysis. -/
lemma low_asymp (A : ℝ) (hA : 0 ≤ A) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ (N : ℝ) / ((N : ℝ) ^ θ) ^ 8 ∧ 1 ≤ (N : ℝ) ^ θ ∧
      ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (-1 / 8 : ℝ) * ((N : ℝ) ^ θ * ((N : ℝ) ^ θ *
        (A * ((((N : ℝ) ^ θ) ^ 10 + 1) *
          Real.log ((N : ℝ) ^ θ * (((N : ℝ) ^ θ) ^ 10 + 2)))))) ≤ Real.exp (-1 / θ) := by
  refine ⟨1 / 400, by norm_num, fun θ hθ hθle => ?_⟩
  set M : ℝ := 6 * A * Real.exp (1 / θ) + 1 with hM
  have hM1 : 1 ≤ M := by have := Real.exp_pos (1 / θ); nlinarith
  refine ⟨⌈M ^ 16⌉₊, fun N hN => ?_⟩
  set n : ℝ := (N : ℝ) with hn
  have hnM : M ^ 16 ≤ n := (Nat.le_ceil _).trans (by rw [hn]; exact_mod_cast hN)
  have hn1 : 1 ≤ n := le_trans (one_le_pow₀ hM1) hnM
  have hn0 : 0 ≤ n := by linarith
  set P : ℝ := n ^ θ with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hn1 hθ.le
  have hPk : ∀ k : ℕ, P ^ k = n ^ (k * θ) := by
    intro k
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hn0, mul_comm]
  have hx : n / P ^ 8 = n ^ (1 - 8 * θ) := by
    rw [hPk 8, Real.rpow_sub' hn0 (by linarith), Real.rpow_one]
    norm_num
  refine ⟨?_, hP1, ?_⟩
  · rw [hx]; exact Real.one_le_rpow hn1 (by linarith)
  have hxe : (n / P ^ 8) ^ (-1 / 8 : ℝ) = n ^ ((1 - 8 * θ) * (-1 / 8)) := by
    rw [hx, ← Real.rpow_mul hn0]
  have hP10 : P ^ 10 + 1 ≤ 2 * P ^ 10 := by
    have : 1 ≤ P ^ 10 := one_le_pow₀ hP1
    linarith
  have hlog : Real.log (P * (P ^ 10 + 2)) ≤ 3 * P ^ 11 := by
    have h1 : 1 ≤ P ^ 10 := one_le_pow₀ hP1
    have h2 : P * (P ^ 10 + 2) ≤ 3 * P ^ 11 := by
      have : P ^ 11 = P * P ^ 10 := by ring
      nlinarith
    exact (Real.log_le_self (by positivity)).trans h2
  have hlog0 : 0 ≤ Real.log (P * (P ^ 10 + 2)) := Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 10) hP1])
  have hbig : P * (P * (A * ((P ^ 10 + 1) * Real.log (P * (P ^ 10 + 2))))) ≤ 6 * A * P ^ 23 := by
    have h3 : (P ^ 10 + 1) * Real.log (P * (P ^ 10 + 2)) ≤ (2 * P ^ 10) * (3 * P ^ 11) :=
      mul_le_mul hP10 hlog hlog0 (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hA
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ P * P)
    calc P * (P * (A * ((P ^ 10 + 1) * Real.log (P * (P ^ 10 + 2)))))
        = P * P * (A * ((P ^ 10 + 1) * Real.log (P * (P ^ 10 + 2)))) := by ring
      _ ≤ P * P * (A * ((2 * P ^ 10) * (3 * P ^ 11))) := h5
      _ = 6 * A * P ^ 23 := by ring
  have hxe0 : 0 ≤ (n / P ^ 8) ^ (-1 / 8 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hcomb : (n / P ^ 8) ^ (-1 / 8 : ℝ) * P ^ 23 ≤ n ^ (-1 / 16 : ℝ) := by
    rw [hxe, hPk 23, ← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    push_cast
    linarith
  have hroot : M ≤ n ^ (1 / 16 : ℝ) := by
    have hM0 : 0 ≤ M := by linarith
    calc M = (M ^ 16) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
      _ ≤ n ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) hnM (by norm_num)
  have hinv : n ^ (-1 / 16 : ℝ) = (n ^ (1 / 16 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hn0]; norm_num
  have hpos : 0 < n ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hfin : 6 * A * n ^ (-1 / 16 : ℝ) ≤ Real.exp (-1 / θ) := by
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have he : Real.exp (-1 / θ) * Real.exp (1 / θ) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hepos : 0 < Real.exp (-1 / θ) := Real.exp_pos _
    have : 6 * A ≤ Real.exp (-1 / θ) * M := by
      rw [hM, mul_add, ← mul_assoc, mul_comm (Real.exp (-1 / θ)) (6 * A), mul_assoc, he]
      linarith
    exact this.trans (mul_le_mul_of_nonneg_left hroot hepos.le)
  calc (n / P ^ 8) ^ (-1 / 8 : ℝ) * (P * (P * (A * ((P ^ 10 + 1) * Real.log (P * (P ^ 10 + 2))))))
      ≤ (n / P ^ 8) ^ (-1 / 8 : ℝ) * (6 * A * P ^ 23) := mul_le_mul_of_nonneg_left hbig hxe0
    _ = 6 * A * ((n / P ^ 8) ^ (-1 / 8 : ℝ) * P ^ 23) := by ring
    _ ≤ 6 * A * n ^ (-1 / 16 : ℝ) := mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ ≤ Real.exp (-1 / θ) := hfin

/-- Gallagher 1975 p.131 display 14, the part from zeros with `β < 7/8`: each term is at most
`m(ρ) x^(-1/8)`, and the total multiplicity is polynomial in `P` by `zeroCountUnit`, while
`x^(-1/8) = (N / P^8)^(-1/8)` beats any fixed power of `P` once `θ` is small. -/
theorem zero_sum_low (b : ℝ) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ, ZeroSetHyp b θ N S →
        zsumP (fun β => β < 7 / 8) θ N S ≤ Real.exp (-1 / θ) := by
  obtain ⟨A, hA, hmult⟩ := mult_total_le
  obtain ⟨θ₀, hθ₀, hasy⟩ := low_asymp A hA
  refine ⟨θ₀, hθ₀, fun θ hθ hθle => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hasy θ hθ hθle
  refine ⟨N₀, fun N hN S hS => ?_⟩
  obtain ⟨hx1, hP1, hfin⟩ := hN₀ N hN
  set P : ℝ := (N : ℝ) ^ θ with hP
  set x : ℝ := (N : ℝ) / P ^ 8 with hx
  set T : ℝ := P ^ 10 with hT
  set B : ℝ := A * ((T + 1) * Real.log (P * (T + 2))) with hB
  have hT0 : 0 ≤ T := by positivity
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log (P * (T + 2)) := Real.log_nonneg (by nlinarith)
    positivity
  have hxe0 : 0 ≤ x ^ (-1 / 8 : ℝ) := Real.rpow_nonneg (by linarith) _
  -- each character contributes at most `x^(-1/8) B`
  have hchi : ∀ k ∈ range ⌊P⌋₊, ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
      (fun χ => χ.IsPrimitive),
      ∑ ρ ∈ (S k χ).filter (fun ρ => ρ.re < 7 / 8), (mult χ ρ : ℝ) * x ^ (ρ.re - 1)
        ≤ x ^ (-1 / 8 : ℝ) * B := by
    intro k hk χ hχ
    have hχp : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
    have hkP : ((k + 1 : ℕ) : ℝ) ≤ P := by
      have h1 : k + 1 ≤ ⌊P⌋₊ := Finset.mem_range.mp hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le (by linarith))
    calc ∑ ρ ∈ (S k χ).filter (fun ρ => ρ.re < 7 / 8), (mult χ ρ : ℝ) * x ^ (ρ.re - 1)
        ≤ ∑ ρ ∈ (S k χ).filter (fun ρ => ρ.re < 7 / 8), x ^ (-1 / 8 : ℝ) * (mult χ ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have hρr : ρ.re < 7 / 8 := (Finset.mem_filter.mp hρ).2
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x ^ (-1 / 8 : ℝ) * ∑ ρ ∈ (S k χ).filter (fun ρ => ρ.re < 7 / 8), (mult χ ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ x ^ (-1 / 8 : ℝ) * B := by
          refine mul_le_mul_of_nonneg_left ?_ hxe0
          have h := hmult (k + 1) χ hχp T hT0 ((S k χ).filter (fun ρ => ρ.re < 7 / 8))
            (fun ρ hρ => by
              obtain ⟨a1, a2, a3, a4, -⟩ := hS k χ ρ (Finset.mem_filter.mp hρ).1
              exact ⟨a1, a2, a3, a4⟩)
          refine h.trans (mul_le_mul_of_nonneg_left ?_ hA)
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          have hq0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
          exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hkP (by linarith))
  have hk : ∀ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ (S k χ).filter (fun ρ => ρ.re < 7 / 8), (mult χ ρ : ℝ) * x ^ (ρ.re - 1)
        ≤ P * (x ^ (-1 / 8 : ℝ) * B) := by
    intro k hk
    have hkP : ((k + 1 : ℕ) : ℝ) ≤ P := by
      have h1 : k + 1 ≤ ⌊P⌋₊ := Finset.mem_range.mp hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le (by linarith))
    refine (Finset.sum_le_sum (hchi k hk)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right ((card_prim_le (k + 1)).trans hkP) (by positivity)
  have hsum : zsumP (fun β => β < 7 / 8) θ N S ≤ P * (P * (x ^ (-1 / 8 : ℝ) * B)) := by
    unfold zsumP
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
  refine hsum.trans (le_of_eq_of_le ?_ hfin)
  simp only [hB]
  ring

/-- The split of the zero sum at `β = 7/8`. Elementary. -/
lemma zsum_split (θ : ℝ) (N : ℕ) (S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ) :
    ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (ρ.re - 1)
      = zsumP (fun β => 7 / 8 ≤ β) θ N S + zsumP (fun β => β < 7 / 8) θ N S := by
  unfold zsumP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have h := Finset.sum_filter_add_sum_filter_not (S k χ) (fun ρ : ℂ => 7 / 8 ≤ ρ.re)
    (fun ρ => (mult χ ρ : ℝ) * ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (ρ.re - 1))
  rw [← h]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ρ; simp [not_le]

/-- Gallagher 1975 p.131 display 14, the zero sum layer. -/
theorem zero_sum_density_layer (b : ℝ) (hb : 0 < b) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ,
        (∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 10 ∧
          (|ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 → ρ.re < 1 - b / Real.log (((N : ℝ) ^ θ) ^ 5))) →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (ρ.re - 1)
          ≤ C * Real.exp (-c / θ) := by
  obtain ⟨c, C, θ₁, hc, hC, hθ₁, hhigh⟩ := zero_sum_high b hb
  obtain ⟨θ₂, hθ₂, hlow⟩ := zero_sum_low b
  refine ⟨min c 1, C + 1, min θ₁ θ₂, lt_min hc one_pos, by linarith, lt_min hθ₁ hθ₂, ?_⟩
  intro θ hθ hθle
  obtain ⟨N₁, hN₁⟩ := hhigh θ hθ (hθle.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hlow θ hθ (hθle.trans (min_le_right _ _))
  refine ⟨max N₁ N₂, fun N hN S hS => ?_⟩
  rw [zsum_split]
  have h1 := hN₁ N (le_of_max_le_left hN) S hS
  have h2 := hN₂ N (le_of_max_le_right hN) S hS
  have e1 : Real.exp (-c / θ) ≤ Real.exp (-min c 1 / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith [min_le_left c 1]) hθ.le)
  have e2 : Real.exp (-1 / θ) ≤ Real.exp (-min c 1 / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith [min_le_right c 1]) hθ.le)
  have := mul_le_mul_of_nonneg_left e1 hC.le
  nlinarith

end LeanLab.Linnik.ExplicitFormula
