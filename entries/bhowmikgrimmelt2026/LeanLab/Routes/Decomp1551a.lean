module

public import Mathlib
public import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian
public import LeanLab.ChirreHagen2025.SmoothTheorem2
public import LeanLab.Routes.Decomp1551b
public import LeanLab.Ported.Zeta23.RvM.ReZeroCount

/-!
Unit U-1551, track T1, DECOMPOSE, run 20261026T1219Z-15327, 2026-10-26. PALOMAR line I5171.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Decomposition of the input `SmoothT2.ExplicitA gZ Z δ` of
`LeanLab.Routes.U1508.goldbach_445_hsw_gZ`: along the truncations `Z n` the sums
`Σ_{ρ ∈ Z n} c_ρ(δ) y^ρ`, `c_ρ(δ) = ((1+δ)^ρ - 1)/ρ`, tend to `-(V_δ(y) - B_δ(y))` for almost
every `y ≥ 2`. This is the difference at `(1+δ)y` and `y` of von Mangoldt's explicit formula
`ψ(x) = x - Σ_ρ x^ρ/ρ - ζ'/ζ(0) - (1/2) log(1 - x^{-2})`, `x > 1` not an integer, the zero sum
taken symmetrically, Davenport, Multiplicative Number Theory, chapter 17, and
Montgomery-Vaughan, Multiplicative Number Theory I, section 12.1, Theorem 12.5 in its limit
form. The formula itself is unconditional; RH enters only through `ρ = 1/2 + iγ`.

The textbook chain, Davenport chapter 17, with `c = 2` and `f(s) = -ζ'/ζ(s) x^s / s`:
* Perron: `J(x, T) = (1/2πi) ∫_{2-iT}^{2+iT} f` tends to `ψ(x)`: LEAVES `perron_kernel_bound`,
  the lemma of Davenport chapter 17, `jc_eq_tsum`, the Dirichlet series interchange, and
  `tsum_kernel_limit`, the dominated limit; assembled in `perron_limit`, PROVED from them.
* Contour shift to `Re s = -(2m+1)`: LEAF `rect_identity`, the residue theorem with residues
  `x` at 1, `-m_ρ x^ρ/ρ` at the zeros, `-ζ'/ζ(0)` at 0 and `x^{-2k}/(2k)` at `-2k`, using LEAF
  `zt_finite`; LEAF `left_edge_limit`, the left edge tends to 0 as `m → ∞`; LEAF `hor_tendsto`,
  the horizontal edges converge to integrals over `(-∞, 2]`; the trivial zero sum tends to
  `-(1/2) log(1 - x^{-2})`, PROVED as `trivU_tendsto`.
* Good heights: LEAF `good_heights`, heights `T_n ∈ [n+2, n+3]` free of zeros with
  `|ζ'/ζ(σ ± iT_n)| ≤ C log² T_n (1 + |σ|)` for `σ ≤ 2`, from the lab's `good_height_full`
  for `-1/2 ≤ σ ≤ 2` and the functional equation for `σ ≤ -1/2`; LEAF `hor_small`, the
  horizontal integrals then tend to 0.
ASSEMBLIES: `explicit_psi`, the explicit formula along `T_n`, and `explicitA_gZ`, the input of
U1508 with the truncations `Z n = {γ : |γ| ≤ T_n}`; both CONDITIONAL ON the leaves.
-/

@[expose] public section

namespace LeanLab.Routes.Decomp1551a

open scoped ComplexConjugate

open Complex Filter Topology MeasureTheory Set
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx re_half_of_RH)
open LeanLab.ChirreHagen2025.SmoothT2 (ExplicitA cδ rho Bf)
open LeanLab.ChirreHagen2025.SmoothKernel (P)
open LeanLab.ChirreHagen2025.Local36 (V)

local notation "ζ" => riemannZeta
local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `f(s) = -ζ'/ζ(s) x^s / s`. -/
noncomputable def fK (x : ℝ) (s : ℂ) : ℂ := -logDeriv ζ s * (x : ℂ) ^ s / s

/-- `J(x, T) = (1/2π) ∫_{-T}^{T} f(2 + it) dt = (1/2πi) ∫_{2-iT}^{2+iT} f(s) ds`. -/
noncomputable def Jc (x T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, fK x ((2 : ℂ) + t * I)

/-- The truncated Perron kernel `I(y, T) = (1/2π) ∫_{-T}^{T} y^{2+it}/(2+it) dt`. -/
noncomputable def pK (y T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I)

/-- The zeros, with multiplicity, of ordinate at most `T` in absolute value; empty if that set
were infinite, which `zt_finite` excludes. -/
noncomputable def ZT (T : ℝ) : Finset ZIdx := by
  classical
  exact if h : {i : ZIdx | |gZ i| ≤ T}.Finite then h.toFinset else ∅

/-- `Σ_{|γ| ≤ T} x^ρ/ρ`, with multiplicity. -/
noncomputable def ZS (x T : ℝ) : ℂ := ∑ i ∈ ZT T, (x : ℂ) ^ (i.1 : ℂ) / (i.1 : ℂ)

/-- `ζ'/ζ(0)`. -/
noncomputable def L0 : ℂ := deriv ζ 0 / ζ 0

/-- `Σ_{k=1}^{m} x^{-2k}/(2k)`, the residues at the trivial zeros `-2, ..., -2m`. -/
noncomputable def TrivU (x : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, ((x ^ 2)⁻¹) ^ (k + 1) / (2 * ((k : ℝ) + 1))

/-- `-(1/2) log(1 - x^{-2})`. -/
noncomputable def TrivInf (x : ℝ) : ℝ := -(1 / 2) * Real.log (1 - (x ^ 2)⁻¹)

/-- The horizontal edge `∫_{-(2m+1)}^{2} f(σ + iT) dσ`. -/
noncomputable def HorI (x : ℝ) (m : ℕ) (T : ℝ) : ℂ :=
  ∫ σ in (-(2 * (m : ℝ) + 1))..2, fK x ((σ : ℂ) + T * I)

/-- The horizontal half line `∫_{-∞}^{2} f(σ + iT) dσ`. -/
noncomputable def HorInf (x T : ℝ) : ℂ := ∫ σ in Set.Iic (2 : ℝ), fK x ((σ : ℂ) + T * I)

/-- The left edge `∫_{-T}^{T} f(-(2m+1) + it) dt`. -/
noncomputable def LeftI (x : ℝ) (m : ℕ) (T : ℝ) : ℂ :=
  ∫ t in (-T)..T, fK x ((-(2 * (m : ℝ) + 1) : ℝ) + t * I)

/-! ### Perron -/

/-- LEAF. Unit U-1551. Davenport chapter 17, the lemma on the discontinuous integral, with
`c = 2`: for `y > 0`, `y ≠ 1`, `T > 0`, `|I(y, T) - δ(y)| ≤ y² / (π T |log y|)`, where
`δ(y) = 1` for `y > 1` and `0` for `y < 1`. The lab's `PNTPort/Perron/Cutoff.lean` has a
cutoff estimate of this kind. -/
theorem perron_kernel_bound (y : ℝ) (hy : 0 < y) (hy1 : y ≠ 1) (T : ℝ) (hT : 0 < T) :
    ‖pK y T - (if 1 < y then 1 else 0)‖ ≤ y ^ 2 / (Real.pi * T * |Real.log y|) := by
  let F : ℂ → ℂ := fun s => (y : ℂ) ^ s / s
  let H : ℝ → ℝ → ℝ → ℂ := fun a b v => ∫ σ in a..b, F ((σ : ℂ) + v * I)
  let V : ℝ → ℂ := fun a => ∫ t in (-T)..T, F ((a : ℂ) + t * I)
  have hF : ∀ s : ℂ, s ≠ 0 → AnalyticAt ℂ F s := by
    intro s hs
    exact (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hy s).div analyticAt_id hs
  have hn : ∀ σ v : ℝ, |v| = T → ‖F ((σ : ℂ) + v * I)‖ ≤ y ^ σ / T := by
    intro σ v hv
    dsimp [F]
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hy]
    have hd : T ≤ ‖(σ : ℂ) + v * I‖ := by
      have hh := abs_im_le_norm ((σ : ℂ) + v * I)
      simpa [hv] using hh
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hT hd
  have hnear : (F - fun s : ℂ => 1 / (s - 0)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    have hd := (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl (ofReal_ne_zero.mpr hy.ne'))
    have hh := hd.tendsto_slope_zero
    simp only [id_eq, zero_add, cpow_zero, mul_one, one_mul, smul_eq_mul] at hh
    have he : (F - fun s : ℂ => 1 / (s - 0)) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun s => s⁻¹ * ((y : ℂ) ^ s - 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      dsimp [F]
      field_simp
      ring
    exact (hh.congr' he.symm).isBigO_one ℂ
  have hrectL : ∀ a : ℝ, a < 0 → RectangleIntegral' F ⟨a, -T⟩ ⟨2, T⟩ = 1 := by
    intro a ha
    apply ResidueTheoremOnRectangleWithSimplePole' (p := 0) (A := 1)
    · simp; linarith
    · simp; linarith
    · rw [rectangle_mem_nhds_iff]
      simp only [mem_reProdIm, zero_re, zero_im, uIoo_of_le (by linarith : a ≤ 2),
        uIoo_of_le (by linarith : -T ≤ T), mem_Ioo]
      exact ⟨⟨ha, by norm_num⟩, by linarith, hT⟩
    · intro s hs
      exact (hF s hs.2).differentiableAt.differentiableWithinAt
    · exact hnear
  have hrectR : ∀ b : ℝ, 2 ≤ b → RectangleIntegral' F ⟨2, -T⟩ ⟨b, T⟩ = 0 := by
    intro b hb
    have hf : HolomorphicOn F (Rectangle (⟨2, -T⟩ : ℂ) ⟨b, T⟩) := by
      intro s hs
      apply (hF s ?_).differentiableAt.differentiableWithinAt
      intro hz
      simp only [Rectangle, mem_reProdIm, uIcc_of_le (by linarith : (2 : ℝ) ≤ b)] at hs
      have hh := hs.1.1
      rw [hz] at hh
      norm_num at hh
    simp only [RectangleIntegral', hf.vanishesOnRectangle (by rfl), smul_zero]
  have hhl : ∀ a : ℝ, a ≤ 2 → 1 < y → ∀ v : ℝ, |v| = T →
      ‖H a 2 v‖ ≤ y ^ 2 / (T * Real.log y) := by
    intro a ha hyy v hv
    have hdom : IntegrableOn (fun σ : ℝ => y ^ σ / T) (Iic 2) := by
      have hh := (integrableOn_exp_mul_Iic (Real.log_pos hyy) 2).div_const T
      simpa [IntegrableOn, Real.rpow_def_of_pos hy, mul_comm] using hh
    have hsub : Ioc a (2 : ℝ) ⊆ Iic 2 := fun _ h => h.2
    have hh := norm_integral_le_of_norm_le (hdom.mono_set hsub) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with σ hσ
      exact hn σ v hv)
    have hh' := setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun σ => by dsimp; positivity))
      (Filter.Eventually.of_forall hsub)
    have he : (∫ σ in Iic (2 : ℝ), y ^ σ / T) = y ^ 2 / (T * Real.log y) := by
      simp_rw [Real.rpow_def_of_pos hy]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      have he : (fun σ : ℝ => Real.exp (Real.log y * σ)) = (fun σ : ℝ => Real.exp (σ * Real.log y)) := by funext σ; rw [mul_comm]
      rw [integral_exp_mul_Iic (Real.log_pos hyy)]
      rw [← Real.rpow_def_of_pos hy, Real.rpow_two]
      ring
    have hh0 : ‖H a 2 v‖ ≤ ∫ σ in Ioc a 2, y ^ σ / T := by simpa [H, intervalIntegral.integral_of_le ha] using hh
    exact hh0.trans (hh'.trans_eq he)
  have hhr : ∀ b : ℝ, 2 ≤ b → y < 1 → ∀ v : ℝ, |v| = T →
      ‖H 2 b v‖ ≤ y ^ 2 / (T * -Real.log y) := by
    intro b hb hyy v hv
    have hl : Real.log y < 0 := Real.log_neg hy hyy
    have hdom : IntegrableOn (fun σ : ℝ => y ^ σ / T) (Ioi 2) := by
      have hh := (integrableOn_exp_mul_Ioi hl 2).div_const T
      simpa [IntegrableOn, Real.rpow_def_of_pos hy, mul_comm] using hh
    have hsub : Ioc (2 : ℝ) b ⊆ Ioi 2 := fun _ h => h.1
    have hh := norm_integral_le_of_norm_le (hdom.mono_set hsub) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with σ hσ
      exact hn σ v hv)
    have hh' := setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun σ => by dsimp; positivity))
      (Filter.Eventually.of_forall hsub)
    have he : (∫ σ in Ioi (2 : ℝ), y ^ σ / T) = y ^ 2 / (T * -Real.log y) := by
      simp_rw [Real.rpow_def_of_pos hy]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      have he : (fun σ : ℝ => Real.exp (Real.log y * σ)) = (fun σ : ℝ => Real.exp (σ * Real.log y)) := by funext σ; rw [mul_comm]
      rw [integral_exp_mul_Ioi hl]
      rw [← Real.rpow_def_of_pos hy, Real.rpow_two]
      ring
    have hh0 : ‖H 2 b v‖ ≤ ∫ σ in Ioc 2 b, y ^ σ / T := by simpa [H, intervalIntegral.integral_of_le hb] using hh
    exact hh0.trans (hh'.trans_eq he)
  have hV : ∀ a : ℝ, 1 ≤ |a| → ‖V a‖ ≤ 2 * T * y ^ a := by
    intro a ha
    have hh : ∀ t ∈ Set.uIoc (-T) T, ‖F ((a : ℂ) + t * I)‖ ≤ y ^ a := by
      intro t _
      have hd : 1 ≤ ‖(a : ℂ) + t * I‖ := by
        have h := abs_re_le_norm ((a : ℂ) + t * I)
        have hre : ((a : ℂ) + t * I).re = a := by simp
        rw [hre] at h
        exact ha.trans h
      dsimp [F]
      rw [norm_div, norm_cpow_eq_rpow_re_of_pos hy]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact div_le_self (Real.rpow_nonneg hy.le _) hd
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hh
    have he : |T - -T| = 2 * T := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
    rw [he] at h
    exact h.trans_eq (by ring)
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have hcI : c * I = ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    dsimp [c]
    push_cast
    field_simp
  have hcn : ‖c‖ = 1 / (2 * Real.pi) := by
    simp [c, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_div]
  have hpK : pK y T = c * I * V 2 := by
    rw [hcI]
    rfl
  let D : ℝ := y ^ 2 / (T * |Real.log y|)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  rcases lt_or_gt_of_ne hy1 with hyy | hyy
  · simp only [not_lt.mpr hyy.le, ↓reduceIte, sub_zero]
    have hl : Real.log y < 0 := Real.log_neg hy hyy
    have hhs : ∀ b : ℝ, 2 ≤ b → ∀ v : ℝ, |v| = T → ‖H 2 b v‖ ≤ D := by
      intro b hb v hv
      simpa [D, abs_of_neg hl] using hhr b hb hyy v hv
    have hbound : ∀ n : ℕ, ‖pK y T‖ ≤ (2 * T * y ^ ((n : ℝ) + 3) + 2 * D) / (2 * Real.pi) := by
      intro n
      let b : ℝ := n + 3
      have hb : 2 ≤ b := by dsimp [b]; have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hId := hrectR b hb
      have hId : c * (H 2 b (-T) - H 2 b T + I * V b - I * V 2) = 0 := by
        simpa only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
          smul_eq_mul, one_div, c, H, V] using hId
      have he : pK y T = c * (H 2 b (-T) - H 2 b T + I * V b) := by
        rw [hpK]
        linear_combination -hId
      have hnorm : ‖H 2 b (-T) - H 2 b T + I * V b‖ ≤ ‖H 2 b (-T)‖ + ‖H 2 b T‖ + ‖V b‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (by simp))
      have hv := hV b (by rw [abs_of_nonneg (by linarith)]; linarith)
      have hh1 := hhs b hb (-T) (by rw [abs_neg, abs_of_pos hT])
      have hh2 := hhs b hb T (abs_of_pos hT)
      rw [he, norm_mul, hcn]
      calc
        _ ≤ (1 / (2 * Real.pi)) * (D + D + 2 * T * y ^ b) := by gcongr; linarith
        _ = _ := by dsimp [b]; ring
    have hp : Tendsto (fun n : ℕ => y ^ ((n : ℝ) + 3)) atTop (𝓝 0) := by
      have he : ∀ n : ℕ, y ^ ((n : ℝ) + 3) = y ^ n * y ^ (3 : ℕ) := by
        intro n
        rw [Real.rpow_add hy, Real.rpow_natCast]
        norm_cast
      simp_rw [he]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hy.le hyy).mul_const (y ^ 3)
    have hh := ((hp.const_mul (2 * T)).add_const (2 * D)).div_const (2 * Real.pi)
    have hfinal : (0 + 2 * D) / (2 * Real.pi) = y ^ 2 / (Real.pi * T * |Real.log y|) := by
      dsimp [D]
      field_simp
      ring
    simp only [mul_zero] at hh
    rw [hfinal] at hh
    exact ge_of_tendsto' hh hbound
  · simp only [hyy, ↓reduceIte]
    have hl : 0 < Real.log y := Real.log_pos hyy
    have hhs : ∀ a : ℝ, a ≤ 2 → ∀ v : ℝ, |v| = T → ‖H a 2 v‖ ≤ D := by
      intro a ha v hv
      simpa [D, abs_of_pos hl] using hhl a ha hyy v hv
    have hbound : ∀ n : ℕ, ‖pK y T - 1‖ ≤ (2 * T * y ^ (-((n : ℝ) + 1)) + 2 * D) / (2 * Real.pi) := by
      intro n
      let a : ℝ := -((n : ℝ) + 1)
      have ha : a < 0 := by dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hId := hrectL a ha
      have hId : c * (H a 2 (-T) - H a 2 T + I * V 2 - I * V a) = 1 := by
        simpa only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
          smul_eq_mul, one_div, c, H, V] using hId
      have he : pK y T - 1 = c * (I * V a - H a 2 (-T) + H a 2 T) := by
        rw [hpK]
        linear_combination hId
      have hnorm : ‖I * V a - H a 2 (-T) + H a 2 T‖ ≤ ‖V a‖ + ‖H a 2 (-T)‖ + ‖H a 2 T‖ := by
        exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by simp)) le_rfl)
      have hv := hV a (by rw [abs_of_neg ha]; dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hh1 := hhs a (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT])
      have hh2 := hhs a (by linarith) T (abs_of_pos hT)
      rw [he, norm_mul, hcn]
      calc
        _ ≤ (1 / (2 * Real.pi)) * (2 * T * y ^ a + D + D) := by gcongr; linarith
        _ = _ := by dsimp [a]; ring
    have hp : Tendsto (fun n : ℕ => y ^ (-((n : ℝ) + 1))) atTop (𝓝 0) := by
      have he : ∀ n : ℕ, y ^ (-((n : ℝ) + 1)) = (y⁻¹) ^ n * y⁻¹ := by
        intro n
        rw [Real.rpow_neg hy.le, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_one,
          mul_inv, inv_pow]
      simp_rw [he]
      have hiy : y⁻¹ < 1 := (inv_lt_one₀ hy).mpr hyy
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hy.le) hiy).mul_const y⁻¹
    have hh := ((hp.const_mul (2 * T)).add_const (2 * D)).div_const (2 * Real.pi)
    have hfinal : (0 + 2 * D) / (2 * Real.pi) = y ^ 2 / (Real.pi * T * |Real.log y|) := by
      dsimp [D]
      field_simp
      ring
    simp only [mul_zero] at hh
    rw [hfinal] at hh
    exact ge_of_tendsto' hh hbound

/-- LEAF. Unit U-1551. Davenport chapter 17, interchange of sum and integral: on `Re s = 2`,
`-ζ'/ζ(s) = Σ Λ(n) n^{-s}`, Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
uniformly convergent, so `J(x, T) = Σ_n Λ(n) I(x/n, T)` for `x > 0`, `T > 0`. -/
theorem jc_eq_tsum (x : ℝ) (hx : 0 < x) (T : ℝ) (hT : 0 < T) :
    Jc x T = ∑' n : ℕ, (Λ n : ℂ) * pK (x / n) T := by
  let F : ℕ → ℝ → ℂ := fun n t => (Λ n : ℂ) * ((x / n : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
      ((2 : ℂ) + t * I)
  have hnorm : ∀ n t, ‖F n t‖ = Λ n * (x / n) ^ 2 * ‖(1 : ℂ) / ((2 : ℂ) + t * I)‖ := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [F]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      norm_cpow_eq_rpow_re_of_pos (div_pos hx hn0)]
    norm_num
    norm_cast
  have hint : ∀ n : ℕ, IntegrableOn (F n) (Ioc (-T) T) := by
    intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -T ≤ T)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hc : Continuous (F n) := by
      dsimp [F]
      apply Continuous.div
      · apply continuous_const.mul
        exact Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr (div_pos hx hn0).ne'))
      · fun_prop
      · intro t ht
        have := congrArg re ht
        norm_num at this
    exact hc.intervalIntegrable _ _
  have hcoeff : Summable (fun n : ℕ => Λ n * (x / n) ^ 2) := by
    have hg := LeanLab.PNTPort.ExplicitPsi1.Trivial.summable_fl.mul_left (x ^ 2)
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)) ?_ hg
    intro n
    calc
      _ ≤ Real.log n * (x / n) ^ 2 := mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (sq_nonneg _)
      _ = _ := by unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl; ring
  have hsum : Summable (fun n : ℕ => ∫ t in Ioc (-T) T, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact hcoeff.mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hr : ∀ t : ℝ, ∑' n, F n t = fK x ((2 : ℂ) + t * I) := by
    intro t
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := (2 : ℂ) + t * I) (by norm_num)
    unfold fK
    rw [logDeriv_apply]
    have hL' : - (deriv ζ ((2 : ℂ) + t * I) / ζ ((2 : ℂ) + t * I)) =
      LSeries (fun n => (Λ n : ℂ)) ((2 : ℂ) + t * I) := by rw [hL]; ring
    rw [hL']
    unfold LSeries
    rw [← tsum_mul_right, ← tsum_div_const]
    apply tsum_congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne']
    dsimp [F]
    rw [Complex.ofReal_div, div_cpow_ofReal_nonneg hx.le hn0.le]
    push_cast
    ring
  have hl : ∀ n : ℕ, ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in Ioc (-T) T, F n t) =
      (Λ n : ℂ) * pK (x / n) T := by
    intro n
    unfold pK
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    dsimp [F]
    rw [show (fun t : ℝ => (Λ n : ℂ) * ((x / n : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
        ((2 : ℂ) + t * I)) =
      (fun t : ℝ => (Λ n : ℂ) * (((x / n : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
        ((2 : ℂ) + t * I))) by funext t; ring, integral_const_mul]
    ring
  unfold Jc
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  simp_rw [← hr]
  rw [← key, ← tsum_mul_left]
  exact tsum_congr hl

/-- LEAF. Unit U-1551. Davenport chapter 17, the limit `T → ∞` in Perron's formula: given the
kernel bound, for `x > 1` not an integer, `Σ_n Λ(n) I(x/n, T) → Σ_{n < x} Λ(n) = ψ(x)`, since
`Σ_n Λ(n) (x/n)² / |log(x/n)|` converges. -/
theorem tsum_kernel_limit (x : ℝ) (hx : 1 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x)
    (hk : ∀ y : ℝ, 0 < y → y ≠ 1 → ∀ T : ℝ, 0 < T →
      ‖pK y T - (if 1 < y then 1 else 0)‖ ≤ y ^ 2 / (Real.pi * T * |Real.log y|)) :
    Tendsto (fun T : ℝ => ∑' n : ℕ, (Λ n : ℂ) * pK (x / n) T) atTop
      (𝓝 ((Chebyshev.psi x : ℝ) : ℂ)) := by
  classical
  have hx0 : 0 < x := by linarith
  let a : ℕ → ℂ := fun n => (Λ n : ℂ) * (if (n : ℝ) < x then 1 else 0)
  let u : ℕ → ℝ := fun n => Λ n * (x / n) ^ 2 / (Real.pi * |Real.log (x / n)|)
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    dsimp [u]
    exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _))
      (mul_nonneg Real.pi_pos.le (abs_nonneg _))
  have hsum : Summable u := by
    apply (LeanLab.PNTPort.ExplicitPsi1.Trivial.summable_fl.mul_left (x ^ 2)).of_norm_bounded_eventually_nat
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (3 * x))] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hl3 : 1 ≤ Real.log 3 := (Real.le_log_iff_exp_le (by norm_num)).mpr Real.exp_one_lt_three.le
    have hlogn : Real.log (3 * x) ≤ Real.log n := Real.log_le_log (by positivity) hn
    rw [Real.log_mul (by norm_num) hx0.ne'] at hlogn
    have hlog : Real.log (x / n) ≤ -1 := by
      rw [Real.log_div hx0.ne' hn0.ne']
      linarith
    have hden : 1 ≤ Real.pi * |Real.log (x / n)| := by
      rw [abs_of_nonpos (by linarith : Real.log (x / n) ≤ 0)]
      nlinarith [Real.pi_gt_three]
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 n)]
    calc
      u n ≤ Λ n * (x / n) ^ 2 := div_le_self (by positivity) hden
      _ ≤ Real.log n * (x / n) ^ 2 :=
        mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (sq_nonneg _)
      _ = x ^ 2 * LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n := by
        unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl
        ring
  have ha0 : ∀ n ∉ Finset.range (⌊x⌋₊ + 1), a n = 0 := by
    intro n hn
    have hn' : ⌊x⌋₊ < n := by simpa using hn
    have hnx : x < n := (Nat.floor_lt hx0.le).mp hn'
    simp [a, not_lt.mpr hnx.le]
  have ha : Summable a := summable_of_ne_finset_zero ha0
  have hat : ∑' n, a n = ((Chebyshev.psi x : ℝ) : ℂ) := by
    rw [tsum_eq_sum ha0, Chebyshev.psi_eq_sum_Icc]
    push_cast
    have hr : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by ext n; simp
    rw [hr]
    apply Finset.sum_congr rfl
    intro n hn
    have hnx : (n : ℝ) < x := lt_of_le_of_ne ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hn).2) (hxn n)
    simp [a, hnx]
  have he : ∀ n : ℕ, ∀ T : ℝ, 0 < T →
      ‖(Λ n : ℂ) * pK (x / n) T - a n‖ ≤ u n / T := by
    intro n T hT
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a, u]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hyn1 : x / (n : ℝ) ≠ 1 := by
      intro h
      have hh : x = n := (div_eq_one_iff_eq hn0.ne').mp h
      exact hxn n hh.symm
    have hif : (if 1 < x / (n : ℝ) then (1 : ℂ) else 0) = if (n : ℝ) < x then 1 else 0 := by
      simp only [one_lt_div hn0]
    rw [show (Λ n : ℂ) * pK (x / n) T - a n =
      (Λ n : ℂ) * (pK (x / n) T - (if 1 < x / (n : ℝ) then 1 else 0)) by rw [hif]; dsimp [a]; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hh := mul_le_mul_of_nonneg_left (hk (x / n) (div_pos hx0 hn0) hyn1 T hT)
      (show 0 ≤ Λ n from ArithmeticFunction.vonMangoldt_nonneg)
    convert hh using 1 <;> dsimp [u] <;> ring
  have hlim : ∀ n : ℕ, Tendsto (fun T : ℝ => (Λ n : ℂ) * pK (x / n) T - a n) atTop (𝓝 0) := by
    intro n
    have hratio : Tendsto (fun T : ℝ => u n / T) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    exact squeeze_zero_norm' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact he n T hT) hratio
  have hdom : ∀ᶠ T : ℝ in atTop, ∀ n : ℕ, ‖(Λ n : ℂ) * pK (x / n) T - a n‖ ≤ u n := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT n
    exact (he n T (by linarith)).trans (div_le_self (hu0 n) hT)
  have hconv := tendsto_tsum_of_dominated_convergence hsum hlim hdom
  simp only [tsum_zero] at hconv
  have hrewrite : ∀ᶠ T : ℝ in atTop,
      (∑' n : ℕ, (Λ n : ℂ) * pK (x / n) T) =
        (∑' n : ℕ, ((Λ n : ℂ) * pK (x / n) T - a n)) + ((Chebyshev.psi x : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hs : Summable (fun n : ℕ => (Λ n : ℂ) * pK (x / n) T - a n) :=
      (hsum.div_const T).of_norm_bounded (fun n => he n T hT)
    rw [← hat, ← hs.tsum_add ha]
    apply tsum_congr
    intro n
    ring
  simpa using (hconv.add_const ((Chebyshev.psi x : ℝ) : ℂ)).congr' (by
    filter_upwards [hrewrite] with T hT
    exact hT.symm)

/-- Perron's formula in the limit: `J(x, T) → ψ(x)` for `x > 1` not an integer. CONDITIONAL ON
`perron_kernel_bound`, `jc_eq_tsum`, `tsum_kernel_limit`. -/
theorem perron_limit (x : ℝ) (hx : 1 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) :
    Tendsto (Jc x) atTop (𝓝 ((Chebyshev.psi x : ℝ) : ℂ)) := by
  refine (tsum_kernel_limit x hx hxn perron_kernel_bound).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (jc_eq_tsum x (by linarith) T hT).symm

/-! ### The contour shift -/

/-- Bridge from finitely many bounded zeros of ξ to the lab nontrivial zero indices,
including their finite multiplicity fibers. Davenport chapter 15 and chapter 12 page 79. -/
lemma zidx_finite_of_xi_zeros (T : ℝ)
    (hXi : {z : ℂ | ‖z‖ ≤ 1 + |T| ∧ Decomp1551b.xi z = 0}.Finite) :
    {i : ZIdx | |gZ i| ≤ T}.Finite := by
  have hS : ∀ z ∈ LeanLab.PNTPort.ExplicitPsi1.Zall,
      riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 := by
    rw [LeanLab.PNTPort.ExplicitPsi1.Zall_eq]
    exact fun _ hz => hz
  have hbase : {z : LeanLab.PNTPort.ExplicitPsi1.Zall | |(z : ℂ).im| ≤ T}.Finite := by
    apply (hXi.preimage Subtype.val_injective.injOn).subset
    intro z hz
    change |(z : ℂ).im| ≤ T at hz
    refine ⟨?_, (Decomp1551b.xi_zero_iff.1 z).mpr (hS z z.property)⟩
    calc
      ‖(z : ℂ)‖ ≤ |(z : ℂ).re| + |(z : ℂ).im| := norm_le_abs_re_add_abs_im _
      _ ≤ 1 + |T| := by
        rw [abs_of_pos (hS z z.property).2.1]
        linarith [(hS z z.property).2.2, le_abs_self T]
  have h := hbase.biUnion (fun z _ => Set.finite_range (fun k : Fin (analyticOrderNatAt riemannZeta (z : ℂ)) =>
    (⟨z, k⟩ : ZIdx)))
  change {i : ZIdx | |(i.1 : ℂ).im| ≤ T}.Finite
  exact h.subset (by rintro ⟨z, k⟩ hz; exact Set.mem_biUnion hz (Set.mem_range_self k))
/-- LEAF. Unit U-1551. Davenport chapter 15: the nontrivial zeros of bounded ordinate, with
multiplicity, are finitely many; the lab's `zeros_rect_finite` of
`PNTPort/ExplicitPsi1/Residues.lean` and `analyticOrderNatAt` give it. -/
theorem zt_finite (T : ℝ) : {i : ZIdx | |gZ i| ≤ T}.Finite := by
  apply zidx_finite_of_xi_zeros T
  have hA : AnalyticOnNhd ℂ Decomp1551b.xi (Metric.ball 0 (2 + |T|)) := by
    intro z _
    apply Differentiable.analyticAt
    unfold Decomp1551b.xi
    exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
      differentiable_completedZeta₀).add_const 1).div_const 2
  exact LeanLab.Ported.Zeta23.RvM.finite_zeros_closedBall
    (R := 2 + |T|) (r := 1 + |T|) (by linarith) hA (z₀ := 0)
    (by simp [Metric.mem_ball]; positivity) (by norm_num [Decomp1551b.xi])

private lemma zall_pos {ρ : ℂ} (h : ρ ∈ LeanLab.PNTPort.ExplicitPsi1.Zall) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hζ : ζ ρ = 0 := h.1
  refine ⟨?_, ?_⟩
  · by_contra hcon
    exact LeanLab.PNTPort.ExplicitPsi1.zeta_ne_zero_left h.2 (not_lt.mp hcon) hζ
  · by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon) hζ

/-! ### Rectangle bookkeeping for `[-(2m+1), 2] × [-T, T]` -/

private lemma rect_mem_a {a T : ℝ} (ha : a ≤ 2) (hT : 0 ≤ T) {z : ℂ} :
    z ∈ Rectangle (⟨a, -T⟩ : ℂ) ⟨2, T⟩ ↔ (a ≤ z.re ∧ z.re ≤ 2) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
  simp only [Rectangle, mem_reProdIm]
  rw [uIcc_of_le ha, uIcc_of_le (by linarith)]
  simp

private lemma rect_border_cases_a {a T : ℝ} {z : ℂ}
    (hz : z ∈ RectangleBorder (⟨a, -T⟩ : ℂ) ⟨2, T⟩) :
    z.im = -T ∨ z.re = a ∨ z.im = T ∨ z.re = 2 := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hz
  rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### The integrand `fK x` -/

private lemma fK_meromorphic {x : ℝ} (hx : 0 < x) (z : ℂ) : MeromorphicAt (fK x) z := by
  have hz := LeanLab.PNTPort.ExplicitPsi1.meromorphicAt_zeta z
  change MeromorphicAt (fun s => -(deriv ζ s / ζ s) * (x : ℂ) ^ s / s) z
  exact ((hz.deriv.div hz).neg.mul (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx z).meromorphicAt).div
    analyticAt_id.meromorphicAt

private lemma fK_analytic {x : ℝ} (hx : 0 < x) {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1)
    (hz : ζ z ≠ 0) : AnalyticAt ℂ (fK x) z := by
  change AnalyticAt ℂ (fun s => -(deriv ζ s / ζ s) * (x : ℂ) ^ s / s) z
  exact ((LeanLab.PNTPort.ExplicitPsi1.analyticAt_logDeriv h1 hz).neg.mul (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx z)).div analyticAt_id h0

private lemma fK_order {x : ℝ} (hx : 0 < x) (z : ℂ) :
    -1 ≤ meromorphicOrderAt (fK x) z := by
  have hz := LeanLab.PNTPort.ExplicitPsi1.meromorphicAt_zeta z
  rcases eq_or_ne z 0 with rfl | h0
  · have hζ0 : ζ 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
    have hH : AnalyticAt ℂ (fun s => -(deriv ζ s / ζ s) * (x : ℂ) ^ s) 0 :=
      (LeanLab.PNTPort.ExplicitPsi1.analyticAt_logDeriv (by norm_num) hζ0).neg.mul (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx 0)
    have hF : fK x = (fun s => -(deriv ζ s / ζ s) * (x : ℂ) ^ s) *
        (fun s : ℂ => s)⁻¹ := by
      funext s
      simp only [fK, logDeriv_apply, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
    have hinv : meromorphicOrderAt (fun s : ℂ => s)⁻¹ (0 : ℂ) = -1 := by
      rw [meromorphicOrderAt_inv]
      show -meromorphicOrderAt id (0 : ℂ) = -1
      rw [meromorphicOrderAt_id]
    rw [hF, meromorphicOrderAt_mul hH.meromorphicAt
      (show MeromorphicAt (fun s : ℂ => s)⁻¹ 0 from analyticAt_id.meromorphicAt.inv), hinv]
    have h := hH.meromorphicOrderAt_nonneg
    calc (-1 : WithTop ℤ) = 0 + -1 := by simp
      _ ≤ _ := add_le_add_left h _
  · have hF : fK x = (fun s => -logDeriv ζ s) * (fun s : ℂ => (x : ℂ) ^ s / s) := by
      funext s; simp only [fK, Pi.mul_apply]; ring
    have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) z :=
      (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx z).div analyticAt_id h0
    have hL : MeromorphicAt (fun s => -logDeriv ζ s) z := (hz.deriv.div hz).neg
    rw [hF, meromorphicOrderAt_mul hL hk.meromorphicAt]
    have hneg : meromorphicOrderAt (fun s => -logDeriv ζ s) z =
        meromorphicOrderAt (logDeriv ζ) z := (meromorphicOrderAt_neg (f := logDeriv ζ)).symm
    rw [hneg]
    calc (-1 : WithTop ℤ) = -1 + 0 := by simp
      _ ≤ _ := add_le_add (LeanLab.PNTPort.ExplicitPsi1.order_logDeriv_zeta_ge z) hk.meromorphicOrderAt_nonneg

private lemma fK_residue_origin {x : ℝ} (hx : 0 < x) : residue (fK x) 0 = -L0 := by
  have hζ0 : ζ 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  apply residue_eq_of_tendsto
  have hH : AnalyticAt ℂ (fun s => -(deriv ζ s / ζ s) * (x : ℂ) ^ s) 0 :=
    (LeanLab.PNTPort.ExplicitPsi1.analyticAt_logDeriv (by norm_num) hζ0).neg.mul (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx 0)
  have ht := hH.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  have hv : -(deriv ζ 0 / ζ 0) * (x : ℂ) ^ (0 : ℂ) = -L0 := by simp [L0]
  rw [hv] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  simp only [fK, logDeriv_apply, sub_zero]
  field_simp

private lemma fK_residue_one {x : ℝ} (hx : 0 < x) : residue (fK x) 1 = (x : ℂ) := by
  apply residue_eq_of_tendsto
  have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) 1 :=
    (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx 1).div analyticAt_id one_ne_zero
  have ht := (LeanLab.PNTPort.ExplicitPsi1.tendsto_logDeriv_zeta_one.mul
    (hk.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ)))).neg
  simpa only [cpow_one, div_one, neg_one_mul, neg_neg] using
    ht.congr (fun s => by simp only [fK, logDeriv_apply]; ring)

private lemma fK_residue_zero {x : ℝ} (hx : 0 < x) {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    residue (fK x) ρ = -(analyticOrderNatAt ζ ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  apply residue_eq_of_tendsto
  have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) ρ :=
    (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx ρ).div analyticAt_id h0
  have ht := ((LeanLab.PNTPort.ExplicitPsi1.tendsto_logDeriv_zeta_of_ne_one h1).mul
    (hk.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ)))).neg
  rw [show -(analyticOrderNatAt ζ ρ : ℂ) * (x : ℂ) ^ ρ / ρ =
    -((analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) by ring]
  refine ht.congr (fun s => ?_)
  simp only [fK, logDeriv_apply]
  ring

private lemma fK_residue_trivial {x : ℝ} (hx : 0 < x) (n : ℕ) :
    residue (fK x) (-2 * ((n : ℂ) + 1)) =
      (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) := by
  let ρ : ℂ := -2 * ((n : ℂ) + 1)
  have h0 : ρ ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    dsimp [ρ] at hh
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  apply residue_eq_of_tendsto
  have hk : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / z) ρ :=
    (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hx ρ).div analyticAt_id h0
  have ht := ((LeanLab.PNTPort.ExplicitPsi1.Trivial.tendsto_logDeriv_trivial n).mul
    (hk.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ)))).neg
  have heq : (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) =
      -(1 * ((x : ℂ) ^ ρ / ρ)) := by
    change (x : ℂ) ^ ρ / (2 * ((n : ℂ) + 1)) = _
    rw [show 2 * ((n : ℂ) + 1) = -ρ by dsimp [ρ]; ring, div_neg]
    simp
  rw [heq]
  refine ht.congr (fun z => ?_)
  simp only [fK, logDeriv_apply]
  ring

/-! ### The contour as `Jc`, `HorI` and `LeftI` -/

private lemma rect_decomp_a (x : ℝ) (m : ℕ) (T : ℝ) :
    RectangleIntegral' (fK x) (⟨-(2 * (m : ℝ) + 1), -T⟩ : ℂ) ⟨2, T⟩ =
      (1 / (2 * Real.pi * I)) * (HorI x m (-T) - HorI x m T
        + ((2 * Real.pi : ℝ) : ℂ) * I * Jc x T - I * LeftI x m T) := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, HorI,
    LeftI, Jc]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  norm_num
  field_simp

/-! ### The residue identity itself -/

/-- LEAF. Unit U-1551. Davenport chapter 17, the residue theorem on the rectangle
`[-(2m+1), 2] × [-T, T]`, `x > 1`, `T > 0`, no zero of ζ on the horizontal edges:
`i ∫_{-T}^{T} f(2+it) dt - ∫ f(σ+iT) dσ + ∫ f(σ-iT) dσ - i ∫_{-T}^{T} f(-(2m+1)+it) dt
 = 2πi (x - Σ_{|γ| ≤ T} x^ρ/ρ - ζ'/ζ(0) + Σ_{k=1}^{m} x^{-2k}/(2k))`.
The residues: `x` at `s = 1`; `-m_ρ x^ρ/ρ` at a nontrivial zero; `-ζ'/ζ(0)` at `s = 0`;
`x^{-2k}/(2k)` at the simple trivial zero `-2k`. The lab's `rect_explicit` does the same for
the kernel `x^s/(s(s+1))`. -/
theorem rect_identity (hfin : ∀ T : ℝ, {i : ZIdx | |gZ i| ≤ T}.Finite)
    (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : 0 < T)
    (hnz : ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧ ζ ((σ : ℂ) - T * I) ≠ 0) (m : ℕ) :
    I * ((2 * Real.pi : ℝ) : ℂ) * Jc x T - HorI x m T + HorI x m (-T) - I * LeftI x m T
      = ((2 * Real.pi : ℝ) : ℂ) * I * ((x : ℂ) - ZS x T - L0 + (TrivU x m : ℂ)) := by
  classical
  have hx0 : 0 < x := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ha2 : -(2 * (m : ℝ) + 1) ≤ 2 := by linarith
  have hC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]; positivity
  have hmem := fun z => rect_mem_a (a := -(2 * (m : ℝ) + 1)) (T := T) ha2 hT.le (z := z)
  set R : Set ℂ := Rectangle (⟨-(2 * (m : ℝ) + 1), -T⟩ : ℂ) ⟨2, T⟩ with hRdef
  have h0R : (0 : ℂ) ∈ R := by
    rw [hRdef, hmem]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨⟨by linarith, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  have h1R : (1 : ℂ) ∈ R := by
    rw [hRdef, hmem]
    simp only [Complex.one_re, Complex.one_im]
    exact ⟨⟨by linarith, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  have hζ0 : ζ 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hzfin : (R ∩ riemannZetaZeros).Finite := by
    rw [hRdef]
    exact IsCompact.inter_riemannZetaZeros_finite (isCompact_uIcc.reProdIm isCompact_uIcc)
  set Zf : Finset ℂ := hzfin.toFinset with hZf
  have hZfmem : ∀ ρ : ℂ, ρ ∈ Zf ↔ ρ ∈ R ∧ ζ ρ = 0 := by
    intro ρ
    rw [hZf, Set.Finite.mem_toFinset]
    exact ⟨fun h => h, fun h => h⟩
  have hgood : ∀ z ∈ R, z ≠ 0 → z ≠ 1 → ζ z ≠ 0 → 0 ≤ meromorphicOrderAt (fK x) z :=
    fun z _ h0 h1 hz => (fK_analytic hx0 h0 h1 hz).meromorphicOrderAt_nonneg
  set Sf : Finset LeanLab.PNTPort.ExplicitPsi1.Zall := Zf.subtype (fun ρ : ℂ => ρ ∈ (LeanLab.PNTPort.ExplicitPsi1.Zall : Set ℂ)) with hSf
  have hSfZf : ∀ ρ ∈ Sf, (ρ : ℂ) ∈ Zf := fun ρ hρ => Finset.mem_subtype.mp hρ
  have hSfZall : ∀ ρ ∈ Sf, (ρ : ℂ) ∈ LeanLab.PNTPort.ExplicitPsi1.Zall := fun ρ _ => ρ.2
  -- the pole set: `0`, `1` and every zero of `ζ` in the rectangle
  set P : Finset ℂ := insert 0 (insert 1 Zf) with hP
  have h0not : (0 : ℂ) ∉ insert 1 Zf := by
    rw [Finset.mem_insert, not_or]
    exact ⟨zero_ne_one, fun h => hζ0 ((hZfmem 0).mp h).2⟩
  have h1not : (1 : ℂ) ∉ Zf := by
    intro h
    exact riemannZeta_one_ne_zero ((hZfmem 1).mp h).2
  have hPR : ∀ z ∈ P, z ∈ R := by
    intro z hz
    rw [hP] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h0R
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h1R
    exact ((hZfmem z).mp hz).1
  have hpoles : ∀ z ∈ R, meromorphicOrderAt (fK x) z < 0 → z ∈ P := by
    intro z hz hneg
    by_contra hns
    have h0 : z ≠ 0 := by
      intro e
      apply hns
      rw [hP, e]
      exact Finset.mem_insert_self _ _
    have h1 : z ≠ 1 := by
      intro e
      apply hns
      rw [hP, e]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hZf : z ∉ Zf := by
      intro e
      apply hns
      rw [hP]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem e)
    have hζ : ζ z ≠ 0 := fun hζz => hZf ((hZfmem z).mpr ⟨hz, hζz⟩)
    exact absurd (hgood z hz h0 h1 hζ) (not_le.mpr hneg)
  have hleft : ∀ t : ℝ, ζ (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t
    refine LeanLab.PNTPort.ExplicitPsi1.Trivial.zeta_ne_zero_of_re_neg (s := (((-(2 * (m : ℝ) + 1)) : ℝ) : ℂ) + t * I) ?_ ?_
    · have hre : ((((-(2 * (m : ℝ) + 1)) : ℝ) : ℂ) + t * I).re = -(2 * (m : ℝ) + 1) := by
        simp
      rw [hre]
      linarith
    · intro k hk
      have hre := congrArg Complex.re hk
      have h1 : (1 : ℝ) - (-(2 * (m : ℝ) + 1)) = 2 * (k : ℝ) + 1 := by
        simpa using hre
      have h2 : 2 * (k : ℝ) = 2 * (m : ℝ) + 1 := by linarith
      have hZ : (2 * k : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast h2
      omega
  have hborder : ∀ z ∈ RectangleBorder (⟨-(2 * (m : ℝ) + 1), -T⟩ : ℂ) ⟨2, T⟩, ζ z ≠ 0 := by
    intro z hzb
    have hzR : z ∈ R := by rw [hRdef]; exact rectangleBorder_subset_rectangle _ _ hzb
    have hz2 : z.re ≤ 2 := ((hmem z).mp hzR).1.2
    have hzz : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
    have e : ((z.re : ℂ) + ((-T : ℝ) : ℂ) * I) = ((z.re : ℂ) - T * I) := by push_cast; ring
    rcases rect_border_cases_a hzb with h | h | h | h
    · rw [hzz, h, e]; exact (hnz z.re hz2).2
    · rw [hzz, h]; exact hleft z.im
    · rw [hzz, h]; exact (hnz z.re hz2).1
    · rw [hzz, h]
      exact riemannZeta_ne_zero_of_one_le_re (s := ((2 : ℂ) + (z.im : ℂ) * I)) (by simp)
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := fK x)
    (z := (⟨-(2 * (m : ℝ) + 1), -T⟩ : ℂ)) (w := ⟨2, T⟩)
    (by simp; linarith) (by simp; linarith)
    (fun z _ => fK_meromorphic hx0 z)
    (by
      rw [Set.disjoint_left]
      intro z hzb hneg
      simp only [Set.mem_ofPred_eq] at hneg
      have hzR : z ∈ R := by rw [hRdef]; exact rectangleBorder_subset_rectangle _ _ hzb
      have hζ := hborder z hzb
      rcases rect_border_cases_a hzb with h | h | h | h
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; try linarith)
          (by intro e; rw [e] at h; simp at h; try linarith) hζ) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; try linarith)
          (by intro e; rw [e] at h; simp at h; try linarith) hζ) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; try linarith)
          (by intro e; rw [e] at h; simp at h; try linarith) hζ) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; try linarith)
          (by intro e; rw [e] at h; simp at h; try linarith) hζ) (not_le.mpr hneg))
    (by
      apply (P : Set ℂ).toFinite.subset
      intro z ⟨hz, hneg⟩
      exact hpoles z hz hneg)
    (fun z _ => fK_order hx0 z)
  have hRres : RectangleIntegral' (fK x) (⟨-(2 * (m : ℝ) + 1), -T⟩ : ℂ) ⟨2, T⟩ =
      sumResiduesIn (fK x) (R ∩ {z | meromorphicOrderAt (fK x) z < 0}) := by
    rw [hres, hRdef]
  have hS : R ∩ {z | meromorphicOrderAt (fK x) z < 0} =
      (P : Set ℂ) ∩ {z | meromorphicOrderAt (fK x) z < 0} := by
    ext z
    simp only [mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hpoles z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩; exact ⟨hPR z hz, hneg⟩
  have hinjT : ∀ a b : ℕ, (-2 * ((a : ℂ) + 1)) = (-2 * ((b : ℂ) + 1)) → a = b := by
    intro a b h
    have h' : ((a : ℂ) + 1) = ((b : ℂ) + 1) :=
      mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) h
    have h'' : (a : ℂ) = (b : ℂ) := add_right_cancel h'
    exact_mod_cast h''
  have hZTf : Zf.filter (fun ρ => ρ.re < 0)
      = (Finset.range m).image (fun k : ℕ => -2 * ((k : ℂ) + 1)) := by
    ext ρ
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hρ, hlt⟩
      obtain ⟨hρR, hρζ⟩ := (hZfmem ρ).mp hρ
      obtain ⟨⟨hza, hz2⟩, hzim, hzim2⟩ := (hmem ρ).mp hρR
      obtain ⟨n, hn⟩ := LeanLab.PNTPort.ExplicitPsi1.Trivial.zero_of_re_neg hlt hρζ
      have h1' : ((n + 1 : ℕ) : ℝ) < (m : ℝ) + 1 := by
        have h := hza
        have hzre : ρ.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
        rw [hzre] at h
        push_cast at h ⊢
        linarith
      have h2 : n + 1 < m + 1 := by exact_mod_cast h1'
      exact ⟨n, Finset.mem_range.mpr (by omega), hn.symm⟩
    · rintro ⟨n, hn, hnρ⟩
      have hnm : (n : ℝ) < (m : ℝ) := by
        have h' : n < m := Finset.mem_range.mp hn
        exact_mod_cast h'
      have hle : ((n : ℝ) + 1) ≤ (m : ℝ) := by
        have h' : n + 1 ≤ m := by
          have h2 : n < m := Finset.mem_range.mp hn
          omega
        exact_mod_cast h'
      have hval : (-2 * ((n : ℂ) + 1)) = (((-2 * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
        push_cast; ring
      have hζ0 : ζ (-2 * ((n : ℂ) + 1)) = 0 := riemannZeta_neg_two_mul_nat_add_one n
      have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
        rw [hval, Complex.ofReal_re]
      have him : (-2 * ((n : ℂ) + 1)).im = 0 := by
        rw [hval, Complex.ofReal_im]
      have hR : (-2 * ((n : ℂ) + 1)) ∈ R := by
        rw [hRdef, hmem, hre, him]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · linarith [hle]
        · linarith [Nat.cast_nonneg (α := ℝ) n]
        · linarith [hT]
        · linarith [hT]
      have hlt : (-2 * ((n : ℂ) + 1)).re < 0 := by
        rw [hval, Complex.ofReal_re]
        linarith
      rw [← hnρ]
      exact ⟨(hZfmem _).mpr ⟨hR, hζ0⟩, hlt⟩
  have hZNf : Zf.filter (fun ρ => ¬ ρ.re < 0)
      = Sf.image (fun σ : LeanLab.PNTPort.ExplicitPsi1.Zall => (σ : ℂ)) := by
    ext ρ
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hρ, hge⟩
      have hρζ : ζ ρ = 0 := ((hZfmem ρ).mp hρ).2
      exact ⟨⟨ρ, hρζ, by linarith⟩, Finset.mem_subtype.mpr hρ, rfl⟩
    · rintro ⟨σ, hσ, hσρ⟩
      have hσZf : (σ : ℂ) ∈ Zf := Finset.mem_subtype.mp hσ
      have hZ : (σ : ℂ) ∈ LeanLab.PNTPort.ExplicitPsi1.Zall := σ.2
      obtain ⟨hpos, -⟩ := zall_pos hZ
      rw [← hσρ]
      exact ⟨hσZf, by linarith⟩
  -- the trivial-zero residues sum to `TrivU`
  have hterm : ∀ k : ℕ, (x : ℂ) ^ (-2 * ((k : ℂ) + 1)) / (2 * ((k : ℂ) + 1)) =
      ((((x ^ 2)⁻¹) ^ (k + 1) / (2 * ((k : ℝ) + 1)) : ℝ) : ℂ) := by
    intro k
    have h1 : (x : ℂ) ^ (-2 * ((k : ℂ) + 1)) = ((((x ^ 2)⁻¹) ^ (k + 1) : ℝ) : ℂ) := by
      rw [show (-2 * ((k : ℂ) + 1)) = (-(((2 * (k + 1) : ℕ) : ℂ))) by push_cast; ring]
      rw [Complex.cpow_neg, Complex.cpow_natCast]
      push_cast
      rw [pow_mul, inv_pow]
    rw [h1]
    push_cast
    ring
  have hsumTriv : ∑ ρ ∈ Zf.filter (fun ρ => ρ.re < 0), residue (fK x) ρ = (TrivU x m : ℂ) := by
    rw [hZTf, Finset.sum_image (f := fun z : ℂ => residue (fK x) z)
      (g := fun k : ℕ => -2 * ((k : ℂ) + 1)) (fun a _ b _ h => hinjT a b h), TrivU,
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [fK_residue_trivial hx0 k, hterm k]
  -- the nontrivial zeros
  have hSfsum : ∑ ρ ∈ Sf, residue (fK x) (ρ : ℂ) =
      -∑ ρ ∈ Sf, (analyticOrderNatAt ζ (ρ : ℂ) : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have hZ : (ρ : ℂ) ∈ LeanLab.PNTPort.ExplicitPsi1.Zall := hSfZall ρ hρ
    obtain ⟨hpos, hlt⟩ := zall_pos hZ
    have h0 : (ρ : ℂ) ≠ 0 := by intro e; rw [e] at hpos; simp at hpos
    have h1 : (ρ : ℂ) ≠ 1 := by intro e; rw [e] at hlt; simp at hlt
    rw [fK_residue_zero hx0 h0 h1]
    ring
  have hsumNt : ∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ.re < 0), residue (fK x) ρ =
      -∑ ρ ∈ Sf, (analyticOrderNatAt ζ (ρ : ℂ) : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ)) := by
    rw [hZNf, Finset.sum_image (f := fun z : ℂ => residue (fK x) z)
      (g := fun σ : LeanLab.PNTPort.ExplicitPsi1.Zall => (σ : ℂ)) (fun a _ b _ h => Subtype.val_injective h), hSfsum]
  have hsplit : ∑ ρ ∈ Zf, residue (fK x) ρ = (TrivU x m : ℂ)
      + (-∑ ρ ∈ Sf, (analyticOrderNatAt ζ (ρ : ℂ) : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ))) := by
    rw [← Finset.sum_filter_add_sum_filter_not Zf (fun ρ => ρ.re < 0)
      (fun ρ => residue (fK x) ρ), hsumTriv, hsumNt]
  -- `ZS` is the nontrivial zero sum
  have hZs : ZS x T = ∑ ρ ∈ Sf,
      (analyticOrderNatAt ζ (ρ : ℂ) : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ)) := by
    have hZTmem : ∀ i : ZIdx, i ∈ ZT T ↔ |gZ i| ≤ T := by
      intro i
      simp only [ZT]
      split_ifs with h
      · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      · exact absurd (hfin T) h
    have hsigma : Sf.sigma (fun ρ => (Finset.univ : Finset (Fin (analyticOrderNatAt ζ (ρ : ℂ)))))
        = ZT T := by
      ext i
      obtain ⟨ρ, k⟩ := i
      rw [Finset.mem_sigma, hZTmem]
      constructor
      · rintro ⟨hρ, -⟩
        have hZ := (hZfmem (ρ : ℂ)).mp (hSfZf ρ hρ)
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hmem (ρ : ℂ)).mp hZ.1
        simp only [gZ]
        exact abs_le.mpr ⟨by linarith, h4⟩
      · intro hk
        obtain ⟨hζ, -⟩ := ρ.2
        obtain ⟨hpos, hlt⟩ := zall_pos (ρ := (ρ : ℂ)) ρ.2
        refine ⟨Finset.mem_subtype.mpr ?_, Finset.mem_univ _⟩
        rw [hZfmem]
        exact ⟨(hmem (ρ : ℂ)).mpr ⟨⟨by linarith, by linarith⟩, abs_le.mp hk⟩, hζ⟩
    unfold ZS
    rw [← hsigma, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have hstep : ∑ k ∈ (Finset.univ : Finset (Fin (analyticOrderNatAt ζ (ρ : ℂ)))),
        (x : ℂ) ^ ((⟨ρ, k⟩ : ZIdx).1 : ℂ) / ((⟨ρ, k⟩ : ZIdx).1 : ℂ)
        = ∑ _k ∈ (Finset.univ : Finset (Fin (analyticOrderNatAt ζ (ρ : ℂ)))),
            ((x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ)) :=
      Finset.sum_congr rfl (fun k _ => rfl)
    rw [hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- assemble
  have hmain : RectangleIntegral' (fK x) (⟨-(2 * (m : ℝ) + 1), -T⟩ : ℂ) ⟨2, T⟩ =
      (x : ℂ) - ZS x T - L0 + (TrivU x m : ℂ) := by
    rw [hRres, sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
        residue_eq_zero_of_not_pole_of_meromorphicAt (fK_meromorphic hx0 z) (not_lt.mp hz)),
      sumResiduesIn, Finset.tsum_subtype' P (fun z => residue (fK x) z)]
    rw [hP, Finset.sum_insert h0not, Finset.sum_insert h1not, hsplit,
      fK_residue_origin hx0, fK_residue_one hx0, hZs]
    ring
  rw [← hmain, rect_decomp_a x m T]
  have h2πI : ((2 * Real.pi : ℝ) : ℂ) * I ≠ 0 := mul_ne_zero hC I_ne_zero
  field_simp
  push_cast
  ring

/-- LEAF. Unit U-1551. Davenport chapter 17: on `Re s = -(2m+1)`, `|ζ'/ζ(s)| ≪ log(2|s|)`, and
`|x^s/s| ≤ x^{-(2m+1)}/(2m+1)`, so the left edge tends to 0 as `m → ∞`, for `x > 1`. -/
theorem left_edge_limit (x : ℝ) (hx : 1 < x) (T : ℝ) :
    Tendsto (fun m : ℕ => LeftI x m T) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  /- The local functional equation proof adapts Mathlib/NumberTheory/LSeries/RiemannZetaLogDeriv.lean.
     Copyright (c) 2026 Terence Tao. Released under Apache 2.0. -/
  have hfe : ∀ s : ℂ, 1 < s.re → cos (Real.pi * s / 2) ≠ 0 →
      logDeriv ζ (1 - s) = -logDeriv ζ s + log (2 * Real.pi) - digamma s
        + Real.pi / 2 * tan (Real.pi * s / 2) := by
    intro s hs hc
    have h2π : 2 * (Real.pi : ℂ) ≠ 0 := mod_cast by positivity
    have hdG := (hasDerivAt_Gamma_of_re_pos (by linarith : 0 < s.re)).differentiableAt
    have hdζ : DifferentiableAt ℂ ζ (1 - s) := differentiableAt_riemannZeta (by
      intro h; have := congrArg re h; simp at this; linarith)
    have hG := Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
    have hz := riemannZeta_ne_zero_of_one_lt_re hs
    have hzs : s ≠ 1 := by intro h; norm_num [h] at hs
    have hpow := (hasDerivAt_neg' s).differentiableAt.const_cpow (Or.inl h2π)
    have hcos : HasDerivAt (fun z : ℂ => Real.pi * z / 2) (Real.pi / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul (Real.pi : ℂ)).div_const 2
    have he : ζ ∘ (1 - ·) =ᶠ[𝓝 s]
        fun z => 2 * (2 * Real.pi) ^ (-z) * Gamma z * cos (Real.pi * z / 2) * ζ z := by
      filter_upwards [(isOpen_re_gt 1).mem_nhds hs] with z hz
      exact riemannZeta_one_sub (LeanLab.PNTPort.ZetaZeros.not_neg_nat_of_re_pos (by linarith))
        (by intro h; norm_num [h] at hz)
    have he := (logDeriv_congr_nhds he).eq_of_nhds
    rw [logDeriv_comp, logDeriv_fun_mul, logDeriv_fun_mul, logDeriv_fun_mul, logDeriv_fun_mul,
      logDeriv_fun_comp (f := cos), ← digamma_def] at he
    <;> first | fun_prop | simp_all
    <;> try grind [differentiableAt_riemannZeta, Gamma_ne_zero,
      LeanLab.PNTPort.ZetaZeros.not_neg_nat_of_re_pos]
  have htan : ∀ (m : ℕ) (t : ℝ),
      ‖tan (Real.pi * (((2 * (m : ℝ) + 2 : ℝ) : ℂ) - t * I) / 2)‖ ≤ 1 := by
    intro m t
    have he : (Real.pi : ℂ) * (((2 * (m : ℝ) + 2 : ℝ) : ℂ) - t * I) / 2 =
        ((m + 1 : ℕ) : ℂ) * Real.pi - ((Real.pi * t / 2 : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, tan_nat_mul_pi_sub, norm_neg, tan_mul_I, norm_mul, Complex.norm_I, mul_one]
    rw [← Complex.ofReal_tanh, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_lt.mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le
  have hψcont : Continuous (fun t : ℝ => digamma ((2 : ℂ) - t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hg := LeanLab.PNTPort.ZetaZeros.gamma_analyticAt (w := (2 : ℂ) - t * I) (by norm_num)
    have hn : Gamma ((2 : ℂ) - t * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
    have hc := (hg.deriv.div hg hn).continuousAt
    exact ContinuousAt.comp (f := fun u : ℝ => (2 : ℂ) - u * I) hc (by fun_prop)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψcont.continuousOn
    (s := Icc (-|T|) |T|)
  let c : ℝ := ‖deriv ζ ((3 / 2 : ℝ) : ℂ) / ζ ((3 / 2 : ℝ) : ℂ)‖
  let A : ℝ := c + |M| + 4
  have hA : 0 ≤ A := by dsimp [A, c]; positivity
  have hlog : ∀ (m : ℕ) (t : ℝ), |t| ≤ |T| →
      ‖logDeriv ζ (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I)‖ ≤ A + 2 * m := by
    intro m t ht
    let w : ℂ := ((2 * (m : ℝ) + 2 : ℝ) : ℂ) - t * I
    have hwre : w.re = 2 * m + 2 := by simp [w]
    have hw1 : 1 < w.re := by rw [hwre]; have := Nat.cast_nonneg (α := ℝ) m; linarith
    have hodd : ∀ k : ℤ, w ≠ 2 * k + 1 := by
      intro k hk
      have he := congrArg re hk
      simp [w] at he
      have he' : ((2 * (m : ℤ) + 2 : ℤ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by push_cast; linarith
      have hh : (2 * (m : ℤ) + 2 : ℤ) = 2 * k + 1 := by exact_mod_cast he'
      omega
    have hc := LeanLab.PNTPort.ZetaZeros.cos_ne_zero_of_not_odd hodd
    have he := hfe w hw1 hc
    have hw : 1 - w = (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I) := by dsimp [w]; push_cast; ring
    rw [hw] at he
    have hr : ‖logDeriv ζ w‖ ≤ c :=
      LeanLab.PNTPort.ExplicitPsi1.Trivial.logDeriv_right_le (by rw [hwre]; have := Nat.cast_nonneg (α := ℝ) m; linarith)
    have hψ : ‖digamma w‖ ≤ |M| + 2 * m := by
      have hb : ∀ k : ℕ, ‖((2 : ℂ) - t * I + k)⁻¹‖ ≤ 1 := by
        intro k
        rw [norm_inv]
        have hh := abs_re_le_norm ((2 : ℂ) - t * I + k)
        have hre : ((2 : ℂ) - t * I + k).re = 2 + k := by simp
        have hk := Nat.cast_nonneg (α := ℝ) k
        rw [hre, abs_of_nonneg (by linarith)] at hh
        exact (inv_le_one₀ (by linarith : 0 < ‖(2 : ℂ) - t * I + k‖)).mpr (by linarith)
      have hsum : ‖∑ k ∈ Finset.range (2 * m), ((2 : ℂ) - t * I + k)⁻¹‖ ≤ 2 * m := by
        refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ _k ∈ Finset.range (2 * m), (1 : ℝ) := Finset.sum_le_sum (fun k _ => hb k)
          _ = _ := by simp
      have hw' : w = (2 : ℂ) - t * I + (2 * m : ℕ) := by dsimp [w]; push_cast; ring
      rw [hw', digamma_apply_add_nat (LeanLab.PNTPort.ZetaZeros.not_neg_nat_of_re_pos (by norm_num))]
      have hh := hM t (abs_le.mp ht)
      exact (norm_add_le _ _).trans (by linarith [le_abs_self M])
    have htrig : ‖(Real.pi : ℂ) / 2 * tan (Real.pi * w / 2)‖ ≤ 2 := by
      have hh := htan m t
      have hp : ‖(Real.pi : ℂ) / 2‖ ≤ 2 := by norm_num [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; linarith [Real.pi_lt_four]
      rw [norm_mul]
      exact (mul_le_mul hp hh (norm_nonneg _) (by norm_num)).trans (by norm_num)
    rw [he]
    have hn := LeanLab.PNTPort.ExplicitPsi1.Trivial.norm_log_two_pi_le
    calc
      _ ≤ ‖logDeriv ζ w‖ + ‖log (2 * (Real.pi : ℂ))‖ + ‖digamma w‖ +
          ‖(Real.pi : ℂ) / 2 * tan (Real.pi * w / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (by rw [norm_neg])) le_rfl)) le_rfl)
      _ ≤ A + 2 * m := by dsimp [A]; linarith
  have hbound : ∀ m : ℕ, ‖LeftI x m T‖ ≤ (2 * |T|) * ((A + 1) * x ^ (-(2 * (m : ℝ) + 1))) := by
    intro m
    unfold LeftI
    have hh : ∀ t ∈ Set.uIoc (-T) T, ‖fK x (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I)‖ ≤
        (A + 1) * x ^ (-(2 * (m : ℝ) + 1)) := by
      intro t ht
      have ht' : |t| ≤ |T| := by
        rcases le_or_gt 0 T with hp | hp
        · rw [Set.uIoc_of_le (by linarith)] at ht
          rw [abs_of_nonneg hp, abs_le]
          exact ⟨ht.1.le, ht.2⟩
        · rw [Set.uIoc_of_ge (by linarith)] at ht
          rw [abs_of_neg hp, abs_le]
          constructor <;> linarith [ht.1, ht.2]
      have hd : 2 * (m : ℝ) + 1 ≤ ‖((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I‖ := by
        have h := abs_re_le_norm (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I)
        have hre : (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I).re = -(2 * (m : ℝ) + 1) := by simp
        rw [hre, abs_neg, abs_of_nonneg (by positivity)] at h
        exact h
      have hd0 : 0 < ‖((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I‖ := by have := Nat.cast_nonneg (α := ℝ) m; linarith
      unfold fK
      rw [norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      apply (div_le_iff₀ hd0).mpr
      have hh := mul_le_mul_of_nonneg_right (hlog m t ht') (Real.rpow_nonneg hx0.le (-(2 * (m : ℝ) + 1)))
      have hratio : A + 2 * m ≤ (A + 1) * ‖((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + t * I‖ := by
        have hm := Nat.cast_nonneg (α := ℝ) m
        have hp := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ A + 1)
        nlinarith
      have hh' := mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hx0.le (-(2 * (m : ℝ) + 1)))
      nlinarith
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hh
    have he : |T - -T| = 2 * |T| := by rw [sub_neg_eq_add, ← two_mul, abs_mul]; norm_num
    rw [he] at h
    exact h.trans_eq (mul_comm _ _)
  have hpow : ∀ m : ℕ, x ^ (-(2 * (m : ℝ) + 1)) = ((x ^ 2)⁻¹) ^ m * x⁻¹ := by
    intro m
    rw [Real.rpow_neg hx0.le,
      show 2 * (m : ℝ) + 1 = ((2 * m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      pow_add, pow_one, pow_mul, mul_inv, inv_pow]
  have hlim : Tendsto (fun m : ℕ => (2 * |T|) * ((A + 1) * x ^ (-(2 * (m : ℝ) + 1)))) atTop (𝓝 0) := by
    simp_rw [hpow]
    have hp : (x ^ 2)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr (by nlinarith)
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp).mul_const x⁻¹).const_mul (A + 1) |>.const_mul (2 * |T|)
    simpa using hh
  exact squeeze_zero_norm hbound hlim

/-- LEAF. Unit U-1551. Davenport chapter 17: if ζ has no zero on `{σ + iT : σ ≤ 2}`,
`|T| ≥ 2`, and `|ζ'/ζ(σ + iT)| ≤ B (1 + |σ|)` there, then `σ ↦ f(σ + iT)` is integrable on
`(-∞, 2]`, as `x^σ` decays for `x > 1`, and the edges over `[-(2m+1), 2]` converge to it. -/
theorem hor_tendsto (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : 2 ≤ |T|) (B : ℝ)
    (hb : ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧
      ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ B * (1 + |σ|)) :
    Tendsto (fun m : ℕ => HorI x m T) atTop (𝓝 (HorInf x T)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 ≤ B := by
    have h := (hb 0 (by norm_num)).2
    norm_num at h
    exact (norm_nonneg _).trans h
  have hnorm : ∀ σ : ℝ, σ ≤ 2 → ‖fK x ((σ : ℂ) + T * I)‖ ≤ 2 * B * x ^ σ := by
    intro σ hσ
    have hre : |σ| ≤ ‖(σ : ℂ) + T * I‖ := by simpa using abs_re_le_norm ((σ : ℂ) + T * I)
    have him : |T| ≤ ‖(σ : ℂ) + T * I‖ := by simpa using abs_im_le_norm ((σ : ℂ) + T * I)
    have hpos : 0 < ‖(σ : ℂ) + T * I‖ := by linarith
    unfold fK
    rw [norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul, mul_zero, sub_zero, add_zero]
    apply (div_le_iff₀ hpos).mpr
    have hp : 0 ≤ x ^ σ := Real.rpow_nonneg hx0.le _
    have h1 := mul_le_mul_of_nonneg_right (hb σ hσ).2 hp
    have h2 : B * (1 + |σ|) ≤ 2 * B * ‖(σ : ℂ) + T * I‖ := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hp
    nlinarith
  have hcont : ContinuousOn (fun σ : ℝ => fK x ((σ : ℂ) + T * I)) (Set.Iic 2) := by
    intro σ hσ
    have hs0 : (σ : ℂ) + T * I ≠ 0 := by
      intro h; have hh := congrArg im h; simp at hh; rw [hh] at hT; norm_num at hT
    have hs1 : (σ : ℂ) + T * I ≠ 1 := by
      intro h; have hh := congrArg im h; simp at hh; rw [hh] at hT; norm_num at hT
    have hl : ContinuousAt (fun σ : ℝ => logDeriv ζ ((σ : ℂ) + T * I)) σ := by
      have hh := (LeanLab.PNTPort.ExplicitPsi1.analyticAt_logDeriv hs1 (hb σ hσ).1).continuousAt
      have hs : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) σ := by fun_prop
      exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + T * I) hh hs
    have hp : ContinuousAt (fun σ : ℝ => (x : ℂ) ^ ((σ : ℂ) + T * I)) σ := by
      fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr hx0.ne'))
    exact ((hl.neg.mul hp).div (by fun_prop) hs0).continuousWithinAt
  have hi : IntegrableOn (fun σ : ℝ => fK x ((σ : ℂ) + T * I)) (Set.Iic 2) := by
    have hdom : IntegrableOn (fun σ : ℝ => 2 * B * x ^ σ) (Set.Iic 2) := by
      have hh := (integrableOn_exp_mul_Iic (Real.log_pos hx) 2).const_mul (2 * B)
      simpa [IntegrableOn, Real.rpow_def_of_pos hx0, mul_comm] using hh
    exact hdom.mono' (hcont.aestronglyMeasurable measurableSet_Iic) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Iic] with σ hσ
      exact hnorm σ hσ)
  apply intervalIntegral_tendsto_integral_Iic 2 hi
  have h : Tendsto (fun m : ℕ => (2 : ℝ) * m + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop)
  exact tendsto_neg_atTop_atBot.comp h

/-- LEAF. Unit U-1551. Davenport chapter 17: along heights `|T_n| ≥ n + 2` with
`|ζ'/ζ(σ + iT_n)| ≤ C log²|T_n| (1 + |σ|)` for `σ ≤ 2`,
`|∫_{-∞}^{2} f(σ + iT_n) dσ| ≤ C log²|T_n| / |T_n| · ∫_{-∞}^{2} (1 + |σ|) x^σ dσ → 0`. -/
theorem hor_small (x : ℝ) (hx : 1 < x) (T : ℕ → ℝ) (C : ℝ) (hT : ∀ n : ℕ, (n : ℝ) + 2 ≤ |T n|)
    (hb : ∀ n : ℕ, ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T n * I) ≠ 0 ∧
      ‖logDeriv ζ ((σ : ℂ) + T n * I)‖ ≤ C * Real.log |T n| ^ 2 * (1 + |σ|)) :
    Tendsto (fun n : ℕ => HorInf x (T n)) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  have hC : 0 ≤ C := by
    have h := (hb 0 0 (by norm_num)).2
    norm_num at h
    have ht := hT 0
    norm_num at ht
    have hl : 0 < Real.log |T 0| := Real.log_pos (by linarith)
    rw [Real.log_abs] at hl
    have hn := norm_nonneg (logDeriv ζ ((0 : ℂ) + T 0 * I))
    simp only [zero_add] at hn
    nlinarith [sq_pos_of_pos hl]
  have hweight : IntegrableOn (fun σ : ℝ => (1 + |σ|) * x ^ σ) (Set.Iic 2) := by
    have hw : IntegrableOn (fun σ : ℝ => (1 + |σ|) * Real.exp (Real.log x * σ)) (Set.Iic 2) := by
      have ha : 0 < Real.log x := Real.log_pos hx
      have hexp := integrableOn_exp_mul_Iic ha 0
      have hpow : IntegrableOn (fun u : ℝ => u * Real.exp (-Real.log x * u)) (Ioi 0) := by
        simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) (by norm_num) ha)
      have hneg : IntegrableOn (fun σ : ℝ => |σ| * Real.exp (Real.log x * σ)) (Iic 0) := by
        rw [integrableOn_Iic_iff_integrableOn_Iio]
        have h := IntegrableOn.comp_neg_Iio (c := (0 : ℝ)) (by simpa using hpow)
        refine h.congr_fun ?_ measurableSet_Iio
        intro σ hσ
        change σ < 0 at hσ
        dsimp only
        rw [abs_of_neg hσ]
        congr 2
        ring
      have hleft : IntegrableOn (fun σ : ℝ => (1 + |σ|) * Real.exp (Real.log x * σ)) (Iic 0) := by
        exact (hexp.add hneg).congr_fun (fun σ _ => by dsimp; ring) measurableSet_Iic
      have hright : IntegrableOn (fun σ : ℝ => (1 + |σ|) * Real.exp (Real.log x * σ)) (Icc 0 2) := by
        apply ContinuousOn.integrableOn_Icc
        fun_prop
      have h := hleft.union hright
      have heq : Iic (0 : ℝ) ∪ Icc 0 2 = Iic 2 := by
        ext σ
        simp only [mem_union, mem_Iic, mem_Icc]
        constructor
        · rintro (h | h) <;> linarith
        · intro h
          by_cases h0 : σ ≤ 0
          · exact Or.inl h0
          · exact Or.inr ⟨by linarith, h⟩
      rwa [heq] at h
    simpa [Real.rpow_def_of_pos hx0, mul_comm] using hw
  have hnorm : ∀ n : ℕ, ∀ σ : ℝ, σ ≤ 2 → ‖fK x ((σ : ℂ) + T n * I)‖ ≤
      (C * Real.log |T n| ^ 2 / |T n|) * ((1 + |σ|) * x ^ σ) := by
    intro n σ hσ
    have ht : 0 < |T n| := by have := hT n; have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hden : |T n| ≤ ‖(σ : ℂ) + T n * I‖ := by simpa using abs_im_le_norm ((σ : ℂ) + T n * I)
    unfold fK
    rw [norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul, mul_zero, sub_zero, add_zero]
    calc
      _ ≤ (C * Real.log |T n| ^ 2 * (1 + |σ|) * x ^ σ) / ‖(σ : ℂ) + T n * I‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hb n σ hσ).2
          (Real.rpow_nonneg hx0.le _)) (norm_nonneg _)
      _ ≤ (C * Real.log |T n| ^ 2 * (1 + |σ|) * x ^ σ) / |T n| :=
        div_le_div_of_nonneg_left (by positivity) ht hden
      _ = _ := by ring
  let W : ℝ := ∫ σ in Set.Iic (2 : ℝ), (1 + |σ|) * x ^ σ
  have hbound : ∀ n : ℕ, ‖HorInf x (T n)‖ ≤ (C * Real.log |T n| ^ 2 / |T n|) * W := by
    intro n
    have h := norm_integral_le_of_norm_le (hweight.const_mul (C * Real.log |T n| ^ 2 / |T n|)) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Iic] with σ hσ
      exact hnorm n σ hσ)
    simpa only [HorInf, integral_const_mul] using h
  have ht : Tendsto (fun n : ℕ => |T n|) atTop atTop :=
    tendsto_atTop_mono hT (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => (C * Real.log |T n| ^ 2 / |T n|) * W) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp ht).const_mul C |>.mul_const W
    simpa [mul_div_assoc] using h
  exact squeeze_zero_norm hbound hlim

/-- LEAF. Unit U-1551. Davenport chapter 17, the choice of `T`: there are heights
`T_n ∈ [n+2, n+3]` and `C > 0` with no zero of ζ on `σ ± iT_n`, `σ ≤ 2`, and
`|ζ'/ζ(σ ± iT_n)| ≤ C log² T_n (1 + |σ|)`; on `-1/2 ≤ σ ≤ 2` this is the lab's
`good_height_full` of `PNTPort/ZetaZeros/LeftHalf.lean` with conjugation, on `σ ≤ -1/2` the
functional equation, Mathlib's `logDeriv_riemannZeta_one_sub`, and the digamma bound. -/
theorem good_heights :
    ∃ (Tn : ℕ → ℝ) (C : ℝ), 0 < C ∧ ∀ n : ℕ, ((n : ℝ) + 2 ≤ Tn n ∧ Tn n ≤ n + 3) ∧
      ∀ σ : ℝ, σ ≤ 2 →
        ζ ((σ : ℂ) + Tn n * I) ≠ 0 ∧ ζ ((σ : ℂ) - Tn n * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + Tn n * I)‖ ≤ C * Real.log (Tn n) ^ 2 * (1 + |σ|) ∧
        ‖logDeriv ζ ((σ : ℂ) - Tn n * I)‖ ≤ C * Real.log (Tn n) ^ 2 * (1 + |σ|) := by
  classical
  have hsmall : ∀ a : ℝ, 2 ≤ a → ∃ T ∈ Icc a (a + 1), ∃ B : ℝ, 0 < B ∧
      ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ B * (1 + |σ|) := by
    intro a ha
    have hfin := (LeanLab.PNTPort.ExplicitPsi1.zeros_rect_finite 2 (a + 1)).image Complex.im
    obtain ⟨T, hT, hnot⟩ := (Set.Ioo_infinite (by linarith : a < a + 1)).exists_notMem_finite hfin
    have hn : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ζ ((σ : ℂ) + T * I) ≠ 0 := by
      intro σ hσ hz
      apply hnot
      refine ⟨(σ : ℂ) + T * I, ⟨?_, hz⟩, by simp⟩
      rw [LeanLab.PNTPort.ExplicitPsi1.mem_rect (by norm_num) (by linarith)]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul, mul_zero,
        sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
      exact ⟨hσ, by linarith [hT.1], hT.2.le⟩
    have hc : ContinuousOn (fun σ : ℝ => logDeriv ζ ((σ : ℂ) + T * I)) (Icc (-1 / 2 : ℝ) 2) := by
      intro σ hσ
      have hs1 : (σ : ℂ) + T * I ≠ 1 := by
        intro h; have hh := congrArg im h; simp at hh; linarith [hT.1]
      have hh := (LeanLab.PNTPort.ExplicitPsi1.analyticAt_logDeriv hs1 (hn σ hσ)).continuousAt
      exact (ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + T * I) hh (by fun_prop)).continuousWithinAt
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    obtain ⟨A, hA, hl⟩ := LeanLab.PNTPort.ExplicitPsi1.Trivial.logDeriv_left_region
    let B := |K| + A * Real.log (|T| + 3) + A + 1
    have hlog : 0 ≤ Real.log (|T| + 3) := Real.log_nonneg (by linarith [abs_nonneg T])
    have hB1 : 1 ≤ B := by dsimp [B]; nlinarith [mul_nonneg hA.le hlog, abs_nonneg K]
    refine ⟨T, ⟨hT.1.le, hT.2.le⟩, B, by linarith, ?_⟩
    intro σ hσ
    rcases le_or_gt (-1 / 2 : ℝ) σ with hs | hs
    · refine ⟨hn σ ⟨hs, hσ⟩, ?_⟩
      have hh := hK σ ⟨hs, hσ⟩
      have hBK : K ≤ B := by dsimp [B]; nlinarith [mul_nonneg hA.le hlog, le_abs_self K]
      nlinarith [abs_nonneg σ]
    · obtain ⟨hn, hh⟩ := hl σ T hs.le (by rw [abs_of_nonneg (by linarith [hT.1])]; linarith [hT.1])
      refine ⟨hn, ?_⟩
      change ‖deriv ζ _ / ζ _‖ ≤ _
      have hBA : A * Real.log (|T| + 3) + A ≤ B := by dsimp [B]; linarith [abs_nonneg K]
      rw [abs_of_neg (by linarith : σ < 0)]
      nlinarith
  have hbig : ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 5 ≤ a → ∃ T ∈ Icc a (a + 1),
      ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ D * Real.log T ^ 2 * (1 + |σ|) := by
    obtain ⟨C, hC, hg⟩ := LeanLab.PNTPort.ZetaZeros.good_height_full
    obtain ⟨A, hA, hl⟩ := LeanLab.PNTPort.ExplicitPsi1.Trivial.logDeriv_left_region
    let D := C + 3 * A + 1
    refine ⟨D, by dsimp [D]; positivity, ?_⟩
    intro a ha
    obtain ⟨T, hT, hb⟩ := hg a ha
    have hT5 : 5 ≤ T := ha.trans hT.1
    have hT0 : 0 < T := by linarith
    have hlog : 1 ≤ Real.log T := by
      apply (Real.le_log_iff_exp_le hT0).mpr
      linarith [Real.exp_one_lt_three]
    have hloga : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    have hlogmono : Real.log a ≤ Real.log T := Real.log_le_log (by linarith) hT.1
    have hlog2 : 1 ≤ Real.log T ^ 2 := by nlinarith
    have hlog3 : Real.log (|T| + 3) ≤ 2 * Real.log T := by
      rw [abs_of_pos hT0]
      calc
        Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    let Q := D * Real.log T ^ 2
    have hQ1 : 1 ≤ Q := by
      dsimp [Q, D]
      nlinarith [mul_nonneg hC.le (sq_nonneg (Real.log T)), mul_nonneg hA.le (sq_nonneg (Real.log T))]
    have hQA : A * Real.log (|T| + 3) + A ≤ Q := by
      have hll : Real.log T ≤ Real.log T ^ 2 := by nlinarith
      have h1 := mul_le_mul_of_nonneg_left hlog3 hA.le
      have h2 := mul_le_mul_of_nonneg_left hll hA.le
      have h3 := mul_le_mul_of_nonneg_left hlog2 hA.le
      dsimp [Q, D]
      nlinarith [mul_nonneg hC.le (sq_nonneg (Real.log T))]
    have hQC : C * Real.log a ^ 2 ≤ Q := by
      have hsq : Real.log a ^ 2 ≤ Real.log T ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hsq hC.le
      dsimp [Q, D]
      nlinarith [mul_nonneg hA.le (sq_nonneg (Real.log T))]
    refine ⟨T, hT, ?_⟩
    intro σ hσ
    change ζ ((σ : ℂ) + T * I) ≠ 0 ∧ ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ Q * (1 + |σ|)
    rcases le_or_gt (-1 / 2 : ℝ) σ with hs | hs
    · obtain ⟨hn, hh⟩ := hb σ ⟨hs, hσ⟩
      rw [mul_comm I] at hn hh
      refine ⟨hn, ?_⟩
      change ‖deriv ζ _ / ζ _‖ ≤ _
      nlinarith [abs_nonneg σ]
    · obtain ⟨hn, hh⟩ := hl σ T hs.le (by rw [abs_of_pos hT0]; linarith)
      refine ⟨hn, ?_⟩
      change ‖deriv ζ _ / ζ _‖ ≤ _
      rw [abs_of_neg (by linarith : σ < 0)]
      nlinarith
  obtain ⟨D, hD, hbig⟩ := hbig
  have hs : ∀ k : Fin 3, ∃ T ∈ Icc ((k : ℝ) + 2) ((k : ℝ) + 3), ∃ B : ℝ, 0 < B ∧
      ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ B * (1 + |σ|) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k.val
    have hh := hsmall ((k : ℝ) + 2) (by linarith)
    simpa only [show ((k : ℝ) + 2) + 1 = (k : ℝ) + 3 by ring] using hh
  choose Ts hTs Bs hBs hs using hs
  have hb : ∀ n : ℕ, ∃ T ∈ Icc (max 5 ((n : ℝ) + 2)) (max 5 ((n : ℝ) + 2) + 1),
      ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ D * Real.log T ^ 2 * (1 + |σ|) := by
    intro n
    exact hbig _ (le_max_left _ _)
  choose Tb hTb hb using hb
  let Cs : Fin 3 → ℝ := fun k => Bs k / Real.log (Ts k) ^ 2
  have hCs : ∀ k, 0 < Cs k := by
    intro k
    have ht : 1 < Ts k := by linarith [(hTs k).1, Nat.cast_nonneg (α := ℝ) k.val]
    exact div_pos (hBs k) (sq_pos_of_pos (Real.log_pos ht))
  let C := D + ∑ k : Fin 3, Cs k
  have hsum : 0 ≤ ∑ k : Fin 3, Cs k := Finset.sum_nonneg (fun k _ => (hCs k).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have hCD : D ≤ C := by dsimp [C]; linarith
  have hCk : ∀ k, Cs k ≤ C := by
    intro k
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hCs j).le)
      (Finset.mem_univ k)
    dsimp [C]
    linarith
  let Tn : ℕ → ℝ := fun n => if h : n < 3 then Ts ⟨n, h⟩ else Tb n
  have hpos : ∀ n : ℕ, ((n : ℝ) + 2 ≤ Tn n ∧ Tn n ≤ n + 3) ∧
      ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + Tn n * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + Tn n * I)‖ ≤ C * Real.log (Tn n) ^ 2 * (1 + |σ|) := by
    intro n
    by_cases hn : n < 3
    · dsimp only [Tn]
      rw [dite_eq_left hn]
      refine ⟨hTs ⟨n, hn⟩, ?_⟩
      intro σ hσ
      obtain ⟨hz, hh⟩ := hs ⟨n, hn⟩ σ hσ
      refine ⟨hz, hh.trans ?_⟩
      have ht : 1 < Ts ⟨n, hn⟩ := by linarith [(hTs ⟨n, hn⟩).1, Nat.cast_nonneg (α := ℝ) n]
      have he : Bs ⟨n, hn⟩ = Cs ⟨n, hn⟩ * Real.log (Ts ⟨n, hn⟩) ^ 2 := by
        dsimp [Cs]
        rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos (Real.log_pos ht)))]
      rw [he]
      gcongr
      exact hCk ⟨n, hn⟩
    · dsimp only [Tn]
      rw [dite_eq_right hn]
      have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
      have hm : max 5 ((n : ℝ) + 2) = n + 2 := max_eq_right (by linarith)
      refine ⟨?_, ?_⟩
      · have hh := hTb n
        rw [hm] at hh
        constructor <;> linarith [hh.1, hh.2]
      · intro σ hσ
        obtain ⟨hz, hh⟩ := hb n σ hσ
        refine ⟨hz, hh.trans ?_⟩
        gcongr
  refine ⟨Tn, C, hC, fun n => ⟨(hpos n).1, fun σ hσ => ?_⟩⟩
  obtain ⟨hz, hh⟩ := (hpos n).2 σ hσ
  have hc : conj ((σ : ℂ) + Tn n * I) = (σ : ℂ) - Tn n * I := by simp [sub_eq_add_neg]
  have hz' : ζ ((σ : ℂ) - Tn n * I) ≠ 0 := by
    rw [← hc, riemannZeta_conj]
    exact (map_ne_zero _).mpr hz
  refine ⟨hz, hz', hh, ?_⟩
  have he := logDerivZeta_conj ((σ : ℂ) + Tn n * I)
  rw [← hc]
  change ‖deriv ζ (conj _) / ζ (conj _)‖ ≤ _
  simp only [Pi.div_apply] at he
  rw [he, Complex.norm_conj]
  exact hh

/-- The trivial zero residues sum to `-(1/2) log(1 - x^{-2})`, from Mathlib's
`Real.hasSum_pow_div_log_of_abs_lt_one`. Proved. -/
theorem trivU_tendsto (x : ℝ) (hx : 1 < x) :
    Tendsto (fun m : ℕ => TrivU x m) atTop (𝓝 (TrivInf x)) := by
  set u : ℝ := (x ^ 2)⁻¹ with hu
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := inv_lt_one_of_one_lt₀ hx2
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := u) (by rw [abs_of_pos hu0]; exact hu1)
  have h2 := h.mul_left (1 / 2)
  have h3 : HasSum (fun k : ℕ => u ^ (k + 1) / (2 * ((k : ℝ) + 1))) (TrivInf x) := by
    convert h2 using 1
    · funext k; field_simp
    · unfold TrivInf; rw [← hu]; ring
  exact h3.tendsto_sum_nat

/-! ### Assemblies -/

lemma neg_cast_I (σ t : ℝ) : (σ : ℂ) + ((-t : ℝ) : ℂ) * I = (σ : ℂ) - t * I := by
  push_cast; ring

/-- von Mangoldt's explicit formula along the good heights: for `x > 1` not an integer,
`Σ_{|γ| ≤ T_n} x^ρ/ρ → x - ζ'/ζ(0) - (1/2) log(1 - x^{-2}) - ψ(x)`. Unconditional.
CONDITIONAL ON the leaves of this file. -/
theorem explicit_psi (Tn : ℕ → ℝ) (C : ℝ)
    (hTn : ∀ n : ℕ, ((n : ℝ) + 2 ≤ Tn n ∧ Tn n ≤ n + 3) ∧
      ∀ σ : ℝ, σ ≤ 2 →
        ζ ((σ : ℂ) + Tn n * I) ≠ 0 ∧ ζ ((σ : ℂ) - Tn n * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + Tn n * I)‖ ≤ C * Real.log (Tn n) ^ 2 * (1 + |σ|) ∧
        ‖logDeriv ζ ((σ : ℂ) - Tn n * I)‖ ≤ C * Real.log (Tn n) ^ 2 * (1 + |σ|))
    (x : ℝ) (hx : 1 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) :
    Tendsto (fun n : ℕ => ZS x (Tn n)) atTop
      (𝓝 ((x : ℂ) - L0 + (TrivInf x : ℂ) - ((Chebyshev.psi x : ℝ) : ℂ))) := by
  have hpos : ∀ n, 0 < Tn n := fun n => by
    have := (hTn n).1.1; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have habs : ∀ n, |Tn n| = Tn n := fun n => abs_of_pos (hpos n)
  have habs' : ∀ n, |-Tn n| = Tn n := fun n => by rw [abs_neg]; exact habs n
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; apply mul_ne_zero _ I_ne_zero
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  -- the identity at each good height, after `m → ∞`
  have key : ∀ n, ZS x (Tn n) = ((x : ℂ) - L0 + (TrivInf x : ℂ)) - Jc x (Tn n)
      + (HorInf x (Tn n) - HorInf x (-Tn n)) / c := by
    intro n
    set T := Tn n with hTdef
    have hbP : ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + T * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + T * I)‖ ≤ (C * Real.log T ^ 2) * (1 + |σ|) := by
      intro σ hσ; have h := (hTn n).2 σ hσ; exact ⟨h.1, h.2.2.1⟩
    have hbM : ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 ∧
        ‖logDeriv ζ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ (C * Real.log T ^ 2) * (1 + |σ|) := by
      intro σ hσ; have h := (hTn n).2 σ hσ
      rw [neg_cast_I]; exact ⟨h.2.1, h.2.2.2⟩
    have hT2 : 2 ≤ |T| := by
      rw [hTdef, habs n]; have := (hTn n).1.1; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hT2' : 2 ≤ |-T| := by rwa [abs_neg]
    have hL := ((tendsto_const_nhds (x := I * ((2 * Real.pi : ℝ) : ℂ) * Jc x T)).sub
      (hor_tendsto x hx T hT2 _ hbP)).add (hor_tendsto x hx (-T) hT2' _ hbM) |>.sub
      ((left_edge_limit x hx T).const_mul I)
    have hR : Tendsto (fun m : ℕ => c * ((x : ℂ) - ZS x T - L0 + (TrivU x m : ℂ))) atTop
        (𝓝 (c * ((x : ℂ) - ZS x T - L0 + (TrivInf x : ℂ)))) := by
      have ht := (Complex.continuous_ofReal.tendsto _).comp (trivU_tendsto x hx)
      exact (tendsto_const_nhds.add ht).const_mul c
    have hEq : ∀ m : ℕ, I * ((2 * Real.pi : ℝ) : ℂ) * Jc x T - HorI x m T + HorI x m (-T)
        - I * LeftI x m T = c * ((x : ℂ) - ZS x T - L0 + (TrivU x m : ℂ)) := fun m => by
      rw [hc]
      exact rect_identity zt_finite x hx T (hpos n) (fun σ hσ =>
        ⟨((hTn n).2 σ hσ).1, ((hTn n).2 σ hσ).2.1⟩) m
    have hlim := tendsto_nhds_unique (hL.congr hEq) hR
    rw [mul_zero, sub_zero] at hlim
    field_simp
    linear_combination hlim
  -- the limit `n → ∞`
  have hTt : Tendsto Tn atTop atTop := by
    refine tendsto_atTop_mono (fun n => (hTn n).1.1) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hJ := (perron_limit x hx hxn).comp hTt
  have hbP' : ∀ n : ℕ, ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + Tn n * I) ≠ 0 ∧
      ‖logDeriv ζ ((σ : ℂ) + Tn n * I)‖ ≤ C * Real.log |Tn n| ^ 2 * (1 + |σ|) := by
    intro n σ hσ; rw [habs n]; exact ⟨((hTn n).2 σ hσ).1, ((hTn n).2 σ hσ).2.2.1⟩
  have hbM' : ∀ n : ℕ, ∀ σ : ℝ, σ ≤ 2 → ζ ((σ : ℂ) + ((-Tn n : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖logDeriv ζ ((σ : ℂ) + ((-Tn n : ℝ) : ℂ) * I)‖ ≤ C * Real.log |-Tn n| ^ 2 * (1 + |σ|) := by
    intro n σ hσ; rw [habs' n, neg_cast_I]; exact ⟨((hTn n).2 σ hσ).2.1, ((hTn n).2 σ hσ).2.2.2⟩
  have hHP := hor_small x hx Tn C (fun n => by rw [habs n]; exact (hTn n).1.1) hbP'
  have hHM := hor_small x hx (fun n => -Tn n) C (fun n => by rw [habs' n]; exact (hTn n).1.1) hbM'
  have hall := (tendsto_const_nhds (x := (x : ℂ) - L0 + (TrivInf x : ℂ))).sub hJ |>.add
    ((hHP.sub hHM).div_const c)
  rw [show (x : ℂ) - L0 + (TrivInf x : ℂ) - ((Chebyshev.psi x : ℝ) : ℂ) =
      (x : ℂ) - L0 + (TrivInf x : ℂ) - ((Chebyshev.psi x : ℝ) : ℂ) + (0 - 0) / c by simp]
  refine hall.congr (fun n => ?_)
  simp only [Function.comp]
  rw [key n]

/-- ASSEMBLY. The input `ExplicitA gZ Z δ` of `U1508.goldbach_445_hsw_gZ`, for the truncations
`Z n = {γ : |γ| ≤ T_n}` at the good heights, for every `δ > 0`, under RH. CONDITIONAL ON the
leaves `perron_kernel_bound`, `jc_eq_tsum`, `tsum_kernel_limit`, `zt_finite`, `rect_identity`,
`left_edge_limit`, `hor_tendsto`, `hor_small`, `good_heights`. -/
theorem explicitA_gZ :
    ∃ Z : ℕ → Finset ZIdx, RiemannHypothesis → ∀ δ : ℝ, 0 < δ → ExplicitA gZ Z δ := by
  obtain ⟨Tn, C, -, hTn⟩ := good_heights
  refine ⟨fun n => ZT (Tn n), fun hRH δ hδ => ?_⟩
  have hρ : ∀ i : ZIdx, (1 / 2 : ℂ) + (gZ i : ℂ) * I = (i.1 : ℂ) := by
    intro i; apply Complex.ext <;> simp [re_half_of_RH hRH i.1, gZ]
  set S : Set ℝ := Set.range (fun n : ℕ => (n : ℝ)) ∪ Set.range (fun n : ℕ => (n : ℝ) / (1 + δ))
  have hS : volume S = 0 := ((Set.countable_range _).union (Set.countable_range _)).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS] with y hy hy2
  have hy0 : 0 < y := by linarith
  have hyn : ∀ n : ℕ, (n : ℝ) ≠ y := fun n h => hy (Or.inl ⟨n, h⟩)
  have hy'n : ∀ n : ℕ, (n : ℝ) ≠ (1 + δ) * y := fun n h => hy (Or.inr ⟨n, by
    simp only; rw [h]; field_simp⟩)
  have h1 := explicit_psi Tn C hTn y (by linarith) hyn
  have h2 := explicit_psi Tn C hTn ((1 + δ) * y) (by nlinarith) hy'n
  have hP : ∀ n, P (ZT (Tn n)) (cδ gZ δ) gZ y = ZS ((1 + δ) * y) (Tn n) - ZS y (Tn n) := by
    intro n
    unfold P ZS
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold cδ rho
    rw [hρ i]
    have hmul : (((1 + δ) * y : ℝ) : ℂ) ^ (i.1 : ℂ) =
        ((1 + δ : ℝ) : ℂ) ^ (i.1 : ℂ) * (y : ℂ) ^ (i.1 : ℂ) := by
      rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg (by linarith) hy0.le _
    rw [hmul]
    ring
  have hlim := (h2.sub h1).congr (fun n => (hP n).symm)
  convert hlim using 2
  unfold V Bf TrivInf
  push_cast
  ring

end LeanLab.Routes.Decomp1551a
