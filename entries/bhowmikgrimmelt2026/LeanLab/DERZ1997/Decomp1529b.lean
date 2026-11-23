module

public import Mathlib
public import LeanLab.PNTPort.ZetaZeros.LeftHalf
public import LeanLab.PNTPort.ZetaZeros.LeftLine
public import LeanLab.PNTPort.ExplicitPsi1.TrivialRect
public import LeanLab.DERZ1997.Lemma
public import LeanLab.PNTPort.ExplicitPsi1.Edges
public import LeanLab.PNTPort.ExplicitPsi1.Log2Pi
public import LeanLab.PNTPort.ExplicitPsi1.Residues
public import LeanLab.DERZ1997.Decomp1529a
public import LeanLab.DERZ1997.Kernel136
public import LeanLab.DERZ1997.Perron136
public import LeanLab.PNTPort.ZetaZeros.GoodHeight
public import LeanLab.DERZ1997.Decomp574a
public import LeanLab.DERZ1997.Decomp574b

/-!
Unit U-1529, run 20261025T2003Z-426, DECOMPOSE of the GRH inputs of P0011,
Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, 99-104.

File b: Perron's formula, the truncated explicit formula, and the GRH bound
`|ψ(x, χ) - δ_χ x| ≤ c √x log²(qx)`.
* `perronI y c T = (1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`, Perron's truncated integral.
* `psiChi χ x = ∑_{n ≤ x} χ(n) Λ(n)`, complex valued.
Leaves: Perron's kernel lemma in its three cases, the truncated Perron formula for `ψ`, the
tail bound, the contour shift, a good height `T` avoiding ordinates, the explicit formula for
`ψ` with an explicit constant, and the explicit formula for `ψ(x, χ)` under GRH.
Assembly `psiChi_bound_of_GRH`, PROVED from leaves here and in Decomp1529a, no unproved step in its
own proof, CONDITIONAL ON GRH and the leaves `explicit_formula_chi_GRH`, `LZeros_finite`,
`LZeros_recip_sum`.

Source when the original is not at hand: Davenport, Multiplicative Number Theory, 3rd ed.,
ch. 17 (Perron, explicit formula for ψ) and ch. 19-20 (ψ(x, χ), the GRH bound, p. 125).
P0011 page 101 uses only the `q = 1` case, through Schoenfeld 1976 (6.1).
AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.DERZ1997.ZetaLeft623
open Complex Real MeasureTheory Set
open LeanLab.Routes.Decomp1551a

/-- Dividing the logarithmic derivative by s removes its logarithmic growth
on the line of real part negative one half.
Auxiliary pointwise left-edge bound for Davenport chapter 17 pages 108 and 109.
-/
theorem zeta_left_pointwise623 : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ,
    ‖fK x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * x ^ (-1 / 2 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := LeanLab.PNTPort.ZetaZeros.logDeriv_left_line
  refine ⟨5 * K, by positivity, ?_⟩
  intro x hx t
  let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
  have hre : s.re = -1 / 2 := by dsimp [s]; simp
  have him : s.im = t := by dsimp [s]; simp
  have hn : 1 / 2 ≤ ‖s‖ := by
    have hh := Complex.abs_re_le_norm s
    rw [hre] at hh
    norm_num at hh
    exact hh
  have ht : |t| ≤ ‖s‖ := by simpa only [him] using Complex.abs_im_le_norm s
  have hlog : Real.log (|t| + 3) ≤ 5 * ‖s‖ := by
    have hh := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 3)
    linarith
  have hden : 0 < ‖s‖ := by linarith
  have hd : ‖logDeriv riemannZeta s‖ ≤ 5 * K * ‖s‖ := by
    have hh : ‖logDeriv riemannZeta s‖ ≤ K * Real.log (|t| + 3) := by
      convert (hb t).2 using 1; norm_num [s, logDeriv_apply]
    exact hh.trans (by nlinarith)
  have hp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  change ‖-logDeriv riemannZeta s * (x : ℂ) ^ s / s‖ ≤ _
  rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre,
    div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right hd hp]

/-- A left edge ending below x plus one contributes at most an absolute
constant times square root x to the unsmoothed contour error.
Auxiliary integral bound for Davenport chapter 17 pages 108 and 109.
-/
theorem zeta_left_integral623 : ∃ C : ℝ, 0 < C ∧ ∀ (x U : ℝ),
    2 ≤ x → 0 ≤ U → U ≤ x + 1 →
    ‖∫ t in (-U)..U, fK x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * √x := by
  obtain ⟨K, hK, hb⟩ := zeta_left_pointwise623
  refine ⟨3 * K, by positivity, ?_⟩
  intro x U hx hU hUx
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hp : x ^ (-1 / 2 : ℝ) = (√x)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow]
  have hcancel : x * x ^ (-1 / 2 : ℝ) = √x := by
    rw [hp, mul_inv_eq_iff_eq_mul₀ hs.ne']
    nlinarith [Real.sq_sqrt hx0.le]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -U) (b := U) (fun t _ => hb x hx0 t)
  have hlen : |U - -U| = 2 * U := by rw [abs_of_nonneg (by linarith)]; ring
  rw [hlen] at hh
  have hlength : 2 * U ≤ 3 * x := by linarith
  calc
    _ ≤ (2 * U) * (K * x ^ (-1 / 2 : ℝ)) := by simpa only [mul_comm] using hh
    _ ≤ (3 * x) * (K * x ^ (-1 / 2 : ℝ)) := by gcongr
    _ = 3 * K * √x := by rw [show (3 * x) * (K * x ^ (-1 / 2 : ℝ)) =
      3 * K * (x * x ^ (-1 / 2 : ℝ)) by ring, hcancel]

end LeanLab.DERZ1997.ZetaLeft623

namespace LeanLab.DERZ1997.Decomp1529b2
open Complex Real MeasureTheory Set Filter Topology
open LeanLab.DERZ1997.Decomp1529a

/-- Auxiliary estimate for the height transfer in Davenport chapter 17 page 109. -/
theorem zero_term_height266 {x T : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    {ρ : ℂ} (hr : ρ.re ≤ 1) (hi : T ≤ |ρ.im|) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤ (m : ℝ) * x / T := by
  have hx0 : 0 < x := by linarith
  have hn : T ≤ ‖ρ‖ := hi.trans (Complex.abs_im_le_norm ρ)
  rw [norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg m) hx0.le)
    (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hx hr) (Nat.cast_nonneg m))
    hT hn

/-- Auxiliary finite-sum height transfer for Davenport chapter 17 page 109. -/
theorem finite_height_transfer266 {x T : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    (A B : Finset ℂ) (hAB : A ⊆ B) (m : ℂ → ℕ)
    (hr : ∀ ρ ∈ B \ A, ρ.re ≤ 1) (hi : ∀ ρ ∈ B \ A, T ≤ |ρ.im|) :
    ‖(∑ ρ ∈ B, (m ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
      ∑ ρ ∈ A, (m ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        (∑ ρ ∈ B \ A, (m ρ : ℝ)) * x / T := by
  classical
  rw [← Finset.sum_sdiff_eq_sub hAB]
  calc
    _ ≤ ∑ ρ ∈ B \ A, ‖(m ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ B \ A, (m ρ : ℝ) * x / T := Finset.sum_le_sum fun ρ hρ =>
      zero_term_height266 hx hT (hr ρ hρ) (hi ρ hρ) (m ρ)
    _ = _ := by rw [← Finset.sum_div, ← Finset.sum_mul]

/-- Multiplicity in a two-sided height band is at most twice the positive window count.
Auxiliary derivation for Davenport chapter 17 page 109. -/
theorem zeta_band_mass266 {T U : ℝ} (hT : 0 < T) (hU : U ≤ T + 1)
    (hfT : (zetaZeros T).Finite) (hfU : (zetaZeros U).Finite)
    (hfW : (zetaZerosWindow T).Finite) :
    (∑ ρ ∈ hfU.toFinset \ hfT.toFinset, (zetaMult ρ : ℝ)) ≤
      2 * ∑ ρ ∈ hfW.toFinset, (zetaMult ρ : ℝ) := by
  classical
  let S := hfU.toFinset \ hfT.toFinset
  have hmem (ρ : ℂ) : ρ ∈ S ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im| ∧ |ρ.im| ≤ U := by
    simp only [S, Finset.mem_sdiff, Set.Finite.mem_toFinset, zetaZeros, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz, h0, h1, hu⟩, hn⟩
      exact ⟨hz, h0, h1, lt_of_not_ge (fun ht => hn ⟨hz, h0, h1, ht⟩), hu⟩
    · rintro ⟨hz, h0, h1, ht, hu⟩
      exact ⟨⟨hz, h0, h1, hu⟩, fun hn => (not_le_of_gt ht) hn.2.2.2⟩
  have hmap {ρ : ℂ} (hρ : ρ ∈ S) : 1 - ρ ∈ S := by
    obtain ⟨hz, h0, h1, ht, hu⟩ := (hmem ρ).mp hρ
    apply (hmem _).mpr
    refine ⟨LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero h0 h1 hz, ?_, ?_, ?_, ?_⟩
    · simp only [sub_re, one_re]; linarith
    · simp only [sub_re, one_re]; linarith
    · simpa only [sub_im, one_im, zero_sub, abs_neg] using ht
    · simpa only [sub_im, one_im, zero_sub, abs_neg] using hu
  let P := S.filter (fun ρ => 0 < ρ.im)
  let N := S.filter (fun ρ => ¬0 < ρ.im)
  have hpair : (∑ ρ ∈ N, (zetaMult ρ : ℝ)) = ∑ ρ ∈ P, (zetaMult ρ : ℝ) := by
    apply Finset.sum_bij (fun ρ _ => 1 - ρ)
    · intro ρ hρ
      obtain ⟨hs, hi⟩ := Finset.mem_filter.mp hρ
      refine Finset.mem_filter.mpr ⟨hmap hs, ?_⟩
      have hh := (hmem ρ).mp hs
      have hn : ρ.im ≠ 0 := by intro he; simp [he] at hh; linarith [hh.2.2.2.1]
      simp only [sub_im, one_im, zero_sub]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hi) hn)
    · intro a ha b hb he
      exact sub_right_inj.mp he
    · intro ρ hρ
      obtain ⟨hs, hi⟩ := Finset.mem_filter.mp hρ
      refine ⟨1 - ρ, Finset.mem_filter.mpr ⟨hmap hs, ?_⟩, ?_⟩
      · simp only [sub_im, one_im, zero_sub]; linarith
      · ring
    · intro ρ hρ
      have hh := (hmem ρ).mp (Finset.mem_filter.mp hρ).1
      exact_mod_cast (LeanLab.PNTPort.ZetaZeros.ord_one_sub hh.2.1 hh.2.2.1).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun ρ => 0 < ρ.im)
    (fun ρ => (zetaMult ρ : ℝ))
  change (∑ ρ ∈ P, (zetaMult ρ : ℝ)) + (∑ ρ ∈ N, (zetaMult ρ : ℝ)) = _ at hsplit
  have hsubset : P ⊆ hfW.toFinset := by
    intro ρ hρ
    obtain ⟨hs, hi⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, h0, h1, ht, hu⟩ := (hmem ρ).mp hs
    rw [abs_of_pos hi] at ht hu
    exact hfW.mem_toFinset.mpr ⟨hz, h0, h1, ht, hu.trans hU⟩
  have hle : (∑ ρ ∈ P, (zetaMult ρ : ℝ)) ≤ ∑ ρ ∈ hfW.toFinset, (zetaMult ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.cast_nonneg _)
  rw [hpair] at hsplit
  change (∑ ρ ∈ S, (zetaMult ρ : ℝ)) ≤ _
  linarith

/-- The zero-sum transfer across an interval of height at most one.
The published zero count remains the explicit window-mass premise.
Auxiliary derivation for Davenport chapter 17 page 109. -/
theorem zeta_height_transfer266 {x T U B : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    (hTU : T ≤ U) (hU : U ≤ T + 1)
    (hfT : (zetaZeros T).Finite) (hfU : (zetaZeros U).Finite)
    (hfW : (zetaZerosWindow T).Finite)
    (hcount : (∑ ρ ∈ hfW.toFinset, (zetaMult ρ : ℝ)) ≤ B) :
    ‖(∑ ρ ∈ hfU.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
      ∑ ρ ∈ hfT.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        2 * B * x / T := by
  classical
  have hsubset : hfT.toFinset ⊆ hfU.toFinset := by
    intro ρ hρ
    have hh := hfT.mem_toFinset.mp hρ
    exact hfU.mem_toFinset.mpr ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.trans hTU⟩
  have hbound := finite_height_transfer266 hx hT hfT.toFinset hfU.toFinset hsubset zetaMult
    (fun ρ hρ => (hfU.mem_toFinset.mp (Finset.mem_sdiff.mp hρ).1).2.2.1.le)
    (fun ρ hρ => by
      obtain ⟨hu, ht⟩ := Finset.mem_sdiff.mp hρ
      have hh := hfU.mem_toFinset.mp hu
      by_contra hn
      exact ht (hfT.mem_toFinset.mpr ⟨hh.1, hh.2.1, hh.2.2.1, le_of_not_ge hn⟩))
  have hmass : (∑ ρ ∈ hfU.toFinset \ hfT.toFinset, (zetaMult ρ : ℝ)) ≤ 2 * B :=
    (zeta_band_mass266 hT hU hfT hfU hfW).trans (by linarith)
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass (by linarith)) hT.le)

end LeanLab.DERZ1997.Decomp1529b2

namespace LeanLab.DERZ1997.Decomp1529b
open Complex LeanLab.DERZ1997.Decomp1529a
open Real MeasureTheory Set
open Filter Topology
open scoped ComplexConjugate
open LeanLab.PNTPort.ExplicitPsi1.Trivial
open LeanLab.PNTPort.ZetaZeros
open LeanLab.PNTPort.ExplicitPsi1
open LeanLab.Routes.Decomp1551a (fK TrivU TrivInf trivU_tendsto)

/-- The twisted Chebyshev function `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
noncomputable def psiChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The truncated Perron integral of `-ζ'/ζ = ∑ Λ(n) n^{-s}` against `x^s/s` on `Re s = c`. -/
noncomputable def perronPsi (x c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) *
      (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

/-! ### Perron's formula -/

/-- LEAF. Perron kernel, `y > 1`: for `c > 0`, `T > 0`,
`|(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds - 1| ≤ y^c min(1, 1/(T log y))`. Shift left past the pole at
0 along a rectangle (bound `y^c/(πT log y)`) or along a circular arc (bound `y^c`).
Davenport ch. 17, Lemma, p. 105. Unit U-1529. -/
theorem perron_gt_one {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronI y c T - 1‖ ≤ y ^ c * min 1 (1 / (T * Real.log y)) := by
  by_cases hlarge : 1 ≤ T * Real.log y
  · exact LeanLab.DERZ1997.Perron136.perron_gt_one_large hy hc hT hlarge
  · have hs : T * Real.log y ≤ 1 := (lt_of_not_ge hlarge).le
    have hd : 0 < T * Real.log y := mul_pos hT (Real.log_pos hy)
    rw [min_eq_left ((one_le_div hd).mpr hs), mul_one]
    exact LeanLab.DERZ1997.Perron136.perron_gt_one_small hy hc hT hs

/-- LEAF. Perron kernel, `0 < y < 1`: for `c > 0`, `T > 0`,
`|(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds| ≤ y^c min(1, 1/(T |log y|))`, by shifting right.
Davenport ch. 17, Lemma, p. 105. Unit U-1529. -/
theorem perron_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronI y c T‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  by_cases hlarge : 1 ≤ T * |Real.log y|
  · exact LeanLab.DERZ1997.Perron136.perron_lt_one_large hy0 hy hc hT hlarge
  · have hs : T * |Real.log y| ≤ 1 := (lt_of_not_ge hlarge).le
    have hd : 0 < T * |Real.log y| := mul_pos hT
      (abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy0 (ne_of_lt hy)))
    rw [min_eq_left ((one_le_div hd).mpr hs), mul_one]
    exact LeanLab.DERZ1997.Perron136.perron_norm_small hy0 hc hT hs

/-- LEAF. Perron kernel, `y = 1`: `|(1/2π) ∫_{-T}^{T} dt/(c+it) - 1/2| ≤ c/T`; the integral is
`arctan(T/c)/π` and `1/2 - arctan(T/c)/π = arctan(c/T)/π`. Davenport ch. 17, p. 105.
Unit U-1529. -/
theorem perron_one {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perronI 1 c T - 1 / 2‖ ≤ c / T := by
  have hval : perronI 1 c T = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
    have hn : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := by
      intro t h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hcont : Continuous (fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * I)) := by
      exact continuous_const.div (by fun_prop) hn
    have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
    have hre : (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I)).re =
        2 * Real.arctan (T / c) := by
      calc
        _ = ∫ t : ℝ in (-T)..T, ((1 : ℂ) / ((c : ℂ) + t * I)).re :=
          (Complex.reCLM.intervalIntegral_comp_comm hint).symm
        _ = ∫ t : ℝ in (-T)..T, c / (c ^ 2 + t ^ 2) := by
          congr 1
          funext t
          simp [Complex.div_re, Complex.normSq_apply, pow_two]
        _ = _ := by rw [integral_div_sq_add_sq, neg_div, Real.arctan_neg]; ring
    have him : (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I)).im = 0 := by
      calc
        _ = ∫ t : ℝ in (-T)..T, ((1 : ℂ) / ((c : ℂ) + t * I)).im :=
          (Complex.imCLM.intervalIntegral_comp_comm hint).symm
        _ = ∫ t : ℝ in (-T)..T, -(t / (c ^ 2 + t ^ 2)) := by
          congr 1
          funext t
          simp [Complex.div_im, Complex.normSq_apply, pow_two, neg_div]
        _ = _ := by
          rw [intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc.ne']
          simp
    unfold perronI
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
    rw [hfac]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero, hre]
      ring
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero, him]
  have hdiff : perronI 1 c T - 1 / 2 =
      ((Real.arctan (T / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by
    rw [hval]
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hupper : Real.arctan (T / c) / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  rw [abs_of_nonpos (by linarith)]
  have hinv : Real.arctan (c / T) = Real.pi / 2 - Real.arctan (T / c) := by
    simpa only [inv_div] using Real.arctan_inv_of_pos (div_pos hT hc)
  have heq : -(Real.arctan (T / c) / Real.pi - 1 / 2) =
      Real.arctan (c / T) / Real.pi := by
    rw [hinv]
    field_simp
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_right (Real.arctan_le_self (by positivity))
    Real.pi_pos.le).trans (div_le_self (by positivity) (by linarith [Real.pi_gt_three]))

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 105-106. Dudek arXiv 1401.4233v1, pages 5-6. This is the sum and integral interchange. -/
theorem perronPsi_eq_tsum197 {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    perronPsi x c T = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * perronI (x / n) c T := by
  let F : ℕ → ℝ → ℂ := fun n t => (ArithmeticFunction.vonMangoldt n : ℂ) * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
      ((c : ℂ) + t * I)
  have hnorm : ∀ n t, ‖F n t‖ = ArithmeticFunction.vonMangoldt n * (x / n) ^ c * ‖(1 : ℂ) / ((c : ℂ) + t * I)‖ := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [F]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      norm_cpow_eq_rpow_re_of_pos (div_pos hx hn0)]
    simp [div_eq_mul_inv]
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
        simp at this
        linarith
    exact hc.intervalIntegrable _ _
  have hcoeff := LeanLab.DERZ1997.Perron136.perron_coeff_summable hx hc
  have hsum : Summable (fun n : ℕ => ∫ t in Ioc (-T) T, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact hcoeff.mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hr : ∀ t : ℝ, ∑' n, F n t = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) *
        (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
    intro t
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
  have hl : ∀ n : ℕ, (1 / (2 * Real.pi) : ℂ) * (∫ t in Ioc (-T) T, F n t) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * perronI (x / n) c T := by
    intro n
    unfold perronI
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    dsimp [F]
    rw [show (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I)) =
      (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) * (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I))) by funext t; ring, integral_const_mul]
    ring
  unfold perronPsi
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  simp_rw [← hr]
  rw [← key, ← tsum_mul_left]
  exact tsum_congr hl

/-- LEAF. Truncated Perron formula for `ψ`: for `x ≥ 2` not an integer, `c > 1`, `T > 0`,
`|ψ(x) - (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ)(s) x^s/s ds| ≤ ∑_n Λ(n) (x/n)^c min(1, 1/(T|log(x/n)|))`.
Expand `-ζ'/ζ(s) = ∑ Λ(n) n^{-s}`, which converges absolutely on `Re s = c`, integrate
term by term, and apply `perron_gt_one` for `n < x`, `perron_lt_one` for `n > x`.
Davenport ch. 17, (2)-(3), p. 105-106. Unit U-1529. -/
theorem perron_psi {x c T : ℝ} (hx : 2 ≤ x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hc : 1 < c)
    (hT : 0 < T) :
    ‖(Chebyshev.psi x : ℂ) - perronPsi x c T‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (x / n) ^ c *
        min 1 (1 / (T * |Real.log (x / n)|)) := by
  classical
  have hx0 : 0 < x := by linarith
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
    (if (n : ℝ) < x then 1 else 0)
  let b : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * perronI (x / n) c T
  let E : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * (x / n) ^ c *
    min 1 (1 / (T * |Real.log (x / n)|))
  have hE0 : ∀ n, 0 ≤ E n := fun n => by dsimp [E]; positivity
  have hE : Summable E := by
    apply (LeanLab.DERZ1997.Perron136.perron_coeff_summable hx0 hc).of_nonneg_of_le hE0
    intro n
    exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  have ha0 : ∀ n ∉ Finset.range (⌊x⌋₊ + 1), a n = 0 := by
    intro n hn
    have hn' : ⌊x⌋₊ < n := by simpa using hn
    have hnx : x < n := (Nat.floor_lt hx0.le).mp hn'
    simp [a, not_lt.mpr hnx.le]
  have ha : Summable a := summable_of_ne_finset_zero ha0
  have hat : ∑' n, a n = (Chebyshev.psi x : ℂ) := by
    rw [tsum_eq_sum ha0, Chebyshev.psi_eq_sum_Icc]
    push_cast
    have hr : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by ext n; simp
    rw [hr]
    apply Finset.sum_congr rfl
    intro n hn
    have hnx : (n : ℝ) < x := lt_of_le_of_ne
      ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hn).2) (hxn n)
    simp [a, hnx]
  have he : ∀ n, ‖a n - b n‖ ≤ E n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a, b, E]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hratio0 : 0 < x / n := div_pos hx0 hn0
    have hratio : x / (n : ℝ) ≠ 1 := by
      intro h
      exact hxn n ((div_eq_one_iff_eq hn0.ne').mp h).symm
    have hk : ‖perronI (x / n) c T - (if (n : ℝ) < x then 1 else 0)‖ ≤
        (x / n) ^ c * min 1 (1 / (T * |Real.log (x / n)|)) := by
      by_cases hnx : (n : ℝ) < x
      · have hy : 1 < x / (n : ℝ) := (one_lt_div hn0).mpr hnx
        simpa [hnx, abs_of_pos (Real.log_pos hy)] using perron_gt_one hy (by linarith) hT
      · have hy : x / (n : ℝ) < 1 := (div_lt_one hn0).mpr
          (lt_of_le_of_ne (le_of_not_gt hnx) (hxn n).symm)
        simpa [hnx] using perron_lt_one hratio0 hy (by linarith) hT
    rw [show a n - b n = -( (ArithmeticFunction.vonMangoldt n : ℂ) *
      (perronI (x / n) c T - (if (n : ℝ) < x then 1 else 0))) by dsimp [a, b]; ring,
      norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_mul_of_nonneg_left hk ArithmeticFunction.vonMangoldt_nonneg).trans_eq (by dsimp [E]; ring)
  have hd : Summable (fun n => a n - b n) := hE.of_norm_bounded he
  have hb : Summable b := by
    convert ha.sub hd using 1
    funext n
    simp
  rw [perronPsi_eq_tsum197 hx0 hc hT, ← hat, ← ha.tsum_sub hb]
  exact tsum_of_norm_bounded hE.hasSum he

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem half_integer_distance197 (N n : ℕ) : (1 / 2 : ℝ) ≤ |(N : ℝ) + 1 / 2 - n| := by
  rcases le_or_gt n N with h | h
  · have : (n : ℝ) ≤ N := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem abs_log_ratio_lower197 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log (x / y)| := by
  rcases le_total y x with h | h
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (Real.log_nonneg ((one_le_div hy).mpr h))]
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rw [inv_div] at hh
    convert hh using 1 <;> field_simp
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h),
      abs_of_nonpos (Real.log_nonpos (div_nonneg hx.le hy.le) ((div_le_one hy).mpr h))]
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [inv_div, Real.log_div hy.ne' hx.ne', Real.log_div hx.ne' hy.ne'] at *
    have heq : -(x - y) / y = 1 - x / y := by field_simp; ring
    rw [heq]
    linarith

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem nat_rpow_tsum_le197 {p : ℝ} (hp : 1 < p) :
    ∑' n : ℕ, (n : ℝ) ^ (-p) ≤ 1 + 1 / (p - 1) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-p)) (Ici 1) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (a := -p) (c := 1) (by linarith) (by norm_num)
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ => t ^ (-p)) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hint)
    (fun t ht => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt (show (1 : ℝ) < t by simpa using ht))) _)
  simp only [Nat.cast_one] at h
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) (by norm_num : (0 : ℝ) < 1),
    Real.one_rpow, neg_div] at h
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := summable_nat_rpow.mpr (by linarith)
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-p)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using hs.comp_injective Nat.succ_injective
  rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : -p ≠ 0), Nat.cast_one,
    Real.one_rpow, zero_add]
  rw [show -p + 1 = -(p - 1) by ring, div_neg, neg_neg] at h
  simpa only [add_comm] using add_le_add_left h 1

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem log_nat_rpow_summable_bound197 {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) ∧
    ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-p) ≤
      (2 / (p - 1)) * (1 + 2 / (p - 1)) := by
  let d := (p - 1) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hpd : 1 < p - d := by dsimp [d]; linarith
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(p - d))) :=
    summable_nat_rpow.mpr (by linarith)
  have hb : ∀ n : ℕ, Real.log n * (n : ℝ) ^ (-p) ≤
      (1 / d) * (n : ℝ) ^ (-(p - d)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.log_zero, zero_mul]
      positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      _ ≤ ((n : ℝ) ^ d / d) * (n : ℝ) ^ (-p) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hn0.le hd) (by positivity)
      _ = (1 / d) * ((n : ℝ) ^ d * (n : ℝ) ^ (-p)) := by ring
      _ = (1 / d) * (n : ℝ) ^ (d + -p) := by rw [Real.rpow_add hn0]
      _ = _ := by congr 2; ring
  have ha0 : ∀ n : ℕ, 0 ≤ Real.log n * (n : ℝ) ^ (-p) := by
    intro n
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have ha := (hs.mul_left (1 / d)).of_nonneg_of_le ha0 hb
  refine ⟨ha, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (1 / d) * (n : ℝ) ^ (-(p - d)) := ha.tsum_le_tsum hb (hs.mul_left _)
    _ = (1 / d) * ∑' n : ℕ, (n : ℝ) ^ (-(p - d)) := tsum_mul_left
    _ ≤ (1 / d) * (1 + 1 / (p - d - 1)) :=
      mul_le_mul_of_nonneg_left (nat_rpow_tsum_le197 hpd) (by positivity)
    _ = _ := by
      rw [show p - d - 1 = d by dsimp [d]; ring]
      have heq : 1 / d = 2 / (p - 1) := by dsimp [d]; rw [div_div_eq_mul_div, one_mul]
      rw [heq]

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem perron_coeff_bound197 {x : ℝ} (hx : 2 ≤ x) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (x / n) ^ (1 + 1 / Real.log x) ≤
      24 * x * Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLhalf : 1 / 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_two_gt_d9
    linarith
  let c : ℝ := 1 + 1 / Real.log x
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hL]
  obtain ⟨hlogsum, hlogbd⟩ := log_nat_rpow_summable_bound197 hc
  have heq : 2 / (c - 1) = 2 * Real.log x := by
    rw [show c - 1 = 1 / Real.log x by dsimp [c]; ring, div_div_eq_mul_div, div_one]
  rw [heq] at hlogbd
  have hb : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * (x / n) ^ c ≤
      x ^ c * (Real.log n * (n : ℝ) ^ (-c)) := by
    intro n
    rw [Real.div_rpow hx0.le (Nat.cast_nonneg n), div_eq_mul_inv,
      ← Real.rpow_neg (Nat.cast_nonneg n)]
    calc
      _ ≤ Real.log n * (x ^ c * (n : ℝ) ^ (-c)) :=
        mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)
      _ = _ := by ring
  have hsum := (hlogsum.mul_left (x ^ c)).of_nonneg_of_le (fun n => by positivity) hb
  have hpow : x ^ c ≤ 3 * x := by
    have heq : x ^ c = x * Real.exp 1 := by
      dsimp [c]
      rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
      congr 1
      rw [mul_one_div_cancel hL.ne']
    rw [heq]
    nlinarith [Real.exp_one_lt_three]
  calc
    _ ≤ ∑' n : ℕ, x ^ c * (Real.log n * (n : ℝ) ^ (-c)) :=
      hsum.tsum_le_tsum hb (hlogsum.mul_left _)
    _ = x ^ c * ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-c) := tsum_mul_left
    _ ≤ x ^ c * ((2 * Real.log x) * (1 + 2 * Real.log x)) :=
      mul_le_mul_of_nonneg_left hlogbd (by positivity)
    _ ≤ (3 * x) * (8 * Real.log x ^ 2) := by
      apply mul_le_mul hpow (by nlinarith) (by positivity) (by positivity)
    _ = _ := by ring

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem perron_far_cutoff197 {x y T : ℝ} (hx : 0 < x) (hy : 0 < y) (hT : 0 < T)
    (hfar : y ≤ x / 2 ∨ 2 * x ≤ y) :
    min 1 (1 / (T * |Real.log (x / y)|)) ≤ 2 / T := by
  have hlog : 1 / 2 ≤ |Real.log (x / y)| := by
    have h := abs_log_ratio_lower197 hx hy
    rcases hfar with hlo | hhi
    · have hyx : y ≤ x := by linarith
      rw [max_eq_left hyx, abs_of_nonneg (sub_nonneg.mpr hyx)] at h
      have hd : 1 / 2 ≤ (x - y) / x := (le_div_iff₀ hx).mpr (by linarith)
      exact hd.trans h
    · have hxy : x ≤ y := by linarith
      rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
      have hd : 1 / 2 ≤ -(x - y) / y := (le_div_iff₀ hy).mpr (by linarith)
      exact hd.trans h
  calc
    _ ≤ 1 / (T * |Real.log (x / y)|) := min_le_right _ _
    _ ≤ 2 / T := by
      rw [div_le_div_iff₀ (mul_pos hT (by linarith)) hT]
      nlinarith

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem perron_near_cutoff197 {x y T : ℝ} (hx : 0 < x) (hy : 0 < y) (hT : 0 < T)
    (hyhi : y ≤ 2 * x) (hne : x ≠ y) :
    min 1 (1 / (T * |Real.log (x / y)|)) ≤ 2 * x / (T * |x - y|) := by
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hm : 0 < max x y := lt_max_of_lt_left hx
  have hmax : max x y ≤ 2 * x := max_le (by linarith) hyhi
  have hlog : |x - y| / (2 * x) ≤ |Real.log (x / y)| :=
    (div_le_div_of_nonneg_left hd.le hm hmax).trans (abs_log_ratio_lower197 hx hy)
  have hlog0 : 0 < |Real.log (x / y)| := (div_pos hd (by positivity)).trans_le hlog
  have hmullog : |x - y| ≤ 2 * x * |Real.log (x / y)| := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * x)).mp hlog
  calc
    _ ≤ 1 / (T * |Real.log (x / y)|) := min_le_right _ _
    _ ≤ 2 * x / (T * |x - y|) := by
      rw [div_le_div_iff₀ (mul_pos hT hlog0) (mul_pos hT hd)]
      nlinarith

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem perron_near_coeff197 {x y : ℝ} (hx : 2 ≤ x) (hylo : x / 2 ≤ y) (hyhi : y ≤ 2 * x) :
    Real.log y * (x / y) ^ (1 + 1 / Real.log x) ≤ 16 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hL : 1 / 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_two_gt_d9
    linarith
  have hc0 : 0 ≤ 1 + 1 / Real.log x := by positivity
  have hc3 : 1 + 1 / Real.log x ≤ 3 := by
    have : 1 / Real.log x ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hratio : x / y ≤ 2 := (div_le_iff₀ hy0).mpr (by linarith)
  have hp : (x / y) ^ (1 + 1 / Real.log x) ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 + 1 / Real.log x) := Real.rpow_le_rpow (by positivity) hratio hc0
      _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
      _ = 8 := by norm_num
  have hl : Real.log y ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (2 * x) := Real.log_le_log hy0 hyhi
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx]
  calc
    _ ≤ (2 * Real.log x) * 8 := mul_le_mul hl hp (by positivity) (by positivity)
    _ = _ := by ring

/-- Auxiliary step for the Perron tail estimate.
Davenport chapter 17, pages 106-107. Dudek arXiv 1401.4233v1, pages 6-8.
The numerical majorants are derived here. -/
theorem half_integer_recip_sum197 (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N + 2), 1 / |(N : ℝ) + 1 / 2 - n| ≤
      4 * (1 + Real.log (N + 1)) := by
  let f : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1 / 2)
  have hl : ∑ n ∈ Finset.range (N + 1), 1 / |(N : ℝ) + 1 / 2 - n| =
      ∑ k ∈ Finset.range (N + 1), f k := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := by simpa using hk
    have heq : (N + 1 - 1 - k : ℕ) = N - k := by omega
    rw [heq, Nat.cast_sub hkN]
    dsimp [f]
    rw [abs_of_nonneg (by have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)]
    congr 1
    ring
  have hr : ∑ n ∈ Finset.range (N + 1), 1 / |(N : ℝ) + 1 / 2 - (N + 1 + n)| =
      ∑ k ∈ Finset.range (N + 1), f k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    rw [abs_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)]
    congr 1
    ring
  have hsum : ∑ k ∈ Finset.range (N + 1), f k ≤ 2 * (1 + Real.log (N + 1)) := by
    have hterm : ∀ k ∈ Finset.range (N + 1), f k ≤ 2 / ((k : ℝ) + 1) := by
      intro k hk
      dsimp [f]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), 2 / ((k : ℝ) + 1) := Finset.sum_le_sum hterm
      _ = 2 * (harmonic (N + 1) : ℝ) := by
        simp [harmonic, Finset.mul_sum, div_eq_mul_inv, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (N + 1)) (by norm_num : (0 : ℝ) ≤ 2)
  rw [show 2 * N + 2 = (N + 1) + (N + 1) by omega, Finset.sum_range_add, hl]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hr]
  linarith

/-- LEAF. Tail of the truncated Perron formula: there is an absolute `C` such that for
`x = N + 1/2` with `N ≥ 2`, `c = 1 + 1/log x`, `T ≥ 2`,
`∑_n Λ(n) (x/n)^c min(1, 1/(T|log(x/n)|)) ≤ C (x log² x / T + log x)`. Split `n` by
`|n - x| ≥ x/4`, the range `x/2 ≤ n ≤ 2x` by `|n - x|`, and use `∑ Λ(n) n^{-c} ≪ log x`.
Davenport ch. 17, p. 106-107. Unit U-1529. -/
theorem perron_tail : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 2 ≤ T →
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (((N : ℝ) + 1 / 2) / n) ^
        (1 + 1 / Real.log ((N : ℝ) + 1 / 2)) *
      min 1 (1 / (T * |Real.log (((N : ℝ) + 1 / 2) / n)|)) ≤
      C * (((N : ℝ) + 1 / 2) * Real.log ((N : ℝ) + 1 / 2) ^ 2 / T +
        Real.log ((N : ℝ) + 1 / 2)) := by
  refine ⟨560, ?_⟩
  intro N hN T hT
  let x : ℝ := N + 1 / 2
  let c : ℝ := 1 + 1 / Real.log x
  have hx : 2 ≤ x := by
    have hncast : (2 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]
    linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_two_gt_d9
    linarith
  have hc : 1 < c := by dsimp [c]; have := one_div_pos.mpr (show 0 < Real.log x by linarith); linarith
  let a : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * (x / n) ^ c
  let E : ℕ → ℝ := fun n => a n * min 1 (1 / (T * |Real.log (x / n)|))
  let R : ℕ → ℝ := fun n => if n ∈ Finset.range (2 * N + 2) then 1 / |x - n| else 0
  let A : ℝ := 32 * x * Real.log x / T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR0 : ∀ n, 0 ≤ R n := by intro n; dsimp [R]; positivity
  have hRsupport : ∀ n ∉ Finset.range (2 * N + 2), R n = 0 := by intros; simp_all [R]
  have hRsum : Summable R := summable_of_ne_finset_zero hRsupport
  have hRbd : ∑' n, R n ≤ 16 * Real.log x := by
    rw [tsum_eq_sum hRsupport]
    have heq : (∑ n ∈ Finset.range (2 * N + 2), R n) =
        ∑ n ∈ Finset.range (2 * N + 2), 1 / |(N : ℝ) + 1 / 2 - n| := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [R, if_pos hn]
      rfl
    rw [heq]
    have hlog : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log x := by
      have hh : (N : ℝ) + 1 ≤ 2 * x := by dsimp [x]; have := Nat.cast_nonneg (α := ℝ) N; linarith
      have hh0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      calc
        _ ≤ Real.log (2 * x) := Real.log_le_log hh0 hh
        _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
        _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx]
    exact (half_integer_recip_sum197 N).trans (by nlinarith)
  have hcoeff : Summable a := LeanLab.DERZ1997.Perron136.perron_coeff_summable hx0 hc
  have hE : Summable E := hcoeff.of_nonneg_of_le (fun n => by dsimp [E, a]; positivity)
    (fun n => mul_le_of_le_one_right (by dsimp [a]; positivity) (min_le_left _ _))
  have hmajor : ∀ n, E n ≤ (2 / T) * a n + A * R n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [E, a] using mul_nonneg hA (hR0 0)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hfar : (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ n
    · have hh := mul_le_mul_of_nonneg_left (perron_far_cutoff197 hx0 hn0 hT0 hfar)
        (show 0 ≤ a n by dsimp [a]; positivity)
      dsimp [E]
      nlinarith [mul_nonneg hA (hR0 n)]
    · have hnlo : x / 2 ≤ n := by push_neg at hfar; linarith [hfar.1]
      have hnhi : (n : ℝ) ≤ 2 * x := by push_neg at hfar; linarith [hfar.2]
      have hmem : n ∈ Finset.range (2 * N + 2) := by
        apply Finset.mem_range.mpr
        have hh : (n : ℝ) < (2 * N + 2 : ℕ) := by push_cast; dsimp [x] at hnhi; linarith
        exact_mod_cast hh
      have hdist : 0 < |x - n| := by have := half_integer_distance197 N n; dsimp [x]; linarith
      have hne : x ≠ (n : ℝ) := sub_ne_zero.mp (abs_pos.mp hdist)
      have ha : a n ≤ 16 * Real.log x := by
        exact (mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)).trans
          (perron_near_coeff197 hx hnlo hnhi)
      have hh := mul_le_mul ha (perron_near_cutoff197 hx0 hn0 hT0 hnhi hne)
        (by positivity : 0 ≤ min 1 (1 / (T * |Real.log (x / n)|))) (by positivity)
      have heq : (16 * Real.log x) * (2 * x / (T * |x - n|)) = A * R n := by
        simp only [R, if_pos hmem, A]
        ring
      dsimp [E]
      exact (hh.trans_eq heq).trans (le_add_of_nonneg_left (by dsimp [a]; positivity))
  have hsum := hE.tsum_le_tsum hmajor ((hcoeff.mul_left (2 / T)).add (hRsum.mul_left A))
  rw [Summable.tsum_add (hcoeff.mul_left _) (hRsum.mul_left _), tsum_mul_left, tsum_mul_left] at hsum
  have habd : ∑' n, a n ≤ 24 * x * Real.log x ^ 2 := perron_coeff_bound197 hx
  have h1 := mul_le_mul_of_nonneg_left habd (by positivity : 0 ≤ 2 / T)
  have h2 := mul_le_mul_of_nonneg_left hRbd hA
  have hresult : ∑' n, E n ≤ 560 * (x * Real.log x ^ 2 / T) := by
    calc
      _ ≤ (2 / T) * (24 * x * Real.log x ^ 2) + A * (16 * Real.log x) := hsum.trans (add_le_add h1 h2)
      _ = _ := by dsimp [A]; ring
  change ∑' n, E n ≤ 560 * (x * Real.log x ^ 2 / T + Real.log x)
  exact hresult.trans (by nlinarith)

/-! ### Contour shift and the explicit formula -/

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. Reuses the proved logarithmic derivative residue limit from PNTPort.ExplicitPsi1. -/
theorem perron_residue_zero197 {x : ℝ} (hx : 0 < x) {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    residue (fK x) ρ = -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  apply residue_eq_of_tendsto
  have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) ρ :=
    (analyticAt_xpow hx ρ).div analyticAt_id h0
  have ht := ((tendsto_logDeriv_zeta_of_ne_one h1).mul
    (hk.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ)))).neg
  rw [show -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ =
    -((analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) by ring]
  refine ht.congr (fun s => ?_)
  simp only [fK, logDeriv_apply]
  ring

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. Reuses the simple pole of zeta at one. -/
theorem perron_residue_one197 {x : ℝ} (hx : 0 < x) :
    residue (fK x) 1 = (x : ℂ) := by
  apply residue_eq_of_tendsto
  have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) 1 :=
    (analyticAt_xpow hx 1).div analyticAt_id one_ne_zero
  have ht := (tendsto_logDeriv_zeta_one.mul
    (hk.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ)))).neg
  simpa only [cpow_one, div_one, neg_one_mul, neg_neg] using
    ht.congr (fun s => by simp only [fK, logDeriv_apply]; ring)

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. Reuses the proved value of the logarithmic derivative of zeta at zero. -/
theorem perron_residue_origin197 {x : ℝ} (hx : 0 < x) :
    residue (fK x) 0 = -(Real.log (2 * Real.pi) : ℂ) := by
  apply residue_eq_of_tendsto
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hH : AnalyticAt ℂ (fun s => -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s) 0 :=
    (analyticAt_logDeriv (by norm_num) hζ0).neg.mul (analyticAt_xpow hx 0)
  have ht := hH.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  simp only [cpow_zero, mul_one, logDeriv_zeta_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  simp only [fK, logDeriv_apply, sub_zero]
  field_simp

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108, the contour integrand. -/
theorem perron_integrand_meromorphic197 {x : ℝ} (hx : 0 < x) (z : ℂ) :
    MeromorphicAt (fK x) z := by
  have hz := meromorphicAt_zeta z
  change MeromorphicAt (fun s => -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s / s) z
  exact ((hz.deriv.div hz).neg.mul (analyticAt_xpow hx z).meromorphicAt).div analyticAt_id.meromorphicAt

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108, exclusion of the poles before the contour shift. -/
theorem perron_integrand_analytic197 {x : ℝ} (hx : 0 < x) {z : ℂ} (h0 : z ≠ 0)
    (h1 : z ≠ 1) (hz : riemannZeta z ≠ 0) : AnalyticAt ℂ (fK x) z := by
  change AnalyticAt ℂ (fun s => -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s / s) z
  exact ((analyticAt_logDeriv h1 hz).neg.mul (analyticAt_xpow hx z)).div analyticAt_id h0

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 105. Mathlib gives the von Mangoldt Dirichlet series identity on real part greater than one. -/
theorem perronPsi_eq_logDeriv197 {x c T : ℝ} (hc : 1 < c) :
    perronPsi x c T = (1 / (2 * Real.pi) : ℂ) *
      ∫ t in (-T)..T, fK x ((c : ℂ) + t * I) := by
  unfold perronPsi
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hc)]
  simp only [fK, logDeriv_apply]
  ring

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108, the simple-pole contour calculation. -/
theorem perron_integrand_order197 {x : ℝ} (hx : 0 < x) (z : ℂ) :
    -1 ≤ meromorphicOrderAt (fK x) z := by
  have hz := meromorphicAt_zeta z
  rcases eq_or_ne z 0 with rfl | h0
  · have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
    have hH : AnalyticAt ℂ (fun s => -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s) 0 :=
      (analyticAt_logDeriv (by norm_num) hζ0).neg.mul (analyticAt_xpow hx 0)
    have hF : fK x = (fun s => -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s) *
        (fun s : ℂ => s)⁻¹ := by funext s; simp [fK, logDeriv_apply, div_eq_mul_inv]
    have hinv : meromorphicOrderAt (fun s : ℂ => s)⁻¹ 0 = -1 := by
      rw [meromorphicOrderAt_inv]
      show -meromorphicOrderAt id (0 : ℂ) = -1
      rw [meromorphicOrderAt_id]
    rw [hF, meromorphicOrderAt_mul hH.meromorphicAt
      (show MeromorphicAt (fun s : ℂ => s)⁻¹ 0 from analyticAt_id.meromorphicAt.inv), hinv]
    have h := hH.meromorphicOrderAt_nonneg
    calc
      (-1 : WithTop ℤ) = 0 + -1 := by simp
      _ ≤ _ := add_le_add_left h _
  · have hF : fK x = (fun s => -logDeriv riemannZeta s) * (fun s : ℂ => (x : ℂ) ^ s / s) := by
      funext s
      simp only [fK, Pi.mul_apply]
      ring
    have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) z :=
      (analyticAt_xpow hx z).div analyticAt_id h0
    have hL : MeromorphicAt (fun s => -logDeriv riemannZeta s) z := (hz.deriv.div hz).neg
    rw [hF, meromorphicOrderAt_mul hL hk.meromorphicAt]
    have hneg : meromorphicOrderAt (fun s => -logDeriv riemannZeta s) z =
        meromorphicOrderAt (logDeriv riemannZeta) z := (meromorphicOrderAt_neg (f := logDeriv riemannZeta)).symm
    rw [hneg]
    calc
      (-1 : WithTop ℤ) = -1 + 0 := by simp
      _ ≤ _ := add_le_add (order_logDeriv_zeta_ge z) hk.meromorphicOrderAt_nonneg

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. Adapted from the proved smoothed rectangle identity in PNTPort.ExplicitPsi1.Residues, using the new unsmoothed residue calculations. -/
theorem perron_rect_explicit197 {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder ⟨-1 / 2, -T⟩ ⟨c, T⟩, riemannZeta z ≠ 0) :
    RectangleIntegral' (fK x) ⟨-1 / 2, -T⟩ ⟨c, T⟩ =
      x - (Real.log (2 * Real.pi) : ℂ) - ∑ ρ ∈ (zeros_rect_finite c T).toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ ρ / ρ) := by
  set R := Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ with hRdef
  set Zf := (zeros_rect_finite c T).toFinset with hZf
  have hmem := fun z => mem_rect (c := c) (T := T) (by linarith) hT.le (z := z)
  have h0R : (0 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have h1R : (1 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have hriemannZeta0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hZfR : ∀ ρ ∈ Zf, ρ ∈ R ∧ riemannZeta ρ = 0 := by
    intro ρ hρ; rw [hZf, Set.Finite.mem_toFinset] at hρ; exact ⟨hρ.1, hρ.2⟩
  -- analytic away from `0`, `1` and the zeros
  have hgood : ∀ z ∈ R, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → 0 ≤ meromorphicOrderAt (fK x) z :=
    fun z hz h0 h1 hriemannZeta => (perron_integrand_analytic197 hx h0 h1 hriemannZeta).meromorphicOrderAt_nonneg
  have hbR : RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  have hP : ∀ z ∈ R, meromorphicOrderAt (fK x) z < 0 → z ∈ (insert 0 (insert 1 Zf) : Finset ℂ) := by
    intro z hz hneg
    by_contra hns
    simp only [Finset.mem_insert, not_or] at hns
    obtain ⟨h0, h1, hZ⟩ := hns
    have hriemannZeta : riemannZeta z ≠ 0 := by
      intro h; apply hZ; rw [hZf, Set.Finite.mem_toFinset]; exact ⟨hz, h⟩
    exact absurd (hgood z hz h0 h1 hriemannZeta) (not_le.mpr hneg)
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := fK x)
    (z := ⟨-1 / 2, -T⟩) (w := ⟨c, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z _ => perron_integrand_meromorphic197 hx z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      rcases border_cases hz with h | h | h | h
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; norm_num at h)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg))
    (by
      apply (insert 0 (insert 1 Zf) : Finset ℂ).finite_toSet.subset
      intro z ⟨hz, hneg⟩
      exact hP z hz hneg)
    (fun z hz => perron_integrand_order197 hx z)
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt (fK x) z < 0} =
      ((insert 0 (insert 1 Zf) : Finset ℂ) : Set ℂ) ∩ {z | meromorphicOrderAt (fK x) z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hP z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩
      refine ⟨?_, hneg⟩
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact h0R
      · exact h1R
      · exact (hZfR z hz).1
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (perron_integrand_meromorphic197 hx z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' (insert 0 (insert 1 Zf)) (fun z => residue (fK x) z)]
  have h1Z : (1 : ℂ) ∉ Zf := fun h => riemannZeta_one_ne_zero (hZfR 1 h).2
  have h0Z : (0 : ℂ) ∉ insert 1 Zf := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨zero_ne_one, fun h => hriemannZeta0 (hZfR 0 h).2⟩
  rw [Finset.sum_insert h0Z, Finset.sum_insert h1Z, perron_residue_origin197 hx, perron_residue_one197 hx]
  have hsum : ∑ ρ ∈ Zf, residue (fK x) ρ =
      ∑ ρ ∈ Zf, -((analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    obtain ⟨hρR, hρ0⟩ := hZfR ρ hρ
    have hρne0 : ρ ≠ 0 := by rintro rfl; exact hriemannZeta0 hρ0
    have hρne1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hρ0
    rw [perron_residue_zero197 hx hρne0 hρne1]
    ring
  rw [hsum, Finset.sum_neg_distrib]
  ring

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 109, the suggested half-integer transfer. This is an auxiliary identity from the finite sum definition. -/
theorem psi_floor_half197 (x : ℝ) :
    Chebyshev.psi ((⌊x⌋₊ : ℝ) + 1 / 2) = Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_psi_coe_floor, add_comm, Nat.floor_add_natCast (by norm_num)]
  norm_num
  exact (Chebyshev.psi_eq_psi_coe_floor x).symm

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 109, the half-integer transfer. This is elementary floor arithmetic. -/
theorem floor_half_distance197 {x : ℝ} (hx : 0 ≤ x) :
    |x - ((⌊x⌋₊ : ℝ) + 1 / 2)| ≤ 1 / 2 := by
  rw [abs_le]
  constructor <;> linarith [Nat.floor_le hx, Nat.lt_floor_add_one x]

/-- Auxiliary step in the existing Perron and contour decomposition.
Auxiliary comparison for the proposed transfer in the explicit_formula_zeta leaf comment. Davenport chapter 17, page 109. The values are chosen here and are not a printed paper claim. -/
theorem zero_variation_majorant_too_large197 :
    1000 * (Real.log (10 ^ 6 : ℝ) ^ 2 + Real.log (10 ^ 6 : ℝ)) <
      (10 ^ 6 : ℝ) * Real.log (10 ^ 6 : ℝ) := by
  have hL0 : 0 < Real.log (10 ^ 6 : ℝ) := Real.log_pos (by norm_num)
  have hL : Real.log (10 ^ 6 : ℝ) < 60 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10) (by norm_num : (10 : ℝ) ≠ 1)]
  nlinarith

/-- Auxiliary step in the existing Perron and contour decomposition.
Auxiliary comparison for the character leaf. Davenport chapter 20, page 125. The values are chosen here and are not a printed paper claim. -/
theorem character_triangle_majorant_too_large197 :
    (1000 : ℝ) * Real.sqrt (10 ^ 12 : ℝ) * Real.log (10 ^ 12 : ℝ) ^ 2 < (10 ^ 12 : ℝ) := by
  have hL0 : 0 ≤ Real.log (10 ^ 12 : ℝ) := Real.log_nonneg (by norm_num)
  have hL : Real.log (10 ^ 12 : ℝ) < 28 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hten := LeanLab.DERZ1997.log_ten_lt'
    nlinarith
  have hs : Real.sqrt (10 ^ 12 : ℝ) = 10 ^ 6 := by norm_num
  rw [hs]
  nlinarith

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. Reuses the proved simple-trivial-zero limit in PNTPort.ExplicitPsi1.TrivialRect. -/
theorem perron_residue_trivial197 {x : ℝ} (hx : 0 < x) (n : ℕ) :
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
    (analyticAt_xpow hx ρ).div analyticAt_id h0
  have ht := ((tendsto_logDeriv_trivial n).mul
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

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. Adapted from the proved smoothed rect_left calculation in PNTPort.ExplicitPsi1.TrivialRect. -/
theorem perron_rect_left197 {x T : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) (hT : 0 < T) :
    RectangleIntegral' (fK x) ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩ =
      ∑ n ∈ Finset.range K, (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) := by
  classical
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hσle : σ ≤ -1 / 2 := by rw [hσ]; linarith
  set R := Rectangle (⟨σ, -T⟩ : ℂ) ⟨-1 / 2, T⟩ with hRdef
  have hmem := fun z => mem_rectL (σ := σ) (T := T) hσle hT.le (z := z)
  set tz : ℕ → ℂ := fun n => -2 * ((n : ℂ) + 1) with htz
  set P : Finset ℂ := (Finset.range K).image tz with hP
  have hRre : ∀ z ∈ R, z.re ≤ -1 / 2 := fun z hz => ((hmem z).mp hz).1.2
  have hR0 : ∀ z ∈ R, z ≠ 0 := by
    intro z hz h; have := hRre z hz; rw [h] at this; norm_num at this
  have hR1 : ∀ z ∈ R, z ≠ 1 := by
    intro z hz h; have := hRre z hz; rw [h] at this; norm_num at this
  have hgood : ∀ z ∈ R, riemannZeta z ≠ 0 → 0 ≤ meromorphicOrderAt (fK x) z :=
    fun z hz hriemannZeta => (perron_integrand_analytic197 hx (hR0 z hz) (hR1 z hz) hriemannZeta).meromorphicOrderAt_nonneg
  have htz_re : ∀ n : ℕ, (tz n).re = -2 * ((n : ℝ) + 1) := by intro n; simp [htz]
  have htz_im : ∀ n : ℕ, (tz n).im = 0 := by intro n; simp [htz]
  have hPR : ∀ z ∈ P, z ∈ R := by
    intro z hz
    rw [hP, Finset.mem_image] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    rw [hmem]
    have hn' : (n : ℝ) + 1 ≤ K := by
      have : n + 1 ≤ K := Finset.mem_range.mp hn
      exact_mod_cast this
    rw [htz_re, htz_im]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpoles : ∀ z ∈ R, meromorphicOrderAt (fK x) z < 0 → z ∈ P := by
    intro z hz hneg
    by_contra hns
    have hriemannZeta : riemannZeta z = 0 := by
      by_contra hriemannZeta
      exact absurd (hgood z hz hriemannZeta) (not_le.mpr hneg)
    obtain ⟨n, hn⟩ := zero_of_re_neg (by linarith [hRre z hz]) hriemannZeta
    apply hns
    rw [hP]
    rw [Finset.mem_image]
    refine ⟨n, Finset.mem_range.mpr ?_, hn.symm⟩
    have hre := ((hmem z).mp hz).1.1
    rw [hn] at hre
    simp at hre
    have : (n : ℝ) + 1 < K + 1 := by linarith
    have : n + 1 < K + 1 := by exact_mod_cast this
    omega
  have hbR : RectangleBorder (⟨σ, -T⟩ : ℂ) ⟨-1 / 2, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  obtain ⟨AL, _, hline⟩ := logDeriv_line
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := fK x)
    (z := ⟨σ, -T⟩) (w := ⟨-1 / 2, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z _ => perron_integrand_meromorphic197 hx z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      have hzz : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
      have hriemannZeta : riemannZeta z ≠ 0 := by
        rcases border_casesL hz with h' | h' | h' | h'
        · exact zeta_ne_zero_of_re_nonpos (by linarith [hRre z hzR]) (by rw [h']; linarith)
        · rw [hzz, h']; exact (hline K z.im).1
        · exact zeta_ne_zero_of_re_nonpos (by linarith [hRre z hzR]) (by rw [h']; linarith)
        · rw [hzz, h']; exact zeta_left_ne z.im
      exact absurd (hgood z hzR hriemannZeta) (not_le.mpr hneg))
    (by
      apply (P : Set ℂ).toFinite.subset
      intro z ⟨hz, hneg⟩
      exact hpoles z hz hneg)
    (fun z _ => perron_integrand_order197 hx z)
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt (fK x) z < 0} =
      (P : Set ℂ) ∩ {z | meromorphicOrderAt (fK x) z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hpoles z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩; exact ⟨hPR z hz, hneg⟩
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (perron_integrand_meromorphic197 hx z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' P (fun z => residue (fK x) z)]
  have hinj : Set.InjOn tz ((Finset.range K : Finset ℕ) : Set ℕ) := by
    intro a _ b _ h
    have := congr_arg Complex.re h
    rw [htz_re, htz_re] at this
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  rw [hP, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro n _
  rw [htz]
  exact perron_residue_trivial197 hx n

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. Reuses the conductor-free logarithmic derivative estimate on the far-left lines from PNTPort.ExplicitPsi1.LeftZeta. -/
theorem perron_left_edge_limit197 {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    Tendsto (fun K : ℕ => ∫ t in (-T)..T,
      fK x (((-2 * (K : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨A, hA, hline⟩ := logDeriv_line
  let M : ℝ := A * Real.log (T + 3) + A + 4
  have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb {K : ℕ} (hK : 1 ≤ K) {t : ℝ} (ht : t ∈ Set.uIoc (-T) T) :
      ‖fK x (((-2 * (K : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        M * x ^ (-2 * (K : ℝ) - 1 / 2) := by
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have htab : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hK0 : (0 : ℝ) < K := by linarith
    let z : ℂ := (((-2 * (K : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)
    have hden : (K : ℝ) ≤ ‖z‖ := by
      have hh := Complex.abs_re_le_norm z
      have hzre : z.re = -2 * (K : ℝ) - 1 / 2 := by simp [z]
      rw [hzre, abs_of_neg (by linarith)] at hh
      linarith
    have hnum : ‖deriv riemannZeta z / riemannZeta z‖ ≤ M * K := by
      have hh := (hline K t).2
      have hl := Real.log_le_log (by linarith [abs_nonneg t] : 0 < |t| + 3)
        (by linarith : |t| + 3 ≤ T + 3)
      have hAA : 0 ≤ A * Real.log (T + 3) + A := by positivity
      have hmul := mul_le_mul_of_nonneg_left hK1 hAA
      have hlog := mul_le_mul_of_nonneg_left hl hA.le
      dsimp [M]
      change ‖deriv riemannZeta z / riemannZeta z‖ ≤ _ at hh
      nlinarith
    change ‖-logDeriv riemannZeta z * (x : ℂ) ^ z / z‖ ≤ _
    rw [norm_div, norm_mul, norm_neg, logDeriv_apply,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hzre : z.re = -2 * (K : ℝ) - 1 / 2 := by simp [z]
    rw [hzre]
    apply (div_le_iff₀ (hK0.trans_le hden)).mpr
    have hp : 0 ≤ x ^ (-2 * (K : ℝ) - 1 / 2) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hnum hp
    have h2 := mul_le_mul_of_nonneg_left hden (mul_nonneg hM hp)
    nlinarith
  have hq0 : 0 ≤ x ^ (-2 : ℝ) := by positivity
  have hq1 : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hpow : Tendsto (fun K : ℕ => x ^ (-2 * (K : ℝ) - 1 / 2)) atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (x ^ (-(1 / 2 : ℝ)))
    simp only [zero_mul] at hg
    convert hg using 1
    funext K
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
  have hboundlim : Tendsto (fun K : ℕ => 2 * T * M * x ^ (-2 * (K : ℝ) - 1 / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (2 * T * M)
  apply squeeze_zero_norm' ?_ hboundlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with K hK
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hb hK ht)
  have hlen : |T - -T| = 2 * T := by rw [abs_of_pos (by linarith)]; ring
  rw [hlen] at hh
  convert hh using 1 <;> ring

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. Reuses the proved local partial fraction estimate and local zero count from PNTPort.ZetaZeros. This is an implication from the exact separation condition in contour_shift. -/
theorem perron_logDeriv_right197 : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 5 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      riemannZeta ((σ : ℂ) + I * T) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + I * T) / riemannZeta ((σ : ℂ) + I * T)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C1, hC1, hcount⟩ := zero_count_two
  obtain ⟨C2, hC2, hlocal⟩ := logDeriv_local
  refine ⟨100 * C1 + C2, by positivity, ?_⟩
  intro T hT hsep σ hσ
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < Real.log T := by linarith
  let δ := 1 / (100 * Real.log T)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity : 0 < 100 * Real.log T)).mpr
    linarith
  let s : ℂ := (σ : ℂ) + I * T
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = T := by simp [s]
  have hzs : riemannZeta s ≠ 0 := by
    intro hz
    have hσ1 : σ < 1 := lt_of_not_ge (fun h =>
      riemannZeta_ne_zero_of_one_le_re (by simpa [hsre] using h) hz)
    have hmem : s ∈ zetaZeros (T + 1) := by
      refine ⟨hz, by rw [hsre]; linarith [hσ.1], by rw [hsre]; exact hσ1, ?_⟩
      rw [hsim, abs_of_pos hT0]
      linarith
    have hh := hsep s hmem
    rw [hsim, sub_self, abs_zero] at hh
    linarith
  refine ⟨hzs, ?_⟩
  obtain ⟨hfin, hb⟩ := hlocal T (by rw [abs_of_pos hT0]; linarith)
  have hsc : ‖s - cen T‖ ≤ 1 := by
    have heq : s - cen T = ((σ - 3 / 2 : ℝ) : ℂ) := by simp only [s, cen]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hloc := hb s hsc hzs
  rw [abs_of_pos hT0] at hloc
  obtain ⟨hfin2, hsum2⟩ := hcount T hT
  have hsub : hfin.toFinset ⊆ hfin2.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    have hh := Complex.abs_im_le_norm (ρ - cen T)
    have heq : (ρ - cen T).im = ρ.im - T := by simp [cen]
    rw [heq] at hh
    linarith [hρ.2]
  have hdist : ∀ ρ ∈ hfin.toFinset, δ ≤ ‖s - ρ‖ := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hr := Complex.abs_re_le_norm (ρ - cen T)
    have hi := Complex.abs_im_le_norm (ρ - cen T)
    have hre : (ρ - cen T).re = ρ.re - 3 / 2 := by simp [cen]
    have him : (ρ - cen T).im = ρ.im - T := by simp [cen]
    rw [hre, abs_le] at hr
    rw [him, abs_le] at hi
    have hρre : 0 < ρ.re := by linarith [hρ.2, hr.1]
    have hρlt : ρ.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hρ.1)
    have hρim : 0 < ρ.im := by linarith [hρ.2, hi.1]
    have hsepρ : δ ≤ |ρ.im - T| := by
      by_cases hbound : |ρ.im| ≤ T + 1
      · exact hsep ρ ⟨hρ.1, hρre, hρlt, hbound⟩
      · have hlarge : T + 1 < ρ.im := by rw [abs_of_pos hρim] at hbound; linarith
        exact hδone.trans (by rw [abs_of_pos (by linarith)]; linarith)
    have hh := Complex.abs_im_le_norm (s - ρ)
    have heq : (s - ρ).im = T - ρ.im := by simp [hsim]
    rw [heq, abs_sub_comm] at hh
    exact hsepρ.trans hh
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
        (analyticOrderNatAt riemannZeta ρ : ℝ) / δ := by
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδpos (hdist ρ hρ)
  have hsum : ‖∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      100 * C1 * Real.log T ^ 2 := by
    calc
      _ ≤ ∑ ρ ∈ hfin.toFinset, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / δ := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) / δ := by rw [Finset.sum_div]
      _ ≤ (C1 * Real.log T) / δ := by
        apply div_le_div_of_nonneg_right _ hδpos.le
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans hsum2
      _ = _ := by dsimp [δ]; rw [div_div_eq_mul_div, div_one]; ring
  have htri := norm_add_le
    (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
    (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
  rw [sub_add_cancel] at htri
  have hlog : C2 * Real.log T ≤ C2 * Real.log T ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hC2.le
  exact htri.trans ((add_le_add hloc hsum).trans (by nlinarith))

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. Reuses the proved functional equation and digamma bounds from PNTPort.ZetaZeros.LeftHalf. -/
theorem perron_logDeriv_strip197 : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 5 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 2,
      riemannZeta ((σ : ℂ) + I * T) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + I * T) / riemannZeta ((σ : ℂ) + I * T)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C1, hC1, hg⟩ := perron_logDeriv_right197
  obtain ⟨K, hK, hψ⟩ := digamma_strip
  refine ⟨C1 + 2 * K + 10, by positivity, ?_⟩
  intro T hT hsep σ hσ
  have hgT := hg T hT hsep
  have hT1 : T ≤ T := le_rfl
  have hT2 : T ≤ T + 1 := by linarith
  have hlT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlT2 : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  rcases le_or_gt (1 / 2) σ with h | h
  · obtain ⟨hne, hb⟩ := hgT σ ⟨h, hσ.2⟩
    refine ⟨hne, hb.trans ?_⟩
    have : 0 ≤ Real.log T ^ 2 := by positivity
    nlinarith
  -- the left part, `-1/2 ≤ σ < 1/2`
  set s : ℂ := σ + I * T with hs
  set u : ℂ := ((1 - σ : ℝ) : ℂ) + I * T with hu
  have hw : 1 - s = conj u := by
    rw [hs, hu]; apply Complex.ext <;> simp
  obtain ⟨hune, hub⟩ := hgT (1 - σ) ⟨by linarith, by linarith [hσ.1]⟩
  have hsim : s.im = T := by simp [hs]
  have hsre : s.re = σ := by simp [hs]
  have hwre : 0 < (1 - s).re := by simp [hsre]; linarith
  have hwim : (1 - s).im ≠ 0 := by simp [hsim]; linarith
  have hriemannZetaw : riemannZeta (1 - s) ≠ 0 := by rw [hw, riemannZeta_conj]; exact (map_ne_zero _).mpr hune
  have hriemannZetas : riemannZeta s ≠ 0 := by
    have hw1 : (1 - s) ≠ 1 := by intro h; apply hwim; rw [h]; simp
    have := riemannZeta_one_sub (not_neg_nat_of_re_pos hwre) hw1
    rw [show 1 - (1 - s) = s by ring] at this
    rw [this]
    exact mul_ne_zero (feF_ne_zero hwre (not_odd_of_im hwim)) hriemannZetaw
  refine ⟨hriemannZetas, ?_⟩
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h; have := congr_arg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hFE := logDeriv_riemannZeta_one_sub hint hriemannZetas
  rw [logDeriv_apply, logDeriv_apply] at hFE
  -- the four pieces
  have h1 : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ C1 * Real.log T ^ 2 := by
    have := logDerivZeta_conj u
    simp only [Pi.div_apply] at this
    rw [hw, this, Complex.norm_conj]; exact hub
  have h2 : ‖Complex.log (2 * π)‖ ≤ 2 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact log_two_pi_le
  have h3 : ‖digamma s‖ ≤ K * (2 * Real.log T) + 2 := by
    have e : s = (σ : ℂ) + T * I := by rw [hs]; ring
    have hb := hψ T (by linarith) σ (by linarith [hσ.1]) (by linarith)
    rw [← e] at hb
    have hl : Real.log (T + 3) ≤ 2 * Real.log T := by
      calc Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    have : K * Real.log (T + 3) ≤ K * (2 * Real.log T) := by gcongr
    linarith
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    have e : (π : ℂ) * s / 2 = ((π * σ / 2 : ℝ) : ℂ) + ((π * T / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [e, norm_mul]
    have ht := norm_tan_le (x := π * σ / 2) (y := π * T / 2) (by nlinarith [Real.pi_gt_three])
    have hp : ‖(π : ℂ) / 2‖ ≤ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num; linarith [Real.pi_lt_four]
    calc _ ≤ 2 * 2 := mul_le_mul hp ht (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  rw [hFE]
  calc ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) + Complex.log (2 * π) - digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖digamma s‖ +
        ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (by rw [norm_neg])) le_rfl)) le_rfl)
    _ ≤ C1 * Real.log T ^ 2 + 2 + (K * (2 * Real.log T) + 2) + 4 := by gcongr
    _ ≤ (C1 + 2 * K + 10) * Real.log T ^ 2 := by nlinarith

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. Uses the strip bound, the functional equation estimate on the negative half-plane and the existing Dirichlet-series bound on the right. -/
theorem perron_logDeriv_horiz197 : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 5 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ σ : ℝ, σ ≤ 3 →
      riemannZeta ((σ : ℂ) + I * T) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + I * T) / riemannZeta ((σ : ℂ) + I * T)‖ ≤
        C * Real.log T ^ 2 * (1 + |σ|) := by
  obtain ⟨C1, hC1, hstrip⟩ := perron_logDeriv_strip197
  obtain ⟨A, hA, hleft⟩ := logDeriv_left_region
  let M : ℝ := ‖deriv riemannZeta ((3 / 2 : ℝ) : ℂ) / riemannZeta ((3 / 2 : ℝ) : ℂ)‖
  have hM : 0 ≤ M := norm_nonneg _
  let C : ℝ := C1 + M + 3 * A + 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hT hsep σ hσ
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hL2 : 1 ≤ Real.log T ^ 2 := by nlinarith
  have hLle : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  have hσ1 : 1 ≤ 1 + |σ| := by linarith [abs_nonneg σ]
  by_cases hneg : σ < -1 / 2
  · obtain ⟨hne, hb⟩ := hleft σ T hneg.le (by rw [abs_of_pos hT0]; linarith)
    have heq : (σ : ℂ) + (T : ℂ) * I = (σ : ℂ) + I * T := by ring
    rw [heq] at hne hb
    rw [abs_of_pos hT0] at hb
    refine ⟨hne, ?_⟩
    have hlog : Real.log (T + 3) ≤ 2 * Real.log T := by
      calc
        _ ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = _ := by rw [Real.log_pow]; norm_num
    have hlogA := mul_le_mul_of_nonneg_left hlog hA.le
    have hlogA2 := mul_le_mul_of_nonneg_left hLle (by positivity : 0 ≤ 2 * A)
    have hAA : A ≤ A * Real.log T ^ 2 := le_mul_of_one_le_right hA.le hL2
    have hnegσ : -σ = |σ| := (abs_of_neg (by linarith)).symm
    have hσL : |σ| ≤ Real.log T ^ 2 * |σ| := le_mul_of_one_le_left (abs_nonneg _) hL2
    have hCC : 3 * A + 1 ≤ C := by dsimp [C]; nlinarith
    have hpos : 0 ≤ 3 * A * Real.log T ^ 2 * |σ| := by positivity
    have hinner : A * Real.log (T + 3) - σ + A ≤
        (3 * A + 1) * Real.log T ^ 2 * (1 + |σ|) := by rw [sub_eq_add_neg, hnegσ]; nlinarith
    exact hb.trans (hinner.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (sq_nonneg _)) (by positivity)))
  · have hσlo : -1 / 2 ≤ σ := le_of_not_gt hneg
    by_cases hσhi : σ ≤ 2
    · obtain ⟨hne, hb⟩ := hstrip T hT hsep σ ⟨hσlo, hσhi⟩
      refine ⟨hne, hb.trans ?_⟩
      have hCC : C1 ≤ C := by dsimp [C]; nlinarith
      exact (mul_le_mul_of_nonneg_right hCC (sq_nonneg _)).trans
        (le_mul_of_one_le_right (mul_nonneg hC.le (sq_nonneg _)) hσ1)
    · have hσ2 : 2 < σ := lt_of_not_ge hσhi
      have hne : riemannZeta ((σ : ℂ) + I * T) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
      refine ⟨hne, ?_⟩
      have hb : ‖deriv riemannZeta ((σ : ℂ) + I * T) / riemannZeta ((σ : ℂ) + I * T)‖ ≤ M :=
        logDeriv_right_le (by simp; linarith)
      have hMC : M ≤ C := by dsimp [C]; nlinarith
      exact hb.trans (hMC.trans ((le_mul_of_one_le_right hC.le hL2).trans
        (le_mul_of_one_le_right (mul_nonneg hC.le (sq_nonneg _)) hσ1)))

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. The bounded-height part is a new auxiliary compactness derivation of the same classical estimate. The unbounded part reuses the proved local partial fraction and functional equation bounds. -/
theorem perron_logDeriv_all197 : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ σ : ℝ, σ ≤ 3 →
      riemannZeta ((σ : ℂ) + I * T) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + I * T) / riemannZeta ((σ : ℂ) + I * T)‖ ≤
        C * Real.log T ^ 2 * (1 + |σ|) := by
  have hlow : ∃ M : ℝ, 0 < M ∧ ∀ T ∈ Set.Icc (2 : ℝ) 5,
      (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
      ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) 3,
        riemannZeta ((σ : ℂ) + I * T) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + I * T) / riemannZeta ((σ : ℂ) + I * T)‖ ≤ M := by
    let δ : ℝ := 1 / (100 * Real.log 5)
    have hL5 : 1 ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5)]
      linarith [Real.exp_one_lt_d9]
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ1 : δ ≤ 1 := by
      dsimp [δ]
      apply (div_le_one (by positivity : 0 < 100 * Real.log 5)).mpr
      linarith
    let R : Set ℂ := Complex.reProdIm (Set.Icc (-1 / 2 : ℝ) 3) (Set.Icc (2 : ℝ) 5)
    let K : Set ℂ := R ∩ ⋂ ρ ∈ zetaZeros 6, {s : ℂ | δ ≤ |s.im - ρ.im|}
    have hclosed : IsClosed (⋂ ρ ∈ zetaZeros 6, {s : ℂ | δ ≤ |s.im - ρ.im|}) := by
      apply isClosed_biInter
      intro ρ hρ
      exact isClosed_le continuous_const ((Complex.continuous_im.sub continuous_const).abs)
    have hK : IsCompact K := by
      dsimp [K, R]
      exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right hclosed
    have hmem (s : ℂ) (hs : s ∈ K) :
        s.re ∈ Set.Icc (-1 / 2 : ℝ) 3 ∧ s.im ∈ Set.Icc (2 : ℝ) 5 ∧
        ∀ ρ ∈ zetaZeros 6, δ ≤ |s.im - ρ.im| := by
      simp only [K, R, Set.mem_inter_iff, Complex.mem_reProdIm, Set.mem_iInter, Set.mem_ofPred_eq] at hs
      exact ⟨hs.1.1, hs.1.2, hs.2⟩
    have hne (s : ℂ) (hs : s ∈ K) : riemannZeta s ≠ 0 := by
      intro hz
      obtain ⟨hre, him, hsep⟩ := hmem s hs
      have hIm : s.im ≠ 0 := by linarith [him.1]
      have hr0 : 0 < s.re := lt_of_not_ge (fun h => zeta_ne_zero_of_re_nonpos h hIm hz)
      have hr1 : s.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
      have hsZ : s ∈ zetaZeros 6 := ⟨hz, hr0, hr1, by rw [abs_of_pos (by linarith [him.1])]; linarith [him.2]⟩
      have hh := hsep s hsZ
      rw [sub_self, abs_zero] at hh
      linarith
    have hcont : ContinuousOn (fun s : ℂ => deriv riemannZeta s / riemannZeta s) K := by
      intro s hs
      have h1 : s ≠ 1 := by
        intro hh
        have := (hmem s hs).2.1.1
        rw [hh] at this
        norm_num at this
      exact (analyticAt_logDeriv h1 (hne s hs)).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨max B 1, by positivity, ?_⟩
    intro T hT hsep σ hσ
    have hT0 : 0 < T := by linarith [hT.1]
    have hLT : 0 < Real.log T := Real.log_pos (by linarith [hT.1])
    have hlog : Real.log T ≤ Real.log 5 := Real.log_le_log hT0 hT.2
    have hδT : δ ≤ 1 / (100 * Real.log T) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hlog (by norm_num))
    let s : ℂ := (σ : ℂ) + I * T
    have hs : s ∈ K := by
      simp only [K, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · simpa [R, s, Complex.mem_reProdIm] using And.intro hσ hT
      · intro ρ hρ
        have heq : s.im = T := by simp [s]
        rw [heq, abs_sub_comm]
        by_cases hbound : |ρ.im| ≤ T + 1
        · exact hδT.trans (hsep ρ ⟨hρ.1, hρ.2.1, hρ.2.2.1, hbound⟩)
        · have hh := abs_sub_abs_le_abs_sub ρ.im T
          rw [abs_of_pos hT0] at hh
          have hlarge : 1 < |ρ.im - T| := by linarith
          exact hδ1.trans hlarge.le
    exact ⟨hne s hs, (hB s hs).trans (le_max_left _ _)⟩
  obtain ⟨M, hM, hl⟩ := hlow
  obtain ⟨C1, hC1, hg⟩ := perron_logDeriv_horiz197
  obtain ⟨A, hA, hleft⟩ := logDeriv_left_region
  let B : ℝ := M + 4 * A + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := C1 + 4 * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hT hsep σ hσ
  by_cases hlarge : 5 ≤ T
  · obtain ⟨hne, hb⟩ := hg T hlarge hsep σ hσ
    refine ⟨hne, hb.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ 1 + |σ|)
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _)
  have hT5 : T ≤ 5 := le_of_not_ge hlarge
  have hT0 : 0 < T := by linarith
  have hLT : 1 / 2 ≤ Real.log T := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    have := Real.log_two_gt_d9
    linarith
  have hL2 : 1 ≤ 4 * Real.log T ^ 2 := by nlinarith
  have hBC : B ≤ C * Real.log T ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hL2 hB.le
    have hCC : 4 * B ≤ C := by dsimp [C]; linarith
    exact (show B ≤ 4 * B * Real.log T ^ 2 by nlinarith).trans
      (mul_le_mul_of_nonneg_right hCC (sq_nonneg _))
  have hscale : B * (1 + |σ|) ≤ C * Real.log T ^ 2 * (1 + |σ|) :=
    mul_le_mul_of_nonneg_right hBC (by positivity)
  by_cases hneg : σ < -1 / 2
  · obtain ⟨hne, hb⟩ := hleft σ T hneg.le (by rw [abs_of_pos hT0]; linarith)
    have heq : (σ : ℂ) + (T : ℂ) * I = (σ : ℂ) + I * T := by ring
    rw [heq] at hne hb
    rw [abs_of_pos hT0] at hb
    refine ⟨hne, hb.trans ?_⟩
    have hlog : Real.log (T + 3) ≤ 3 := by
      calc
        _ ≤ Real.log 8 := Real.log_le_log (by linarith) (by linarith)
        _ ≤ 3 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          norm_num only [Nat.cast_ofNat]
          linarith [Real.log_two_lt_d9]
    have hAlog := mul_le_mul_of_nonneg_left hlog hA.le
    have hB4 : 4 * A ≤ B := by dsimp [B]; linarith
    have hB1 : 1 ≤ B := by dsimp [B]; linarith
    have hσB := mul_le_mul_of_nonneg_right hB1 (abs_nonneg σ)
    have hinner : A * Real.log (T + 3) - σ + A ≤ B * (1 + |σ|) := by
      rw [abs_of_neg (by linarith)] at hσB ⊢
      nlinarith
    exact hinner.trans hscale
  · obtain ⟨hne, hb⟩ := hl T ⟨hT, hT5⟩ hsep σ ⟨le_of_not_gt hneg, hσ⟩
    refine ⟨hne, hb.trans ?_⟩
    have hMB : M ≤ B := by dsimp [B]; linarith
    exact (hMB.trans (le_mul_of_one_le_right hB.le (by linarith [abs_nonneg σ]))).trans hscale

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. The negative half-line uses an explicit exponential primitive. The positive part uses x to the power c equal to e x. -/
theorem perron_horizontal_bound197 : ∃ B : ℝ, 0 < B ∧ ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ a : ℝ, a ≤ 0 → ∀ y ∈ ({T, -T} : Set ℝ),
      IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume a (1 + 1 / Real.log x) ∧
      ‖∫ u in a..(1 + 1 / Real.log x), fK x ((u : ℂ) + y * I)‖ ≤
        B * (x * Real.log T ^ 2 / T) := by
  obtain ⟨C, hC, hline⟩ := perron_logDeriv_all197
  have hnegative {a : ℝ} (ha : a ≤ 0) :
      ∫ u in a..0, Real.exp (u / 2) * (1 - u) ≤ 6 := by
    have hd (u : ℝ) : HasDerivAt (fun v : ℝ => (6 - 2 * v) * Real.exp (v / 2))
        (Real.exp (u / 2) * (1 - u)) u := by
      have h1 : HasDerivAt (fun v : ℝ => 6 - 2 * v) (-2) u := by
        convert (hasDerivAt_const u (6 : ℝ)).sub ((hasDerivAt_id u).const_mul 2) using 1
        · funext v
          simp [id]
        · norm_num
      have h2 : HasDerivAt (fun v : ℝ => Real.exp (v / 2)) (Real.exp (u / 2) / 2) u := by
        convert ((hasDerivAt_id u).div_const 2).exp using 1
        · funext v
          simp [id, div_eq_mul_inv]
        · simp [id, div_eq_mul_inv]
      convert h1.mul h2 using 1 <;> ring
    have hi : IntervalIntegrable (fun u : ℝ => Real.exp (u / 2) * (1 - u)) volume a 0 :=
      (by fun_prop : Continuous (fun u : ℝ => Real.exp (u / 2) * (1 - u))).intervalIntegrable _ _
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
    rw [heq]
    have hp : 0 ≤ (6 - 2 * a) * Real.exp (a / 2) := mul_nonneg (by linarith) (Real.exp_pos _).le
    norm_num only [mul_zero, sub_zero, zero_div, Real.exp_zero, mul_one]
    linarith
  refine ⟨39 * C, by positivity, ?_⟩
  intro x T hx hT hsep a ha y hy
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hLx : 1 / 2 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_two_gt_d9
    linarith
  have hLx0 : 0 < Real.log x := by linarith
  let c : ℝ := 1 + 1 / Real.log x
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc3 : c ≤ 3 := by
    have hh : 1 / Real.log x ≤ 2 := (div_le_iff₀ hLx0).mpr (by linarith)
    dsimp [c]
    linarith
  have hxc : x ^ c ≤ 3 * x := by
    have heq : x ^ c = x * Real.exp 1 := by
      dsimp [c]
      rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
      congr 1
      rw [mul_one_div_cancel hLx0.ne']
    rw [heq]
    nlinarith [Real.exp_one_lt_three]
  let D : ℝ := C * Real.log T ^ 2 / T
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hyT : |y| = T := by rcases hy with rfl | rfl <;> simp [abs_of_pos hT0]
  have hy0 : y ≠ 0 := by intro hh; rw [hh, abs_zero] at hyT; linarith
  have hbound : ∀ u : ℝ, u ≤ 3 →
      riemannZeta ((u : ℂ) + y * I) ≠ 0 ∧
      ‖deriv riemannZeta ((u : ℂ) + y * I) / riemannZeta ((u : ℂ) + y * I)‖ ≤
        C * Real.log T ^ 2 * (1 + |u|) := by
    intro u hu
    obtain ⟨hne, hb⟩ := hline T hT hsep u hu
    have heq : (u : ℂ) + I * T = (u : ℂ) + T * I := by ring
    rw [heq] at hne hb
    rcases hy with rfl | rfl
    · exact ⟨hne, hb⟩
    · have heq : (u : ℂ) + ((-T : ℝ) : ℂ) * I = conj ((u : ℂ) + T * I) := by
        apply Complex.ext <;> simp
      rw [heq, riemannZeta_conj, deriv_riemannZeta_conj]
      refine ⟨fun hh => hne (by simpa using hh), ?_⟩
      rw [← map_div₀, RCLike.norm_conj]
      exact hb
  have hpoint {u : ℝ} (hu : u ≤ 3) :
      ‖fK x ((u : ℂ) + y * I)‖ ≤ D * x ^ u * (1 + |u|) := by
    let z : ℂ := (u : ℂ) + y * I
    have hden : T ≤ ‖z‖ := by
      have hh := Complex.abs_im_le_norm z
      simpa [z, hyT] using hh
    have hn := (hbound u hu).2
    change ‖-logDeriv riemannZeta z * (x : ℂ) ^ z / z‖ ≤ _
    rw [norm_div, norm_mul, norm_neg, logDeriv_apply,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : z.re = u := by simp [z]
    rw [hre]
    calc
      _ ≤ (C * Real.log T ^ 2 * (1 + |u|)) * x ^ u / ‖z‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity)) (norm_nonneg _)
      _ ≤ (C * Real.log T ^ 2 * (1 + |u|)) * x ^ u / T :=
        div_le_div_of_nonneg_left (by positivity) hT0 hden
      _ = _ := by dsimp [D]; ring
  have hcont : ContinuousOn (fun u : ℝ => fK x ((u : ℂ) + y * I)) (Set.Icc a c) := by
    intro u hu
    have hzne := (hbound u (by linarith [hu.2])).1
    have hz0 : (u : ℂ) + y * I ≠ 0 := by
      intro hh
      have hi := congrArg Complex.im hh
      simp at hi
      exact hy0 hi
    have hz1 : (u : ℂ) + y * I ≠ 1 := by
      intro hh
      have hi := congrArg Complex.im hh
      simp at hi
      exact hy0 hi
    have hcA : ContinuousAt (fK x) ((u : ℂ) + y * I) :=
      (perron_integrand_analytic197 hx0 hz0 hz1 hzne).continuousAt
    have hcB : ContinuousAt (fun v : ℝ => (v : ℂ) + y * I) u := by fun_prop
    have hcC : ContinuousAt (fun v : ℝ => fK x ((v : ℂ) + y * I)) u :=
      ContinuousAt.comp (g := fK x) (f := fun v : ℝ => (v : ℂ) + y * I) hcA hcB
    exact hcC.continuousWithinAt
  have hac : a ≤ c := by linarith
  have hint : IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume a c := hcont.intervalIntegrable_of_Icc hac
  refine ⟨hint, ?_⟩
  have hi0 : IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume a 0 := (hcont.mono (Set.Icc_subset_Icc le_rfl hc0.le)).intervalIntegrable_of_Icc ha
  have h0i : IntervalIntegrable (fun u : ℝ => fK x ((u : ℂ) + y * I)) volume 0 c := (hcont.mono (Set.Icc_subset_Icc ha le_rfl)).intervalIntegrable_of_Icc hc0.le
  have hneg : ‖∫ u in a..0, fK x ((u : ℂ) + y * I)‖ ≤ 6 * D := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun u : ℝ => fK x ((u : ℂ) + y * I))
      (g := fun u : ℝ => D * (Real.exp (u / 2) * (1 - u))) ha
      (Filter.Eventually.of_forall (fun u hu => by
        have hu0 : u ≤ 0 := hu.2
        have hxp : x ^ u ≤ Real.exp (u / 2) := by
          rw [Real.rpow_def_of_pos hx0]
          apply Real.exp_le_exp.mpr
          have hmul := mul_le_mul_of_nonpos_right hLx hu0
          nlinarith
        calc
          _ ≤ D * x ^ u * (1 + |u|) := hpoint (by linarith)
          _ = D * (x ^ u * (1 - u)) := by rw [abs_of_nonpos hu0]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxp (by linarith)) hD))
      ((by fun_prop : Continuous (fun u : ℝ => D * (Real.exp (u / 2) * (1 - u)))).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh.trans (by have := mul_le_mul_of_nonneg_left (hnegative ha) hD; nlinarith)
  have hpos : ‖∫ u in (0 : ℝ)..c, fK x ((u : ℂ) + y * I)‖ ≤ 36 * D * x := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := c) (C := 12 * D * x) (fun u hu => by
        rw [Set.uIoc_of_le hc0.le] at hu
        have hu0 : 0 ≤ u := hu.1.le
        have hpow : x ^ u ≤ 3 * x :=
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hu.2).trans hxc
        have hab : 1 + |u| ≤ 4 := by rw [abs_of_nonneg hu0]; linarith [hu.2]
        calc
          _ ≤ D * x ^ u * (1 + |u|) := hpoint (by linarith [hu.2])
          _ ≤ D * (3 * x) * 4 := mul_le_mul (mul_le_mul_of_nonneg_left hpow hD) hab
            (by positivity) (by positivity)
          _ = _ := by ring)
    rw [sub_zero, abs_of_pos hc0] at hh
    exact hh.trans (by have := mul_le_mul_of_nonneg_left hc3 (show 0 ≤ 12 * D * x by positivity); nlinarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 h0i]
  have hh := norm_add_le (∫ u in a..0, fK x ((u : ℂ) + y * I)) (∫ u in (0 : ℝ)..c, fK x ((u : ℂ) + y * I))
  have hscale := mul_le_mul_of_nonneg_left hx hD
  have hsum : ‖(∫ u in a..0, fK x ((u : ℂ) + y * I)) + (∫ u in (0 : ℝ)..c, fK x ((u : ℂ) + y * I))‖ ≤
      39 * D * x := hh.trans (by nlinarith)
  convert hsum using 1 <;> dsimp [D] <;> ring

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. This bridges the rectangle notation and the sealed zero sum. -/
theorem perron_zeros_rect197 {c T : ℝ} (hc : 1 < c) (hT : 0 ≤ T) :
    Rectangle ⟨-1/2, -T⟩ ⟨c, T⟩ ∩ riemannZetaZeros = zetaZeros T := by
  ext z
  rw [Set.mem_inter_iff, mem_rect (by linarith) hT]
  change ((-1/2 ≤ z.re ∧ z.re ≤ c) ∧ -T ≤ z.im ∧ z.im ≤ T) ∧ riemannZeta z = 0 ↔ _
  constructor
  · rintro ⟨⟨hr, hi⟩, hz⟩
    have hlt : z.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hz
    have hpos : 0 < z.re := by
      by_contra h
      have hn : z.re ≤ 0 := le_of_not_gt h
      by_cases hneg : z.re < 0
      · obtain ⟨n, he⟩ := zero_of_re_neg hneg hz
        have hh := congrArg Complex.re he
        simp at hh
        have := Nat.cast_nonneg (α := ℝ) n
        linarith [hr.1]
      · have he : z.re = 0 := le_antisymm hn (le_of_not_gt hneg)
        by_cases him : z.im ≠ 0
        · exact zeta_ne_zero_of_re_nonpos hn him hz
        · have hz0 : z = 0 := Complex.ext he (not_ne_iff.mp him)
          norm_num [hz0, riemannZeta_zero] at hz
    exact ⟨hz, hpos, hlt, abs_le.mpr hi⟩
  · rintro ⟨hz, hp, hl, hi⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, abs_le.mp hi⟩, hz⟩

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 108-109. Algebraic form of the trivial zero contribution. -/
theorem perron_triv_sum197 (x : ℝ) (K : ℕ) :
    (∑ n ∈ Finset.range K, (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) /
      (2 * ((n : ℂ) + 1))) = (TrivU x K : ℂ) := by
  unfold TrivU
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have he : (-2 * ((n : ℂ) + 1)) = ((-(2 * (n+1) : ℤ) : ℤ) : ℂ) := by push_cast; ring
  rw [he, Complex.cpow_intCast, zpow_neg, show (2 * ((n : ℤ) + 1)) = (2 * (n+1) : ℕ) by omega,
    zpow_natCast, pow_mul, inv_pow]

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, page 108. The oriented rectangle identity is algebraic. -/
theorem perron_rect_decomp197 (x a b T : ℝ) :
    RectangleIntegral' (fK x) ⟨a,-T⟩ ⟨b,T⟩ =
      (1/(2*Real.pi):ℂ) * ((∫ t in -T..T, fK x ((b:ℂ)+t*I)) -
        (∫ t in -T..T, fK x ((a:ℂ)+t*I))) +
      (1/(2*Real.pi*I):ℂ) * ((∫ u in a..b, fK x ((u:ℂ)+(-T:ℝ)*I)) -
        (∫ u in a..b, fK x ((u:ℂ)+T*I))) := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : I ≠ 0 := I_ne_zero
  rw [div_mul_eq_mul_div, one_mul]
  field_simp
  ring

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapters 19-20, the character version of Perron formula from chapter 17, pages 105-106. The proof uses character norm at most one and the already proved kernel bounds. -/
theorem perron_character_error197 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x c T : ℝ} (hx : 2 ≤ x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hc : 1 < c)
    (hT : 0 < T) :
    ‖psiChi χ x - ∑' n : ℕ, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * perronI (x / n) c T‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (x / n) ^ c *
        min 1 (1 / (T * |Real.log (x / n)|)) := by
  classical
  have hx0 : 0 < x := by linarith
  let a : ℕ → ℂ := fun n => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) *
    (if (n : ℝ) < x then 1 else 0)
  let b : ℕ → ℂ := fun n => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * perronI (x / n) c T
  let E : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * (x / n) ^ c *
    min 1 (1 / (T * |Real.log (x / n)|))
  have hE0 : ∀ n, 0 ≤ E n := fun n => by dsimp [E]; positivity
  have hE : Summable E := by
    apply (LeanLab.DERZ1997.Perron136.perron_coeff_summable hx0 hc).of_nonneg_of_le hE0
    intro n
    exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  have ha0 : ∀ n ∉ Finset.range (⌊x⌋₊ + 1), a n = 0 := by
    intro n hn
    have hn' : ⌊x⌋₊ < n := by simpa using hn
    have hnx : x < n := (Nat.floor_lt hx0.le).mp hn'
    simp [a, not_lt.mpr hnx.le]
  have ha : Summable a := summable_of_ne_finset_zero ha0
  have hat : ∑' n, a n = psiChi χ x := by
    rw [tsum_eq_sum ha0]
    unfold psiChi
    have hr : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
      ext n; simp
    rw [hr, Finset.sum_insert (by simp)]
    simp [a]
    apply Finset.sum_congr rfl
    intro n hn
    have hnx : (n : ℝ) < x := lt_of_le_of_ne
      ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Ioc.mp hn).2) (hxn n)
    simp [hnx]
  have he : ∀ n, ‖a n - b n‖ ≤ E n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a, b, E]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hratio0 : 0 < x / n := div_pos hx0 hn0
    have hratio : x / (n : ℝ) ≠ 1 := by
      intro h
      exact hxn n ((div_eq_one_iff_eq hn0.ne').mp h).symm
    have hk : ‖perronI (x / n) c T - (if (n : ℝ) < x then 1 else 0)‖ ≤
        (x / n) ^ c * min 1 (1 / (T * |Real.log (x / n)|)) := by
      by_cases hnx : (n : ℝ) < x
      · have hy : 1 < x / (n : ℝ) := (one_lt_div hn0).mpr hnx
        simpa [hnx, abs_of_pos (Real.log_pos hy)] using perron_gt_one hy (by linarith) hT
      · have hy : x / (n : ℝ) < 1 := (div_lt_one hn0).mpr
          (lt_of_le_of_ne (le_of_not_gt hnx) (hxn n).symm)
        simpa [hnx] using perron_lt_one hratio0 hy (by linarith) hT
    have hh : ‖(χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))‖ ≤ ArithmeticFunction.vonMangoldt n := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
    rw [show a n - b n = -((χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
      (perronI (x / n) c T - (if (n : ℝ) < x then 1 else 0))) by dsimp [a,b]; ring,
      norm_neg, norm_mul]
    exact (mul_le_mul hh hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (by dsimp [E]; ring)
  have hd : Summable (fun n => a n - b n) := hE.of_norm_bounded he
  have hb : Summable b := by
    convert ha.sub hd using 1
    funext n
    simp
  rw [← hat, ← ha.tsum_sub hb]
  exact tsum_of_norm_bounded hE.hasSum he

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapters 19-20 and chapter 17, pages 105-106, character Perron formula. Mathlib LSeriesSummable_twist_vonMangoldt and the existing coefficient majorant supply convergence. -/
theorem perron_character_tsum197 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t in -T..T,
      LSeries (fun n => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) *
        (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) = ∑' n : ℕ, (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) * perronI (x / n) c T := by
  let F : ℕ → ℝ → ℂ := fun n t => (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
      ((c : ℂ) + t * I)
  have hnorm : ∀ n t, ‖F n t‖ = ‖χ (n : ZMod q)‖ * ArithmeticFunction.vonMangoldt n * (x / n) ^ c * ‖(1 : ℂ) / ((c : ℂ) + t * I)‖ := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [F]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      norm_cpow_eq_rpow_re_of_pos (div_pos hx hn0)]
    simp [div_eq_mul_inv]
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
        simp at this
        linarith
    exact hc.intervalIntegrable _ _
  have hcoeff : Summable (fun n : ℕ => ‖χ (n : ZMod q)‖ * ArithmeticFunction.vonMangoldt n * (x / n) ^ c) := by
    apply (LeanLab.DERZ1997.Perron136.perron_coeff_summable hx hc).of_nonneg_of_le (fun n => by positivity)
    intro n
    have hh := mul_le_of_le_one_left (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (χ.norm_le_one (n : ZMod q))
    exact mul_le_mul_of_nonneg_right hh (by positivity)
  have hsum : Summable (fun n : ℕ => ∫ t in Ioc (-T) T, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact hcoeff.mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hr : ∀ t : ℝ, ∑' n, F n t = LSeries (fun n => (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) ((c : ℂ) + t * I) *
        (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
    intro t
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
  have hl : ∀ n : ℕ, (1 / (2 * Real.pi) : ℂ) * (∫ t in Ioc (-T) T, F n t) =
      (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) * perronI (x / n) c T := by
    intro n
    unfold perronI
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    dsimp [F]
    rw [show (fun t : ℝ => (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I)) =
      (fun t : ℝ => (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) * (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I))) by funext t; ring, integral_const_mul]
    ring
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  simp_rw [← hr]
  rw [← key, ← tsum_mul_left]
  exact tsum_congr hl

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 105-107, and chapters 19-20, the character Perron formula. Mathlib supplies the logarithmic derivative series identity. This closes the Perron part of explicit_formula_chi_GRH without asserting the missing character contour estimate. -/
theorem perron_character_tail197 : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℕ), 2 ≤ N → ∀ T : ℝ, 2 ≤ T →
    let x : ℝ := N + 1/2
    let c : ℝ := 1 + 1 / Real.log x
    ‖psiChi χ x - (1/(2*Real.pi):ℂ) * (∫ t in -T..T,
      (-deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I) /
        DirichletCharacter.LFunction χ ((c:ℂ)+t*I)) *
      (x:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖ ≤
        C * (x * Real.log x^2/T + Real.log x) := by
  obtain ⟨C, hC⟩ := perron_tail
  refine ⟨C, ?_⟩
  intro q hq χ N hN T hT
  dsimp only
  let x : ℝ := N + 1/2
  let c : ℝ := 1 + 1 / Real.log x
  have hx : 2 ≤ x := by
    have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]; linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlog]
  have hT0 : 0 < T := by linarith
  have hxn (n:ℕ) : (n:ℝ) ≠ x := by
    intro hn
    have hh := half_integer_distance197 N n
    change 1/2 ≤ |x - n| at hh
    rw [hn, sub_self, abs_zero] at hh
    norm_num at hh
  have hid (t:ℝ) : LSeries (fun n => χ (n:ZMod q) * (ArithmeticFunction.vonMangoldt n:ℂ)) ((c:ℂ)+t*I) =
      -deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I) / DirichletCharacter.LFunction χ ((c:ℂ)+t*I) := by
    have hs : 1 < ((c:ℂ)+t*I).re := by simpa using hc
    have hh := χ.LSeries_twist_vonMangoldt_eq hs
    change LSeries (fun n => χ (n:ZMod q) * (ArithmeticFunction.vonMangoldt n:ℂ)) ((c:ℂ)+t*I) = _ at hh
    rw [hh, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
  change ‖psiChi χ x - (1/(2*Real.pi):ℂ) * (∫ t in -T..T,
      (-deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I) / DirichletCharacter.LFunction χ ((c:ℂ)+t*I)) *
      (x:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖ ≤ _
  simp_rw [← hid]
  rw [perron_character_tsum197 χ hx0 hc hT0]
  exact (perron_character_error197 χ hx hxn hc hT0).trans (hC N hN T hT)

/-- LEAF. Contour shift: there is an absolute `C` such that for `x ≥ 2`, `T ≥ 2` at distance
at least `1/(100 log T)` from every ordinate with `|γ| ≤ T + 1`, and `c = 1 + 1/log x`,
the truncated Perron integral of `-ζ'/ζ` equals
`x - ∑_{|γ| ≤ T} m_ρ x^ρ/ρ - log 2π - (1/2) log(1 - x^{-2})` up to `C x log² T / T`.
Residues at `1`, at the zeros, at `0` (`ζ'(0)/ζ(0) = log 2π`) and at `-2, -4, ...`;
horizontal sides bounded by `|ζ'/ζ(σ ± iT)| ≪ log² T`. Davenport ch. 17, p. 108-109.
Unit U-1529. -/
theorem contour_shift : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ hfin : (zetaZeros T).Finite,
      ‖perronPsi x (1 + 1 / Real.log x) T -
          ((x : ℂ) - ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
            - Real.log (2 * Real.pi) - (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ)))‖ ≤
        C * (x * Real.log T ^ 2 / T) := by
  obtain ⟨B, hB, hhor⟩ := perron_horizontal_bound197
  obtain ⟨C, hC, hline⟩ := perron_logDeriv_all197
  refine ⟨2 * B, ?_⟩
  intro x T hx hT hsep hfin
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  let c : ℝ := 1 + 1 / Real.log x
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlog]
  have hc3 : c ≤ 3 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    have : 1/2 ≤ Real.log x := by linarith [Real.log_two_gt_d9]
    have : 1 / Real.log x ≤ 2 := (div_le_iff₀ hlog).mpr (by linarith)
    dsimp [c]; linarith
  let V (a : ℝ) : ℂ := ∫ t in -T..T, fK x ((a:ℂ)+t*I)
  let H (a b y : ℝ) : ℂ := ∫ u in a..b, fK x ((u:ℂ)+y*I)
  let r : ℂ := 1/(2*Real.pi)
  let s : ℂ := 1/(2*Real.pi*I)
  let Q : ℂ := (x:ℂ) - ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ - Real.log (2*Real.pi)
  have hbound : ∀ u : ℝ, u ≤ 3 → ∀ y ∈ ({T,-T}:Set ℝ),
      riemannZeta ((u:ℂ)+y*I) ≠ 0 := by
    intro u hu y hy
    have hz := (hline T hT hsep u hu).1
    have he : (u:ℂ)+I*T = (u:ℂ)+T*I := by ring
    rw [he] at hz
    rcases hy with rfl | rfl
    · exact hz
    · have he : (u:ℂ)+((-T:ℝ):ℂ)*I = conj ((u:ℂ)+T*I) := by apply Complex.ext <;> simp
      rw [he, riemannZeta_conj]
      exact fun hh => hz (by simpa using hh)
  have hbd : ∀z ∈ RectangleBorder ⟨-1/2,-T⟩ ⟨c,T⟩, riemannZeta z ≠ 0 := by
    intro z hz
    have hzR := rectangleBorder_subset_rectangle _ _ hz
    have hmem := (mem_rect (by linarith : -1/2 ≤ c) hT0.le).mp hzR
    rcases border_cases hz with h | h | h | h
    · have he : z = (z.re:ℂ)+(-T:ℝ)*I := by apply Complex.ext <;> simp [h]
      rw [he]; exact hbound z.re (by linarith [hmem.1.2]) (-T) (by simp)
    · have he : z = (-1/2:ℂ)+z.im*I := by apply Complex.ext <;> simp [h]
      rw [he]; simpa using zeta_left_ne z.im
    · have he : z = (z.re:ℂ)+T*I := by apply Complex.ext <;> simp [h]
      rw [he]; exact hbound z.re (by linarith [hmem.1.2]) T (by simp)
    · exact riemannZeta_ne_zero_of_one_lt_re (by linarith)
  have hcentral : RectangleIntegral' (fK x) ⟨-1/2,-T⟩ ⟨c,T⟩ = Q := by
    have hrect := perron_rect_explicit197 hx0 hc hT0 hbd
    have hset : (zeros_rect_finite c T).toFinset = hfin.toFinset := by
      ext z
      simp only [Set.Finite.mem_toFinset]
      rw [perron_zeros_rect197 hc hT0.le]
    rw [hset] at hrect
    rw [hrect]
    dsimp [Q]
    simp only [zetaMult, mul_div_assoc]
    ring
  have hr : ‖r‖ ≤ 1 := by
    norm_num [r, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simpa [mul_inv, mul_comm] using (inv_le_one₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mpr
      (show 1 ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
  have hs : ‖s‖ ≤ 1 := by
    have he : s = r / I := by dsimp [r,s]; field_simp
    rw [he, norm_div, norm_I, div_one]
    exact hr
  have hP : perronPsi x c T = r * V c := perronPsi_eq_logDeriv197 hc
  have hK : ∀ K : ℕ, 1 ≤ K →
      ‖perronPsi x c T - (Q + (TrivU x K:ℂ))‖ ≤
        ‖V (-2*(K:ℝ)-1/2)‖ + 2*B*(x*Real.log T^2/T) := by
    intro K hK
    let a : ℝ := -2*(K:ℝ)-1/2
    have ha : a ≤ 0 := by dsimp [a]; have := Nat.cast_nonneg (α:=ℝ) K; linarith
    have hi (y:ℝ) (hy:y∈({T,-T}:Set ℝ)) := (hhor x T hx hT hsep a ha y hy).1
    have hi0 (y:ℝ) (hy:y∈({T,-T}:Set ℝ)) := (hhor x T hx hT hsep (-1/2) (by norm_num) y hy).1
    have hadj (y:ℝ) (hy:y∈({T,-T}:Set ℝ)) : H a (-1/2) y + H (-1/2) c y = H a c y := by
      exact intervalIntegral.integral_add_adjacent_intervals ((hi y hy).trans (hi0 y hy).symm) (hi0 y hy)
    have hl := perron_rect_left197 hx0 hK hT0
    rw [perron_triv_sum197] at hl
    rw [perron_rect_decomp197] at hl hcentral
    change r*(V (-1/2)-V a)+s*(H a (-1/2) (-T)-H a (-1/2) T) = _ at hl
    change r*(V c-V (-1/2))+s*(H (-1/2) c (-T)-H (-1/2) c T) = Q at hcentral
    have heq : perronPsi x c T - (Q+(TrivU x K:ℂ)) =
        r*V a-s*(H a c (-T)-H a c T) := by
      rw [hP]
      linear_combination hcentral + hl - s*(hadj (-T) (by simp)) + s*(hadj T (by simp))
    rw [heq]
    calc
      _ ≤ ‖r*V a‖ + ‖s*(H a c (-T)-H a c T)‖ := norm_sub_le _ _
      _ ≤ ‖V a‖ + (‖H a c (-T)‖+‖H a c T‖) := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hr)
          ((mul_le_of_le_one_left (norm_nonneg _) hs).trans (norm_sub_le _ _))
      _ ≤ _ := by
        have h1 := (hhor x T hx hT hsep a ha (-T) (by simp)).2
        have h2 := (hhor x T hx hT hsep a ha T (by simp)).2
        change ‖H a c (-T)‖ ≤ _ at h1
        change ‖H a c T‖ ≤ _ at h2
        linarith
  have hU : Tendsto (fun K:ℕ => (TrivU x K:ℂ)) atTop (nhds (TrivInf x:ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (trivU_tendsto x hx1)
  have hleft := perron_left_edge_limit197 hx1 hT0
  have hlim1 : Tendsto (fun K:ℕ => ‖perronPsi x c T - (Q+(TrivU x K:ℂ))‖) atTop
      (nhds ‖perronPsi x c T - (Q+(TrivInf x:ℂ))‖) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.add hU)).norm
  have hlim2 : Tendsto (fun K:ℕ => ‖V (-2*(K:ℝ)-1/2)‖ + 2*B*(x*Real.log T^2/T)) atTop
      (nhds (0 + 2*B*(x*Real.log T^2/T))) := by
    simpa only [norm_zero] using hleft.norm.add_const (2*B*(x*Real.log T^2/T))
  have hfinal : ‖perronPsi x c T - (Q+(TrivInf x:ℂ))‖ ≤ 0 + 2*B*(x*Real.log T^2/T) :=
    le_of_tendsto_of_tendsto hlim1 hlim2 (Filter.eventually_atTop.2 ⟨1,hK⟩)
  simpa [c,Q,TrivInf,zpow_neg,sub_eq_add_neg, mul_assoc] using hfinal

/-- Auxiliary step in the existing Perron and contour decomposition.
Davenport chapter 17, pages 105-109. Dudek arXiv 1401.4233v1, pages 4 and 9. The result is an auxiliary consequence of the proved Perron tail and contour shift, on the full stated small range with an unspecified constant. -/
theorem explicit_formula_half_good197 : ∃ C : ℝ, ∀ (N : ℕ), 2 ≤ N → ∀ T : ℝ, 2 ≤ T →
    let x : ℝ := N + 1/2
    T ≤ x → (∀ ρ ∈ zetaZeros (T+1), 1/(100*Real.log T) ≤ |ρ.im-T|) →
    ∀ hfin : (zetaZeros T).Finite,
      ‖(Chebyshev.psi x:ℂ) - x + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ‖ ≤
        C * (x*Real.log x^2/T + Real.log x) := by
  obtain ⟨A,hA⟩ := perron_tail
  obtain ⟨B,hB⟩ := contour_shift
  let K : ℝ := |Real.log (2*Real.pi)|+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨|A|+|B|+2*K, ?_⟩
  intro N hN T hT
  dsimp only
  let x : ℝ := N+1/2
  intro hTx hsep hfin
  have hx : 2 ≤ x := by
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]; linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1/2 ≤ Real.log x := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < Real.log x := by linarith
  have hxn (n:ℕ) : (n:ℝ) ≠ x := by
    intro hn
    have hh := half_integer_distance197 N n
    change 1/2 ≤ |x-n| at hh
    rw [hn,sub_self,abs_zero] at hh
    norm_num at hh
  let c : ℝ := 1+1/Real.log x
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hL0]
  let E : ℝ := x*Real.log x^2/T + Real.log x
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hper : ‖(Chebyshev.psi x:ℂ)-perronPsi x c T‖ ≤ |A| *E := by
    have hh := (perron_psi hx hxn hc hT0).trans (hA N hN T hT)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self A) hE0)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogTx : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
  have hratio : x*Real.log T^2/T ≤ E := by
    have hh : Real.log T^2 ≤ Real.log x^2 := pow_le_pow_left₀ hlogT hlogTx 2
    have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hx0.le) hT0.le
    dsimp [E]; linarith
  let Z : ℂ := ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ
  let M : ℂ := (x:ℂ)-Z-Real.log (2*Real.pi)-(1/2:ℂ)*Real.log (1-x^(-2:ℤ))
  have hcont : ‖perronPsi x c T-M‖ ≤ |B| *E := by
    have hh := hB x T hx hT hsep hfin
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hratio (abs_nonneg B)))
  have hw : 1/2 ≤ 1-x^(-2:ℤ) := by
    have hs : 2 ≤ x^2 := by nlinarith
    have hi : (x^2)⁻¹ ≤ (2:ℝ)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hs
    simp only [zpow_neg, zpow_ofNat] at *
    norm_num at hi
    linarith
  have hw1 : 1-x^(-2:ℤ) ≤ 1 := by
    have : 0 ≤ x^(-2:ℤ) := by positivity
    linarith
  have hcorr : |Real.log (1-x^(-2:ℤ))| ≤ 1 := by
    have hlo := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1-x^(-2:ℤ))
    have hi : (1-x^(-2:ℤ))⁻¹ ≤ (1/2:ℝ)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hw
    have hhi := Real.log_nonpos (by linarith : 0 ≤ 1-x^(-2:ℤ)) hw1
    rw [abs_of_nonpos hhi]
    norm_num only [one_div, inv_inv] at hi
    linarith
  simp only [zpow_neg, zpow_ofNat] at hcorr
  have hcorrection : ‖(Real.log (2*Real.pi):ℂ)+(1/2:ℂ)*Real.log (1-x^(-2:ℤ))‖ ≤ K := by
    calc
      _ ≤ ‖(Real.log (2*Real.pi):ℂ)‖+‖(1/2:ℂ)*Real.log (1-x^(-2:ℤ))‖ := norm_add_le _ _
      _ ≤ K := by
        norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        dsimp [K]
        linarith
  have hElog : Real.log x ≤ E := by
    have : 0 ≤ x*Real.log x^2/T := by positivity
    dsimp [E]; linarith
  have hKE : K ≤ 2*K*E := by nlinarith
  have heq : (Chebyshev.psi x:ℂ)-x+Z = ((Chebyshev.psi x:ℂ)-perronPsi x c T)+
      (perronPsi x c T-M)-((Real.log (2*Real.pi):ℂ)+(1/2:ℂ)*Real.log (1-x^(-2:ℤ))) := by
    dsimp [M]; ring
  change ‖(Chebyshev.psi x:ℂ)-x+Z‖ ≤ (|A|+|B|+2*K)*E
  rw [heq]
  calc
    _ ≤ (‖(Chebyshev.psi x:ℂ)-perronPsi x c T‖+‖perronPsi x c T-M‖)+
        ‖(Real.log (2*Real.pi):ℂ)+(1/2:ℂ)*Real.log (1-x^(-2:ℤ))‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

end LeanLab.DERZ1997.Decomp1529b

namespace LeanLab.DERZ1997.Decomp1529b2
open Complex Real MeasureTheory Set Filter Topology
open LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp1529b

/-- Away from the two integers around x, comparison with its cell midpoint costs at most three halves.
Auxiliary estimate for the Perron cutoff in Davenport chapter 17 pages 105 to 109. -/
theorem distant_integer_compare266 {x : ℝ} (N n : ℕ)
    (hlo : (N : ℝ) ≤ x) (hhi : x < (N : ℝ) + 1)
    (hn : n ≠ N) (hn1 : n ≠ N + 1) :
    |(N : ℝ) + 1 / 2 - n| ≤ (3 / 2 : ℝ) * |x - n| := by
  by_cases hle : n ≤ N
  · have hh : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ (N : ℝ) + 1 / 2 - n),
      abs_of_nonneg (by linarith : 0 ≤ x - n)]
    linarith
  · have hh : (N : ℝ) + 2 ≤ n := by exact_mod_cast (show N + 2 ≤ n by omega)
    rw [abs_of_nonpos (by linarith : (N : ℝ) + 1 / 2 - n ≤ 0),
      abs_of_nonpos (by linarith : x - n ≤ 0)]
    linarith

/-- The reciprocal cutoff after removing the two nearest integers.
Auxiliary estimate for Davenport chapter 17 pages 105 to 109. -/
theorem distant_recip_sum266 {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.range (2 * ⌊x⌋₊ + 2),
      if n = ⌊x⌋₊ ∨ n = ⌊x⌋₊ + 1 then 0 else 1 / |x - n|) ≤ 12 * Real.log x := by
  classical
  let N := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hlo : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hhi : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hterm (n : ℕ) : (if n = N ∨ n = N + 1 then 0 else 1 / |x - n|) ≤
      (3 / 2 : ℝ) * (1 / |(N : ℝ) + 1 / 2 - n|) -
        (if n = N ∨ n = N + 1 then 3 else 0) := by
    by_cases hn : n = N ∨ n = N + 1
    · rw [if_pos hn, if_pos hn]
      rcases hn with rfl | rfl <;> norm_num
    · rw [if_neg hn, if_neg hn, sub_zero]
      have hm : 0 < |(N : ℝ) + 1 / 2 - n| := lt_of_lt_of_le (by norm_num)
        (half_integer_distance197 N n)
      have hh := distant_integer_compare266 N n hlo hhi
        (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))
      have hd : 0 < |x - n| := by linarith
      rw [mul_one_div]
      exact (div_le_div_iff₀ hd hm).mpr (by simpa using hh)
  have hremoved : (∑ n ∈ Finset.range (2 * N + 2),
      if n = N ∨ n = N + 1 then (3 : ℝ) else 0) = 6 := by
    rw [← Finset.sum_filter]
    have heq : (Finset.range (2 * N + 2)).filter (fun n => n = N ∨ n = N + 1) =
        ({N, N + 1} : Finset ℕ) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [heq, Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
    norm_num
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (2 * N + 2)) => hterm n)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hremoved] at hsum
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (by linarith)
      _ ≤ _ := by linarith
  have hhalf : 1 / 2 ≤ Real.log x := by linarith [Real.log_two_gt_d9]
  have hmid := half_integer_recip_sum197 N
  change (∑ n ∈ Finset.range (2 * N + 2),
    if n = N ∨ n = N + 1 then 0 else 1 / |x - n|) ≤ _
  nlinarith

/-- Perron cutoff bound at every real x at least two.
Auxiliary derivation for Davenport chapter 17 pages 105 to 109.
This bounds the coefficient sum. It does not assert Perron's formula at integers. -/
theorem perron_tail_arbitrary266 {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (x / n) ^ (1 + 1 / Real.log x) *
      min 1 (1 / (T * |Real.log (x / n)|)) ≤
        432 * (x * Real.log x ^ 2 / T) + 32 * Real.log x := by
  classical
  let N := ⌊x⌋₊
  let c : ℝ := 1 + 1 / Real.log x
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log x := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  have hc : 1 < c := by
    dsimp [c]; have := one_div_pos.mpr (show 0 < Real.log x by linarith); linarith
  have hlo : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hhi : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  let a : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * (x / n) ^ c
  let E : ℕ → ℝ := fun n => a n * min 1 (1 / (T * |Real.log (x / n)|))
  let R : ℕ → ℝ := fun n => if n ∈ Finset.range (2 * N + 2) then
    if n = N ∨ n = N + 1 then 0 else 1 / |x - n| else 0
  let K : ℕ → ℝ := fun n => if n = N ∨ n = N + 1 then 1 else 0
  let A : ℝ := 32 * x * Real.log x / T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR0 : ∀ n, 0 ≤ R n := by intro n; dsimp [R]; split_ifs <;> positivity
  have hK0 : ∀ n, 0 ≤ K n := by intro n; dsimp [K]; split_ifs <;> positivity
  have hRsupport : ∀ n ∉ Finset.range (2 * N + 2), R n = 0 := by intros; simp_all [R]
  have hKsupport : ∀ n ∉ ({N, N + 1} : Finset ℕ), K n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [K, if_neg (not_or.mpr hn)]
  have hRsum : Summable R := summable_of_ne_finset_zero hRsupport
  have hKsum : Summable K := summable_of_ne_finset_zero hKsupport
  have hRbd : ∑' n, R n ≤ 12 * Real.log x := by
    rw [tsum_eq_sum hRsupport]
    calc
      _ = ∑ n ∈ Finset.range (2 * N + 2),
          if n = N ∨ n = N + 1 then 0 else 1 / |x - n| := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [R, if_pos hn]
      _ ≤ _ := distant_recip_sum266 hx
  have hKbd : ∑' n, K n = 2 := by
    rw [tsum_eq_sum hKsupport, Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton]
    norm_num [K]
  have hcoeff : Summable a := LeanLab.DERZ1997.Perron136.perron_coeff_summable hx0 hc
  have hE : Summable E := hcoeff.of_nonneg_of_le (fun n => by dsimp [E, a]; positivity)
    (fun n => mul_le_of_le_one_right (by dsimp [a]; positivity) (min_le_left _ _))
  have hmajor : ∀ n, E n ≤ (2 / T) * a n + A * R n + 16 * Real.log x * K n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [E, a] using add_nonneg (mul_nonneg hA (hR0 0))
        (mul_nonneg (show 0 ≤ 16 * Real.log x by positivity) (hK0 0))
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hfar : (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ n
    · have hh := mul_le_mul_of_nonneg_left (perron_far_cutoff197 hx0 hn0 hT0 hfar)
        (show 0 ≤ a n by dsimp [a]; positivity)
      dsimp [E]
      nlinarith [mul_nonneg hA (hR0 n), mul_nonneg (show 0 ≤ 16 * Real.log x by positivity) (hK0 n)]
    · have hnlo : x / 2 ≤ n := by push_neg at hfar; linarith [hfar.1]
      have hnhi : (n : ℝ) ≤ 2 * x := by push_neg at hfar; linarith [hfar.2]
      have ha : a n ≤ 16 * Real.log x :=
        (mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)).trans
          (perron_near_coeff197 hx hnlo hnhi)
      by_cases hnear : n = N ∨ n = N + 1
      · have he : E n ≤ 16 * Real.log x :=
          (mul_le_of_le_one_right (by dsimp [a]; positivity) (min_le_left _ _)).trans ha
        have hKn : K n = 1 := by simp only [K, if_pos hnear]
        rw [hKn, mul_one]
        exact he.trans (le_add_of_nonneg_left (add_nonneg (by dsimp [a]; positivity) (mul_nonneg hA (hR0 n))))
      · have hmem : n ∈ Finset.range (2 * N + 2) := by
          apply Finset.mem_range.mpr
          have hh : (n : ℝ) < (2 * N + 2 : ℕ) := by push_cast; linarith
          exact_mod_cast hh
        have hd := distant_integer_compare266 N n hlo hhi
          (fun h => hnear (Or.inl h)) (fun h => hnear (Or.inr h))
        have hmid := half_integer_distance197 N n
        have hdist : 0 < |x - n| := by linarith
        have hne : x ≠ (n : ℝ) := sub_ne_zero.mp (abs_pos.mp hdist)
        have hh := mul_le_mul ha (perron_near_cutoff197 hx0 hn0 hT0 hnhi hne)
          (by positivity : 0 ≤ min 1 (1 / (T * |Real.log (x / n)|))) (by positivity)
        have heq : (16 * Real.log x) * (2 * x / (T * |x - n|)) = A * R n := by
          simp only [R, if_pos hmem, if_neg hnear, A]; ring
        dsimp [E]
        have he := hh.trans_eq heq
        nlinarith [mul_nonneg (show 0 ≤ 16 * Real.log x by positivity) (hK0 n),
          mul_nonneg (show 0 ≤ 2 / T by positivity) (show 0 ≤ a n by dsimp [a]; positivity)]
  have hsum := hE.tsum_le_tsum hmajor
    (((hcoeff.mul_left (2 / T)).add (hRsum.mul_left A)).add (hKsum.mul_left (16 * Real.log x)))
  rw [Summable.tsum_add ((hcoeff.mul_left _).add (hRsum.mul_left _)) (hKsum.mul_left _),
    Summable.tsum_add (hcoeff.mul_left _) (hRsum.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, hKbd] at hsum
  have habd : ∑' n, a n ≤ 24 * x * Real.log x ^ 2 := perron_coeff_bound197 hx
  have h1 := mul_le_mul_of_nonneg_left habd (by positivity : 0 ≤ 2 / T)
  have h2 := mul_le_mul_of_nonneg_left hRbd hA
  change ∑' n, E n ≤ _
  calc
    _ ≤ (2 / T) * (24 * x * Real.log x ^ 2) + A * (12 * Real.log x) +
        16 * Real.log x * 2 := hsum.trans (by linarith)
    _ = _ := by dsimp [A]; ring

end LeanLab.DERZ1997.Decomp1529b2

namespace LeanLab.DERZ1997.Decomp1529b
open Complex LeanLab.DERZ1997.Decomp1529a
open Real MeasureTheory Set
open Filter Topology
open scoped ComplexConjugate
open LeanLab.PNTPort.ExplicitPsi1.Trivial
open LeanLab.PNTPort.ZetaZeros
open LeanLab.PNTPort.ExplicitPsi1
open LeanLab.Routes.Decomp1551a (fK TrivU TrivInf trivU_tendsto)
open LeanLab.DERZ1997.Decomp1529b2
open LeanLab.DERZ1997.Decomp574a
open LeanLab.DERZ1997.Decomp574b

/-- Perron's character error at every noninteger x, uniformly in the modulus.
Davenport chapter 17 pages 105 to 109 and chapter 19 page 120.
This uses the existing coefficient majorant and logarithmic derivative bridge.
-/
theorem character_perron_error623 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T)
    (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) :
    ‖psiChi χ x - (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
      -(deriv (DirichletCharacter.LFunction χ)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
        DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) *
      (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
        (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I))‖ ≤
      432 * (x * Real.log x ^ 2 / T + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hc : 1 < 1 + 1 / Real.log x := by
    have := one_div_pos.mpr (Real.log_pos (by linarith : 1 < x))
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hh := (perron_character_error197 χ hx hxn hc hT0).trans
    (perron_tail_arbitrary266 hx hT)
  rw [← perron_character_tsum197 χ hx0 hc hT0,
    character_perron_logderiv574 χ x (1 + 1 / Real.log x) T hc] at hh
  exact hh.trans (by nlinarith)

/-- The nonprincipal explicit formula at noninteger x under GRH.
Davenport chapter 19 page 120, displays 13 and 14, with the inclusive cutoff.
The selected-height contour keeps the original zero sum at T.
-/
theorem character_formula_noninteger623 (hG : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x →
    (∀ n : ℕ, (n : ℝ) ≠ x) → ∀ hf : (LZeros χ T).Finite,
    ‖psiChi χ x + ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      C * (x * Real.log (q * x) ^ 2 / T + √x + Real.log (q * x) ^ 2) := by
  obtain ⟨A, hA, hcontour⟩ := character_cutoff_contour_GRH574 hG
  refine ⟨A + 864, by linarith, ?_⟩
  intro q _ χ hχ x T hx hT hTx hxn hf
  obtain ⟨U, hU, hcontour⟩ := hcontour q χ hχ x T hx hT hTx
  let P : ℂ := (1 / (2 * Real.pi) : ℂ) * (∫ t in (-U)..U,
    -(deriv (DirichletCharacter.LFunction χ)
      (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
      DirichletCharacter.LFunction χ
        (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) *
    (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
      (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I))
  let Z : ℂ := ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let L : ℝ := Real.log ((q : ℝ) * x)
  let E : ℝ := x * L ^ 2 / T + √x + L ^ 2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := hT0.trans_le hU.1
  have hLx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hL : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith)
  have hLhalf : 1 / 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  have hterm : x * Real.log x ^ 2 / U ≤ x * L ^ 2 / T := by
    apply div_le_div₀ (by positivity) ?_ hT0 hU.1
    gcongr
  have hlog : Real.log x ≤ 2 * L ^ 2 := by nlinarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hmain : 0 ≤ x * L ^ 2 / T := by positivity
  have hper : ‖psiChi χ x - P‖ ≤ 864 * E := by
    have hh := character_perron_error623 χ hx (hT.trans hU.1) hxn
    change ‖psiChi χ x - P‖ ≤ _ at hh
    exact hh.trans (by dsimp [E]; nlinarith [Real.sqrt_nonneg x])
  have hcont : ‖P + Z‖ ≤ A * E := hcontour hf
  change ‖psiChi χ x + Z‖ ≤ (A + 864) * E
  calc
    _ = ‖(psiChi χ x - P) + (P + Z)‖ := by congr 1; ring
    _ ≤ ‖psiChi χ x - P‖ + ‖P + Z‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

/-- The nonprincipal explicit formula includes integer x by a right limit.
Davenport chapter 19 page 120, displays 13 and 14, and page 125 under GRH.
The psi sum is constant on each half-open integer cell.
-/
theorem character_formula623 (hG : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x →
    ∀ hf : (LZeros χ T).Finite,
    ‖psiChi χ x + ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      C * (x * Real.log (q * x) ^ 2 / T + √x + Real.log (q * x) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := character_formula_noninteger623 hG
  refine ⟨C, hC0, ?_⟩
  intro q _ χ hχ x T hx hT hTx hf
  by_cases hnat : ∃ N : ℕ, (N : ℝ) = x
  · obtain ⟨N, rfl⟩ := hnat
    have hN0 : (0 : ℝ) < N := by linarith
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hpow (ρ : ℂ) : ContinuousAt (fun y : ℝ => (y : ℂ) ^ ρ) (N : ℝ) :=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hN0)).comp
        Complex.continuous_ofReal.continuousAt
    have hsum : ContinuousAt (fun y : ℝ => ∑ ρ ∈ hf.toFinset,
        (LMult χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) (N : ℝ) := by
      apply tendsto_finsetSum hf.toFinset
      intro ρ hρ
      exact (continuousAt_const.mul (hpow ρ)).div_const ρ
    have hleft : ContinuousAt (fun y : ℝ => ‖psiChi χ N +
        ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖) (N : ℝ) :=
      (continuousAt_const.add hsum).norm
    have hright : ContinuousAt (fun y : ℝ =>
        C * (y * Real.log ((q : ℝ) * y) ^ 2 / T + √y +
          Real.log ((q : ℝ) * y) ^ 2)) (N : ℝ) := by
      fun_prop (disch := positivity)
    apply le_of_tendsto_of_tendsto (b := 𝓝[>] (N : ℝ))
      (hleft.tendsto.mono_left inf_le_left) (hright.tendsto.mono_left inf_le_left)
    filter_upwards [Ioo_mem_nhdsGT (show (N : ℝ) < N + 1 by linarith)] with y hy
    have hy0 : (N : ℝ) < y := hy.1
    have hy1 : y < (N : ℝ) + 1 := hy.2
    have hfloor : ⌊y⌋₊ = N :=
      (Nat.floor_eq_iff (by linarith [hy.1, Nat.cast_nonneg (α := ℝ) N])).mpr ⟨hy.1.le, hy.2⟩
    have hpsi : psiChi χ y = psiChi χ N := by
      simp only [psiChi, hfloor, Nat.floor_natCast]
    have hnonint : ∀ n : ℕ, (n : ℝ) ≠ y := by
      intro n hn
      have h0 : N < n := by exact_mod_cast (show (N : ℝ) < n by simpa only [hn] using hy.1)
      have h1 : n < N + 1 := by exact_mod_cast (show (n : ℝ) < (N : ℝ) + 1 by simpa only [hn] using hy.2)
      omega
    simpa only [hpsi] using hC q χ hχ y T (by linarith) hT (by linarith) hnonint hf
  · apply hC q χ hχ x T hx hT hTx _ hf
    intro n hn
    exact hnat ⟨n, hn⟩

/-- The positive zeta window has logarithmic mass from the proved local count.
Davenport chapter 17 page 109, auxiliary height-transfer estimate.
-/
theorem zeta_window_mass593 : ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 5 ≤ T →
    ∀ hf : (zetaZerosWindow T).Finite,
      (∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℝ)) ≤ K * Real.log T := by
  classical
  obtain ⟨K, hK, hb⟩ := LeanLab.PNTPort.ZetaZeros.zero_count_two
  refine ⟨2 * K, by positivity, ?_⟩
  intro T hT hf
  obtain ⟨hg, hm⟩ := hb (T + 1 / 2) (by linarith)
  have hsub : hf.toFinset ⊆ hg.toFinset := by
    intro ρ hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hf.mem_toFinset.mp hρ
    apply hg.mem_toFinset.mpr
    refine ⟨hz, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  have hh : (∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℝ)) ≤ K * Real.log (T + 1 / 2) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ρ _ _ => Nat.cast_nonneg (zetaMult ρ)))
    exact hm
  have hlog : Real.log (T + 1 / 2) ≤ 2 * Real.log T := by
    have hl := Real.log_le_log (by linarith : 0 < T + 1 / 2)
      (show T + 1 / 2 ≤ T ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  exact hh.trans (by nlinarith)

/-- A fixed-left-edge zeta contour gives the square-root error budget.
Davenport chapter 17 pages 108 and 109, auxiliary selected-height formula.
This uses an unspecified absolute constant and does not assert coefficient 1000.
-/
theorem zeta_selected_contour593 : ∃ B : ℝ, 0 < B ∧ ∀ x T : ℝ,
    5 ≤ T → T ≤ x → ∃ U ∈ Set.Icc T (T + 1),
      ∀ hf : (zetaZeros U).Finite,
      ‖perronPsi x (1 + 1 / Real.log x) U -
        ((x : ℂ) - ∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
        B * (x * Real.log x ^ 2 / T + √x + Real.log x ^ 2) := by
  obtain ⟨C, hC, hg⟩ := good_height_pm
  obtain ⟨A, hA, hl⟩ := LeanLab.DERZ1997.ZetaLeft623.zeta_left_integral623
  let D : ℝ := |Real.log (2 * Real.pi)|
  refine ⟨A + 18 * C + D + 1, by dsimp [D]; positivity, ?_⟩
  intro x T hT hTx
  have hx : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlogx : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    linarith [Real.exp_one_lt_three]
  let c : ℝ := 1 + 1 / Real.log x
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr (by linarith : 0 < Real.log x)]
  have hc2 : c ≤ 2 := by
    have hi : 1 / Real.log x ≤ 1 := (div_le_one (by linarith : 0 < Real.log x)).mpr hlogx
    dsimp [c]; linarith
  have hpow : x ^ c ≤ 3 * x := by
    have heq : x ^ c = x * Real.exp 1 := by
      dsimp [c]
      rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
      congr 1
      rw [mul_one_div_cancel (by linarith : Real.log x ≠ 0)]
    rw [heq]
    nlinarith [Real.exp_one_lt_three]
  obtain ⟨U, hU, hgood⟩ := hg T hT
  refine ⟨U, hU, ?_⟩
  intro hf
  have hU0 : 0 < U := hT0.trans_le hU.1
  let V : ℝ → ℂ := fun a => ∫ t in (-U)..U, fK x ((a : ℂ) + t * I)
  let H : ℝ → ℂ := fun y => ∫ σ in (-1 / 2 : ℝ)..c, fK x ((σ : ℂ) + y * I)
  let M : ℝ := x * Real.log x ^ 2 / T
  let E : ℝ := M + √x + Real.log x ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsx : 1 ≤ √x := by rw [Real.one_le_sqrt]; linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogTx : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
  have hhorizontal (y : ℝ) (hy : y ∈ ({U, -U} : Set ℝ)) : ‖H y‖ ≤ 9 * C * M := by
    have hyU : |y| = U := by rcases hy with rfl | rfl <;> simp [abs_of_pos hU0]
    have hpoint (σ : ℝ) (hσ : σ ∈ Set.uIcc (-1 / 2 : ℝ) c) :
        ‖fK x ((σ : ℂ) + y * I)‖ ≤ 3 * C * x * Real.log T ^ 2 / T := by
      rw [Set.uIcc_of_le (by linarith : (-1 / 2 : ℝ) ≤ c)] at hσ
      have hσ2 : σ ∈ Set.Icc (-1 / 2 : ℝ) 2 := ⟨hσ.1, hσ.2.trans hc2⟩
      have hb := (hgood σ hσ2 y hy).2
      have hn : T ≤ ‖(σ : ℂ) + y * I‖ := by
        have hh := Complex.abs_im_le_norm ((σ : ℂ) + y * I)
        have hh' : |y| ≤ ‖(σ : ℂ) + y * I‖ := by simpa using hh
        rw [hyU] at hh'
        exact hU.1.trans hh'
      have hp : x ^ σ ≤ 3 * x :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσ.2).trans hpow
      change ‖-(deriv riemannZeta ((σ : ℂ) + y * I) /
        riemannZeta ((σ : ℂ) + y * I)) * (x : ℂ) ^ ((σ : ℂ) + y * I) /
          ((σ : ℂ) + y * I)‖ ≤ _
      rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
      apply (div_le_div₀ (by positivity : 0 ≤ C * Real.log T ^ 2 * (3 * x))
        (mul_le_mul hb hp (Real.rpow_nonneg hx0.le _) (by positivity)) hT0 hn).trans
      exact le_of_eq (by ring)
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun σ hσ => hpoint σ (Set.uIoc_subset_uIcc hσ))
    have hlen : |c - -1 / 2| ≤ 3 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hmain : x * Real.log T ^ 2 / T ≤ M := by
      dsimp [M]
      gcongr
    change ‖∫ σ in (-1 / 2 : ℝ)..c, fK x ((σ : ℂ) + y * I)‖ ≤ _
    calc
      _ ≤ |c - -1 / 2| * (3 * C * x * Real.log T ^ 2 / T) := by simpa [mul_comm] using hh
      _ ≤ 3 * (3 * C * x * Real.log T ^ 2 / T) := by gcongr
      _ = (9 * C) * (x * Real.log T ^ 2 / T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)
  have hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -U⟩ : ℂ) ⟨c, U⟩,
      riemannZeta z ≠ 0 := by
    intro z hz
    have hzR := (mem_rect (by linarith : (-1 / 2 : ℝ) ≤ c) hU0.le).mp
      (rectangleBorder_subset_rectangle _ _ hz)
    rcases border_cases hz with h | h | h | h
    · have he : z = (z.re : ℂ) + (-U : ℝ) * I := by apply Complex.ext <;> simp [h]
      rw [he]
      exact (hgood z.re ⟨hzR.1.1, hzR.1.2.trans hc2⟩ (-U) (by simp)).1
    · have he : z = (-1 / 2 : ℂ) + z.im * I := by apply Complex.ext <;> simp [h]
      rw [he]
      simpa using LeanLab.PNTPort.ZetaZeros.zeta_left_ne z.im
    · have he : z = (z.re : ℂ) + U * I := by apply Complex.ext <;> simp [h]
      rw [he]
      exact (hgood z.re ⟨hzR.1.1, hzR.1.2.trans hc2⟩ U (by simp)).1
    · exact riemannZeta_ne_zero_of_one_lt_re (by linarith)
  let Z : ℂ := ∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  have hcentral : RectangleIntegral' (fK x) ⟨-1 / 2, -U⟩ ⟨c, U⟩ =
      x - Real.log (2 * Real.pi) - Z := by
    have hh := perron_rect_explicit197 hx0 hc hU0 hbd
    have hset : (zeros_rect_finite c U).toFinset = hf.toFinset := by
      ext ρ
      simp only [Set.Finite.mem_toFinset]
      rw [perron_zeros_rect197 hc hU0.le]
    rw [hset] at hh
    simpa only [Z, zetaMult, mul_div_assoc] using hh
  let r : ℂ := 1 / (2 * Real.pi)
  let v : ℂ := 1 / (2 * Real.pi * I)
  have hr : ‖r‖ ≤ 1 := by
    norm_num [r, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simpa [mul_inv, mul_comm] using (inv_le_one₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (show 1 ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
  have hv : ‖v‖ ≤ 1 := by
    have he : v = r / I := by dsimp [r, v]; field_simp
    rw [he, norm_div, norm_I, div_one]
    exact hr
  have hP : perronPsi x c U = r * V c := perronPsi_eq_logDeriv197 hc
  rw [perron_rect_decomp197] at hcentral
  change r * (V c - V (-1 / 2)) + v * (H (-U) - H U) = _ at hcentral
  have he : perronPsi x c U - ((x : ℂ) - Z) =
      r * V (-1 / 2) - v * (H (-U) - H U) - Real.log (2 * Real.pi) := by
    rw [hP]
    linear_combination hcentral
  have hleft : ‖V (-1 / 2)‖ ≤ A * √x := by
    simpa [V] using hl x U hx hU0.le (by linarith [hU.2])
  have hh0 := hhorizontal (-U) (by simp)
  have hh1 := hhorizontal U (by simp)
  change ‖perronPsi x c U - ((x : ℂ) - Z)‖ ≤ (A + 18 * C + D + 1) * E
  rw [he]
  have htri : ‖r * V (-1 / 2) - v * (H (-U) - H U) - Real.log (2 * Real.pi)‖ ≤
      ‖V (-1 / 2)‖ + (‖H (-U)‖ + ‖H U‖) + D := by
    apply (norm_sub_le _ _).trans
    apply add_le_add
    · apply (norm_sub_le _ _).trans
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hr)
        ((mul_le_of_le_one_left (norm_nonneg _) hv).trans (norm_sub_le _ _))
    · simp only [D, Complex.norm_real, Real.norm_eq_abs]
      exact le_rfl
  have hDE : D ≤ D * E := by
    have hD : 0 ≤ D := abs_nonneg _
    have hE : 1 ≤ E := by dsimp [E]; nlinarith [sq_nonneg (Real.log x)]
    exact le_mul_of_one_le_right hD hE
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hAE : A * √x ≤ A * E := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    dsimp [E]
    nlinarith [sq_nonneg (Real.log x)]
  have hCE : 18 * C * M ≤ 18 * C * E := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp [E]; nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.log x)]
  nlinarith

/-- The zeta formula at noninteger x with the square-root error allowance.
Davenport chapter 17 pages 108 to 110, auxiliary formula for the principal branch.
All constants are unspecified and independent of x and the cutoff.
-/
theorem zeta_formula_noninteger593 : ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ,
    2 ≤ x → 2 ≤ T → T ≤ x → (∀ n : ℕ, (n : ℝ) ≠ x) →
    ∀ hf : (zetaZeros T).Finite,
      ‖(Chebyshev.psi x : ℂ) - x + ∑ ρ ∈ hf.toFinset,
        (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        C * (x * Real.log x ^ 2 / T + √x + Real.log x ^ 2) := by
  classical
  obtain ⟨A, hA, hcontour⟩ := zeta_selected_contour593
  obtain ⟨B, hB, hmass⟩ := zeta_window_mass593
  let F := (zetaZeros_finite 5).toFinset
  let D : ℝ := ∑ ρ ∈ F, (zetaMult ρ : ℝ) / ‖ρ‖
  have hD : 0 ≤ D := Finset.sum_nonneg (fun ρ _ => by positivity)
  let K : ℝ := 20 * (Real.log 4 + 5 + D)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A + 864 + 4 * B + K, by positivity, ?_⟩
  intro x T hx hT hTx hxn hf
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  let M : ℝ := x * Real.log x ^ 2 / T
  let E : ℝ := M + √x + Real.log x ^ 2
  let Z : ℝ → ℂ := fun U => ∑ ρ ∈ (zetaZeros_finite U).toFinset,
    (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlog : 1 / 2 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  have hzero : (∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ) = Z T := by
    congr 1
  change ‖(Chebyshev.psi x : ℂ) - x + Z T‖ ≤ (A + 864 + 4 * B + K) * E
  by_cases hT5 : 5 ≤ T
  · obtain ⟨U, hU, hco⟩ := hcontour x T hT5 hTx
    let hfU := zetaZeros_finite U
    let c : ℝ := 1 + 1 / Real.log x
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hlogTx : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
    have hlogbound : Real.log T ≤ 2 * Real.log x ^ 2 := by nlinarith
    have hper : ‖(Chebyshev.psi x : ℂ) - perronPsi x c U‖ ≤ 864 * E := by
      have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr (by linarith : 0 < Real.log x)]
      have hp' := (perron_psi hx hxn hc (show 0 < U by linarith [hU.1])).trans
        (perron_tail_arbitrary266 hx (hT.trans hU.1))
      have hratio : x * Real.log x ^ 2 / U ≤ M :=
        div_le_div_of_nonneg_left (by positivity) hT0 hU.1
      have hl : Real.log x ≤ 2 * Real.log x ^ 2 := by nlinarith
      change ‖(Chebyshev.psi x : ℂ) - perronPsi x c U‖ ≤ _ at hp'
      exact hp'.trans (by dsimp [E]; nlinarith [Real.sqrt_nonneg x])
    have hfW : (zetaZerosWindow T).Finite := by
      apply (zetaZeros_finite (T + 1)).subset
      intro ρ hρ
      obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hρ
      exact ⟨hz, hr0, hr1, by rw [abs_of_pos (by linarith : 0 < ρ.im)]; exact hhi⟩
    have hwindow := hmass T hT5 hfW
    have htransfer := zeta_height_transfer266 (by linarith : 1 ≤ x) hT0 hU.1 hU.2
      (zetaZeros_finite T) hfU hfW hwindow
    have hdiff : ‖Z U - Z T‖ ≤ (4 * B) * M := by
      apply htransfer.trans
      have hh := mul_le_mul_of_nonneg_left hlogbound (show 0 ≤ 2 * B * x by positivity)
      have hd := div_le_div_of_nonneg_right hh hT0.le
      dsimp [M]
      convert hd using 1 <;> ring
    have hco' : ‖perronPsi x c U - ((x : ℂ) - Z U)‖ ≤ A * E := hco hfU
    have htri : ‖(Chebyshev.psi x : ℂ) - x + Z T‖ ≤
        ‖(Chebyshev.psi x : ℂ) - perronPsi x c U‖ +
        ‖perronPsi x c U - ((x : ℂ) - Z U)‖ + ‖Z U - Z T‖ := by
      have he : (Chebyshev.psi x : ℂ) - x + Z T =
          ((Chebyshev.psi x : ℂ) - perronPsi x c U) +
          (perronPsi x c U - ((x : ℂ) - Z U)) - (Z U - Z T) := by ring
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hME : M ≤ E := by dsimp [E]; nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.log x)]
    have hd := mul_le_mul_of_nonneg_left hME (show 0 ≤ 4 * B by positivity)
    nlinarith [mul_nonneg hK.le hE]
  · have hTsmall : T ≤ 5 := (lt_of_not_ge hT5).le
    have hsub : (zetaZeros_finite T).toFinset ⊆ F := by
      intro ρ hρ
      obtain ⟨hz, hr0, hr1, hi⟩ := (zetaZeros_finite T).mem_toFinset.mp hρ
      exact (zetaZeros_finite 5).mem_toFinset.mpr ⟨hz, hr0, hr1, hi.trans hTsmall⟩
    have hsum : ‖Z T‖ ≤ D * x := by
      calc
        _ ≤ ∑ ρ ∈ (zetaZeros_finite T).toFinset,
          ‖(zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ (zetaZeros_finite T).toFinset, ((zetaMult ρ : ℝ) / ‖ρ‖) * x := by
          apply Finset.sum_le_sum
          intro ρ hρ
          have hr := ((zetaZeros_finite T).mem_toFinset.mp hρ).2.2.1.le
          rw [norm_div, norm_mul, Complex.norm_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hp := Real.rpow_le_self_of_one_le (by linarith : 1 ≤ x) hr
          have hh := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (zetaMult ρ))) (norm_nonneg ρ)
          exact hh.trans_eq (by ring)
        _ = (∑ ρ ∈ (zetaZeros_finite T).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) * x := by
          rw [Finset.sum_mul]
        _ ≤ D * x := mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => by positivity)) hx0.le
    have hpsi : ‖(Chebyshev.psi x : ℂ)‖ ≤ (Real.log 4 + 4) * x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg x)]
      exact Chebyshev.psi_le_const_mul_self hx0.le
    have hxM : x ≤ 20 * M := by
      have hsq : (1 / 4 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
      have hd : x / 4 ≤ x * Real.log x ^ 2 := by nlinarith
      have hMt : M * T = x * Real.log x ^ 2 := by dsimp [M]; field_simp
      have hm5 := mul_le_mul_of_nonneg_left hTsmall hM
      nlinarith
    have htri : ‖(Chebyshev.psi x : ℂ) - x + Z T‖ ≤ (Real.log 4 + 5 + D) * x := by
      have hh := (norm_add_le ((Chebyshev.psi x : ℂ) - x) (Z T)).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
      have hnx : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      rw [hnx] at hh
      nlinarith
    have hcoef : 0 ≤ Real.log 4 + 5 + D := by positivity
    have hbudget : (Real.log 4 + 5 + D) * x ≤ K * M := by
      have hh := mul_le_mul_of_nonneg_left hxM hcoef
      dsimp [K]
      nlinarith
    have hME : M ≤ E := by dsimp [E]; nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.log x)]
    exact htri.trans (hbudget.trans ((mul_le_mul_of_nonneg_left hME hK.le).trans (by
      nlinarith [mul_nonneg (show 0 ≤ A + 864 + 4 * B by positivity) hE])))

/-- The weaker zeta formula extends to integers by a right limit.
Davenport chapter 17 pages 109 and 110, auxiliary principal-character input.
The square-root error allowance is retained and no numerical coefficient is asserted.
-/
theorem zeta_formula593 : ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    T ≤ x →
    ∀ hfin : (zetaZeros T).Finite,
      ‖(Chebyshev.psi x:ℂ) - x + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ‖ ≤
        C * (x*Real.log x^2/T + √x + Real.log x^2) := by
  obtain ⟨C, hC0, hC⟩ := zeta_formula_noninteger593
  refine ⟨C, hC0, ?_⟩
  intro x T hx hT hTx hfin
  by_cases hnat : ∃ N : ℕ, (N : ℝ) = x
  · obtain ⟨N, rfl⟩ := hnat
    have hN : 2 ≤ N := by exact_mod_cast hx
    have hlocal : ∀ y : ℝ, (N : ℝ) < y → y < (N : ℝ) + 1 →
        ‖(Chebyshev.psi y : ℂ) - y + ∑ ρ ∈ hfin.toFinset,
          (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ C * (y * Real.log y ^ 2 / T + √y + Real.log y ^ 2) := by
      intro y hy hy1
      apply hC y T (by linarith) hT (by linarith) _ hfin
      intro n hn
      have h0 : N < n := by exact_mod_cast (show (N : ℝ) < n by simpa only [hn] using hy)
      have h1 : n < N + 1 := by exact_mod_cast (show (n : ℝ) < (N : ℝ) + 1 by simpa only [hn] using hy1)
      omega
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hpow (ρ : ℂ) : ContinuousAt (fun y : ℝ => (y : ℂ) ^ ρ) (N : ℝ) :=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hN0)).comp
        Complex.continuous_ofReal.continuousAt
    have hsum : ContinuousAt (fun y : ℝ => ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ) (N : ℝ) := by
      apply tendsto_finsetSum hfin.toFinset
      intro ρ hρ
      exact (continuousAt_const.mul (hpow ρ)).div_const ρ
    have hleft : ContinuousAt (fun y : ℝ =>
        ‖(Chebyshev.psi N : ℂ) - y + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖) (N : ℝ) :=
      ((continuousAt_const.sub Complex.continuous_ofReal.continuousAt).add hsum).norm
    have hright : ContinuousAt (fun y : ℝ => C * (y * Real.log y ^ 2 / T + √y + Real.log y ^ 2)) (N : ℝ) := by
      fun_prop (disch := exact hN0.ne')
    apply le_of_tendsto_of_tendsto (b := 𝓝[>] (N : ℝ)) (hleft.tendsto.mono_left inf_le_left)
      (hright.tendsto.mono_left inf_le_left)
    filter_upwards [Ioo_mem_nhdsGT (show (N : ℝ) < N + 1 by linarith)] with y hy
    have hfloor : ⌊y⌋₊ = N := (Nat.floor_eq_iff (by linarith [hy.1, Nat.cast_nonneg (α := ℝ) N])).mpr ⟨hy.1.le, hy.2⟩
    have hpsi : Chebyshev.psi y = Chebyshev.psi N := by
      rw [Chebyshev.psi_eq_psi_coe_floor, hfloor]
    simpa only [hpsi] using hlocal y hy.1 hy.2
  · apply hC x T hx hT hTx _ hfin
    intro n hn
    exact hnat ⟨n, hn⟩

/-- Principal characters satisfy the U-1667 error scale with an absolute constant.
Davenport chapter 20 page 121 and chapter 17 pages 109 and 110.
The proved weaker zeta formula and the finite Euler factors suffice.
-/
theorem principal_formula593 : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (x T : ℝ), 2 ≤ x → 2 ≤ T → T ≤ x →
      ∀ hf : (LZeros (1 : DirichletCharacter ℂ q) T).Finite,
        ‖psiChi (1 : DirichletCharacter ℂ q) x - x +
          ∑ ρ ∈ hf.toFinset, (LMult (1 : DirichletCharacter ℂ q) ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
          C * (x * Real.log ((q : ℝ) * x) ^ 2 / T + √x + Real.log ((q : ℝ) * x) ^ 2) := by
  obtain ⟨A, hA, hz⟩ := zeta_formula593
  refine ⟨A + 2, by positivity, ?_⟩
  intro q _ x T hx hT hTx hf
  let L : ℝ := Real.log ((q : ℝ) * x)
  let E : ℝ := x * L ^ 2 / T + √x + L ^ 2
  have hx0 : 0 < x := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hlogx : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith)
  have hlogq : Real.log q ≤ L := Real.log_le_log hq0 (by nlinarith)
  have hEuler : Real.log q / Real.log 2 * Real.log x ≤ 2 * L ^ 2 := by
    have hinv : 1 / Real.log 2 ≤ (2 : ℝ) :=
      (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
        (by linarith [Real.log_two_gt_d9])
    have hm : Real.log q * Real.log x ≤ L ^ 2 := by
      simpa only [pow_two] using mul_le_mul hlogq hlogx hlogx0 hL0
    calc
      _ = (Real.log q * Real.log x) * (1 / Real.log 2) := by ring
      _ ≤ L ^ 2 * (1 / Real.log 2) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ ≤ L ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg L)
      _ = _ := by ring
  have hpsi : ‖psiChi (1 : DirichletCharacter ℂ q) x - (Chebyshev.psi x : ℂ)‖ ≤
      2 * L ^ 2 := (principal_psi_error574 (q := q) (by linarith : 1 ≤ x)).trans hEuler
  let Z : ℂ := ∑ ρ ∈ (zetaZeros_finite T).toFinset,
    (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  have hzeta : ‖(Chebyshev.psi x : ℂ) - x + Z‖ ≤ A * E := by
    apply (hz x T hx hT hTx (zetaZeros_finite T)).trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    dsimp [E]
    gcongr
  rw [principal_zero_sum574 x T hf (zetaZeros_finite T)]
  have htri : ‖psiChi (1 : DirichletCharacter ℂ q) x - x + Z‖ ≤
      ‖psiChi (1 : DirichletCharacter ℂ q) x - (Chebyshev.psi x : ℂ)‖ +
      ‖(Chebyshev.psi x : ℂ) - x + Z‖ := by
    have he : psiChi (1 : DirichletCharacter ℂ q) x - x + Z =
        (psiChi (1 : DirichletCharacter ℂ q) x - (Chebyshev.psi x : ℂ)) +
          ((Chebyshev.psi x : ℂ) - x + Z) := by ring
    rw [he]
    exact norm_add_le _ _
  have hE : L ^ 2 ≤ E := by
    have hm : 0 ≤ x * L ^ 2 / T := by positivity
    dsimp [E]
    linarith [Real.sqrt_nonneg x]
  change ‖psiChi (1 : DirichletCharacter ℂ q) x - x + Z‖ ≤ (A + 2) * E
  nlinarith

/-- CONDITIONAL ON the displayed zeta estimate with constant 1000.
The nonprincipal character formula is proved independently of that input.
Davenport chapter 19 pages 119 and 120 and chapter 20 page 125.
-/
theorem character_formula_of_zeta623 (hG : GRH)
    (hZ : ∀ (x T : ℝ), 2 ≤ x → 2 ≤ T → T ≤ x →
      ∀ hf : (zetaZeros T).Finite,
      ‖(Chebyshev.psi x : ℂ) - x + ∑ ρ ∈ hf.toFinset,
        (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        1000 * (x * Real.log x ^ 2 / T + Real.log x)) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x T : ℝ),
      2 ≤ x → 2 ≤ T → T ≤ x → ∀ hf : (LZeros χ T).Finite,
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
        ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        C * (x * Real.log (q * x) ^ 2 / T + √x + Real.log (q * x) ^ 2) := by
  obtain ⟨A, hA, hnon⟩ := character_formula623 hG
  refine ⟨A + 2002, ?_⟩
  intro q _ χ x T hx hT hTx hf
  have hE : 0 ≤ x * Real.log ((q : ℝ) * x) ^ 2 / T + √x +
      Real.log ((q : ℝ) * x) ^ 2 := by positivity
  by_cases hχ : χ = 1
  · subst χ
    have hh := principal_error_of_zeta574 (q := q) hx hT hf (zetaZeros_finite T)
      (hZ x T hx hT hTx (zetaZeros_finite T))
    change ‖psiChi (1 : DirichletCharacter ℂ q) x - x +
      ∑ ρ ∈ hf.toFinset, (LMult (1 : DirichletCharacter ℂ q) ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤ _ at hh
    simp only [↓reduceIte]
    exact hh.trans (by nlinarith)
  · simp only [ite_eq_right hχ, sub_zero]
    exact (hnon q χ hχ x T hx hT hTx hf).trans (by nlinarith)

/-- LEAF. CONDITIONAL ON explicit_formula_zeta for principal characters.
Truncated explicit formula for `ψ(x, χ)` under GRH: there is an absolute `C` such
that for every modulus `q`, every character `χ` mod `q`, `x ≥ 2`, `2 ≤ T ≤ x`,
`|ψ(x, χ) - δ_χ x + ∑_{|γ| ≤ T} m_ρ x^ρ/ρ| ≤ C (x log²(qx)/T + √x + log²(qx))`,
`δ_χ = 1` for the trivial character. GRH gives `|ρ| ≥ 1/2`, so the zeros with `|γ| < 1` and
the constant `b(χ)` cost `O(log q)`; an imprimitive `χ` differs from its primitive inducing
character by at most `log q log x`. Davenport ch. 19, (13)-(14), p. 120, and ch. 20, p. 125.
Unit U-1529. -/
theorem explicit_formula_chi_GRH : GRH → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x T : ℝ), 2 ≤ x → 2 ≤ T → T ≤ x →
    ∀ hfin : (LZeros χ T).Finite,
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        C * (x * Real.log (q * x) ^ 2 / T + √x + Real.log (q * x) ^ 2) := by
  intro hG
  obtain ⟨A, hA, hnon⟩ := character_formula623 hG
  obtain ⟨B, hB, hprincipal⟩ := principal_formula593
  refine ⟨A + B, ?_⟩
  intro q _ χ x T hx hT hTx hf
  have hE : 0 ≤ x * Real.log ((q : ℝ) * x) ^ 2 / T + √x +
      Real.log ((q : ℝ) * x) ^ 2 := by positivity
  by_cases hχ : χ = 1
  · subst χ
    simp only [↓reduceIte]
    exact (hprincipal q x T hx hT hTx hf).trans (by nlinarith)
  · simp only [ite_eq_right hχ, sub_zero]
    exact (hnon q χ hχ x T hx hT hTx hf).trans (by nlinarith)

/-! ### Assembly: the GRH bound for `ψ(x, χ)` -/

/-- Under the line hypothesis, each term of the sum over zeros has norm `m √x / |ρ|`. -/
theorem norm_zero_term {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ ρ / ρ‖ = √x * ((m : ℝ) / ‖ρ‖) := by
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ,
    ← Real.sqrt_eq_rpow]
  ring

/-- The sum over zeros of `L(s, χ)` up to height `T`, on the critical line, is at most
`√x ∑ m_ρ/|ρ|`. -/
theorem norm_zero_sum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x T : ℝ}
    (hx : 0 < x) (hfin : (LZeros χ T).Finite) (hline : ∀ ρ ∈ LZeros χ T, ρ.re = 1 / 2) :
    ‖∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      √x * ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun ρ hρ => ?_)
  exact norm_zero_term hx (hline ρ ((Set.Finite.mem_toFinset hfin).mp hρ)) _

/-- Multiplicity in a closed unit band is logarithmic, including the band at zero.
Davenport chapter 19 pages 117 to 120, auxiliary local-count estimate.
Both signs are bounded by the existing local Jensen mass.
-/
theorem character_unit_mass593 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (T U : ℝ) (S : Finset ℂ), 0 ≤ T → U ≤ T + 1 →
        (∀ ρ ∈ S, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          T ≤ |ρ.im| ∧ |ρ.im| ≤ U) →
        (∑ ρ ∈ S, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
          C * Real.log ((q : ℝ) * (T + 4)) := by
  classical
  obtain ⟨K, hK, hmass⟩ := character_local_mass574
  refine ⟨2 * K, by positivity, ?_⟩
  intro q _ χ hχ T U S hT hU hS
  let t : ℝ := T + 1 / 2
  let P := S.filter (fun ρ => 0 ≤ ρ.im)
  let N := S.filter (fun ρ => ¬ 0 ≤ ρ.im)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hlog : Real.log ((q : ℝ) * (|t| + 3)) ≤ Real.log ((q : ℝ) * (T + 4)) := by
    apply Real.log_le_log (by positivity)
    rw [abs_of_nonneg ht]
    dsimp [t]
    nlinarith
  have hpos : (∑ ρ ∈ P, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
      K * Real.log ((q : ℝ) * (T + 4)) := by
    apply (hmass q χ hχ t P ?_).trans (mul_le_mul_of_nonneg_left hlog hK.le)
    intro ρ hρ
    obtain ⟨hρS, hi⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hS ρ hρS
    refine ⟨hz, hG q χ ρ hz hr0 hr1, ?_⟩
    rw [abs_of_nonneg hi] at hlo hhi
    rw [abs_le]
    dsimp [t]
    constructor <;> linarith
  have hneg : (∑ ρ ∈ N, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
      K * Real.log ((q : ℝ) * (T + 4)) := by
    apply (hmass q χ hχ (-t) N ?_).trans
      (mul_le_mul_of_nonneg_left (by simpa only [abs_neg] using hlog) hK.le)
    intro ρ hρ
    obtain ⟨hρS, hi⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hS ρ hρS
    refine ⟨hz, hG q χ ρ hz hr0 hr1, ?_⟩
    rw [abs_of_neg (lt_of_not_ge hi)] at hlo hhi
    rw [abs_le]
    dsimp [t]
    constructor <;> linarith
  have he := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ => 0 ≤ ρ.im)
    (fun ρ => (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ))
  change (∑ ρ ∈ P, _) + (∑ ρ ∈ N, _) = _ at he
  linarith

/-- Under GRH, low nonprincipal zeros have reciprocal mass of order log q.
Davenport chapter 19 page 118, display 9, and chapter 20 page 125.
The closed cutoff at one also bounds the strict source cutoff.
-/
theorem character_low_reciprocal593 (hG : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ hf : (LZeros χ 1).Finite,
        (∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤ C * Real.log q := by
  classical
  obtain ⟨K, hK, hmass⟩ := character_unit_mass593 hG
  refine ⟨6 * K, by positivity, ?_⟩
  intro q _ χ hχ hf
  have hq1 : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hq2 : 2 ≤ q := by have := NeZero.pos q; omega
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < q := by linarith
  have hm := hmass q χ hχ 0 1 hf.toFinset (by norm_num) (by norm_num) (by
    intro ρ hρ
    obtain ⟨hz, hr0, hr1, hi⟩ := hf.mem_toFinset.mp hρ
    exact ⟨hz, hr0, hr1, abs_nonneg _, hi⟩)
  simp only [zero_add] at hm
  have hsum : (∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤
      2 * ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hr := L_re_eq_half_of_GRH hG χ ρ (hf.mem_toFinset.mp hρ)
    have hn : (1 / 2 : ℝ) ≤ ‖ρ‖ := by
      have hh := Complex.abs_re_le_norm ρ
      rw [hr] at hh
      norm_num at hh ⊢
      exact hh
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (LMult χ ρ))
      (by norm_num : (0 : ℝ) < 1 / 2) hn
    nlinarith
  have hlog : Real.log ((q : ℝ) * 4) ≤ 3 * Real.log q := by
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq
    rw [Real.log_mul hq0.ne' (by norm_num : (4 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  nlinarith

/-- A coarse global nonprincipal count follows from unit bands under GRH.
Davenport chapter 19 pages 117 and 118, auxiliary count for partial summation.
The absolute constant comes from the proved local Jensen bound.
-/
theorem character_count_GRH593 (hG : GRH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ T : ℝ, 1 ≤ T → ∀ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ LZeros χ T) →
        (∑ ρ ∈ S, (LMult χ ρ : ℝ)) ≤
          K * T * Real.log ((q : ℝ) * (T + 4)) := by
  classical
  obtain ⟨K, hK, hmass⟩ := character_unit_mass593 hG
  refine ⟨2 * K, by positivity, ?_⟩
  intro q _ χ hχ T hT S hS
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hT0 : 0 ≤ T := by linarith
  let b : ℂ → ℕ := fun ρ => ⌊|ρ.im|⌋₊
  let N : ℕ := ⌊T⌋₊ + 1
  have hmaps : ∀ ρ ∈ S, b ρ ∈ Finset.range N := by
    intro ρ hρ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hS ρ hρ).2.2.2))
  have hb (n : ℕ) (hn : n ∈ Finset.range N) :
      (∑ ρ ∈ S.filter (fun ρ => b ρ = n), (LMult χ ρ : ℝ)) ≤
        K * Real.log ((q : ℝ) * (T + 4)) := by
    have hnT : (n : ℝ) ≤ T := by
      have hn' : n ≤ ⌊T⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      exact (Nat.cast_le.mpr hn').trans (Nat.floor_le hT0)
    have hh := hmass q χ hχ n (n + 1) (S.filter (fun ρ => b ρ = n))
      (Nat.cast_nonneg n) le_rfl (by
        intro ρ hρ
        obtain ⟨hρ, he⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hz, hr0, hr1, hi⟩ := hS ρ hρ
        have he' : ⌊|ρ.im|⌋₊ = n := he
        have hlo := Nat.floor_le (abs_nonneg ρ.im)
        have hhi := Nat.lt_floor_add_one |ρ.im|
        rw [he'] at hlo hhi
        exact ⟨hz, hr0, hr1, hlo, hhi.le⟩)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.log_le_log (by positivity)
    nlinarith
  have hN : (N : ℝ) ≤ 2 * T := by
    have hh := Nat.floor_le hT0
    dsimp [N]
    push_cast
    linarith
  have hlog : 0 ≤ Real.log ((q : ℝ) * (T + 4)) :=
    Real.log_nonneg (by nlinarith)
  calc
    _ = ∑ n ∈ Finset.range N,
        ∑ ρ ∈ S.filter (fun ρ => b ρ = n), (LMult χ ρ : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ Finset.range N, K * Real.log ((q : ℝ) * (T + 4)) :=
      Finset.sum_le_sum hb
    _ = (N : ℝ) * (K * Real.log ((q : ℝ) * (T + 4))) := by simp
    _ ≤ (2 * T) * (K * Real.log ((q : ℝ) * (T + 4))) :=
      mul_le_mul_of_nonneg_right hN (mul_nonneg hK.le hlog)
    _ = _ := by ring

/-- Reciprocal zero mass for nonprincipal characters under GRH, from local Jensen.
Davenport chapter 19 pages 117 and 118 and chapter 20 page 125.
Finite partial summation avoids the cited explicit global zero count.
-/
theorem character_reciprocal_GRH593 (hG : GRH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ hf : (LZeros χ T).Finite,
        (∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤
          K * Real.log ((q : ℝ) * T) ^ 2 := by
  classical
  obtain ⟨K, hK, hcount⟩ := character_count_GRH593 hG
  refine ⟨20 * K, by positivity, ?_⟩
  intro q _ χ hχ T hT hf
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  let S := hf.toFinset
  let w : ℂ → ℝ := fun ρ => LMult χ ρ
  let u : ℂ → ℝ := fun ρ => max 1 |ρ.im|
  let L := Real.log ((q : ℝ) * (T + 4))
  let M := Real.log ((q : ℝ) * T)
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hMhalf : 1 / 2 ≤ M := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ (q : ℝ) * T by nlinarith)
    linarith [Real.log_two_gt_d9]
  have hlogT : Real.log T ≤ M :=
    Real.log_le_log hT0 (by nlinarith)
  have hLM : L ≤ 3 * M := by
    have hh : L ≤ Real.log (3 * ((q : ℝ) * T)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hh
    have h3 : Real.log 3 ≤ 2 * M := by
      have h32 := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
      rw [Real.log_pow] at h32
      have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show 2 ≤ (q : ℝ) * T by nlinarith)
      dsimp [M]
      norm_num only [Nat.cast_ofNat] at h32
      linarith
    change L ≤ Real.log 3 + M at hh
    linarith
  have hw (ρ : ℂ) : 0 ≤ w ρ := Nat.cast_nonneg _
  have hu (ρ : ℂ) (hρ : ρ ∈ S) : 1 ≤ u ρ ∧ u ρ ≤ T :=
    ⟨le_max_left _ _, max_le (by linarith) (hf.mem_toFinset.mp hρ).2.2.2⟩
  obtain ⟨hint, hpartial⟩ := reciprocal_sum_partial193 S u w one_pos (by linarith) hu
  have hc (t : ℝ) (ht : 1 ≤ t) (htT : t ≤ T) (A : Finset ℂ)
      (hA : ∀ ρ ∈ A, ρ ∈ LZeros χ t) :
      (∑ ρ ∈ A, w ρ) ≤ K * t * L := by
    have hh := hcount q χ hχ t ht A hA
    have hl : Real.log ((q : ℝ) * (t + 4)) ≤ L :=
      Real.log_le_log (by positivity) (by nlinarith)
    exact hh.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  have hboundary : (∑ ρ ∈ S, w ρ) ≤ K * T * L :=
    hc T (by linarith) le_rfl S (fun ρ hρ => hf.mem_toFinset.mp hρ)
  have hcut (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) T) :
      (∑ ρ ∈ S.filter (fun ρ => u ρ < t), w ρ) ≤ K * t * L := by
    apply hc t ht.1 ht.2
    intro ρ hρ
    obtain ⟨hρ, hut⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hr0, hr1, hi⟩ := hf.mem_toFinset.mp hρ
    exact ⟨hz, hr0, hr1, (le_max_right 1 |ρ.im|).trans hut.le⟩
  have hlow : (∑ ρ ∈ S.filter (fun ρ => |ρ.im| ≤ 1), w ρ) ≤ K * L := by
    have hh := hc 1 le_rfl (by linarith) (S.filter (fun ρ => |ρ.im| ≤ 1)) (by
      intro ρ hρ
      obtain ⟨hρ, hi⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hr0, hr1, _⟩ := hf.mem_toFinset.mp hρ
      exact ⟨hz, hr0, hr1, hi⟩)
    simpa using hh
  have hnorm : (∑ ρ ∈ S, w ρ / ‖ρ‖) ≤ (∑ ρ ∈ S, w ρ / u ρ) +
      ∑ ρ ∈ S.filter (fun ρ => |ρ.im| ≤ 1), w ρ := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hr := L_re_eq_half_of_GRH hG χ ρ (hf.mem_toFinset.mp hρ)
    have hn : (1 / 2 : ℝ) ≤ ‖ρ‖ := by
      have hh := Complex.abs_re_le_norm ρ
      rw [hr] at hh
      norm_num at hh ⊢
      exact hh
    by_cases hi : |ρ.im| ≤ 1
    · simp only [if_pos hi, u, max_eq_left hi, div_one]
      have hh := div_le_div_of_nonneg_left (hw ρ) (by norm_num : (0 : ℝ) < 1 / 2) hn
      linarith
    · simp only [if_neg hi, add_zero, u, max_eq_right (le_of_not_ge hi)]
      exact div_le_div_of_nonneg_left (hw ρ) (by linarith [lt_of_not_ge hi])
        (Complex.abs_im_le_norm ρ)
  have hzero (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) T) : t ≠ 0 := by
    rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ T)] at ht
    linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => K * t * L / t ^ 2)
      (Set.uIcc (1 : ℝ) T) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht; exact pow_ne_zero 2 (hzero t ht)
  have hInt : (∫ t in (1 : ℝ)..T, K * t * L / t ^ 2) = K * L * Real.log T := by
    have he : (∫ t in (1 : ℝ)..T, K * t * L / t ^ 2) =
        ∫ t in (1 : ℝ)..T, (K * L) * (1 / t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      field_simp [hzero t ht] <;> ring
    rw [he, intervalIntegral.integral_const_mul, integral_one_div]
    · simp
    · intro ht
      exact hzero 0 ht rfl
  have hIntle := intervalIntegral.integral_mono_on (by linarith : (1 : ℝ) ≤ T)
    hint hcont.intervalIntegrable
    (fun t ht => div_le_div_of_nonneg_right (hcut t ht) (sq_nonneg t))
  rw [hInt] at hIntle
  have hdiv := div_le_div_of_nonneg_right hboundary hT0.le
  have hcancel : K * T * L / T = K * L := by field_simp <;> ring
  rw [hcancel] at hdiv
  have htotal : (∑ ρ ∈ S, w ρ / ‖ρ‖) ≤ K * L * (2 + Real.log T) := by
    nlinarith
  have hfactor : 2 + Real.log T ≤ 5 * M := by linarith
  have hprod : L * (2 + Real.log T) ≤ (3 * M) * (5 * M) :=
    mul_le_mul hLM hfactor (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)])
      (by linarith)
  change (∑ ρ ∈ S, w ρ / ‖ρ‖) ≤ (20 * K) * M ^ 2
  calc
    _ ≤ K * L * (2 + Real.log T) := htotal
    _ = K * (L * (2 + Real.log T)) := by ring
    _ ≤ K * ((3 * M) * (5 * M)) := mul_le_mul_of_nonneg_left hprod hK.le
    _ = 15 * K * M ^ 2 := by ring
    _ ≤ (20 * K) * M ^ 2 := by nlinarith [mul_nonneg hK.le (sq_nonneg M)]

/-- The nonprincipal square-root bound uses only the proved character formula.
Davenport chapter 20 page 125, the unnumbered bound before display 14.
The constant is absolute and GRH remains an explicit hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
theorem psiChi_nonprincipal_bound593 (hG : GRH) :
    ∃ c : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ x : ℝ, 2 ≤ x →
        ‖psiChi χ x‖ ≤ c * √x * Real.log (q * x) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := character_formula623 hG
  obtain ⟨B, hB0, hB⟩ := character_reciprocal_GRH593 hG
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  refine ⟨B + 5 * C', ?_⟩
  intro q _ χ hχ x hx
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hx0 : 0 < x := by linarith
  have hfin := LZeros_finite χ x
  have hline := L_re_eq_half_of_GRH hG χ (T := x)
  have h1 := hC q χ hχ x x hx hx le_rfl hfin
  have h2 := norm_zero_sum_le χ hx0 hfin hline
  have h3 := hB q χ hχ x hx hfin
  set L := Real.log (q * x) with hL
  set S := ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  set R := ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖
  -- elementary facts
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL069 : 0.69 ≤ L := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
    linarith
  have hlogx : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsx : 1 ≤ √x := by rw [Real.one_le_sqrt]; linarith
  have hxL : x * L ^ 2 / x = L ^ 2 := by field_simp
  rw [hxL] at h1
  have hRL : R ≤ B * L ^ 2 := h3
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun ρ _ => by positivity
  -- triangle inequality
  have htri : ‖psiChi χ x‖ ≤
      ‖psiChi χ x + S‖ + ‖S‖ := by
    have := norm_sub_le (psiChi χ x + S) S
    simpa using this
  have hE : C * (L ^ 2 + √x + L ^ 2) ≤ C' * (2 * L ^ 2 + √x) := by
    have : 0 ≤ L ^ 2 + √x + L ^ 2 := by positivity
    nlinarith
  have hL2 : 1 ≤ 2.11 * L ^ 2 := by nlinarith
  have hsxL : √x ≤ 2.11 * √x * L ^ 2 := by nlinarith
  have hLL : L ^ 2 ≤ √x * L ^ 2 := by nlinarith [sq_nonneg L]
  have hSR : √x * R ≤ B * √x * L ^ 2 := by nlinarith
  have hfin' : C' * (2 * L ^ 2 + √x) ≤ 5 * C' * √x * L ^ 2 := by nlinarith
  nlinarith

/-- A coarse cumulative zeta count follows from local unit windows.
Davenport chapter 17 pages 108 and 109, auxiliary count for partial summation.
The finite head is absorbed into an unspecified absolute constant.
-/
theorem zeta_count593 : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
    ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ zetaZeros T) →
      (∑ ρ ∈ S, (zetaMult ρ : ℝ)) ≤ C * T * Real.log (T + 4) := by
  classical
  obtain ⟨K, hK, hwindow⟩ := zeta_window_mass593
  let F := (zetaZeros_finite 6).toFinset
  let H : ℝ := ∑ ρ ∈ F, (zetaMult ρ : ℝ)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun ρ _ => Nat.cast_nonneg _)
  let J : ℝ := H + 2 * K + 1
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨3 * J, by positivity, ?_⟩
  intro T hT S hS
  have hT0 : 0 ≤ T := by linarith
  let L := Real.log (T + 4)
  have hL : 1 ≤ L := (Real.le_log_iff_exp_le (by linarith : 0 < T + 4)).mpr
    (by linarith [Real.exp_one_lt_three])
  let b : ℂ → ℕ := fun ρ => ⌈|ρ.im|⌉₊
  let N := ⌈T⌉₊ + 1
  have hmaps : ∀ ρ ∈ S, b ρ ∈ Finset.range N := by
    intro ρ hρ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (hS ρ hρ).2.2.2))
  have hband (n : ℕ) (hn : n ∈ Finset.range N) :
      (∑ ρ ∈ S.filter (fun ρ => b ρ = n), (zetaMult ρ : ℝ)) ≤ J * L := by
    have hnT : (n : ℝ) ≤ T + 1 := by
      have hh : n ≤ ⌈T⌉₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      exact (Nat.cast_le.mpr hh).trans (Nat.ceil_lt_add_one hT0).le
    have hhi (ρ : ℂ) (hρ : ρ ∈ S.filter (fun ρ => b ρ = n)) : |ρ.im| ≤ n := by
      have he : ⌈|ρ.im|⌉₊ = n := (Finset.mem_filter.mp hρ).2
      simpa only [he] using Nat.le_ceil |ρ.im|
    by_cases hn6 : n ≤ 6
    · have hsub : S.filter (fun ρ => b ρ = n) ⊆ F := by
        intro ρ hρ
        obtain ⟨hz, hr0, hr1, _⟩ := hS ρ (Finset.mem_filter.mp hρ).1
        have hh : (n : ℝ) ≤ 6 := by exact_mod_cast hn6
        exact (zetaZeros_finite 6).mem_toFinset.mpr ⟨hz, hr0, hr1, (hhi ρ hρ).trans hh⟩
      have hh : (∑ ρ ∈ S.filter (fun ρ => b ρ = n), (zetaMult ρ : ℝ)) ≤ H :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => Nat.cast_nonneg _)
      have hHL : H ≤ H * L := le_mul_of_one_le_right hH hL
      exact hh.trans (hHL.trans (mul_le_mul_of_nonneg_right
        (by dsimp [J]; linarith) (by linarith)))
    · have hnpos : 0 < n := by omega
      let a : ℝ := (n - 1 : ℕ)
      have ha : 5 ≤ a := by dsimp [a]; exact_mod_cast (show 5 ≤ n - 1 by omega)
      have he : a + 1 = (n : ℝ) := by
        dsimp [a]
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ n by omega) : n - 1 + 1 = n)
      let hfA := zetaZeros_finite a
      let hfN := zetaZeros_finite n
      have hfW : (zetaZerosWindow a).Finite := by
        apply (zetaZeros_finite (a + 1)).subset
        intro ρ hρ
        obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hρ
        exact ⟨hz, hr0, hr1, by rw [abs_of_pos (by linarith : 0 < ρ.im)]; exact hhi⟩
      have hsub : S.filter (fun ρ => b ρ = n) ⊆ hfN.toFinset \ hfA.toFinset := by
        intro ρ hρ
        obtain ⟨hz, hr0, hr1, _⟩ := hS ρ (Finset.mem_filter.mp hρ).1
        have hceil : ⌈|ρ.im|⌉₊ = n := (Finset.mem_filter.mp hρ).2
        have hlo : a < |ρ.im| := (Nat.ceil_eq_iff hnpos.ne').mp hceil |>.1
        refine Finset.mem_sdiff.mpr ⟨hfN.mem_toFinset.mpr ⟨hz, hr0, hr1, hhi ρ hρ⟩, ?_⟩
        intro hh
        exact not_le_of_gt hlo (hfA.mem_toFinset.mp hh).2.2.2
      have hm := zeta_band_mass266 (by linarith : 0 < a) he.ge hfA hfN hfW
      have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun ρ _ _ => (show (0 : ℝ) ≤ (zetaMult ρ : ℝ) from Nat.cast_nonneg _))
      have hw := hwindow a ha hfW
      have hlog : Real.log a ≤ L := Real.log_le_log (by linarith) (by linarith)
      have hkL := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * K by positivity)
      have hJL : 2 * K * L ≤ J * L := mul_le_mul_of_nonneg_right
        (by dsimp [J]; linarith) (by linarith)
      nlinarith
  have hN : (N : ℝ) ≤ 3 * T := by
    have hh := Nat.ceil_lt_add_one hT0
    dsimp [N]
    push_cast
    linarith
  calc
    _ = ∑ n ∈ Finset.range N,
        ∑ ρ ∈ S.filter (fun ρ => b ρ = n), (zetaMult ρ : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ Finset.range N, J * L := Finset.sum_le_sum hband
    _ = (N : ℝ) * (J * L) := by simp
    _ ≤ (3 * T) * (J * L) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

/-- Under GRH, reciprocal zeta mass has an absolute log-squared bound.
Davenport chapter 17 page 108, auxiliary bound using the proved local count.
No Rosser coefficients or low-height zero-free certificate are assumed.
-/
theorem zeta_reciprocal_GRH593 (hG : GRH) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 2 ≤ T → ∀ hf : (zetaZeros T).Finite,
      (∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) ≤ K * Real.log T ^ 2 := by
  classical
  obtain ⟨K, hK, hcount⟩ := zeta_count593
  refine ⟨20 * K, by positivity, ?_⟩
  intro T hT hf
  have hT0 : 0 < T := by linarith
  let S := hf.toFinset
  let w : ℂ → ℝ := fun ρ => zetaMult ρ
  let u : ℂ → ℝ := fun ρ => max 1 |ρ.im|
  let L := Real.log (T + 4)
  let M := Real.log T
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hMhalf : 1 / 2 ≤ M := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      hT
    linarith [Real.log_two_gt_d9]
  have hlogT : Real.log T ≤ M := le_rfl
  have hLM : L ≤ 3 * M := by
    have hh : L ≤ Real.log (3 * T) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hh
    have h3 : Real.log 3 ≤ 2 * M := by
      have h32 := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
      rw [Real.log_pow] at h32
      have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        hT
      dsimp [M]
      norm_num only [Nat.cast_ofNat] at h32
      linarith
    change L ≤ Real.log 3 + M at hh
    linarith
  have hw (ρ : ℂ) : 0 ≤ w ρ := Nat.cast_nonneg _
  have hu (ρ : ℂ) (hρ : ρ ∈ S) : 1 ≤ u ρ ∧ u ρ ≤ T :=
    ⟨le_max_left _ _, max_le (by linarith) (hf.mem_toFinset.mp hρ).2.2.2⟩
  obtain ⟨hint, hpartial⟩ := reciprocal_sum_partial193 S u w one_pos (by linarith) hu
  have hc (t : ℝ) (ht : 1 ≤ t) (htT : t ≤ T) (A : Finset ℂ)
      (hA : ∀ ρ ∈ A, ρ ∈ zetaZeros t) :
      (∑ ρ ∈ A, w ρ) ≤ K * t * L := by
    have hh := hcount t ht A hA
    have hl : Real.log (t + 4) ≤ L :=
      Real.log_le_log (by positivity) (by nlinarith)
    exact hh.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  have hboundary : (∑ ρ ∈ S, w ρ) ≤ K * T * L :=
    hc T (by linarith) le_rfl S (fun ρ hρ => hf.mem_toFinset.mp hρ)
  have hcut (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) T) :
      (∑ ρ ∈ S.filter (fun ρ => u ρ < t), w ρ) ≤ K * t * L := by
    apply hc t ht.1 ht.2
    intro ρ hρ
    obtain ⟨hρ, hut⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hr0, hr1, hi⟩ := hf.mem_toFinset.mp hρ
    exact ⟨hz, hr0, hr1, (le_max_right 1 |ρ.im|).trans hut.le⟩
  have hlow : (∑ ρ ∈ S.filter (fun ρ => |ρ.im| ≤ 1), w ρ) ≤ K * L := by
    have hh := hc 1 le_rfl (by linarith) (S.filter (fun ρ => |ρ.im| ≤ 1)) (by
      intro ρ hρ
      obtain ⟨hρ, hi⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hr0, hr1, _⟩ := hf.mem_toFinset.mp hρ
      exact ⟨hz, hr0, hr1, hi⟩)
    simpa using hh
  have hnorm : (∑ ρ ∈ S, w ρ / ‖ρ‖) ≤ (∑ ρ ∈ S, w ρ / u ρ) +
      ∑ ρ ∈ S.filter (fun ρ => |ρ.im| ≤ 1), w ρ := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hr := re_eq_half_of_GRH hG (hf.mem_toFinset.mp hρ)
    have hn : (1 / 2 : ℝ) ≤ ‖ρ‖ := by
      have hh := Complex.abs_re_le_norm ρ
      rw [hr] at hh
      norm_num at hh ⊢
      exact hh
    by_cases hi : |ρ.im| ≤ 1
    · simp only [if_pos hi, u, max_eq_left hi, div_one]
      have hh := div_le_div_of_nonneg_left (hw ρ) (by norm_num : (0 : ℝ) < 1 / 2) hn
      linarith
    · simp only [if_neg hi, add_zero, u, max_eq_right (le_of_not_ge hi)]
      exact div_le_div_of_nonneg_left (hw ρ) (by linarith [lt_of_not_ge hi])
        (Complex.abs_im_le_norm ρ)
  have hzero (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) T) : t ≠ 0 := by
    rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ T)] at ht
    linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => K * t * L / t ^ 2)
      (Set.uIcc (1 : ℝ) T) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht; exact pow_ne_zero 2 (hzero t ht)
  have hInt : (∫ t in (1 : ℝ)..T, K * t * L / t ^ 2) = K * L * Real.log T := by
    have he : (∫ t in (1 : ℝ)..T, K * t * L / t ^ 2) =
        ∫ t in (1 : ℝ)..T, (K * L) * (1 / t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      field_simp [hzero t ht] <;> ring
    rw [he, intervalIntegral.integral_const_mul, integral_one_div]
    · simp
    · intro ht
      exact hzero 0 ht rfl
  have hIntle := intervalIntegral.integral_mono_on (by linarith : (1 : ℝ) ≤ T)
    hint hcont.intervalIntegrable
    (fun t ht => div_le_div_of_nonneg_right (hcut t ht) (sq_nonneg t))
  rw [hInt] at hIntle
  have hdiv := div_le_div_of_nonneg_right hboundary hT0.le
  have hcancel : K * T * L / T = K * L := by field_simp <;> ring
  rw [hcancel] at hdiv
  have htotal : (∑ ρ ∈ S, w ρ / ‖ρ‖) ≤ K * L * (2 + Real.log T) := by
    nlinarith
  have hfactor : 2 + Real.log T ≤ 5 * M := by linarith
  have hprod : L * (2 + Real.log T) ≤ (3 * M) * (5 * M) :=
    mul_le_mul hLM hfactor (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)])
      (by linarith)
  change (∑ ρ ∈ S, w ρ / ‖ρ‖) ≤ (20 * K) * M ^ 2
  calc
    _ ≤ K * L * (2 + Real.log T) := htotal
    _ = K * (L * (2 + Real.log T)) := by ring
    _ ≤ K * ((3 * M) * (5 * M)) := mul_le_mul_of_nonneg_left hprod hK.le
    _ = 15 * K * M ^ 2 := by ring
    _ ≤ (20 * K) * M ^ 2 := by nlinarith [mul_nonneg hK.le (sq_nonneg M)]

/-- All characters have a coarse reciprocal zero bound under GRH.
Davenport chapter 19 pages 117 and 118 and chapter 20 page 125.
Principal characters use the zeta zero-set and multiplicity identities.
-/
theorem character_reciprocal_all593 (hG : GRH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (T : ℝ), 2 ≤ T → ∀ hf : (LZeros χ T).Finite,
        (∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤
          K * Real.log ((q : ℝ) * T) ^ 2 := by
  classical
  obtain ⟨A, hA, hnon⟩ := character_reciprocal_GRH593 hG
  obtain ⟨B, hB, hzeta⟩ := zeta_reciprocal_GRH593 hG
  refine ⟨A + B, by positivity, ?_⟩
  intro q _ χ T hT hf
  by_cases hχ : χ = 1
  · subst χ
    let hfZ := zetaZeros_finite T
    have hset : LZeros (1 : DirichletCharacter ℂ q) T = zetaZeros T := by
      ext ρ
      constructor
      · intro hρ
        exact ⟨(principal_zero_data574 (q := q) hρ.2.1 hρ.2.2.1).1.mp hρ.1, hρ.2⟩
      · intro hρ
        exact ⟨(principal_zero_data574 (q := q) hρ.2.1 hρ.2.2.1).1.mpr hρ.1, hρ.2⟩
    have hsum : (∑ ρ ∈ hf.toFinset, (LMult (1 : DirichletCharacter ℂ q) ρ : ℝ) / ‖ρ‖) =
        ∑ ρ ∈ hfZ.toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ := by
      apply Finset.sum_congr (Set.Finite.toFinset_inj.mpr hset)
      intro ρ hρ
      obtain ⟨hz, hr0, hr1, hi⟩ := hfZ.mem_toFinset.mp hρ
      rw [(principal_zero_data574 (q := q) hr0 hr1).2]
    rw [hsum]
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have ht0 : 0 < T := by linarith
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hlog : Real.log T ≤ Real.log ((q : ℝ) * T) :=
      Real.log_le_log ht0 (by nlinarith)
    have hsquare := pow_le_pow_left₀ hlogT hlog 2
    have hb := mul_le_mul_of_nonneg_left hsquare hB.le
    have hrest : 0 ≤ A * Real.log ((q : ℝ) * T) ^ 2 := by positivity
    exact (hzeta T hT hfZ).trans (by nlinarith)
  · exact (hnon q χ hχ T hT hf).trans (by nlinarith [sq_nonneg (Real.log ((q : ℝ) * T))])

/-- **GRH bound for `ψ(x, χ)`**: there is an absolute `c` with
`|ψ(x, χ) - δ_χ x| ≤ c √x log²(qx)` for every modulus `q`, character `χ` mod `q`, and
`x ≥ 2`. Davenport ch. 20, p. 125. PROVED from the leaves with `T = x`, no unproved step in this
proof; CONDITIONAL ON GRH and the leaves `explicit_formula_chi_GRH`, `LZeros_finite`,
`LZeros_recip_sum`. -/
theorem psiChi_bound_of_GRH (hG : GRH) : ∃ c : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ c * √x * Real.log (q * x) ^ 2 := by
  obtain ⟨C, hC⟩ := explicit_formula_chi_GRH hG
  obtain ⟨B, hB0, hB⟩ := character_reciprocal_all593 hG
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  refine ⟨B + 5 * C', ?_⟩
  intro q _ χ x hx
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hx0 : 0 < x := by linarith
  have hfin := LZeros_finite χ x
  have hline := L_re_eq_half_of_GRH hG χ (T := x)
  have h1 := hC q χ x x hx hx le_rfl hfin
  have h2 := norm_zero_sum_le χ hx0 hfin hline
  have h3 := hB q χ x hx hfin
  set L := Real.log (q * x) with hL
  set S := ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  set R := ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖
  -- elementary facts
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL069 : 0.69 ≤ L := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
    linarith
  have hlogx : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsx : 1 ≤ √x := by rw [Real.one_le_sqrt]; linarith
  have hxL : x * L ^ 2 / x = L ^ 2 := by field_simp
  rw [hxL] at h1
  have hRL : R ≤ B * L ^ 2 := h3
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun ρ _ => by positivity
  -- triangle inequality
  have htri : ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + S‖ + ‖S‖ := by
    have := norm_sub_le (psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + S) S
    simpa using this
  have hE : C * (L ^ 2 + √x + L ^ 2) ≤ C' * (2 * L ^ 2 + √x) := by
    have : 0 ≤ L ^ 2 + √x + L ^ 2 := by positivity
    nlinarith
  have hL2 : 1 ≤ 2.11 * L ^ 2 := by nlinarith
  have hsxL : √x ≤ 2.11 * √x * L ^ 2 := by nlinarith
  have hLL : L ^ 2 ≤ √x * L ^ 2 := by nlinarith [sq_nonneg L]
  have hSR : √x * R ≤ B * √x * L ^ 2 := by nlinarith
  have hfin' : C' * (2 * L ^ 2 + √x) ≤ 5 * C' * √x * L ^ 2 := by nlinarith
  nlinarith

/-- Vacuity: the hypotheses `2 ≤ x`, `2 ≤ T ≤ x` of the explicit formulas hold at
`x = T = 2`, and `x = 5/2` is a non-integer with `x ≥ 2` for `perron_psi`. -/
example : (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 ∧ (∀ n : ℕ, (n : ℝ) ≠ 5 / 2) := by
  refine ⟨le_rfl, le_rfl, fun n h => ?_⟩
  have h2 : (n : ℝ) * 2 = 5 := by rw [h]; norm_num
  have : n * 2 = 5 := by exact_mod_cast h2
  omega

example : (1 / 2 : ℝ) ≤ |(2 : ℝ) + 1 / 2 - 2| := by simpa using half_integer_distance197 2 2

example : (0 : ℝ) < 2 ∧ (0 : ℝ) < 1 := by norm_num

example : (1 : ℝ) < 2 := by norm_num

example : Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-(2 : ℝ))) := (log_nat_rpow_summable_bound197 (by norm_num : (1 : ℝ) < 2)).1

example : (2 : ℝ) ≤ 2 := le_rfl

example : (0 : ℝ) < 2 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧ ((1 : ℝ) ≤ 2 / 2 ∨ 2 * 2 ≤ 1) := by norm_num

example : (0 : ℝ) < 2 ∧ (0 : ℝ) < 3 ∧ (0 : ℝ) < 2 ∧ (3 : ℝ) ≤ 2 * 2 ∧ (2 : ℝ) ≠ 3 := by norm_num

example : (2 : ℝ) ≤ 2 ∧ (2 : ℝ) / 2 ≤ 2 ∧ (2 : ℝ) ≤ 2 * 2 := by norm_num

example : (∑ n ∈ Finset.range (2 * 2 + 2), 1 / |(2 : ℝ) + 1 / 2 - n|) ≤ 4 * (1 + Real.log (2 + 1 : ℝ)) := by simpa using half_integer_recip_sum197 2

example : (2 : ℕ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := by norm_num

example : (0 : ℝ) < 2 ∧ (1 : ℝ) < 2 ∧ (0 : ℝ) < 2 := by norm_num

example : (2 : ℝ) ≤ 5 / 2 ∧ (1 : ℝ) < 2 ∧ (0 : ℝ) < 2 := by norm_num

example : (0 : ℝ) < 2 ∧ (2 : ℂ) ≠ 0 ∧ (2 : ℂ) ≠ 1 := by norm_num

example : (0 : ℝ) < 2 := by norm_num

example : (0 : ℝ) < 2 := by norm_num

example : MeromorphicAt (fK 2) 1 := perron_integrand_meromorphic197 (by norm_num) 1

example : AnalyticAt ℂ (fK 2) 2 := perron_integrand_analytic197 (by norm_num) (by norm_num) (by norm_num) (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

example : (1 : ℝ) < 2 := by norm_num

example : -1 ≤ meromorphicOrderAt (fK 2) 0 := perron_integrand_order197 (by norm_num) 0

example : ∃ T ∈ Set.Icc (5 : ℝ) 6,
    ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩, riemannZeta z ≠ 0 := by
  obtain ⟨C, hC, hg⟩ := good_height_pm
  obtain ⟨T, hTI, hgood⟩ := hg 5 (by norm_num)
  refine ⟨T, by constructor <;> linarith [hTI.1, hTI.2], ?_⟩
  intro z hz
  have hzR := (mem_rect (c := 2) (T := T) (by norm_num) (by linarith [hTI.1])).mp
    ((rectangleBorder_subset_rectangle _ _) hz)
  rcases border_cases hz with h | h | h | h
  · have heq : (z.re : ℂ) + ((-T : ℝ) : ℂ) * I = z := by
      apply Complex.ext <;> simp [h]
    simpa only [heq] using (hgood z.re hzR.1 (-T) (by simp)).1
  · have heq : ((-1 / 2 : ℝ) : ℂ) + z.im * I = z := by
      apply Complex.ext <;> simp [h]
    simpa only [heq] using LeanLab.PNTPort.ZetaZeros.zeta_left_ne z.im
  · have heq : (z.re : ℂ) + (T : ℂ) * I = z := by
      apply Complex.ext <;> simp [h]
    simpa only [heq] using (hgood z.re hzR.1 T (by simp)).1
  · apply riemannZeta_ne_zero_of_one_lt_re
    rw [h]
    norm_num

example : Chebyshev.psi ((⌊(2 : ℝ)⌋₊ : ℝ) + 1 / 2) = Chebyshev.psi 2 := psi_floor_half197 2

example : (0 : ℝ) ≤ 2 := by norm_num

example : (0 : ℝ) < 2 := by norm_num

example : (0 : ℝ) < 2 ∧ (0 : ℝ) < 2 ∧ (1 : ℕ) ≤ 1 := by norm_num

example : (1 : ℝ) < 2 ∧ (0 : ℝ) < 2 := by norm_num

example : (5 : ℝ) ≤ 5 ∧ (-(1 / 2 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 2) := by norm_num

example : (5 : ℝ) ≤ 5 ∧ (-2 : ℝ) ≤ 3 := by norm_num

example : (2 : ℝ) ≤ 5 ∧ (0 : ℝ) ≤ 3 := by norm_num

example : (2 : ℝ) ≤ 2 ∧ (0 : ℝ) ≤ 0 := by norm_num

example : (1 : ℝ) < 2 ∧ (0 : ℝ) ≤ 2 := by norm_num

example : (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 5 := by norm_num

example : (2 : ℝ) ≤ 5/2 ∧ (1 : ℝ) < 2 ∧ (0 : ℝ) < 2 := by norm_num

example : (0 : ℝ) < 2 ∧ (1 : ℝ) < 2 ∧ (0 : ℝ) < 2 := by norm_num

example : (2 : ℕ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := by norm_num

example : (2 : ℕ) ≤ 5 ∧ (2 : ℝ) ≤ 5 ∧ (5 : ℝ) ≤ 5+1/2 := by norm_num

/-- The nonprincipal hypotheses have a concrete modulus-three witness. -/
example : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ 3
  refine ⟨e.symm (-1), ?_⟩
  intro hh
  have hh' := congrArg e hh
  simp only [MulEquiv.apply_symm_apply, map_one] at hh'
  have hc := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hh'
  exact (by decide : (-1 : ZMod 3) ≠ 1) hc

example (hG : GRH) : ∃ K : ℝ, 0 < K ∧
    ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      (∑ ρ ∈ (LZeros_finite χ 2).toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤
        K * Real.log (6 : ℝ) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := character_reciprocal_GRH593 hG
  refine ⟨K, hK, ?_⟩
  intro χ hχ
  have hh := hb 3 χ hχ 2 (by norm_num) (LZeros_finite χ 2)
  norm_num at hh ⊢
  exact hh

example (hG : GRH) : ∃ c : ℝ,
    ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      ‖psiChi χ 2‖ ≤ c * √2 * Real.log (6 : ℝ) ^ 2 := by
  obtain ⟨c, hb⟩ := psiChi_nonprincipal_bound593 hG
  refine ⟨c, ?_⟩
  intro χ hχ
  have hh := hb 3 χ hχ 2 (by norm_num)
  norm_num at hh ⊢
  exact hh

example : (0 : ℝ) ≤ 0 ∧ (1 : ℝ) ≤ 1 ∧ (2 : ℝ) ≤ 2 ∧
    ∀ ρ ∈ (∅ : Finset ℂ), ρ ∈ LZeros (1 : DirichletCharacter ℂ 1) 1 := by
  simp

example : ∃ C : ℝ, 0 < C ∧
    ‖(Chebyshev.psi 2 : ℂ) - 2 + ∑ ρ ∈ (zetaZeros_finite 2).toFinset,
      (zetaMult ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
      C * (2 * Real.log 2 ^ 2 / 2 + √2 + Real.log 2 ^ 2) := by
  obtain ⟨C, hC, hb⟩ := zeta_formula593
  exact ⟨C, hC, hb 2 2 (by norm_num) (by norm_num) le_rfl (zetaZeros_finite 2)⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖psiChi (1 : DirichletCharacter ℂ 1) 2 - 2 +
      ∑ ρ ∈ (LZeros_finite (1 : DirichletCharacter ℂ 1) 2).toFinset,
        (LMult (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
      C * (2 * Real.log 2 ^ 2 / 2 + √2 + Real.log 2 ^ 2) := by
  obtain ⟨C, hC, hb⟩ := principal_formula593
  refine ⟨C, hC, ?_⟩
  simpa using hb 1 2 2 (by norm_num) (by norm_num) le_rfl
    (LZeros_finite (1 : DirichletCharacter ℂ 1) 2)

example : ∃ B : ℝ, 0 < B ∧ ∃ U ∈ Set.Icc (5 : ℝ) 6,
    ∀ hf : (zetaZeros U).Finite,
      ‖perronPsi 5 (1 + 1 / Real.log 5) U -
        ((5 : ℂ) - ∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (5 : ℂ) ^ ρ / ρ)‖ ≤
        B * (5 * Real.log 5 ^ 2 / 5 + √5 + Real.log 5 ^ 2) := by
  obtain ⟨B, hB, hb⟩ := zeta_selected_contour593
  refine ⟨B, hB, ?_⟩
  have hh := hb 5 5 le_rfl le_rfl
  norm_num at hh ⊢
  exact hh

example (hG : GRH) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      (∑ ρ ∈ (LZeros_finite χ 1).toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤
        C * Real.log (3 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := character_low_reciprocal593 hG
  exact ⟨C, hC, fun χ hχ => hb 3 χ hχ (LZeros_finite χ 1)⟩

example : ∃ C : ℝ, 0 < C ∧
    (∑ ρ ∈ (zetaZeros_finite 2).toFinset, (zetaMult ρ : ℝ)) ≤ C * 2 * Real.log 6 := by
  obtain ⟨C, hC, hb⟩ := zeta_count593
  refine ⟨C, hC, ?_⟩
  have hh := hb 2 (by norm_num) (zetaZeros_finite 2).toFinset
    (fun ρ hρ => (zetaZeros_finite 2).mem_toFinset.mp hρ)
  norm_num at hh ⊢
  exact hh

example (hG : GRH) : ∃ K : ℝ, 0 < K ∧
    (∑ ρ ∈ (zetaZeros_finite 2).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) ≤ K * Real.log 2 ^ 2 := by
  obtain ⟨K, hK, hb⟩ := zeta_reciprocal_GRH593 hG
  exact ⟨K, hK, hb 2 (by norm_num) (zetaZeros_finite 2)⟩

example (hG : GRH) : ∃ K : ℝ, 0 < K ∧
    ∀ hf : (LZeros (1 : DirichletCharacter ℂ 1) 2).Finite,
      (∑ ρ ∈ hf.toFinset, (LMult (1 : DirichletCharacter ℂ 1) ρ : ℝ) / ‖ρ‖) ≤
        K * Real.log 2 ^ 2 := by
  obtain ⟨K, hK, hb⟩ := character_reciprocal_all593 hG
  refine ⟨K, hK, ?_⟩
  intro hf
  have hh := hb 1 (1 : DirichletCharacter ℂ 1) 2 (by norm_num) hf
  norm_num at hh ⊢
  exact hh

end LeanLab.DERZ1997.Decomp1529b
