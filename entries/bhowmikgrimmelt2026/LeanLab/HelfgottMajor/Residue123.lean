module

public import Mathlib
public import LeanLab.HelfgottMajor.ZetaRatio123
public import LeanLab.HelfgottMajor.Landau123
public import LeanLab.HelfgottMajor.StripBound123
public import LeanLab.HelfgottMajor.PolyaVinogradov123

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p5, a repair of the rejected p4 branch.
P0014 Helfgott, Major arcs for Goldbach's problem, pages 35 to 37: Lemma 4.2 and displays 4.16
to 4.21, the bound on L'(1, χ)/L(1, χ) that feeds the residue R of Lemma 4.1.

The lab leaf SplitGaussian123.log_derivative_norm_le states the bound 2 log q + 15.07017 with NO
hypothesis on the zeros of L(s, χ). The paper proves it only through Lemma 4.2, whose hypothesis
is that the nontrivial zeros with abs Im at most 5/8 lie on the critical line. This file gives
the paper's route WITH that hypothesis. Lemma 4.2 is PROVED here from Landau123, StripBound123
and ZetaRatio123. Display 4.21 is PROVED CONDITIONAL ON the one LEAF of PolyaVinogradov123,
display 4.20, which the paper states without proof.

No definition is made in this file. M(q) of Lemma 4.2 is written out each time as the supremum
over n of the norm of the sum of χ(m) for m from 1 to n. The p4 file had three definitions,
charSumMax, psum and emSeq, and a copy of the arithmetic of page 37; main already has that
arithmetic in SPLIT_residue_log_derivative_bound, so the copy is not carried.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Residue123
open Real
open scoped NNReal

/-! ## The inputs of Lemma 4.2 and display 4.21 -/

lemma charSumMax_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) : 0 ≤ (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) :=
  Real.iSup_nonneg (fun _ => norm_nonneg _)

/-! ## Lemma 4.2, split along its proof on page 36 -/

/-- PROVED in Landau123 from the Borel Caratheodory and Schwarz lemmas of Mathlib. P0014 display 4.16, page 36: a lemma of Landau based on Borel-Carathéodory,
cited from Montgomery and Vaughan 2007, Lemma 6.3 with Lemma 6.2. For f analytic and zero free on
the closed disc of radius R about s0 and bounded there by B, abs f'/f at any point of the disc of
radius r < R about s0 is at most 2R log(B/abs f(s0))/(R − r)². Stated for entire f, which is
all that is used and is narrower. -/
theorem landau_lemma (f : ℂ → ℂ) (hf : Differentiable ℂ f) (s0 : ℂ) (r R B : ℝ) (hr : 0 < r)
    (hrR : r < R) (hz : ∀ z ∈ Metric.closedBall s0 R, f z ≠ 0)
    (hB : ∀ z ∈ Metric.closedBall s0 R, ‖f z‖ ≤ B) (s : ℂ) (hs : s ∈ Metric.closedBall s0 r) :
    ‖deriv f s / f s‖ ≤ 2 * R * Real.log (B / ‖f s0‖) / (R - r) ^ 2 := by
  exact LeanLab.HelfgottMajor.Landau123.landau_lemma f hf s0 r R B hr hrR hz hB s hs

/-- PROVED in StripBound123. P0014 displays 4.18 and 4.19, page 36: by partial summation with N = M(q)/3,
abs L(s, χ) is at most 2√3 √M(q) on the closed disc of radius H = 5/8 about s0 = 1/2 + H,
where the real part is at least 1/2. QUESTION, minor: N must be a positive integer and M(q)/3
need not be one; with N an integer near M(q)/3 the constant 2√3 may change slightly. -/
theorem strip_bound_4_19 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (s : ℂ) (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * Real.sqrt 3 * Real.sqrt ((⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖)) := by
  exact LeanLab.HelfgottMajor.StripBound123.strip_bound_4_19 χ hχ hq s hs

/-- PROVED. One Euler factor: for c of norm at most 1 and x = p^(−9/8),
1/(1 − x²) is at most 1/abs(1 − c x) times 1/(1 − x), since abs(1 − c x) is at most 1 + x. -/
lemma euler_factor_le (p : Nat.Primes) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖(1 - (p : ℂ) ^ (-(9 / 4 : ℂ)))⁻¹‖₊ ≤
      ‖(1 - c * (p : ℂ) ^ (-(9 / 8 : ℂ)))⁻¹‖₊ * ‖(1 - (p : ℂ) ^ (-(9 / 8 : ℂ)))⁻¹‖₊ := by
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  set x : ℝ := (p : ℝ) ^ (-(9 / 8 : ℝ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos (by linarith) _
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have e1 : (p : ℂ) ^ (-(9 / 8 : ℂ)) = (x : ℂ) := by
    rw [hx, Complex.ofReal_cpow (by linarith)]; push_cast; ring_nf
  have e2 : (p : ℂ) ^ (-(9 / 4 : ℂ)) = ((x ^ 2 : ℝ) : ℂ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Complex.ofReal_cpow (by linarith)]
    push_cast; ring_nf
  rw [e1, e2]
  rw [← NNReal.coe_le_coe]
  push_cast
  simp only [norm_inv]
  have hn1 : ‖(1 : ℂ) - (x : ℂ)‖ = 1 - x := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hn2 : ‖(1 : ℂ) - (x : ℂ) ^ 2‖ = 1 - x ^ 2 := by
    rw [show (1 : ℂ) - (x : ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith)]
  have hn3 : ‖(1 : ℂ) - c * (x : ℂ)‖ ≤ 1 + x := by
    calc ‖(1 : ℂ) - c * (x : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖c * (x : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + x := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        nlinarith
  have hn3pos : 0 < ‖(1 : ℂ) - c * (x : ℂ)‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have : ‖c * (x : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; nlinarith
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  rw [hn1, hn2, ← mul_inv]
  apply inv_anti₀ (by nlinarith)
  calc ‖(1 : ℂ) - c * (x : ℂ)‖ * (1 - x) ≤ (1 + x) * (1 - x) :=
        mul_le_mul_of_nonneg_right hn3 (by linarith)
    _ = 1 - x ^ 2 := by ring

/-- PROVED. P0014 page 36, the display after 4.17, at s0 = 9/8: by the Euler product,
abs L(s0, χ) is at least ζ(2 s0)/ζ(s0). -/
theorem euler_lower_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖riemannZeta (9 / 4)‖ / ‖riemannZeta (9 / 8)‖ ≤ ‖DirichletCharacter.LFunction χ (9 / 8)‖ := by
  have hs : 1 < (9 / 8 : ℂ).re := by norm_num
  have hs2 : 1 < (9 / 4 : ℂ).re := by norm_num
  have hL := (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).map
    (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom continuous_nnnorm
  have hZ := (riemannZeta_eulerProduct_hasProd hs).map
    (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom continuous_nnnorm
  have hZ2 := (riemannZeta_eulerProduct_hasProd hs2).map
    (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom continuous_nnnorm
  have hprod := hL.mul hZ
  have hle := hasProd_le (fun p => ?_) hZ2 hprod
  · have hle' : ‖riemannZeta (9 / 4)‖₊ ≤ ‖LSeries (fun n => χ n) (9 / 8)‖₊ *
        ‖riemannZeta (9 / 8)‖₊ := hle
    rw [← NNReal.coe_le_coe] at hle'
    push_cast at hle'
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    have hz98 : 0 < ‖riemannZeta (9 / 8)‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
    rw [div_le_iff₀ hz98]
    exact hle'
  · show ‖(1 - (p : ℂ) ^ (-(9 / 4 : ℂ)))⁻¹‖₊ ≤
      ‖(1 - χ p * (p : ℂ) ^ (-(9 / 8 : ℂ)))⁻¹‖₊ * ‖(1 - (p : ℂ) ^ (-(9 / 8 : ℂ)))⁻¹‖₊
    exact euler_factor_le p (χ p) (DirichletCharacter.norm_le_one χ _)

/-- PROVED in ZetaRatio123. Numerical, narrower than constant_c_le, which it replaces one for one.
ζ(9/8)/ζ(9/4) = 5.88013389940..., by mpmath at 30 digits; the leaf allows 5.880137.
It needs ζ(9/8) to relative precision about 5 times 10 to the minus 7. -/
theorem zeta_ratio_le :
    ‖riemannZeta (9 / 8)‖ / ‖riemannZeta (9 / 4)‖ ≤ 5.880137 := by
  exact LeanLab.HelfgottMajor.ZetaRatio123.zeta_ratio_le

/-- PROVED. 12 · 5.880137² is at most exp 6.028068, from e > 2.7182818283 and the cubic
Taylor lower bound of exp at 0.028068. -/
theorem twelve_sq_le_exp : 12 * (5.880137 : ℝ) ^ 2 ≤ Real.exp 6.028068 := by
  have he := Real.exp_one_gt_d9
  have hsplit : Real.exp 6.028068 = Real.exp 1 ^ 6 * Real.exp 0.028068 := by
    rw [Real.exp_one_pow, ← Real.exp_add]; norm_num
  have hx := Real.sum_le_exp_of_nonneg (x := (0.028068 : ℝ)) (by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hx
  norm_num at hx
  have he6 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 :=
    pow_le_pow_left₀ (by norm_num) he.le 6
  rw [hsplit]
  have h1 : (0 : ℝ) ≤ Real.exp 0.028068 := (Real.exp_pos _).le
  calc 12 * (5.880137 : ℝ) ^ 2 ≤ (2.7182818283 : ℝ) ^ 6 * (1 + 0.028068 + 0.028068 ^ 2 / 2
        + 0.028068 ^ 3 / 6) := by norm_num
    _ ≤ Real.exp 1 ^ 6 * Real.exp 0.028068 := by
        apply mul_le_mul he6 (by norm_num at hx ⊢; linarith) (by norm_num) (by positivity)

/-- The numerical constant of P0014 Lemma 4.2, page 36: c = 5 log(2√3/(ζ(9/4)/ζ(9/8))) =
15.07016..., used as 15.07017 on page 37. SPLIT: PROVED from the narrower leaf
zeta_ratio_le and twelve_sq_le_exp. -/
theorem constant_c_le :
    5 * Real.log (2 * Real.sqrt 3 * (‖riemannZeta (9 / 8)‖ / ‖riemannZeta (9 / 4)‖)) ≤
      15.07017 := by
  have hz94 : 0 < ‖riemannZeta (9 / 4)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hz98 : 0 < ‖riemannZeta (9 / 8)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  set r := ‖riemannZeta (9 / 8)‖ / ‖riemannZeta (9 / 4)‖ with hrdef
  have hr0 : 0 < r := div_pos hz98 hz94
  have hr := zeta_ratio_le
  rw [← hrdef] at hr
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set a := 2 * Real.sqrt 3 * r with hadef
  have ha0 : 0 < a := by positivity
  have hale : a ≤ 2 * Real.sqrt 3 * 5.880137 := by
    rw [hadef]; exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hb0 : 0 < Real.exp 3.014034 := Real.exp_pos _
  have hsqexp : Real.exp 3.014034 ^ 2 = Real.exp 6.028068 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h12 := twelve_sq_le_exp
  have hc2 : (2 * Real.sqrt 3 * 5.880137) ^ 2 ≤ Real.exp 3.014034 ^ 2 := by
    rw [hsqexp]
    have : (2 * Real.sqrt 3 * 5.880137) ^ 2 = 12 * (5.880137 : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, hsq]; ring
    rw [this]; exact h12
  have hc : 2 * Real.sqrt 3 * 5.880137 ≤ Real.exp 3.014034 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hlog : Real.log a ≤ 3.014034 := by
    rw [Real.log_le_iff_le_exp ha0]
    linarith
  linarith

lemma sum_Icc_eq_psum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) = (∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp

lemma sum_range_shift {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (c : ℕ) :
    ∑ m ∈ Finset.range q, f ((c + m : ℕ) : ZMod q) = ∑ a, f a := by
  apply Finset.sum_nbij' (fun m => ((c + m : ℕ) : ZMod q)) (fun a => (a - (c : ZMod q)).val)
  · intro m _; simp
  · intro a _; simpa using ZMod.val_lt (a - (c : ZMod q))
  · intro m hm
    have hm' : m < q := Finset.mem_range.mp hm
    simp only [Nat.cast_add, add_sub_cancel_left]
    exact ZMod.val_cast_of_lt hm'
  · intro a _
    simp only [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  · intro m _; rfl

lemma psum_add_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + q), χ ((1 + k : ℕ) : ZMod q)) = (∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q)) := by
  rw [Finset.sum_range_add]
  have h := sum_range_shift (fun a => χ a) (1 + n)
  have h2 : ∑ x ∈ Finset.range q, χ ((1 + (n + x) : ℕ) : ZMod q) =
      ∑ m ∈ Finset.range q, χ ((1 + n + m : ℕ) : ZMod q) := by
    apply Finset.sum_congr rfl; intro x _; congr 2; ring
  rw [h2, h, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]

lemma psum_mod {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q)) = (∑ k ∈ Finset.range (n % q), χ ((1 + k : ℕ) : ZMod q)) := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  induction n / q with
  | zero => simp
  | succ k ih =>
    rw [show n % q + q * (k + 1) = (n % q + q * k) + q by ring, psum_add_period χ hχ, ih]

lemma norm_psum_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖(∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q))‖ ≤ n := by
  calc _ ≤ ∑ k ∈ Finset.range n, ‖χ ((1 + k : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = n := by simp

lemma norm_psum_le_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q))‖ ≤ (q : ℝ) / 2 := by
  rw [psum_mod χ hχ n]
  set r := n % q with hr
  have hrq : r < q := Nat.mod_lt _ (NeZero.pos q)
  have h1 := norm_psum_le χ r
  -- the complement inside one period
  have hsplit : (∑ k ∈ Finset.range q, χ ((1 + k : ℕ) : ZMod q)) = (∑ k ∈ Finset.range r, χ ((1 + k : ℕ) : ZMod q)) + ∑ k ∈ Finset.range (q - r),
      χ ((1 + (r + k) : ℕ) : ZMod q) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hrq.le]
  have hq0 : (∑ k ∈ Finset.range q, χ ((1 + k : ℕ) : ZMod q)) = 0 := by
    have := psum_add_period χ hχ 0
    simpa using this
  have h2 : ‖(∑ k ∈ Finset.range r, χ ((1 + k : ℕ) : ZMod q))‖ ≤ ((q - r : ℕ) : ℝ) := by
    have he : (∑ k ∈ Finset.range r, χ ((1 + k : ℕ) : ZMod q)) = -∑ k ∈ Finset.range (q - r), χ ((1 + (r + k) : ℕ) : ZMod q) := by
      rw [hq0] at hsplit; exact eq_neg_of_add_eq_zero_left hsplit.symm
    rw [he, norm_neg]
    calc _ ≤ ∑ k ∈ Finset.range (q - r), ‖χ ((1 + (r + k) : ℕ) : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (q - r), (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
      _ = _ := by simp
  rw [Nat.cast_sub hrq.le] at h2
  linarith

/-- PROVED. Page 36, before display 4.20: since the sum of χ(n) over any interval of length q
is 0 for χ nontrivial, M(q) is at most q/2. -/
theorem charSumMax_le_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤ (q : ℝ) / 2 := by
  apply ciSup_le
  intro n
  rw [sum_Icc_eq_psum]
  exact norm_psum_le_half χ hχ n

/-- PROVED. A primitive character modulo q above 1 is nontrivial. -/
theorem ne_one_of_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : χ ≠ 1 := by
  rintro rfl
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
  exact hq hχ.symm

/-- PROVED. Page 37, from display 4.20 to display 4.21: for q at least 33 the even case bound
of the explicit Pólya-Vinogradov inequality 4.20 is at most q^(4/5). -/
theorem pv_even_le (q : ℝ) (hq : 33 ≤ q) :
    2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q ≤
      q ^ (4 / 5 : ℝ) := by
  have hq0 : 0 < q := by linarith
  set u := log q with hu
  have hu32 : 5 * log 2 ≤ u := by
    have h5 : Real.log ((2 : ℝ) ^ 5) = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [hu, ← h5]; exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hl2 := Real.log_two_gt_d9
  have hu0 : 3.4657 ≤ u := by linarith
  have hpi := Real.pi_gt_d4
  have hpi2 : 9.869 ≤ π ^ 2 := by nlinarith
  have hc1 : 2 / π ^ 2 ≤ 0.2027 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hc2 : 4 / π ^ 2 ≤ 0.4054 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have he := Real.exp_one_gt_d9
  have hlogu : log u ≤ 0.36788 * u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < u / exp 1 by positivity)
    rw [Real.log_div (by linarith) (exp_pos 1).ne', Real.log_exp] at h
    have : u / exp 1 ≤ 0.36788 * u := by
      rw [div_le_iff₀ (exp_pos 1)]; nlinarith
    linarith
  have hsplit : q ^ (4 / 5 : ℝ) = sqrt q * exp (0.3 * u) := by
    rw [Real.sqrt_eq_rpow, hu, show (0.3 : ℝ) * log q = log q * 0.3 by ring,
      ← Real.rpow_def_of_pos hq0, ← Real.rpow_add hq0]; norm_num
  have hexp := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.3 * u by positivity) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hexp
  norm_num at hexp
  have hs := Real.sqrt_pos.mpr hq0
  have hlu0 : 0 ≤ log u := Real.log_nonneg (by linarith)
  rw [hsplit]
  have key : 0.2027 * u + 0.4054 * log u + 3 / 2 ≤ exp (0.3 * u) := by
    nlinarith [sq_nonneg u, mul_pos (by linarith : (0:ℝ) < u) (by linarith : (0:ℝ) < u)]
  have hA : 2 / π ^ 2 * u ≤ 0.2027 * u := mul_le_mul_of_nonneg_right hc1 (by linarith)
  have hB : 4 / π ^ 2 * log u ≤ 0.4054 * log u := mul_le_mul_of_nonneg_right hc2 hlu0
  have : 2 / π ^ 2 * u + 4 / π ^ 2 * log u + 3 / 2 ≤ exp (0.3 * u) := by linarith
  calc _ = sqrt q * (2 / π ^ 2 * u + 4 / π ^ 2 * log u + 3 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hs.le

/-- PROVED. Page 37, from display 4.20 to display 4.21: for q at least 33 the odd case bound
of 4.20 is at most q^(4/5). -/
theorem pv_odd_le (q : ℝ) (hq : 33 ≤ q) :
    1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q ≤
      q ^ (4 / 5 : ℝ) := by
  refine le_trans ?_ (pv_even_le q hq)
  have hq0 : 0 < q := by linarith
  have hs := Real.sqrt_nonneg q
  have hu : 0 ≤ log q := Real.log_nonneg (by linarith)
  have hlu0 : 0 ≤ log (log q) := Real.log_nonneg (by
    have : log 3 ≤ log q := Real.log_le_log (by norm_num) (by linarith)
    have h3 : (1 : ℝ) ≤ log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith)
  have hpi := Real.pi_gt_d4
  have hpi4 := Real.pi_lt_d4
  have hpi2 : 9.869 ≤ π ^ 2 := by nlinarith
  have hc1 : 1 / (2 * π) ≤ 2 / π ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hc2 : 1 / π ≤ 4 / π ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h1 := mul_le_mul_of_nonneg_right hc1 (mul_nonneg hs hu)
  have h2 := mul_le_mul_of_nonneg_right hc2 (mul_nonneg hs hlu0)
  nlinarith

/-- PROVED for q at most 32: q/2 is at most q^(4/5). -/
lemma half_le_rpow (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 32) : q / 2 ≤ q ^ (4 / 5 : ℝ) := by
  have h5 : (q ^ ((5 : ℝ)⁻¹)) ^ (5 : ℕ) = q := by
    have := Real.rpow_inv_natCast_pow (x := q) (n := 5) hq0.le (by norm_num)
    simpa using this
  have hle : q ^ ((5 : ℝ)⁻¹) ≤ 2 := by
    by_contra h
    push_neg at h
    have h' : (2 : ℝ) ^ 5 < (q ^ ((5 : ℝ)⁻¹)) ^ (5 : ℕ) :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [h5] at h'
    norm_num at h'
    linarith
  have hsplit : q = q ^ (4 / 5 : ℝ) * q ^ ((5 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hq0]; norm_num
  have hpos : 0 ≤ q ^ (4 / 5 : ℝ) := Real.rpow_nonneg hq0.le _
  have hp2 : 0 ≤ q ^ ((5 : ℝ)⁻¹) := Real.rpow_nonneg hq0.le _
  calc q / 2 = q ^ (4 / 5 : ℝ) * q ^ ((5 : ℝ)⁻¹) / 2 := by rw [← hsplit]
    _ ≤ _ := by nlinarith

/-- PROVED. M(q) is at least 1 for a nontrivial character: the partial sum at n = 1 is χ(1). -/
lemma one_le_charSumMax {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    1 ≤ (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) := by
  have hbdd : BddAbove (Set.range fun n : ℕ => ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) := by
    refine ⟨(q : ℝ) / 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    show ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ (q : ℝ) / 2
    rw [sum_Icc_eq_psum]
    exact norm_psum_le_half χ hχ n
  have h := le_ciSup hbdd 1
  refine le_trans ?_ h
  simp

/-- PROVED from landau_lemma, strip_bound_4_19, euler_lower_bound and constant_c_le, all PROVED.
P0014 Lemma 4.2, pages 35 and 36: under the zero hypothesis with H = 5/8,
abs L'(1, χ)/L(1, χ) is at most 5/2 log M(q) + 15.07017. Display 4.17 is display 4.16 with
s0 = 1/2 + H, r = H − 1/2 and R tending to H from below. -/
theorem lemma_4_2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≠ 1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      5 / 2 * Real.log ((⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖)) + 15.07017 := by
  have hχ1 := ne_one_of_isPrimitive χ hχ hq
  set L := DirichletCharacter.LFunction χ with hLdef
  have hdiff : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ1
  set M := (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) with hMdef
  have hM1 : 1 ≤ M := one_le_charSumMax χ hχ1
  set B := 2 * Real.sqrt 3 * Real.sqrt M with hBdef
  have hB0 : 0 < B := by positivity
  have hL0 : 0 < ‖L (9 / 8)‖ := by
    rw [norm_pos_iff]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by norm_num)
  have hz94 : 0 < ‖riemannZeta (9 / 4)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hz98 : 0 < ‖riemannZeta (9 / 8)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  set Z := ‖riemannZeta (9 / 4)‖ / ‖riemannZeta (9 / 8)‖ with hZdef
  have hZ0 : 0 < Z := div_pos hz94 hz98
  have hZL : Z ≤ ‖L (9 / 8)‖ := euler_lower_bound χ
  have hs1 : (1 : ℂ) ∈ Metric.closedBall (9 / 8 : ℂ) (1 / 8) := by
    rw [Metric.mem_closedBall, Complex.dist_eq,
      show (1 : ℂ) - 9 / 8 = ((-1 / 8 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    norm_num [abs_of_neg]
  -- Display 4.16 for each R between r = 1/8 and H = 5/8.
  have hbound : ∀ R ∈ Set.Ioo (1 / 8 : ℝ) (5 / 8),
      ‖deriv L 1 / L 1‖ ≤ 2 * R * Real.log (B / ‖L (9 / 8)‖) / (R - 1 / 8) ^ 2 := by
    intro R hR
    apply landau_lemma L hdiff (9 / 8) (1 / 8) R B (by norm_num) hR.1 _ _ 1 hs1
    · intro z hz
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz
      have hre := Complex.abs_re_le_norm (z - 9 / 8)
      have him := Complex.abs_im_le_norm (z - 9 / 8)
      have e1 : (z - 9 / 8).re = z.re - 9 / 8 := by simp
      have e2 : (z - 9 / 8).im = z.im := by simp
      rw [e1] at hre
      rw [e2] at him
      have hre' : 1 / 2 < z.re := by
        have := (abs_le.mp (hre.trans hz)).1; linarith [hR.2]
      have him' : |z.im| ≤ 5 / 8 := by linarith [hR.2]
      intro h0
      by_cases h1 : 1 ≤ z.re
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h1 h0
      · push_neg at h1
        have := hzeros z h0 (by linarith) h1 him'
        linarith
    · intro z hz
      apply strip_bound_4_19 χ hχ hq z
      exact Metric.closedBall_subset_closedBall hR.2.le hz
  -- R tends to H from below.
  set X := Real.log (B / ‖L (9 / 8)‖) with hX
  have hcont : ContinuousAt (fun R : ℝ => 2 * R * X / (R - 1 / 8) ^ 2) (5 / 8) := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have htend : Filter.Tendsto (fun R : ℝ => 2 * R * X / (R - 1 / 8) ^ 2)
      (nhdsWithin (5 / 8) (Set.Iio (5 / 8))) (nhds (5 * X)) := by
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (5 / 8 : ℝ)))
    have e : 2 * (5 / 8 : ℝ) * X / (5 / 8 - 1 / 8) ^ 2 = 5 * X := by ring
    rw [e] at h
    exact h
  have hev : ∀ᶠ R in nhdsWithin (5 / 8 : ℝ) (Set.Iio (5 / 8)),
      ‖deriv L 1 / L 1‖ ≤ 2 * R * X / (R - 1 / 8) ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 8 : ℝ) < 5 / 8 by norm_num)] with R hR
    exact hbound R hR
  have h417 : ‖deriv L 1 / L 1‖ ≤ 5 * X := ge_of_tendsto htend hev
  -- The Euler product lower bound and the constant c.
  have hXle : X ≤ Real.log (B / Z) := by
    apply Real.log_le_log (div_pos hB0 hL0)
    exact div_le_div_of_nonneg_left hB0.le hZ0 hZL
  have hsplit : Real.log (B / Z) =
      Real.log (2 * Real.sqrt 3 * (‖riemannZeta (9 / 8)‖ / ‖riemannZeta (9 / 4)‖)) +
        1 / 2 * Real.log M := by
    have hM0 : 0 < M := by linarith
    have e : B / Z = (2 * Real.sqrt 3 * (‖riemannZeta (9 / 8)‖ / ‖riemannZeta (9 / 4)‖)) *
        Real.sqrt M := by
      rw [hBdef, hZdef]; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_sqrt hM0.le]
    ring
  have hc := constant_c_le
  rw [hsplit] at hXle
  linarith

/-! ## The step from Lemma 4.2 to the bound in q, page 37 -/

end LeanLab.HelfgottMajor.Residue123
