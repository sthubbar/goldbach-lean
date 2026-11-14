module

public import Mathlib
public import LeanLab.PNTPort.DirichletZF.LogDerivStrip
public import LeanLab.PNTPort.DirichletZF.SiegelTaylor

/-!
Finite Turan interpolation from Vaughan Vol.3 pp.351 to 353.
AI wrote the Lean code. Codex task262. Goldbach is open.
Source https://personal.science.psu.edu/rcv4/Vol3/Vol3.pdf
The fixed radius interval gives a bound of thirty two to the M.
The telescoping circle kernel permits repeated roots.
-/

@[expose] public section

open Polynomial Finset
namespace LeanLab.Linnik.Decomp1532b2
/-- Vaughan Vol.3 p.351 Chebyshev step, coefficient form. -/
theorem exists_large_polynomial_value (p : ℝ[X]) (n : ℕ)
    (hd : p.degree ≤ n) (hc : 0 < p.coeff n) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, p.coeff n / 2 ^ (n - 1) ≤ |p.eval x| := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-1 : ℝ) 1).Nonempty from ⟨0, by constructor <;> norm_num⟩)
    p.continuous.abs.continuousOn
  refine ⟨x, hx, ?_⟩
  by_contra h
  have hh : |p.eval x| < p.coeff n / 2 ^ (n - 1) := lt_of_not_ge h
  let B : ℝ := (|p.eval x| + p.coeff n / 2 ^ (n - 1)) / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : |p.eval x| ≤ B := by dsimp [B]; linarith
  have hBc : B < p.coeff n / 2 ^ (n - 1) := by dsimp [B]; linarith
  have hbound : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |((B⁻¹) • p).eval y| ≤ 1 := by
    intro y hy
    simp only [eval_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hB]
    apply (inv_mul_le_one₀ hB).2
    exact (hmax hy).trans hAB
  have hd' : ((B⁻¹) • p).degree ≤ n := (degree_smul_le _ _).trans hd
  have hcoef := Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one hd' hbound
  simp only [coeff_smul, smul_eq_mul] at hcoef
  have hcoef' : p.coeff n ≤ B * 2 ^ (n - 1) := by
    have ht : p.coeff n / B ≤ 2 ^ (n - 1) := by
      simpa only [div_eq_inv_mul] using hcoef
    simpa only [mul_comm] using (div_le_iff₀ hB).mp ht
  have hsmall : B * 2 ^ (n - 1) < p.coeff n := (lt_div_iff₀ (by positivity)).mp hBc
  linarith

/-- Vaughan Vol.3 p.351 radius choice on a fixed interval. -/
theorem exists_radius_product_gap {n : ℕ} (a : Fin n → ℝ) :
    ∃ r ∈ Set.Icc (1 / 2 : ℝ) 1, (1 / 8 : ℝ) ^ n ≤ ∏ i, |r - a i| := by
  let p : ℝ[X] := ∏ i, (X - C (a i))
  let l : ℝ[X] := C (1 / 4) * X + C (3 / 4)
  let q : ℝ[X] := p.comp l
  have hp : p.Monic := monic_prod_X_sub_C a univ
  have hpn : p.natDegree = n := by
    dsimp [p]
    rw [natDegree_prod _ _ (fun i _ => (monic_X_sub_C (a i)).ne_zero)]
    simp
  have hln : l.natDegree = 1 := natDegree_linear (by norm_num)
  have hqn : q.natDegree = n := by simp only [q, natDegree_comp, hpn, hln, mul_one]
  have hqc : q.coeff n = (1 / 4 : ℝ) ^ n := by
    calc
      q.coeff n = q.leadingCoeff := by rw [leadingCoeff, hqn]
      _ = (1 / 4 : ℝ) ^ n := by
        dsimp [q]
        rw [leadingCoeff_comp (by rw [hln]; omega), hp.leadingCoeff, one_mul, hpn]
        rw [show l.leadingCoeff = (1 / 4 : ℝ) from leadingCoeff_linear (by norm_num)]
  obtain ⟨x, hx, hval⟩ := exists_large_polynomial_value q n
    (degree_le_of_natDegree_le (by omega)) (by rw [hqc]; positivity)
  refine ⟨x / 4 + 3 / 4, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  have he : |q.eval x| = ∏ i, |x / 4 + 3 / 4 - a i| := by
    simp only [q, p, l, eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_prod,
      eval_sub, abs_prod]
    congr 1
    ext i
    congr 1
    ring
  rw [hqc, he] at hval
  refine le_trans ?_ hval
  have hp2 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (1 / 8 : ℝ) ^ n = (1 / 4 : ℝ) ^ n / 2 ^ n := by rw [← div_pow]; congr 1; norm_num
    _ ≤ (1 / 4 : ℝ) ^ n / 2 ^ (n - 1) := div_le_div_of_nonneg_left (by positivity) (by positivity) hp2

/-- Vaughan Vol.3 pp.351 and 352, every subproduct retains the radius gap. -/
theorem radius_subproduct_gap {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) {r D : ℝ} (hr : r ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hgap : D ≤ ∏ i, |r - ‖z i‖|) (s : Finset (Fin n)) :
    D ≤ ∏ i ∈ s, |r - ‖z i‖| := by
  apply hgap.trans
  exact prod_le_prod_of_subset_of_le_one₀ (subset_univ s)
    (fun i _ => abs_nonneg _) (fun i _ _ => abs_le.mpr ⟨by linarith [hz i, hr.1], by linarith [norm_nonneg (z i), hr.2]⟩)

/-- Vaughan Vol.3 p.352 denominator estimate on the chosen circle. -/
theorem circle_subproduct_gap {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) {r D : ℝ} (hr : r ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hgap : D ≤ ∏ i, |r - ‖z i‖|) (s : Finset (Fin n))
    (w : ℂ) (hw : ‖w‖ = r) :
    D ≤ ‖∏ i ∈ s, (w - z i)‖ := by
  rw [norm_prod]
  apply (radius_subproduct_gap z hz hr hgap s).trans
  exact prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by
    rw [← hw]
    exact abs_norm_sub_norm_le w (z i))

/-- Vaughan Vol.3 p.351 the selected outer root set is nonempty. -/
theorem radius_outer_nonempty {n : ℕ} (z : Fin n → ℂ)
    (hunit : ∃ i, ‖z i‖ = 1) {r D : ℝ} (hr : r ≤ 1) (hD : 0 < D)
    (hgap : D ≤ ∏ i, |r - ‖z i‖|) :
    (univ.filter (fun i => r < ‖z i‖)).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := hunit
  have hne : r ≠ 1 := by
    intro he
    have hzero : (∏ j, |r - ‖z j‖|) = 0 := prod_eq_zero (mem_univ i) (by rw [he, hi]; simp)
    rw [hzero] at hgap
    linarith
  exact ⟨i, mem_filter.mpr ⟨mem_univ i, by rw [hi]; exact lt_of_le_of_ne hr hne⟩⟩

/-- Vaughan Vol.3 p.352 excludes every root from the integration circle. -/
theorem radius_ne_root_norm {n : ℕ} (z : Fin n → ℂ) {r D : ℝ} (hD : 0 < D)
    (hgap : D ≤ ∏ i, |r - ‖z i‖|) (i : Fin n) : r ≠ ‖z i‖ := by
  intro he
  have hzero : (∏ j, |r - ‖z j‖|) = 0 := prod_eq_zero (mem_univ i) (by rw [he]; simp)
  rw [hzero] at hgap
  linarith

/-- Vaughan Vol.3 p.353 coefficient majorization for a root product. -/
theorem root_product_coeff_sum {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) :
    (∑ j ∈ range (s.card + 1), ‖(∏ i ∈ s, (X - C (z i))).coeff j‖) ≤ (2 : ℝ) ^ s.card := by
  classical
  let p : ℂ[X] := ∏ i ∈ s, (X - C (z i))
  have hpn : p.natDegree = s.card := by
    dsimp [p]
    rw [natDegree_prod _ _ (fun i _ => (monic_X_sub_C (z i)).ne_zero)]
    simp
  have hpm : p.mahlerMeasure = 1 := by
    dsimp [p]
    clear hpn
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [prod_insert ha, mahlerMeasure_mul, mahlerMeasure_X_sub_C,
        max_eq_left (hz a (mem_insert_self a s))]
      rw [ih (fun i hi => hz i (mem_insert_of_mem hi))]
      simp
  calc
    _ ≤ ∑ j ∈ range (s.card + 1), ((s.card.choose j : ℕ) : ℝ) := by
      apply sum_le_sum
      intro j _
      simpa only [hpn, hpm, mul_one] using p.norm_coeff_le_choose_mul_mahlerMeasure j
    _ = (2 : ℝ) ^ s.card := by exact_mod_cast Nat.sum_range_choose s.card
end LeanLab.Linnik.Decomp1532b2
open Polynomial Finset Metric Complex
namespace LeanLab.Linnik.Decomp1532b2

/-- Vaughan Vol.3 p.352 the Newton root products. -/
noncomputable def rootPrefix (z : ℕ → ℂ) (k : ℕ) : ℂ[X] :=
  ∏ j ∈ range k, (X - C (z j))

/-- Vaughan Vol.3 p.352 Newton product recursion. -/
theorem rootPrefix_succ (z : ℕ → ℂ) (k : ℕ) :
    rootPrefix z (k + 1) = rootPrefix z k * (X - C (z k)) := by
  exact prod_range_succ _ _

/-- Vaughan Vol.3 p.352 telescoping divided difference kernel. -/
theorem rootPrefix_kernel (z : ℕ → ℂ) (n : ℕ) (u w : ℂ)
    (hu : ∀ j < n, u ≠ z j) :
    (u - w) * (∑ k ∈ range n, (rootPrefix z k).eval w / (rootPrefix z (k + 1)).eval u) =
      1 - (rootPrefix z n).eval w / (rootPrefix z n).eval u := by
  have hne (k : ℕ) (hk : k ≤ n) : (rootPrefix z k).eval u ≠ 0 := by
    simp only [rootPrefix, eval_prod, eval_sub, eval_X, eval_C]
    exact prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hu j (lt_of_lt_of_le (mem_range.mp hj) hk)))
  induction n with
  | zero => simp [rootPrefix]
  | succ n ih =>
    have hi := ih (fun j hj => hu j (by omega)) (fun k hk => hne k (by omega))
    rw [sum_range_succ, mul_add, hi, rootPrefix_succ]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    have hn := hne n (by omega)
    have hun : u - z n ≠ 0 := sub_ne_zero.mpr (hu n (by omega))
    field_simp
    ring

/-- Vaughan Vol.3 p.352 a root specialization of the kernel identity. -/
theorem rootPrefix_kernel_at_root (z : ℕ → ℂ) (n : ℕ) (u : ℂ)
    (hu : ∀ j < n, u ≠ z j) (j : ℕ) (hj : j < n) :
    (∑ k ∈ range n, (rootPrefix z k).eval (z j) / (rootPrefix z (k + 1)).eval u) =
      (u - z j)⁻¹ := by
  have hz : (rootPrefix z n).eval (z j) = 0 := by
    simp only [rootPrefix, eval_prod, eval_sub, eval_X, eval_C]
    exact prod_eq_zero (mem_range.mpr hj) (sub_self _)
  have h := rootPrefix_kernel z n u (z j) hu
  rw [hz, zero_div, sub_zero] at h
  rw [← one_div]
  exact (eq_div_iff (sub_ne_zero.mpr (hu j hj))).2 (by simpa [mul_comm] using h)

/-- Gallagher p.334 power kernel, finite partial fraction identity. -/
theorem power_kernel_partial_fraction (u w : ℂ) (hu : u ≠ 0) (huw : u ≠ w) (M : ℕ) :
    w ^ (M + 1) / (u ^ (M + 1) * (u - w)) =
      (u - w)⁻¹ - ∑ k ∈ range (M + 1), w ^ k / u ^ (k + 1) := by
  induction M with
  | zero => simp only [zero_add, pow_one, sum_range_one, pow_zero, one_div]; field_simp; ring
  | succ M ih =>
    rw [sum_range_succ, ← sub_sub, ← ih]
    rw [pow_succ (w), pow_succ (u)]
    field_simp
    ring

/-- Vaughan p.352 the Cauchy kernel vanishes outside the disc. -/
theorem circle_integral_inv_outside (w : ℂ) {r : ℝ} (hr : 0 ≤ r) (hw : r < ‖w‖) :
    (∮ u in C(0, r), (u - w)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
  · apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro u hu
    apply sub_ne_zero.mpr
    intro he
    change u = w at he
    subst u
    simp only [mem_closedBall, dist_zero_right] at hu
    linarith
  · intro u hu
    apply DifferentiableAt.inv (differentiableAt_id.sub_const w)
    apply sub_ne_zero.mpr
    intro he
    change u = w at he
    subst u
    simp only [Set.mem_sdiff, mem_ball, dist_zero_right, Set.mem_empty_iff_false, not_false_eq_true, and_true] at hu
    linarith

/-- Vaughan Vol.3 p.352 elementary circle moments at zero. -/
theorem circle_inverse_power (k : ℕ) {r : ℝ} (hr : 0 < r) :
    (∮ u in C(0, r), (u ^ (k + 1))⁻¹) = if k = 0 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa using circleIntegral.integral_sub_inv_of_mem_ball
      (show (0 : ℂ) ∈ ball 0 r by simpa)
  · rw [ite_eq_right hk]
    convert circleIntegral.integral_sub_zpow_of_ne
      (show (-((k + 1 : ℕ) : ℤ)) ≠ -1 by omega) (0 : ℂ) (0 : ℂ) r using 1
    congr 1
    ext u
    simp only [sub_zero, zpow_neg, zpow_natCast]

/-- Vaughan Vol.3 p.352 circle integrability of the zero pole moments. -/
theorem circleIntegrable_inverse_power (k : ℕ) {r : ℝ} (hr : 0 < r) :
    CircleIntegrable (fun u : ℂ => (u ^ (k + 1))⁻¹) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  apply ContinuousOn.inv₀ (continuousOn_id.pow _)
  intro u hu
  apply pow_ne_zero
  intro he
  change u = 0 at he
  subst u
  have hzero : (0 : ℝ) = r := by simpa using hu
  linarith

/-- Vaughan Vol.3 p.352 the normalized power kernel selects the outside roots. -/
theorem circle_power_kernel (w : ℂ) (M : ℕ) {r : ℝ} (hr : 0 < r) (hw : ‖w‖ ≠ r) :
    -w ^ (M + 1) * ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ u in C(0, r), (u ^ (M + 1) * (u - w))⁻¹) =
        if r < ‖w‖ then 1 else 0 := by
  have huw : w ∉ sphere (0 : ℂ) |r| := by simpa [abs_of_pos hr, mem_sphere_iff_norm] using hw
  have hi : CircleIntegrable (fun u : ℂ => (u - w)⁻¹) 0 r :=
    circleIntegrable_sub_inv_iff.mpr (Or.inr huw)
  have hs : ∀ k ∈ range (M + 1),
      CircleIntegrable (fun u : ℂ => w ^ k / u ^ (k + 1)) 0 r := by
    intro k _
    apply ContinuousOn.circleIntegrable hr.le
    apply ContinuousOn.div continuousOn_const (continuousOn_id.pow _)
    intro u hu
    apply pow_ne_zero
    intro he
    change u = 0 at he
    subst u
    have hzero : (0 : ℝ) = r := by simpa using hu
    linarith
  have halg : w ^ (M + 1) * (∮ u in C(0, r), (u ^ (M + 1) * (u - w))⁻¹) =
      (∮ u in C(0, r), (u - w)⁻¹) - 2 * Real.pi * Complex.I := by
    rw [← circleIntegral.integral_const_mul]
    have he : (∮ u in C(0, r), w ^ (M + 1) * (u ^ (M + 1) * (u - w))⁻¹) =
        ∮ u in C(0, r), (u - w)⁻¹ - ∑ k ∈ range (M + 1), w ^ k / u ^ (k + 1) := by
      apply circleIntegral.integral_congr hr.le
      intro u hu
      have hu0 : u ≠ 0 := by
        intro he
        subst u
        have hzero : (0 : ℝ) = r := by simpa using hu
        linarith
      have huw' : u ≠ w := by intro he; subst u; exact huw (by simpa [abs_of_pos hr] using hu)
      simpa only [div_eq_mul_inv] using power_kernel_partial_fraction u w hu0 huw' M
    rw [he, circleIntegral.integral_sub hi (CircleIntegrable.fun_sum (range (M + 1)) hs),
      circleIntegral.integral_fun_sum hs]
    congr 1
    simp_rw [div_eq_mul_inv, circleIntegral.integral_const_mul, circle_inverse_power _ hr]
    simp
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  by_cases hout : r < ‖w‖
  · rw [circle_integral_inv_outside w hr.le hout] at halg
    rw [ite_eq_left hout]
    calc
      _ = -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (w ^ (M + 1) * ∮ u in C(0, r), (u ^ (M + 1) * (u - w))⁻¹) := by ring
      _ = 1 := by rw [halg]; field_simp; ring
  · have hin : ‖w‖ < r := lt_of_le_of_ne (le_of_not_gt hout) hw
    rw [circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hin)] at halg
    rw [ite_eq_right hout]
    calc
      _ = -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (w ^ (M + 1) * ∮ u in C(0, r), (u ^ (M + 1) * (u - w))⁻¹) := by ring
      _ = 0 := by rw [halg]; ring

/-- Vaughan Vol.3 p.352 the Newton prefix has its expected degree. -/
theorem rootPrefix_natDegree (z : ℕ → ℂ) (k : ℕ) : (rootPrefix z k).natDegree = k := by
  dsimp [rootPrefix]
  rw [natDegree_prod _ _ (fun j _ => (monic_X_sub_C (z j)).ne_zero)]
  simp

/-- Vaughan Vol.3 p.353 Newton coefficients give a polynomial of degree below n. -/
theorem newton_sum_natDegree_lt (z c : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ range n, C (c k) * rootPrefix z k).natDegree < n := by
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le (range n) (fun k => C (c k) * rootPrefix z k) ?_) (show n - 1 < n by omega)
  intro k hk
  exact (natDegree_C_mul_le _ _).trans (by rw [rootPrefix_natDegree]; have := mem_range.mp hk; omega)
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open Polynomial Finset Metric Complex
/-- Vaughan Vol.3 p.353 coefficient bound for a Newton sum. -/
theorem newton_sum_coeff_norm (z c : ℕ → ℂ) (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ j < n, ‖z j‖ ≤ 1) (hc : ∀ k < n, ‖c k‖ ≤ L) :
    (∑ j ∈ range n, ‖(∑ k ∈ range n, C (c k) * rootPrefix z k).coeff j‖) ≤
      L * 2 ^ n := by
  calc
    _ ≤ ∑ j ∈ range n, ∑ k ∈ range n, ‖c k‖ * ‖(rootPrefix z k).coeff j‖ := by
      apply sum_le_sum
      intro j hj
      simpa only [finsetSum_coeff, coeff_C_mul, norm_mul] using
        norm_sum_le (range n) (fun k => (C (c k) * rootPrefix z k).coeff j)
    _ = ∑ k ∈ range n, ‖c k‖ * (∑ j ∈ range n, ‖(rootPrefix z k).coeff j‖) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ ∑ k ∈ range n, L * 2 ^ k := by
      apply sum_le_sum
      intro k hk
      have hk' := mem_range.mp hk
      apply mul_le_mul (hc k hk') _ (sum_nonneg fun _ _ => norm_nonneg _) hL
      have hs : (∑ j ∈ range n, ‖(rootPrefix z k).coeff j‖) =
          ∑ j ∈ range (k + 1), ‖(rootPrefix z k).coeff j‖ := by
        symm
        apply sum_subset (range_mono (by omega))
        intro j hj hj'
        rw [coeff_eq_zero_of_natDegree_lt (by rw [rootPrefix_natDegree]; simp only [mem_range] at hj'; omega), norm_zero]
      rw [hs]
      simpa only [rootPrefix, card_range] using root_product_coeff_sum (range k) z
        (fun j hj => hz j (lt_trans (mem_range.mp hj) hk'))
    _ = L * (2 ^ n - 1) := by rw [← mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; ring
    _ ≤ L * 2 ^ n := by nlinarith

/-- Vaughan Vol.3 p.352 the contour Newton coefficient. -/
noncomputable def circleNewtonCoefficient (z : ℕ → ℂ) (M : ℕ) (r : ℝ) (k : ℕ) : ℂ :=
  -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ u in C(0, r), (u ^ (M + 1) * (rootPrefix z (k + 1)).eval u)⁻¹

/-- Vaughan Vol.3 p.352 contour integrability for a root prefix. -/
theorem circleIntegrable_prefix_kernel (z : ℕ → ℂ) (M k : ℕ) {r : ℝ}
    (hr : 0 < r) (hz : ∀ j < k, ‖z j‖ ≠ r) :
    CircleIntegrable (fun u : ℂ => (u ^ (M + 1) * (rootPrefix z k).eval u)⁻¹) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  apply ContinuousOn.inv₀ ((continuousOn_id.pow _).mul (rootPrefix z k).continuous.continuousOn)
  intro u hu
  apply mul_ne_zero
  · apply pow_ne_zero
    intro he
    change u = 0 at he
    subst u
    have hzero : (0 : ℝ) = r := by simpa using hu
    linarith
  · simp only [rootPrefix, eval_prod, eval_sub, eval_X, eval_C]
    apply prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro he
    have he' : u = z j := he
    subst u
    exact hz j (mem_range.mp hj) (by simpa using hu)

/-- Vaughan Vol.3 p.352 the contour Newton sum interpolates the outside selector. -/
theorem circle_newton_interpolates (z : ℕ → ℂ) (M n : ℕ) {r : ℝ}
    (hr : 0 < r) (hz : ∀ j < n, ‖z j‖ ≠ r) (j : ℕ) (hj : j < n) :
    z j ^ (M + 1) * (∑ k ∈ range n, circleNewtonCoefficient z M r k * (rootPrefix z k).eval (z j)) =
      if r < ‖z j‖ then 1 else 0 := by
  have hs : ∀ k ∈ range n, CircleIntegrable
      (fun u : ℂ => (rootPrefix z k).eval (z j) *
        (u ^ (M + 1) * (rootPrefix z (k + 1)).eval u)⁻¹) 0 r := by
    intro k hk
    have hi := circleIntegrable_prefix_kernel z M (k + 1) hr (fun i hi => hz i (by have := mem_range.mp hk; omega))
    change IntervalIntegrable _ _ _ _
    exact IntervalIntegrable.const_mul hi _
  have he : (∑ k ∈ range n, circleNewtonCoefficient z M r k * (rootPrefix z k).eval (z j)) =
      -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ u in C(0, r), (u ^ (M + 1) * (u - z j))⁻¹ := by
    calc
      _ = -(2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∑ k ∈ range n, ∮ u in C(0, r), (rootPrefix z k).eval (z j) *
            (u ^ (M + 1) * (rootPrefix z (k + 1)).eval u)⁻¹ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        rw [circleIntegral.integral_const_mul]
        dsimp [circleNewtonCoefficient]
        ring
      _ = _ := by
        rw [← circleIntegral.integral_fun_sum hs]
        congr 1
        apply circleIntegral.integral_congr hr.le
        intro u hu
        have hun : ∀ i < n, u ≠ z i := by
          intro i hi he
          subst u
          exact hz i hi (by simpa using hu)
        calc
          _ = (u ^ (M + 1))⁻¹ *
              ∑ k ∈ range n, (rootPrefix z k).eval (z j) / (rootPrefix z (k + 1)).eval u := by
            rw [mul_sum]
            apply sum_congr rfl
            intro k hk
            simp only [mul_inv, div_eq_mul_inv]
            ring
          _ = _ := by rw [rootPrefix_kernel_at_root z n u hun j hj]; simp only [mul_inv]
  rw [he]
  convert circle_power_kernel (z j) M hr (hz j hj) using 1; ring

/-- Vaughan Vol.3 p.352 the selected radius bounds every prefix denominator. -/
theorem prefix_circle_norm_ge (z : ℕ → ℂ) (n k : ℕ) {r D : ℝ}
    (hr : r ∈ Set.Icc (1 / 2 : ℝ) 1) (hz : ∀ j < n, ‖z j‖ ≤ 1)
    (hgap : D ≤ ∏ j ∈ range n, |r - ‖z j‖|) (hk : k ≤ n)
    (u : ℂ) (hu : ‖u‖ = r) :
    D ≤ ‖(rootPrefix z k).eval u‖ := by
  simp only [rootPrefix, eval_prod, eval_sub, eval_X, eval_C, norm_prod]
  calc
    D ≤ ∏ j ∈ range k, |r - ‖z j‖| := by
      apply hgap.trans
      exact prod_le_prod_of_subset_of_le_one₀ (range_mono hk)
        (fun j _ => abs_nonneg _) (fun j hj _ => abs_le.mpr
          ⟨by linarith [hz j (mem_range.mp hj), hr.1], by linarith [norm_nonneg (z j), hr.2]⟩)
    _ ≤ _ := prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => by
      rw [← hu]; exact abs_norm_sub_norm_le u (z j))

/-- Vaughan Vol.3 p.352 uniform contour coefficient estimate. -/
theorem circleNewtonCoefficient_norm_le (z : ℕ → ℂ) (M k : ℕ) {r D : ℝ}
    (hr : (1 / 2 : ℝ) ≤ r) (hD : 0 < D)
    (hgap : ∀ u : ℂ, ‖u‖ = r → D ≤ ‖(rootPrefix z (k + 1)).eval u‖) :
    ‖circleNewtonCoefficient z M r k‖ ≤ 2 ^ M / D := by
  have hr0 : 0 < r := by linarith
  have hb : ∀ u ∈ sphere (0 : ℂ) r,
      ‖(u ^ (M + 1) * (rootPrefix z (k + 1)).eval u)⁻¹‖ ≤
        1 / (r ^ (M + 1) * D) := by
    intro u hu
    have hun : ‖u‖ = r := by simpa using hu
    rw [norm_inv, norm_mul, norm_pow, hun]
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (hgap u hun) (by positivity)
  have hc := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr0.le hb
  have he : ‖circleNewtonCoefficient z M r k‖ ≤ r * (1 / (r ^ (M + 1) * D)) := by
    simpa only [circleNewtonCoefficient, neg_mul, norm_neg, smul_eq_mul] using hc
  have hp : 1 ≤ (2 : ℝ) ^ M * r ^ M := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hr M)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) M)
    simpa only [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow] using h
  calc
    _ ≤ r * (1 / (r ^ (M + 1) * D)) := he
    _ = (1 / r ^ M) / D := by rw [pow_succ]; field_simp
    _ ≤ 2 ^ M / D := div_le_div_of_nonneg_right ((div_le_iff₀ (by positivity)).2 (by nlinarith)) hD.le

/-- Vaughan Vol.3 pp.351 to 353, finite Turan selector with repeated roots allowed.
The fixed interval radius gives the stronger coefficient bound thirty two to the M. -/
theorem turan_interpolant_finite {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hunit : ∃ i, ‖z i‖ = 1) :
    ∃ J : Finset (Fin n), J.Nonempty ∧ ∃ b : Fin n → ℂ,
      (∀ i, z i ^ (M + 1) * (∑ j, b j * z i ^ j.val) = if i ∈ J then 1 else 0) ∧
      (∑ j, ‖b j‖) ≤ (50 : ℝ) ^ M := by
  classical
  obtain ⟨r, hr, hgap⟩ := exists_radius_product_gap (fun i => ‖z i‖)
  have hr0 : 0 < r := by linarith [hr.1]
  let w : ℕ → ℂ := fun j => if hj : j < n then z ⟨j, hj⟩ else 0
  have hw (j : ℕ) (hj : j < n) : w j = z ⟨j, hj⟩ := dite_eq_left hj
  have hwz : ∀ j < n, ‖w j‖ ≤ 1 := fun j hj => by rw [hw j hj]; exact hz _
  have hgap' : (1 / 8 : ℝ) ^ n ≤ ∏ j ∈ range n, |r - ‖w j‖| := by
    rw [prod_range]
    simpa only [w, Fin.isLt, dite_true] using hgap
  have hwcircle : ∀ j < n, ‖w j‖ ≠ r := by
    intro j hj he
    have he0 : (∏ i ∈ range n, |r - ‖w i‖|) = 0 :=
      prod_eq_zero (mem_range.mpr hj) (by rw [he]; simp)
    rw [he0] at hgap'
    exact (not_le_of_gt (by positivity : (0 : ℝ) < (1 / 8 : ℝ) ^ n)) hgap'
  let c : ℕ → ℂ := circleNewtonCoefficient w M r
  let P : ℂ[X] := ∑ k ∈ range n, C (c k) * rootPrefix w k
  have hPn : P.natDegree < n := newton_sum_natDegree_lt w c hn
  have hc : ∀ k < n, ‖c k‖ ≤ (2 : ℝ) ^ M / (1 / 8 : ℝ) ^ n := by
    intro k hk
    exact circleNewtonCoefficient_norm_le w M k hr.1 (by positivity)
      (fun u hu => prefix_circle_norm_ge w n (k + 1) hr hwz hgap' (by omega) u hu)
  let J : Finset (Fin n) := univ.filter (fun i => r < ‖z i‖)
  refine ⟨J, radius_outer_nonempty z hunit hr.2 (by positivity) hgap, fun j => P.coeff j.val, ?_, ?_⟩
  · intro i
    have hp : (∑ j : Fin n, P.coeff j.val * z i ^ j.val) = P.eval (z i) := by
      rw [← sum_range (fun j : ℕ => P.coeff j * z i ^ j)]
      exact (eval_eq_sum_range' hPn (z i)).symm
    rw [hp]
    have hi := circle_newton_interpolates w M n hr0 hwcircle i.val i.isLt
    rw [hw i.val i.isLt] at hi
    simpa only [J, mem_filter, mem_univ, true_and, P, eval_finsetSum, eval_mul, eval_C] using hi
  · have hb := newton_sum_coeff_norm w c n (by positivity : (0 : ℝ) ≤ 2 ^ M / (1 / 8 : ℝ) ^ n) hwz hc
    change (∑ j : Fin n, ‖P.coeff j.val‖) ≤ 50 ^ M
    rw [← sum_range (fun j : ℕ => ‖P.coeff j‖)]
    calc
      _ ≤ (2 : ℝ) ^ M / (1 / 8 : ℝ) ^ n * 2 ^ n := hb
      _ = (2 : ℝ) ^ M * 16 ^ n := by
        rw [div_pow, one_pow, div_div_eq_mul_div, div_one, mul_assoc, ← mul_pow]
        norm_num
      _ ≤ (2 : ℝ) ^ M * 16 ^ M := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hnM) (by positivity)
      _ = (32 : ℝ) ^ M := by rw [← mul_pow]; norm_num
      _ ≤ (50 : ℝ) ^ M := pow_le_pow_left₀ (by norm_num) (by norm_num) M

end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2

/-- Gallagher 1970 p.334 display 22, the detector smoothing kernel. -/
noncomputable def poissonKernel (k : ℕ) (u : ℝ) : ℝ := Real.exp (-u) * u ^ k / k.factorial

/-- Gallagher p.335 the smoothing kernel is nonnegative. -/
theorem poissonKernel_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ poissonKernel k u := by
  unfold poissonKernel
  positivity

/-- Gallagher p.335 the smoothing kernel is at most one. -/
theorem poissonKernel_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : poissonKernel k u ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp u hu k) (Real.exp_pos (-u)).le
  simpa only [poissonKernel, mul_div_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

/-- Gallagher p.335 the derivative recursion for the smoothing kernel. -/
theorem hasDerivAt_poissonKernel_succ (k : ℕ) (u : ℝ) :
    HasDerivAt (poissonKernel (k + 1)) (poissonKernel k u - poissonKernel (k + 1) u) u := by
  have hf := (((hasDerivAt_id u).neg.exp).mul ((hasDerivAt_id u).pow (k + 1))).div_const
    (((k + 1).factorial : ℕ) : ℝ)
  convert hf using 1
  · rfl
  · dsimp [poissonKernel]
    rw [Nat.factorial_succ]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Gallagher p.335 the derivative of every kernel is bounded in absolute value by one. -/
theorem abs_deriv_poissonKernel_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |deriv (poissonKernel k) u| ≤ 1 := by
  cases k with
  | zero =>
    have hd : HasDerivAt (poissonKernel 0) (-Real.exp (-u)) u := by
      convert (hasDerivAt_id u).neg.exp using 1
      · ext x; simp [poissonKernel]
      · simp
    rw [hd.deriv, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  | succ k =>
    rw [(hasDerivAt_poissonKernel_succ k u).deriv]
    exact abs_le.mpr ⟨by linarith [poissonKernel_nonneg k hu, poissonKernel_le_one (k + 1) hu],
      by linarith [poissonKernel_le_one k hu, poissonKernel_nonneg (k + 1) hu]⟩

/-- Gallagher p.335 exponential tilting gives both tails of the smoothing kernel. -/
theorem poissonKernel_tilt_bound (k : ℕ) {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) :
    poissonKernel k u ≤ (a ^ k)⁻¹ * Real.exp ((a - 1) * u) := by
  have h := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) k
  have hp : 0 < a ^ k := pow_pos ha _
  calc
    _ = Real.exp (-u) * ((a * u) ^ k / k.factorial) / a ^ k := by
      unfold poissonKernel
      rw [mul_pow]
      field_simp
    _ ≤ Real.exp (-u) * Real.exp (a * u) / a ^ k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le) hp.le
    _ = _ := by
      rw [← Real.exp_add, div_eq_mul_inv, mul_comm]
      congr 2
      ring
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.335 the lower tail cutoff can be chosen uniformly in k. -/
theorem poissonKernel_small_tail (D : ℝ) (hD : 0 < D) :
    ∃ B₁ : ℝ, 0 < B₁ ∧ ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ B₁ * k →
      poissonKernel k u ≤ (1 / (2 * D)) ^ k := by
  let a : ℝ := 2 * D * Real.exp 1
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨1 / a, by positivity, ?_⟩
  intro k u hu hlu
  have hau : a * u ≤ k := by
    calc
      _ ≤ a * ((1 / a) * k) := mul_le_mul_of_nonneg_left hlu ha.le
      _ = k := by field_simp
  have hex : (a - 1) * u ≤ k := by nlinarith
  calc
    _ ≤ (a ^ k)⁻¹ * Real.exp ((a - 1) * u) := poissonKernel_tilt_bound k hu ha
    _ ≤ (a ^ k)⁻¹ * Real.exp (k : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (by positivity)
    _ = (Real.exp 1 / a) ^ k := by rw [← mul_one (k : ℝ), Real.exp_nat_mul, div_pow]; ring
    _ = (1 / (2 * D)) ^ k := by congr 1; dsimp [a]; field_simp

/-- Gallagher p.335 the upper tail cutoff leaves exponential decay in u. -/
theorem poissonKernel_large_tail (D : ℝ) (hD : 0 < D) :
    ∃ B₂ : ℝ, 0 < B₂ ∧ ∀ (k : ℕ) (u : ℝ), 0 ≤ u → B₂ * k ≤ u →
      poissonKernel k u ≤ (1 / (2 * D)) ^ k * Real.exp (-u / 2) := by
  let B₂ : ℝ := 4 * (max 0 (Real.log (8 * D)) + 1)
  have hB : 0 < B₂ := by dsimp [B₂]; positivity
  refine ⟨B₂, hB, ?_⟩
  intro k u hu hlu
  have hlog : (k : ℝ) * Real.log (8 * D) ≤ u / 4 := by
    have h := mul_le_mul_of_nonneg_left (le_max_right 0 (Real.log (8 * D))) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    dsimp [B₂] at hlu
    nlinarith
  have hdec : Real.exp (-u / 4) ≤ (1 / (8 * D)) ^ k := by
    calc
      _ ≤ Real.exp (-(k : ℝ) * Real.log (8 * D)) := Real.exp_le_exp.mpr (by linarith)
      _ = (1 / (8 * D)) ^ k := by
        rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity), one_div, inv_pow]
  calc
    _ ≤ ((1 / 4 : ℝ) ^ k)⁻¹ * Real.exp (((1 / 4 : ℝ) - 1) * u) :=
      poissonKernel_tilt_bound k hu (by norm_num)
    _ = (4 : ℝ) ^ k * Real.exp (-u / 4) * Real.exp (-u / 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      · rw [← inv_pow]; norm_num
      · congr 1; ring
    _ ≤ (4 : ℝ) ^ k * (1 / (8 * D)) ^ k * Real.exp (-u / 2) := by gcongr
    _ = _ := by rw [← mul_pow]; congr 2; field_simp; ring
end LeanLab.Linnik.Decomp1532b2

open Finset MeasureTheory
namespace LeanLab.Linnik.Decomp1532b2

/-- Gallagher 1970 p.335 partial summation for coefficients supported above x. -/
theorem supported_partial_summation (a : ℕ → ℂ) (f : ℝ → ℂ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (ha : ∀ n ≤ ⌊x⌋₊, a n = 0)
    (hf : ∀ t ∈ Set.Icc x y, DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Set.Icc x y)) :
    (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, f n * a n) =
      f y * (∑ n ∈ Icc 0 ⌊y⌋₊, a n) -
        ∫ t in Set.Ioc x y, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n := by
  have hzero : (∑ n ∈ Icc 0 ⌊x⌋₊, a n) = 0 := sum_eq_zero
    (fun n hn => ha n (mem_Icc.mp hn).2)
  simpa only [hzero, mul_zero, sub_zero] using
    sum_mul_eq_sub_sub_integral_mul a hx hxy hf hfi

/-- Gallagher 1970 p.335 the weighted sum lower bound forces detector L1 mass.
The input H is the remaining analytic weighted sum estimate. -/
theorem detector_partial_summation_lower (a : ℕ → ℂ) (f : ℝ → ℂ) {x y E D H : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ha : ∀ n ≤ ⌊x⌋₊, a n = 0)
    (hf : ∀ t ∈ Set.Icc x y, DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Set.Icc x y))
    (hfy : ‖f y‖ ≤ E)
    (hfd : ∀ t ∈ Set.Ioc x y, ‖deriv f t‖ ≤ D / t)
    (hSi : IntegrableOn (fun t : ℝ => ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t) (Set.Ioc x y))
    (hH : H ≤ ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, f n * a n‖) :
    H ≤ E * ‖∑ n ∈ Icc 0 ⌊y⌋₊, a n‖ +
      D * ∫ t in Set.Ioc x y, ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t := by
  have hprod : IntegrableOn (fun t : ℝ => deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n) (Set.Ioc x y) :=
    (integrableOn_mul_sum_Icc a hx.le hfi).mono_set Set.Ioc_subset_Icc_self
  have hint : ‖∫ t in Set.Ioc x y, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ ≤
      D * ∫ t in Set.Ioc x y, ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t := by
    calc
      _ ≤ ∫ t in Set.Ioc x y, ‖deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc x y, D * (‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t) := by
        apply integral_mono_ae hprod.norm (hSi.const_mul D)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [norm_mul]
        calc
          _ ≤ (D / t) * ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ :=
            mul_le_mul_of_nonneg_right (hfd t ht) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := integral_const_mul D _
  calc
    H ≤ ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, f n * a n‖ := hH
    _ = ‖f y * (∑ n ∈ Icc 0 ⌊y⌋₊, a n) -
        ∫ t in Set.Ioc x y, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ :=
      congrArg norm (supported_partial_summation a f hx.le hxy ha hf hfi)
    _ ≤ ‖f y * (∑ n ∈ Icc 0 ⌊y⌋₊, a n)‖ +
        ‖∫ t in Set.Ioc x y, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ := norm_sub_le _ _
    _ ≤ _ := by rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hfy (norm_nonneg _)) hint
end LeanLab.Linnik.Decomp1532b2

open Complex Set Filter Metric Finset
open scoped LSeries.notation
namespace LeanLab.Linnik.Decomp1532b2

/-- Gallagher 1970 p.334 the right half plane logarithmic derivative bound. -/
theorem norm_logDeriv_right_halfplane : ∃ A : ℝ, 1 ≤ A ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t d : ℝ), d ∈ Set.Ioo 0 1 →
      ‖deriv χ.LFunction (1 + d + I * t) / χ.LFunction (1 + d + I * t)‖ ≤ 1 / d + A := by
  obtain ⟨A, hA, hbound⟩ := ShiftZeroBound
  refine ⟨A, hA, ?_⟩
  intro q hq χ t d hd
  let s : ℂ := 1 + d + I * t
  have hs : 1 < s.re := by dsimp [s]; simp; linarith [hd.1]
  have hsr : s.re = 1 + d := by dsimp [s]; simp
  have hs' : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith [hd.1]
  have hm := ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
  have hc := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hterm (n : ℕ) : ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s n‖ ≤
      (LSeries.term ↗ArithmeticFunction.vonMangoldt ((1 + d : ℝ) : ℂ) n).re := by
    by_cases hn : n = 0
    · subst n; simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hp : 0 < (n : ℝ) ^ (1 + d) := Real.rpow_pos_of_pos hn0 _
    have hcp : (n : ℂ) ^ ((1 + d : ℝ) : ℂ) = (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply, norm_div, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hsr, hcp, ← Complex.ofReal_div, Complex.ofReal_re]
    have hmpos : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmpos]
    apply div_le_div_of_nonneg_right _ hp.le
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (χ.norm_le_one _) hmpos
  have hle : ‖LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s‖ ≤
      (LSeries ↗ArithmeticFunction.vonMangoldt ((1 + d : ℝ) : ℂ)).re := by
    rw [LSeries, LSeries, Complex.re_tsum hm]
    exact (norm_tsum_le_tsum_norm hc.norm).trans
      (hc.norm.tsum_le_tsum hterm (Complex.reCLM.summable hm))
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'] at hle
  have he := LeanLab.PNTPort.DirichletZF.neg_logDeriv_eq_LSeries χ hs
  have hn : ‖deriv χ.LFunction s / χ.LFunction s‖ =
      ‖LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s‖ := by
    rw [← he, neg_div, norm_neg]
  change ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ _
  rw [hn]
  apply hle.trans
  have hz := hbound d hd
  simpa only [Complex.ofReal_add, Complex.ofReal_one, neg_div, neg_re] using hz

/-- Gallagher p.333 local density lemma, elementary reciprocal pole estimate. -/
theorem reciprocal_pole_re_ge {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hzre : z.re ≤ 0) (hzn : ‖z‖ ≤ r) :
    1 / (4 * r) ≤ (((r : ℂ) - z)⁻¹).re := by
  have hvre : r ≤ ((r : ℂ) - z).re := by simp; linarith
  have hv0 : (r : ℂ) - z ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hvn : ‖(r : ℂ) - z‖ ≤ 2 * r := by
    calc
      _ ≤ ‖(r : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 2 * r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith
  rw [Complex.inv_re]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * r) (Complex.normSq_pos.mpr hv0)).2
  have hs : Complex.normSq ((r : ℂ) - z) = ‖(r : ℂ) - z‖ ^ 2 := (Complex.sq_norm _).symm
  rw [hs]
  nlinarith [norm_nonneg ((r : ℂ) - z)]
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF

/-- Gallagher 1970 p.333 Linnik local density bound, with multiplicity.
The zeros are expressed in the existing shifted coordinates centered at three halves plus i t. -/
theorem local_disc_order_sum_nonprincipal_add_one : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      0 < r → r ≤ 1 / 8 →
      (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
        (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤ C * (1 + r * Real.log (Bt q t)) := by
  obtain ⟨A, hA, hnorm⟩ := norm_logDeriv_right_halfplane
  refine ⟨4 * (K0 + A + 1), by have := K0_pos; positivity, ?_⟩
  intro q hq χ hχ t r hr hrl
  have hr1 : r < 1 := by linarith
  let z : ℂ := (r : ℂ) - 1 / 2
  let T : Finset ℂ := zset hχ t
  let S : Finset ℂ := T.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r)
  let F : ℂ := deriv χ.LFunction (1 + r + I * t) / χ.LFunction (1 + r + I * t)
  let V : ℂ := ∑ ρ ∈ T, (analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ)
  obtain ⟨hz, he⟩ := shift_setup hχ t ⟨hr, hr1⟩
  have hkey := logDeriv_sub_sum_le hχ t hz
  have hd : deriv (fShift χ t) z = deriv χ.LFunction (1 + r + I * t) := by
    unfold fShift
    rw [deriv_comp_add_const]
    exact congrArg (deriv χ.LFunction) he
  have hv : fShift χ t z = χ.LFunction (1 + r + I * t) := by
    unfold fShift
    exact congrArg χ.LFunction he
  have hkey' : ‖F - V‖ ≤ K0 * Real.log (Bt q t) := by
    change ‖deriv (fShift χ t) z / fShift χ t z - V‖ ≤ _ at hkey
    rw [hd, hv] at hkey
    exact hkey
  have hV : V.re ≤ 1 / r + A + K0 * Real.log (Bt q t) := by
    calc
      V.re ≤ ‖V‖ := Complex.re_le_norm _
      _ = ‖F - (F - V)‖ := by congr 1; ring
      _ ≤ ‖F‖ + ‖F - V‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (hnorm q χ t r ⟨hr, hr1⟩) hkey'
  have hzeroRe (ρ : ℂ) (hρ : ρ ∈ T) : (ρ + (1 / 2 : ℂ)).re ≤ 0 := by
    have hz0 := (mem_zset.mp hρ).2
    have hreal : (ρ + ((3 : ℂ) / 2 + I * t)).re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hz0
    norm_num at hreal ⊢
    linarith
  have hpositive (ρ : ℂ) (hρ : ρ ∈ T) :
      0 ≤ ((analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ)).re := by
    apply re_natCast_div_nonneg
    dsimp [z]
    have := hzeroRe ρ hρ
    norm_num [z] at this ⊢
    linarith
  have hnear (ρ : ℂ) (hρ : ρ ∈ S) :
      (analyticOrderNatAt (fShift χ t) ρ : ℝ) / (4 * r) ≤
        ((analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ)).re := by
    obtain ⟨hρT, hρn⟩ := mem_filter.mp hρ
    have hp := reciprocal_pole_re_ge hr (hzeroRe ρ hρT) hρn
    have hez : z - ρ = (r : ℂ) - (ρ + 1 / 2) := by dsimp [z]; ring
    rw [hez]
    simp only [div_eq_mul_inv, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    simpa only [one_div, one_mul] using mul_le_mul_of_nonneg_left hp
      (Nat.cast_nonneg (analyticOrderNatAt (fShift χ t) ρ) : (0 : ℝ) ≤ _)
  have hsum : (∑ ρ ∈ S, (analyticOrderNatAt (fShift χ t) ρ : ℝ)) / (4 * r) ≤
      1 / r + A + K0 * Real.log (Bt q t) := by
    apply le_trans _ hV
    dsimp only [V]
    rw [Complex.re_sum, sum_div]
    exact (sum_le_sum (fun ρ hρ => hnear ρ hρ)).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ρ hρ _ => hpositive ρ hρ))
  have hnum := (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hsum
  have hex : (1 / r + A + K0 * Real.log (Bt q t)) * (4 * r) =
      4 + 4 * A * r + 4 * K0 * (r * Real.log (Bt q t)) := by field_simp
  rw [hex] at hnum
  have hAr : A * r ≤ A := mul_le_of_le_one_right (by linarith) hr1.le
  have hrt : 0 ≤ r * Real.log (Bt q t) := mul_nonneg hr.le (Real.log_nonneg (one_lt_Bt t).le)
  change (∑ ρ ∈ S, (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤ _
  have hK := K0_pos
  nlinarith [mul_nonneg (show 0 ≤ A + 1 by linarith) hrt]

/-- Gallagher p.333 the log scale absorbs the constant in the local disc count. -/
theorem local_disc_order_sum_nonprincipal : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      0 < r → r ≤ 1 / 8 → 1 ≤ r * Real.log (Bt q t) →
      (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
        (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤ C * r * Real.log (Bt q t) := by
  obtain ⟨C, hC, hc⟩ := local_disc_order_sum_nonprincipal_add_one
  refine ⟨2 * C, by positivity, ?_⟩
  intro q hq χ hχ t r hr hrl hlog
  have h := hc q χ hχ t r hr hrl
  have hmul := mul_le_mul_of_nonneg_left hlog hC
  nlinarith
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF
/-- Gallagher 1970 p.333 the principal character local count away from low height. -/
theorem local_disc_order_sum_zeta_add_one : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t r : ℝ), 2 ≤ |t| → 0 < r → r ≤ 1 / 8 →
      ∀ hfin : (ZeroWindow t).Finite,
      (∑ ρ ∈ hfin.toFinset.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r),
        (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * (1 + r * Real.log |t|) := by
  obtain ⟨A, hA, hnorm⟩ := norm_logDeriv_right_halfplane
  obtain ⟨K, hK, herr⟩ := SumBoundI
  refine ⟨4 * (K + A + 1), by positivity, ?_⟩
  intro t r ht hr hrl hfin
  have hr1 : r < 1 := by linarith
  let T : Finset ℂ := hfin.toFinset
  let S : Finset ℂ := T.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r)
  let s : ℂ := 1 + r + I * t
  let F : ℂ := deriv riemannZeta s / riemannZeta s
  let V : ℂ := ∑ ρ ∈ T, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)
  have hkey : ‖F - V‖ ≤ K * Real.log |t| := herr r ⟨hr, hr1⟩ t ht hfin
  have hF : ‖F‖ ≤ 1 / r + A := by
    simpa only [F, s, DirichletCharacter.LFunction_modOne_eq] using hnorm 1 1 t r ⟨hr, hr1⟩
  have hV : V.re ≤ 1 / r + A + K * Real.log |t| := by
    calc
      V.re ≤ ‖V‖ := Complex.re_le_norm _
      _ = ‖F - (F - V)‖ := by congr 1; ring
      _ ≤ ‖F‖ + ‖F - V‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hF hkey
  have hzeroRe (ρ : ℂ) (hρ : ρ ∈ T) : ρ.re < 1 := by
    have hz0 : riemannZeta ρ = 0 := ((Set.Finite.mem_toFinset hfin).mp hρ).1
    exact lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz0)
  have hpositive (ρ : ℂ) (hρ : ρ ∈ T) :
      0 ≤ ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re := by
    apply re_natCast_div_nonneg
    have := hzeroRe ρ hρ
    norm_num [s]
    linarith
  have hnear (ρ : ℂ) (hρ : ρ ∈ S) :
      (analyticOrderNatAt riemannZeta ρ : ℝ) / (4 * r) ≤
        ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re := by
    obtain ⟨hρT, hρn⟩ := mem_filter.mp hρ
    have hρre : (ρ - (1 + I * t)).re ≤ 0 := by norm_num; linarith [hzeroRe ρ hρT]
    have hp := reciprocal_pole_re_ge hr hρre hρn
    have hez : s - ρ = (r : ℂ) - (ρ - (1 + I * t)) := by dsimp [s]; ring
    rw [hez]
    simp only [div_eq_mul_inv, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    simpa only [one_div, one_mul] using mul_le_mul_of_nonneg_left hp
      (Nat.cast_nonneg (analyticOrderNatAt riemannZeta ρ) : (0 : ℝ) ≤ _)
  have hsum : (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) / (4 * r) ≤
      1 / r + A + K * Real.log |t| := by
    apply le_trans _ hV
    dsimp only [V]
    rw [Complex.re_sum, sum_div]
    exact (sum_le_sum (fun ρ hρ => hnear ρ hρ)).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ρ hρ _ => hpositive ρ hρ))
  have hnum := (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hsum
  have hex : (1 / r + A + K * Real.log |t|) * (4 * r) =
      4 + 4 * A * r + 4 * K * (r * Real.log |t|) := by field_simp
  rw [hex] at hnum
  have hAr : A * r ≤ A := mul_le_of_le_one_right (by linarith) hr1.le
  have hrt : 0 ≤ r * Real.log |t| := mul_nonneg hr.le (Real.log_nonneg (by linarith))
  change (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ _
  nlinarith [mul_nonneg (show 0 ≤ A + 1 by linarith) hrt]
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF
/-- Gallagher p.333 local density bound in the original L-function coordinates. -/
theorem local_zero_order_sum_nonprincipal : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ t r : ℝ, 0 < r → r ≤ 1 / 8 → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        C * (1 + r * Real.log (Bt q t)) := by
  classical
  obtain ⟨C, hC, hcount⟩ := local_disc_order_sum_nonprincipal_add_one
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ t r hr hrl S hS
  let c : ℂ := 3 / 2 + I * t
  let U : Finset ℂ := S.image (fun ρ => ρ - c)
  let T : Finset ℂ := (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r)
  have hsub : U ⊆ T := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hu
    have hzero := (hS ρ hρ).1
    have hnear := (hS ρ hρ).2
    apply mem_filter.mpr
    have he : ρ - c + 1 / 2 = ρ - (1 + I * t) := by dsimp [c]; ring
    refine ⟨mem_zset.mpr ⟨?_, ?_⟩, by rwa [he]⟩
    · have hn : ‖ρ - c‖ ≤ ‖ρ - (1 + I * t)‖ + 1 / 2 := by
        have he' : ρ - c = (ρ - (1 + I * t)) - (1 / 2 : ℂ) := by dsimp [c]; ring
        rw [he']
        simpa using norm_sub_le (ρ - (1 + I * t)) (1 / 2 : ℂ)
      linarith
    · simpa only [fShift, c, sub_add_cancel] using hzero
  have hord (ρ : ℂ) : analyticOrderNatAt (fShift χ t) (ρ - c) = analyticOrderNatAt χ.LFunction ρ := by
    unfold fShift
    change analyticOrderNatAt (fun z => χ.LFunction (z + c)) (ρ - c) = _
    rw [analyticOrderNatAt_fun_comp_add_right, sub_add_cancel]
  have heq : (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
      ∑ u ∈ U, (analyticOrderNatAt (fShift χ t) u : ℝ) := by
    dsimp only [U]
    rw [sum_image (fun a ha b hb h => by
      have hh := congrArg (fun x : ℂ => x + c) h
      simpa only [sub_add_cancel] using hh)]
    simp only [hord]
  rw [heq]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
    (hcount q χ hχ t r hr hrl)

/-- Gallagher p.333 principal local density bound in the original zeta coordinates. -/
theorem local_zero_order_sum_zeta : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t r : ℝ, 2 ≤ |t| → 0 < r → r ≤ 1 / 8 → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, riemannZeta ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * (1 + r * Real.log |t|) := by
  classical
  obtain ⟨C, hC, hcount⟩ := local_disc_order_sum_zeta_add_one
  refine ⟨C, hC, ?_⟩
  intro t r ht hr hrl S hS
  let hfin := ZeroWindowFinite ht
  let T : Finset ℂ := hfin.toFinset.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r)
  have hsub : S ⊆ T := by
    intro ρ hρ
    apply mem_filter.mpr
    refine ⟨(Set.Finite.mem_toFinset hfin).mpr ⟨(hS ρ hρ).1, ?_⟩, (hS ρ hρ).2⟩
    have he : ρ - (3 / 2 + I * t) = (ρ - (1 + I * t)) - (1 / 2 : ℂ) := by ring
    rw [he]
    have htri := norm_sub_le (ρ - (1 + I * t)) (1 / 2 : ℂ)
    norm_num at htri
    linarith [(hS ρ hρ).2]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
    (hcount t r ht hr hrl hfin)

/-- Gallagher p.333 local density lemma for every primitive character.
The principal character height restriction is retained. -/
theorem local_zero_order_sum_primitive : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ t r : ℝ, (χ = 1 → 2 ≤ |t|) → 0 < r → r ≤ 1 / 8 → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        C * (1 + r * Real.log (Bt q t)) := by
  obtain ⟨C₁, hC₁, hnon⟩ := local_zero_order_sum_nonprincipal
  obtain ⟨C₂, hC₂, hzeta⟩ := local_zero_order_sum_zeta
  refine ⟨max C₁ C₂, le_trans hC₁ (le_max_left _ _), ?_⟩
  intro q hq χ hp t r ht hr hrl S hS
  have hfac : 0 ≤ 1 + r * Real.log (Bt q t) := by
    have hlog := Real.log_nonneg (one_lt_Bt (N := q) t).le
    positivity
  by_cases hχ : χ = 1
  · have hq1 : q = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    subst q
    have hS' : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using hS
    have h := hzeta t r (ht hχ) hr hrl S hS'
    simp only [DirichletCharacter.LFunction_modOne_eq]
    apply h.trans
    have hBt : |t| ≤ Bt 1 t := by
      have hZ := one_le_Z
      have hm := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 2 * (|t| + 3) by positivity)
      norm_num [Bt]
      nlinarith [abs_nonneg t]
    have hlog := Real.log_le_log (by have := ht hχ; positivity : 0 < |t|) hBt
    exact (mul_le_mul_of_nonneg_left (by nlinarith : 1 + r * Real.log |t| ≤ 1 + r * Real.log (Bt 1 t)) hC₂).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hfac)
  · exact (hnon q χ hχ t r hr hrl S hS).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hfac)
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open Set MeasureTheory Finset
/-- Gallagher 1970 p.336 every zero height is detected for a full one-sided radius. -/
theorem height_window_mass_ge {T r γ : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T)
    (hγ : γ ∈ Set.Icc (-T) T) :
    r ≤ ∫ v in Set.Icc (-T) T, (Set.Icc (γ - r) (γ + r)).indicator (fun _ => (1 : ℝ)) v := by
  rw [setIntegral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
    Set.Icc_inter_Icc, Real.volume_real_Icc]
  have hmin1 : -T + r ≤ min T (γ + r) := le_min (by linarith) (by linarith [hγ.1])
  have hmin2 : γ ≤ min T (γ + r) := le_min hγ.2 (by linarith)
  have hmax : max (-T) (γ - r) ≤ min T (γ + r) - r :=
    max_le (by linarith) (by linarith)
  exact (show r ≤ min T (γ + r) - max (-T) (γ - r) by linarith).trans (le_max_left _ _)

/-- Gallagher p.336 finite covering count from a supplied pointwise energy bound. -/
theorem finite_height_cover_bound {ι : Type*} (S : Finset ι) (height : ι → ℝ)
    {T r H K : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T) (hH : 0 ≤ H)
    (hheight : ∀ i ∈ S, height i ∈ Set.Icc (-T) T) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Set.Icc (-T) T))
    (hpoint : ∀ v ∈ Set.Icc (-T) T,
      H * (∑ i ∈ S, (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v) ≤ K * g v) :
    (S.card : ℝ) * r * H ≤ K * ∫ v in Set.Icc (-T) T, g v := by
  have hi (i : ι) : IntegrableOn
      ((Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ))) (Set.Icc (-T) T) := by
    have hfull : Integrable ((Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ))) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const isCompact_Icc.measure_lt_top.ne
    exact hfull.integrableOn
  calc
    _ = H * ∑ _i ∈ S, r := by simp; ring
    _ ≤ H * ∑ i ∈ S, ∫ v in Set.Icc (-T) T,
        (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v := by
      apply mul_le_mul_of_nonneg_left _ hH
      exact sum_le_sum (fun i hi => height_window_mass_ge hr hrT (hheight i hi))
    _ = ∫ v in Set.Icc (-T) T, H *
        (∑ i ∈ S, (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v) := by
      rw [integral_const_mul, integral_finsetSum S (fun i _ => hi i)]
    _ ≤ ∫ v in Set.Icc (-T) T, K * g v := by
      apply integral_mono_ae ((integrable_finsetSum S (fun i _ => hi i)).const_mul H) (hg.const_mul K)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact hpoint v hv
    _ = _ := integral_const_mul K _
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open Finset MeasureTheory Real
/-- Gallagher p.335 reciprocal tails from square root cumulative mass. -/
theorem reciprocal_tail_of_sqrt_mass (b : ℕ → ℝ) {C x y : ℝ}
    (hC : 0 ≤ C) (hx : 1 ≤ x) (hxy : x ≤ y) (hb : ∀ n, 0 ≤ b n)
    (hmass : ∀ t ∈ Set.Icc x y, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) ≤ C * Real.sqrt t) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, b n / (n : ℝ)) ≤ 2 * C / Real.sqrt x := by
  let A : ℝ → ℝ := fun t => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hpos : ∀ t ∈ Set.Icc x y, 0 < t := fun t ht => hx0.trans_le ht.1
  have hf : ∀ t ∈ Set.Icc x y, DifferentiableAt ℝ (fun u : ℝ => 1 / u) t := by
    intro t ht
    exact ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (hpos t ht).ne').differentiableAt
  have hd (t : ℝ) (ht : t ∈ Set.Icc x y) : deriv (fun u : ℝ => 1 / u) t = -(t ^ 2)⁻¹ := by
    have h := ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (hpos t ht).ne').deriv
    change deriv (fun u : ℝ => 1 / u) t = (0 * t - 1 * 1) / t ^ 2 at h
    simpa only [zero_mul, one_mul, zero_sub, neg_div, one_div] using h
  have hfi : IntegrableOn (deriv (fun u : ℝ => 1 / u)) (Set.Icc x y) := by
    apply IntegrableOn.congr_fun ?_ (fun t ht => (hd t ht).symm) measurableSet_Icc
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (hpos t ht).ne')).neg.integrableOn_Icc
  have hAb := sum_mul_eq_sub_sub_integral_mul b hx0.le hxy hf hfi
  have hker : IntegrableOn (fun t : ℝ => A t / t ^ 2) (Set.Icc x y) := by
    have hh : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc x y) :=
      ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (hpos t ht).ne')).integrableOn_Icc
    simpa only [A, div_eq_mul_inv, mul_comm] using integrableOn_mul_sum_Icc b hx0.le hh
  have hle : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, b n / (n : ℝ)) ≤ A y / y +
      ∫ t in Set.Ioc x y, A t / t ^ 2 := by
    have he : (∫ t in Set.Ioc x y, deriv (fun u : ℝ => 1 / u) t * A t) =
        -(∫ t in Set.Ioc x y, A t / t ^ 2) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change deriv (fun u : ℝ => 1 / u) t * A t = -(A t / t ^ 2)
      rw [hd t ⟨ht.1.le, ht.2⟩]
      ring
    have hA0 : 0 ≤ A x := sum_nonneg (fun n _ => hb n)
    have heq : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, b n / (n : ℝ)) = A y / y - A x / x +
        ∫ t in Set.Ioc x y, A t / t ^ 2 := by
      change (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, (1 / (n : ℝ)) * b n) =
        (1 / y) * A y - (1 / x) * A x - ∫ t in Set.Ioc x y, deriv (fun u : ℝ => 1 / u) t * A t at hAb
      rw [he] at hAb
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm, sub_neg_eq_add] using hAb
    rw [heq]
    have hnon := div_nonneg hA0 hx0.le
    linarith
  have ht_eq (t : ℝ) (ht : 0 < t) : Real.sqrt t / t ^ 2 = t ^ (-3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 2, ← Real.rpow_sub ht]
    congr 1
    norm_num
  have hbnd : (∫ t in Set.Ioc x y, A t / t ^ 2) ≤ C *
      ∫ t in x..y, t ^ (-3 / 2 : ℝ) := by
    rw [intervalIntegral.integral_of_le hxy, ← integral_const_mul]
    apply setIntegral_mono_on (hker.mono_set Set.Ioc_subset_Icc_self)
      ((continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (hpos t ht).ne'))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      measurableSet_Ioc
    intro t ht
    calc
      _ ≤ C * Real.sqrt t / t ^ 2 := div_le_div_of_nonneg_right (hmass t ⟨ht.1.le, ht.2⟩) (sq_nonneg t)
      _ = _ := by rw [mul_div_assoc, ht_eq t (hpos t ⟨ht.1.le, ht.2⟩)]; rfl
  have hzero : (0 : ℝ) ∉ Set.uIcc x y := by rw [Set.uIcc_of_le hxy]; intro h; linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)] at hbnd
  have hsqrt (t : ℝ) (ht : 0 < t) : t ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
    norm_num
  norm_num only [show (-3 / 2 : ℝ) + 1 = -1 / 2 by norm_num] at hbnd
  rw [hsqrt x hx0, hsqrt y hy0] at hbnd
  have hterm : A y / y ≤ C / Real.sqrt y := by
    calc
      _ ≤ C * Real.sqrt y / y := div_le_div_of_nonneg_right (hmass y ⟨hxy, le_rfl⟩) hy0.le
      _ = _ := by
        apply (div_eq_div_iff hy0.ne' (Real.sqrt_pos.mpr hy0).ne').2
        rw [mul_assoc, ← pow_two, Real.sq_sqrt hy0.le]
  have he : C * ((1 / Real.sqrt y - 1 / Real.sqrt x) / -(1 / 2 : ℝ)) =
      2 * C / Real.sqrt x - 2 * (C / Real.sqrt y) := by ring
  rw [he] at hbnd
  have hnon : 0 ≤ C / Real.sqrt y := div_nonneg hC (Real.sqrt_nonneg y)
  linarith
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher 1970 p.335 the prime power contribution above x is O of reciprocal square root x.
The sum contains von Mangoldt coefficients at every nonprime integer in the window. -/
theorem prime_power_reciprocal_tail : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x y : ℝ, 1 ≤ x → x ≤ y →
      (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤ C / Real.sqrt x := by
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  let b : ℕ → ℝ := fun n => if n.Prime then 0 else ArithmeticFunction.vonMangoldt n
  have hb (n : ℕ) : 0 ≤ b n := by
    dsimp [b]
    split_ifs
    · rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg
  have hmass (t : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) ≤ C * Real.sqrt t := by
    have hI : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) = ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n := by
      symm
      apply sum_subset (fun n hn => mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioc.mp hn).2⟩)
      intro n hn hn'
      have hn0 : n = 0 := by
        by_contra hn0
        exact hn' (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, (mem_Icc.mp hn).2⟩)
      subst n
      simp [b]
    rw [hI]
    have he : (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n) = Chebyshev.psi t - Chebyshev.theta t := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter]
      apply sum_congr rfl
      intro n hn
      by_cases hp : n.Prime <;> simp [b, hp]
    rw [he]
    exact (hC₀ t).trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (Real.sqrt_nonneg t))
  refine ⟨2 * C, by positivity, ?_⟩
  intro x y hx hxy
  have h := reciprocal_tail_of_sqrt_mass b hC hx hxy hb (fun t ht => hmass t)
  convert h using 1
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [b, hp]
end LeanLab.Linnik.Decomp1532b2

open Complex Set Filter LSeries
open scoped LSeries.notation Topology
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher 1970 p.334 arithmetic form of every logarithmic derivative in the right half plane. -/
theorem iterated_neg_logDeriv_eq_LSeries {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z) s =
      (-1) ^ k * LSeries (LSeries.logMul^[k] (↗χ * ↗ArithmeticFunction.vonMangoldt)) s := by
  have hconv : LSeries.abscissaOfAbsConv (↗χ * ↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simpa using hy)
  have heq : (fun z => -deriv χ.LFunction z / χ.LFunction z) =ᶠ[𝓝 s]
      LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact LeanLab.PNTPort.DirichletZF.neg_logDeriv_eq_LSeries χ hz
  rw [heq.iteratedDeriv_eq k]
  apply LSeries_iteratedDeriv
  exact hconv.trans_lt (by exact_mod_cast hs)
end LeanLab.Linnik.Decomp1532b2

open Complex Set Filter Metric Finset
open scoped Topology
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 removing the finite zero product leaves a nonzero analytic factor. -/
theorem zero_removed_factor_ne_zero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (h0 : f 0 ≠ 0)
    (hfin : (SetOfZeros 1 f).Finite) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) :
    Cf (3 / 4) f z ≠ 0 := by
  have h := BlaschkeNonzero (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    hfin hf h0 z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
  unfold BlaschkeB at h
  simp only [finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin, ↓reduceDIte] at h
  exact (mul_ne_zero_iff.mp h).1

/-- Gallagher p.334 the logarithmic derivative residual is analytic across every removed zero. -/
theorem zero_removed_logDeriv_analytic {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (h0 : f 0 ≠ 0)
    (hfin : (SetOfZeros 1 f).Finite) :
    AnalyticOnNhd ℂ (logDeriv (Cf (3 / 4) f)) (closedBall (0 : ℂ) (3 / 4)) := by
  have han := CfAnalytic (by norm_num : (3 / 4 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 1) hf h0
  intro z hz
  have hz' : z ∈ closedBall (0 : ℂ) (4 / 5) := closedBall_subset_closedBall (by norm_num) hz
  exact (han z hz').deriv.div (han z hz') (zero_removed_factor_ne_zero hf h0 hfin (by simpa [mem_closedBall, dist_zero_right] using hz))

/-- Gallagher p.334 off the finite zero set the residual is the original logarithmic derivative minus the pole sum. -/
theorem zero_removed_logDeriv_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (h0 : f 0 ≠ 0)
    (hfin : (SetOfZeros 1 f).Finite) {z : ℂ} (hz : ‖z‖ ≤ 2 / 3) (hne : f z ≠ 0) :
    logDeriv (Cf (3 / 4) f) z = logDeriv f z -
      ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ) := by
  let S := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset
  have hznot : z ∉ SetOfZeros (3 / 4) f := fun h => hne h.2
  have heq : Cf (3 / 4) f =ᶠ[𝓝 z]
      (fun w => f w / ∏ ρ ∈ S, (w - ρ) ^ analyticOrderNatAt f ρ) := by
    filter_upwards [(isOpen_compl_iff.mpr (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).isClosed).mem_nhds hznot] with w hw
    simp only [Cf, finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin, ↓reduceDIte, show w ∉ SetOfZeros (3 / 4) f from hw, S]
  have hρ (ρ : ℂ) (hρ : ρ ∈ S) : z - ρ ≠ 0 := by
    intro he
    have hzρ : z = ρ := sub_eq_zero.mp he
    exact hne (hzρ ▸ ((Set.Finite.mem_toFinset _).mp hρ).2)
  have hprod : (∏ ρ ∈ S, (z - ρ) ^ analyticOrderNatAt f ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun ρ hρ' => pow_ne_zero _ (hρ ρ hρ'))
  have hdiff : ∀ ρ ∈ S, DifferentiableAt ℂ (fun w => (w - ρ) ^ analyticOrderNatAt f ρ) z :=
    fun ρ _ => (differentiableAt_id.sub_const ρ).pow _
  have hlog : logDeriv (Cf (3 / 4) f) z =
      logDeriv (fun w => f w / ∏ ρ ∈ S, (w - ρ) ^ analyticOrderNatAt f ρ) z := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.self_of_nhds]
  rw [hlog, logDeriv_fun_div z hne hprod
    (hf z (by simpa [mem_closedBall, dist_zero_right] using hz.trans (by norm_num : (2 / 3 : ℝ) ≤ 1))).differentiableAt
    (DifferentiableAt.fun_finsetProd hdiff), logDeriv_fun_prod (f := fun (ρ : ℂ) (w : ℂ) => (w - ρ) ^ analyticOrderNatAt f ρ)
      (fun ρ hρ' => pow_ne_zero _ (hρ ρ hρ')) hdiff]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ'
  rw [logDeriv_fun_pow]
  · simp [logDeriv_apply, deriv_fun_sub, div_eq_mul_inv]
  · exact differentiableAt_id.sub_const ρ
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF
/-- Gallagher p.334 the analytic residual retains the uniform logarithmic bound at removed zeros. -/
theorem zero_removed_logDeriv_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ < 2 / 3) :
    ‖logDeriv (Cf (3 / 4) (fShift χ t)) z‖ ≤ K0 * Real.log (Bt q t) := by
  have hf : AnalyticOnNhd ℂ (fShift χ t) (closedBall (0 : ℂ) 1) := fun w _ => fShift_analyticAt hχ t w
  have hfin := fShift_finite_zeros hχ t
  have h0 := fShift_zero_ne χ t
  have han := zero_removed_logDeriv_analytic hf h0 hfin
  let U : Set ℂ := ball (0 : ℂ) (2 / 3) ∩ (SetOfZeros 1 (fShift χ t))ᶜ
  have hdense : Dense (SetOfZeros 1 (fShift χ t))ᶜ := hfin.countable.dense_compl ℂ
  have hzcl : z ∈ closure U := hdense.open_subset_closure_inter isOpen_ball (by simpa [mem_ball, dist_zero_right] using hz)
  have hmaps : MapsTo (fun w => ‖logDeriv (Cf (3 / 4) (fShift χ t)) w‖) U
      (Set.Iic (K0 * Real.log (Bt q t))) := by
    intro w hw
    have hnorm : ‖w‖ < 2 / 3 := by simpa [U, mem_ball, dist_zero_right] using hw.1
    have hne : fShift χ t w ≠ 0 := fun h => hw.2 ⟨hnorm.le.trans (by norm_num), h⟩
    change ‖logDeriv (Cf (3 / 4) (fShift χ t)) w‖ ≤ K0 * Real.log (Bt q t)
    rw [zero_removed_logDeriv_eq hf h0 hfin hnorm.le hne]
    exact logDeriv_sub_sum_le hχ t ⟨by simpa [mem_closedBall, dist_zero_right] using hnorm.le,
      fun h => hne h.2⟩
  have hcont : ContinuousAt (fun w => ‖logDeriv (Cf (3 / 4) (fShift χ t)) w‖) z :=
    (han z (by simp [mem_closedBall, dist_zero_right]; linarith)).continuousAt.norm
  have h := hcont.continuousWithinAt.mem_closure hzcl hmaps
  simpa only [isClosed_Iic.closure_eq, Set.mem_Iic] using h
end LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF
/-- Gallagher p.334 uniform Cauchy estimate for every derivative of the zero removed residual. -/
theorem iterated_zero_removed_logDeriv_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (t : ℝ) (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖iteratedDeriv k (logDeriv (Cf (3 / 4) (fShift χ t))) z‖ ≤
      (k.factorial : ℝ) * (K0 * Real.log (Bt q t)) * 8 ^ k := by
  have hf : AnalyticOnNhd ℂ (fShift χ t) (closedBall (0 : ℂ) 1) := fun w _ => fShift_analyticAt hχ t w
  have han := zero_removed_logDeriv_analytic hf (fShift_zero_ne χ t) (fShift_finite_zeros hχ t)
  have hsub : closedBall z (1 / 8) ⊆ closedBall (0 : ℂ) (3 / 4) := by
    intro w hw
    have hdist : ‖w - z‖ ≤ 1 / 8 := by simpa [mem_closedBall, dist_eq_norm] using hw
    have hh : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hdc : DiffContOnCl ℂ (logDeriv (Cf (3 / 4) (fShift χ t))) (ball z (1 / 8)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num : (1 / 8 : ℝ) ≠ 0)]
    exact (han.mono hsub).differentiableOn
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 1 / 8) hdc (C := K0 * Real.log (Bt q t)) ?_
  · simpa only [one_div, inv_pow, div_inv_eq_mul] using hbound
  · intro w hw
    have hdist : ‖w - z‖ = 1 / 8 := by simpa [mem_sphere, dist_eq_norm] using hw
    have hh : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
    exact zero_removed_logDeriv_bound hχ t (by linarith)
end LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF
/-- Gallagher p.334 every derivative of L prime over L is the nearby pole power sum plus a controlled residual. -/
theorem iterated_logDeriv_pole_expansion_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (t : ℝ) (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (hne : fShift χ t z ≠ 0) :
    ‖iteratedDeriv k (logDeriv (fShift χ t)) z -
      (-1 : ℂ) ^ k * k.factorial *
        ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1)
          (fShift_finite_zeros hχ t)).toFinset,
          (analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ) ^ (k + 1)‖ ≤
      (k.factorial : ℝ) * (K0 * Real.log (Bt q t)) * 8 ^ k := by
  let f := fShift χ t
  have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) := fun w _ => fShift_analyticAt hχ t w
  let S := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1)
    (fShift_finite_zeros hχ t)).toFinset
  have h0 := fShift_zero_ne χ t
  have hfin := fShift_finite_zeros hχ t
  have hρ (ρ : ℂ) (hρ : ρ ∈ S) : z - ρ ≠ 0 := by
    intro he
    exact hne (sub_eq_zero.mp he ▸ ((Set.Finite.mem_toFinset _).mp hρ).2)
  have heq : logDeriv (Cf (3 / 4) f) =ᶠ[𝓝 z]
      (fun w => logDeriv f w - ∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℂ) / (w - ρ)) := by
    have hzc : z ∈ ball (0 : ℂ) (2 / 3) := by simp [mem_ball, dist_zero_right]; linarith
    filter_upwards [isOpen_ball.mem_nhds hzc,
      (fShift_analyticAt hχ t z).continuousAt.eventually_ne hne] with w hw hwn
    have hh : ‖w‖ < 2 / 3 := by simpa [mem_ball, dist_zero_right] using hw
    exact zero_removed_logDeriv_eq hf h0 hfin hh.le hwn
  have hdf : ContDiffAt ℂ k (logDeriv f) z := by
    exact ((fShift_analyticAt hχ t z).deriv.div (fShift_analyticAt hχ t z) hne).contDiffAt
  have hdp (ρ : ℂ) (hρ' : ρ ∈ S) : ContDiffAt ℂ k (fun w => (analyticOrderNatAt f ρ : ℂ) / (w - ρ)) z :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hρ ρ hρ')).contDiffAt
  have hpole (ρ : ℂ) : iteratedDeriv k (fun w => (analyticOrderNatAt f ρ : ℂ) / (w - ρ)) z =
      (-1 : ℂ) ^ k * k.factorial * ((analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)) := by
    simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field]
    change (analyticOrderNatAt f ρ : ℂ) * iteratedDeriv k (fun w => (fun u : ℂ => u⁻¹) (w - ρ)) z = _
    rw [iteratedDeriv_comp_sub_const]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_inv]
    rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    ring
  have heqder := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_fun_sub hdf (ContDiffAt.sum (fun ρ hρ' => hdp ρ hρ')),
    iteratedDeriv_fun_sum (fun ρ hρ' => hdp ρ hρ')] at heqder
  simp_rw [hpole] at heqder
  rw [← Finset.mul_sum] at heqder
  rw [← heqder]
  exact iterated_zero_removed_logDeriv_bound hχ t k hz
end LeanLab.Linnik.Decomp1532b2

open Complex Set Filter Metric Finset
open scoped Topology
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 exact derivative identity after removing the finite pole product. -/
theorem iterated_zero_removed_logDeriv_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (h0 : f 0 ≠ 0)
    (hfin : (SetOfZeros 1 f).Finite) (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (hne : f z ≠ 0) :
    iteratedDeriv k (logDeriv (Cf (3 / 4) f)) z =
      iteratedDeriv k (logDeriv f) z - (-1 : ℂ) ^ k * k.factorial *
        ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset,
          (analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1) := by
  let S := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset
  have hρ (ρ : ℂ) (hρ : ρ ∈ S) : z - ρ ≠ 0 := by
    intro he
    exact hne (sub_eq_zero.mp he ▸ ((Set.Finite.mem_toFinset _).mp hρ).2)
  have heq : logDeriv (Cf (3 / 4) f) =ᶠ[𝓝 z]
      (fun w => logDeriv f w - ∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℂ) / (w - ρ)) := by
    have hfz := (hf z (by simp [mem_closedBall, dist_zero_right]; linarith)).continuousAt
    have hzc : z ∈ ball (0 : ℂ) (2 / 3) := by simp [mem_ball, dist_zero_right]; linarith
    filter_upwards [isOpen_ball.mem_nhds hzc,
      (hf z (by simp [mem_closedBall, dist_zero_right]; linarith)).continuousAt.eventually_ne hne] with w hw hwn
    have hh : ‖w‖ < 2 / 3 := by simpa [mem_ball, dist_zero_right] using hw
    exact zero_removed_logDeriv_eq hf h0 hfin hh.le hwn
  have hdf : ContDiffAt ℂ k (logDeriv f) z := by
    exact ((hf z (by simp [mem_closedBall, dist_zero_right]; linarith)).deriv.div (hf z (by simp [mem_closedBall, dist_zero_right]; linarith)) hne).contDiffAt
  have hdp (ρ : ℂ) (hρ' : ρ ∈ S) : ContDiffAt ℂ k (fun w => (analyticOrderNatAt f ρ : ℂ) / (w - ρ)) z :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hρ ρ hρ')).contDiffAt
  have hpole (ρ : ℂ) : iteratedDeriv k (fun w => (analyticOrderNatAt f ρ : ℂ) / (w - ρ)) z =
      (-1 : ℂ) ^ k * k.factorial * ((analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)) := by
    simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field]
    change (analyticOrderNatAt f ρ : ℂ) * iteratedDeriv k (fun w => (fun u : ℂ => u⁻¹) (w - ρ)) z = _
    rw [iteratedDeriv_comp_sub_const]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_inv]
    rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    ring
  have heqder := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_fun_sub hdf (ContDiffAt.sum (fun ρ hρ' => hdp ρ hρ')),
    iteratedDeriv_fun_sum (fun ρ hρ' => hdp ρ hρ')] at heqder
  simp_rw [hpole] at heqder
  rw [← Finset.mul_sum] at heqder
  exact heqder
end LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b2
open LeanLab.PNTPort.DirichletZF
/-- Gallagher p.334 the principal character pole expansion at absolute height at least two. -/
theorem iterated_zeta_logDeriv_pole_expansion_bound : ∃ A : ℝ, 0 < A ∧
    ∀ t : ℝ, 2 ≤ |t| →
    ∀ hfin : (SetOfZeros 1 (fun z : ℂ => riemannZeta (z + 3 / 2 + I * t))).Finite,
    ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → riemannZeta (z + 3 / 2 + I * t) ≠ 0 →
      ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t))) z -
        (-1 : ℂ) ^ k * k.factorial *
          ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset,
            (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℂ) /
              (z - ρ) ^ (k + 1)‖ ≤ (k.factorial : ℝ) * A * Real.log |t| * 8 ^ k := by
  obtain ⟨C, hC, hbound⟩ := LogDerivZetaFinalBound
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (3 / 4 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
  refine ⟨K0 * C, mul_pos K0_pos hC, ?_⟩
  intro t ht hfin k z hz hne
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) := by
    intro w hw
    have hnorm : ‖w‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hw
    have hsne : w + 3 / 2 + I * (t : ℂ) ≠ 1 := by
      intro he
      have hi := congr_arg Complex.im he
      simp only [add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, I_re, ofReal_im,
        mul_zero, I_im, ofReal_re, one_mul, zero_add, one_im] at hi
      have habs := Complex.abs_im_le_norm w
      have hh : w.im = -t := by linarith
      rw [hh, abs_neg] at habs
      linarith
    exact AnalyticAt.fun_comp (analyticAt_riemannZeta hsne) ((analyticAt_id.fun_add analyticAt_const).fun_add analyticAt_const)
  have h0 : f 0 ≠ 0 := by
    dsimp [f]
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have han := zero_removed_logDeriv_analytic hf h0 hfin
  have hres (w : ℂ) (hw : ‖w‖ < 2 / 3) :
      ‖logDeriv (Cf (3 / 4) f) w‖ ≤ K0 * (C * Real.log |t|) := by
    let U : Set ℂ := ball (0 : ℂ) (2 / 3) ∩ (SetOfZeros 1 f)ᶜ
    have hdense : Dense (SetOfZeros 1 f)ᶜ := hfin.countable.dense_compl ℂ
    have hwcl : w ∈ closure U := hdense.open_subset_closure_inter isOpen_ball
      (by simpa [mem_ball, dist_zero_right] using hw)
    have hmaps : MapsTo (fun u => ‖logDeriv (Cf (3 / 4) f) u‖) U
        (Set.Iic (K0 * (C * Real.log |t|))) := by
      intro u hu
      have hn : ‖u‖ < 2 / 3 := by simpa [U, mem_ball, dist_zero_right] using hu.1
      have hnu : f u ≠ 0 := fun he => hu.2 ⟨hn.le.trans (by norm_num), he⟩
      change ‖logDeriv (Cf (3 / 4) f) u‖ ≤ _
      rw [zero_removed_logDeriv_eq hf h0 hfin hn.le hnu]
      exact hbound t ht hfin u ⟨by simpa [mem_closedBall, dist_zero_right] using hn.le,
        fun h => hnu h.2⟩
    have hcont : ContinuousAt (fun u => ‖logDeriv (Cf (3 / 4) f) u‖) w :=
      (han w (by simp [mem_closedBall, dist_zero_right]; linarith)).continuousAt.norm
    have h := hcont.continuousWithinAt.mem_closure hwcl hmaps
    simpa only [isClosed_Iic.closure_eq, Set.mem_Iic] using h
  rw [← iterated_zero_removed_logDeriv_eq hf h0 hfin k hz hne]
  have hsub : closedBall z (1 / 8) ⊆ closedBall (0 : ℂ) (3 / 4) := by
    intro w hw
    have hd : ‖w - z‖ ≤ 1 / 8 := by simpa [mem_closedBall, dist_eq_norm] using hw
    have hh : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hdc : DiffContOnCl ℂ (logDeriv (Cf (3 / 4) f)) (ball z (1 / 8)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num : (1 / 8 : ℝ) ≠ 0)]
    exact (han.mono hsub).differentiableOn
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 1 / 8) hdc (C := K0 * (C * Real.log |t|)) (by
      intro w hw
      have hd : ‖w - z‖ = 1 / 8 := by simpa [mem_sphere, dist_eq_norm] using hw
      have hh : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
      exact hres w (by linarith))
  simpa only [one_div, inv_pow, div_inv_eq_mul, mul_assoc] using h
end LeanLab.Linnik.Decomp1532b2

open Finset Complex
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.335 prime power removal for bounded twists and the detector kernel on a finite window. -/
theorem poisson_weighted_prime_power_removal : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x y d : ℝ, 1 ≤ x → x ≤ y → 0 ≤ d → ∀ k : ℕ, ∀ a : ℕ → ℂ,
    (∀ n, ‖a n‖ ≤ 1) →
    ‖(∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, a n *
        ((ArithmeticFunction.vonMangoldt n / (n : ℝ)) * poissonKernel k (d * Real.log n) : ℝ)) -
      ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, a n *
        ((Real.log n / (n : ℝ)) * poissonKernel k (d * Real.log n) : ℝ)‖ ≤ C / Real.sqrt x := by
  obtain ⟨C, hC, htail⟩ := prime_power_reciprocal_tail
  refine ⟨C, hC, ?_⟩
  intro x y d hx hxy hd k a ha
  let S := Finset.Ioc ⌊x⌋₊ ⌊y⌋₊
  let f : ℕ → ℂ := fun n => a n *
    ((ArithmeticFunction.vonMangoldt n / (n : ℝ)) * poissonKernel k (d * Real.log n) : ℝ)
  have hprime : (∑ n ∈ S.filter Nat.Prime, a n *
      ((Real.log n / (n : ℝ)) * poissonKernel k (d * Real.log n) : ℝ)) = ∑ n ∈ S.filter Nat.Prime, f n := by
    apply sum_congr rfl
    intro n hn
    dsimp [f]
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hn).2]
  rw [hprime, ← sum_filter_add_sum_filter_not S Nat.Prime f, add_sub_cancel_left]
  calc
    ‖∑ n ∈ S.filter (fun n => ¬n.Prime), f n‖ ≤ ∑ n ∈ S.filter (fun n => ¬n.Prime), ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S.filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hu : 0 ≤ d * Real.log n := mul_nonneg hd (Real.log_natCast_nonneg n)
      have hp := poissonKernel_nonneg k hu
      have hp1 := poissonKernel_le_one k hu
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
      dsimp [f]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hΛ hp)]
      calc
        _ ≤ 1 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) * poissonKernel k (d * Real.log n)) :=
          mul_le_mul_of_nonneg_right (ha n) (mul_nonneg hΛ hp)
        _ ≤ _ := by simpa using mul_le_of_le_one_right hΛ hp1
    _ ≤ _ := htail x y hx hxy
end LeanLab.Linnik.Decomp1532b2

open Finset
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 dyadic tail estimate from a linear local mass bound. -/
theorem finite_dyadic_reciprocal_tail {ι : Type*} (S : Finset ι) (w R : ι → ℝ)
    {C cutoff : ℝ} (hC : 0 ≤ C) (hcutoff : 0 < cutoff) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hR : ∀ i ∈ S, cutoff ≤ R i)
    (hmass : ∀ u : ℝ, cutoff ≤ u → (∑ i ∈ S.filter (fun i => R i ≤ u), w i) ≤ C * u)
    {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ S, w i / R i ^ (k + 1)) ≤ 4 * C / cutoff ^ k := by
  classical
  choose j hj using fun i : ι => exists_nat_pow_near (le_max_left 1 (R i / cutoff)) (by norm_num : (1 : ℝ) < 2)
  have hnear (i : ι) (hi : i ∈ S) : (2 : ℝ) ^ j i * cutoff ≤ R i ∧ R i < 2 ^ (j i + 1) * cutoff := by
    have hge : 1 ≤ R i / cutoff := (le_div_iff₀ hcutoff).2 (by simpa using hR i hi)
    have hh := hj i
    rw [max_eq_right hge] at hh
    exact ⟨(le_div_iff₀ hcutoff).mp hh.1, (div_lt_iff₀ hcutoff).mp hh.2⟩
  let J := S.image j
  have hshell (m : ℕ) : (∑ i ∈ S.filter (fun i => j i = m), w i / R i ^ (k + 1)) ≤
      (2 * C / cutoff ^ k) * (1 / 2 : ℝ) ^ m := by
    have hlower : 0 < (2 : ℝ) ^ m * cutoff := by positivity
    have hsub : S.filter (fun i => j i = m) ⊆ S.filter (fun i => R i ≤ 2 ^ (m + 1) * cutoff) := by
      intro i hi
      obtain ⟨hiS, hij⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨hiS, by simpa [hij] using (hnear i hiS).2.le⟩
    have hm : (∑ i ∈ S.filter (fun i => j i = m), w i) ≤ C * (2 ^ (m + 1) * cutoff) :=
      (sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw i (mem_filter.mp hi).1)).trans
        (hmass _ (by nlinarith [one_le_pow₀ (n := m + 1) (by norm_num : (1 : ℝ) ≤ 2)]))
    calc
      _ ≤ ∑ i ∈ S.filter (fun i => j i = m), w i / (2 ^ m * cutoff) ^ (k + 1) := by
        apply sum_le_sum
        intro i hi
        obtain ⟨hiS, hij⟩ := mem_filter.mp hi
        exact div_le_div_of_nonneg_left (hw i hiS) (pow_pos hlower _)
          (pow_le_pow_left₀ hlower.le (by simpa [hij] using (hnear i hiS).1) _)
      _ = (∑ i ∈ S.filter (fun i => j i = m), w i) / (2 ^ m * cutoff) ^ (k + 1) := by rw [sum_div]
      _ ≤ (C * (2 ^ (m + 1) * cutoff)) / (2 ^ m * cutoff) ^ (k + 1) :=
        div_le_div_of_nonneg_right hm (pow_nonneg hlower.le _)
      _ = (2 * C / cutoff ^ k) * ((1 / 2 : ℝ) ^ k) ^ m := by
        rw [mul_pow, pow_succ (2 ^ m), pow_succ cutoff, pow_succ 2, ← pow_mul, mul_comm m k,
          pow_mul, div_pow, one_pow]
        simp only [one_div, inv_pow]
        field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hk
  rw [← sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem j hi) (fun i => w i / R i ^ (k + 1))]
  calc
    _ ≤ ∑ m ∈ J, (2 * C / cutoff ^ k) * (1 / 2 : ℝ) ^ m := sum_le_sum (fun m hm => hshell m)
    _ = (2 * C / cutoff ^ k) * ∑ m ∈ J, (1 / 2 : ℝ) ^ m := (mul_sum ..).symm
    _ ≤ (2 * C / cutoff ^ k) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hs : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) := summable_geometric_of_abs_lt_one (by norm_num)
      have hh := Summable.sum_le_tsum J (fun m hm => by positivity) hs
      have hts : (∑' m : ℕ, (1 / 2 : ℝ) ^ m) = 2 := by
        rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
        norm_num
      rw [hts] at hh
      exact hh
    _ = _ := by ring
end LeanLab.Linnik.Decomp1532b2

open Finset Complex
open LeanLab.PNTPort.DirichletZF
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 local density bound at every radius for the finite ambient zero set. -/
theorem local_disc_order_sum_nonprincipal_all_radii : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      0 < r → 1 ≤ r * Real.log (Bt q t) →
      (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
        (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤ C * r * Real.log (Bt q t) := by
  obtain ⟨C₀, hC₀, hsmall⟩ := local_disc_order_sum_nonprincipal
  let C : ℝ := max C₀ (8 / Real.log (10 / 9))
  have hlog : 0 < Real.log (10 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := hC₀.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ t r hr hscale
  have hBt : 0 ≤ Real.log (Bt q t) := Real.log_nonneg (one_lt_Bt t).le
  by_cases hrl : r ≤ 1 / 8
  · exact (hsmall q χ hχ t r hr hrl hscale).trans
      (by dsimp [C]; gcongr; exact le_max_left _ _)
  · have htotal := zero_count_le hχ t
    have hsub : (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
        (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤
        ∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ρ hρ _ => Nat.cast_nonneg _)
    apply hsub.trans (htotal.trans ?_)
    have hCr : 1 / Real.log (10 / 9 : ℝ) ≤ C * r := by
      have hcle : 8 / Real.log (10 / 9 : ℝ) ≤ C := le_max_right _ _
      have hr8 : 1 / 8 ≤ r := le_of_not_ge hrl
      have hh := mul_le_mul_of_nonneg_left hr8 (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hlog.le)
      have hh' := mul_le_mul_of_nonneg_right hcle hr.le
      have he : (8 / Real.log (10 / 9 : ℝ)) * (1 / 8) = 1 / Real.log (10 / 9 : ℝ) := by ring
      rw [he] at hh
      exact hh.trans hh'
    convert mul_le_mul_of_nonneg_right hCr hBt using 1; ring
end LeanLab.Linnik.Decomp1532b2

open Finset Complex
open LeanLab.PNTPort.DirichletZF
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 moving the evaluation point to the right increases every zero distance. -/
theorem norm_shift_right_ge {u : ℂ} (hu : u.re ≤ 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖u‖ ≤ ‖(r : ℂ) - u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im, zero_sub]
  nlinarith

/-- Gallagher p.334 the far zero reciprocal power tail has a uniform logarithmic bound. -/
theorem far_zero_pole_power_sum_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r cutoff : ℝ),
      0 ≤ r → 0 < cutoff → 1 ≤ cutoff * Real.log (Bt q t) → ∀ k : ℕ, 1 ≤ k →
      ‖∑ ρ ∈ (zset hχ t).filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖),
        (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
          C * Real.log (Bt q t) / cutoff ^ k := by
  obtain ⟨C₀, hC₀, hlocal⟩ := local_disc_order_sum_nonprincipal_all_radii
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro q hq χ hχ t r cutoff hr hcutoff hscale k hk
  let S := (zset hχ t).filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖)
  let w : ℂ → ℝ := fun ρ => analyticOrderNatAt (fShift χ t) ρ
  let R : ℂ → ℝ := fun ρ => ‖ρ + (1 / 2 : ℂ)‖
  have hlog : 0 ≤ Real.log (Bt q t) := Real.log_nonneg (one_lt_Bt t).le
  have hmass (u : ℝ) (hu : cutoff ≤ u) : (∑ ρ ∈ S.filter (fun ρ => R ρ ≤ u), w ρ) ≤
      (C₀ * Real.log (Bt q t)) * u := by
    have hsub : S.filter (fun ρ => R ρ ≤ u) ⊆ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ u) := by
      intro ρ hρ
      obtain ⟨hρS, hρR⟩ := mem_filter.mp hρ
      exact mem_filter.mpr ⟨(mem_filter.mp hρS).1, hρR⟩
    have hsc : 1 ≤ u * Real.log (Bt q t) := hscale.trans (mul_le_mul_of_nonneg_right hu hlog)
    have h := (sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ hρ' => Nat.cast_nonneg _)).trans
      (hlocal q χ hχ t u (hcutoff.trans_le hu) hsc)
    convert h using 1 <;> ring
  have htail := finite_dyadic_reciprocal_tail S w R (mul_nonneg hC₀ hlog) hcutoff
    (fun ρ hρ => Nat.cast_nonneg _) (fun ρ hρ => (mem_filter.mp hρ).2.le) hmass hk
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt (fShift χ t) ρ : ℂ) /
        ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, w ρ / R ρ ^ (k + 1) := by
      apply sum_le_sum
      intro ρ hρ
      have hρz := (mem_zset.mp (mem_filter.mp hρ).1).2
      have hre : (ρ + (1 / 2 : ℂ)).re ≤ 0 := by
        have hreal : (ρ + ((3 : ℂ) / 2 + I * t)).re < 1 := by
          by_contra h
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρz
        norm_num at hreal ⊢
        linarith
      have hdist : R ρ ≤ ‖(r : ℂ) - 1 / 2 - ρ‖ := by
        have h := norm_shift_right_ge hre hr
        convert h using 1 <;> congr 1 <;> ring
      have hRpos : 0 < R ρ := hcutoff.trans (mem_filter.mp hρ).2
      rw [norm_div, norm_pow, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hRpos _)
        (pow_le_pow_left₀ hRpos.le hdist _)
    _ ≤ _ := by convert htail using 1 <;> ring
end LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 display 21 restricted to the nonprincipal character case. -/
theorem near_zero_logDeriv_expansion_nonprincipal : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r cutoff : ℝ),
      0 < r → r ≤ 1 / 8 → 0 < cutoff → cutoff ≤ 1 / 8 →
      1 ≤ cutoff * Real.log (Bt q t) → ∀ k : ℕ, 1 ≤ k →
      ‖iteratedDeriv k (logDeriv (fShift χ t)) ((r : ℂ) - 1 / 2) -
        (-1 : ℂ) ^ k * k.factorial *
          ∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff),
            (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) * C * Real.log (Bt q t) / cutoff ^ k := by
  obtain ⟨C₀, hC₀, htail⟩ := far_zero_pole_power_sum_bound
  refine ⟨K0 + C₀, by have := K0_pos; positivity, ?_⟩
  intro q hq χ hχ t r cutoff hr hrl hc hcl hscale k hk
  let z : ℂ := (r : ℂ) - 1 / 2
  let a : ℂ := (-1 : ℂ) ^ k * k.factorial
  let f : ℂ → ℂ := fShift χ t
  let P : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)
  let S := zset hχ t
  have hz : ‖z‖ ≤ 1 / 2 := by
    have he : z = ((r - 1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hne : f z ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    dsimp [z]
    norm_num
    linarith
  have hfull := iterated_logDeriv_pole_expansion_bound hχ t k hz hne
  have hfar := htail q χ hχ t r cutoff hr.le hc hscale k hk
  have hsplit : (∑ ρ ∈ S, P ρ) =
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ) +
      (∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) := by
    simpa only [not_le] using (sum_filter_add_sum_filter_not S (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff) P).symm
  have ha : ‖a‖ = (k.factorial : ℝ) := by simp [a, norm_pow]
  have hlog : 0 ≤ Real.log (Bt q t) := Real.log_nonneg (one_lt_Bt t).le
  have hp : (8 : ℝ) ^ k ≤ 1 / cutoff ^ k := by
    apply (le_div_iff₀ (pow_pos hc k)).2
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have htriangle : ‖iteratedDeriv k (logDeriv f) z -
      a * ∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ‖ ≤
      ‖iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ‖ +
        (k.factorial : ℝ) * ‖∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ‖ := by
    rw [← ha, ← norm_mul]
    convert norm_add_le (iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ)
      (a * ∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) using 1
    congr 1
    rw [hsplit]
    ring
  apply htriangle.trans
  have hb := add_le_add hfull (mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg k.factorial))
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg k.factorial) (mul_nonneg K0_pos.le hlog))
  convert add_le_add_right hh ((k.factorial : ℝ) * (C₀ * Real.log (Bt q t) / cutoff ^ k)) using 1 <;> ring
end LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 absorption of the far zero error by the Turan lower bound. -/
theorem reciprocal_pole_error_absorbed {r C massLog : ℝ} (hr : 0 < r) {k : ℕ}
    (hk : 200 * C * r * massLog ≤ (k : ℝ)) :
    C * massLog / (200 * r) ^ k ≤ 1 / (2 * (100 * r) ^ (k + 1)) := by
  have hBern := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) k
  have htwo : 200 * C * r * massLog ≤ (2 : ℝ) ^ k := by norm_num at hBern; linarith
  have he : (200 * r) ^ k = (2 : ℝ) ^ k * (100 * r) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [he, pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  convert mul_le_mul_of_nonneg_right htwo (pow_nonneg (show 0 ≤ 100 * r by positivity) k) using 1 <;> ring
end LeanLab.Linnik.Decomp1532b2

open Complex LSeries LeanLab.PNTPort.DirichletZF
open scoped LSeries.notation
namespace LeanLab.Linnik.Decomp1532b2
/-- Gallagher p.334 display 22 exact identity for each arithmetic kernel term. -/
theorem normalized_log_series_term_eq_poisson {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) (r t : ℝ) (n : ℕ) :
    ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
      LSeries.term (LSeries.logMul^[k] (↗χ * ↗ArithmeticFunction.vonMangoldt)) (1 + r + I * t) n =
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * t)) *
      (poissonKernel k (r * Real.log n) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, ArithmeticFunction.vonMangoldt_apply]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnR.le]
  rw [LSeries.term_of_ne_zero hn, logMul_iter_apply]
  simp only [Pi.mul_apply]
  have hsplit : (n : ℂ) ^ (1 + r + I * t) =
      (n : ℂ) ^ (1 + I * t) * Complex.exp ((r * Real.log n : ℝ) : ℂ) := by
    have hnr : (n : ℂ) ^ (r : ℂ) = Complex.exp ((r * Real.log n : ℝ) : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero hnC, hlog]
      congr 1
      push_cast
      ring
    rw [show (1 : ℂ) + r + I * t = (1 + I * t) + r by ring, Complex.cpow_add _ _ hnC, hnr]
  rw [hsplit, hlog]
  unfold poissonKernel
  push_cast
  rw [Complex.exp_neg]
  field_simp
  <;> ring

/-- Gallagher p.334 display 22 exact arithmetic kernel identity. -/
theorem normalized_log_series_eq_poisson {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) (r t : ℝ) :
    ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
      LSeries (LSeries.logMul^[k] (↗χ * ↗ArithmeticFunction.vonMangoldt)) (1 + r + I * t) =
    ∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * t)) *
      (poissonKernel k (r * Real.log n) : ℂ) := by
  rw [LSeries, ← tsum_mul_left]
  exact tsum_congr (normalized_log_series_term_eq_poisson χ k r t)

/-- Gallagher p.334 display 22 the kernel series is absolutely convergent for positive smoothing. -/
theorem summable_poisson_twist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Summable (fun n : ℕ => (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
      (n : ℂ) ^ (1 + I * t)) * (poissonKernel k (r * Real.log n) : ℂ)) := by
  have hconv : LSeries.abscissaOfAbsConv (↗χ * ↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simpa using hy)
  have hs : 1 < (1 + (r : ℂ) + I * t).re := by norm_num; linarith
  have hconv' : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] (↗χ * ↗ArithmeticFunction.vonMangoldt)) <
      (1 + (r : ℂ) + I * t).re := by
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact hconv.trans_lt (by exact_mod_cast hs)
  have hh := (LSeriesSummable_of_abscissaOfAbsConv_lt_re hconv').mul_left
    (((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
  exact hh.congr (normalized_log_series_term_eq_poisson χ k r t)
end LeanLab.Linnik.Decomp1532b2
