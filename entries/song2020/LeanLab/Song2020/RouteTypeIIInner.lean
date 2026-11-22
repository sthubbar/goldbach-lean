module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-!
AI wrote the Lean code, 2026-11-15, the inner sum over
r of the Type II bound.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed page 7: "By Cor.
8.13 in [3], we have sum over r in I of e(R_b(r(s+l)) - R_b(r s)) << R^(1/2)
x^(gamma/2-3/2) y |hl|^(1/2) + x^(1/2-gamma/2) R^(1/2) |hl|^(-1/2)".
This file proves the statement of the leaf SPLIT_typeII_per_RS.inner_vdc, with the lab's
proved discrete van der Corput second derivative test
BakerHarmanPintz1997.PortedVanDerCorput.vdC_second_derivative in the place of Iwaniec and
Kowalski Corollary 8.13. The phase is g(r) = alpha l r + h r^gamma ((s+l)^gamma - s^gamma),
its second difference has size |h| l (R S)^(gamma-1) / R, and the set I of r is a run of
consecutive integers of length at most 2 y / S + 1. Reading as in the split file: x of the
print is R S. The private lemmas rpow_first_diff, second_diff_bounds, eC_eq_eK, eK_neg and
convex_finset_eq_Ioc are copied from RouteVaughanInner, where they are private. The file
defines nothing.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteTypeIIInner

open LeanLab.Song2020 LeanLab.Song2020.State1562
open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-- Song 2020, page 7, "g''(r) of size x^(gamma-1) |hl| / R", first half: the first
difference of t^(gamma-1) over a step d lies between (gamma-1) d x^(gamma-2) and
(gamma-1) d (x+d)^(gamma-2), by the mean value inequality. -/
private theorem rpow_first_diff (γ : ℝ) (hγ1 : γ < 1) (x d : ℝ) (hx : 0 < x)
    (hd : 0 < d) :
    (γ - 1) * x ^ (γ - 2) * d ≤ (x + d) ^ (γ - 1) - x ^ (γ - 1) ∧
      (x + d) ^ (γ - 1) - x ^ (γ - 1) ≤ (γ - 1) * (x + d) ^ (γ - 2) * d := by
  have hD : Convex ℝ (Set.Icc x (x + d)) := convex_Icc _ _
  have hcont : ContinuousOn (fun t : ℝ => t ^ (γ - 1)) (Set.Icc x (x + d)) := fun t ht =>
    (Real.continuousAt_rpow_const t (γ - 1)
      (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ (γ - 1))
      (interior (Set.Icc x (x + d))) := fun t ht => by
    rw [interior_Icc] at ht
    exact (Real.differentiableAt_rpow_const_of_ne (γ - 1)
      (by linarith [ht.1] : t ≠ 0)).differentiableWithinAt
  have hder : ∀ t ∈ interior (Set.Icc x (x + d)),
      deriv (fun t : ℝ => t ^ (γ - 1)) t = (γ - 1) * t ^ (γ - 2) := fun t ht => by
    rw [interior_Icc] at ht
    have h := (Real.hasDerivAt_rpow_const (p := γ - 1)
      (Or.inl (by linarith [ht.1] : t ≠ 0))).deriv
    rw [h]
    congr 2; ring
  have hxm : x ∈ Set.Icc x (x + d) := ⟨le_rfl, by linarith⟩
  have hym : x + d ∈ Set.Icc x (x + d) := ⟨by linarith, le_rfl⟩
  have hsub : x + d - x = d := by ring
  constructor
  · have h := hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff (C := (γ - 1) * x ^ (γ - 2))
      (fun t ht => by
        rw [hder t ht]
        rw [interior_Icc] at ht
        have : t ^ (γ - 2) ≤ x ^ (γ - 2) :=
          Real.rpow_le_rpow_of_nonpos hx ht.1.le (by linarith)
        nlinarith) x hxm (x + d) hym (by linarith)
    rw [hsub] at h
    exact h
  · have h := hD.image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (C := (γ - 1) * (x + d) ^ (γ - 2))
      (fun t ht => by
        rw [hder t ht]
        rw [interior_Icc] at ht
        have : (x + d) ^ (γ - 2) ≤ t ^ (γ - 2) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) ht.2.le (by linarith)
        nlinarith) x hxm (x + d) hym (by linarith)
    rw [hsub] at h
    exact h

/-- Song 2020, page 7, "g''(r) of size x^(gamma-1) |hl| / R": the second difference of
the concave power t^gamma with step d at the point a, taken with the sign that makes it
positive, lies between gamma (1-gamma) d^2 (a+2d)^(gamma-2) and
gamma (1-gamma) d^2 a^(gamma-2). -/
private theorem second_diff_bounds (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (a d : ℝ)
    (ha : 0 < a) (hd : 0 < d) :
    γ * (1 - γ) * d ^ 2 * (a + 2 * d) ^ (γ - 2) ≤
        2 * (a + d) ^ γ - a ^ γ - (a + 2 * d) ^ γ ∧
      2 * (a + d) ^ γ - a ^ γ - (a + 2 * d) ^ γ ≤ γ * (1 - γ) * d ^ 2 * a ^ (γ - 2) := by
  have hD : Convex ℝ (Set.Icc a (a + d)) := convex_Icc _ _
  have hda : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ => (t + d) ^ γ - t ^ γ)
        (γ * ((t + d) ^ (γ - 1) - t ^ (γ - 1))) t := fun t ht => by
    have h1 : HasDerivAt (fun t : ℝ => (t + d) ^ γ) (1 * γ * (t + d) ^ (γ - 1)) t :=
      ((hasDerivAt_id' t).add_const d).rpow_const (Or.inl (by linarith))
    have h2 : HasDerivAt (fun t : ℝ => t ^ γ) (1 * γ * t ^ (γ - 1)) t :=
      (hasDerivAt_id' t).rpow_const (Or.inl (by linarith))
    have h3 := h1.sub h2
    convert h3 using 1
    ring
  have hcont : ContinuousOn (fun t : ℝ => (t + d) ^ γ - t ^ γ) (Set.Icc a (a + d)) :=
    fun t ht => (hda t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => (t + d) ^ γ - t ^ γ)
      (interior (Set.Icc a (a + d))) := fun t ht => by
    rw [interior_Icc] at ht
    exact (hda t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
  have hxm : a ∈ Set.Icc a (a + d) := ⟨le_rfl, by linarith⟩
  have hym : a + d ∈ Set.Icc a (a + d) := ⟨by linarith, le_rfl⟩
  have hsub : a + d - a = d := by ring
  have hadd : a + d + d = a + 2 * d := by ring
  have hA : 0 < γ * (1 - γ) := mul_pos hγ0 (by linarith)
  constructor
  · have h := hD.image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (C := γ * (γ - 1) * d * (a + 2 * d) ^ (γ - 2))
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hda t (by linarith [ht.1])).deriv]
        have h1 := (rpow_first_diff γ hγ1 t d (by linarith [ht.1]) hd).2
        have h2 : (a + 2 * d) ^ (γ - 2) ≤ (t + d) ^ (γ - 2) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) (by linarith [ht.2])
            (by linarith)
        have h3 : γ * ((t + d) ^ (γ - 1) - t ^ (γ - 1)) ≤
            γ * ((γ - 1) * (t + d) ^ (γ - 2) * d) := mul_le_mul_of_nonneg_left h1 hγ0.le
        have h4 : γ * (1 - γ) * d * (a + 2 * d) ^ (γ - 2) ≤
            γ * (1 - γ) * d * (t + d) ^ (γ - 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith) a hxm (a + d) hym (by linarith)
    rw [hsub] at h
    simp only [hadd] at h
    nlinarith
  · have h := hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff
      (C := γ * (γ - 1) * d * a ^ (γ - 2))
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hda t (by linarith [ht.1])).deriv]
        have h1 := (rpow_first_diff γ hγ1 t d (by linarith [ht.1]) hd).1
        have h2 : t ^ (γ - 2) ≤ a ^ (γ - 2) :=
          Real.rpow_le_rpow_of_nonpos ha ht.1.le (by linarith)
        have h3 : γ * ((γ - 1) * t ^ (γ - 2) * d) ≤
            γ * ((t + d) ^ (γ - 1) - t ^ (γ - 1)) := mul_le_mul_of_nonneg_left h1 hγ0.le
        have h4 : γ * (1 - γ) * d * t ^ (γ - 2) ≤ γ * (1 - γ) * d * a ^ (γ - 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith) a hxm (a + d) hym (by linarith)
    rw [hsub] at h
    simp only [hadd] at h
    nlinarith

/-- Song 2020, page 7, the phase e(R_b(r s)): the lab's two additive characters agree. -/
private theorem eC_eq_eK (x : ℝ) : eC x = eK x := by
  unfold eC eK
  congr 1
  push_cast
  ring

/-- Song 2020, page 7, the phase e(R_b(r s)): negating the phase conjugates the
character, which is how the case h > 0 is brought to a convex phase. -/
private theorem eK_neg (x : ℝ) : eK (-x) = (starRingEnd ℂ) (eK x) := by
  unfold eK
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Song 2020, page 7, the interval I of r: a nonempty set of
positive integers closed under taking intermediate integers is an interval Ioc a b, so the
van der Corput estimate for consecutive integers applies to it. -/
private theorem convex_finset_eq_Ioc (T : Finset ℕ) (hne : T.Nonempty)
    (hpos : ∀ s ∈ T, 1 ≤ s)
    (hconv : ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s, s₁ ≤ s → s ≤ s₂ → s ∈ T) :
    ∃ a b : ℕ, a < b ∧ T = Finset.Ioc a b ∧ a + 1 ∈ T ∧ b ∈ T := by
  have h1 := hpos _ (T.min'_mem hne)
  have h2 : T.min' hne ≤ T.max' hne := T.min'_le _ (T.max'_mem hne)
  refine ⟨T.min' hne - 1, T.max' hne, by omega, ?_, ?_, T.max'_mem hne⟩
  · ext s
    rw [Finset.mem_Ioc]
    constructor
    · intro hs
      exact ⟨by have := T.min'_le s hs; omega, T.le_max' s hs⟩
    · intro hs
      exact hconv _ (T.min'_mem hne) _ (T.max'_mem hne) s (by omega) hs.2
  · have : T.min' hne - 1 + 1 = T.min' hne := by omega
    rw [this]
    exact T.min'_mem hne

/-- Song 2020, page 7, the size of the coefficient (s+l)^gamma - s^gamma of r^gamma in
g(r): by the mean value inequality for the concave power t^gamma it lies between
gamma d (x+d)^(gamma-1) and gamma d x^(gamma-1). -/
private theorem rpow_gamma_diff (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (x d : ℝ) (hx : 0 < x)
    (hd : 0 < d) :
    γ * (x + d) ^ (γ - 1) * d ≤ (x + d) ^ γ - x ^ γ ∧
      (x + d) ^ γ - x ^ γ ≤ γ * x ^ (γ - 1) * d := by
  have hD : Convex ℝ (Set.Icc x (x + d)) := convex_Icc _ _
  have hcont : ContinuousOn (fun t : ℝ => t ^ γ) (Set.Icc x (x + d)) := fun t ht =>
    (Real.continuousAt_rpow_const t γ
      (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ γ)
      (interior (Set.Icc x (x + d))) := fun t ht => by
    rw [interior_Icc] at ht
    exact (Real.differentiableAt_rpow_const_of_ne γ
      (by linarith [ht.1] : t ≠ 0)).differentiableWithinAt
  have hder : ∀ t ∈ interior (Set.Icc x (x + d)),
      deriv (fun t : ℝ => t ^ γ) t = γ * t ^ (γ - 1) := fun t ht => by
    rw [interior_Icc] at ht
    exact (Real.hasDerivAt_rpow_const (p := γ)
      (Or.inl (by linarith [ht.1] : t ≠ 0))).deriv
  have hxm : x ∈ Set.Icc x (x + d) := ⟨le_rfl, by linarith⟩
  have hym : x + d ∈ Set.Icc x (x + d) := ⟨by linarith, le_rfl⟩
  have hsub : x + d - x = d := by ring
  constructor
  · have h := hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff (C := γ * (x + d) ^ (γ - 1))
      (fun t ht => by
        rw [hder t ht]
        rw [interior_Icc] at ht
        have : (x + d) ^ (γ - 1) ≤ t ^ (γ - 1) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) ht.2.le (by linarith)
        nlinarith) x hxm (x + d) hym (by linarith)
    rw [hsub] at h
    exact h
  · have h := hD.image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (C := γ * x ^ (γ - 1))
      (fun t ht => by
        rw [hder t ht]
        rw [interior_Icc] at ht
        have : t ^ (γ - 1) ≤ x ^ (γ - 1) :=
          Real.rpow_le_rpow_of_nonpos hx ht.1.le (by linarith)
        nlinarith) x hxm (x + d) hym (by linarith)
    rw [hsub] at h
    exact h

/-- Song 2020, page 7, the phase g(r) = R_b(r(s+l)) - R_b(r s) = alpha l r +
h r^gamma ((s+l)^gamma - s^gamma): for either sign of h the modulus of the sum of e(g(r))
equals that of a sum with the convex phase beta r - |h| ((s+l)^gamma - s^gamma) r^gamma,
by conjugation when h is positive. -/
private theorem phase_flip (γ α : ℝ) (h : ℤ) (hh : h ≠ 0) (s l : ℕ) :
    ∃ β : ℝ, ∀ T : Finset ℕ,
      ‖∑ r ∈ T, eC ((α * ((r * (s + l) : ℕ) : ℝ) + h * ((r * (s + l) : ℕ) : ℝ) ^ γ) -
          (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ))‖ =
        ‖∑ r ∈ T, eK (β * r - |(h : ℝ)| * (((s + l : ℕ) : ℝ) ^ γ - (s : ℝ) ^ γ) *
          (r : ℝ) ^ γ)‖ := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have e := Nat.cast_add (R := ℝ) s l
  rcases lt_or_gt_of_ne hh' with hneg | hpos
  · refine ⟨α * l, fun T => ?_⟩
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [eC_eq_eK, abs_of_neg hneg]
    congr 1
    rw [Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    linear_combination (α * r) * e
  · refine ⟨-(α * l), fun T => ?_⟩
    rw [← RCLike.norm_conj (K := ℂ) (∑ r ∈ T, eK (-(α * l) * r - |(h : ℝ)| *
      (((s + l : ℕ) : ℝ) ^ γ - (s : ℝ) ^ γ) * (r : ℝ) ^ γ)), map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [eC_eq_eK, ← eK_neg, abs_of_pos hpos]
    congr 1
    rw [Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    linear_combination (α * r) * e

/-- Song 2020, page 7, "By Cor. 8.13 in [3]" with g''(r) of size x^(gamma-1) |hl| / R, on
a run of consecutive r with R <= r < 2R: the lab's discrete second derivative test with
lam = K gamma (1-gamma) R^(gamma-2) / 9 and c = 9, where K stands for
|h| ((s+l)^gamma - s^gamma). The three points r, r+1, r+2 lie in [R, 3R). -/
private theorem run_vdC (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (K : ℝ) (hK : 0 < K)
    (β R : ℝ) (hR : 1 ≤ R) (a b : ℕ) (hab : a ≤ b) (ha : R ≤ (a : ℝ) + 1)
    (hb : (b : ℝ) < 2 * R) :
    ‖∑ r ∈ Finset.Ioc a b, eK (β * r - K * (r : ℝ) ^ γ)‖ ≤
      8 * (9 * ((b : ℝ) - a) * Real.sqrt (K * (γ * (1 - γ)) * R ^ (γ - 2) / 9) +
        1 / Real.sqrt (K * (γ * (1 - γ)) * R ^ (γ - 2) / 9)) := by
  have hA : 0 < γ * (1 - γ) := mul_pos hγ0 (by linarith)
  have hR0 : 0 < R := by linarith
  have hRp : 0 < R ^ (γ - 2) := Real.rpow_pos_of_pos hR0 _
  have h19 : (1 : ℝ) / 9 ≤ (3 : ℝ) ^ (γ - 2) := by
    have e : (3 : ℝ) ^ (-2 : ℝ) = 1 / 9 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
    rw [← e]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hbd : ∀ m : ℕ, a < m → m < b →
      K * (γ * (1 - γ)) * R ^ (γ - 2) / 9 ≤
          K * (2 * ((m : ℝ) + 1) ^ γ - (m : ℝ) ^ γ - ((m : ℝ) + 2 * 1) ^ γ) ∧
        K * (2 * ((m : ℝ) + 1) ^ γ - (m : ℝ) ^ γ - ((m : ℝ) + 2 * 1) ^ γ) ≤
          9 * (K * (γ * (1 - γ)) * R ^ (γ - 2) / 9) := by
    intro m h1 h2
    have hm1 : (a : ℝ) + 1 ≤ m := by exact_mod_cast h1
    have hm2 : (m : ℝ) + 1 ≤ b := by exact_mod_cast h2
    have hm0 : (0 : ℝ) < m := by linarith
    have hsd := second_diff_bounds γ hγ0 hγ1 (m : ℝ) 1 hm0 one_pos
    rw [one_pow, mul_one] at hsd
    have hlow : (1 : ℝ) / 9 * R ^ (γ - 2) ≤ ((m : ℝ) + 2 * 1) ^ (γ - 2) := by
      have e1 : (3 * R) ^ (γ - 2) ≤ ((m : ℝ) + 2 * 1) ^ (γ - 2) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) hR0.le] at e1
      exact (mul_le_mul_of_nonneg_right h19 hRp.le).trans e1
    have hup : (m : ℝ) ^ (γ - 2) ≤ R ^ (γ - 2) :=
      Real.rpow_le_rpow_of_nonpos hR0 (by linarith) (by linarith)
    have hc : 0 ≤ K * (γ * (1 - γ)) := by positivity
    have l1 := mul_le_mul_of_nonneg_left hlow hc
    have l2 := mul_le_mul_of_nonneg_left hup hc
    have l3 := mul_le_mul_of_nonneg_left hsd.1 hK.le
    have l4 := mul_le_mul_of_nonneg_left hsd.2 hK.le
    constructor
    · calc K * (γ * (1 - γ)) * R ^ (γ - 2) / 9
          = K * (γ * (1 - γ)) * (1 / 9 * R ^ (γ - 2)) := by ring
        _ ≤ K * (γ * (1 - γ)) * ((m : ℝ) + 2 * 1) ^ (γ - 2) := l1
        _ = K * (γ * (1 - γ) * ((m : ℝ) + 2 * 1) ^ (γ - 2)) := by ring
        _ ≤ _ := l3
    · calc K * (2 * ((m : ℝ) + 1) ^ γ - (m : ℝ) ^ γ - ((m : ℝ) + 2 * 1) ^ γ)
          ≤ K * (γ * (1 - γ) * (m : ℝ) ^ (γ - 2)) := l4
        _ = K * (γ * (1 - γ)) * (m : ℝ) ^ (γ - 2) := by ring
        _ ≤ K * (γ * (1 - γ)) * R ^ (γ - 2) := l2
        _ = _ := by ring
  have hcast : ∀ m : ℕ,
      (β * ((m + 1 + 1 : ℕ) : ℝ) - K * ((m + 1 + 1 : ℕ) : ℝ) ^ γ -
          (β * ((m + 1 : ℕ) : ℝ) - K * ((m + 1 : ℕ) : ℝ) ^ γ)) -
        (β * ((m + 1 : ℕ) : ℝ) - K * ((m + 1 : ℕ) : ℝ) ^ γ -
          (β * (m : ℝ) - K * (m : ℝ) ^ γ)) =
      K * (2 * ((m : ℝ) + 1) ^ γ - (m : ℝ) ^ γ - ((m : ℝ) + 2 * 1) ^ γ) := by
    intro m
    have e1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have e2 : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 * 1 := by push_cast; ring
    rw [e1, e2]
    ring
  exact vdC_second_derivative
    (f := fun r : ℕ => β * (r : ℝ) - K * (r : ℝ) ^ γ) (a := a) (b := b)
    (lam := K * (γ * (1 - γ)) * R ^ (γ - 2) / 9) (c := 9) hab (by positivity) (by norm_num)
    (fun m h1 h2 => by
      have := (hbd m h1 h2).1
      rw [← hcast m] at this
      exact this)
    (fun m h1 h2 => by
      have := (hbd m h1 h2).2
      rw [← hcast m] at this
      exact this)

/-- Song 2020, page 7, the two terms of the display after Cor. 8.13: with
X = R^(-1/2) x^((gamma-1)/2) |hl|^(1/2) and Y = R^(1/2) x^((1-gamma)/2) |hl|^(-1/2),
x = R S, one has X Y = 1 and X^2 = |hl| x^(gamma-1) / R, the size of g''(r). -/
private theorem two_terms (γ R S M : ℝ) (hR : 0 < R) (hS : 0 < S) (hM : 0 < M) :
    0 < R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) * M ^ ((1 : ℝ) / 2) ∧
    (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) * M ^ ((1 : ℝ) / 2)) *
        (R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * M ^ (-(1 : ℝ) / 2)) = 1 ∧
    (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) * M ^ ((1 : ℝ) / 2)) ^ 2 =
        M * S ^ (γ - 1) * R ^ (γ - 2) := by
  have hRS : 0 < R * S := mul_pos hR hS
  refine ⟨by positivity, ?_, ?_⟩
  · have e1 : R ^ (-(1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hR]; norm_num
    have e2 : (R * S) ^ ((γ - 1) / 2) * (R * S) ^ ((1 - γ) / 2) = 1 := by
      rw [← Real.rpow_add hRS]
      rw [show (γ - 1) / 2 + (1 - γ) / 2 = 0 by ring, Real.rpow_zero]
    have e3 : M ^ ((1 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hM]; norm_num
    calc _ = (R ^ (-(1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2)) *
          ((R * S) ^ ((γ - 1) / 2) * (R * S) ^ ((1 - γ) / 2)) *
          (M ^ ((1 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2)) := by ring
      _ = 1 := by rw [e1, e2, e3]; norm_num
  · have e1 : R ^ (-(1 : ℝ) / 2) * R ^ (-(1 : ℝ) / 2) = R ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hR]; norm_num
    have e2 : (R * S) ^ ((γ - 1) / 2) * (R * S) ^ ((γ - 1) / 2) =
        R ^ (γ - 1) * S ^ (γ - 1) := by
      rw [← Real.rpow_add hRS, ← Real.mul_rpow hR.le hS.le]
      congr 1; ring
    have e3 : M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) = M := by
      rw [← Real.rpow_add hM]; norm_num
    have e4 : R ^ (γ - 2) = R ^ (γ - 1) * R ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hR]; congr 1; ring
    calc _ = (R ^ (-(1 : ℝ) / 2) * R ^ (-(1 : ℝ) / 2)) *
          ((R * S) ^ ((γ - 1) / 2) * (R * S) ^ ((γ - 1) / 2)) *
          (M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)) := by ring
      _ = _ := by rw [e1, e2, e3, e4]; ring

set_option maxHeartbeats 1600000 in
/-- Song 2020, page 7, "By Cor. 8.13 in [3], we have sum over r in I of
e(R_b(r(s+l)) - R_b(r s)) << R^(1/2) x^(gamma/2-3/2) y |hl|^(1/2) + x^(1/2-gamma/2) R^(1/2)
|hl|^(-1/2)": the statement of the leaf SPLIT_typeII_per_RS.inner_vdc, proved from the
lab's discrete second derivative test, with C = 144 + 8 / sqrt(gamma^2 (1-gamma) / 18). -/
theorem inner_vdc_route :
    ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : ℝ), 0 < y → ∀ (α t : ℝ)
      (h : ℤ), h ≠ 0 → ∀ R S : ℝ, 1 ≤ R → 1 ≤ S → ∀ l s : ℕ, 1 ≤ l → S ≤ (s : ℝ) →
        ((s + l : ℕ) : ℝ) < 2 * S →
          ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              if (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) ∧
                  (|((r * (s + l) : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧
                    ((r * (s + l) : ℕ) : ℝ) ≤ t) then
                eC ((α * ((r * (s + l) : ℕ) : ℝ) + h * ((r * (s + l) : ℕ) : ℝ) ^ γ) -
                  (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ))
              else 0‖ ≤
            C * ((y / S + 1) * (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
                (|(h : ℝ)| * l) ^ ((1 : ℝ) / 2)) +
              R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) *
                (|(h : ℝ)| * l) ^ (-(1 : ℝ) / 2)) := by
  intro γ hγ0 hγ1
  have hκ : 0 < γ ^ 2 * (1 - γ) / 18 := by
    have : 0 < 1 - γ := by linarith
    positivity
  refine ⟨144 + 8 / Real.sqrt (γ ^ 2 * (1 - γ) / 18), by positivity, ?_⟩
  intro n y hy α t h hh R S hR hS l s hl hsS hslS
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hs0 : (0 : ℝ) < s := by linarith
  have hsnat : 1 ≤ s := by exact_mod_cast hs0
  have hH : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
  have hM : 0 < |(h : ℝ)| * l := mul_pos hH hl0
  obtain ⟨hX0, hXY, hXX⟩ := two_terms γ R S (|(h : ℝ)| * l) hR0 hS0 hM
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
      (|(h : ℝ)| * l) ^ ((1 : ℝ) / 2) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) *
      (|(h : ℝ)| * l) ^ (-(1 : ℝ) / 2) := ⟨_, rfl⟩
  rw [← hXdef, ← hYdef] at hXY
  rw [← hXdef] at hX0 hXX
  rw [← hXdef, ← hYdef]
  have hY0 : 0 < Y := by
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos hX0.le (not_lt.mp hc)
    linarith
  rw [← Finset.sum_filter]
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T =
      ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R)).filter
        (fun r : ℕ => (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) ∧
          (|((r * (s + l) : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * (s + l) : ℕ) : ℝ) ≤ t)) :=
    ⟨_, rfl⟩
  rw [← hT]
  have hmem : ∀ r, r ∈ T ↔ (r < Nat.ceil ((n : ℝ) / 3 + y) + 1 ∧
      (R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R)) ∧
      ((|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) ∧
        (|((r * (s + l) : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * (s + l) : ℕ) : ℝ) ≤ t)) := by
    intro r; rw [hT, Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
  obtain ⟨β, hβ⟩ := phase_flip γ α h hh s l
  rw [hβ]
  have hpos : 0 ≤ (144 + 8 / Real.sqrt (γ ^ 2 * (1 - γ) / 18)) * ((y / S + 1) * X + Y) := by
    positivity
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, norm_zero]
    exact hpos
  have hconv : ∀ r₁ ∈ T, ∀ r₂ ∈ T, ∀ r, r₁ ≤ r → r ≤ r₂ → r ∈ T := by
    intro r1 h1 r2 h2 r h1r hr2
    obtain ⟨⟨p1, p2, p3⟩, ⟨p4, p5⟩, p6, p7⟩ := (hmem r1).mp h1
    obtain ⟨⟨q1, q2, q3⟩, ⟨q4, q5⟩, q6, q7⟩ := (hmem r2).mp h2
    have c0 : (r1 : ℝ) ≤ r := by exact_mod_cast h1r
    have c0' : (r : ℝ) ≤ r2 := by exact_mod_cast hr2
    have c1 : ((r1 * s : ℕ) : ℝ) ≤ ((r * s : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right s h1r
    have c2 : ((r * s : ℕ) : ℝ) ≤ ((r2 * s : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right s hr2
    have c3 : ((r1 * (s + l) : ℕ) : ℝ) ≤ ((r * (s + l) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right (s + l) h1r
    have c4 : ((r * (s + l) : ℕ) : ℝ) ≤ ((r2 * (s + l) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right (s + l) hr2
    rw [abs_lt] at p4 p6 q4 q6
    refine (hmem r).mpr ⟨⟨by omega, by linarith, by linarith⟩, ⟨?_, by linarith⟩, ?_,
      by linarith⟩
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith
  have hr1 : ∀ r ∈ T, 1 ≤ r := by
    intro r hr
    have := ((hmem r).mp hr).1.2.1
    have : (1 : ℝ) ≤ r := by linarith
    exact_mod_cast this
  obtain ⟨a, b, hab, hTab, ha, hb⟩ := convex_finset_eq_Ioc T hne hr1 hconv
  obtain ⟨⟨_, pa2, _⟩, ⟨pa4, _⟩, _, _⟩ := (hmem _).mp ha
  obtain ⟨⟨_, _, pb3⟩, ⟨pb4, _⟩, _, _⟩ := (hmem _).mp hb
  rw [hTab]
  -- the coefficient D = (s+l)^gamma - s^gamma
  have hsl : ((s + l : ℕ) : ℝ) = (s : ℝ) + l := by push_cast; ring
  obtain ⟨hD1, hD2⟩ := rpow_gamma_diff γ hγ0 hγ1 (s : ℝ) l hs0 hl0
  rw [← hsl] at hD1 hD2
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ((s + l : ℕ) : ℝ) ^ γ - (s : ℝ) ^ γ := ⟨_, rfl⟩
  rw [← hDdef] at hD1 hD2 ⊢
  have hSp : 0 < S ^ (γ - 1) := Real.rpow_pos_of_pos hS0 _
  have hDup : D ≤ γ * S ^ (γ - 1) * l := by
    have : (s : ℝ) ^ (γ - 1) ≤ S ^ (γ - 1) :=
      Real.rpow_le_rpow_of_nonpos hS0 hsS (by linarith)
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hγ0.le hl0.le)
    linarith
  have hDlo : γ * S ^ (γ - 1) * l / 2 ≤ D := by
    have e1 : (2 * S) ^ (γ - 1) ≤ ((s + l : ℕ) : ℝ) ^ (γ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by rw [hsl]; positivity) hslS.le (by linarith)
    rw [Real.mul_rpow (by norm_num) hS0.le] at e1
    have e2 : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (γ - 1) := by
      have e : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
        rw [Real.rpow_neg_one]; norm_num
      rw [← e]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have e3 := mul_le_mul_of_nonneg_right e2 hSp.le
    have e4 : S ^ (γ - 1) / 2 ≤ ((s + l : ℕ) : ℝ) ^ (γ - 1) := by linarith
    have := mul_le_mul_of_nonneg_left e4 (mul_nonneg hγ0.le hl0.le)
    linarith
  have hD0 : 0 < D := by
    have : 0 < γ * S ^ (γ - 1) * l / 2 := by positivity
    linarith
  have hv := run_vdC γ hγ0 hγ1 (|(h : ℝ)| * D) (mul_pos hH hD0) β R hR a b hab.le
    (by push_cast at pa2; exact pa2) pb3
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = |(h : ℝ)| * D * (γ * (1 - γ)) * R ^ (γ - 2) / 9 :=
    ⟨_, rfl⟩
  rw [← hlam] at hv
  have hRp : 0 < R ^ (γ - 2) := Real.rpow_pos_of_pos hR0 _
  have hg1 : 0 < 1 - γ := by linarith
  have hc : 0 ≤ |(h : ℝ)| * (γ * (1 - γ)) * R ^ (γ - 2) / 9 := by positivity
  have hlam_up : lam ≤ X ^ 2 := by
    rw [hXX, hlam]
    have h1 := mul_le_mul_of_nonneg_left hDup hc
    have h2 : γ ^ 2 * (1 - γ) / 9 ≤ 1 := by
      have e1 : γ ^ 2 ≤ 1 := by nlinarith
      have e2 : γ ^ 2 * (1 - γ) ≤ 1 * 1 := mul_le_mul e1 (by linarith) hg1.le (by norm_num)
      linarith
    have h3 : 0 ≤ |(h : ℝ)| * l * S ^ (γ - 1) * R ^ (γ - 2) := by positivity
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    linarith only [h1, h4]
  have hlam_lo : γ ^ 2 * (1 - γ) / 18 * X ^ 2 ≤ lam := by
    rw [hXX, hlam]
    have h1 := mul_le_mul_of_nonneg_left hDlo hc
    linarith only [h1]
  have hlam0 : 0 < lam := by
    have : 0 < γ ^ 2 * (1 - γ) / 18 * X ^ 2 := by positivity
    linarith
  have hsq_up : Real.sqrt lam ≤ X := by
    have := Real.sqrt_le_sqrt hlam_up
    rwa [Real.sqrt_sq hX0.le] at this
  have hsq_lo : Real.sqrt (γ ^ 2 * (1 - γ) / 18) * X ≤ Real.sqrt lam := by
    have := Real.sqrt_le_sqrt hlam_lo
    rwa [Real.sqrt_mul hκ.le, Real.sqrt_sq hX0.le] at this
  have hsκ : 0 < Real.sqrt (γ ^ 2 * (1 - γ) / 18) := Real.sqrt_pos.mpr hκ
  have hinv : 1 / Real.sqrt lam ≤ Y / Real.sqrt (γ ^ 2 * (1 - γ) / 18) := by
    have h1 := one_div_le_one_div_of_le (mul_pos hsκ hX0) hsq_lo
    have h2 : 1 / (Real.sqrt (γ ^ 2 * (1 - γ) / 18) * X) =
        Y / Real.sqrt (γ ^ 2 * (1 - γ) / 18) := by
      rw [div_eq_div_iff (ne_of_gt (mul_pos hsκ hX0)) (ne_of_gt hsκ)]
      linear_combination (-Real.sqrt (γ ^ 2 * (1 - γ) / 18)) * hXY
    linarith
  -- the length of the run
  have hcnt : (b : ℝ) - a ≤ 2 * (y / S + 1) := by
    have h1 := (abs_lt.mp pa4).1
    have h2 := (abs_lt.mp pb4).2
    push_cast at h1 h2
    have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    have h3 : ((b : ℝ) - a - 1) * S ≤ ((b : ℝ) - a - 1) * s :=
      mul_le_mul_of_nonneg_left hsS (by linarith)
    have h4 : ((b : ℝ) - a - 1) * S < 2 * y := by linarith only [h1, h2, h3]
    have h5 : (b : ℝ) - a - 1 < 2 * y / S := by
      rw [lt_div_iff₀ hS0]; exact h4
    have h6 : 2 * y / S = 2 * (y / S) := by ring
    linarith
  have hsl0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hyS : 0 ≤ y / S + 1 := by positivity
  have hmain : 9 * ((b : ℝ) - a) * Real.sqrt lam ≤ 18 * ((y / S + 1) * X) := by
    calc 9 * ((b : ℝ) - a) * Real.sqrt lam = 9 * (((b : ℝ) - a) * Real.sqrt lam) := by ring
      _ ≤ 9 * ((2 * (y / S + 1)) * X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hcnt hsq_up hsl0 (by positivity))
            (by norm_num)
      _ = _ := by ring
  have hfin : (144 + 8 / Real.sqrt (γ ^ 2 * (1 - γ) / 18)) * ((y / S + 1) * X + Y) =
      8 * (18 * ((y / S + 1) * X) + Y / Real.sqrt (γ ^ 2 * (1 - γ) / 18)) +
        (8 / Real.sqrt (γ ^ 2 * (1 - γ) / 18)) * ((y / S + 1) * X) + 144 * Y := by ring
  have hextra : 0 ≤ (8 / Real.sqrt (γ ^ 2 * (1 - γ) / 18)) * ((y / S + 1) * X) + 144 * Y := by
    positivity
  rw [mul_assoc] at hv
  linarith only [hv, hmain, hinv, hfin, hextra]

end LeanLab.Song2020.RouteTypeIIInner
