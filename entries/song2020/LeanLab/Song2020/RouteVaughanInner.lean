module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-!
AI wrote the Lean code, 2026-11-15, the inner sum of Sigma 1.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed page 6: "Let
f(s) = R_b(r s), and noting that r s ~ n and f''(s) is of size r^2 n^(gamma-2) |h|. And
applying the van der Corput's estimate in [3] (Cor. 8.13) to f(s) in the inner sum".
This file proves the statement of the leaf RouteVaughanSigma1.inner_sum_bound, with the
lab's proved discrete van der Corput second derivative test
BakerHarmanPintz1997.PortedVanDerCorput.vdC_second_derivative in the place of Iwaniec and
Kowalski Corollary 8.13. The s range is cut into the dyadic blocks 2^j <= s < 2^(j+1); the
number of blocks, at most log n / log 2 + 1, is carried by the factor n^epsilon. It defines
nothing.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteVaughanInner

open LeanLab.Song2020 LeanLab.Song2020.State1562
open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-- Song 2020, page 6, "f''(s) is of size r^2 n^(gamma-2) |h|", first half: the first
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

/-- Song 2020, page 6, "f''(s) is of size r^2 n^(gamma-2) |h|": the second difference of
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

/-- Song 2020, page 6, the phase e(R_b(r s)): the lab's two additive characters agree. -/
private theorem eC_eq_eK (x : ℝ) : eC x = eK x := by
  unfold eC eK
  congr 1
  push_cast
  ring

/-- Song 2020, page 6, the phase e(R_b(r s)): negating the phase conjugates the
character, which is how the case h > 0 is brought to a convex phase. -/
private theorem eK_neg (x : ℝ) : eK (-x) = (starRingEnd ℂ) (eK x) := by
  unfold eK
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Song 2020, page 6, "Let f(s) = R_b(r s)": for either sign of h the modulus of the sum
of e(alpha r s + h (r s)^gamma) equals that of a sum with the convex phase
beta s - |h| (r s)^gamma, by conjugation when h is positive. -/
private theorem phase_flip (γ α : ℝ) (h : ℤ) (hh : h ≠ 0) (r : ℕ) :
    ∃ β : ℝ, ∀ T : Finset ℕ,
      ‖∑ s ∈ T, eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)‖ =
        ‖∑ s ∈ T, eK (β * s - |(h : ℝ)| * ((r * s : ℕ) : ℝ) ^ γ)‖ := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  rcases lt_or_gt_of_ne hh' with hneg | hpos
  · refine ⟨α * r, fun T => ?_⟩
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eC_eq_eK, abs_of_neg hneg]
    congr 1
    push_cast
    ring
  · refine ⟨-(α * r), fun T => ?_⟩
    rw [← RCLike.norm_conj (K := ℂ) (∑ s ∈ T, eK (-(α * r) * s - |(h : ℝ)| *
      ((r * s : ℕ) : ℝ) ^ γ)), map_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eC_eq_eK, ← eK_neg, abs_of_pos hpos]
    congr 1
    push_cast
    ring

/-- Song 2020, page 6, the inner sum over s with |r s - n/3| < z: a nonempty set of
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

/-- Song 2020, page 6, "applying the van der Corput's estimate in [3] (Cor. 8.13) to f(s)
in the inner sum", on one dyadic block 2^j <= s < 2^(j+1): the lab's discrete second
derivative test with lam = w^2, w = sqrt(H) sqrt(gamma (1-gamma)) r (r 2^j)^(gamma/2-1)/2
and c = 4. -/
private theorem block_vdC (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (H : ℝ) (hH : 0 < H)
    (β : ℝ) (r : ℕ) (hr : 1 ≤ r) (j a b : ℕ) (hab : a ≤ b) (ha : 2 ^ j ≤ a + 1)
    (hb : b + 1 ≤ 2 ^ (j + 1)) :
    ‖∑ s ∈ Finset.Ioc a b, eK (β * s - H * ((r * s : ℕ) : ℝ) ^ γ)‖ ≤
      8 * (4 * ((b : ℝ) - a) *
          (Real.sqrt H * Real.sqrt (γ * (1 - γ)) * r *
            ((r : ℝ) * 2 ^ j) ^ (γ / 2 - 1) / 2) +
        1 / (Real.sqrt H * Real.sqrt (γ * (1 - γ)) * r *
            ((r : ℝ) * 2 ^ j) ^ (γ / 2 - 1) / 2)) := by
  have hA : 0 < γ * (1 - γ) := mul_pos hγ0 (by linarith)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hP : (0 : ℝ) < (r : ℝ) * 2 ^ j := by positivity
  set p : ℝ := ((r : ℝ) * 2 ^ j) ^ (γ / 2 - 1) with hp
  have hp0 : 0 < p := Real.rpow_pos_of_pos hP _
  have hpp : p * p = ((r : ℝ) * 2 ^ j) ^ (γ - 2) := by
    rw [hp, ← Real.rpow_add hP]
    congr 1; ring
  set w : ℝ := Real.sqrt H * Real.sqrt (γ * (1 - γ)) * r * p / 2 with hw
  have hw0 : 0 < w := by
    have := Real.sqrt_pos.mpr hH
    have := Real.sqrt_pos.mpr hA
    positivity
  have hlam : w ^ 2 = H * (γ * (1 - γ)) * (r : ℝ) ^ 2 * ((r : ℝ) * 2 ^ j) ^ (γ - 2) / 4 := by
    rw [← hpp, hw]
    have e1 := Real.mul_self_sqrt hH.le
    have e2 := Real.mul_self_sqrt hA.le
    calc (Real.sqrt H * Real.sqrt (γ * (1 - γ)) * r * p / 2) ^ 2
        = (Real.sqrt H * Real.sqrt H) * (Real.sqrt (γ * (1 - γ)) * Real.sqrt (γ * (1 - γ))) *
            (r : ℝ) ^ 2 * (p * p) / 4 := by ring
      _ = _ := by rw [e1, e2]
  have h14 : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ (γ - 2) := by
    have e : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
    rw [← e]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hbd : ∀ m : ℕ, a < m → m < b →
      w ^ 2 ≤ H * (2 * ((r : ℝ) * m + r) ^ γ - ((r : ℝ) * m) ^ γ -
          ((r : ℝ) * m + 2 * r) ^ γ) ∧
        H * (2 * ((r : ℝ) * m + r) ^ γ - ((r : ℝ) * m) ^ γ -
          ((r : ℝ) * m + 2 * r) ^ γ) ≤ 4 * w ^ 2 := by
    intro m h1 h2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hx0 : (0 : ℝ) < (r : ℝ) * m := by positivity
    have hsd := second_diff_bounds γ hγ0 hγ1 ((r : ℝ) * m) r hx0 hr0
    have hPm : (r : ℝ) * 2 ^ j ≤ (r : ℝ) * m := by
      have : (2 : ℝ) ^ j ≤ m := by exact_mod_cast (by omega : 2 ^ j ≤ m)
      exact mul_le_mul_of_nonneg_left this hr0.le
    have hm2 : (r : ℝ) * m + 2 * r ≤ 2 * ((r : ℝ) * 2 ^ j) := by
      have h3 : m + 2 ≤ 2 ^ (j + 1) := by omega
      have : ((m : ℝ) + 2) ≤ 2 ^ (j + 1) := by exact_mod_cast h3
      rw [pow_succ] at this
      nlinarith
    have hlow : (1 : ℝ) / 4 * ((r : ℝ) * 2 ^ j) ^ (γ - 2) ≤
        ((r : ℝ) * m + 2 * r) ^ (γ - 2) := by
      have e1 : (2 * ((r : ℝ) * 2 ^ j)) ^ (γ - 2) ≤ ((r : ℝ) * m + 2 * r) ^ (γ - 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hm2 (by linarith)
      rw [Real.mul_rpow (by norm_num) hP.le] at e1
      have e2 : (1 : ℝ) / 4 * ((r : ℝ) * 2 ^ j) ^ (γ - 2) ≤
          (2 : ℝ) ^ (γ - 2) * ((r : ℝ) * 2 ^ j) ^ (γ - 2) :=
        mul_le_mul_of_nonneg_right h14 (Real.rpow_nonneg hP.le _)
      linarith
    have hup : ((r : ℝ) * m) ^ (γ - 2) ≤ ((r : ℝ) * 2 ^ j) ^ (γ - 2) :=
      Real.rpow_le_rpow_of_nonpos hP hPm (by linarith)
    have hc : 0 ≤ H * (γ * (1 - γ)) * (r : ℝ) ^ 2 := by positivity
    have l1 := mul_le_mul_of_nonneg_left hlow hc
    have l2 := mul_le_mul_of_nonneg_left hup hc
    have l3 := mul_le_mul_of_nonneg_left hsd.1 hH.le
    have l4 := mul_le_mul_of_nonneg_left hsd.2 hH.le
    rw [hlam]
    constructor
    · nlinarith
    · nlinarith
  have hcast : ∀ m : ℕ,
      (β * ((m + 1 + 1 : ℕ) : ℝ) - H * ((r * (m + 1 + 1) : ℕ) : ℝ) ^ γ -
          (β * ((m + 1 : ℕ) : ℝ) - H * ((r * (m + 1) : ℕ) : ℝ) ^ γ)) -
        (β * ((m + 1 : ℕ) : ℝ) - H * ((r * (m + 1) : ℕ) : ℝ) ^ γ -
          (β * (m : ℝ) - H * ((r * m : ℕ) : ℝ) ^ γ)) =
      H * (2 * ((r : ℝ) * m + r) ^ γ - ((r : ℝ) * m) ^ γ - ((r : ℝ) * m + 2 * r) ^ γ) := by
    intro m
    have e0 : ((r * m : ℕ) : ℝ) = (r : ℝ) * m := by push_cast; ring
    have e1 : ((r * (m + 1) : ℕ) : ℝ) = (r : ℝ) * m + r := by push_cast; ring
    have e2 : ((r * (m + 1 + 1) : ℕ) : ℝ) = (r : ℝ) * m + 2 * r := by push_cast; ring
    rw [e0, e1, e2]
    push_cast
    ring
  have hv := vdC_second_derivative
    (f := fun s : ℕ => β * (s : ℝ) - H * ((r * s : ℕ) : ℝ) ^ γ) (a := a) (b := b)
    (lam := w ^ 2) (c := 4) hab (by positivity) (by norm_num)
    (fun m h1 h2 => by
      have := (hbd m h1 h2).1
      rw [← hcast m] at this
      exact this)
    (fun m h1 h2 => by
      have := (hbd m h1 h2).2
      rw [← hcast m] at this
      exact this)
  rw [Real.sqrt_sq hw0.le] at hv
  exact hv

set_option maxHeartbeats 1600000 in
/-- Song 2020, page 6, the display "Sigma1 << log^2 x (u |h|^(1/2) x^(gamma/2-1) y +
x^(1-gamma/2) |h|^(-1/2))", one dyadic block of the inner sum for one r: the van der
Corput bound of block_vdC, with r s at most n and at most 2y + r values of s, is at most
a constant times sqrt(H) n^(gamma/2-1) y + r^(-1) n^(1-gamma/2) / sqrt(H). When r > y the
block has at most two terms and the trivial bound is used. -/
private theorem block_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (H : ℝ) (hH : 1 ≤ H)
    (β : ℝ) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : y ≤ (n : ℝ) / 3)
    (hE : 1 ≤ (n : ℝ) ^ (γ / 2 - 1) * y) (j a b : ℕ) (hab : a < b)
    (ha : 2 ^ j ≤ a + 1) (hb : b + 1 ≤ 2 ^ (j + 1))
    (hlo : (n : ℝ) / 3 - y < (r : ℝ) * ((a : ℝ) + 1)) (hhi : (r : ℝ) * b < (n : ℝ) / 3 + y) :
    ‖∑ s ∈ Finset.Ioc a b, eK (β * s - H * ((r * s : ℕ) : ℝ) ^ γ)‖ ≤
      (576 + 16 / Real.sqrt (γ * (1 - γ))) *
        (Real.sqrt H * (n : ℝ) ^ (γ / 2 - 1) * y +
          (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) / Real.sqrt H)) := by
  have hA : 0 < γ * (1 - γ) := mul_pos hγ0 (by linarith)
  have hA1 : γ * (1 - γ) ≤ 1 := by nlinarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hH0 : 0 < H := by linarith
  obtain ⟨sH, hsH⟩ : ∃ sH : ℝ, sH = Real.sqrt H := ⟨_, rfl⟩
  obtain ⟨sA, hsA⟩ : ∃ sA : ℝ, sA = Real.sqrt (γ * (1 - γ)) := ⟨_, rfl⟩
  have hsH1 : 1 ≤ sH := by
    rw [hsH]; exact Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt hH)
  have hsA0 : 0 < sA := by rw [hsA]; exact Real.sqrt_pos.mpr hA
  have hsA1 : sA ≤ 1 := by
    rw [hsA]; exact (Real.sqrt_le_sqrt hA1).trans_eq Real.sqrt_one
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℝ, N1 = (n : ℝ) ^ (γ / 2 - 1) := ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℝ, N2 = (n : ℝ) ^ (1 - γ / 2) := ⟨_, rfl⟩
  have hN10 : 0 < N1 := by rw [hN1]; exact Real.rpow_pos_of_pos hn0 _
  have hN20 : 0 < N2 := by rw [hN2]; exact Real.rpow_pos_of_pos hn0 _
  rw [← hsH, ← hsA, ← hN1, ← hN2]
  rw [← hN1] at hE
  have hy0 : 0 < y := by
    by_contra hc
    have : N1 * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN10.le (not_lt.mp hc)
    linarith
  have t1 : 0 ≤ sH * N1 * y := by positivity
  have t2 : 0 ≤ (r : ℝ)⁻¹ * (N2 / sH) := by positivity
  have t3 : 0 ≤ 16 / sA := by positivity
  have habR : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  -- the number of terms
  have hcnt : ((b : ℝ) - a) * r < 2 * y + r := by nlinarith
  rcases lt_or_ge y (r : ℝ) with hry | hry
  · -- trivial bound
    have htriv : ‖∑ s ∈ Finset.Ioc a b, eK (β * s - H * ((r * s : ℕ) : ℝ) ^ γ)‖ ≤
        (b : ℝ) - a := by
      calc _ ≤ ∑ s ∈ Finset.Ioc a b, ‖eK (β * s - H * ((r * s : ℕ) : ℝ) ^ γ)‖ :=
            norm_sum_le _ _
        _ = (b : ℝ) - a := by
            simp [eK_norm, Nat.card_Ioc, Nat.cast_sub hab.le]
    have h3 : (b : ℝ) - a < 3 := by
      by_contra hc
      have : 3 * (r : ℝ) ≤ ((b : ℝ) - a) * r :=
        mul_le_mul_of_nonneg_right (not_lt.mp hc) hr0.le
      linarith
    have h4 : 1 ≤ sH * N1 * y := by
      have : 1 * 1 ≤ sH * (N1 * y) := mul_le_mul hsH1 hE (by norm_num) (by linarith)
      linarith
    nlinarith [mul_nonneg t3 t1]
  · have hP : (0 : ℝ) < (r : ℝ) * 2 ^ j := by positivity
    have hv := block_vdC γ hγ0 hγ1 H hH0 β r hr j a b hab.le ha hb
    rw [← hsH, ← hsA] at hv
    obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ((r : ℝ) * 2 ^ j) ^ (γ / 2 - 1) := ⟨_, rfl⟩
    rw [← hp] at hv
    have hp0 : 0 < p := by rw [hp]; exact Real.rpow_pos_of_pos hP _
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = sH * sA * r * p / 2 := ⟨_, rfl⟩
    rw [← hw] at hv
    have hw0 : 0 < w := by rw [hw]; positivity
    have haj : (2 : ℝ) ^ j ≤ (a : ℝ) + 1 := by exact_mod_cast ha
    have hbj : (b : ℝ) + 1 ≤ 2 * 2 ^ j := by
      have : ((b : ℝ) + 1) ≤ 2 ^ (j + 1) := by exact_mod_cast hb
      rw [pow_succ] at this; linarith
    have hPn : (r : ℝ) * 2 ^ j ≤ n := by
      have : (r : ℝ) * 2 ^ j ≤ (r : ℝ) * b :=
        mul_le_mul_of_nonneg_left (by linarith) hr0.le
      linarith
    have hmul : ∀ t : ℝ, 0 < t → t * t ^ (γ / 2 - 1) = t ^ (γ / 2) := by
      intro t ht
      have := Real.rpow_add ht 1 (γ / 2 - 1)
      rw [Real.rpow_one] at this
      rw [← this]; congr 1; ring
    -- the main term
    have hX : ((b : ℝ) - a) * r * p ≤ 36 * N1 * y := by
      rcases le_or_gt ((n : ℝ) / 12) ((r : ℝ) * 2 ^ j) with hbig | hsmall
      · have e1 : p ≤ ((n : ℝ) / 12) ^ (γ / 2 - 1) := by
          rw [hp]
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hbig (by linarith)
        have e2 : ((n : ℝ) / 12) ^ (γ / 2 - 1) ≤ 12 * N1 := by
          have e3 : N1 = (12 : ℝ) ^ (γ / 2 - 1) * ((n : ℝ) / 12) ^ (γ / 2 - 1) := by
            rw [hN1, ← Real.mul_rpow (by norm_num) (by positivity)]
            congr 1; ring
          have e4 : (1 : ℝ) / 12 ≤ (12 : ℝ) ^ (γ / 2 - 1) := by
            have e : (12 : ℝ) ^ (-1 : ℝ) = 1 / 12 := by
              rw [Real.rpow_neg_one]; norm_num
            rw [← e]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have e5 : 0 ≤ ((n : ℝ) / 12) ^ (γ / 2 - 1) := Real.rpow_nonneg (by positivity) _
          nlinarith
        have e6 : ((b : ℝ) - a) * r ≤ 3 * y := by linarith
        calc ((b : ℝ) - a) * r * p ≤ (3 * y) * (12 * N1) :=
              mul_le_mul e6 (e1.trans e2) hp0.le (by positivity)
          _ = 36 * N1 * y := by ring
      · have hy6 : (n : ℝ) / 6 < y := by
          have : (r : ℝ) * ((a : ℝ) + 1) ≤ (r : ℝ) * (2 * 2 ^ j) :=
            mul_le_mul_of_nonneg_left (by linarith) hr0.le
          linarith
        have e1 : ((b : ℝ) - a) * r ≤ (r : ℝ) * 2 ^ j := by
          have : (b : ℝ) - a ≤ 2 ^ j := by linarith
          nlinarith
        have e2 : ((r : ℝ) * 2 ^ j) * p ≤ (n : ℝ) * N1 := by
          rw [hp, hN1, hmul _ hP, hmul _ hn0]
          exact Real.rpow_le_rpow hP.le hPn (by linarith)
        calc ((b : ℝ) - a) * r * p ≤ ((r : ℝ) * 2 ^ j) * p :=
              mul_le_mul_of_nonneg_right e1 hp0.le
          _ ≤ (n : ℝ) * N1 := e2
          _ ≤ 36 * N1 * y := by
            have := mul_le_mul_of_nonneg_left hy6.le hN10.le
            linarith [mul_nonneg hN10.le hy0.le]
    have hba : 0 ≤ ((b : ℝ) - a) * r * p := by
      have : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
      positivity
    have h1 : 4 * ((b : ℝ) - a) * w ≤ 72 * (sH * N1 * y) := by
      calc 4 * ((b : ℝ) - a) * w = (2 * sH * sA) * (((b : ℝ) - a) * r * p) := by
            rw [hw]; ring
        _ ≤ (2 * sH * 1) * (36 * N1 * y) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsA1 (by positivity)) hX hba
              (by positivity)
        _ = 72 * (sH * N1 * y) := by ring
    have hpinv : 1 / p ≤ N2 := by
      have e : 1 / p = ((r : ℝ) * 2 ^ j) ^ (1 - γ / 2) := by
        rw [hp, one_div, ← Real.rpow_neg hP.le]; congr 1; ring
      rw [e, hN2]
      exact Real.rpow_le_rpow hP.le hPn (by linarith)
    have h2 : 1 / w ≤ 2 * (1 / sA) * ((r : ℝ)⁻¹ * (N2 / sH)) := by
      have e : 1 / w = 2 * (1 / sA) * ((r : ℝ)⁻¹ * ((1 / p) / sH)) := by
        rw [hw]; field_simp
      rw [e]
      have : (1 / p) / sH ≤ N2 / sH := div_le_div_of_nonneg_right hpinv (by positivity)
      have hc : 0 ≤ 2 * (1 / sA) := by positivity
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left this (by positivity)) hc
    have h5 : 2 * (1 / sA) * ((r : ℝ)⁻¹ * (N2 / sH)) =
        (16 / sA) * ((r : ℝ)⁻¹ * (N2 / sH)) / 8 := by ring
    nlinarith [mul_nonneg t3 t1]

/-- Song 2020, page 6, the display "Sigma1 << log^2 x (...)": the number of dyadic blocks
2^j <= s < 2^(j+1) that can meet the range s <= n is at most log n / log 2 + 1, which is at
most (2/epsilon + 1) n^epsilon. This is the logarithm carried by n^epsilon. -/
private theorem blocks_le (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (2 / ε + 1) * (n : ℝ) ^ ε := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_le_rpow_div hn0.le hε
  have h5 : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
  have h6 : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
    have : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
    nlinarith
  have h7 : (2 / ε + 1) * (n : ℝ) ^ ε = 2 * ((n : ℝ) ^ ε / ε) + (n : ℝ) ^ ε := by ring
  rw [h7]
  push_cast
  linarith

set_option maxHeartbeats 1600000 in
/-- Song 2020, page 6, "Let f(s) = R_b(r s), and noting that r s ~ n and f''(s) is of size
r^2 n^(gamma-2) |h|. And applying the van der Corput's estimate in [3] (Cor. 8.13) to f(s)
in the inner sum": the statement of the leaf RouteVaughanSigma1.inner_sum_bound, proved
from the lab's discrete second derivative test over the dyadic blocks 2^j <= s < 2^(j+1),
with C = (576 + 16 / sqrt(gamma (1-gamma))) (2/epsilon + 1) and N0 = 1. -/
theorem inner_sum_bound_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ r : ℕ, 1 ≤ r → ∀ τ : ℝ,
            ‖∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ (s : ℝ) ≤ τ),
                eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)‖ ≤
              C * (n : ℝ) ^ ε *
                (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y +
                  (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2))) := by
  intro γ hγ hγ1 ε hε
  have hγ0 : 0 < γ := by linarith
  refine ⟨(576 + 16 / Real.sqrt (γ * (1 - γ))) * (2 / ε + 1), by positivity, 1, ?_⟩
  intro n hn y hy1 hy2 α h hh r hr τ
  obtain ⟨β, hβ⟩ := phase_flip γ α h hh r
  rw [hβ]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH : 1 ≤ |(h : ℝ)| := by
    have : (1 : ℝ) ≤ ((|h| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hh
    rwa [Int.cast_abs] at this
  have hE : 1 ≤ (n : ℝ) ^ (γ / 2 - 1) * y := by
    have h1 : (n : ℝ) ^ (γ / 2 - 1) * (n : ℝ) ^ (songExponent γ) =
        (n : ℝ) ^ (γ / 2 - 1 + songExponent γ) := (Real.rpow_add hn0 _ _).symm
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ (γ / 2 - 1 + songExponent γ) :=
      Real.one_le_rpow hn1 (by unfold songExponent; linarith)
    have h3 := mul_le_mul_of_nonneg_left hy1.le (Real.rpow_nonneg hn0.le (γ / 2 - 1))
    linarith
  have e1 : |(h : ℝ)| ^ ((1 : ℝ) / 2) = Real.sqrt |(h : ℝ)| := (Real.sqrt_eq_rpow _).symm
  have e2 : |(h : ℝ)| ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt |(h : ℝ)| := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (abs_nonneg _),
      ← Real.sqrt_eq_rpow, one_div]
  rw [e1, e2]
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = |(h : ℝ)| := ⟨_, rfl⟩
  rw [← hHdef] at hH ⊢
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S =
      (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun s : ℕ => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ (s : ℝ) ≤ τ) := ⟨_, rfl⟩
  rw [← hS]
  have hmem : ∀ s, s ∈ S ↔ s < Nat.ceil ((n : ℝ) / 3 + y) + 1 ∧
      |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ (s : ℝ) ≤ τ := by
    intro s; rw [hS, Finset.mem_filter, Finset.mem_range]
  have hs1 : ∀ s ∈ S, 1 ≤ s := by
    intro s hs
    by_contra hc
    have h0 : s = 0 := by omega
    have := ((hmem s).mp hs).2.1
    rw [h0] at this
    simp only [Nat.mul_zero, Nat.cast_zero, zero_sub, abs_neg] at this
    rw [abs_of_nonneg (by positivity)] at this
    linarith
  have hsn : ∀ s ∈ S, s ≤ n := by
    intro s hs
    have h1 := (abs_lt.mp ((hmem s).mp hs).2.1).2
    have h2 : (s : ℝ) ≤ ((r * s : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left s (by omega)
    have : (s : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hmaps : ∀ s ∈ S, Nat.log 2 s ∈ Finset.range (Nat.log 2 n + 1) := fun s hs =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hsn s hs)))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Finset.range (Nat.log 2 n + 1),
      ‖∑ s ∈ S.filter (fun s => Nat.log 2 s = j),
          eK (β * s - H * ((r * s : ℕ) : ℝ) ^ γ)‖ ≤
        (576 + 16 / Real.sqrt (γ * (1 - γ))) *
          (Real.sqrt H * (n : ℝ) ^ (γ / 2 - 1) * y +
            (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) / Real.sqrt H)) := by
    intro j _
    rcases (S.filter (fun s => Nat.log 2 s = j)).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]
      have : 0 ≤ y := by
        have := Real.rpow_nonneg hn0.le (songExponent γ)
        linarith
      positivity
    · have hconv : ∀ s₁ ∈ S.filter (fun s => Nat.log 2 s = j),
          ∀ s₂ ∈ S.filter (fun s => Nat.log 2 s = j), ∀ s, s₁ ≤ s → s ≤ s₂ →
            s ∈ S.filter (fun s => Nat.log 2 s = j) := by
        intro s1 h1 s2 h2 s h1s hs2
        obtain ⟨h1S, h1j⟩ := Finset.mem_filter.mp h1
        obtain ⟨h2S, h2j⟩ := Finset.mem_filter.mp h2
        obtain ⟨p1, p2, p3⟩ := (hmem s1).mp h1S
        obtain ⟨q1, q2, q3⟩ := (hmem s2).mp h2S
        refine Finset.mem_filter.mpr ⟨(hmem s).mpr ⟨by omega, ?_, ?_⟩, ?_⟩
        · have c1 : ((r * s1 : ℕ) : ℝ) ≤ ((r * s : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_le_mul_left r h1s
          have c2 : ((r * s : ℕ) : ℝ) ≤ ((r * s2 : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_le_mul_left r hs2
          rw [abs_lt] at p2 q2 ⊢
          constructor <;> linarith
        · have : (s : ℝ) ≤ s2 := by exact_mod_cast hs2
          linarith
        · have a1 := Nat.log_mono_right (b := 2) h1s
          have a2 := Nat.log_mono_right (b := 2) hs2
          omega
      obtain ⟨a, b, hab, hT, ha, hb⟩ := convex_finset_eq_Ioc _ hne
        (fun s hs => hs1 s (Finset.mem_filter.mp hs).1) hconv
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
      rw [hT]
      refine block_bound γ hγ0 hγ1 H hH β r hr n hn y hy2 hE j a b hab ?_ ?_ ?_ ?_
      · rw [← ha2]; exact Nat.pow_log_le_self 2 (by omega)
      · rw [← hb2]; exact Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) b)
      · have := (abs_lt.mp ((hmem _).mp ha1).2.1).1
        push_cast at this
        linarith
      · have := (abs_lt.mp ((hmem _).mp hb1).2.1).2
        push_cast at this
        linarith
  have hy0 : 0 ≤ y := by
    have := Real.rpow_nonneg hn0.le (songExponent γ)
    linarith
  have hEE : 0 ≤ (576 + 16 / Real.sqrt (γ * (1 - γ))) *
      (Real.sqrt H * (n : ℝ) ^ (γ / 2 - 1) * y +
        (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) / Real.sqrt H)) := by positivity
  calc ‖∑ j ∈ Finset.range (Nat.log 2 n + 1), ∑ s ∈ S.filter (fun s => Nat.log 2 s = j),
          eK (β * s - H * ((r * s : ℕ) : ℝ) ^ γ)‖
      ≤ ∑ _j ∈ Finset.range (Nat.log 2 n + 1),
          (576 + 16 / Real.sqrt (γ * (1 - γ))) *
            (Real.sqrt H * (n : ℝ) ^ (γ / 2 - 1) * y +
              (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) / Real.sqrt H)) :=
        norm_sum_le_of_le _ hblock
    _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) * ((576 + 16 / Real.sqrt (γ * (1 - γ))) *
            (Real.sqrt H * (n : ℝ) ^ (γ / 2 - 1) * y +
              (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) / Real.sqrt H))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((2 / ε + 1) * (n : ℝ) ^ ε) * ((576 + 16 / Real.sqrt (γ * (1 - γ))) *
            (Real.sqrt H * (n : ℝ) ^ (γ / 2 - 1) * y +
              (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) / Real.sqrt H))) :=
        mul_le_mul_of_nonneg_right (blocks_le ε hε n hn) hEE
    _ = _ := by ring

end LeanLab.Song2020.RouteVaughanInner
