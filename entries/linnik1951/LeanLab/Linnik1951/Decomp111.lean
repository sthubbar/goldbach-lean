module

public import LeanLab.Linnik1951.Conventions
public import LeanLab.Perelli1996.Sing
public import LeanLab.Linnik1951.CircleSplit111
public import LeanLab.Linnik1951.Repair493Data
public import LeanLab.Perelli1996.Series320
public import LeanLab.Perelli1996.TotientRatio320
public import LeanLab.Linnik1951.Lemma4Port111
public import LeanLab.Linnik1951.Lemma6Split111
public import LeanLab.Linnik1951.Major81Split111

/-!
P0093 pages 154 and 168 to 169. Decomposition of the lab's GRH existence statement.
AI wrote the Lean code. Binary Goldbach is open.
The circle method error remains a cited input. The Romanov input is proved in SecondMoment111.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- LEAF. P0093 page 154, equation 2.1. A positive count gives a representation. -/
theorem representation_of_count_pos111 {k N : ℕ} (h : 0 < representationCount111 k N) :
    LinnikExact k N := by
  classical
  unfold representationCount111 at h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp h
  obtain ⟨_, hp, hq, hν, heq⟩ := Finset.mem_filter.mp ht
  exact ⟨t.1.val, t.2.1.val, hp, hq, fun i => (t.2.2 i).val, hν, heq⟩

/-- P0093 page 154, equation 2.1. No representation is lost by the finite bounds. -/
theorem count_pos_of_representation111 {k N : ℕ} (h : LinnikExact k N) : 0 < representationCount111 k N := by
  classical
  obtain ⟨p, q, hp, hq, ν, hν, hN⟩ := h
  have hpN : p < N + 1 := by omega
  have hqN : q < N + 1 := by omega
  have hνN : ∀ i, ν i < N + 1 := by
    intro i
    have hi : 2 ^ ν i ≤ ∑ j, 2 ^ ν j := Finset.single_le_sum (f := fun j : Fin k => 2 ^ ν j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hpow : ν i < 2 ^ ν i := Nat.lt_two_pow_self
    omega
  unfold representationCount111
  apply Finset.card_pos.mpr
  refine ⟨(⟨p, hpN⟩, ⟨q, hqN⟩, fun i => ⟨ν i, hνN i⟩), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hp, hq, hν, hN⟩

/-! ### SPLIT of error_bound111 along P0093 Sections 2, 8, 9 and 10.
AI wrote the Lean code. Binary Goldbach is open.
The definitions below are local copies, made upstream of SecondMoment111 and
Decomp280b, of the damped generating functions, the three arc families and the
arc contribution. They are definitionally the same expressions as
primeFourier111, powerFourier111, majorArcs280, exceptionalArcs280,
goodMinorArcs280 and arcContribution280, which live in modules importing this
one and so cannot be used here. -/

/-- SPLIT piece 1 of error_bound111. P0093 page 154 equation 2.2 and page 167
equation 10.2. Fourier orthogonality on the unit interval counts the ordered
representations, and the disjoint partition into major, exceptional and good
minor arcs splits the integral into three parts. -/
theorem circle_partition_split111 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111 k N : ℝ) =
      arcContributionSplit111 k N (majorArcsSplit111 N) +
      arcContributionSplit111 k N (exceptionalArcsSplit111 N η) +
      arcContributionSplit111 k N (goodMinorArcsSplit111 N η) := by
  -- PROVE PASS: the local copies are definitionally the ported proved
  -- circle_partition_proved435_up111 of CircleSplit111.
  exact circle_partition_proved435_up111 k N hN η

/-! ### SPLIT burst 9 of major_error_split111 and exceptional_error_split111.
AI wrote the Lean code. Binary Goldbach is open. P0093 Sections 7 to 10. The
two GRH pieces are reduced to two GRH leaves with no k dependence or a cleaner
form, plus one unconditional arithmetic leaf on the singular series. -/

section Burst9Split
open Filter

/-- SPLIT 9 helper, P0093 pages 166 and 168, the step by which (9.2) and (10.6)
are absorbed into the scale. A fixed power of log N times a constant is
eventually below epsilon times a fixed positive power of N. Proved. -/
theorem polylog_small_split111 (j : ℕ) {c A ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → A * Real.log N ^ j ≤ ε * (N : ℝ) ^ c := by
  have hA : 0 < |A| + 1 := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ) hc).def (c := ε / (|A| + 1)) (by positivity)
  have h3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (h.and (eventually_gt_atTop 1))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h3
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hb, h1⟩ := hN0 N hN.le
  have hL : 0 ≤ Real.log N := (Real.log_pos h1).le
  have hNc : 0 ≤ (N : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL _),
    Real.norm_eq_abs, abs_of_nonneg hNc] at hb
  have hpow : 0 ≤ Real.log N ^ j := pow_nonneg hL _
  calc A * Real.log N ^ j ≤ (|A| + 1) * Real.log N ^ j :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) hpow
    _ ≤ (|A| + 1) * (ε / (|A| + 1) * (N : ℝ) ^ c) := mul_le_mul_of_nonneg_left hb hA.le
    _ = ε * (N : ℝ) ^ c := by field_simp

/-- SPLIT 9, P0093 page 166 equation 9.2 and page 167 equation 10.1, where the
integrals of S squared times T to the k are bounded through absolute values.
The arc contribution is at most e times the integral of the norms. Proved. -/
theorem arc_abs_le_split111 (k N : ℕ) (s : Set ℝ) :
    |arcContributionSplit111 k N s| ≤ Real.exp 1 *
      ∫ α in s, ‖primeSeriesSplit111 N α‖ ^ 2 * ‖powerSeriesSplit111 N α‖ ^ k := by
  unfold arcContributionSplit111
  rw [abs_mul, abs_of_pos (Real.exp_pos 1)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext α
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]


/-- SPLIT 9, P0093 page 166. The squared prime series is integrable on every
subset of the unit interval, by continuity, used to compare integrals in 9.3.
Proved. -/
theorem prime_square_integrableOn_split111 (N : ℕ) (hN : 1 ≤ N) (s : Set ℝ)
    (hs : s ⊆ Set.Icc 0 1) :
    MeasureTheory.IntegrableOn (fun α => ‖primeSeriesSplit111 N α‖ ^ 2) s := by
  have hc : Continuous (fun α => ‖primeSeriesSplit111 N α‖ ^ 2) :=
    ((continuous_prime_fourier111_up111 N hN).norm).pow 2
  exact (hc.continuousOn.integrableOn_Icc).mono_set hs

/-- P0093 page 165, Lemma 5 equation 7.19: the union of the closed segments of
length N to the minus 0.99 centred at the points of a finite set s. -/
noncomputable def coverSet111 (N : ℕ) (s : Finset ℝ) : Set ℝ :=
  ⋃ c ∈ s, Set.Icc (c - 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))
    (c + 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))

section Burst9Cover
open MeasureTheory

/-- P0093 page 162, the set O_theta of 7.5 where T is large, taken on the
interval from minus 1 to 2 so that segments around points of the unit interval
stay inside; T has period one, so this is three copies of the paper's set. -/
noncomputable def largeSet111 (N : ℕ) (θ : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc (-1 : ℝ) 2 ∧
    (1 - θ) * ‖powerSeriesSplit111 N 0‖ < ‖powerSeriesSplit111 N α‖}

/-- SPLIT 9 LEAF, unconditional. P0093 page 162, Lemma 4 equation 7.6, used for
2 eta as in the proof of Lemma 5 on page 165: since epsilon of eta tends to 0
with eta, for every kappa there is a small eta with the measure of O_{2 eta}
at most C N to the kappa minus 1. Proof in the paper by the binary digit count
7.9 to 7.18. -/
theorem lemma4_measure_split111 (κ : ℝ) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      volume (largeSet111 N (2 * η)) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (κ - 1)) := by
  -- PROVE PASS burst 8 p3: Lemma 4 is proved in Lemma4Port111 for every kappa
  -- at most one, a port of the clean Measure435 chain; a larger kappa only
  -- weakens the bound since N is at least one.
  obtain ⟨η, hη, hηh, C, hC, N0, h⟩ :=
    large_value_measure_general_l4p111 (min κ 1) (lt_min hκ one_pos) (min_le_right _ _)
  refine ⟨η, hη, hηh, C, hC, N0, fun N hN => ?_⟩
  have hfin : volume (largeSet111 N (2 * η)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hle : (N : ℝ) ^ (min κ 1 - 1) ≤ (N : ℝ) ^ (κ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left κ 1])
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  have hN' := h N hN
  exact hN'.trans (mul_le_mul_of_nonneg_left hle hC.le)

/-- SPLIT 9, P0093 page 161 equation 7.1 in its weakest form: T at zero is at
least one third once N is at least 2, from its first term. Proved. -/
theorem power_zero_lower_split111 (N : ℕ) (hN : 2 ≤ N) :
    1 / 3 ≤ ‖powerSeriesSplit111 N 0‖ := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have ha : Summable a := (damping_summable111_up111 N (by omega)).comp_injective hi
  have heq : powerSeriesSplit111 N 0 = ((∑' m, a m : ℝ) : ℂ) := by
    unfold powerSeriesSplit111
    rw [Complex.ofReal_tsum]
    congr 1
    funext m
    simp [a]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hsplit := ha.sum_add_tsum_nat_add 1
  have htail : 0 ≤ ∑' m, a (m + 1) := tsum_nonneg (fun m => (Real.exp_pos _).le)
  have ha0 : 1 / 3 ≤ a 0 := by
    have h1 : -1 ≤ -((2 ^ (0 + 1) : ℕ) : ℝ) / N := by
      rw [neg_div, neg_le_neg_iff, div_le_one hNp]
      push_cast; exact_mod_cast hN
    have h2 := Real.exp_le_exp.mpr h1
    have h3 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9]) |>.trans_eq rfl
    exact h3.trans h2
  have hsum : a 0 ≤ ∑' m, a m := by
    rw [← hsplit]; simp; linarith
  rw [abs_of_nonneg (tsum_nonneg (fun m => (Real.exp_pos _).le))]
  linarith

/-- SPLIT 9, P0093 page 165 proof of Lemma 5: the derivative weight of T, the sum
of 2 to the m times e to the minus 2 to the m over N, converges and is at most
6 N. Head bounded by a geometric sum, tail by the quadratic lower bound of exp.
Proved. -/
theorem dyadic_weight_split111 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => (2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) ∧
      ∑' m : ℕ, (2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) ≤ 6 * N := by
  let g : ℕ → ℝ := fun m => (2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let L := Nat.log 2 N
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  have hNpow : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have hpowL : (2 : ℝ) ^ L ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have htail (j : ℕ) : g (j + L) ≤ 2 * N * (1 / 2 : ℝ) ^ j := by
    set x : ℝ := (2 : ℝ) ^ (j + L + 1) with hx
    have hxN : (N : ℝ) * 2 ^ j ≤ x := by
      rw [hx, show j + L + 1 = j + (L + 1) by omega, pow_add, mul_comm]
      exact mul_le_mul_of_nonneg_left hNpow (by positivity)
    have hxpos : 0 < x := by positivity
    have hy : 0 ≤ x / N := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hy
    have hexp : Real.exp (-((2 ^ (j + L + 1) : ℕ) : ℝ) / N) ≤ 2 * N ^ 2 / x ^ 2 := by
      have hcast : (((2 ^ (j + L + 1) : ℕ) : ℝ)) = x := by rw [hx]; push_cast; ring
      rw [hcast, neg_div, Real.exp_neg]
      have hE : (x / N) ^ 2 / 2 ≤ Real.exp (x / N) := by nlinarith
      have hE0 : 0 < (x / N) ^ 2 / 2 := by positivity
      calc (Real.exp (x / N))⁻¹ ≤ ((x / N) ^ 2 / 2)⁻¹ := inv_anti₀ hE0 hE
        _ = 2 * N ^ 2 / x ^ 2 := by field_simp
    have hg : g (j + L) = x * Real.exp (-((2 ^ (j + L + 1) : ℕ) : ℝ) / N) := by
      simp only [g, hx]
    rw [hg]
    calc x * Real.exp (-((2 ^ (j + L + 1) : ℕ) : ℝ) / N) ≤ x * (2 * N ^ 2 / x ^ 2) :=
          mul_le_mul_of_nonneg_left hexp hxpos.le
      _ = 2 * N ^ 2 / x := by field_simp
      _ ≤ 2 * N ^ 2 / (N * 2 ^ j) := div_le_div_of_nonneg_left (by positivity) (by positivity) hxN
      _ = 2 * N * (1 / 2 : ℝ) ^ j := by rw [one_div_pow]; field_simp
  have hgeo : Summable (fun j : ℕ => 2 * N * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsL : Summable (fun j => g (j + L)) :=
    Summable.of_nonneg_of_le (fun j => hg0 _) htail hgeo
  have hs : Summable g := (summable_nat_add_iff L).mp hsL
  refine ⟨hs, ?_⟩
  have hhead : ∑ m ∈ range L, g m ≤ 2 * N := by
    have hgeom : ∀ K : ℕ, ∑ m ∈ range K, (2 : ℝ) ^ (m + 1) = 2 ^ (K + 1) - 2 := by
      intro K; induction K with
      | zero => simp
      | succ K ih => rw [sum_range_succ, ih]; ring
    calc ∑ m ∈ range L, g m ≤ ∑ m ∈ range L, (2 : ℝ) ^ (m + 1) := by
          apply sum_le_sum; intro m _
          have h1 : Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            rw [neg_div]; exact neg_nonpos.mpr (by positivity)
          simp only [g]
          calc (2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) ≤
              (2 : ℝ) ^ (m + 1) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = _ := mul_one _
      _ = 2 ^ (L + 1) - 2 := hgeom L
      _ ≤ 2 * N := by rw [pow_succ]; linarith
  have htailSum : ∑' j, g (j + L) ≤ 4 * N := by
    calc ∑' j, g (j + L) ≤ ∑' j : ℕ, 2 * N * (1 / 2 : ℝ) ^ j := hsL.tsum_le_tsum htail hgeo
      _ = 4 * N := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  calc ∑' m, g m = ∑ m ∈ range L, g m + ∑' j, g (j + L) := (hs.sum_add_tsum_nat_add L).symm
    _ ≤ 2 * N + 4 * N := add_le_add hhead htailSum
    _ = 6 * N := by ring

/-- Two unit phases differ by at most the difference of their angles. Proved. -/
theorem exp_phase_diff_split111 (θ1 θ2 : ℝ) :
    ‖Complex.exp ((θ1 : ℂ) * Complex.I) - Complex.exp ((θ2 : ℂ) * Complex.I)‖ ≤ |θ1 - θ2| := by
  have h : Complex.exp ((θ1 : ℂ) * Complex.I) - Complex.exp ((θ2 : ℂ) * Complex.I) =
      Complex.exp ((θ2 : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((θ1 - θ2 : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ1 - θ2))

/-- SPLIT 9, P0093 page 165 proof of Lemma 5: T moves by at most 2 pi times xi
times 6 N when its argument moves by xi. Proved. -/
theorem power_shift_diff_split111 (N : ℕ) (hN : 1 ≤ N) (α ξ : ℝ) :
    ‖powerSeriesSplit111 N (α + ξ) - powerSeriesSplit111 N α‖ ≤
      2 * Real.pi * |ξ| * (6 * N) := by
  obtain ⟨hgs, hgle⟩ := dyadic_weight_split111 N hN
  have hu := power_fourier_summable111_up111 N hN (α + ξ)
  have hv := power_fourier_summable111_up111 N hN α
  let w : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * (α + ξ) * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I) -
      (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hw : ∀ m, ‖w m‖ ≤ 2 * Real.pi * |ξ| *
      ((2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) := by
    intro m
    simp only [w]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hd := exp_phase_diff_split111 (-(2 * Real.pi * (α + ξ) * (2 ^ (m + 1) : ℕ)))
      (-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)))
    have hab : |-(2 * Real.pi * (α + ξ) * ((2 ^ (m + 1) : ℕ) : ℝ)) -
        -(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ))| =
        2 * Real.pi * |ξ| * (2 : ℝ) ^ (m + 1) := by
      push_cast
      rw [show -(2 * Real.pi * (α + ξ) * 2 ^ (m + 1)) - -(2 * Real.pi * α * 2 ^ (m + 1)) =
        -(2 * Real.pi * 2 ^ (m + 1) * ξ) by ring, abs_neg, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * 2 ^ (m + 1))]
      ring
    rw [hab] at hd
    calc Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) * ‖_‖ ≤
        Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) * (2 * Real.pi * |ξ| * (2 : ℝ) ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      _ = _ := by ring
  have hws : Summable (fun m => ‖w m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hw (hgs.mul_left _)
  have hsub : powerSeriesSplit111 N (α + ξ) - powerSeriesSplit111 N α = ∑' m, w m := by
    unfold powerSeriesSplit111
    rw [← hu.tsum_sub hv]
  rw [hsub]
  calc ‖∑' m, w m‖ ≤ ∑' m, ‖w m‖ := norm_tsum_le_tsum_norm hws
    _ ≤ ∑' m, 2 * Real.pi * |ξ| *
          ((2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) :=
        hws.tsum_le_tsum hw (hgs.mul_left _)
    _ = 2 * Real.pi * |ξ| * ∑' m,
          ((2 : ℝ) ^ (m + 1) * Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) := tsum_mul_left
    _ ≤ 2 * Real.pi * |ξ| * (6 * N) := mul_le_mul_of_nonneg_left hgle (by positivity)

/-- SPLIT 9, unconditional, PROVED. P0093 page 165, proof of Lemma 5: if N is large
and xi is at most Delta equal to 1 over N ln N, a point of O_eta moved by xi
lies in O_{2 eta}. The paper calls this obvious. -/
theorem lemma5_shift_split111 (η : ℝ) (hη : 0 < η) (hη1 : η < 1 / 2) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ α ξ : ℝ, |ξ| ≤ 1 / (N * Real.log N) →
      (1 - η) * ‖powerSeriesSplit111 N 0‖ < ‖powerSeriesSplit111 N α‖ →
        (1 - 2 * η) * ‖powerSeriesSplit111 N 0‖ < ‖powerSeriesSplit111 N (α + ξ)‖ := by
  -- PROVED: T at zero is at least one third and T moves by at most 12 pi over ln N.
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp (36 * Real.pi / η))
  refine ⟨max B 2, fun N hN α ξ hξ hα => ?_⟩
  have hNB : B < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNr : (2 : ℝ) < N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 36 * Real.pi / η ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) (hB.trans (by exact_mod_cast hNB : (B : ℝ) < N)).le
    rwa [Real.log_exp] at h
  have hlpos : 0 < Real.log N := lt_of_lt_of_le (by positivity) hlog
  have hd := power_shift_diff_split111 N (by omega) α ξ
  have hT0 := power_zero_lower_split111 N (by omega)
  have hdiff : 2 * Real.pi * |ξ| * (6 * N) ≤ η * (1 / 3) := by
    have h1 : 2 * Real.pi * |ξ| * (6 * N) ≤ 2 * Real.pi * (1 / (N * Real.log N)) * (6 * N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hξ (by positivity)
    have h2 : 2 * Real.pi * (1 / (N * Real.log N)) * (6 * N) = 12 * Real.pi / Real.log N := by
      field_simp; ring
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ hlpos]
    have := (div_le_iff₀ hη).mp hlog
    nlinarith
  have htri : ‖powerSeriesSplit111 N α‖ - ‖powerSeriesSplit111 N (α + ξ)‖ ≤
      ‖powerSeriesSplit111 N (α + ξ) - powerSeriesSplit111 N α‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  nlinarith

/-- SPLIT 9, P0093 page 165, the counting step of Lemma 5 done with a grid of
cells of length L: cells meeting E lie inside O, are disjoint, so their number
times L is at most the measure of O, and their centres cover E within L over 2.
Proved. -/
theorem grid_cover_split111 (L : ℝ) (hL : 0 < L) (E O : Set ℝ) (hE : E ⊆ Set.Icc 0 1)
    (hcell : ∀ α ∈ E, ∀ β, |β - α| < L → β ∈ O) (V : ℝ) (hV : 0 ≤ V)
    (hO : volume O ≤ ENNReal.ofReal V) :
    ∃ s : Finset ℝ, (s.card : ℝ) * L ≤ V ∧
      ∀ α ∈ E, ∃ c ∈ s, |α - c| ≤ L / 2 := by
  classical
  let M := ⌈1 / L⌉₊
  let I : ℕ → Set ℝ := fun j => Set.Ico (j * L) ((j + 1) * L)
  let J := (Finset.range (M + 1)).filter (fun j => ∃ α ∈ E, α ∈ I j)
  refine ⟨J.image (fun j : ℕ => (j : ℝ) * L + L / 2), ?_, ?_⟩
  · have hcard : ((J.image (fun j : ℕ => (j : ℝ) * L + L / 2)).card : ℝ) ≤ J.card := by
      exact_mod_cast Finset.card_image_le
    have hsub : (⋃ j ∈ J, I j) ⊆ O := by
      intro β hβ
      simp only [Set.mem_iUnion] at hβ
      obtain ⟨j, hj, hβj⟩ := hβ
      obtain ⟨α, hαE, hαj⟩ := (Finset.mem_filter.mp hj).2
      apply hcell α hαE β
      simp only [I, Set.mem_Ico] at hβj hαj
      rw [abs_lt]; constructor <;> nlinarith
    have hdisj : Set.PairwiseDisjoint (↑J) I := by
      intro a _ b _ hab
      simp only [Function.onFun, I]
      rw [Set.disjoint_iff]
      intro x ⟨hxa, hxb⟩
      simp only [Set.mem_Ico] at hxa hxb
      rcases lt_or_gt_of_ne hab with h | h
      · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
        nlinarith
      · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
        nlinarith
    have hvol : volume (⋃ j ∈ J, I j) = ENNReal.ofReal (J.card * L) := by
      rw [measure_biUnion_finset hdisj (fun j _ => measurableSet_Ico)]
      simp only [I, Real.volume_Ico]
      have : ∀ j : ℕ, ((j : ℝ) + 1) * L - j * L = L := fun j => by ring
      simp only [this, Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hle := (measure_mono hsub).trans hO
    rw [hvol, ENNReal.ofReal_le_ofReal_iff hV] at hle
    exact (mul_le_mul_of_nonneg_right hcard hL.le).trans hle
  · intro α hα
    have hα0 : 0 ≤ α := (hE hα).1
    have hα1 : α ≤ 1 := (hE hα).2
    set j := ⌊α / L⌋₊ with hj
    have hj1 : (j : ℝ) ≤ α / L := Nat.floor_le (div_nonneg hα0 hL.le)
    have hj2 : α / L < j + 1 := Nat.lt_floor_add_one _
    have hjL : (j : ℝ) * L ≤ α := by rwa [le_div_iff₀ hL] at hj1
    have hjL2 : α < (j + 1) * L := by rwa [div_lt_iff₀ hL] at hj2
    have hjM : j < M + 1 := by
      have h1 : α / L ≤ 1 / L := div_le_div_of_nonneg_right hα1 hL.le
      have h2 : j ≤ M := Nat.floor_le_ceil _ |>.trans' (Nat.floor_mono h1)
      omega
    refine ⟨(j : ℝ) * L + L / 2, Finset.mem_image.mpr ⟨j, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjM, α, hα, ⟨hjL, hjL2⟩⟩
    · rw [abs_le]; constructor <;> linarith

end Burst9Cover

/-- SPLIT 9, unconditional, proved from the Lemma 4 and shift leaves. P0093 pages 162 to 165, Lemma 4 equation 7.6 and
Lemma 5 equation 7.19, with eta fixed as at the start of Section 8 so that
2 epsilon of 2 eta and epsilon of eta are below 0.01: for large N the points
where T is large are covered by at most N to the 0.01 segments of length N to
the minus 0.99. Stated for the lab exceptional set, a subset of the paper's
set O_eta. No GRH is used here. -/
theorem lemma5_cover_split111 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∃ s : Finset ℝ, (s.card : ℝ) ≤ (N : ℝ) ^ (1 / 100 : ℝ) ∧
        exceptionalArcsSplit111 N η ⊆ coverSet111 N s := by
  -- SPLIT burst 9: Lemma 4 measure leaf, shift leaf and the proved grid count.
  obtain ⟨η, hη, hη2, C, hC, N1, h4⟩ := lemma4_measure_split111 (1 / 200) (by norm_num)
  obtain ⟨N2, hsh⟩ := lemma5_shift_split111 η hη hη2
  obtain ⟨N3, hpoly⟩ := polylog_small_split111 1 (A := C) (c := (1 / 200 : ℝ))
    (by norm_num) (by norm_num : (0 : ℝ) < 1)
  refine ⟨η, hη, by linarith, max (max N1 N2) (max N3 3), fun N hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : 3 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNr : (3 : ℝ) < N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set L : ℝ := 1 / (N * Real.log N) with hLdef
  have hNL : 1 ≤ (N : ℝ) * Real.log N := by nlinarith
  have hL : 0 < L := by positivity
  have hL1' : L ≤ 1 := by rw [hLdef, div_le_one (by positivity)]; exact hNL
  have hV : 0 ≤ C * (N : ℝ) ^ (1 / 200 - 1 : ℝ) := by positivity
  obtain ⟨s, hcard, hcov⟩ := grid_cover_split111 L hL (exceptionalArcsSplit111 N η)
    (largeSet111 N (2 * η)) (fun α hα => hα.1)
    (fun α hα β hβ => by
      have hβ' : |β - α| ≤ 1 / (N * Real.log N) := hβ.le
      have h := hsh N hN2 α (β - α) hβ' hα.2.2
      rw [add_sub_cancel] at h
      refine ⟨?_, h⟩
      have h01 := hα.1
      rw [abs_lt] at hβ
      constructor <;> linarith [h01.1, h01.2])
    _ hV (h4 N hN1)
  refine ⟨s, ?_, ?_⟩
  · have hp := hpoly N hN3
    rw [pow_one, one_mul] at hp
    have hsplit : (N : ℝ) ^ (1 / 200 - 1 : ℝ) * N = (N : ℝ) ^ (1 / 200 : ℝ) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]; field_simp
    have hexp : (N : ℝ) ^ (1 / 200 : ℝ) * (N : ℝ) ^ (1 / 200 : ℝ) = (N : ℝ) ^ (1 / 100 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    have hc : (s.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 200 - 1 : ℝ) / L := by
      rw [le_div_iff₀ hL]; exact hcard
    calc (s.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 200 - 1 : ℝ) / L := hc
      _ = (C * Real.log N) * ((N : ℝ) ^ (1 / 200 - 1 : ℝ) * N) := by
          rw [hLdef]; field_simp
      _ = (C * Real.log N) * (N : ℝ) ^ (1 / 200 : ℝ) := by rw [hsplit]
      _ ≤ (N : ℝ) ^ (1 / 200 : ℝ) * (N : ℝ) ^ (1 / 200 : ℝ) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := hexp
  · intro α hα
    obtain ⟨c, hc, hdist⟩ := hcov α hα
    have h99 : (N : ℝ) ^ (99 / 100 : ℝ) ≤ N * Real.log N := by
      calc (N : ℝ) ^ (99 / 100 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = N := Real.rpow_one _
        _ ≤ N * Real.log N := le_mul_of_one_le_right hN0.le hL1
    have hpos99 : 0 < (N : ℝ) ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hN0 _
    have hrad : L / 2 ≤ 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)) := by
      rw [hLdef, div_div, one_div_le_one_div (by positivity) (by positivity)]
      nlinarith
    simp only [coverSet111, Set.mem_iUnion]
    refine ⟨c, hc, ?_⟩
    rw [abs_le] at hdist
    constructor <;> linarith [hdist.1, hdist.2]

/-- SPLIT 9, P0093 page 161 equation 7.1. Pointwise bound of T by its value at
zero, through the proved port power_abs_le_log357_up111. Proved. -/
theorem power_norm_le_split111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖powerSeriesSplit111 N α‖ ≤ Real.log N / Real.log 2 + 2 :=
  power_abs_le_log357_up111 N hN α

/-- SPLIT 9, P0093 page 168 after equation 10.7. The Lemma 7 bound with the
factor e of equation 2.2 is eventually below epsilon times the scale, since
B to the k times ln squared N is small against N to the one twentieth. Proved. -/
theorem exceptional_absorb_split111 (k : ℕ) (hk : 2 ≤ k) (B ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.exp 1 * (B ^ k * N * Real.log N ^ k / (N : ℝ) ^ (1 / 20 : ℝ)) ≤
        ε * scale111 k N := by
  obtain ⟨N1, h1⟩ := polylog_small_split111 2
    (A := Real.exp 1 * B ^ k * Real.log 2 ^ (k - 2)) (by norm_num : (0 : ℝ) < 1 / 20) hε
  refine ⟨max N1 1, fun N hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 1 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hpoly := h1 N hN1
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hL : 0 < Real.log N := Real.log_pos hNr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNc : 0 < (N : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  set F : ℝ := (N : ℝ) * Real.log N ^ (k - 2) / ((N : ℝ) ^ (1 / 20 : ℝ) * Real.log 2 ^ (k - 2))
  have hF : 0 ≤ F := by positivity
  have hk2 : Real.log N ^ k = Real.log N ^ (k - 2) * Real.log N ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hlhs : Real.exp 1 * (B ^ k * N * Real.log N ^ k / (N : ℝ) ^ (1 / 20 : ℝ)) =
      (Real.exp 1 * B ^ k * Real.log 2 ^ (k - 2) * Real.log N ^ 2) * F := by
    simp only [F]; rw [hk2]; field_simp
  have hrhs : ε * scale111 k N = (ε * (N : ℝ) ^ (1 / 20 : ℝ)) * F := by
    simp only [F, scale111]; rw [div_pow]; field_simp
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right hpoly hF

/-- P0093 page 168 equation 10.6 left side: the truncated singular series
sum over q at most Q of mu squared of q over phi squared of q times the
Ramanujan sum, written as the real cosine sum it equals. -/
noncomputable def truncSingular111 (Q n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Real.cos (2 * Real.pi * (n : ℝ) * (a : ℝ) / (q : ℝ))

/-- P0093 page 165 equation 8.1 main term, with the truncated singular series at
level Q in place of the full series. Same index set as mainTerm111; every
residual N1 is even because N is even. -/
noncomputable def mainTermTrunc111 (k N Q : ℕ) : ℝ := by
  classical
  exact ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
      Even (N - ∑ i, 2 ^ (ν i).val)),
    truncSingular111 Q (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2

/-- P0093 page 165 equation 8.1 applied to the major arcs, burst 8 p3: the major arc
contribution is e times the real part of the sum over tuples of the tuple weight times the
major arc integral of S squared times e of N_1 alpha. Proved from arc_tuple_expand_split111
of Major81Split111. -/
theorem major_tuple_expand_split111 (k N : ℕ) (hN : 1 ≤ N) :
    arcContributionSplit111 k N (majorArcsSplit111 N) = Real.exp 1 *
      (∑' ν : Fin k → ℕ,
        (((∏ i, Real.exp (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N)) : ℝ) : ℂ) *
          ∫ α in majorArcsSplit111 N, primeSeriesSplit111 N α ^ 2 *
            Complex.exp (((2 * Real.pi * α * ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ))) : ℝ) *
              Complex.I)).re := by
  have h := (arc_tuple_expand_split111 k N hN (majorArcsSplit111 N) (fun α h => h.1)).tsum_eq
  unfold arcContributionSplit111
  exact congrArg (fun z : ℂ => Real.exp 1 * z.re) h.symm

section Burst9Singular
open Real Finset

/-- SPLIT 9, divisor bound used in P0093 page 168 equation 10.5, where tau of N1
is absorbed into a small power of N. Port of the proved
LeanLab.Akeno2026.Decomp86.card_divisors_le_rpow, copied because that module is
not upstream of this one. Proved. -/
theorem divisor_count_le_rpow_split111 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hc (p : ℕ) : 1 ≤ c p := by dsimp [c]; split_ifs <;> linarith
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

end Burst9Singular

/-- The real part of the lab additive character e of LeanLab.Perelli1996.Kernel
is the cosine used in truncSingular111. Proved. -/
theorem kernel_e_re_split111 (x : ℝ) :
    (LeanLab.Perelli1996.Kernel.e x).re = Real.cos (2 * Real.pi * x) := by
  unfold LeanLab.Perelli1996.Kernel.e
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]

/-- SPLIT 9, P0093 page 168 equation 10.6: the truncated singular series is the
real part of the partial sum of the proved Ramanujan coefficient expansion
LeanLab.Perelli1996.Series320.coefficient, which has the same terms mu squared
over phi squared times the Ramanujan sum. Proved. -/
theorem truncSingular_eq_re_split111 (Q n : ℕ) :
    truncSingular111 Q n =
      (∑ q ∈ Finset.Icc 1 Q, LeanLab.Perelli1996.Series320.coefficient n q).re := by
  unfold truncSingular111
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  unfold LeanLab.Perelli1996.Series320.coefficient
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum
  have hc : ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) =
      ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [kernel_e_re_split111]
  congr 1
  ring

/-- SPLIT 9, unconditional, PROVED. P0093 page 168 equations 10.4 to 10.6: the tail
rho of the singular series beyond Q is at most a constant times tau of N1
times Q to the minus one half, which is at most N to the minus 0.02. Stated for
even residuals N1 between 2 and N, the only ones in the main term. The proof uses
the lab's sharper tail N1 tau of N1 over phi of N1 over Q from Perelli1996, which
gives the same N to the minus 0.02. -/
theorem singular_truncation_split111 :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℕ, Even n → 2 ≤ n → n ≤ N →
      |truncSingular111 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ n - singularSeries111 n| ≤
        B / (N : ℝ) ^ (1 / 50 : ℝ) := by
  -- PROVED from the clean lab expansion tail LeanLab.Perelli1996.Series320.partial_tail,
  -- the totient ratio bound ratio_le_log and the ported divisor bound.
  obtain ⟨K, hK, htail⟩ := LeanLab.Perelli1996.Series320.partial_tail
  obtain ⟨C, hC, hdiv⟩ := divisor_count_le_rpow_split111 (ε := 1 / 100) (by norm_num)
  obtain ⟨N1, h1⟩ := polylog_small_split111 1 (A := 4 * K * C) (c := (7 / 100 : ℝ))
    (by norm_num) (by norm_num : (0 : ℝ) < 1)
  refine ⟨1, one_pos, max N1 3, fun N hN n hev hn2 hnN => ?_⟩
  have hN1' : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNr : (3 : ℝ) < N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set P : ℝ := (N : ℝ) ^ (1 / 10 : ℝ) with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) (by norm_num)
  have hn0 : 0 < n := by omega
  have ht := htail n hn0 P hP1
  have hsing : (LeanLab.Perelli1996.Sing n : ℂ) = ((singularSeries111 n : ℝ) : ℂ) := rfl
  have hre : |truncSingular111 ⌊P⌋₊ n - singularSeries111 n| ≤
      ‖(LeanLab.Perelli1996.Sing n : ℂ) -
        ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, LeanLab.Perelli1996.Series320.coefficient n q‖ := by
    rw [truncSingular_eq_re_split111, hsing, ← norm_neg, neg_sub]
    have := Complex.abs_re_le_norm
      ((∑ q ∈ Finset.Icc 1 ⌊P⌋₊, LeanLab.Perelli1996.Series320.coefficient n q) -
        ((singularSeries111 n : ℝ) : ℂ))
    simpa only [Complex.sub_re, Complex.ofReal_re] using this
  have hratio := LeanLab.Perelli1996.TotientRatio320.ratio_le_log n hn0
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn0
  have hlogn : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnN)
  have hR : (n : ℝ) / n.totient ≤ 4 * Real.log N := by linarith
  have hR0 : 0 ≤ (n : ℝ) / n.totient := by positivity
  have hτ : (n.divisors.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 100 : ℝ) := by
    refine (hdiv n).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnN) (by norm_num)
  have hpoly := h1 N hN1'
  rw [pow_one, one_mul] at hpoly
  have hP0 : 0 < P := by linarith
  have h100 : 0 < (N : ℝ) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have h50 : 0 < (N : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hexp : (N : ℝ) ^ (7 / 100 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (1 / 50 : ℝ) = P := by
    rw [hPdef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
  calc _ ≤ _ := hre
    _ ≤ K * ((n : ℝ) * n.divisors.card / n.totient) / P := ht
    _ = K * ((n : ℝ) / n.totient * n.divisors.card) / P := by ring
    _ ≤ K * ((4 * Real.log N) * (C * (N : ℝ) ^ (1 / 100 : ℝ))) / P := by
        apply div_le_div_of_nonneg_right _ hP0.le
        apply mul_le_mul_of_nonneg_left _ hK.le
        exact mul_le_mul hR hτ (Nat.cast_nonneg _) (by linarith)
    _ = (4 * K * C * Real.log N) * (N : ℝ) ^ (1 / 100 : ℝ) / P := by ring
    _ ≤ (N : ℝ) ^ (7 / 100 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ) / P := by
        apply div_le_div_of_nonneg_right _ hP0.le
        exact mul_le_mul_of_nonneg_right hpoly h100.le
    _ = 1 / (N : ℝ) ^ (1 / 50 : ℝ) := by
        rw [div_eq_div_iff hP0.ne' h50.ne', one_mul, hexp]

/-- SPLIT 9, P0093 page 165 after equation 8.1: the number of residuals N1, that
is of exponent tuples, is at most a power of log N. Each exponent is at most
the base two logarithm of N. Proved. -/
theorem exponent_count_split111 (k N : ℕ) [DecidablePred fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧ Even (N - ∑ i, 2 ^ (ν i).val)] :
    ((Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
      (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
        Even (N - ∑ i, 2 ^ (ν i).val)).card : ℕ) ≤ (Nat.log 2 N + 1) ^ k := by
  classical
  let L := Nat.log 2 N
  let f : (Fin k → Fin (N + 1)) → (Fin k → Fin (L + 1)) :=
    fun ν i => ⟨min (ν i).val L, by omega⟩
  have hb : ∀ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
      (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
        Even (N - ∑ i, 2 ^ (ν i).val)), ∀ i, (ν i).val ≤ L := by
    intro ν hν i
    have h2 := (Finset.mem_filter.mp hν).2.2.1
    have hi : 2 ^ (ν i).val ≤ ∑ j, 2 ^ (ν j).val :=
      Finset.single_le_sum (f := fun j : Fin k => 2 ^ (ν j).val)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  calc _ ≤ (Finset.univ : Finset (Fin k → Fin (L + 1))).card := by
        apply Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
        intro a ha b hb' hab
        funext i
        have h := congrArg (fun g => (g i).val) hab
        simp only [f] at h
        have ha' := hb a ha i
        have hb'' := hb b hb' i
        apply Fin.ext
        rw [min_eq_left ha', min_eq_left hb''] at h
        exact h
    _ = (L + 1) ^ k := by simp

/-- SPLIT 9, P0093 page 168, applying 10.6 inside 8.1. Replacing the truncated
singular series by the full one changes the main term by at most the number
of tuples times the uniform truncation error times N over ln squared 2.
Proved. -/
theorem trunc_difference_split111 (k N Q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ n : ℕ, Even n → 2 ≤ n → n ≤ N →
      |truncSingular111 Q n - singularSeries111 n| ≤ δ) :
    |mainTermTrunc111 k N Q - mainTerm111 k N| ≤
      ((Nat.log 2 N + 1) ^ k : ℕ) * (δ * ((N : ℝ) / Real.log 2 ^ 2)) := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mainTermTrunc111 mainTerm111
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
      (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
        Even (N - ∑ i, 2 ^ (ν i).val)),
      |truncSingular111 Q (N - ∑ i, 2 ^ (ν i).val) *
          (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2 -
        singularSeries111 (N - ∑ i, 2 ^ (ν i).val) *
          (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2| ≤
        δ * ((N : ℝ) / Real.log 2 ^ 2) := by
    intro ν hν
    obtain ⟨_, h2, hev⟩ := (Finset.mem_filter.mp hν).2
    set n := N - ∑ i, 2 ^ (ν i).val with hn
    have hnN : n ≤ N := Nat.sub_le _ _
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnr
    have hl2sq : Real.log 2 ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hl2.le hlog2n 2
    have hfrac : (n : ℝ) / Real.log n ^ 2 ≤ (N : ℝ) / Real.log 2 ^ 2 := by
      calc (n : ℝ) / Real.log n ^ 2 ≤ (n : ℝ) / Real.log 2 ^ 2 :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hl2sq
        _ ≤ (N : ℝ) / Real.log 2 ^ 2 :=
            div_le_div_of_nonneg_right (by exact_mod_cast hnN) (by positivity)
    have heq : truncSingular111 Q n * (n : ℝ) / Real.log n ^ 2 -
        singularSeries111 n * (n : ℝ) / Real.log n ^ 2 =
        (truncSingular111 Q n - singularSeries111 n) * ((n : ℝ) / Real.log n ^ 2) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / Real.log n ^ 2)]
    exact mul_le_mul (hS n hev h2 hnN) hfrac (by positivity) hδ
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast exponent_count_split111 k N

/-- SPLIT 9, P0093 page 168 after equation 10.7. The truncation change of
trunc_difference_split111 with error B times N to the minus 0.02 is
eventually below epsilon times the scale. Proved. -/
theorem trunc_absorb_split111 (k : ℕ) (hk : 2 ≤ k) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ((Nat.log 2 N + 1) ^ k : ℕ) * (B / (N : ℝ) ^ (1 / 50 : ℝ) * ((N : ℝ) / Real.log 2 ^ 2)) ≤
        ε * scale111 k N := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N1, h1⟩ := polylog_small_split111 2
    (A := 2 ^ k * B / Real.log 2 ^ 4) (by norm_num : (0 : ℝ) < 1 / 50) hε
  refine ⟨max N1 1, fun N hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 ≤ N := lt_of_le_of_lt (le_max_right _ _) hN
  have hpoly := h1 N hN1
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNc : 0 < (N : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  set t : ℝ := Real.log N / Real.log 2
  have ht1 : 1 ≤ t := by
    rw [le_div_iff₀ hl2, one_mul]; exact Real.log_le_log (by norm_num) hNr
  have hlogN : (Nat.log 2 N : ℝ) ≤ t := by
    have hpow : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ hl2).mpr hlog
  have hcount : (((Nat.log 2 N + 1) ^ k : ℕ) : ℝ) ≤ 2 ^ k * t ^ k := by
    push_cast
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have htk : t ^ k = t ^ (k - 2) * (Real.log N ^ 2 / Real.log 2 ^ 2) := by
    rw [show Real.log N ^ 2 / Real.log 2 ^ 2 = t ^ 2 by simp only [t]; rw [div_pow]]
    rw [← pow_add]; congr 1; omega
  set F : ℝ := (N : ℝ) * t ^ (k - 2) / (N : ℝ) ^ (1 / 50 : ℝ)
  have hF : 0 ≤ F := by positivity
  have hX : 0 ≤ B / (N : ℝ) ^ (1 / 50 : ℝ) * ((N : ℝ) / Real.log 2 ^ 2) := by positivity
  calc _ ≤ (2 ^ k * t ^ k) * (B / (N : ℝ) ^ (1 / 50 : ℝ) * ((N : ℝ) / Real.log 2 ^ 2)) :=
        mul_le_mul_of_nonneg_right hcount hX
    _ = (2 ^ k * B / Real.log 2 ^ 4 * Real.log N ^ 2) * F := by
        simp only [F]; rw [htk]; field_simp
    _ ≤ (ε * (N : ℝ) ^ (1 / 50 : ℝ)) * F := mul_le_mul_of_nonneg_right hpoly hF
    _ = ε * scale111 k N := by
        simp only [F, scale111, t]; field_simp

end Burst9Split

/-- P0093 page 167 immediately before equation 10.1. Outside the exceptional
set, T is at most the threshold one minus eta times T at zero. Proved. -/
theorem good_minor_power_bound_split111 (N : ℕ) (η α : ℝ)
    (hα : α ∈ goodMinorArcsSplit111 N η) :
    ‖powerSeriesSplit111 N α‖ ≤ (1 - η) * ‖powerSeriesSplit111 N 0‖ :=
  le_of_not_gt (fun h => hα.2 (Or.inr ⟨hα.1, fun hm => hα.2 (Or.inl hm), h⟩))

/-- SPLIT piece 4 of error_bound111. P0093 page 167 equation 10.1, with Lemma 3
of page 162, equation 7.3, from Romanov 1940. Bounding k minus 2 factors of T
by the threshold and the remaining square by Lemma 3 gives geometric decay in
k minus 2, the factor e of equation 2.2 absorbed in C. -/
theorem minor_error_split111 (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hT : ∀ N : ℕ, ∀ α : ℝ, α ∈ goodMinorArcsSplit111 N η →
      ‖powerSeriesSplit111 N α‖ ≤ (1 - η) * ‖powerSeriesSplit111 N 0‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        |arcContributionSplit111 k N (goodMinorArcsSplit111 N η)| ≤
          C * scale111 k N * (1 - η) ^ (k - 2) := by
  -- PROVE PASS: definitional transport of the ported proved
  -- minor_error_proved357_up111 of CircleSplit111.
  exact minor_error_proved357_up111 η hη hη1 hT

/-- P0093 page 168 following equation 10.6. The singular series is at least one
at every positive even residual, by the existing lab Euler product proof. -/
theorem one_le_singularSeries111 {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) :
    1 ≤ singularSeries111 n := by
  change 1 ≤ LeanLab.Perelli1996.Sing n
  exact LeanLab.Perelli1996.one_le_sing hn (by omega)

/-- P0093 Section 11, page 168. Every tuple in a small exponent box has a positive even residual. -/
theorem cutoff_residual111 {N k L : ℕ} (ν : Fin k → ℕ) (hcut : k * 2 ^ L + 2 ≤ N)
    (hν : ∀ i, 1 ≤ ν i) (hL : ∀ i, ν i ≤ L) (hN : Even N) :
    2 ≤ N - ∑ i, 2 ^ ν i ∧ Even (N - ∑ i, 2 ^ ν i) := by
  have hsum : ∑ i, 2 ^ ν i ≤ k * 2 ^ L := by
    calc
      _ ≤ ∑ _ : Fin k, 2 ^ L := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right (by norm_num) (hL i)
      _ = k * 2 ^ L := by simp
  have htwo : 2 ∣ ∑ i, 2 ^ ν i := by
    apply Finset.dvd_sum
    intro i hi
    exact dvd_pow_self 2 (by have := hν i; omega)
  refine ⟨by omega, ?_⟩
  exact even_iff_two_dvd.mpr (Nat.dvd_sub (even_iff_two_dvd.mp hN) htwo)

/-- P0093 Section 11, page 168. A common logarithmic denominator bounds each positive even summand. -/
theorem main_weight_lower111 {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) (hev : Even n) :
    (n : ℝ) / Real.log N ^ 2 ≤ singularSeries111 n * n / Real.log n ^ 2 := by
  have hnr : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hln := Real.log_pos hnr
  have hlN := Real.log_pos hNr
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) (by exact_mod_cast hnN)
  have hsq : Real.log n ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hsing := one_le_singularSeries111 hev hn
  calc
    _ ≤ (n : ℝ) / Real.log n ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hln) hsq
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (sq_nonneg _)

/-- P0093 Section 11, pages 168 and 169. The full exponent box contributes a uniform lower sum. -/
theorem main_box_lower111 (N k L : ℕ) (hN : Even N) (hLN : L ≤ N) (hcut : k * 2 ^ L + 2 ≤ N)
 :
    (L : ℝ) ^ k * ((N - k * 2 ^ L : ℕ) : ℝ) / Real.log N ^ 2 ≤ mainTerm111 k N := by
  classical
  let e : (Fin k → Fin L) → (Fin k → Fin (N + 1)) :=
    fun ν i => ⟨(ν i).val + 1, by have := (ν i).isLt; omega⟩
  let t := univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧ Even (N - ∑ i, 2 ^ (ν i).val)
  let w : (Fin k → Fin (N + 1)) → ℝ := fun ν =>
    singularSeries111 (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2
  let B : ℝ := ((N - k * 2 ^ L : ℕ) : ℝ) / Real.log N ^ 2
  have hsum (ν : Fin k → Fin L) : ∑ i, 2 ^ ((e ν i).val) ≤ k * 2 ^ L := by
    calc
      _ ≤ ∑ _ : Fin k, 2 ^ L := by
        apply sum_le_sum
        intro i hi
        apply Nat.pow_le_pow_right (by norm_num)
        dsimp [e]
        have := (ν i).isLt
        omega
      _ = _ := by simp
  have ht (ν : Fin k → Fin L) : e ν ∈ t := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact ⟨fun i => by dsimp [e]; omega,
      cutoff_residual111 (fun i => (e ν i).val) hcut
        (fun i => by dsimp [e]; omega)
        (fun i => by dsimp [e]; have := (ν i).isLt; omega) hN⟩
  have hcmp : ∑ _ : Fin k → Fin L, B ≤ mainTerm111 k N := by
    change _ ≤ ∑ ν ∈ t, w ν
    apply sum_le_sum_of_injOn e
    · intro a ha b hb hab
      funext i
      have h := congrArg (fun f => (f i).val) hab
      apply Fin.ext
      dsimp [e] at h
      omega
    · intro z hz
      obtain ⟨ν, hν, rfl⟩ := mem_image.mp hz
      exact ht ν
    · intro ν hν
      have hmem := (mem_filter.mp (ht ν)).2
      have hres : N - k * 2 ^ L ≤ N - ∑ i, 2 ^ (e ν i).val := by have := hsum ν; omega
      have hresr : ((N - k * 2 ^ L : ℕ) : ℝ) ≤ (N - ∑ i, 2 ^ (e ν i).val : ℕ) := by exact_mod_cast hres
      exact (div_le_div_of_nonneg_right hresr (sq_nonneg _)).trans
        (main_weight_lower111 hmem.2.1 (Nat.sub_le _ _) hmem.2.2)
    · intro ν hν hn
      have hmem := (mem_filter.mp hν).2
      have hs := one_le_singularSeries111 hmem.2.2 hmem.2.1
      dsimp [w]
      positivity
  simpa [B, mul_div_assoc] using hcmp

/-- P0093 Section 11, page 169. Bernoulli bounds the power loss from a bounded cutoff gap. -/
theorem power_lower_of_gap111 (k : ℕ) (t L D : ℝ) (ht : 0 < t) (hL : 0 ≤ L)
    (hgap : t - L ≤ D) (hlarge : 2 * k * D ≤ t) : t ^ k / 2 ≤ L ^ k := by
  have hratio : 0 ≤ L / t := div_nonneg hL ht.le
  have hbern := one_add_mul_le_pow (show -2 ≤ L / t - 1 by linarith) k
  have hmid : (1 / 2 : ℝ) ≤ 1 + k * (L / t - 1) := by
    have hid : 1 + k * (L / t - 1) = (t + k * (L - t)) / t := by field_simp
    rw [hid]
    apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have hbern' : (1 / 2 : ℝ) ≤ (L / t) ^ k := by
    have hid : 1 + (L / t - 1) = L / t := by ring
    rw [hid] at hbern
    exact hmid.trans hbern
  rw [div_pow, le_div_iff₀ (pow_pos ht k)] at hbern'
  nlinarith

/-- P0093 Section 11, pages 168 and 169. An explicit logarithmic threshold suffices for the main lower bound. -/
theorem main_lower_at111 (k N : ℕ) (hk : 3 ≤ k) (hN : 4 ≤ N) (hev : Even N)
    (hlarge : 2 * (k : ℝ) * (Real.log (2 * (k : ℝ)) / Real.log 2 + 1) ≤
      Real.log N / Real.log 2) :
    (1 / (4 * Real.log 2 ^ 2)) * scale111 k N ≤ mainTerm111 k N := by
  let t := Real.log N / Real.log 2
  let d := Real.log (2 * (k : ℝ)) / Real.log 2
  let L := ⌊t - d⌋₊
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hkp : (0 : ℝ) < k := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have ht : 0 < t := div_pos hlogN hl2
  have hd : 0 ≤ d := div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  have htd : 0 ≤ t - d := by
    change 2 * (k : ℝ) * (d + 1) ≤ t at hlarge
    nlinarith
  have hLf : (L : ℝ) ≤ t - d := Nat.floor_le htd
  have hX : 0 < (N : ℝ) / (2 * k) := div_pos hNp (by positivity)
  have hpow : (2 : ℝ) ^ L ≤ (N : ℝ) / (2 * k) := by
    apply (Real.log_le_log_iff (pow_pos (by norm_num) L) hX).mp
    rw [Real.log_pow, Real.log_div hNp.ne' (by positivity : 2 * (k : ℝ) ≠ 0)]
    have h := mul_le_mul_of_nonneg_right hLf hl2.le
    dsimp [t, d] at h
    simpa only [sub_mul, div_mul_cancel₀ _ hl2.ne'] using h
  have hdoubleR : (2 : ℝ) * ((k : ℝ) * 2 ^ L) ≤ N := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mp hpow
    nlinarith
  have hdouble : 2 * (k * 2 ^ L) ≤ N := by exact_mod_cast hdoubleR
  have hcut : k * 2 ^ L + 2 ≤ N := by omega
  have hpowN : (2 : ℝ) ^ L ≤ N := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) L]
  have hpowNnat : 2 ^ L ≤ N := by exact_mod_cast hpowN
  have hLN : L ≤ N := (Nat.lt_two_pow_self.trans_le hpowNnat).le
  have hgap : t - (L : ℝ) ≤ d + 1 := by
    have h := Nat.lt_floor_add_one (t - d)
    change t - d < (L : ℝ) + 1 at h
    linarith
  have hLpow := power_lower_of_gap111 k t L (d + 1) ht (Nat.cast_nonneg _) hgap hlarge
  have hres : (N : ℝ) / 2 ≤ ((N - k * 2 ^ L : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show k * 2 ^ L ≤ N by omega)]
    push_cast
    nlinarith
  have hlogeq : Real.log N = t * Real.log 2 := by dsimp [t]; field_simp
  have htpow : t ^ k = t ^ (k - 2) * t ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hid : (1 / (4 * Real.log 2 ^ 2)) * scale111 k N * Real.log N ^ 2 =
      (t ^ k / 2) * ((N : ℝ) / 2) := by
    change (1 / (4 * Real.log 2 ^ 2)) * ((N : ℝ) * t ^ (k - 2)) * Real.log N ^ 2 = _
    rw [hlogeq, htpow]
    field_simp
    ring
  calc
    _ ≤ (L : ℝ) ^ k * ((N - k * 2 ^ L : ℕ) : ℝ) / Real.log N ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hlogN)).mpr
      rw [hid]
      exact mul_le_mul hLpow hres (by positivity) (by positivity)
    _ ≤ _ := main_box_lower111 N k L hev hLN hcut

/-- LEAF. P0093 Section 11, pages 168 and 169. The main term has a uniform
positive lower coefficient for each fixed k and all sufficiently large even N.
The singular series lower bound is the assertion following equation 10.6. -/
theorem main_lower111 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N → c * scale111 k N ≤ mainTerm111 k N := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (4 * Real.log 2 ^ 2), by positivity, ?_⟩
  intro k hk
  let T := 2 * (k : ℝ) * (Real.log (2 * (k : ℝ)) / Real.log 2 + 1)
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp (T * Real.log 2))
  refine ⟨max 4 B, ?_⟩
  intro N hev hN
  have hNB : B < N := lt_of_le_of_lt (le_max_right _ _) hN
  have h4 : 4 ≤ N := by have := le_max_left 4 B; omega
  have hNB' : (B : ℝ) < N := by exact_mod_cast hNB
  have hlarge : T ≤ Real.log N / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    have hh := Real.log_le_log (Real.exp_pos (T * Real.log 2)) (hB.trans hNB').le
    rwa [Real.log_exp] at hh
  exact main_lower_at111 k N hk h4 hev hlarge

/-- LEAF. P0093 Section 11, page 169. Choose a fixed k so the geometric error
coefficient is smaller than the positive main coefficient. -/
theorem choose_exponent111 {C c η : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hη : 0 < η) (hη1 : η < 1) :
    ∃ k : ℕ, 3 ≤ k ∧ 5 * C * (1 - η) ^ (k - 2) < c := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hc (by positivity : 0 < 5 * C))
    (show 1 - η < 1 by linarith)
  refine ⟨n + 3, by omega, ?_⟩
  have hp : (1 - η) ^ (n + 3 - 2) ≤ (1 - η) ^ n :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hh : (1 - η) ^ (n + 3 - 2) < c / (5 * C) := hp.trans_lt hn
  simpa only [mul_comm] using (lt_div_iff₀ (by positivity : 0 < 5 * C)).mp hh

/-- LEAF. P0093 page 169. The scale is positive once N is larger than one. -/
theorem scale_pos111 (k N : ℕ) (hN : 1 < N) : 0 < scale111 k N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (by exact_mod_cast (show 0 < N by omega))
    (pow_pos (div_pos (Real.log_pos hNr) (Real.log_pos (by norm_num))) _)

/-- LEAF. P0093 page 169. A main term larger than its absolute error gives
positive representation count. This is the real arithmetic step. -/
theorem positive_of_error111 {q m s a c : ℝ} (hs : 0 < s) (hac : a < c)
    (hm : c * s ≤ m) (he : |q - m| ≤ a * s) : 0 < q := by
  have h := (abs_le.mp he).1
  nlinarith

end LeanLab.Linnik1951
