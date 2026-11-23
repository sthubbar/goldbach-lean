module

public import LeanLab.Linnik1951.CircleSplit111
public import LeanLab.Linnik.Gallagher1975Lemma2

/-!
P0093 pages 162 to 165, Lemma 4 equation 7.6 and its proof 7.7 to 7.18.
Burst 8 p3 port, AI wrote the Lean code. Binary Goldbach is open.

The lab already holds a clean proof of Lemma 4 at the fixed exponent one two hundredth,
large_value_measure435 in Measure435, built from Truncation412, Decomp412c, Phase435,
EntropyBridge412, Alignment435, Decomp435a and Entropy435. Those modules sit downstream
of Decomp111 through SecondMoment111, so Decomp111 cannot import them. This file copies
the needed declarations with the same proofs, renamed with the suffix _l4p111, on top
of CircleSplit111, whose powerFourier111_up111 is the same series. The only new content
is lemma4_measure_general_l4p111 and its finite companion, which run the same assembly
for an arbitrary exponent kappa in place of one two hundredth.
-/

@[expose] public section

namespace LeanLab.Linnik1951

section PortStability412
open Finset

/-- PORT of weighted_power_summable412 from Stability412, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 proof of Lemma 5, differentiation of the damped
series. The first frequency moment converges absolutely for positive N. -/
theorem weighted_power_summable412_l4p111 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => ((2 ^ (m + 1) : ℕ) : ℝ) *
      Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 1 (r := 1 / (N : ℝ)) (by positivity)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  apply (hs.comp_injective hi).congr
  intro m
  simp only [Function.comp_apply, pow_one]
  congr 2
  ring

/-- PORT of weighted_power_bound412 from Stability412, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 proof of Lemma 5, the uniform derivative majorant.
Split the dyadic first moment at the integer logarithm of N. The initial
geometric sum is at most two N and the tail is at most eight N. -/
theorem weighted_power_bound412_l4p111 (N : ℕ) (hN : 1 ≤ N) :
    (∑' m : ℕ, ((2 ^ (m + 1) : ℕ) : ℝ) *
      Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)) ≤ 10 * N := by
  let a : ℕ → ℝ := fun m => ((2 ^ (m + 1) : ℕ) : ℝ) *
    Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let L := Nat.log 2 N
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : Summable a := weighted_power_summable412_l4p111 N hN
  have hlow : (2 : ℝ) ^ L ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have hupp : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have hcap : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by rw [pow_succ]; linarith
  have hhead : ∑ j ∈ range L, a j ≤ 2 * N := by
    have hgeom (l : ℕ) : ∑ j ∈ range l, (2 : ℝ) ^ (j + 1) = 2 ^ (l + 1) - 2 := by
      induction l with
      | zero => norm_num
      | succ l ih => rw [sum_range_succ, ih, pow_succ (2 : ℝ) (l + 1)]; ring
    calc
      _ ≤ ∑ j ∈ range L, (2 : ℝ) ^ (j + 1) := by
        apply sum_le_sum
        intro j hj
        dsimp [a]
        push_cast
        exact mul_le_of_le_one_right (by positivity)
          (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hNp.le))
      _ = 2 ^ (L + 1) - 2 := hgeom L
      _ ≤ _ := by linarith
  have htail (j : ℕ) : a (j + L) ≤ 4 * N * (1 / 2 : ℝ) ^ j := by
    have hratio : (2 : ℝ) ^ j ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) / N := by
      apply (le_div_iff₀ hNp).mpr
      push_cast
      rw [show j + L + 1 = j + (L + 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left hupp (by positivity)
    have he : ((2 : ℝ) ^ j) ^ 2 / 2 ≤ Real.exp ((2 : ℝ) ^ j) := by
      have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    have hx : (0 : ℝ) < 2 ^ j := by positivity
    have hi : (2 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j)) ≤ 2 * (1 / 2 : ℝ) ^ j := by
      calc
        _ = (2 : ℝ) ^ j / Real.exp ((2 : ℝ) ^ j) := by rw [Real.exp_neg]; ring
        _ ≤ 2 / (2 : ℝ) ^ j :=
          (div_le_div_iff₀ (Real.exp_pos _) hx).mpr (by nlinarith)
        _ = _ := by rw [one_div_pow]; ring
    calc
      a (j + L) ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) * Real.exp (-((2 : ℝ) ^ j)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by rw [neg_div]; exact neg_le_neg hratio)
      _ = (2 : ℝ) ^ (L + 1) * ((2 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j))) := by
        push_cast
        rw [show j + L + 1 = (L + 1) + j by omega, pow_add]
        ring
      _ ≤ (2 * N) * (2 * (1 / 2 : ℝ) ^ j) := mul_le_mul hcap hi (by positivity) (by positivity)
      _ = _ := by ring
  have htailSum : (∑' j : ℕ, a (j + L)) ≤ 8 * N := by
    have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (4 * (N : ℝ))
    calc
      _ ≤ ∑' j : ℕ, 4 * (N : ℝ) * (1 / 2 : ℝ) ^ j :=
        Summable.tsum_le_tsum htail (ha.comp_injective (add_left_injective L)) hg
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  change (∑' m, a m) ≤ _
  rw [← ha.sum_add_tsum_nat_add L]
  linarith

end PortStability412


section PortTruncation412
open Finset

/-- PORT of powerTrunc412 from Truncation412, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 equation 7.7. The finite damped polynomial contains
exactly the positive powers of two at most N. -/
noncomputable def powerTrunc412_l4p111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ range (Nat.log 2 N),
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)

/-- PORT of power_trunc_error412 from Truncation412, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 passage from equation 7.5 to 7.7 and page 161
7.2. The discarded dyadic tail has uniformly bounded norm. Ten is a
conservative constant from the proved first moment bound. -/
theorem power_trunc_error412_l4p111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖powerFourier111_up111 N α - powerTrunc412_l4p111 N α‖ ≤ 10 := by
  let L := Nat.log 2 N
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let w : ℕ → ℝ := fun m => ((2 ^ (m + 1) : ℕ) : ℝ) * a m
  let f : ℕ → ℂ := fun m => (a m : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : Summable f := power_fourier_summable111_up111 N hN α
  have hw : Summable w := weighted_power_summable412_l4p111 N hN
  have hcut : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have hterm (j : ℕ) : ‖f (j + L)‖ ≤ w (j + L) / N := by
    have hfreq : (N : ℝ) ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) := by
      apply hcut.trans
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [f, w, a]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]
    apply (le_div_iff₀ hNp).mpr
    nlinarith [Real.exp_pos (-((2 ^ (j + L + 1) : ℕ) : ℝ) / N)]
  have htail : (∑' j : ℕ, w (j + L)) ≤ ∑' j : ℕ, w j := by
    rw [← hw.sum_add_tsum_nat_add L]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j hj => by dsimp [w, a]; positivity))
  have heq : powerFourier111_up111 N α - powerTrunc412_l4p111 N α = ∑' j : ℕ, f (j + L) := by
    change (∑' j, f j) - ∑ j ∈ range L, f j = _
    rw [← hf.sum_add_tsum_nat_add L]
    ring
  rw [heq]
  calc
    _ ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm
      (hf.comp_injective (add_left_injective L)).norm
    _ ≤ ∑' j : ℕ, w (j + L) / N :=
      Summable.tsum_le_tsum hterm (hf.comp_injective (add_left_injective L)).norm
        ((hw.comp_injective (add_left_injective L)).div_const N)
    _ = (∑' j : ℕ, w (j + L)) / N := tsum_div_const
    _ ≤ (∑' j : ℕ, w j) / N := div_le_div_of_nonneg_right htail hNp.le
    _ ≤ (10 * (N : ℝ)) / N := div_le_div_of_nonneg_right (weighted_power_bound412_l4p111 N hN) hNp.le
    _ = 10 := by field_simp

/-- PORT of power_trunc_zero_lower412 from Truncation412, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 equation 7.7. At zero every retained damping
weight is at least exp of negative one. Thus the finite polynomial grows
at least linearly in the integer base two logarithm of N. -/
theorem power_trunc_zero_lower412_l4p111 (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-1) * Nat.log 2 N ≤ ‖powerTrunc412_l4p111 N 0‖ := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heq : powerTrunc412_l4p111 N 0 = ((∑ m ∈ range (Nat.log 2 N), a m : ℝ) : ℂ) := by
    simp [powerTrunc412_l4p111, a, Complex.ofReal_sum]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le))]
  calc
    _ = ∑ _m ∈ range (Nat.log 2 N), Real.exp (-1) := by simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Real.exp_le_exp.mpr
      have hp : 2 ^ (m + 1) ≤ N :=
        (Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hm)).trans
          (Nat.pow_log_le_self 2 (show N ≠ 0 by omega))
      rw [neg_div]
      apply neg_le_neg
      exact (div_le_one hNp).mpr (by exact_mod_cast hp)

/-- PORT of large_value_to_trunc412 from Truncation412, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 equation 7.7. A fixed large value margin absorbs
the bounded discarded tail once the finite polynomial at zero is large.
Only the finite polynomial remains on the right side. -/
theorem large_value_to_trunc412_l4p111 (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ α : ℝ,
      (1 - η / 2) * ‖powerFourier111_up111 N 0‖ < ‖powerFourier111_up111 N α‖ →
      (1 - η) * ‖powerTrunc412_l4p111 N 0‖ < ‖powerTrunc412_l4p111 N α‖ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (20 / (η * Real.exp (-1)))
  refine ⟨max 1 (2 ^ M), ?_⟩
  intro N hN α hlarge
  have h1 : 1 ≤ N := by have := le_max_left 1 (2 ^ M); omega
  have hpow : 2 ^ M ≤ N := by have := le_max_right 1 (2 ^ M); omega
  have hlog : M ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hpow
  have hL : (M : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hlog
  have hbig : 20 < η * ‖powerTrunc412_l4p111 N 0‖ := by
    have hm := (div_lt_iff₀ (mul_pos hη (Real.exp_pos _))).mp hM
    have hb := power_trunc_zero_lower412_l4p111 N h1
    have hbη := mul_le_mul_of_nonneg_left hb hη.le
    have hLη := mul_le_mul_of_nonneg_left hL (mul_pos hη (Real.exp_pos (-1))).le
    nlinarith
  have hzero : ‖powerTrunc412_l4p111 N 0‖ ≤ ‖powerFourier111_up111 N 0‖ := by
    let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
    have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
      (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
    have ha : Summable a := (damping_summable111_up111 N h1).comp_injective hi
    have heq : powerFourier111_up111 N 0 = ((∑' m, a m : ℝ) : ℂ) := by
      unfold powerFourier111_up111
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro m
      simp [a]
    rw [heq]
    simp only [powerTrunc412_l4p111, mul_zero, zero_mul, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero, mul_one, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le)),
      abs_of_nonneg (tsum_nonneg (fun m => (Real.exp_pos _).le))]
    exact ha.sum_le_tsum _ (fun m hm => (Real.exp_pos _).le)
  have hdiff := power_trunc_error412_l4p111 N h1 α
  have hnorm := norm_sub_norm_le (powerFourier111_up111 N α) (powerTrunc412_l4p111 N α)
  have hz := mul_le_mul_of_nonneg_left hzero (show 0 ≤ 1 - η / 2 by linarith)
  nlinarith

end PortTruncation412


section PortDecomp412c
open MeasureTheory Finset

/-- PORT of nearIntegerIndices412 from Decomp412c, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 equation 7.11. Indices of the first M positive
powers whose phase lies within two to negative r of an integer. -/
noncomputable def nearIntegerIndices412_l4p111 (M r : ℕ) (α : ℝ) : Finset ℕ := by
  classical
  exact (range M).filter fun m => ∃ z : ℤ,
    |α * (2 : ℝ) ^ (m + 1) - z| ≤ (1 / 2 : ℝ) ^ r

/-- PORT of dyadic_measure_scale412 from Decomp412c, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 conversion from binary length to N after 7.19.
For a negative exponent a between negative one and zero, using the
integer logarithm costs at most a factor two. -/
theorem dyadic_measure_scale412_l4p111 (N : ℕ) (hN : 1 ≤ N) (a : ℝ)
    (ha : -1 ≤ a) (ha0 : a ≤ 0) :
    (2 : ℝ) ^ ((Nat.log 2 N : ℝ) * a) ≤ 2 * (N : ℝ) ^ a := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut : (N : ℝ) / 2 ≤ (2 : ℝ) ^ Nat.log 2 N := by
    have hh : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
    rw [pow_succ] at hh
    linarith
  have hpow : (2 : ℝ) ^ (-a) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := Real.rpow_one _
  calc
    _ = ((2 : ℝ) ^ Nat.log 2 N) ^ a := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ ≤ ((N : ℝ) / 2) ^ a :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcut ha0
    _ = (N : ℝ) ^ a * (2 : ℝ) ^ (-a) := by
      rw [Real.div_rpow hNp.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ (N : ℝ) ^ a * 2 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end PortDecomp412c


section PortPhase435
open Finset

/-- PORT of adjacent_pair435 from Phase435, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 after equation 7.10. More than half of a finite
interval, with its endpoint allowance, contains an adjacent pair. -/
theorem adjacent_pair435_l4p111 (M : ℕ) (S : Finset ℕ) (hS : S ⊆ range M)
    (hcard : M + 1 < 2 * S.card) : ∃ n : ℕ, n ∈ S ∧ n + 1 ∈ S := by
  classical
  by_contra h
  push_neg at h
  have hd : Disjoint S (S.image (fun n => n + 1)) := by
    apply Finset.disjoint_left.mpr
    intro m hm him
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp him
    exact h n hn hm
  have hsub : S ∪ S.image (fun n => n + 1) ⊆ range (M + 1) := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have := Finset.mem_range.mp (hS hm)
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      have := Finset.mem_range.mp (hS hn)
      exact Finset.mem_range.mpr (by omega)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (add_left_injective 1), Finset.card_range] at hc
  omega

/-- PORT of rotation_removal435 from Phase435, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 the two displays after equation 7.10 and equation
7.11. If a set of dyadic phases clusters within rho of a common
rotation and contains an adjacent pair, all its phases lie within
four rho of integers. This uses no Fourier or measure estimate. -/
theorem rotation_removal435_l4p111 (α φ ρ : ℝ) (S : Finset ℕ)
    (hcluster : ∀ m ∈ S, ∃ z : ℤ, |α * (2 : ℝ) ^ (m + 1) - φ - z| ≤ ρ)
    (n : ℕ) (hn : n ∈ S) (hn1 : n + 1 ∈ S) :
    ∀ m ∈ S, ∃ z : ℤ, |α * (2 : ℝ) ^ (m + 1) - z| ≤ 4 * ρ := by
  obtain ⟨a, ha⟩ := hcluster n hn
  obtain ⟨b, hb⟩ := hcluster (n + 1) hn1
  have hpow : α * (2 : ℝ) ^ (n + 1 + 1) = 2 * (α * (2 : ℝ) ^ (n + 1)) := by
    rw [pow_succ]
    ring
  rw [hpow] at hb
  have hφ : |φ - ((b - 2 * a : ℤ) : ℝ)| ≤ 3 * ρ := by
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    apply abs_le.mpr
    push_cast
    constructor <;> linarith
  intro m hm
  obtain ⟨c, hc⟩ := hcluster m hm
  refine ⟨c + (b - 2 * a), ?_⟩
  have hc' := abs_le.mp hc
  have hφ' := abs_le.mp hφ
  apply abs_le.mpr
  push_cast at *
  constructor <;> linarith

/-- PORT of cluster_to_near_indices435 from Phase435, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 equation 7.11. A common rotation cluster of
fraction at least one minus epsilon over two gives the required
near integer index count, once epsilon is below one half and M is
at least four. The radius is one quarter of the desired radius. -/
theorem cluster_to_near_indices435_l4p111 (M r : ℕ) (hM : 4 ≤ M) (α φ ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (S : Finset ℕ)
    (hS : S ⊆ range M) (hc : (1 - ε / 2) * (M : ℝ) ≤ S.card)
    (hp : ∀ m ∈ S, ∃ z : ℤ,
      |α * (2 : ℝ) ^ (m + 1) - φ - z| ≤ (1 / 2 : ℝ) ^ r / 4) :
    (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card := by
  classical
  have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hcardR : (M : ℝ) + 1 < 2 * S.card := by nlinarith
  have hcard : M + 1 < 2 * S.card := by exact_mod_cast hcardR
  obtain ⟨n, hn, hn1⟩ := adjacent_pair435_l4p111 M S hS hcard
  have hrot := rotation_removal435_l4p111 α φ ((1 / 2 : ℝ) ^ r / 4) S hp n hn hn1
  have hsub : S ⊆ nearIntegerIndices412_l4p111 M r α := by
    intro m hm
    obtain ⟨z, hz⟩ := hrot m hm
    apply Finset.mem_filter.mpr
    refine ⟨hS hm, z, ?_⟩
    linarith
  have hle : (S.card : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card := by
    exact_mod_cast Finset.card_le_card hsub
  nlinarith

end PortPhase435


section PortEntropyBridge412
open Finset

/-- PORT of near_phase_digit_equal412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 after equation 7.12. A near integer doubling at
binary radius at most one sixteenth forces two adjacent binary digits
 to agree. Reuse the proved lab cosine to digit implication from P0094
page 132 Lemma 1. -/
theorem near_phase_digit_equal412_l4p111 (M r m : ℕ) (hr : 4 ≤ r) (α : ℝ)
    (hm : m ∈ nearIntegerIndices412_l4p111 M r α) :
    LeanLab.Linnik.Gallagher1975Lemma1.digit α (m + 2) =
      LeanLab.Linnik.Gallagher1975Lemma1.digit α (m + 3) := by
  classical
  obtain ⟨_, z, hz⟩ := Finset.mem_filter.mp hm
  have hrad : (1 / 2 : ℝ) ^ r ≤ 1 / 16 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hr
    norm_num at h ⊢
    exact h
  have habs := abs_le.mp (hz.trans hrad)
  have harg : 2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α - z) ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcos := Real.cos_pos_of_mem_Ioo harg
  have heq : 2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α) =
      2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α - z) + (z : ℝ) * (2 * Real.pi) := by ring
  have hp : 0 < Real.cos (2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α)) := by
    rw [heq, Real.cos_add_int_mul_two_pi]
    exact hcos
  simpa only [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega] using
    LeanLab.Linnik.Gallagher1975Lemma1.digit_eq_of_cos_pos α (m + 1) hp

/-- PORT of changes_le_bad_indices412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 164 binary run count leading to 7.13. Every change
in the interior digit string corresponds injectively to an index outside
the near integer set. This supplies the exact exceptional set needed
by the existing Gallagher finite word counting proof. -/
theorem changes_le_bad_indices412_l4p111 (M r : ℕ) (hr : 4 ≤ r) (α : ℝ) :
    (LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card ≤
      M - (nearIntegerIndices412_l4p111 M r α).card := by
  classical
  have hc : (LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card ≤
      ((range M) \ nearIntegerIndices412_l4p111 M r α).card := by
    apply Finset.card_le_card_of_injOn (fun m : ℕ => m - 2)
    · intro m hm
      have hmem := Finset.mem_filter.mp hm
      have hb := Finset.mem_Icc.mp hmem.1
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr (by change m - 2 < M; omega), ?_⟩
      intro hnear
      have heq := near_phase_digit_equal412_l4p111 M r (m - 2) hr α hnear
      have h1 : m - 2 + 2 = m := by omega
      have h2 : m - 2 + 3 = m + 1 := by omega
      rw [h1, h2] at heq
      exact hmem.2 heq
    · intro m hm n hn hmn
      have hm2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
      have hn2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      change m - 2 = n - 2 at hmn
      omega
  have hs : nearIntegerIndices412_l4p111 M r α ⊆ range M := Finset.filter_subset _ _
  simpa only [Finset.card_sdiff_of_subset hs, Finset.card_range] using hc

/-- PORT of changes_fraction_bound412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 164 equations 7.13 through 7.15. The concentration
fraction implies the corresponding real upper bound for digit changes.
The existing Gallagher count and binomial estimate can now be reused. -/
theorem changes_fraction_bound412_l4p111 (M r : ℕ) (hr : 4 ≤ r) (α ε : ℝ)
    (hgood : (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card) :
    ((LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card : ℝ) ≤ ε * M := by
  classical
  have hc := changes_le_bad_indices412_l4p111 M r hr α
  have hs : (nearIntegerIndices412_l4p111 M r α).card ≤ M := by
    simpa only [nearIntegerIndices412_l4p111, Finset.card_range] using Finset.card_filter_le
      (s := range M) (p := fun m => ∃ z : ℤ, |α * (2 : ℝ) ^ (m + 1) - z| ≤ (1 / 2 : ℝ) ^ r)
  have hR : ((LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card : ℝ) ≤
      (M : ℝ) - (nearIntegerIndices412_l4p111 M r α).card := by
    exact_mod_cast hc
  linarith

/-- PORT of concentrated_word_mem412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 164 equation 7.13 and page 165 equation 7.19.
The binary word of a concentrated phase belongs to the exact finite
word set already counted in the proved Gallagher module. -/
theorem concentrated_word_mem412_l4p111 (M r : ℕ) (hr : 4 ≤ r) (α ε : ℝ)
    (hα : α ∈ Set.Ico 0 1)
    (hgood : (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card) :
    ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, ?_⟩
  · have hfloor := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (M + 1)) hα.1)
    have hn : (⌊(2 : ℝ) ^ (M + 1) * α⌋₊ : ℝ) < (2 : ℝ) ^ (M + 1) := by
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (M + 1), hα.2]
    exact_mod_cast hn
  · rw [← LeanLab.Linnik.Gallagher1975Lemma1.changes_eq_bitChanges hα.1]
    have h := changes_fraction_bound412_l4p111 M r hr α ε hgood
    convert h using 1 <;> ring

/-- PORT of binary_cells_measure412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 after equation 7.19. A finite collection of binary
words covers its phases by equal dyadic cells. Its measure is at most
the word count times their common length. -/
theorem binary_cells_measure412_l4p111 (M : ℕ) (S : Finset ℕ) :
    MeasureTheory.volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ S} ≤
        (S.card : ENNReal) * ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := by
  classical
  have hsub : {α : ℝ | α ∈ Set.Ico 0 1 ∧ ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ S} ⊆
      ⋃ n ∈ S, Set.Ico ((n : ℝ) / 2 ^ (M + 1)) (((n : ℝ) + 1) / 2 ^ (M + 1)) := by
    intro α hα
    let n := ⌊(2 : ℝ) ^ (M + 1) * α⌋₊
    have hnlo : (n : ℝ) ≤ 2 ^ (M + 1) * α := Nat.floor_le (mul_nonneg (by positivity) hα.1.1)
    have hnhi : (2 : ℝ) ^ (M + 1) * α < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    refine Set.mem_iUnion₂.mpr ⟨n, hα.2, ?_, ?_⟩
    · exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (M + 1))).mpr (by nlinarith)
    · exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (M + 1))).mpr (by nlinarith)
  calc
    _ ≤ MeasureTheory.volume (⋃ n ∈ S,
        Set.Ico ((n : ℝ) / 2 ^ (M + 1)) (((n : ℝ) + 1) / 2 ^ (M + 1))) :=
      MeasureTheory.measure_mono hsub
    _ ≤ ∑ n ∈ S, MeasureTheory.volume
        (Set.Ico ((n : ℝ) / 2 ^ (M + 1)) (((n : ℝ) + 1) / 2 ^ (M + 1))) :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [Real.volume_Ico]
      have he (n : ℕ) : ((n : ℝ) + 1) / 2 ^ (M + 1) - (n : ℝ) / 2 ^ (M + 1) =
          1 / 2 ^ (M + 1) := by ring
      simp only [he, Finset.sum_const, nsmul_eq_mul]

/-- PORT of binary_unit_measure_le_words412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 164 word count and page 165 conversion to measure.
The actual near integer phase set in one period is bounded by the
proved Gallagher word count at parameter epsilon over four. -/
theorem binary_unit_measure_le_words412_l4p111 (M r : ℕ) (hr : 4 ≤ r) (ε : ℝ) :
    MeasureTheory.volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} ≤
        ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ENNReal) *
          ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := by
  apply le_trans (MeasureTheory.measure_mono (t := {α : ℝ | α ∈ Set.Ico 0 1 ∧
    ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)}) ?_)
    (binary_cells_measure412_l4p111 M _)
  intro α hα
  exact ⟨hα.1, concentrated_word_mem412_l4p111 M r hr α ε hα.1 hα.2⟩

/-- PORT of near_indices_int_shift412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 binary expansion and page 165 measure bound.
Integer translation preserves the exact near integer index set.
Thus the binary concentration condition is periodic with period one. -/
theorem near_indices_int_shift412_l4p111 (M r : ℕ) (α : ℝ) (z : ℤ) :
    nearIntegerIndices412_l4p111 M r (α + z) = nearIntegerIndices412_l4p111 M r α := by
  classical
  ext m
  simp only [nearIntegerIndices412_l4p111, Finset.mem_filter]
  apply and_congr_right
  intro hm
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - z * 2 ^ (m + 1), ?_⟩
    have he : α * (2 : ℝ) ^ (m + 1) - ((k - z * 2 ^ (m + 1) : ℤ) : ℝ) =
        (α + z) * (2 : ℝ) ^ (m + 1) - k := by push_cast; ring
    rw [he]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k + z * 2 ^ (m + 1), ?_⟩
    have he : (α + z) * (2 : ℝ) ^ (m + 1) - ((k + z * 2 ^ (m + 1) : ℤ) : ℝ) =
        α * (2 : ℝ) ^ (m + 1) - k := by push_cast; ring
    rw [he]
    exact hk

/-- PORT of binary_word_card_bound412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 164 binomial estimate 7.15 and Gallagher page 133
counting proof. Reuse the proved finite word injection and small subset
bound to retain the explicit entropy expression before choosing epsilon. -/
theorem binary_word_card_bound412_l4p111 (M : ℕ) (ε : ℝ)
    (hε : 0 < ε * M) (hM : ε * M ≤ (M - 1 : ℕ)) :
    ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ℝ) ≤
      4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) := by
  classical
  have he : 4 * (ε / 4) * (M : ℝ) = ε * M := by ring
  have hc := LeanLab.Linnik.Gallagher1975Lemma1.card_T_le M (ε / 4)
  rw [he] at hc
  have hcard : (Icc 2 M).card = M - 1 := by simp
  have hs := LeanLab.Linnik.Gallagher1975Lemma1.card_small_subsets_le
    (Icc 2 M) hε (by simpa only [hcard] using hM)
  rw [hcard] at hs
  have hcR : ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ℝ) ≤
      4 * ({S ∈ (Icc 2 M).powerset | (S.card : ℝ) ≤ ε * M}.card : ℝ) := by
    exact_mod_cast hc
  exact hcR.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

/-- PORT of binary_unit_measure_explicit412 from EntropyBridge412, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 conversion of word count to measure after 7.19.
The actual binary concentration set in one period satisfies the explicit
binomial entropy bound already proved in the Gallagher counting library.
Only the small fraction choice and bounded period extension remain. -/
theorem binary_unit_measure_explicit412_l4p111 (M r : ℕ) (hr : 4 ≤ r) (ε : ℝ)
    (hε : 0 < ε * M) (hM : ε * M ≤ (M - 1 : ℕ)) :
    MeasureTheory.volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} ≤
        ENNReal.ofReal (4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) /
          (2 : ℝ) ^ (M + 1)) := by
  have hc := binary_word_card_bound412_l4p111 M ε hε hM
  have hcE : ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ENNReal) ≤
      ENNReal.ofReal (4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hc
  calc
    _ ≤ ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ENNReal) *
        ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := binary_unit_measure_le_words412_l4p111 M r hr ε
    _ ≤ ENNReal.ofReal (4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M)) *
        ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := mul_le_mul_left hcE _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end PortEntropyBridge412


section PortAlignment435
open Finset Complex

/-- PORT of cosine_deficit_radius435 from Alignment435, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 equation 7.10. For every positive radius there
is a positive cosine deficit threshold that forces distance to an
integer within that radius. Round supplies the nearest integer. -/
theorem cosine_deficit_radius435_l4p111 (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : ℝ, 1 - Real.cos (2 * Real.pi * x) < d →
      ∃ z : ℤ, |x - z| ≤ ρ := by
  let t : ℝ := min ρ (1 / 4)
  have ht : 0 < t := lt_min hρ (by norm_num)
  have ht4 : t ≤ 1 / 4 := min_le_right _ _
  have htp : 2 * Real.pi * t ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (2 * Real.pi * t) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      htp (by positivity : (0 : ℝ) < 2 * Real.pi * t)
    simpa only [Real.cos_zero] using h
  refine ⟨1 - Real.cos (2 * Real.pi * t), by linarith, ?_⟩
  intro x hx
  refine ⟨round x, ?_⟩
  by_contra h
  have hr : ρ < |x - (round x : ℤ)| := lt_of_not_ge h
  have hrhalf : |x - (round x : ℤ)| ≤ (1 / 2 : ℝ) := abs_sub_round x
  have hcosx : Real.cos (2 * Real.pi * x) =
      Real.cos (2 * Real.pi * |x - (round x : ℤ)|) := by
    have he : 2 * Real.pi * x = 2 * Real.pi * (x - (round x : ℤ)) +
        (round x : ℤ) * (2 * Real.pi) := by ring
    rw [he, Real.cos_add_int_mul_two_pi, ← Real.cos_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2 * Real.pi * t by positivity)
    (show 2 * Real.pi * |x - (round x : ℤ)| ≤ Real.pi by nlinarith [Real.pi_pos])
    (show 2 * Real.pi * t ≤ 2 * Real.pi * |x - (round x : ℤ)| by
      exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hr.le) (by positivity))
  rw [hcosx] at hx
  linarith

/-- PORT of rotation_cosine435 from Alignment435, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 equation 7.8. A unit complex rotation is an
exponential of its argument. Multiplying a negative Fourier phase by
that rotation subtracts one common real phase inside the cosine. -/
theorem rotation_cosine435_l4p111 (u : ℂ) (hu : ‖u‖ = 1) (x : ℝ) :
    (u * Complex.exp ((-(2 * Real.pi * x) : ℝ) * Complex.I)).re =
      Real.cos (2 * Real.pi * (x - u.arg / (2 * Real.pi))) := by
  have he : Complex.exp ((u.arg : ℂ) * Complex.I) = u := by
    simpa only [hu, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I u
  conv_lhs => rw [← he, ← Complex.exp_add]
  have ha : (u.arg : ℂ) * Complex.I +
      ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * (x - u.arg / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [ha, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- PORT of weighted_deficit435 from Alignment435, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 equations 7.8 and 7.9. The weighted cosine
deficit is small when the norm of the weighted phase sum is almost
its total weight. This is the finite scalar identity before counting
exceptional indices. -/
theorem weighted_deficit435_l4p111 (M : ℕ) (w θ : ℕ → ℝ) (η : ℝ)
    (hw : ∀ m ∈ range M, 0 ≤ w m ∧ w m ≤ 1)
    (hη : 0 ≤ η)
    (hlarge : (1 - η) * (∑ m ∈ range M, w m) <
      ‖∑ m ∈ range M, (w m : ℂ) *
        Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)‖) :
    ∃ φ : ℝ, ∑ m ∈ range M, w m *
      (1 - Real.cos (2 * Real.pi * (θ m - φ))) < η * M := by
  let Z : ℂ := ∑ m ∈ range M, (w m : ℂ) *
    Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)
  obtain ⟨u, hu, huZ⟩ := LeanLab.Linnik.Gallagher1975Lemma1.exists_rot Z
  refine ⟨u.arg / (2 * Real.pi), ?_⟩
  have hs : (u * Z).re = ∑ m ∈ range M, w m *
      Real.cos (2 * Real.pi * (θ m - u.arg / (2 * Real.pi))) := by
    dsimp [Z]
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [show u * ((w m : ℂ) * Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)) =
      (w m : ℂ) * (u * Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      rotation_cosine435_l4p111 u hu (θ m)]
  have hW : (∑ m ∈ range M, w m) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ _m ∈ range M, (1 : ℝ) := Finset.sum_le_sum (fun m hm => (hw m hm).2)
      _ = _ := by simp
  have heq : (∑ m ∈ range M, w m *
      (1 - Real.cos (2 * Real.pi * (θ m - u.arg / (2 * Real.pi))))) =
      (∑ m ∈ range M, w m) - ‖Z‖ := by
    calc
      _ = ∑ m ∈ range M, (w m - w m *
          Real.cos (2 * Real.pi * (θ m - u.arg / (2 * Real.pi)))) := by
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← hs, huZ]
  rw [heq]
  change (1 - η) * (∑ m ∈ range M, w m) < ‖Z‖ at hlarge
  nlinarith

/-- PORT of weighted_bad_count435 from Alignment435, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 the exceptional index count between equations
7.8 and 7.9. Positive lower damping weights turn a small total
weighted deficit into a small number of indices above a fixed deficit.
Only finite sums and real inequalities occur here. -/
theorem weighted_bad_count435_l4p111 (M : ℕ) (w D : ℕ → ℝ) (ε d : ℝ)
    (hε : 0 < ε) (hd : 0 < d)
    (hw : ∀ m ∈ Finset.range M, Real.exp (-1) ≤ w m)
    (hD : ∀ m ∈ Finset.range M, 0 ≤ D m)
    (hs : ∑ m ∈ Finset.range M, w m * D m <
      ε * d * Real.exp (-1) * M) :
    ((Finset.range M).filter (fun m => d ≤ D m)).card ≤ ε * (M : ℝ) := by
  classical
  let B := (Finset.range M).filter (fun m => d ≤ D m)
  have hb : (B.card : ℝ) * (d * Real.exp (-1)) ≤
      ∑ m ∈ Finset.range M, w m * D m := by
    calc
      _ = ∑ _m ∈ B, d * Real.exp (-1) := by simp
      _ ≤ ∑ m ∈ B, w m * D m := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hw' := hw m hm'.1
        simpa only [mul_comm] using
          (mul_le_mul hw' hm'.2 hd.le ((Real.exp_pos (-1)).le.trans hw'))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun m hm _ => mul_nonneg ((Real.exp_pos (-1)).le.trans (hw m hm)) (hD m hm))
  have hp : 0 < d * Real.exp (-1) := mul_pos hd (Real.exp_pos _)
  change (B.card : ℝ) ≤ ε * M
  nlinarith

/-- PORT of weighted_phase_alignment_proved435 from Alignment435, same proof, renamed so that Decomp111 can use it.
 P0093 page 162 equations 7.8 and 7.9 through page 163 equation
7.10. The exact generic weighted alignment input follows from the
rotation identity, weighted deficit count and cosine radius bound. -/
theorem weighted_phase_alignment_proved435_l4p111 (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∀ M : ℕ,
      ∀ w θ : ℕ → ℝ,
        (∀ m ∈ Finset.range M, Real.exp (-1) ≤ w m ∧ w m ≤ 1) →
        (1 - η) * (∑ m ∈ Finset.range M, w m) <
          ‖∑ m ∈ Finset.range M, (w m : ℂ) *
            Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)‖ →
        ∃ φ : ℝ, ∃ S : Finset ℕ, S ⊆ Finset.range M ∧
          (1 - ε) * (M : ℝ) ≤ S.card ∧
          ∀ m ∈ S, ∃ z : ℤ, |θ m - φ - z| ≤ ρ := by
  classical
  obtain ⟨d, hd, hradius⟩ := cosine_deficit_radius435_l4p111 ρ hρ
  let η : ℝ := min (ε * d * Real.exp (-1)) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ ε * d * Real.exp (-1) := min_le_left _ _
  refine ⟨η, hη, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro M w θ hw hlarge
  obtain ⟨φ, hsum⟩ := weighted_deficit435_l4p111 M w θ η
    (fun m hm => ⟨(Real.exp_pos (-1)).le.trans (hw m hm).1, (hw m hm).2⟩) hη.le hlarge
  let D : ℕ → ℝ := fun m => 1 - Real.cos (2 * Real.pi * (θ m - φ))
  have hD : ∀ m ∈ Finset.range M, 0 ≤ D m := fun m _ =>
    sub_nonneg.mpr (Real.cos_le_one _)
  have hcount := weighted_bad_count435_l4p111 M w D ε d hε hd
    (fun m hm => (hw m hm).1) hD
    (lt_of_lt_of_le hsum (mul_le_mul_of_nonneg_right hηsmall (Nat.cast_nonneg M)))
  let B := (Finset.range M).filter (fun m => d ≤ D m)
  let S := Finset.range M \ B
  refine ⟨φ, S, Finset.sdiff_subset, ?_, ?_⟩
  · have hB : B.card ≤ M := by
      simpa using (Finset.card_le_card (Finset.filter_subset (fun m => d ≤ D m) (Finset.range M)))
    have hc : (S.card : ℝ) = (M : ℝ) - B.card := by
      dsimp only [S]
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range,
        Nat.cast_sub hB]
    rw [hc]
    change (B.card : ℝ) ≤ ε * M at hcount
    linarith
  · intro m hm
    have hb := (Finset.mem_sdiff.mp hm).2
    have hm' := (Finset.mem_sdiff.mp hm).1
    have hlt : D m < d := by
      by_contra h
      exact hb (Finset.mem_filter.mpr ⟨hm', le_of_not_gt h⟩)
    exact hradius (θ m - φ) hlt

end PortAlignment435


section PortDecomp435a
open Finset

/-- PORT of finite_phase_concentration_decomposed435 from Decomp435a, same proof, renamed so that Decomp111 can use it.
 P0093 page 163 equation 7.11. Exact finite_phase_concentration412
statement, assembled from weighted alignment and the proved adjacent
pair rotation removal. Both components now have clean proofs. -/
theorem finite_phase_concentration_decomposed435_l4p111 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (r : ℕ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, α ∈ Set.Icc (-1) 2 →
        (1 - η) * ‖powerTrunc412_l4p111 N 0‖ < ‖powerTrunc412_l4p111 N α‖ →
          (1 - ε) * (Nat.log 2 N : ℝ) ≤
            (nearIntegerIndices412_l4p111 (Nat.log 2 N) r α).card := by
  obtain ⟨η, hη, hηhalf, ha⟩ :=
    weighted_phase_alignment_proved435_l4p111 (ε / 2) ((1 / 2 : ℝ) ^ r / 4) (by positivity) (by positivity)
  refine ⟨η, hη, hηhalf, 16, ?_⟩
  intro N hN α _ hlarge
  have h1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  let w : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let θ : ℕ → ℝ := fun m => α * (2 : ℝ) ^ (m + 1)
  have hw : ∀ m ∈ range (Nat.log 2 N), Real.exp (-1) ≤ w m ∧ w m ≤ 1 := by
    intro m hm
    have hp : 2 ^ (m + 1) ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hm)).trans
        (Nat.pow_log_le_self 2 (by omega))
    constructor
    · apply Real.exp_le_exp.mpr
      have hdiv : (((2 ^ (m + 1) : ℕ) : ℝ) / N) ≤ 1 :=
        (div_le_one hNp).mpr (by exact_mod_cast hp)
      rw [neg_div]
      linarith
    · apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hNp.le
  have hzero : ‖powerTrunc412_l4p111 N 0‖ = ∑ m ∈ range (Nat.log 2 N), w m := by
    simp only [powerTrunc412_l4p111, mul_zero, zero_mul, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero, mul_one, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le))
  have hpoly : (∑ m ∈ range (Nat.log 2 N), (w m : ℂ) *
      Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)) = powerTrunc412_l4p111 N α := by
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [w, θ]
    congr 2
    push_cast
    ring
  rw [hzero] at hlarge
  obtain ⟨φ, S, hS, hc, hp⟩ := ha (Nat.log 2 N) w θ hw (by rwa [hpoly])
  exact cluster_to_near_indices435_l4p111 (Nat.log 2 N) r hM α φ ε hε hεhalf S hS hc hp

end PortDecomp435a


section PortEntropy435
open MeasureTheory Filter
open scoped Topology

/-- PORT of entropy_fraction435 from Entropy435, same proof, renamed so that Decomp111 can use it.
 P0093 page 164 equation 7.18 and page 165 equation 7.19.
The entropy cost tends to zero with the exceptional fraction.
This is the parameter choice after the binary word count. -/
theorem entropy_fraction435_l4p111 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ε * Real.log (Real.exp 1 / ε) ≤ δ * Real.log 2 := by
  have hcont : Continuous (fun x : ℝ => x - x * Real.log x) :=
    continuous_id.sub Real.continuous_mul_log
  have hbudget : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos (by norm_num))
  have hevent : ∀ᶠ x : ℝ in nhds 0, x - x * Real.log x < δ * Real.log 2 := by
    have ht : Tendsto (fun x : ℝ => x - x * Real.log x) (nhds 0) (nhds 0) := by
      simpa using (hcont.continuousAt (x := 0)).tendsto
    exact ht.eventually (gt_mem_nhds hbudget)
  obtain ⟨a, ha, haall⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε : ℝ := min (a / 2) (1 / 4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεa : ε < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  refine ⟨ε, hε, by linarith, ?_⟩
  have hb := haall (show dist ε 0 < a by simpa [Real.dist_eq, abs_of_pos hε] using hεa)
  rw [Real.log_div (Real.exp_ne_zero _) hε.ne', Real.log_exp]
  nlinarith

/-- PORT of entropy_unit_bound435 from Entropy435, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 after equation 7.19. The explicit finite word
bound is at most four times the prescribed dyadic measure scale once
the entropy cost is below delta log two. -/
theorem entropy_unit_bound435_l4p111 (M r : ℕ) (hM : 2 ≤ M) (hr : 4 ≤ r)
    (ε δ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hcost : ε * Real.log (Real.exp 1 / ε) ≤ δ * Real.log 2) :
    volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} ≤
        ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hsmall : ε * (M : ℝ) ≤ (M - 1 : ℕ) := by
    rw [hcast]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hbase : Real.exp 1 * (M - 1 : ℕ) / (ε * M) ≤ Real.exp 1 / ε := by
    rw [div_le_div_iff₀ (mul_pos hε hMp) hε]
    have hm : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
    calc
      Real.exp 1 * (M - 1 : ℕ) * ε = (Real.exp 1 * ε) * (M - 1 : ℕ) := by ring
      _ ≤ (Real.exp 1 * ε) * M := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Real.exp 1 * (ε * M) := by ring
  have hp : (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) ≤
      (2 : ℝ) ^ ((M : ℝ) * δ) := by
    calc
      _ ≤ (Real.exp 1 / ε) ^ (ε * M) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ ≤ (2 : ℝ) ^ ((M : ℝ) * δ) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by norm_num)]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hcost hMp.le]
  refine (binary_unit_measure_explicit412_l4p111 M r hr ε (mul_pos hε hMp) hsmall).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ 4 * (2 : ℝ) ^ ((M : ℝ) * δ) / (2 : ℝ) ^ (M + 1) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ ≤ 4 * (2 : ℝ) ^ ((M : ℝ) * δ) / (2 : ℝ) ^ M := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) M]
    _ = _ := by
      rw [← Real.rpow_natCast, mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- PORT of entropy_three_periods435 from Entropy435, same proof, renamed so that Decomp111 can use it.
 P0093 page 165 measure conclusion after equation 7.19.
Three consecutive periods cost at most three unit period measures.
Integer translation preserves the concentration predicate. -/
theorem entropy_three_periods435_l4p111 (M r : ℕ) (ε : ℝ) :
    volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} ≤
      3 * volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
        (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} := by
  let s : Set ℝ := {α | α ∈ Set.Ico 0 1 ∧
    (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card}
  have hsub : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} ⊆
      ((fun α : ℝ => α + 1) ⁻¹' s) ∪ s ∪
        ((fun α : ℝ => α + (-1)) ⁻¹' s) ∪ {2} := by
    intro α hα
    by_cases h0 : α < 0
    · apply Set.mem_union_left
      apply Set.mem_union_left
      apply Set.mem_union_left
      refine ⟨⟨by linarith [hα.1.1], by linarith⟩, ?_⟩
      simpa only [show (1 : ℝ) = (1 : ℤ) by norm_num,
        near_indices_int_shift412_l4p111] using hα.2
    · by_cases h1 : α < 1
      · exact Or.inl (Or.inl (Or.inr ⟨⟨by linarith, h1⟩, hα.2⟩))
      · by_cases h2 : α < 2
        · apply Set.mem_union_left
          apply Set.mem_union_right
          refine ⟨⟨by linarith, by linarith⟩, ?_⟩
          simpa only [show (-1 : ℝ) = (-1 : ℤ) by norm_num,
            near_indices_int_shift412_l4p111] using hα.2
        · exact Or.inr (by simpa only [Set.mem_singleton_iff] using
            (show α = 2 by linarith [hα.1.2]))
  calc
    _ ≤ volume ((((fun α : ℝ => α + 1) ⁻¹' s) ∪ s) ∪
        ((fun α : ℝ => α + (-1)) ⁻¹' s) ∪ {2}) := measure_mono hsub
    _ ≤ ((volume ((fun α : ℝ => α + 1) ⁻¹' s) + volume s) +
        volume ((fun α : ℝ => α + (-1)) ⁻¹' s)) + volume ({2} : Set ℝ) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ = 3 * volume s := by
      rw [measure_preimage_add_right, measure_preimage_add_right]
      simp [show (3 : ENNReal) = 1 + 1 + 1 by norm_num, add_mul]

/-- PORT of binary_entropy_measure_proved435 from Entropy435, same proof, renamed so that Decomp111 can use it.
 P0093 pages 164 and 165 binary word count and measure conclusion.
The exact binary_entropy_measure412 statement has a clean proof from
the proved Gallagher word count. No cited entropy input is used. -/
theorem binary_entropy_measure_proved435_l4p111 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∃ r : ℕ, 4 ≤ r ∧
      ∃ C : ℝ, 0 < C ∧ ∃ M0 : ℕ, ∀ M : ℕ, M0 < M →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412_l4p111 M r α).card} ≤
            C * (2 : ℝ) ^ ((M : ℝ) * (δ - 1)) := by
  obtain ⟨ε, hε, hεhalf, hc⟩ := entropy_fraction435_l4p111 δ hδ
  refine ⟨ε, hε, hεhalf, 4, le_rfl, 12, by norm_num, 1, ?_⟩
  intro M hM
  have hu := entropy_unit_bound435_l4p111 M 4 (by omega) le_rfl ε δ hε hεhalf hc
  have ht := (entropy_three_periods435_l4p111 M 4 ε).trans (mul_le_mul' le_rfl hu)
  have he : (3 : ENNReal) * ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) =
      ENNReal.ofReal (12 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by
    rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [he] at ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal

end PortEntropy435


section PortAssembly
open MeasureTheory Filter
open scoped Topology

/-- P0093 pages 162 to 165, Lemma 4 for the finite polynomial 7.7, with the exponent
kappa of 7.6 free. Same assembly as finite_large_value_measure435 in Measure435, which is
the case kappa equal to one two hundredth: the phase concentration 7.8 to 7.11, the binary
digit and entropy count 7.12 to 7.18, and the passage from M to N after 7.18. -/
theorem finite_large_value_measure_general_l4p111 (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - η) * ‖powerTrunc412_l4p111 N 0‖ < ‖powerTrunc412_l4p111 N α‖} ≤
            C * (N : ℝ) ^ (κ - 1) := by
  obtain ⟨ε, hε, hεhalf, r, hr, C, hC, M0, hm⟩ :=
    binary_entropy_measure_proved435_l4p111 κ hκ
  obtain ⟨η, hη, hηhalf, Na, ha⟩ :=
    finite_phase_concentration_decomposed435_l4p111 ε hε hεhalf r
  refine ⟨η, hη, hηhalf, 2 * C, by positivity, max 1 (max Na (2 ^ (M0 + 1))), ?_⟩
  intro N hN
  have h1 : 1 ≤ N := by have := le_max_left 1 (max Na (2 ^ (M0 + 1))); omega
  have hNa : Na < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hpow : 2 ^ (M0 + 1) ≤ N := by
    have := le_trans (le_max_right Na (2 ^ (M0 + 1))) (le_max_right 1 (max Na (2 ^ (M0 + 1))))
    omega
  have hM : M0 < Nat.log 2 N := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hpow
    omega
  have hsub : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - η) * ‖powerTrunc412_l4p111 N 0‖ < ‖powerTrunc412_l4p111 N α‖} ⊆
      {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
        (1 - ε) * (Nat.log 2 N : ℝ) ≤ (nearIntegerIndices412_l4p111 (Nat.log 2 N) r α).card} :=
    fun α hα => ⟨hα.1, ha N hNa α hα.1 hα.2⟩
  have hfinite : volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (Nat.log 2 N : ℝ) ≤ (nearIntegerIndices412_l4p111 (Nat.log 2 N) r α).card} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  calc
    _ ≤ volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
        (1 - ε) * (Nat.log 2 N : ℝ) ≤ (nearIntegerIndices412_l4p111 (Nat.log 2 N) r α).card} :=
      measureReal_mono hsub hfinite
    _ ≤ C * (2 : ℝ) ^ ((Nat.log 2 N : ℝ) * (κ - 1)) := hm _ hM
    _ ≤ C * (2 * (N : ℝ) ^ (κ - 1)) :=
      mul_le_mul_of_nonneg_left
        (dyadic_measure_scale412_l4p111 N h1 _ (by linarith) (by linarith)) hC.le
    _ = _ := by ring

/-- P0093 page 162 equation 7.6, Lemma 4, read at 2 eta as in the proof of Lemma 5 on
page 165, with the exponent kappa free. Same passage from the full series to the finite
polynomial 7.7 as large_value_measure435 in Measure435, which is the case kappa equal to
one two hundredth. -/
theorem large_value_measure_general_l4p111 (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - 2 * η) * ‖powerFourier111_up111 N 0‖ < ‖powerFourier111_up111 N α‖} ≤
            C * (N : ℝ) ^ (κ - 1) := by
  obtain ⟨η, hη, hηhalf, C, hC, Nm, hm⟩ := finite_large_value_measure_general_l4p111 κ hκ hκ1
  obtain ⟨Nt, ht⟩ := large_value_to_trunc412_l4p111 η hη (by linarith)
  refine ⟨η / 4, by positivity, by linarith, C, hC, max Nm Nt, ?_⟩
  intro N hN
  have hmN : Nm < N := lt_of_le_of_lt (le_max_left _ _) hN
  have htN : Nt < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hsub : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - 2 * (η / 4)) * ‖powerFourier111_up111 N 0‖ < ‖powerFourier111_up111 N α‖} ⊆
      {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
        (1 - η) * ‖powerTrunc412_l4p111 N 0‖ < ‖powerTrunc412_l4p111 N α‖} := by
    intro α hα
    refine ⟨hα.1, ht N htN α ?_⟩
    convert hα.2 using 1
    ring
  have hfinite : volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - η) * ‖powerTrunc412_l4p111 N 0‖ < ‖powerTrunc412_l4p111 N α‖} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  exact (measureReal_mono hsub hfinite).trans (hm N hmN)

end PortAssembly

end LeanLab.Linnik1951
