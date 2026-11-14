module

public import LeanLab.Linnik.MajorArcEnergy.Leaves13
public import LeanLab.Linnik.MajorArcEnergy.Basic13
public import LeanLab.Linnik.MajorArcEnergy.Display11
public import LeanLab.Linnik.MajorArcEnergy.Display7
public import LeanLab.Linnik.MajorArcEnergy.Display3

/-!
Gallagher 1975 P0094 p.131 display 13, the conductor zero case of the major arc reduction.
Assembled from displays 3, 4, 7, 10, 11 and 12 exactly as on pp.128 to 131.
CONDITIONAL ON the CITED-LEFT leaves of Leaves13.lean, see the main theorem.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries ramanujanSum)
open LeanLab.Linnik.U7204 (Sg)

/-- Gallagher 1975 p.128 after display 3: a member of the family is a primitive character. -/
theorem isPrimitive_of_mem_family {P : ℝ} {x : PChar} (hx : x ∈ family P) :
    x.2.IsPrimitive := by
  unfold family at hx
  rw [Finset.mem_sigma] at hx
  exact (Finset.mem_filter.mp hx.2).2

/-- Gallagher 1975 p.129 display 8 for one pair, from displays 4 and 7:
|J_n(chi, chi')| is at most K n/phi(n) ||A(chi)|| ||A(chi')|| for chi, chi' in the family. -/
theorem pairSum_le_of_mem_family {K : ℝ}
    (hK : ∀ (P : ℝ) (n : ℤ) (x y : PChar), n ≠ 0 →
      x.2.IsPrimitive → y.2.IsPrimitive → pairWeight P n x y ≤ K * totientWeight n)
    (N : ℕ) {P : ℝ} (hP : 0 ≤ P) {n : ℤ} (hn : n ≠ 0) {x y : PChar}
    (hx : x ∈ family P) (hy : y ∈ family P) :
    ‖pairSum N P n x y‖ ≤ K * totientWeight n * ampNorm N P x * ampNorm N P y := by
  have h1 := pair_sum_schwarz N P hP n x y
  have h2 := hK P n x y hn (isPrimitive_of_mem_family hx) (isPrimitive_of_mem_family hy)
  have hax : 0 ≤ ampNorm N P x := Real.sqrt_nonneg _
  have hay : 0 ≤ ampNorm N P y := Real.sqrt_nonneg _
  calc ‖pairSum N P n x y‖ ≤ pairWeight P n x y * ampNorm N P x * ampNorm N P y := h1
    _ ≤ K * totientWeight n * ampNorm N P x * ampNorm N P y := by
      gcongr

/-- Gallagher 1975 p.130, the summation step of displays 8 and 12: a double sum of pair
sums each bounded by c ||A(chi)|| ||A(chi')|| is bounded by c times the product of the
two sums of norms. -/
theorem norm_double_sum_le (s t : Finset PChar) (f : PChar → PChar → ℂ) (a : PChar → ℝ)
    (c : ℝ) (hf : ∀ x ∈ s, ∀ y ∈ t, ‖f x y‖ ≤ c * a x * a y) :
    ‖∑ x ∈ s, ∑ y ∈ t, f x y‖ ≤ c * (∑ x ∈ s, a x) * (∑ y ∈ t, a y) := by
  calc ‖∑ x ∈ s, ∑ y ∈ t, f x y‖ ≤ ∑ x ∈ s, ‖∑ y ∈ t, f x y‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, ∑ y ∈ t, ‖f x y‖ := Finset.sum_le_sum fun x _ => norm_sum_le _ _
    _ ≤ ∑ x ∈ s, ∑ y ∈ t, c * a x * a y :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hf x hx y hy
    _ = c * (∑ x ∈ s, a x) * (∑ y ∈ t, a y) := by
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring

/-- Gallagher 1975 p.130: the split of the pairs into (1, 1), the pairs (1, chi')
with chi' other than 1, and the pairs (chi, chi') with chi other than 1. -/
theorem double_sum_split (F : Finset PChar) (h1 : one ∈ F) (f : PChar → PChar → ℂ) :
    ∑ x ∈ F, ∑ y ∈ F, f x y =
      f one one + ∑ y ∈ F.erase one, f one y + ∑ x ∈ F.erase one, ∑ y ∈ F, f x y := by
  rw [← Finset.add_sum_erase F _ h1, ← Finset.add_sum_erase F _ h1]

/-- Gallagher 1975 p.129: n/phi(n) is at least 1 for n not zero. -/
theorem one_le_totientWeight {n : ℤ} (hn : n ≠ 0) : 1 ≤ totientWeight n := by
  unfold totientWeight
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have ht : 0 < n.natAbs.totient := Nat.totient_pos.mpr hpos
  rw [one_le_div (by exact_mod_cast ht)]
  exact_mod_cast Nat.totient_le _

/-- Gallagher 1975 p.131 display 13: the divisor function tau(n) is at least 1 for n not zero. -/
theorem one_le_divisors_card {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ n.natAbs.divisors.card := by
  have : 0 < n.natAbs.divisors.card :=
    Finset.card_pos.mpr (Nat.nonempty_divisors.mpr (Int.natAbs_ne_zero.mpr hn))
  exact_mod_cast this

/-- Gallagher 1975 p.131, the real arithmetic of display 13: the terms of displays 3,
8, 11 and 12, with ||A(1)|| at most K4 N^(1/2) L^(-1) plus ||R|| from display 10 and
E equal to ||R|| plus S, combine to the normalized form of display 13. Here Q stands
for N L^(-2), sN for N^(1/2) L^(-1), tw for n/phi(n), lp for log P/P and d for tau(n). -/
theorem display13_algebra {cfe K1 K2 K3 K4 Q tw lp d sN R S a1 Pw : ℝ}
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4)
    (hsN : 0 < sN) (hQ : Q = sN ^ 2) (htw : 0 ≤ tw) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (ha1le : a1 ≤ K4 * sN + R) (hX : 0 ≤ lp * d)
    (hPw : Pw ≤ Q * tw * (lp * d))
    (hcfe : cfe ≤ K1 * Pw + K3 * tw * (Q * d * lp + sN * R + R ^ 2) +
      (K2 * tw * a1 * S + K2 * tw * S * (a1 + S))) :
    cfe ≤ (K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2) * Q * tw *
      (lp * d + (1 + (R + S) / sN) * ((R + S) / sN)) := by
  have hY : Q * ((1 + (R + S) / sN) * ((R + S) / sN)) = sN * (R + S) + (R + S) ^ 2 := by
    rw [hQ]; field_simp
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hX0 : 0 ≤ Q * tw * (lp * d) := by positivity
  set E := R + S with hE
  have hE0 : 0 ≤ E := by positivity
  have hYv : 0 ≤ sN * E + E ^ 2 := by positivity
  -- the display 3 term
  have t1 : K1 * Pw ≤ K1 * (Q * tw * (lp * d)) := mul_le_mul_of_nonneg_left hPw hK1
  -- the display 11 term
  have t2 : K3 * tw * (Q * d * lp + sN * R + R ^ 2) ≤
      K3 * (Q * tw * (lp * d)) + K3 * tw * (sN * E + E ^ 2) := by
    have : sN * R + R ^ 2 ≤ sN * E + E ^ 2 := by
      have hRE : R ≤ E := by rw [hE]; linarith
      gcongr
    have hK3tw : 0 ≤ K3 * tw := mul_nonneg hK3 htw
    nlinarith [mul_le_mul_of_nonneg_left this hK3tw]
  -- the displays 8 and 12 terms
  have t3 : K2 * tw * a1 * S + K2 * tw * S * (a1 + S) ≤
      (2 * K2 * K4 + K2) * tw * (sN * E + E ^ 2) := by
    have hin : 2 * a1 * S + S ^ 2 ≤ 2 * K4 * (sN * E) + E ^ 2 := by
      have h1 : a1 * S ≤ (K4 * sN + R) * S := mul_le_mul_of_nonneg_right ha1le hS
      have h2 : K4 * sN * S ≤ K4 * sN * E := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); rw [hE]; linarith
      nlinarith
    have hK2tw : 0 ≤ K2 * tw := mul_nonneg hK2 htw
    have h3 := mul_le_mul_of_nonneg_left hin hK2tw
    have h4 : 0 ≤ K2 * tw * (2 * K4 * (sN * E)) := by positivity
    have h5 : 0 ≤ K2 * tw * (sN * E) := by positivity
    nlinarith
  have hfin : cfe ≤ (K1 + K3) * (Q * tw * (lp * d)) +
      (K3 + 2 * K2 * K4 + K2) * (tw * (sN * E + E ^ 2)) := by nlinarith
  have hgoal : (K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2) * Q * tw *
      (lp * d + (1 + E / sN) * (E / sN)) =
      (K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2) * (Q * tw * (lp * d)) +
      (K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2) * (tw * (sN * E + E ^ 2)) := by
    rw [← hY]; ring
  rw [hgoal]
  have hA : (K1 + K3) * (Q * tw * (lp * d)) ≤
      (K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2) * (Q * tw * (lp * d)) := by
    apply mul_le_mul_of_nonneg_right _ hX0; nlinarith [mul_nonneg hK2 hK4]
  have hB : (K3 + 2 * K2 * K4 + K2) * (tw * (sN * E + E ^ 2)) ≤
      (K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2) * (tw * (sN * E + E ^ 2)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
  linarith

/-- Gallagher 1975 p.131, the size conditions behind the absorption of the O(P^(5/2)) of
display 3 into display 13: for 0 < theta at most 1/8 and N large, with P equal to N^theta,
N is at least 4, log P is at least 1, P/N is at most 1/2, and
P^(5/2) is at most N L^(-2) log P / P. -/
theorem large_N_facts (θ : ℝ) (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 4 ≤ N ∧ 1 ≤ Real.log ((N : ℝ) ^ θ) ∧
      (N : ℝ) ^ θ / N ≤ 1 / 2 ∧
      ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) ≤
        (N : ℝ) / Real.log N ^ 2 * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) := by
  have e1 : ∀ᶠ N : ℕ in Filter.atTop, 4 ≤ N := Filter.eventually_ge_atTop 4
  have e2 : ∀ᶠ N : ℕ in Filter.atTop, 1 / θ ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / θ)
  have e3 : ∀ᶠ N : ℕ in Filter.atTop, Real.log N ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).bound one_pos
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
      tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with N hN hN1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hN
    exact (le_abs_self _).trans hN
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp ((e1.and e2).and e3)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h4, hlog⟩, hL⟩ := hN₀ N hN
  have hNr4 : (4 : ℝ) ≤ N := by exact_mod_cast h4
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogP : Real.log ((N : ℝ) ^ θ) = θ * Real.log N := Real.log_rpow hN0 θ
  have hlogP1 : 1 ≤ Real.log ((N : ℝ) ^ θ) := by
    rw [hlogP]
    have := mul_le_mul_of_nonneg_left hlog hθ.le
    rwa [mul_one_div_cancel hθ.ne'] at this
  have hP0 : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hN0 θ
  have hPsqrt : (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hsq2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (x := 2) (by norm_num)]; norm_num
    calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := this.symm
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) hNr4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine ⟨h4, hlogP1, ?_, ?_⟩
  · rw [div_le_iff₀ hN0]
    nlinarith
  · have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
    have hLsq : Real.log N ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      have h14 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hN0]; norm_num
      rw [← h14, sq]
      exact mul_le_mul hL hL hL0.le (Real.rpow_nonneg hN0.le _)
    have h72 : ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    have hmain : ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) * (Real.log N ^ 2 * (N : ℝ) ^ θ) ≤ N := by
      have hpow0 : 0 ≤ ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) := Real.rpow_nonneg hP0.le _
      calc ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) * (Real.log N ^ 2 * (N : ℝ) ^ θ)
          = (((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ θ) * Real.log N ^ 2 := by ring
        _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul h72 hLsq (by positivity) (Real.rpow_nonneg hN0.le _)
        _ = N := hsq
    have hstep : ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) ≤ (N : ℝ) / (Real.log N ^ 2 * (N : ℝ) ^ θ) := by
      rw [le_div_iff₀ (by positivity)]; exact hmain
    calc ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) ≤ (N : ℝ) / (Real.log N ^ 2 * (N : ℝ) ^ θ) := hstep
      _ = (N : ℝ) / Real.log N ^ 2 * (1 / (N : ℝ) ^ θ) := by field_simp
      _ ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) := by
        gcongr

/-- CONDITIONAL ON the three CITED-LEFT leaves only: `induced_cn_bound` through
`pair_weight_bound_of_cited` in Display7.lean, and `singular_tail_cited` and
`singular_weighted_sums_cited` through `principal_pair_sum_of_leaves` in Display11.lean.
Display 3 is `major_arc_pair_expansion_of_steps`, PROVED in Display3.lean. Gallagher 1975 p.131 display 13: combining display 3, display 8
from 4 and 7, display 11 and display 12 from 4, 7 and 10, the major arc integral is
J(n) S(n) plus O(n/phi(n) (N L^(-2) tau(n) log P / P + (N^(1/2) L^(-1) + E) E)),
and the O(P^(5/2)) of display 3 is absorbed for theta small.
The statement is exactly that of `Decomp486b.major_arc_energy_zero`. -/
theorem major_arc_energy_zero_split
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
          K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
  obtain ⟨K1, θ1, hK1, hθ1, hexp⟩ := major_arc_pair_expansion_of_steps hExpansion
  obtain ⟨K2, hK2, hpw⟩ := pair_weight_bound_of_cited
  obtain ⟨K3, θ3, hK3, hθ3, hpp⟩ := principal_pair_sum_of_leaves
  obtain ⟨K4, hK4, N4, hamp⟩ := principal_amp_norm
  refine ⟨K1 + 2 * K3 + 2 * K2 * K4 + 3 * K2, min θ1 (min θ3 (1 / 8)), by positivity,
    lt_min hθ1 (lt_min hθ3 (by norm_num)), (min_le_right _ _).trans
      ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro θ hθ hθle
  have hθ1' : θ ≤ θ1 := hθle.trans (min_le_left _ _)
  have hθ3' : θ ≤ θ3 := hθle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ8 : θ ≤ 1 / 8 := hθle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N1, h1⟩ := hexp θ hθ hθ1'
  obtain ⟨N3, h3⟩ := hpp θ hθ hθ3'
  obtain ⟨N5, h5⟩ := large_N_facts θ hθ hθ8
  refine ⟨max N1 (max N3 (max N4 N5)), fun N hN n hn => ?_⟩
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN3 : N3 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN4 : N4 ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hN5 : N5 ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  obtain ⟨h4, hlogP1, hPN, hPw⟩ := h5 N hN5
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast h4
  have hN0 : (0 : ℝ) < N := by linarith
  have hP1 : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by linarith) hθ.le
  have hP0 : 0 < (N : ℝ) ^ θ := by linarith
  set P := (N : ℝ) ^ θ with hPdef
  set F := family P with hF
  have hone : one ∈ F := one_mem_family hP1
  set f : PChar → PChar → ℂ := fun x y => pairSum N P n x y with hf
  set a : PChar → ℝ := fun x => ampNorm N P x with ha
  set R := remNorm N P with hRdef
  set S := ∑ x ∈ F.erase one, a x with hSdef
  set I := ∫ α in majorArcs N P,
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α) with hI
  set JS := (Jn N n : ℂ) * singSeries n with hJS
  set tw := totientWeight n with htw
  -- display 8: every pair is bounded by K2 n/phi(n) ||A|| ||A||
  have hpair : ∀ x ∈ F, ∀ y ∈ F, ‖f x y‖ ≤ K2 * tw * a x * a y := fun x hx y hy =>
    pairSum_le_of_mem_family hpw N hP0.le hn hx hy
  have hsumF : ∑ x ∈ F, a x = a one + S := (Finset.add_sum_erase F a hone).symm
  -- the triangle inequality of p.130
  have hsplit : I - JS = (I - ∑ x ∈ F, ∑ y ∈ F, f x y) + (f one one - JS) +
      (∑ y ∈ F.erase one, f one y + ∑ x ∈ F.erase one, ∑ y ∈ F, f x y) := by
    rw [double_sum_split F hone f]; ring
  have hcross1 : ‖∑ y ∈ F.erase one, f one y‖ ≤ K2 * tw * a one * S := by
    have := norm_double_sum_le {one} (F.erase one) f a (K2 * tw) (by
      intro x hx y hy
      rw [Finset.mem_singleton] at hx; subst hx
      exact hpair one hone y (Finset.mem_of_mem_erase hy))
    simpa using this
  have hcross2 : ‖∑ x ∈ F.erase one, ∑ y ∈ F, f x y‖ ≤ K2 * tw * S * (a one + S) := by
    have := norm_double_sum_le (F.erase one) F f a (K2 * tw) (fun x hx y hy =>
      hpair x (Finset.mem_of_mem_erase hx) y hy)
    rwa [hsumF] at this
  have hcfe : complexFrequencyError N θ n ≤ K1 * P ^ (5 / 2 : ℝ) +
      K3 * tw * ((N : ℝ) / Real.log N ^ 2 * n.natAbs.divisors.card *
        (Real.log P / P) + Real.sqrt N / Real.log N * R + R ^ 2) +
      (K2 * tw * a one * S + K2 * tw * S * (a one + S)) := by
    have e : complexFrequencyError N θ n = ‖I - JS‖ := rfl
    rw [e, hsplit]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (h1 N hN1 n) (h3 N hN3 n hn))) ((norm_add_le _ _).trans
      (add_le_add hcross1 hcross2)))
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hsN : 0 < Real.sqrt N / Real.log N := div_pos (Real.sqrt_pos.mpr hN0) hL0
  have hQ : (N : ℝ) / Real.log N ^ 2 = (Real.sqrt N / Real.log N) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hN0.le]
  have htw1 : 1 ≤ tw := one_le_totientWeight hn
  have hd1 := one_le_divisors_card hn
  have hlp : 0 ≤ Real.log P / P * n.natAbs.divisors.card := by positivity
  have hPw' : P ^ (5 / 2 : ℝ) ≤
      (N : ℝ) / Real.log N ^ 2 * tw * (Real.log P / P * n.natAbs.divisors.card) := by
    have hX0 : 0 ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) := by positivity
    calc P ^ (5 / 2 : ℝ) ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) := hPw
      _ = (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) * 1 * 1 := by ring
      _ ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) * tw * n.natAbs.divisors.card := by
        gcongr
      _ = (N : ℝ) / Real.log N ^ 2 * tw * (Real.log P / P * n.natAbs.divisors.card) := by
        ring
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => Real.sqrt_nonneg _
  have ha1le : a one ≤ K4 * (Real.sqrt N / Real.log N) + R := hamp N hN4 P hPN
  have hE : normalizedEnergy N θ 0 0 = (R + S) / (Real.sqrt N / Real.log N) := by
    unfold normalizedEnergy; rw [correctedEnergy_zero_eq N θ hP1]
  rw [hE]
  have key := display13_algebra hK1.le hK2.le hK3.le hK4.le hsN hQ (by linarith) hR0 hS0
    ha1le hlp hPw' (by
      refine hcfe.trans (le_of_eq ?_)
      ring)
  refine key.trans (le_of_eq ?_)
  ring

end LeanLab.Linnik.MajorArcEnergy


