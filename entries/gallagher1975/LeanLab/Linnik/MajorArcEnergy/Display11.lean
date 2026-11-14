module

public import LeanLab.Linnik.MajorArcEnergy.Leaves13
public import LeanLab.Linnik.MajorArcEnergy.Display9

/-!
Gallagher 1975 P0094 p.130, displays 9 to 11. Display 11 assembled from the leaves
`principal_arc_integral_of_steps` of Display9.lean, `singular_tail_cited` and `singular_weighted_sums_cited`.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries ramanujanSum)

/-- Gallagher 1975 p.130: the modulus one character induces the principal character mod q. -/
theorem induced_one (q : ℕ) : induced one q = 1 := by
  unfold induced
  split_ifs with h
  · exact map_one _
  · rfl

/-- Gallagher 1975 p.130: pairModuli P 1 1 is all q at most P, since lcm 1 1 is 1. -/
theorem pairModuli_one (P : ℝ) : pairModuli P one one = Icc 1 ⌊P⌋₊ := by
  unfold pairModuli
  apply filter_true_of_mem
  intro q _
  simp [one]

/-- Gallagher 1975 p.130: c_n of the principal character mod q is the Ramanujan sum c_q(n). -/
theorem cn_one {q : ℕ} (n : ℤ) :
    cn (1 : DirichletCharacter ℂ q) n = ramanujanSum q n := by
  unfold cn ramanujanSum
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  have hu : IsUnit ((a : ℕ) : ZMod q) ↔ Nat.Coprime a q := ZMod.isUnit_iff_coprime a q
  by_cases hc : Nat.Coprime a q
  · rw [if_pos hc, MulChar.one_apply (hu.mpr hc), one_mul]
    unfold LeanLab.PNTPort.LargeSieve.e LeanLab.Linnik.U1412Display53.eC
    congr 1
    push_cast
    ring
  · rw [if_neg hc, MulChar.map_nonunit _ (fun h => hc (hu.mp h)), zero_mul]

/-- Gallagher 1975 p.130: tau of the principal character mod q is c_q(1) equal to mu(q). -/
theorem ramanujanSum_one {q : ℕ} (hq : 1 ≤ q) :
    ramanujanSum q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  rw [LeanLab.Linnik.Decomp1532b.ramanujanSum_eq_divisor_sum hq]
  simp

/-- Gallagher 1975 p.130: J(n) is nonnegative. -/
theorem Jn_nonneg (N : ℕ) (n : ℤ) : 0 ≤ Jn N n := by
  unfold Jn
  apply sum_nonneg
  intro m _
  have h1 := Real.log_natCast_nonneg m.1
  have h2 := Real.log_natCast_nonneg m.2
  positivity

/-- Gallagher 1975 p.130: the q coefficient of J_n(1, 1) is c_q(n) mu(q)^2, from
c_n(1_q) equal to c_q(n) and tau(1_q) equal to mu(q). -/
theorem pairCoeff_one {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    pairCoeff n q one one =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 * ramanujanSum q n := by
  unfold pairCoeff tau
  rw [induced_one, inv_one, one_mul, cn_one, cn_one, ramanujanSum_one hq]
  simp only [star_intCast]
  ring

/-- Gallagher 1975 p.130 display 11, first line: J_n(1, 1) is the sum over q at most P of
(mu(q)/phi(q))^2 c_q(n) I_{n,q}(1, 1). -/
theorem pairSum_one (N : ℕ) (P : ℝ) (n : ℤ) :
    pairSum N P n one one = ∑ q ∈ Icc 1 ⌊P⌋₊,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ramanujanSum q n * arcIntegral N P n q one one := by
  unfold pairSum
  rw [pairModuli_one]
  apply sum_congr rfl
  intro q hq
  rw [pairCoeff_one (mem_Icc.mp hq).1]
  ring

/-- Gallagher 1975 p.130 display 11: the exact split
J_n(1, 1) minus J(n) S(n) equals the sum over q of (mu(q)/phi(q))^2 c_q(n) (I_{n,q} minus J(n))
plus J(n) times the truncated minus the full singular series. -/
theorem pairSum_one_sub (N : ℕ) (P : ℝ) (n : ℤ) :
    pairSum N P n one one - (Jn N n : ℂ) * singSeries n =
      (∑ q ∈ Icc 1 ⌊P⌋₊,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
          ramanujanSum q n * (arcIntegral N P n q one one - (Jn N n : ℂ))) +
      (Jn N n : ℂ) * (singTrunc P n - singSeries n) := by
  rw [pairSum_one]
  unfold singTrunc
  simp only [mul_sub, sum_sub_distrib, mul_sum]
  have : ∀ q ∈ Icc 1 ⌊P⌋₊, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ramanujanSum q n * (Jn N n : ℂ) = (Jn N n : ℂ) *
      (((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ramanujanSum q n) := fun q _ => by ring
  rw [sum_congr rfl this]
  ring

/-- Gallagher 1975 p.130: J(0) is asymptotic to N/log^2 N, so J(0) is at most
2 N/log^2 N for large N. From the lab's `J0_asymp`. -/
theorem J0_le_two : ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N →
    Jn N 0 ≤ 2 * ((N : ℝ) / Real.log N ^ 2) := by
  have h := (LeanLab.Linnik.Decomp1532b.J0_asymp).eventually
    (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h
  refine ⟨max N₂ 2, fun N hN => ?_⟩
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < (N : ℝ) / Real.log N ^ 2 := by positivity
  have := hN₂ N (le_of_max_le_left hN)
  rw [div_lt_iff₀ hpos] at this
  linarith

/-- Gallagher 1975 p.130: for theta positive, N^theta is at least 3 once N is at least
3^(1/theta), so log P is at least 1 for P equal to N^theta. -/
theorem three_le_rpow {θ : ℝ} (hθ : 0 < θ) {N : ℕ} (hN : ⌈(3 : ℝ) ^ (1 / θ)⌉₊ ≤ N) :
    3 ≤ (N : ℝ) ^ θ := by
  have h1 : (3 : ℝ) ^ (1 / θ) ≤ N := (Nat.ceil_le).mp hN
  have h2 : ((3 : ℝ) ^ (1 / θ)) ^ θ ≤ (N : ℝ) ^ θ :=
    Real.rpow_le_rpow (by positivity) h1 hθ.le
  rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ.ne', Real.rpow_one] at h2

/-- Gallagher 1975 p.130: log 3 is at least 1. -/
theorem one_le_log_of_three_le {P : ℝ} (hP : 3 ≤ P) : 1 ≤ Real.log P := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- Gallagher 1975 p.130: the norm of the q summand of display 11. -/
theorem norm_summand (q : ℕ) (c X : ℂ) :
    ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * c * X‖ =
      ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 * ‖c‖ * ‖X‖ := by
  rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_intCast,
    Complex.norm_natCast, sq_abs]

/-- Gallagher 1975 p.130 display 11, assembled from display 9 `principal_arc_integral_of_steps`, PROVED in Display9.lean,
the identities tau(1_q) equal to mu(q) and c_n(1_q) equal to c_q(n), and the cited
estimates `singular_tail_cited` and `singular_weighted_sums_cited` of reference 10. -/
theorem principal_pair_sum_of_leaves :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ, n ≠ 0 →
        ‖pairSum N ((N : ℝ) ^ θ) n one one - (Jn N n : ℂ) * singSeries n‖ ≤
          K * totientWeight n *
            ((N : ℝ) / Real.log N ^ 2 * n.natAbs.divisors.card *
                (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) +
              Real.sqrt N / Real.log N * remNorm N ((N : ℝ) ^ θ) +
              remNorm N ((N : ℝ) ^ θ) ^ 2) := by
  obtain ⟨K1, θ1, hK1, hθ1, hI⟩ := principal_arc_integral_of_steps
  obtain ⟨K3, hK3, hT⟩ := singular_tail_cited
  obtain ⟨K2, hK2, hW⟩ := singular_weighted_sums_cited
  obtain ⟨N2, hN2⟩ := J0_le_two
  refine ⟨K1 * K2 + 2 * K3, θ1, by positivity, hθ1, ?_⟩
  intro θ hθ hθθ
  obtain ⟨N1, hN1⟩ := hI θ hθ hθθ
  refine ⟨max (max N1 N2) ⌈(3 : ℝ) ^ (1 / θ)⌉₊, ?_⟩
  intro N hN n hn
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hNN2 : N2 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hP3 : 3 ≤ (N : ℝ) ^ θ := three_le_rpow hθ (le_of_max_le_right hN)
  set P := (N : ℝ) ^ θ with hPdef
  have hlogP : 1 ≤ Real.log P := one_le_log_of_three_le hP3
  set L := Real.log N with hLdef
  set R := remNorm N P with hRdef
  set w := totientWeight n with hwdef
  set τ : ℝ := (n.natAbs.divisors.card : ℝ) with hτdef
  set J := Jn N n with hJdef
  set B := Real.sqrt N / L * R + R ^ 2 with hBdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg N
  have hB0 : 0 ≤ B := by positivity
  have hw0 : 0 ≤ w := by rw [hwdef, totientWeight]; positivity
  have hτ0 : 0 ≤ τ := by positivity
  have hJ0 : 0 ≤ J := Jn_nonneg N n
  have hJle : J ≤ 2 * ((N : ℝ) / L ^ 2) :=
    (LeanLab.Linnik.Decomp1532b.Jn_le_J0 N n).trans (hN2 N hNN2)
  obtain ⟨hW1, hW2⟩ := hW P n (by linarith) hn
  have hT1 := hT P n (by linarith) hn
  let a : ℕ → ℝ := fun q =>
    ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 * ‖ramanujanSum q n‖
  have ha0 : ∀ q, 0 ≤ a q := fun q => by positivity
  -- first part: the sum over q
  have hS : ‖∑ q ∈ Icc 1 ⌊P⌋₊,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
          ramanujanSum q n * (arcIntegral N P n q one one - (J : ℂ))‖ ≤
      K1 * K2 * w * ((N : ℝ) / L ^ 2 * τ * (Real.log P / P)) + K1 * K2 * w * B := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_summand]
    calc
      _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, a q * (K1 * (q * ((N : ℝ) / P) / L ^ 2 + B)) := by
        apply sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (by
          have := hN1 N hNN1 n q hq
          rw [hBdef, ← add_assoc]
          exact this) (ha0 q)
      _ = K1 * ((N : ℝ) / P) / L ^ 2 * (∑ q ∈ Icc 1 ⌊P⌋₊, a q * q) +
          K1 * B * (∑ q ∈ Icc 1 ⌊P⌋₊, a q) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ K1 * ((N : ℝ) / P) / L ^ 2 * (K2 * w * τ * Real.log P) + K1 * B * (K2 * w) := by
        gcongr
      _ = _ := by ring
  -- second part: J times the singular tail
  have hJT : ‖(J : ℂ) * (singTrunc P n - singSeries n)‖ ≤
      2 * K3 * w * ((N : ℝ) / L ^ 2 * τ * (Real.log P / P)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hJ0]
    have hP0 : 0 < P := by linarith
    have hX : 0 ≤ K3 * w * τ / P := by positivity
    calc
      _ ≤ 2 * ((N : ℝ) / L ^ 2) * (K3 * w * τ / P) :=
        mul_le_mul hJle hT1 (norm_nonneg _) (by positivity)
      _ = 2 * K3 * w * ((N : ℝ) / L ^ 2 * τ * (1 / P)) := by ring
      _ ≤ _ := by
        gcongr
  rw [pairSum_one_sub]
  refine (norm_add_le _ _).trans ?_
  have hX0 : 0 ≤ (N : ℝ) / L ^ 2 * τ * (Real.log P / P) := by
    have : 0 ≤ Real.log P := by linarith
    have : 0 < P := by linarith
    positivity
  have h2 : 0 ≤ 2 * K3 * w * B := by positivity
  calc
    _ ≤ _ := add_le_add hS hJT
    _ ≤ (K1 * K2 + 2 * K3) * w * ((N : ℝ) / L ^ 2 * τ * (Real.log P / P) + B) := by
      nlinarith
    _ = _ := by rw [hBdef]; ring


end LeanLab.Linnik.MajorArcEnergy
