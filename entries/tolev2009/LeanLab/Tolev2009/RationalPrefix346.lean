module

public import LeanLab.Tolev2009.Discrepancy346
public import LeanLab.Tolev2009.SeriesIdentification

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 pages 6 to 7, rational progression replacement.
The q equal to one bridge uses the prime theta convention exactly.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.RationalPrefix346
open LeanLab.PNTPort.BVMax
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Progression346 LeanLab.Tolev2009.Discrepancy346

/-- Halupczok page 7, cancel the positive progression totient in the local coefficient. -/
theorem mainCoeff_eq_lifted (k l q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    mainCoeff k l q a =
      (∑ r ∈ liftRes k l q, ee ((a : ℝ) * r / q)) / ((Nat.lcm k q).totient : ℂ) := by
  have hk0 : ((k.totient : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < k)).ne'
  have hm0 : (((Nat.lcm k q).totient : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos (by omega) (by omega))).ne'
  unfold mainCoeff localSum
  field_simp

/-- Halupczok page 7, at most q lifted residues occur in the local coefficient. -/
theorem lifted_card_le (k l q : ℕ) (hq : 1 ≤ q) : (liftRes k l q).card ≤ q := by
  have h := Finset.card_le_card_of_injOn (s := liftRes k l q) (t := range q)
    (fun r => r % q) (fun r _ => mem_range.mpr (Nat.mod_lt r (by omega)))
    (SeriesIdentification.liftRes_projection_inj k l q)
  simpa only [card_range] using h

/-- Halupczok page 7, an elementary local coefficient bound before cancellation in the residue sum. -/
theorem mainCoeff_norm_le (k l q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    ‖mainCoeff k l q a‖ ≤ (q : ℝ) / (Nat.lcm k q).totient := by
  rw [mainCoeff_eq_lifted k l q a hk hq, norm_div]
  have hs : ‖∑ r ∈ liftRes k l q, ee ((a : ℝ) * r / q)‖ ≤ q := by
    refine (norm_sum_le _ _).trans ?_
    simp only [Displays14to16.norm_ee, sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast lifted_card_le k l q hq
  simpa only [Complex.norm_natCast] using div_le_div_of_nonneg_right hs
    (show (0 : ℝ) ≤ (Nat.lcm k q).totient by positivity)

/-- Halupczok page 7, the unit denominator coefficient is the reciprocal progression totient. -/
theorem mainCoeff_one (k l : ℕ) (hk : 1 ≤ k) (hl : Nat.Coprime l k) :
    mainCoeff k l 1 0 = 1 / (k.totient : ℂ) := by
  have hk0 : ((k.totient : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < k)).ne'
  simp [mainCoeff, localSum, liftRes_one hk hl, hk0, ee_zero]

/-- Halupczok page 6, zero phase in the exact prime polynomial is theta, not psi. -/
theorem Sexp_zero_eq_theta (k l m : ℕ) :
    Sexp k l m 0 = (thetaN m k l : ℂ) := by
  unfold thetaN
  rw [sum_filter, Complex.ofReal_sum]
  have hcast (n : ℕ) :
      ((if n % k = l % k ∧ n.Prime then Real.log n else 0 : ℝ) : ℂ) =
        if n % k = l % k ∧ n.Prime then (Real.log n : ℂ) else 0 := by
    split_ifs <;> rfl
  simp_rw [hcast]
  rw [← positive_sum m (fun n =>
    if n % k = l % k ∧ n.Prime then (Real.log n : ℂ) else 0)]
  simp only [Sexp, sum_filter, zero_mul, ee_zero, mul_one]
  apply sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · simp only [if_neg hn0]
    by_cases hp : n.Prime <;> by_cases hc : n % k = l % k <;> simp [hp, hc]

/-- Halupczok page 7, the unit rational denominator prefix is controlled by thetaError. -/
theorem prefixError_one_le (k l N : ℕ) (hk : 1 ≤ k) (hl : Nat.Coprime l k) (hlk : l ≤ k) :
    prefixError k l 1 0 N ≤ thetaError N k := by
  unfold prefixError
  apply Finset.sup'_le
  intro m hm
  rw [prefix_identity, mainCoeff_one k l hk hl]
  simp only [Nat.cast_zero, zero_div]
  rw [Sexp_zero_eq_theta]
  have he : (thetaN m k l : ℂ) - 1 / (k.totient : ℂ) * m =
      ((thetaN m k l - (m : ℝ) / k.totient : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact thetaError_term_le N k m l (by have := mem_range.mp hm; omega) hlk hl

/-- Halupczok page 6, an unconditional unit denominator progression prefix mean.
No identity for nonunit rational phases is assumed. -/
theorem prefixError_one_mean (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ l : ℕ → ℕ,
      (∀ k, 1 ≤ k → l k ≤ k ∧ Nat.Coprime (l k) k) →
        ∑ k ∈ Icc 1 ⌊Real.sqrt N / Real.log N ^ (4 * D + 15)⌋₊,
          prefixError k (l k) 1 0 N ≤ C * N / Real.log N ^ D := by
  obtain ⟨C, hC⟩ := thetaError_mean D hD
  refine ⟨C, fun N hN l hl => ?_⟩
  refine (sum_le_sum fun k hk => ?_).trans (hC N hN)
  have hk1 := (mem_Icc.mp hk).1
  exact prefixError_one_le k (l k) N hk1 (hl k hk1).2 (hl k hk1).1

end LeanLab.Tolev2009.RationalPrefix346
