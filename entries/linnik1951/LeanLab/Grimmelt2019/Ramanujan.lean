module

public import LeanLab.Grimmelt2019.MainTerm
public import LeanLab.PNTPort.Vinogradov.MajorArc

/-!
AI wrote this Lean code for CODEX task03.
P0074, pages 13 and 14, the truncated singular series calculation.
The coprime exponential sum is imported from the lab's Vinogradov port.
Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve

/-- The cosine Ramanujan sum is the real part of the exponential sum. -/
theorem ram_eq_re_sum (q : ℕ) (m : ℤ) :
    ram q m = (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * a / q)).re := by
  classical
  unfold ram
  rw [show (Finset.range q).filter (fun a => q.Coprime a) =
      (Finset.range q).filter (fun a => Nat.Coprime a q) by
        ext a; simp only [Finset.mem_filter, Nat.coprime_comm]]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [LeanLab.PNTPort.LargeSieve.e, Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
    mul_zero, sub_zero, add_zero, Real.exp_zero]
  congr 1
  ring

/-- A coprime frequency has Ramanujan sum equal to the Möbius value. -/
theorem ram_coprime {q : ℕ} (hq : 1 ≤ q) {m : ℤ} (hm : Int.gcd m q = 1) :
    ram q m = (ArithmeticFunction.moebius q : ℝ) := by
  rw [ram_eq_re_sum]
  have hc : IsCoprime m (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hm
  rw [LeanLab.PNTPort.Vinogradov.ramanujan_coprime hq hc]
  simp

/-- Convolution with the reduced residue classes multiplies the Ramanujan sum by μ. -/
theorem sum_ram_sub_nat {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), ram q (n - r) =
      (ArithmeticFunction.moebius q : ℝ) * ram q n := by
  classical
  simp_rw [ram_eq_re_sum]
  rw [← Complex.re_sum, Finset.sum_comm]
  have hinner : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        LeanLab.PNTPort.LargeSieve.e (((n - r : ℤ) : ℝ) * a / q) =
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * a / q) * (ArithmeticFunction.moebius q : ℂ) := by
    intro a ha
    have hc : IsCoprime (-(a : ℤ)) (q : ℤ) := by
      apply IsCoprime.neg_left
      exact_mod_cast (Finset.mem_filter.mp ha).2
    rw [← LeanLab.PNTPort.Vinogradov.ramanujan_coprime hq hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero]
  ring

/-- The integer reduced residues and the natural reduced residues give the same sum. -/
theorem sum_reduced_residues (q : ℕ) (f : ℤ → ℝ) :
    ∑ r ∈ (Finset.Ico (0 : ℤ) q).filter (fun r => Int.gcd r q = 1), f r =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), f r := by
  classical
  refine Finset.sum_nbij' Int.toNat (fun r : ℕ => (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr0, hrq⟩ := Finset.mem_Ico.mp hr
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact_mod_cast (show (r.toNat : ℤ) < q by rwa [Int.toNat_of_nonneg hr0])
    · change Nat.gcd r.toNat q = 1
      have hc' : Int.gcd (r.toNat : ℤ) (q : ℤ) = 1 := by
        rwa [Int.toNat_of_nonneg hr0]
      rw [Int.gcd_natCast_natCast] at hc'
      exact hc'
  · intro r hr
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by positivity, by exact_mod_cast Finset.mem_range.mp hr⟩,
      by simpa only [Int.gcd_natCast_natCast] using hc⟩
  · intro r hr
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1).1
  · intro r hr
    simp
  · intro r hr
    rw [Int.toNat_of_nonneg (Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1).1]

/-- The Ramanujan identity in the exact integer form used by `SQ`. -/
theorem sum_ram_sub {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ∑ r ∈ (Finset.Ico (0 : ℤ) q).filter (fun r => Int.gcd r q = 1), ram q (n - r) =
      (ArithmeticFunction.moebius q : ℝ) * ram q n := by
  rw [sum_reduced_residues]
  exact sum_ram_sub_nat hq n

/-- `SQ` equals the paper's Möbius-square truncated singular series. -/
theorem SQ_eq_paper (Q : ℕ) (n : ℤ) :
    SQ Q n = ∑ q ∈ Finset.Icc 1 Q,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * ram q n := by
  unfold SQ
  apply Finset.sum_congr rfl
  intro q hq
  rw [sum_ram_sub (Finset.mem_Icc.mp hq).1]
  ring

/-- The absolute Möbius form printed on page 14 of the paper. -/
theorem SQ_eq_abs_moebius (Q : ℕ) (n : ℤ) :
    SQ Q n = ∑ q ∈ Finset.Icc 1 Q,
      |(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ) ^ 2 * ram q n := by
  rw [SQ_eq_paper]
  apply Finset.sum_congr rfl
  intro q hq
  have hμ : (ArithmeticFunction.moebius q : ℝ) ^ 2 =
      |(ArithmeticFunction.moebius q : ℝ)| := by
    have hz : ArithmeticFunction.moebius q ^ 2 = |ArithmeticFunction.moebius q| := by
      rw [ArithmeticFunction.moebius_sq, ArithmeticFunction.abs_moebius]
    exact_mod_cast hz
  rw [hμ]

end LeanLab.Grimmelt2019.MainTerm
