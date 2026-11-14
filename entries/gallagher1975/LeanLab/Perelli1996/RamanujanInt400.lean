module

public import LeanLab.Perelli1996.Ramanujan400

/-!
Perelli 1996, page 481, the signed Ramanujan sum in equation 3.
The negative frequency is the one used by the polynomial singular mean.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.RamanujanInt400
open Finset
open scoped ComplexConjugate
noncomputable section

/-- Page 481. The Ramanujan sum for an integer frequency. -/
def ramanujanSumInt (q : ℕ) (m : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), Kernel.e ((m : ℝ) * a / q)

/-- Page 481. Natural frequencies agree with the existing sum. -/
theorem ramanujanSumInt_natCast (q m : ℕ) :
    ramanujanSumInt q (m : ℤ) = Ramanujan103.ramanujanSum q m := by
  simp only [ramanujanSumInt, Ramanujan103.ramanujanSum, Int.cast_natCast]

/-- Page 481. Reversing a frequency conjugates its Ramanujan sum. -/
theorem ramanujanSumInt_neg (q : ℕ) (m : ℤ) :
    ramanujanSumInt q (-m) = conj (ramanujanSumInt q m) := by
  unfold ramanujanSumInt
  rw [map_sum]
  simp_rw [Parseval103.conj_e]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  push_cast
  ring

/-- Page 481. The printed Ramanujan formula for every integer frequency. -/
theorem ramanujanSumInt_formula (q : ℕ) (m : ℤ) (hq : 0 < q) :
    ramanujanSumInt q m = (q.totient : ℂ) *
      (ArithmeticFunction.moebius (q / Nat.gcd q m.natAbs) : ℂ) /
        ((q / Nat.gcd q m.natAbs).totient : ℂ) := by
  cases m with
  | ofNat n =>
    simpa using (ramanujanSumInt_natCast q n).trans (Ramanujan400.ramanujanSum_formula q n hq)
  | negSucc n =>
    change ramanujanSumInt q (-((n + 1 : ℕ) : ℤ)) =
      (q.totient : ℂ) * (ArithmeticFunction.moebius (q / Nat.gcd q (n + 1)) : ℂ) /
        ((q / Nat.gcd q (n + 1)).totient : ℂ)
    rw [ramanujanSumInt_neg, ramanujanSumInt_natCast,
      Ramanujan400.ramanujanSum_formula q (n + 1) hq]
    simp

/-- Page 481 equation 3. Signed frequencies have the same value as their absolute value. -/
theorem ramanujanSumInt_eq_natAbs (q : ℕ) (m : ℤ) (hq : 0 < q) :
    ramanujanSumInt q m = Ramanujan103.ramanujanSum q m.natAbs := by
  rw [ramanujanSumInt_formula q m hq, Ramanujan400.ramanujanSum_formula q m.natAbs hq]

end
end LeanLab.Perelli1996.RamanujanInt400
