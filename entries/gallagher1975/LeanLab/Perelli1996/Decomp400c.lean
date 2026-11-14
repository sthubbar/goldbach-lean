module

public import LeanLab.Perelli1996.Ramanujan103

/-!
Perelli 1996, page 481, the Ramanujan formula before equation 3.
The squarefree case is the support of the Mobius squared coefficient there.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Decomp400c
open Finset Real Polynomial
open LeanLab.Perelli1996.Ramanujan103
noncomputable section

/-- Page 481. On squarefree moduli the Ramanujan sum factors at the common divisor. -/
theorem ramanujanSum_squarefree (q m : ℕ) (hq : Squarefree q) :
    ramanujanSum q m = ((Nat.gcd q m).totient : ℂ) *
      (ArithmeticFunction.moebius (q / Nat.gcd q m) : ℂ) := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.gcd_zero_right, Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero)]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, mul_one]
    exact ramanujanSum_dvd q 0 hq.ne_zero.bot_lt (dvd_zero q)
  have hg : 0 < Nat.gcd q m := Nat.gcd_pos_of_pos_left m hq.ne_zero.bot_lt
  have hd : Nat.gcd q m ∣ q := Nat.gcd_dvd_left q m
  have heq : q / Nat.gcd q m * Nat.gcd q m = q := Nat.div_mul_cancel hd
  have hr : 0 < q / Nat.gcd q m := Nat.div_pos (Nat.le_of_dvd hq.ne_zero.bot_lt hd) hg
  have hcop : Nat.Coprime (q / Nat.gcd q m) (Nat.gcd q m) :=
    Nat.coprime_of_squarefree_mul (by rwa [heq])
  conv_lhs => rw [← heq]
  rw [ramanujanSum_mul _ _ m hr hg hcop]
  rw [ramanujanSum_coprime _ m hr (Nat.coprime_div_gcd_of_squarefree hq hm),
    ramanujanSum_dvd _ m hg (Nat.gcd_dvd_right q m)]
  ring

/-- Page 481. The printed totient and Mobius formula holds on every squarefree modulus. -/
theorem ramanujanSum_squarefree_formula (q m : ℕ) (hq : Squarefree q) :
    ramanujanSum q m = ((q.totient : ℝ) *
      (ArithmeticFunction.moebius (q / Nat.gcd q m) : ℝ) /
        (q / Nat.gcd q m).totient : ℂ) := by
  have hg : 0 < Nat.gcd q m := Nat.gcd_pos_of_pos_left m hq.ne_zero.bot_lt
  have hd : Nat.gcd q m ∣ q := Nat.gcd_dvd_left q m
  have heq : q / Nat.gcd q m * Nat.gcd q m = q := Nat.div_mul_cancel hd
  have hr : 0 < q / Nat.gcd q m := Nat.div_pos (Nat.le_of_dvd hq.ne_zero.bot_lt hd) hg
  have hcop : Nat.Coprime (q / Nat.gcd q m) (Nat.gcd q m) :=
    Nat.coprime_of_squarefree_mul (by rwa [heq])
  have ht : q.totient = (q / Nat.gcd q m).totient * (Nat.gcd q m).totient := by
    rw [← Nat.totient_mul hcop, heq]
  have hφ : ((q / Nat.gcd q m).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hr).ne'
  rw [ramanujanSum_squarefree q m hq]
  push_cast
  rw [ht, Nat.cast_mul]
  field_simp [hφ]

/-- Page 481 equation 3. The printed formula holds after the Mobius squared coefficient,
for every modulus, including nonsquarefree moduli. -/
theorem moebius_sq_mul_ramanujanSum (q m : ℕ) :
    (ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q m =
      (ArithmeticFunction.moebius q : ℂ) ^ 2 *
        ((q.totient : ℝ) * (ArithmeticFunction.moebius (q / Nat.gcd q m) : ℝ) /
          (q / Nat.gcd q m).totient : ℂ) := by
  by_cases hq : Squarefree q
  · rw [ramanujanSum_squarefree_formula q m hq]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

end
end LeanLab.Perelli1996.Decomp400c
