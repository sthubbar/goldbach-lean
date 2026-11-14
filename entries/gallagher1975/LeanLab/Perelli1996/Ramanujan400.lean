module

public import LeanLab.Perelli1996.Decomp400c

/-!
Perelli 1996, page 481, the full displayed Ramanujan sum formula.
Extend the existing prime power and multiplicative identities to every positive modulus.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Ramanujan400
open Finset
open LeanLab.Perelli1996.Ramanujan103
noncomputable section

/-- Page 481. The displayed totient and Mobius formula at a positive prime power. -/
theorem ramanujanSum_prime_power_formula (p e m : ℕ) (hp : p.Prime) :
    ramanujanSum (p ^ (e + 1)) m =
      ((p ^ (e + 1)).totient : ℂ) *
        (ArithmeticFunction.moebius (p ^ (e + 1) / Nat.gcd (p ^ (e + 1)) m) : ℂ) /
        ((p ^ (e + 1) / Nat.gcd (p ^ (e + 1)) m).totient : ℂ) := by
  have hq : 0 < p ^ (e + 1) := pow_pos hp.pos _
  by_cases hfull : p ^ (e + 1) ∣ m
  · rw [ramanujanSum_dvd _ m hq hfull, Nat.gcd_eq_left_iff_dvd.mpr hfull,
      Nat.div_self hq]
    simp
  obtain ⟨j, hj, hgj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ (e + 1)) m)
  have hgjm : p ^ j ∣ m := by rw [← hgj]; exact Nat.gcd_dvd_right _ _
  have hje : j ≤ e := by
    have hne : j ≠ e + 1 := by intro h; subst j; exact hfull hgjm
    omega
  have hpe : p ^ e ∣ m ↔ e ≤ j := by
    constructor
    · intro hd
      have hh := Nat.dvd_gcd (pow_dvd_pow p (Nat.le_succ e)) hd
      rw [hgj] at hh
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hh
    · intro hh
      exact dvd_trans (pow_dvd_pow p hh) hgjm
  by_cases hediv : p ^ e ∣ m
  · have hjeq : j = e := by have := hpe.mp hediv; omega
    subst j
    have hquot : p ^ (e + 1) / p ^ e = p := by rw [Nat.pow_div (Nat.le_succ e) hp.pos]; simp
    have ht : (p ^ (e + 1)).totient = p ^ e * p.totient := by
      rw [Nat.totient_prime_pow_succ hp e, Nat.totient_prime hp]
    have hφ : (p.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
    rw [ramanujanSum_prime_pow p e m hp, if_neg hfull, if_pos hediv, Nat.cast_zero, zero_sub,
      hgj, hquot, ArithmeticFunction.moebius_apply_prime hp, ht]
    push_cast
    field_simp [hφ]
  · have hlt : j < e := by
      have hh : ¬ e ≤ j := fun hh => hediv (hpe.mpr hh)
      omega
    have hquot : p ^ (e + 1) / p ^ j = p ^ (e + 1 - j) := Nat.pow_div hj hp.pos
    have hnsq : ¬ Squarefree (p ^ (e + 1 - j)) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      simp only [not_and]
      intro _
      omega
    rw [ramanujanSum_prime_pow p e m hp, if_neg hfull, if_neg hediv, Nat.cast_zero, sub_self,
      hgj, hquot, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
    simp

/-- Page 481. The printed Ramanujan sum formula for every positive modulus. -/
theorem ramanujanSum_formula (q m : ℕ) (hq : 0 < q) :
    ramanujanSum q m = (q.totient : ℂ) *
      (ArithmeticFunction.moebius (q / Nat.gcd q m) : ℂ) /
        ((q / Nat.gcd q m).totient : ℂ) := by
  have hall : ∀ n : ℕ, 0 < n → ramanujanSum n m = (n.totient : ℂ) *
      (ArithmeticFunction.moebius (n / Nat.gcd n m) : ℂ) /
        ((n / Nat.gcd n m).totient : ℂ) := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => intro hn; omega
    | one =>
      intro _
      rw [ramanujanSum_dvd 1 m (by omega) (one_dvd m)]
      simp
    | prime_pow p k hp hk =>
      intro _
      obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact ramanujanSum_prime_power_formula p e m hp
    | coprime a b ha hb hab ia ib =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      have hgcd : Nat.gcd (a * b) m = Nat.gcd a m * Nat.gcd b m := by
        rw [Nat.gcd_comm (a * b) m, hab.gcd_mul m, Nat.gcd_comm m a, Nat.gcd_comm m b]
      have hquot : a * b / Nat.gcd (a * b) m = (a / Nat.gcd a m) * (b / Nat.gcd b m) := by
        rw [hgcd, Nat.mul_div_mul_comm (Nat.gcd_dvd_left a m) (Nat.gcd_dvd_left b m)]
      have hcop : Nat.Coprime (a / Nat.gcd a m) (b / Nat.gcd b m) :=
        hab.of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a m))
          (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left b m))
      rw [ramanujanSum_mul a b m ha0 hb0 hab, ia ha0, ib hb0,
        Nat.totient_mul hab, hquot,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        Nat.totient_mul hcop]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  exact hall q hq

/-- Page 481 equation 3. The Ramanujan norm is bounded by the totient quotient. -/
theorem norm_ramanujanSum_le (q m : ℕ) (hq : 0 < q) :
    ‖ramanujanSum q m‖ ≤ (q.totient : ℝ) / (q / Nat.gcd q m).totient := by
  rw [ramanujanSum_formula q m hq, norm_div, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast, Complex.norm_intCast]
  have hμ : |(ArithmeticFunction.moebius (q / Nat.gcd q m) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / Nat.gcd q m)
  calc
    _ ≤ (q.totient : ℝ) * 1 / (q / Nat.gcd q m).totient :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Page 481 equation 3. Each Mobius weighted coefficient has the printed totient majorant. -/
theorem norm_weighted_ramanujanSum_le (q m : ℕ) (hq : 0 < q) :
    ‖((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) * ramanujanSum q m‖ ≤
      1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hg : 0 < Nat.gcd q m := Nat.gcd_pos_of_pos_left m hq
  have hr : 0 < q / Nat.gcd q m :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q m)) hg
  have hψ : (0 : ℝ) < (q / Nat.gcd q m).totient := by exact_mod_cast Nat.totient_pos.mpr hr
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hμsq : |(ArithmeticFunction.moebius q : ℝ)| ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (ArithmeticFunction.moebius q : ℝ)]
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_intCast, Complex.norm_natCast]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 2) *
        ((q.totient : ℝ) / (q / Nat.gcd q m).totient) :=
      mul_le_mul (div_le_div_of_nonneg_right hμsq (sq_nonneg _))
        (norm_ramanujanSum_le q m hq) (norm_nonneg _)
        (by positivity)
    _ = _ := by field_simp

end
end LeanLab.Perelli1996.Ramanujan400
