module

public import LeanLab.Linnik1951.Divisor376
public import LeanLab.PerelliPintz1992.Decomp1519
public import LeanLab.Perelli1996.SingularDivisor88

/-!
P0093 page 168 equations 10.5 and 10.6. Reuse the proved lab singular tail.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 167 definition before equation 10.4. The two lab
Ramanujan sums agree at positive moduli despite their residue ranges. -/
theorem ramanujan_eq_perelli_pintz376 (q n : ℕ) (hq : 1 ≤ q) :
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n =
      LeanLab.PerelliPintz1992.Decomp1519.ram q (n : ℤ) := by
  classical
  by_cases hq1 : q = 1
  · subst q
    simp only [LeanLab.Perelli1996.Ramanujan103.ramanujanSum,
      LeanLab.PerelliPintz1992.Decomp1519.ram,
      LeanLab.PerelliPintz1992.Decomp1519.As]
    norm_num [LeanLab.Perelli1996.Kernel.e, LeanLab.PerelliPintz1992.e]
    convert (Complex.exp_nat_mul_two_pi_mul_I n).symm using 1 <;> push_cast <;> ring
  · have hsets : LeanLab.PerelliPintz1992.Decomp1519.As q =
        (Finset.range q).filter (fun b => Nat.Coprime b q) := by
      ext b
      simp only [LeanLab.PerelliPintz1992.Decomp1519.As, mem_filter, mem_Icc, mem_range]
      by_cases hb0 : b = 0
      · subst b; simp [Nat.coprime_zero_left, hq1]
      · by_cases hbq : b = q
        · subst b; simp [Nat.coprime_self, hq1]
        · omega
    unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum
      LeanLab.PerelliPintz1992.Decomp1519.ram
    rw [hsets]
    apply Finset.sum_congr rfl
    intro a ha
    unfold LeanLab.Perelli1996.Kernel.e LeanLab.PerelliPintz1992.e
    congr 1
    push_cast
    ring

/-- P0093 page 168 equation 10.6. The prime Euler product agrees with
the existing finite odd prime factor form at a positive even residual. -/
theorem singular_eq_heath_brown376 (n : ℕ) (hn : 2 ≤ n) (hev : Even n) :
    singularSeries111 n = LeanLab.HeathBrown1985.singular n := by
  classical
  change LeanLab.Perelli1996.Sing n = _
  rw [LeanLab.Perelli1996.Section3.sing_even_divisor_sum n (by omega) hev,
    LeanLab.Perelli1996.Section3.sum_arithmeticFactor n (by omega)]
  unfold LeanLab.Perelli1996.Section3.singularConstant LeanLab.HeathBrown1985.singular
  rw [if_pos hev, Finset.prod_filter]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_cases hp2 : 2 < p
  · rw [if_pos hp2, LeanLab.Perelli1996.Section3.arithmeticFactor_prime hprime hp2]
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
    have hpne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp [hpne]
    <;> ring
  · have hpeq : p = 2 := by have := hprime.two_le; omega
    subst p
    rw [if_neg (by omega), LeanLab.Perelli1996.Section3.arithmeticFactor_even (by norm_num)]
    norm_num

/-- P0093 page 168 equation 10.6. The even residual product is the
Perelli Pintz singular series at half the residual. -/
theorem singular_eq_perelli_pintz376 (k : ℕ) (hk : 1 ≤ k) :
    singularSeries111 (2 * k) = LeanLab.PerelliPintz1992.S2k k := by
  classical
  rw [singular_eq_heath_brown376 (2 * k) (by omega) (by exact ⟨k, by omega⟩)]
  have hsets : (2 * k).primeFactors.filter (2 < ·) = k.primeFactors.filter (2 < ·) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp, hpd, hp0⟩ := Nat.mem_primeFactors.mp hp
      refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, ?_, by omega⟩, hp2⟩
      exact (hpp.dvd_mul.mp hpd).resolve_left (fun h => by
        have := Nat.le_of_dvd (by norm_num : 0 < 2) h
        omega)
    · intro hp
      obtain ⟨hp, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp, hpd, hp0⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
        ⟨hpp, hpd.trans (Nat.dvd_mul_left k 2), by omega⟩, hp2⟩
  rw [LeanLab.HeathBrown1985.singular, if_pos (show Even (2 * k) from ⟨k, by omega⟩),
    LeanLab.PerelliPintz1992.S2k, hsets]

/-- P0093 page 168 finite singular series. Reversing the phase
conjugates the finite sum, and the real coefficients are unchanged. -/
theorem singular_cutoff_conj376 (k Q : ℕ) :
    (starRingEnd ℂ) (∑ q ∈ Finset.Icc 1 Q,
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q (2 * k)) =
      ∑ q ∈ Finset.Icc 1 Q,
        ((LeanLab.PerelliPintz1992.Decomp1519.muφ q ^ 2 : ℝ) : ℂ) *
          LeanLab.PerelliPintz1992.Decomp1519.ram q (-(2 * k : ℤ)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [map_mul, Complex.conj_ofReal,
    ramanujan_eq_perelli_pintz376 q (2 * k) (Finset.mem_Icc.mp hq).1]
  have hmu : (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 =
      LeanLab.PerelliPintz1992.Decomp1519.muφ q ^ 2 := by
    rw [LeanLab.PerelliPintz1992.Decomp1519.muφ, div_pow]
  rw [hmu]
  congr 1
  unfold LeanLab.PerelliPintz1992.Decomp1519.ram
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [LeanLab.PerelliPintz1992.conj_e]
  congr 1
  push_cast
  ring

/-- P0093 page 168 equation 10.5 at the integer cutoff. Taking a floor
in Q equal to N to one tenth costs at most a factor two after the inverse
square root. This does not use any singular series input. -/
theorem inverse_sqrt_floor376 (N : ℕ) (hN : 1 ≤ N) :
    1 / Real.sqrt (⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ) ≤
      2 * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
  let x := (N : ℝ) ^ (1 / 10 : ℝ)
  let Q := ⌊x⌋₊
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hQ : 1 ≤ Q := Nat.floor_pos.mpr hx
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hfloor : x ≤ 2 * (Q : ℝ) := by
    have h := Nat.lt_floor_add_one x
    change x < (Q : ℝ) + 1 at h
    linarith
  have hsq : ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    dsimp [x]
    congr 1
    norm_num
  have hrootQ : 0 < Real.sqrt (Q : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hNr : 0 < (N : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hroot : (N : ℝ) ^ (1 / 20 : ℝ) ≤ 2 * Real.sqrt (Q : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Q by positivity)]
  change 1 / Real.sqrt (Q : ℝ) ≤ _
  rw [Real.rpow_neg (Nat.cast_nonneg N)]
  apply (div_le_iff₀ hrootQ).mpr
  calc
    (1 : ℝ) ≤ (2 * Real.sqrt (Q : ℝ)) / (N : ℝ) ^ (1 / 20 : ℝ) :=
      (le_div_iff₀ hNr).mpr (by simpa using hroot)
    _ = _ := by ring

/-- P0093 page 168 equations 10.5 and 10.6. Exact
 divisor_dependent_tail376 statement from the already proved Perelli
Pintz tail theorem and the convention bridges above. -/
theorem divisor_dependent_tail_proved376 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n - singularSeries111 n| ≤
          C * (n.divisors.card : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
  obtain ⟨C, hC, ht⟩ := LeanLab.PerelliPintz1992.Decomp1519.sing_tail
  refine ⟨2 * (C + 1), by positivity, 1, ?_⟩
  intro N hN n hn hnN hev
  obtain ⟨k, hk⟩ := hev
  have hnEq : n = 2 * k := by omega
  rw [hnEq] at hn hnN ⊢
  have hk1 : 1 ≤ k := by omega
  let Q := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
  have hQ : 1 ≤ Q := Nat.floor_pos.mpr
    (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  let F : ℂ := ∑ q ∈ Finset.Icc 1 Q,
    (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q (2 * k)
  have hb := ht k hk1 Q hQ
  have hc := singular_cutoff_conj376 k Q
  change (starRingEnd ℂ) F = _ at hc
  have hre : (((LeanLab.PerelliPintz1992.S2k k : ℝ) : ℂ) -
      ∑ q ∈ Finset.Icc 1 Q,
        ((LeanLab.PerelliPintz1992.Decomp1519.muφ q ^ 2 : ℝ) : ℂ) *
          LeanLab.PerelliPintz1992.Decomp1519.ram q (-(2 * k : ℤ))).re =
      LeanLab.PerelliPintz1992.S2k k - F.re := by
    rw [← hc]
    simp
  rw [abs_sub_comm, singular_eq_perelli_pintz376 k hk1]
  change |LeanLab.PerelliPintz1992.S2k k - F.re| ≤ _
  calc
    _ ≤ ‖((LeanLab.PerelliPintz1992.S2k k : ℝ) : ℂ) -
        ∑ q ∈ Finset.Icc 1 Q,
          ((LeanLab.PerelliPintz1992.Decomp1519.muφ q ^ 2 : ℝ) : ℂ) *
            LeanLab.PerelliPintz1992.Decomp1519.ram q (-(2 * k : ℤ))‖ := by
      rw [← hre]
      exact Complex.abs_re_le_norm _
    _ ≤ C / Real.sqrt Q * ((2 * k).divisors.card : ℝ) := hb
    _ ≤ (C + 1) * (1 / Real.sqrt Q) * ((2 * k).divisors.card : ℝ) := by
      rw [mul_one_div]
      gcongr
      linarith
    _ ≤ (C + 1) * (2 * (N : ℝ) ^ (-(1 / 20 : ℝ))) * ((2 * k).divisors.card : ℝ) := by
      gcongr
      exact inverse_sqrt_floor376 N (by omega)
    _ = _ := by ring

end LeanLab.Linnik1951
