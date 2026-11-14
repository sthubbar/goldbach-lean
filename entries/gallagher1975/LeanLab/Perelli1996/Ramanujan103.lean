module

public import LeanLab.Perelli1996.Parseval103

/-!
P0083 Perelli 1996, page 481, the Ramanujan sum preceding equation 3.
The prime modulus case is elementary from finite geometric sums.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Ramanujan103
open Finset Real Polynomial
noncomputable section

/-- The Ramanujan sum over reduced natural residue representatives. -/
def ramanujanSum (q m : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), Kernel.e ((m : ℝ) * a / q)

/-- A rational exponential equals one exactly when its denominator divides its numerator. -/
theorem e_div_eq_one_iff (m q : ℕ) (hq : q ≠ 0) :
    Kernel.e ((m : ℝ) / q) = 1 ↔ q ∣ m := by
  unfold Kernel.e
  have heq : Complex.I * ((2 * Real.pi * ((m : ℝ) / q) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * (m : ℂ) / q := by
    push_cast
    ring
  rw [heq]
  exact Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq

/-- Integer phases give the value one. -/
theorem e_nat (m : ℕ) : Kernel.e (m : ℝ) = 1 := by
  simpa using (e_div_eq_one_iff m 1 (by norm_num)).mpr (one_dvd m)

/-- Multiples of a rational phase are powers of its exponential. -/
theorem e_div_mul (m q a : ℕ) :
    Kernel.e ((m : ℝ) * a / q) = Kernel.e ((m : ℝ) / q) ^ a := by
  unfold Kernel.e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Complete residue exponential sums are zero off the divisibility condition. -/
theorem complete_sum (m q : ℕ) (hq : 0 < q) :
    (∑ a ∈ range q, Kernel.e ((m : ℝ) * a / q)) = if q ∣ m then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpower : Kernel.e ((m : ℝ) / q) ^ q = 1 := by
    rw [← e_div_mul]
    have heq : (m : ℝ) * q / q = m := by field_simp
    rw [heq, e_nat]
  simp_rw [e_div_mul]
  by_cases hdiv : q ∣ m
  · rw [if_pos hdiv, (e_div_eq_one_iff m q hq.ne').mpr hdiv]
    simp
  · rw [if_neg hdiv]
    have hz : Kernel.e ((m : ℝ) / q) - 1 ≠ 0 :=
      sub_ne_zero.mpr (mt (e_div_eq_one_iff m q hq.ne').mp hdiv)
    have hmul := geom_sum_mul (Kernel.e ((m : ℝ) / q)) q
    rw [hpower, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right hz

/-- At a prime modulus, Ramanujan sums equal p minus one or negative one. -/
theorem ramanujanSum_prime (p m : ℕ) (hp : p.Prime) :
    ramanujanSum p m = if p ∣ m then (p : ℂ) - 1 else -1 := by
  classical
  have hfilter : (range p).filter (fun a => Nat.Coprime a p) = (range p).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨ha, hcop⟩
      have ha0 : a ≠ 0 := by
        intro hz
        have := hcop
        simp [hz, hp.ne_one] at this
      exact ⟨ha0, ha⟩
    · rintro ⟨ha0, ha⟩
      exact ⟨ha, (Nat.coprime_of_lt_prime ha0 ha hp).symm⟩
  unfold ramanujanSum
  rw [hfilter, Finset.sum_erase_eq_sub (Finset.mem_range.mpr hp.pos), complete_sum m p hp.pos]
  simp [Kernel.e]
  split_ifs <;> ring

/-- The prime Ramanujan sum is the printed totient and Mobius formula. -/
theorem ramanujanSum_prime_formula (p m : ℕ) (hp : p.Prime) :
    ramanujanSum p m = ((p.totient : ℝ) *
      (ArithmeticFunction.moebius (p / Nat.gcd p m) : ℝ) /
        (p / Nat.gcd p m).totient : ℂ) := by
  rw [ramanujanSum_prime p m hp]
  by_cases hdiv : p ∣ m
  · have hg : Nat.gcd p m = p := Nat.gcd_eq_left_iff_dvd.mpr hdiv
    have ht : (p.totient : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
      norm_num
    simp [hdiv, hg, Nat.div_self hp.pos, ht]
  · have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hdiv
    have hg : Nat.gcd p m = 1 := hcop.gcd_eq_one
    simp [hdiv, hg, ArithmeticFunction.moebius_apply_prime hp]
    have hφ : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr hp.pos
    have hφC : (p.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    field_simp [hφC]
/-- At a prime power the reduced sum is the difference of two complete residue sums. -/
theorem ramanujanSum_prime_pow (p e m : ℕ) (hp : p.Prime) :
    ramanujanSum (p ^ (e + 1)) m =
      (if p ^ (e + 1) ∣ m then (p ^ (e + 1) : ℕ) else 0) -
      (if p ^ e ∣ m then (p ^ e : ℕ) else 0 : ℂ) := by
  classical
  let q := p ^ (e + 1)
  have hq : 0 < q := pow_pos hp.pos _
  have hpe : 0 < p ^ e := pow_pos hp.pos _
  have hqeq : q = p * p ^ e := by dsimp [q]; rw [pow_succ']
  have hfilter : (range q).filter (fun a => p ∣ a) = (range (p ^ e)).image (fun b => p * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      exact ⟨b, (Nat.mul_lt_mul_left hp.pos).mp (by simpa [hqeq] using ha), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by rw [hqeq]; exact (Nat.mul_lt_mul_left hp.pos).mpr hb, ⟨b, rfl⟩⟩
  have hbad : (∑ a ∈ (range q).filter (fun a => p ∣ a), Kernel.e ((m : ℝ) * a / q)) =
      ∑ b ∈ range (p ^ e), Kernel.e ((m : ℝ) * b / (p ^ e : ℕ)) := by
    rw [hfilter, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      congr 1
      rw [hqeq]
      push_cast
      field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
      <;> ring
    · intro b hb c hc heq
      exact Nat.eq_of_mul_eq_mul_left hp.pos heq
  have hgood : ramanujanSum q m =
      ∑ a ∈ (range q).filter (fun a => ¬p ∣ a), Kernel.e ((m : ℝ) * a / q) := by
    unfold ramanujanSum
    have hpred : ∀ a, Nat.Coprime a q ↔ ¬p ∣ a := by
      intro a
      rw [show q = p ^ (e + 1) from rfl, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
        hp.coprime_iff_not_dvd]
    simp_rw [hpred]
  have hpart := Finset.sum_filter_add_sum_filter_not (range q) (fun a => p ∣ a)
    (fun a => Kernel.e ((m : ℝ) * a / q))
  rw [hbad, ← hgood, complete_sum m (p ^ e) hpe, complete_sum m q hq] at hpart
  dsimp [q] at *
  push_cast
  push_cast at hpart
  linear_combination hpart

/-- Mobius inversion gives the coprimality indicator at every positive modulus. -/
theorem coprime_indicator (q a : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime a q then 1 else 0 := by
  classical
  have hset : q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd a q ≠ 0 := Nat.gcd_ne_zero_right hq.ne'
    simp [hg, hq.ne', and_comm, and_left_comm, and_assoc]
  rw [← Finset.sum_filter, hset]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd a q))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.coprime_iff_gcd_eq_one] using h

/-- The complete sum over multiples of a divisor reduces to the quotient modulus. -/
theorem multiples_sum (q d m : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    (∑ a ∈ (range q).filter (fun a => d ∣ a), Kernel.e ((m : ℝ) * a / q)) =
      if q / d ∣ m then ((q / d : ℕ) : ℂ) else 0 := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hq
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hd0
  have hqeq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
  have hfilter : (range q).filter (fun a => d ∣ a) = (range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      rw [hqeq] at ha
      exact ⟨b, (Nat.mul_lt_mul_left hd0).mp ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by rw [hqeq]; exact (Nat.mul_lt_mul_left hd0).mpr hb, ⟨b, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · have heq (b : ℕ) : Kernel.e ((m : ℝ) * ((d * b : ℕ) : ℝ) / q) =
        Kernel.e ((m : ℝ) * b / ((q / d : ℕ) : ℝ)) := by
      congr 1
      conv_lhs => rw [hqeq]
      push_cast
      field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd0.ne',
        show (((q / d : ℕ) : ℝ)) ≠ 0 by exact_mod_cast hqd.ne']
    simp_rw [heq]
    exact complete_sum m (q / d) hqd
  · intro b hb c hc heq
    exact Nat.eq_of_mul_eq_mul_left hd0 heq

/-- The general Ramanujan sum has its exact Mobius divisor expansion. -/
theorem ramanujanSum_divisor_expansion (q m : ℕ) (hq : 0 < q) :
    ramanujanSum q m = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if q / d ∣ m then ((q / d : ℕ) : ℂ) else 0) := by
  classical
  have heq (a : ℕ) :
      (if Nat.Coprime a q then Kernel.e ((m : ℝ) * a / q) else 0) =
        (∑ d ∈ q.divisors, if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
          Kernel.e ((m : ℝ) * a / q) := by
    rw [coprime_indicator q a hq]
    split_ifs <;> simp
  unfold ramanujanSum
  rw [Finset.sum_filter]
  simp_rw [heq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdis (a : ℕ) : (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
        Kernel.e ((m : ℝ) * a / q) =
      (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ a then Kernel.e ((m : ℝ) * a / q) else 0) := by split_ifs <;> simp
  simp_rw [hdis]
  rw [← Finset.mul_sum, ← Finset.sum_filter,
    multiples_sum q d m hq (Nat.dvd_of_mem_divisors hd)]

/-- At a coprime argument the general Ramanujan sum equals Mobius of the modulus. -/
theorem ramanujanSum_coprime (q m : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q m) :
    ramanujanSum q m = (ArithmeticFunction.moebius q : ℂ) := by
  rw [ramanujanSum_divisor_expansion q m hq]
  rw [Finset.sum_eq_single q]
  · simp [Nat.div_self hq]
  · intro d hd hdne
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hnot : ¬q / d ∣ m := by
      intro hdm
      have hquot : q / d = 1 := Nat.eq_one_of_dvd_coprimes hcop
        (Nat.div_dvd_of_dvd hdq) hdm
      have heq := Nat.mul_div_cancel' hdq
      rw [hquot, mul_one] at heq
      exact hdne heq
    simp [hnot]
  · intro hnot
    exact (hnot (Nat.mem_divisors_self q hq.ne')).elim

/-- When the modulus divides the argument, the Ramanujan sum is its totient. -/
theorem ramanujanSum_dvd (q m : ℕ) (hq : 0 < q) (hdiv : q ∣ m) :
    ramanujanSum q m = (q.totient : ℂ) := by
  classical
  obtain ⟨k, rfl⟩ := hdiv
  have heq (a : ℕ) : Kernel.e ((((q * k : ℕ) : ℝ) * a) / q) = 1 := by
    have harg : (((q * k : ℕ) : ℝ) * a) / q = ((k * a : ℕ) : ℝ) := by
      push_cast
      field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne']
    rw [harg, e_nat]
  unfold ramanujanSum
  simp_rw [heq]
  have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp [Nat.coprime_comm]
  simp [hcard]

/-- Ramanujan sums multiply across coprime positive moduli. -/
theorem ramanujanSum_mul (q r m : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hcop : Nat.Coprime q r) :
    ramanujanSum (q * r) m = ramanujanSum q m * ramanujanSum r m := by
  let g : ArithmeticFunction ℂ := ⟨fun n => if n ∣ m then (n : ℂ) else 0, by simp⟩
  have hg : g.IsMultiplicative := by
    refine ⟨by simp [g], ?_⟩
    intro a b hab
    have hdiv : a * b ∣ m ↔ a ∣ m ∧ b ∣ m := by
      constructor
      · intro h
        exact ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩
      · intro h
        exact hab.mul_dvd_of_dvd_of_dvd h.1 h.2
    change (if a * b ∣ m then ((a * b : ℕ) : ℂ) else 0) =
      (if a ∣ m then (a : ℂ) else 0) * (if b ∣ m then (b : ℂ) else 0)
    simp only [hdiv]
    by_cases ha : a ∣ m <;> by_cases hb : b ∣ m <;> simp [ha, hb, Nat.cast_mul]
  have hf : (ArithmeticFunction.moebius : ArithmeticFunction ℂ).IsMultiplicative := by
    refine ⟨by simp, ?_⟩
    intro a b hab
    change (ArithmeticFunction.moebius (a * b) : ℂ) =
      (ArithmeticFunction.moebius a : ℂ) * (ArithmeticFunction.moebius b : ℂ)
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab, Int.cast_mul]
  have heval (n : ℕ) (hn : 0 < n) : ramanujanSum n m =
      ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) * g) n := by
    rw [ramanujanSum_divisor_expansion n m hn, ArithmeticFunction.mul_apply]
    simpa [g] using (Nat.sum_divisorsAntidiagonal (n := n)
      (fun a b => (ArithmeticFunction.moebius a : ℂ) * g b)).symm
  rw [heval (q * r) (Nat.mul_pos hq hr), heval q hq, heval r hr]
  exact (hf.mul hg).map_mul_of_coprime hcop


end
end LeanLab.Perelli1996.Ramanujan103
