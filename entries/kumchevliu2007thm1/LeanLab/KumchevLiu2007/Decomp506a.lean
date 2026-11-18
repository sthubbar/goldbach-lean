module

public import LeanLab.KumchevLiu2007.Decomp129a
public import LeanLab.KumchevLiu2007.Decomp1534b

/-!
Upstream copy of the clean Task506aTask342e proof chain for page 14 display 49.
Only helpers used by that proof are copied. No Decomp129 dependency is imported.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task506aTask129

open Real Complex
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask129.series2. -/
noncomputable def series2 (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q


end LeanLab.KumchevLiu2007.Task506aTask129

namespace LeanLab.KumchevLiu2007.Task506aTask129b

open Real Complex LeanLab.KumchevLiu2007 Task506aTask129
open U1534
open scoped BigOperators
attribute [local instance] Classical.propDecidable

                                                               

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask129b.intervalNumbers. -/
noncomputable def intervalNumbers (x y : ℝ) : Finset ℕ := Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.product2. -/
noncomputable def product2 (n : ℕ) (Q : ℝ) : ℂ :=
  ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.smoothWeight. -/
noncomputable def smoothWeight (q : ℕ) (Q : ℝ) : ℝ :=
  if ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q then 1 else 0


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.tail2. -/
noncomputable def tail2 (n : ℕ) (P Q0 Q : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊, -(smoothWeight q Q : ℂ) * U1534.A2 n q


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.mean_square_add. -/
theorem mean_square_add {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    (∑ n ∈ s, ‖f n + g n‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖f n‖ ^ 2) + 2 * (∑ n ∈ s, ‖g n‖ ^ 2) := by
  calc _ ≤ ∑ n ∈ s, (2 * ‖f n‖ ^ 2 + 2 * ‖g n‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        have hsq : ‖f n + g n‖ ^ 2 ≤ (‖f n‖ + ‖g n‖) ^ 2 := by
          gcongr
          exact norm_add_le _ _
        nlinarith [sq_nonneg (‖f n‖ - ‖g n‖)]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_eq_zero_of_not_squarefree. -/
theorem A2_eq_zero_of_not_squarefree (n q : ℕ) (hq : ¬ Squarefree q) : U1534.A2 n q = 0 := by
  simp [U1534.A2, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_periodic. -/
theorem A2_periodic (q : ℕ) : Function.Periodic (fun n : ℕ => U1534.A2 n q) q := by
  intro n
  by_cases hq : q = 0
  · subst q
    rfl
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold U1534.A2
  refine congrArg (fun z : ℂ => ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)^2 * z) ?_
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun z : ℂ => U1534.gaussS q a * z)
  unfold U1534.ee
  have heq : 2 * (Real.pi : ℂ) * I * ↑(-((a * (n + q) : ℕ) : ℝ) / q) =
      2 * (Real.pi : ℂ) * I * ↑(-((a * n : ℕ) : ℝ) / q) +
      ((-(a : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    field_simp
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_orthogonal. -/
theorem A2_orthogonal (q r : ℕ) (hqr : q ≠ r) :
    ∑ n ∈ Finset.range (q * r), U1534.A2 n q * U1534.A2 n r = 0 := by
  by_cases hq : q = 0
  · subst q; simp
  by_cases hr : r = 0
  · subst r; simp
  have hN : q * r ≠ 0 := Nat.mul_ne_zero hq hr
  have : NeZero (q * r) := ⟨hN⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have sum_range (f : ZMod (q * r) → ℂ) :
      ∑ n ∈ Finset.range (q * r), f (n : ZMod (q * r)) = ∑ n : ZMod (q * r), f n := by
    apply Finset.sum_bij (s := Finset.range (q*r))
      (t := (Finset.univ : Finset (ZMod (q*r)))) (fun a _ => (a : ZMod (q*r)))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have cross (a b : ℕ) (ha : a.Coprime q) (hb : b.Coprime r) :
      ∑ n ∈ Finset.range (q*r), ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r) = 0 := by
    have hfreq : (-((a*r+b*q : ℕ) : ZMod (q*r))) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff (a*r+b*q) (q*r)).mp (neg_eq_zero.mp h)
      have hqd : q ∣ a*r+b*q := dvd_trans (dvd_mul_right q r) hd
      have hrd : r ∣ a*r+b*q := dvd_trans (dvd_mul_left r q) hd
      have hqd' : q ∣ a*r := (Nat.dvd_add_iff_left (dvd_mul_left q b)).mpr hqd
      have hrd' : r ∣ b*q := (Nat.dvd_add_iff_right (dvd_mul_left r a)).mpr hrd
      exact hqr (Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hqd')
        (hb.symm.dvd_of_dvd_mul_left hrd'))
    have heq (n : ℕ) : ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r) =
        ZMod.stdAddChar ((n : ZMod (q*r)) * (-((a*r+b*q : ℕ) : ZMod (q*r)))) := by
      have hcast : (n : ZMod (q*r)) * (-((a*r+b*q : ℕ) : ZMod (q*r))) =
          (((-((n*(a*r+b*q) : ℕ) : ℤ)) : ℤ) : ZMod (q*r)) := by push_cast; ring
      rw [hcast, ZMod.stdAddChar_coe]
      unfold ee
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    simp_rw [heq]
    rw [sum_range (fun n => ZMod.stdAddChar (n * (-((a*r+b*q : ℕ) : ZMod (q*r)))))]
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q*r))
      (-((a*r+b*q : ℕ) : ZMod (q*r))) (ZMod.isPrimitive_stdAddChar (q*r))
    simpa only [ite_eq_right hfreq, Nat.cast_zero] using hs
  unfold A2
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hca := (Finset.mem_filter.mp ha).2
  have hcb := (Finset.mem_filter.mp hb).2
  have hs := cross a b hca hcb
  have heq (n : ℕ) :
      (((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)^2 *
        (gaussS q a * ee (-((a*n : ℕ) : ℝ)/q))) *
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) / (Nat.totient r : ℂ)^2 *
        (gaussS r b * ee (-((b*n : ℕ) : ℝ)/r))) =
      ((((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)^2 * gaussS q a) *
        (((ArithmeticFunction.moebius r : ℤ) : ℂ) / (Nat.totient r : ℂ)^2 * gaussS r b)) *
        (ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r)) := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum, hs, mul_zero]


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.periodic_zero_mean_interval. -/
theorem periodic_zero_mean_interval (f : ℕ → ℂ) {T : ℕ} (hT : 0 < T)
    (hf : Function.Periodic f T) (hs : ∑ i ∈ Finset.range T, f i = 0) (a b : ℕ) :
    ‖∑ i ∈ Finset.Ico a b, f i‖ ≤ 2 * ∑ i ∈ Finset.range T, ‖f i‖ := by
  have hp : Function.Periodic (fun N => ∑ i ∈ Finset.range N, f i) T := by
    intro N
    change (∑ i ∈ Finset.range (N + T), f i) = ∑ i ∈ Finset.range N, f i
    induction N with
    | zero => simpa using hs
    | succ N ih =>
      rw [show N + 1 + T = (N + T) + 1 by omega, Finset.sum_range_succ, hf N, ih,
        Finset.sum_range_succ]
  have hprefix (N : ℕ) : ‖∑ i ∈ Finset.range N, f i‖ ≤ ∑ i ∈ Finset.range T, ‖f i‖ := by
    rw [← hp.map_mod_nat N]
    calc _ ≤ ∑ i ∈ Finset.range (N % T), ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range T, ‖f i‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.mod_lt N hT).le
        · intro i hi hi'; exact norm_nonneg _
  by_cases hab : a ≤ b
  · rw [Finset.sum_Ico_eq_sub _ hab]
    calc _ ≤ ‖∑ i ∈ Finset.range b, f i‖ + ‖∑ i ∈ Finset.range a, f i‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hprefix a, hprefix b]
  · have hempty : Finset.Ico a b = ∅ := Finset.Ico_eq_empty_of_le (by omega : b ≤ a)
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_interval_bound. -/
theorem A2_interval_bound {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, A2 n q * A2 n r‖ ≤
      2 * ∑ n ∈ Finset.range (q * r), ‖A2 n q * A2 n r‖ := by
  have hq' : Function.Periodic (fun n => A2 n q) (q * r) := by
    simpa [Nat.mul_comm] using (A2_periodic q).nat_mul r
  have hr' : Function.Periodic (fun n => A2 n r) (q * r) := by
    simpa using (A2_periodic r).nat_mul q
  exact periodic_zero_mean_interval _ (Nat.mul_pos hq hr) (hq'.mul hr')
    (A2_orthogonal q r hqr) a b


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_prime_root_count. -/
theorem A2_prime_root_count (p : ℕ) [Fact p.Prime] (n : ℕ) :
    A2 n p = ((p : ℂ) - 1 - (p : ℂ) *
      (((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card : ℂ)) /
      ((p : ℂ) - 1) ^ 2 := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have std_int (a : ℤ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    rw [ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    simpa using std_int (a : ℤ)
  have sum_range (f : ZMod p → ℂ) :
      ∑ a ∈ Finset.range p, f (a : ZMod p) = ∑ a : ZMod p, f a := by
    apply Finset.sum_bij (s := Finset.range p) (t := (Finset.univ : Finset (ZMod p))) (fun a _ => (a : ZMod p))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have coprime_iff (a : ℕ) : Nat.Coprime a p ↔ (a : ZMod p) ≠ 0 := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, ne_eq, ZMod.natCast_eq_zero_iff]
  have filtered (f : ZMod p → ℂ) :
      ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p), f (a : ZMod p) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod p)), f a := by
    rw [Finset.sum_filter]
    simp_rw [coprime_iff]
    rw [sum_range (fun a => if a ≠ 0 then f a else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  have std_neg (a : ℕ) : ee (-((a * n : ℕ) : ℝ) / p) =
      ZMod.stdAddChar (-((a : ZMod p) * (n : ZMod p))) := by
    have heq : -((a * n : ℕ) : ℝ) / p = ((-((a * n : ℕ) : ℤ) : ℤ) : ℝ) / p := by
      push_cast; ring
    rw [heq, std_int]
    push_cast
    rfl
  have gauss_eq (a : ℕ) : gaussS p a * ee (-((a*n : ℕ) : ℝ)/p) =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p),
        ZMod.stdAddChar ((a : ZMod p) * (x ^ 2 - (n : ZMod p))) := by
    rw [std_neg]
    unfold gaussS
    simp_rw [std_nat, Nat.cast_mul, Nat.cast_pow]
    rw [filtered (fun x => ZMod.stdAddChar ((a : ZMod p) * x ^ 2)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hchar (t : ZMod p) :
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * t) =
        if t = 0 then (p : ℂ) - 1 else -1 := by
    have ht := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) t
      (ZMod.isPrimitive_stdAddChar p)
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a : ZMod p => ZMod.stdAddChar (a * t)) (Finset.mem_univ 0)
    simp only [zero_mul, AddChar.map_zero_eq_one] at hs
    rw [ht, ZMod.card] at hs
    by_cases ht0 : t = 0
    · simp only [ht0, ite_true] at hs ⊢
      linear_combination hs
    · simp only [ht0, ite_false, Nat.cast_zero] at hs ⊢
      linear_combination hs
  let s := Finset.univ.erase (0 : ZMod p)
  let R := s.filter (fun x => x ^ 2 = (n : ZMod p))
  have hg : ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
      gaussS p a * ee (-((a*n : ℕ) : ℝ)/p) =
      (p : ℂ) * (R.card : ℂ) - ((p : ℂ) - 1) := by
    simp_rw [gauss_eq]
    rw [filtered (fun a => ∑ x ∈ Finset.univ.erase (0 : ZMod p),
      ZMod.stdAddChar (a * (x ^ 2 - (n : ZMod p)))), Finset.sum_comm]
    simp_rw [hchar, sub_eq_zero]
    have heq (x : ZMod p) : (if x ^ 2 = (n : ZMod p) then (p : ℂ) - 1 else -1) =
        (p : ℂ) * (if x ^ 2 = (n : ZMod p) then 1 else 0) - 1 := by
      split_ifs <;> ring
    simp_rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hR : (∑ x ∈ s, if x ^ 2 = (n : ZMod p) then (1 : ℂ) else 0) = R.card := by
      simp [R]
    change (p : ℂ) * (∑ x ∈ s, if x ^ 2 = (n : ZMod p) then (1 : ℂ) else 0) -
      (∑ x ∈ s, (1 : ℂ)) = _
    rw [hR]
    simp [s, ZMod.card, Nat.cast_sub hp.one_le]
  unfold A2
  rw [hg, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  norm_num only [Int.cast_neg, Int.cast_one, Nat.cast_sub hp.one_le, Nat.cast_one]
  change -1 / ((p : ℂ) - 1)^2 * ((p : ℂ) * (R.card : ℂ) - ((p : ℂ) - 1)) =
    ((p : ℂ) - 1 - (p : ℂ) * (R.card : ℂ)) / ((p : ℂ) - 1)^2
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.nonzero_square_roots_le_two. -/
theorem nonzero_square_roots_le_two (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card ≤ 2 := by
  let f : Polynomial (ZMod p) := Polynomial.X ^ 2 - Polynomial.C (n : ZMod p)
  have hf : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) _
  have hsub : ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).val ⊆ f.roots := by
    intro x hx
    apply (Polynomial.mem_roots hf).mpr
    have heq := (Finset.mem_filter.mp hx).2
    simpa [f] using sub_eq_zero.mpr heq
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  simpa only [f, Polynomial.natDegree_X_pow_sub_C] using hc


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_prime_norm_bound. -/
theorem A2_prime_norm_bound (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖A2 n p‖ ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1)^2 := by
  let R := (Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))
  have hp : p.Prime := Fact.out
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hR : (R.card : ℝ) ≤ 2 := by exact_mod_cast nonzero_square_roots_le_two p n
  have heq : A2 n p =
      ((((p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)) / ((p : ℝ) - 1)^2 : ℝ) : ℂ) := by
    rw [A2_prime_root_count]
    push_cast
    rfl
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  have hm : (p : ℝ) * (R.card : ℝ) ≤ (p : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  have hn : 0 ≤ (p : ℝ) * (R.card : ℝ) := by positivity
  have habs : |(p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)| ≤ (p : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right habs hd.le


/-- Page 13 through page 15, copied proof helper from Task506aTask129b.A2_prime_norm_le_inv_add. -/
theorem A2_prime_norm_le_inv_add (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖A2 n p‖ ≤ 1 / (p : ℝ) + 6 / (p : ℝ)^2 := by
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst p
    by_cases hn : n % 2 = 0
    · rw [A2_two_even hn]; norm_num
    · rw [A2_two_odd (by omega)]; norm_num
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  apply (A2_prime_norm_bound p n).trans
  have heq : 1 / (p : ℝ) + 6 / (p : ℝ)^2 = ((p : ℝ) + 6) / (p : ℝ)^2 := by
    field_simp
  rw [heq, div_le_div_iff₀ hd (by positivity : 0 < (p : ℝ)^2)]
  have hh : 0 ≤ ((p : ℝ) - 3) * (3 * (p : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith


end LeanLab.KumchevLiu2007.Task506aTask129b

namespace LeanLab.KumchevLiu2007.Task506aTask271a

open Real Complex Task506aTask129 Task506aTask129b
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000

                                                 


set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_add_real. -/
private lemma ee_add_real (x y : ℝ) : U1534.ee (x + y) = U1534.ee x * U1534.ee y := by
  unfold U1534.ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_int_add. -/
private lemma ee_int_add (u : ℝ) (k : ℤ) : U1534.ee (u + (k : ℝ)) = U1534.ee u := by
  unfold U1534.ee
  have h : ((2 : ℂ) * (π : ℂ) * I) * ((u + (k : ℝ) : ℝ) : ℂ)
      = ((2 : ℂ) * (π : ℂ) * I) * (u : ℂ) + (k : ℂ) * ((2 : ℂ) * (π : ℂ) * I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.crt_coprime. -/
private lemma crt_coprime {q r a1 a2 : ℕ} (hqr : q.Coprime r)
    (h1 : a1.Coprime q) (h2 : a2.Coprime r) : (a1 * r + a2 * q).Coprime (q * r) := by
  have hq' : q.Coprime (a1 * r) := Nat.Coprime.mul_right h1.symm hqr
  have hr' : r.Coprime (a2 * q) := Nat.Coprime.mul_right h2.symm hqr.symm
  have hqc : (a1 * r + a2 * q).Coprime q := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_add_mul_right_right q (a1 * r) a2).mpr hq'
  have hrc : (a1 * r + a2 * q).Coprime r := by
    rw [Nat.coprime_comm]
    rw [show a1 * r + a2 * q = a2 * q + a1 * r from by ring]
    exact (Nat.coprime_add_mul_right_right r (a2 * q) a1).mpr hr'
  exact Nat.Coprime.mul_right hqc hrc


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.coprime_of_mod. -/
private lemma coprime_of_mod {x n : ℕ} (h : x.Coprime n) : (x % n).Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one] at *
  rw [← Nat.gcd_rec n x, Nat.gcd_comm n x]
  exact h


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.crt_image_mem. -/
private lemma crt_image_mem {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r)
    {p : ℕ × ℕ}
    (hp : p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)) :
    (p.1 * r + p.2 * q) % (q * r) ∈
      (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)) := by
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨-, h1⟩ := Finset.mem_filter.mp hp1
  obtain ⟨-, h2⟩ := Finset.mem_filter.mp hp2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hq hr)),
      coprime_of_mod (crt_coprime hqr h1 h2)⟩


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.crt_injOn. -/
private lemma crt_injOn {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1 * r + p.2 * q) % (q * r))
      ↑((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)) := by
  intro p hp p' hp' hpp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
  obtain ⟨hp1', hp2'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp')
  have hb1 : p.1 < q := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
  have hb2 : p.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp hp2).1
  have hb1' : p'.1 < q := Finset.mem_range.mp (Finset.mem_filter.mp hp1').1
  have hb2' : p'.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp hp2').1
  have hmod : p.1 * r + p.2 * q ≡ p'.1 * r + p'.2 * q [MOD q * r] := hpp
  have hq' : p.1 * r + p.2 * q ≡ p'.1 * r + p'.2 * q [MOD q] :=
    hmod.of_dvd (Nat.dvd_mul_right q r)
  have hr' : p.1 * r + p.2 * q ≡ p'.1 * r + p'.2 * q [MOD r] :=
    hmod.of_dvd (Nat.dvd_mul_left r q)
  have e1 : (p.1 * r + p.2 * q) % q = (p.1 * r) % q := by
    rw [show p.1 * r + p.2 * q = p.1 * r + q * p.2 from by ring,
      Nat.add_mul_mod_self_left]
  have e2 : (p'.1 * r + p'.2 * q) % q = (p'.1 * r) % q := by
    rw [show p'.1 * r + p'.2 * q = p'.1 * r + q * p'.2 from by ring,
      Nat.add_mul_mod_self_left]
  have e3 : (p.1 * r + p.2 * q) % r = (p.2 * q) % r := by
    rw [show p.1 * r + p.2 * q = p.2 * q + r * p.1 from by ring,
      Nat.add_mul_mod_self_left]
  have e4 : (p'.1 * r + p'.2 * q) % r = (p'.2 * q) % r := by
    rw [show p'.1 * r + p'.2 * q = p'.2 * q + r * p'.1 from by ring,
      Nat.add_mul_mod_self_left]
  have ha1 : p.1 ≡ p'.1 [MOD q] := by
    refine Nat.ModEq.cancel_right_of_coprime hqr ?_
    have hq2 : (p.1 * r) % q = (p'.1 * r) % q := by
      rw [← e1, ← e2]
      exact hq'
    exact hq2
  have ha2 : p.2 ≡ p'.2 [MOD r] := by
    refine Nat.ModEq.cancel_right_of_coprime hqr.symm ?_
    have hr2 : (p.2 * q) % r = (p'.2 * q) % r := by
      rw [← e3, ← e4]
      exact hr'
    exact hr2
  have h1 : p.1 = p'.1 := by
    have h : p.1 % q = p'.1 % q := ha1
    rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb1'] at h
    exact h
  have h2 : p.2 = p'.2 := by
    have h : p.2 % r = p'.2 % r := ha2
    rw [Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb2'] at h
    exact h
  exact Prod.ext h1 h2


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.card_filter_coprime. -/
private lemma card_filter_coprime (n : ℕ) :
    ((Finset.range n).filter (fun a => Nat.Coprime a n)).card = n.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, Nat.coprime_comm.mp h.2⟩, fun h => ⟨h.1, Nat.coprime_comm.mpr h.2⟩⟩


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.crt_residue_bij. -/
private lemma crt_residue_bij {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)).image
      (fun p : ℕ × ℕ => (p.1 * r + p.2 * q) % (q * r))
      = (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)) := by
  have hsub : ((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)).image
      (fun p : ℕ × ℕ => (p.1 * r + p.2 * q) % (q * r)) ⊆
      (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact crt_image_mem hq hr hqr hp
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hinj := crt_injOn hq hr hqr
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_filter_coprime,
    card_filter_coprime, card_filter_coprime, Nat.totient_mul hqr]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sum_units_mul. -/
private lemma sum_units_mul {q m : ℕ} (hq : 0 < q) (hm : q.Coprime m) (F : ℕ → ℂ) :
    (∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F ((b * m) % q))
      = ∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F b := by
  classical
  set U := (Finset.range q).filter (fun a => Nat.Coprime a q) with hU
  have hmaps : ∀ b ∈ U, (b * m) % q ∈ U := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩
    have : (b * m).Coprime q := Nat.Coprime.mul_left hb2 hm.symm
    exact coprime_of_mod this
  have hinj : Set.InjOn (fun b => (b * m) % q) ↑U := by
    intro b hb b' hb' hbb'
    obtain ⟨hb1, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    obtain ⟨hb1', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb')
    have hb1 : b < q := Finset.mem_range.mp hb1
    have hb1' : b' < q := Finset.mem_range.mp hb1'
    have hme : b * m ≡ b' * m [MOD q] := hbb'
    have h1 : b ≡ b' [MOD q] := Nat.ModEq.cancel_right_of_coprime hm hme
    have h2 : b % q = b' % q := h1
    rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb1'] at h2
    exact h2
  have hcard : (U.image (fun b => (b * m) % q)).card = U.card := Finset.card_image_of_injOn hinj
  have hsub : U.image (fun b => (b * m) % q) ⊆ U := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact hmaps b hb
  have heq : U.image (fun b => (b * m) % q) = U := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard]
  conv_rhs => rw [← heq]
  rw [Finset.sum_image hinj]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sum_residue_reindex. -/
private lemma sum_residue_reindex {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r)
    (G : ℕ → ℂ) (hper : ∀ a b : ℕ, a ≡ b [MOD q * r] → G a = G b) :
    (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)), G a)
      = ∑ p ∈ ((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
          (Finset.range r).filter (fun a => Nat.Coprime a r)), G (p.1 * r + p.2 * q) := by
  rw [← crt_residue_bij hq hr hqr, Finset.sum_image (crt_injOn hq hr hqr)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine hper _ _ ?_
  show ((p.1 * r + p.2 * q) % (q * r)) % (q * r) = (p.1 * r + p.2 * q) % (q * r)
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.mul_pos hq hr))]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_nat_period. -/
private lemma ee_nat_period (M : ℕ) (hM : 0 < M) {a b : ℕ} (hab : a ≡ b [MOD M]) (u : ℕ) :
    U1534.ee (((a * u : ℕ) : ℝ) / (M : ℝ))
      = U1534.ee (((b * u : ℕ) : ℝ) / (M : ℝ)) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hab
  -- `hk : (b : ℤ) - (a : ℤ) = (M : ℤ) * k`
  have hz : ((b * u : ℕ) : ℤ) = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by
    have h1 : (b : ℤ) = (a : ℤ) + (M : ℤ) * k := by
      rw [← hk]; ring
    calc ((b * u : ℕ) : ℤ) = (b : ℤ) * (u : ℤ) := by push_cast; ring
      _ = ((a : ℤ) + (M : ℤ) * k) * (u : ℤ) := by rw [h1]
      _ = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by push_cast; ring
  have hb : ((b * u : ℕ) : ℝ) = ((a * u : ℕ) : ℝ) + (M : ℝ) * ((k * (u : ℤ) : ℤ) : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at h3 ⊢
    linarith
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hkey : ((b * u : ℕ) : ℝ) / (M : ℝ)
      = ((a * u : ℕ) : ℝ) / (M : ℝ) + ((k * (u : ℤ) : ℤ) : ℝ) := by
    rw [hb]
    field_simp
    try ring
  rw [hkey, ee_int_add]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_nat_period_neg. -/
private lemma ee_nat_period_neg (M : ℕ) (hM : 0 < M) {a b : ℕ} (hab : a ≡ b [MOD M])
    (u : ℕ) :
    U1534.ee (-(((a * u : ℕ) : ℝ) / (M : ℝ)))
      = U1534.ee (-(((b * u : ℕ) : ℝ) / (M : ℝ))) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hab
  have h1 : (b : ℤ) = (a : ℤ) + (M : ℤ) * k := by
    rw [← hk]; ring
  have hz : ((b * u : ℕ) : ℤ) = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by
    calc ((b * u : ℕ) : ℤ) = (b : ℤ) * (u : ℤ) := by push_cast; ring
      _ = ((a : ℤ) + (M : ℤ) * k) * (u : ℤ) := by rw [h1]
      _ = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by push_cast; ring
  have hb : ((b * u : ℕ) : ℝ) = ((a * u : ℕ) : ℝ) + (M : ℝ) * ((k * (u : ℤ) : ℤ) : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at h3 ⊢
    linarith
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hkey : (-(((b * u : ℕ) : ℝ) / (M : ℝ)))
      = (-(((a * u : ℕ) : ℝ) / (M : ℝ))) + ((-(k * (u : ℤ) : ℤ) : ℤ) : ℝ) := by
    rw [hb]
    push_cast
    field_simp
    try ring
  rw [hkey, ee_int_add]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_sq_split. -/
private lemma ee_sq_split (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (a1 a2 z : ℕ) :
    U1534.ee (((((a1 * r + a2 * q) * z ^ 2 : ℕ)) : ℝ) / ((q * r : ℕ) : ℝ))
      = U1534.ee (((a1 * z ^ 2 : ℕ) : ℝ) / (q : ℝ))
        * U1534.ee (((a2 * z ^ 2 : ℕ) : ℝ) / (r : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hr
  have harg : (((((a1 * r + a2 * q) * z ^ 2 : ℕ)) : ℝ) / ((q * r : ℕ) : ℝ))
      = ((a1 * z ^ 2 : ℕ) : ℝ) / (q : ℝ) + ((a2 * z ^ 2 : ℕ) : ℝ) / (r : ℝ) := by
    push_cast
    field_simp
    try ring
  rw [harg, ee_add_real]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_neg_split. -/
private lemma ee_neg_split (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (a1 a2 n : ℕ) :
    U1534.ee (-((((a1 * r + a2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
      = U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))
        * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hr
  have harg : (-((((a1 * r + a2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
      = (-(((a1 * n : ℕ) : ℝ) / (q : ℝ))) + (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))) := by
    push_cast
    field_simp
    try ring
  rw [harg, ee_add_real]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.ee_nat_period'. -/
private lemma ee_nat_period' (M : ℕ) (hM : 0 < M) {a b : ℕ} (hab : a ≡ b [MOD M]) (u : ℕ) :
    U1534.ee (((u * a : ℕ) : ℝ) / (M : ℝ))
      = U1534.ee (((u * b : ℕ) : ℝ) / (M : ℝ)) := by
  rw [mul_comm u a, mul_comm u b]
  exact ee_nat_period M hM hab u


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sum_units_mul_raw. -/
private lemma sum_units_mul_raw {q m : ℕ} (hq : 0 < q) (hm : q.Coprime m) (F : ℕ → ℂ)
    (hper : ∀ b b' : ℕ, b ≡ b' [MOD q] → F b = F b') :
    (∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F (b * m))
      = ∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F b := by
  refine (Finset.sum_congr rfl (fun b _ => hper _ _ ?_)).trans (sum_units_mul hq hm F)
  show (b * m) % q = ((b * m) % q) % q
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hq)]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.inner_mul. -/
private lemma inner_mul (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) (n : ℕ) :
    (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)),
        ∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
          U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
            * U1534.ee (-(((a * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))))
      = (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
              U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ))
                * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))))
        * (∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
            ∑ x ∈ (Finset.range r).filter (fun x => Nat.Coprime x r),
              U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (r : ℝ))
                * U1534.ee (-(((a * n : ℕ) : ℝ) / (r : ℝ)))) := by
  classical
  have hM : 0 < q * r := Nat.mul_pos hq hr
  -- (1) reindex the outer variable
  have step1 :
      (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)),
        ∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
          U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
            * U1534.ee (-(((a * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))))
      = ∑ p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
            (Finset.range r).filter (fun a => Nat.Coprime a r),
          ∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
            U1534.ee ((((p.1 * r + p.2 * q) * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
              * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))) := by
    refine sum_residue_reindex hq hr hqr _ ?_
    intro a b hab
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have h1 : U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
        = U1534.ee (((b * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)) :=
      ee_nat_period (q * r) hM hab (x ^ 2)
    have h2 : U1534.ee (-(((a * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
        = U1534.ee (-(((b * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))) :=
      ee_nat_period_neg (q * r) hM hab n
    rw [h1, h2]
  rw [step1]
  -- (2) reindex the inner variable
  have step2 : ∀ p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r),
      (∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
        U1534.ee ((((p.1 * r + p.2 * q) * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
          * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))))
      = ∑ p' ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
            (Finset.range r).filter (fun a => Nat.Coprime a r),
          U1534.ee ((((p.1 * r + p.2 * q) * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ)
              / ((q * r : ℕ) : ℝ))
            * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))) := by
    intro p _
    refine sum_residue_reindex hq hr hqr _ ?_
    intro x y hxy
    have hsq : x ^ 2 ≡ y ^ 2 [MOD q * r] := by simpa [pow_two] using hxy.mul hxy
    have h1 : U1534.ee ((((p.1 * r + p.2 * q) * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
        = U1534.ee ((((p.1 * r + p.2 * q) * y ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)) :=
      ee_nat_period' (q * r) hM hsq (p.1 * r + p.2 * q)
    rw [h1]
  rw [Finset.sum_congr rfl step2]
  -- (3) split each value into its `q` and `r` parts
  have step3 : ∀ p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r),
      ∀ p' ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r),
      U1534.ee ((((p.1 * r + p.2 * q) * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ)
          / ((q * r : ℕ) : ℝ))
        * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
      = (U1534.ee (((p.1 * (p'.1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ))
            * U1534.ee (-(((p.1 * n : ℕ) : ℝ) / (q : ℝ))))
        * (U1534.ee (((p.2 * (p'.2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ))
            * U1534.ee (-(((p.2 * n : ℕ) : ℝ) / (r : ℝ)))) := by
    intro p _ p' _
    rw [ee_sq_split q r hq hr p.1 p.2 (p'.1 * r + p'.2 * q),
      ee_neg_split q r hq hr p.1 p.2 n]
    have hmodq : (p'.1 * r + p'.2 * q) ≡ (p'.1 * r) [MOD q] := by
      show (p'.1 * r + p'.2 * q) % q = (p'.1 * r) % q
      rw [show p'.1 * r + p'.2 * q = p'.1 * r + q * p'.2 from by ring,
        Nat.add_mul_mod_self_left]
    have hmodr : (p'.1 * r + p'.2 * q) ≡ (p'.2 * q) [MOD r] := by
      show (p'.1 * r + p'.2 * q) % r = (p'.2 * q) % r
      rw [show p'.1 * r + p'.2 * q = p'.2 * q + r * p'.1 from by ring,
        Nat.add_mul_mod_self_left]
    have hA : U1534.ee (((p.1 * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ) / (q : ℝ))
        = U1534.ee (((p.1 * (p'.1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ)) := by
      simp only [pow_two]
      exact ee_nat_period' q hq (hmodq.mul hmodq) p.1
    have hB : U1534.ee (((p.2 * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ))
        = U1534.ee (((p.2 * (p'.2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ)) := by
      simp only [pow_two]
      exact ee_nat_period' r hr (hmodr.mul hmodr) p.2
    rw [hA, hB]
    ring
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun p' hp' => step3 p hp p' hp'))]
  -- (4) remove the multipliers `r` and `q` from the two inner variables
  have subst1 : ∀ a1 a2 x2 : ℕ, (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        U1534.ee (((a1 * (x1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ))
          * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.ee (((a1 * x1 ^ 2 : ℕ) : ℝ) / (q : ℝ))
            * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ))) := by
    intro a1 a2 x2
    refine sum_units_mul_raw hq hqr (fun b => U1534.ee (((a1 * b ^ 2 : ℕ) : ℝ) / (q : ℝ))
      * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) ?_
    intro b b' hbb
    have hsq : b ^ 2 ≡ b' ^ 2 [MOD q] := by simpa [pow_two] using hbb.mul hbb
    rw [ee_nat_period' q hq hsq a1]
  have subst2 : ∀ a1 a2 x1 : ℕ, (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
        U1534.ee (((a2 * (x2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ))
          * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
      = ∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
          U1534.ee (((a2 * x2 ^ 2 : ℕ) : ℝ) / (r : ℝ))
            * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))) := by
    intro a1 a2 x1
    refine sum_units_mul_raw hr hqr.symm (fun b => U1534.ee (((a2 * b ^ 2 : ℕ) : ℝ) / (r : ℝ))
      * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ)))) ?_
    intro b b' hbb
    have hsq : b ^ 2 ≡ b' ^ 2 [MOD r] := by simpa [pow_two] using hbb.mul hbb
    rw [ee_nat_period' r hr hsq a2]
  simp only [Finset.sum_product]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (U1534.ee (((a1 * (x1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * (x2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ =>
      Finset.sum_congr rfl (fun x1 _ => ?_)))
    rw [← Finset.mul_sum, subst2 a1 a2 x1]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), U1534.ee (((a1 * (x1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * (x2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => ?_))
    rw [Finset.sum_mul]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), U1534.ee (((a1 * x1 ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * x2 ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => ?_))
    rw [subst1 a1 a2 0, subst2 a1 a2 0]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), U1534.ee (((a1 * x1 ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * x2 ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => ?_)
    rw [Finset.mul_sum]
  · rw [← Finset.sum_mul]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.A2_eq_double. -/
private lemma A2_eq_double (n q : ℕ) :
    U1534.A2 n q
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2)
        * ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
              U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ))
                * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))) := by
  unfold U1534.A2 U1534.gaussS
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [neg_div]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.A2_mul_coprime. -/
private lemma A2_mul_coprime {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r)
    (n : ℕ) : U1534.A2 n (q * r) = U1534.A2 n q * U1534.A2 n r := by
  rw [A2_eq_double n (q * r), A2_eq_double n q, A2_eq_double n r,
    inner_mul q r hq hr hqr n]
  have hμ : ((ArithmeticFunction.moebius (q * r) : ℤ) : ℂ)
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) * ((ArithmeticFunction.moebius r : ℤ) : ℂ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr]
    push_cast
    ring
  have hφ : ((Nat.totient (q * r) : ℂ))
      = (Nat.totient q : ℂ) * (Nat.totient r : ℂ) := by
    rw [Nat.totient_mul hqr]
    push_cast
    ring
  have hqφ : (Nat.totient q : ℂ) ≠ 0 := by
    have h : 0 < Nat.totient q := Nat.totient_pos.mpr hq
    exact_mod_cast h.ne'
  have hrφ : (Nat.totient r : ℂ) ≠ 0 := by
    have h : 0 < Nat.totient r := Nat.totient_pos.mpr hr
    exact_mod_cast h.ne'
  rw [hμ, hφ]
  field_simp
  try ring


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.A2_one. -/
private lemma A2_one (n : ℕ) : U1534.A2 n 1 = 1 := by
  unfold U1534.A2 U1534.gaussS
  have h1 : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  rw [h1, ArithmeticFunction.moebius_apply_one, Nat.totient_one]
  simp [U1534.ee, Complex.exp_zero]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.A2_prod_primes. -/
private lemma A2_prod_primes (n : ℕ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → U1534.A2 n (s.prod id) = ∏ p ∈ s, U1534.A2 n p := by
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    simpa using A2_one n
  · intro a s ha hih hprime
    have hpa : a.Prime := hprime a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (s.prod id) := by
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      exact (Nat.coprime_primes hpa (hs p hp)).mpr (by rintro rfl; exact ha hp)
    have hpos : 0 < s.prod id :=
      Finset.prod_pos (fun p hp => (hs p hp).pos)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    show U1534.A2 n (a * s.prod id) = U1534.A2 n a * s.prod (fun p => U1534.A2 n p)
    rw [A2_mul_coprime hpa.pos hpos hcop n, hih hs]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.prod_expansion. -/
private lemma prod_expansion (n : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 + U1534.A2 n p) = ∑ t ∈ s.powerset, U1534.A2 n (t.prod id) := by
  classical
  rw [Finset.prod_add]
  trans ∑ t ∈ s.powerset, ∏ i ∈ s \ t, U1534.A2 n i
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.prod_const_one, one_mul]
  trans ∑ t ∈ s.powerset, U1534.A2 n ((s \ t).prod id)
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    refine (A2_prod_primes n (s \ t) (fun p hp => hprime p (Finset.mem_sdiff.mp hp).1)).symm
  · refine Finset.sum_bij (fun t _ => s \ t) (fun t _ => Finset.mem_powerset.mpr Finset.sdiff_subset)
      ?_ ?_ ?_
    · intro t ht t' ht' heq
      have ht : t ⊆ s := Finset.mem_powerset.mp ht
      have ht' : t' ⊆ s := Finset.mem_powerset.mp ht'
      have h := heq
      rw [← Finset.sdiff_sdiff_eq_self ht, ← Finset.sdiff_sdiff_eq_self ht', h]
    · intro b hb
      refine ⟨s \ b, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hb)
    · intro t _
      rfl


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.squarefree_prod_primes. -/
private lemma squarefree_prod_primes (t : Finset ℕ) (h : ∀ p ∈ t, p.Prime) :
    Squarefree (t.prod id) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using squarefree_one (R := ℕ)
  | insert a t ha ih =>
    have hpa : a.Prime := h a (Finset.mem_insert_self a t)
    have ht : ∀ p ∈ t, p.Prime := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (t.prod id) := by
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      exact (Nat.coprime_primes hpa (ht p hp)).mpr (by rintro rfl; exact ha hp)
    have hins : (insert a t).prod id = a * t.prod id := by
      rw [Finset.prod_insert ha]; rfl
    rw [hins]
    exact (Nat.squarefree_mul hcop).mpr ⟨hpa.squarefree, ih ht⟩


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sum_smooth_eq_subsets. -/
private lemma sum_smooth_eq_subsets (n : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (m : ℕ) :
    (∑ q ∈ (Finset.Icc 1 m).filter
        (fun q => (∀ p, p.Prime → p ∣ q → p ∈ s) ∧ Squarefree q), U1534.A2 n q)
      = ∑ t ∈ s.powerset.filter (fun t => t.prod id ≤ m), U1534.A2 n (t.prod id) := by
  classical
  refine (Finset.sum_bij (s := s.powerset.filter (fun t => t.prod id ≤ m))
    (t := (Finset.Icc 1 m).filter
      (fun q => (∀ p, p.Prime → p ∣ q → p ∈ s) ∧ Squarefree q))
    (f := fun t => U1534.A2 n (t.prod id)) (g := fun q => U1534.A2 n q)
    (fun t _ => t.prod id) ?_ ?_ ?_ ?_).symm
  · intro t ht
    obtain ⟨hts, hle⟩ := Finset.mem_filter.mp ht
    have hsub : t ⊆ s := Finset.mem_powerset.mp hts
    have hpr : ∀ p ∈ t, p.Prime := fun p hp => hprime p (hsub hp)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hle⟩, ?_, ?_⟩
    · exact Finset.one_le_prod (fun p hp => (hpr p hp).one_le)
    · intro p hpp hpdvd
      have hmem : p ∈ t := by
        obtain ⟨a, hat, hdvd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp) (fun x => x)).mp hpdvd
        have hap : Nat.Prime a := hpr a hat
        rcases (Nat.dvd_prime hap).mp hdvd with h1 | h2
        · exact absurd h1 hpp.ne_one
        · rw [h2]
          exact hat
      exact hsub hmem
    · exact squarefree_prod_primes t hpr
  · intro t ht t' ht' heq
    have hsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hsub' : t' ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have h1 : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod (fun p hp => hprime p (hsub hp))
    have h2 : (∏ p ∈ t', p).primeFactors = t' :=
      Nat.primeFactors_prod (fun p hp => hprime p (hsub' hp))
    have heq' : (∏ p ∈ t, p) = (∏ p ∈ t', p) := heq
    calc t = (∏ p ∈ t, p).primeFactors := h1.symm
      _ = (∏ p ∈ t', p).primeFactors := by rw [heq']
      _ = t' := h2
  · intro q hq
    obtain ⟨hIcc, hsmooth, hsq⟩ := Finset.mem_filter.mp hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hIcc).1
    have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
    have hle : q ≤ m := (Finset.mem_Icc.mp hIcc).2
    refine ⟨q.primeFactors, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro p hp
        obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
        exact hsmooth p hpp hpdvd
      · have hpf : q.primeFactors.prod id = q := Nat.prod_primeFactors_of_squarefree hsq
        rw [hpf]
        exact hle
    · exact Nat.prod_primeFactors_of_squarefree hsq
  · intro t _; rfl


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.mem_primes_iff. -/
private lemma mem_primes_iff (Q : ℝ) (hQ : 0 ≤ Q) {p : ℕ} (hp : p.Prime) :
    (p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime ↔ (p : ℝ) ≤ Q) := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, -⟩
    have h1 : p ≤ ⌊Q⌋₊ := Nat.lt_succ_iff.mp hlt
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hQ)
  · intro hle
    refine ⟨?_, hp⟩
    have h1 : p ≤ ⌊Q⌋₊ := Nat.le_floor hle
    omega


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.smoothWeight_eq_indicator. -/
private lemma smoothWeight_eq_indicator (Q : ℝ) (hQ : 0 ≤ Q) (q : ℕ) :
    (Task506aTask129b.smoothWeight q Q : ℂ)
      = if (∀ p, p.Prime → p ∣ q → p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime)
          then 1 else 0 := by
  unfold LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight
  by_cases h : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
  · have h' : ∀ p, p.Prime → p ∣ q →
        p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime :=
      fun p hp hpq => (mem_primes_iff Q hQ hp).mpr (h p hp hpq)
    simp only [if_pos h, if_pos h']
    norm_num
  · have h' : ¬ ∀ p, p.Prime → p ∣ q →
        p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
      intro hc
      exact h fun p hp hpq => (mem_primes_iff Q hQ hp).mp (hc p hp hpq)
    simp only [if_neg h, if_neg h']
    norm_num


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sum_smoothWeight_eq. -/
private lemma sum_smoothWeight_eq (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (m : ℕ) :
    (∑ q ∈ Finset.Icc 1 m, (Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
      = ∑ q ∈ (Finset.Icc 1 m).filter
          (fun q => (∀ p, p.Prime → p ∣ q →
              p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) ∧ Squarefree q),
          U1534.A2 n q := by
  classical
  have hstep : ∀ q ∈ Finset.Icc 1 m,
      (Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q
        = if (∀ p, p.Prime → p ∣ q →
              p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) then U1534.A2 n q else 0 := by
    intro q _
    rw [smoothWeight_eq_indicator Q hQ q]
    by_cases h : ∀ p, p.Prime → p ∣ q → p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
    · simp only [if_pos h, one_mul]
    · simp only [if_neg h, zero_mul]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
  have hsub : (Finset.Icc 1 m).filter
        (fun q => (∀ p, p.Prime → p ∣ q →
            p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) ∧ Squarefree q)
      ⊆ (Finset.Icc 1 m).filter (fun q => ∀ p, p.Prime → p ∣ q →
          p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) := by
    intro q hq
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  refine (Finset.sum_subset hsub ?_).symm
  intro q hq hqnot
  refine LeanLab.KumchevLiu2007.Task506aTask129b.A2_eq_zero_of_not_squarefree n q ?_
  intro hsq
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
  exact hqnot (Finset.mem_filter.mpr ⟨h1, h2, hsq⟩)


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.smooth_sum_Icc. -/
private lemma smooth_sum_Icc (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (m : ℕ) :
    (∑ q ∈ Finset.Icc 1 m, (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
      = ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => t.prod id ≤ m), U1534.A2 n (t.prod id) := by
  refine (sum_smoothWeight_eq n Q hQ m).trans (sum_smooth_eq_subsets n _ ?_ m)
  intro p hp
  exact (Finset.mem_filter.mp hp).2


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.series_tail_eq. -/
private lemma series_tail_eq (n : ℕ) (P Q Q0 : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P) (hPQ : P ≤ Q) :
    LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
        - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P Q0 Q
      = ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => t.prod id ≤ max ⌊P⌋₊ ⌊Q0⌋₊), U1534.A2 n (t.prod id) := by
  classical
  have hPQ' : ⌊P⌋₊ ≤ ⌊Q⌋₊ := Nat.floor_mono hPQ
  have hser : LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
      = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
          (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q := by
    unfold LeanLab.KumchevLiu2007.Task506aTask129.series2
    refine Finset.sum_congr rfl (fun q hq => ?_)
    obtain ⟨hq1, hqP⟩ := Finset.mem_Icc.mp hq
    have hqQ : q ≤ ⌊Q⌋₊ := le_trans hqP hPQ'
    have hsmooth : ∀ p, p.Prime → p ∣ q →
        p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
      intro p hp hpq
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
      have hpq' : p ≤ q := Nat.le_of_dvd hqpos hpq
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    rw [smoothWeight_eq_indicator Q hQ q, if_pos hsmooth]
    ring
  have htail : LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P Q0 Q
      = -∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊,
          (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q := by
    unfold LeanLab.KumchevLiu2007.Task506aTask129b.tail2
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [hser, htail]
  by_cases hle : ⌊P⌋₊ ≤ ⌊Q0⌋₊
  · rw [max_eq_right hle, sub_neg_eq_add]
    have hsplit : (∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
          (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
        + (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊,
          (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
        = ∑ q ∈ Finset.Icc 1 ⌊Q0⌋₊,
          (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q := by
      have h1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊Q0⌋₊)
        (fun q : ℕ => q ≤ ⌊P⌋₊)
        (fun q => (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
      rw [← h1]
      congr 1
      · refine Finset.sum_congr ?_ (fun q _ => rfl)
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · refine Finset.sum_congr ?_ (fun q _ => rfl)
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        omega
    rw [hsplit, smooth_sum_Icc n Q hQ ⌊Q0⌋₊]
  · have hPle : ⌊Q0⌋₊ ≤ ⌊P⌋₊ := le_of_lt (not_le.mp hle)
    rw [max_eq_left hPle]
    have hzero : (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊,
        (LeanLab.KumchevLiu2007.Task506aTask129b.smoothWeight q Q : ℂ) * U1534.A2 n q) = 0 := by
      refine Finset.sum_eq_zero (fun q hq => ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hq
      omega
    rw [hzero, neg_zero, sub_zero, smooth_sum_Icc n Q hQ ⌊P⌋₊]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.product2_eq_subsets. -/
private lemma product2_eq_subsets (n : ℕ) (Q : ℝ) :
    LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q
      = ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset,
          U1534.A2 n (t.prod id) := by
  unfold LeanLab.KumchevLiu2007.Task506aTask129b.product2
  exact prod_expansion n _ (fun p hp => (Finset.mem_filter.mp hp).2)


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.rem_eq_subset_tail. -/
private lemma rem_eq_subset_tail (n : ℕ) (P Q Q0 : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P)
    (hPQ : P ≤ Q) :
    LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
        - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q
        - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P Q0 Q
      = -∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id), U1534.A2 n (t.prod id) := by
  classical
  have hstep : LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
        - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q
        - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P Q0 Q
      = (LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
          - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P Q0 Q)
        - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q := by ring
  rw [hstep, series_tail_eq n P Q Q0 hQ hP hPQ, product2_eq_subsets n Q]
  have h2 := Finset.sum_filter_add_sum_filter_not
    (((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset)
    (fun t : Finset ℕ => t.prod id ≤ max ⌊P⌋₊ ⌊Q0⌋₊)
    (fun t => U1534.A2 n (t.prod id))
  rw [← h2]
  have hcongr : ((((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset).filter
        (fun t : Finset ℕ => ¬ t.prod id ≤ max ⌊P⌋₊ ⌊Q0⌋₊))
      = ((((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset).filter
        (fun t : Finset ℕ => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id)) := by
    exact Finset.filter_congr (fun t _ => not_le)
  rw [hcongr]
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.prod_le_prod_real. -/
private lemma prod_le_prod_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h1 : f a ≤ g a := h a (Finset.mem_insert_self a s)
    have h2 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul h1 h2 hfs (le_trans hfa h1)


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.A2_norm_le. -/
private lemma A2_norm_le (n : ℕ) (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime) :
    ‖U1534.A2 n (t.prod id)‖ ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
  classical
  rw [A2_prod_primes n t hprime, Complex.norm_prod]
  refine prod_le_prod_real t (fun p => ‖U1534.A2 n p‖)
    (fun p => ((p : ℝ) + 6) / (p : ℝ) ^ 2) (fun p _ => norm_nonneg _) (fun p hp => ?_)
  haveI : Fact p.Prime := ⟨hprime p hp⟩
  refine (LeanLab.KumchevLiu2007.Task506aTask129b.A2_prime_norm_le_inv_add p n).trans ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkey : (1 : ℝ) / (p : ℝ) + 6 / (p : ℝ) ^ 2 = ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    field_simp
  rw [hkey]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.prod_add_expansion. -/
private lemma prod_add_expansion {M : Type*} [CommSemiring M] (s : Finset ℕ) (g : ℕ → M) :
    ∏ p ∈ s, (1 + g p) = ∑ t ∈ s.powerset, ∏ p ∈ t, g p := by
  classical
  rw [Finset.prod_add]
  trans ∑ t ∈ s.powerset, ∏ i ∈ s \ t, g i
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.prod_const_one, one_mul]
  · refine Finset.sum_bij (fun t _ => s \ t) (fun t _ => Finset.mem_powerset.mpr Finset.sdiff_subset)
      ?_ ?_ ?_
    · intro t ht t' ht' heq
      have ht : t ⊆ s := Finset.mem_powerset.mp ht
      have ht' : t' ⊆ s := Finset.mem_powerset.mp ht'
      have h := heq
      rw [← Finset.sdiff_sdiff_eq_self ht, ← Finset.sdiff_sdiff_eq_self ht', h]
    · intro b hb
      refine ⟨s \ b, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hb)
    · intro t _
      rfl


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.subset_tail_rankin. -/
private lemma subset_tail_rankin (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (Q0 : ℝ) (hQ0 : 0 < Q0) (σ : ℝ) (hσ : 0 < σ) :
    (∑ t ∈ s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)),
        ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      ≤ Q0 ^ (-σ) * ∏ p ∈ s,
          (1 + (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) := by
  classical
  have hw : ∀ p ∈ s, (0 : ℝ) ≤ ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro p _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p ‹p ∈ s›).two_le
    positivity
  -- pointwise Rankin bound on the filtered set
  have hpt : ∀ t ∈ s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)),
      ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2
        ≤ Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
            * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro t ht
    obtain ⟨-, hgt⟩ := Finset.mem_filter.mp ht
    have hX : (0 : ℝ) ≤ (((t.prod id : ℕ)) : ℝ) := by positivity
    have hge : (1 : ℝ) ≤ ((((t.prod id : ℕ)) : ℝ) / Q0) ^ σ := by
      refine Real.one_le_rpow (le_of_lt ?_) hσ.le
      rw [lt_div_iff₀ hQ0]
      linarith
    have heq : Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
        = ((((t.prod id : ℕ)) : ℝ) / Q0) ^ σ := by
      rw [Real.rpow_neg hQ0.le, Real.div_rpow hX hQ0.le]
      field_simp
    have hprodw : (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 :=
      Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hp))
    calc ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2
        = 1 * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := (one_mul _).symm
      _ ≤ (Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ))
            * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hprodw
          rw [heq]
          exact hge
  refine (Finset.sum_le_sum hpt).trans ?_
  -- drop the filter, keeping nonnegativity
  have hsub : s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)) ⊆ s.powerset :=
    Finset.filter_subset _ _
  have hnonneg : ∀ t ∈ s.powerset, t ∉ s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)) →
      (0 : ℝ) ≤ Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro t ht _
    have h1 : (0 : ℝ) ≤ Q0 ^ (-σ) := Real.rpow_nonneg hQ0.le _
    have h2 : (0 : ℝ) ≤ ((((t.prod id : ℕ)) : ℝ) ^ σ) := Real.rpow_nonneg (by positivity) _
    have h3 : (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 :=
      Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp ht hp))
    positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans ?_
  have hcongr : (∑ t ∈ s.powerset, Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      = ∑ t ∈ s.powerset, Q0 ^ (-σ) * (((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2) :=
    Finset.sum_congr rfl (fun t _ => by ring)
  rw [hcongr, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hQ0.le _)
  have hexp : (∑ t ∈ s.powerset, ((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      = ∑ t ∈ s.powerset, ∏ p ∈ t, ((p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hcast : ((((t.prod id : ℕ)) : ℝ)) = ∏ p ∈ t, (p : ℝ) := by push_cast; rfl
    rw [hcast, ← Real.finsetProd_rpow t (fun p => (p : ℝ))
      (fun p _ => Nat.cast_nonneg p) σ, Finset.prod_mul_distrib]
  rw [hexp, prod_add_expansion]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.prod_one_add_le_exp. -/
private lemma prod_one_add_le_exp (s : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ p ∈ s, 0 ≤ y p) :
    ∏ p ∈ s, (1 + y p) ≤ Real.exp (∑ p ∈ s, y p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.exp_add]
    have h1 : 1 + y a ≤ Real.exp (y a) := by
      simpa [add_comm] using Real.add_one_le_exp (y a)
    have h2 : ∏ p ∈ s, (1 + y p) ≤ Real.exp (∑ p ∈ s, y p) :=
      ih (fun p hp => hy p (Finset.mem_insert_of_mem hp))
    have h3 : (0 : ℝ) ≤ ∏ p ∈ s, (1 + y p) :=
      Finset.prod_nonneg (fun p hp => by
        have := hy p (Finset.mem_insert_of_mem hp); linarith)
    exact mul_le_mul h1 h2 h3 (Real.exp_nonneg _)


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.weight_pow_le. -/
private lemma weight_pow_le (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : 0 ≤ σ) :
    (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2) ≤ 7 * (p : ℝ) ^ (σ - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkey : (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)
      = (p : ℝ) ^ (σ - 1) * (1 + 6 / (p : ℝ)) := by
    rw [Real.rpow_sub hp0 σ 1, Real.rpow_one]
    field_simp
    try ring
  rw [hkey]
  have hnon : (0 : ℝ) ≤ (p : ℝ) ^ (σ - 1) := Real.rpow_nonneg hp0.le _
  have h6 : 1 + 6 / (p : ℝ) ≤ 7 := by
    have : 0 < (p : ℝ) := hp0
    have hle : 6 / (p : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hp0]; linarith
    linarith
  calc (p : ℝ) ^ (σ - 1) * (1 + 6 / (p : ℝ))
      ≤ (p : ℝ) ^ (σ - 1) * 7 := mul_le_mul_of_nonneg_left h6 hnon
    _ = 7 * (p : ℝ) ^ (σ - 1) := by ring


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.euler_product_le. -/
private lemma euler_product_le (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∏ p ∈ s, (1 + (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2))
      ≤ Real.exp (7 * ∑ p ∈ s, (p : ℝ) ^ (σ - 1)) := by
  classical
  refine (prod_one_add_le_exp s
    (fun p => (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) ?_).trans ?_
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    positivity
  · refine Real.exp_le_exp.mpr ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    exact weight_pow_le p (hprime p hp) σ hσ


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.one_div_succ_le_log_sub. -/
private lemma one_div_succ_le_log_sub (K : ℕ) (hK : 1 ≤ K) :
    1 / ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 1) - Real.log (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h := Real.one_sub_inv_le_log_of_pos (x := ((K : ℝ) + 1) / (K : ℝ)) (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hK0)] at h
  have hinv : (((K : ℝ) + 1) / (K : ℝ))⁻¹ = 1 - 1 / ((K : ℝ) + 1) := by
    field_simp
    ring
  rw [hinv] at h
  linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sum_Icc_one_div_le. -/
private lemma sum_Icc_one_div_le (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ)) ≤ 1 + Real.log K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
      have hstep := one_div_succ_le_log_sub K hK
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.card_primes_block_le. -/
private lemma card_primes_block_le (k : ℕ) (hk : 1 ≤ k) (s : Finset ℕ)
    (hsp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, 2 ^ k ≤ p) (hhi : ∀ p ∈ s, p ≤ 2 ^ (k + 1)) :
    (s.card : ℝ) ≤ Real.log 4 * (2 : ℝ) ^ (k + 1) / ((k : ℝ) * Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpt : ∀ p ∈ s, (k : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    have hp2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hcast : (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    have hkp : (2 : ℝ) ^ k ≤ (p : ℝ) := by
      have h : (((2 ^ k : ℕ)) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo p hp
      rwa [hcast] at h
    have h := Real.log_le_log hp2 hkp
    rwa [Real.log_pow] at h
  have hsum : (s.card : ℝ) * ((k : ℝ) * Real.log 2) ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
    have h := Finset.sum_le_sum hpt
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have htheta : (∑ p ∈ s, Real.log (p : ℝ)) ≤ Real.log 4 * (((2 ^ (k + 1) : ℕ)) : ℝ) := by
    have hsub : s ⊆ Nat.primesLE (2 ^ (k + 1)) := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨hhi p hp, hsp p hp⟩
    have h1 : (∑ p ∈ s, Real.log (p : ℝ))
        ≤ ∑ p ∈ Nat.primesLE (2 ^ (k + 1)), Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    rw [← Chebyshev.theta_eq_sum_primesLE_log (2 ^ (k + 1))] at h1
    have h3 := Chebyshev.theta_le_log4_mul_x
      (x := (((2 ^ (k + 1) : ℕ)) : ℝ)) (by positivity)
    linarith
  have hcast2 : (((2 ^ (k + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) * Real.log 2)]
  calc (s.card : ℝ) * ((k : ℝ) * Real.log 2) ≤ ∑ p ∈ s, Real.log (p : ℝ) := hsum
    _ ≤ Real.log 4 * (((2 ^ (k + 1) : ℕ)) : ℝ) := htheta
    _ = Real.log 4 * (2 : ℝ) ^ (k + 1) := by rw [hcast2]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.log2_spec. -/
private lemma log2_spec {z : ℕ} (hz : 0 < z) : 2 ^ Nat.log2 z ≤ z ∧ z < 2 ^ (Nat.log2 z + 1) := by
  refine ⟨(Nat.le_log2 hz.ne').mp le_rfl, ?_⟩
  by_contra hcon
  simp only [not_lt] at hcon
  have hle := (Nat.le_log2 hz.ne').mpr hcon
  omega


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.prime_sum_inv_le. -/
private lemma prime_sum_inv_le (z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) ≤ 40 * (1 + Real.log (1 + Real.log z)) := by
  classical
  have hz0 : z ≠ 0 := by omega
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKspec := log2_spec (z := z) (by omega : 0 < z)
  obtain ⟨h2K, -⟩ := hKspec
  have hmaps : ∀ p ∈ Nat.primesLE z, Nat.log2 p ∈ Finset.Icc 1 (Nat.log2 z) := by
    intro p hp
    obtain ⟨hpz, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpne : p ≠ 0 := hpp.ne_zero
    have h2p : 2 ^ Nat.log2 p ≤ p := (Nat.le_log2 hpne).mp le_rfl
    have h2z : 2 ^ Nat.log2 p ≤ z := le_trans h2p hpz
    refine Finset.mem_Icc.mpr ⟨?_, (Nat.le_log2 hz0).mpr h2z⟩
    rw [Nat.le_log2 hpne]
    calc 2 ^ 1 = 2 := by norm_num
      _ ≤ p := hpp.two_le
  have hfiber : ∀ j ∈ Finset.Icc 1 (Nat.log2 z),
      (∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ)) ≤ 6 / (j : ℝ) := by
    intro j hj
    obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
    have hsp : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), p.Prime :=
      fun p hp => (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hlo : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 2 ^ j ≤ p := by
      intro p hp
      have hpe : Nat.log2 p = j := (Finset.mem_filter.mp hp).2
      have hpne : p ≠ 0 := (hsp p hp).ne_zero
      rw [← hpe]
      exact (Nat.le_log2 hpne).mp le_rfl
    have hhi : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), p ≤ 2 ^ (j + 1) := by
      intro p hp
      have hpe : Nat.log2 p = j := (Finset.mem_filter.mp hp).2
      have hpne : p ≠ 0 := (hsp p hp).ne_zero
      have hlt : p < 2 ^ (Nat.log2 p + 1) := (log2_spec hpne.bot_lt).2
      rw [hpe] at hlt
      omega
    have hcard := card_primes_block_le j hj1 _ hsp hlo hhi
    have hpoint : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j),
        1 / (p : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
      intro p hp
      have hp2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hpj : (2 : ℝ) ^ j ≤ (p : ℝ) := by
        have hcast : (((2 ^ j : ℕ)) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
        have h : (((2 ^ j : ℕ)) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo p hp
        rwa [hcast] at h
      exact one_div_le_one_div_of_le hp2 hpj
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    calc (∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ))
        ≤ ∑ _p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (2 : ℝ) ^ j :=
          Finset.sum_le_sum hpoint
      _ = (((Nat.primesLE z).filter (fun p => Nat.log2 p = j)).card : ℝ) * (1 / (2 : ℝ) ^ j) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = (((Nat.primesLE z).filter (fun p => Nat.log2 p = j)).card : ℝ) / (2 : ℝ) ^ j := by ring
      _ ≤ (Real.log 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) * Real.log 2)) / (2 : ℝ) ^ j :=
          div_le_div_of_nonneg_right hcard h2j.le
      _ = 4 / (j : ℝ) := by
          rw [hlog4]
          field_simp
          ring
      _ ≤ 6 / (j : ℝ) := div_le_div_of_nonneg_right (by norm_num) hjR.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => 1 / (p : ℝ))]
  have hKpos : 1 ≤ Nat.log2 z := by
    have hmem : Nat.log2 2 ∈ Finset.Icc 1 (Nat.log2 z) :=
      hmaps 2 (Nat.mem_primesLE.mpr ⟨hz, Nat.prime_two⟩)
    rw [show Nat.log2 2 = 1 by decide] at hmem
    exact (Finset.mem_Icc.mp hmem).2
  have hKle : ((Nat.log2 z : ℕ) : ℝ) * Real.log 2 ≤ Real.log z := by
    have hcast : (((2 ^ Nat.log2 z : ℕ)) : ℝ) = (2 : ℝ) ^ Nat.log2 z := by push_cast; ring
    have h : (((2 ^ Nat.log2 z : ℕ)) : ℝ) ≤ (z : ℝ) := by exact_mod_cast h2K
    rw [hcast] at h
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 z := by positivity
    have hlog := Real.log_le_log h2pos h
    rw [Real.log_pow] at hlog
    exact hlog
  have hKle' : ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log z / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact hKle
  have hloglog : Real.log ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log (Real.log z) + 1 := by
    have hKR : (0 : ℝ) < ((Nat.log2 z : ℕ) : ℝ) := by exact_mod_cast hKpos
    have h1 : Real.log ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log (Real.log z / Real.log 2) :=
      Real.log_le_log hKR hKle'
    rw [Real.log_div hlogz.ne' hlog2.ne'] at h1
    have h2 : -Real.log (Real.log 2) ≤ 1 := by
      have hexp : Real.exp (-1) < Real.log 2 := by
        have h1 : Real.exp (-1) < 0.4 := by
          rw [Real.exp_neg]
          rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 0.4)]
          have := Real.exp_one_gt_d9
          norm_num
          linarith
        linarith [Real.log_two_gt_d9]
      have h3 := Real.le_log_iff_exp_le hlog2 |>.mpr hexp.le
      linarith
    linarith
  have hlog1 : Real.log (1 + Real.log z) ≥ 0 := Real.log_nonneg (by linarith)
  calc (∑ j ∈ Finset.Icc 1 (Nat.log2 z),
        ∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ))
      ≤ ∑ j ∈ Finset.Icc 1 (Nat.log2 z), 6 / (j : ℝ) := Finset.sum_le_sum hfiber
    _ = 6 * ∑ j ∈ Finset.Icc 1 (Nat.log2 z), 1 / (j : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 6 * (1 + Real.log ((Nat.log2 z : ℕ) : ℝ)) := by
        have := sum_Icc_one_div_le (Nat.log2 z)
        linarith
    _ ≤ 40 * (1 + Real.log (1 + Real.log z)) := by
        have hLL : Real.log (Real.log z) ≤ Real.log (1 + Real.log z) :=
          Real.log_le_log hlogz (by linarith)
        linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.log_le_rpow_div. -/
private lemma log_le_rpow_div {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) :
    Real.log u ≤ u ^ t / t := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ t) = t * Real.log u := Real.log_rpow hu0 t
  have h2 : Real.log (u ^ t) ≤ u ^ t - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 t)
  have hut : (1 : ℝ) ≤ u ^ t := Real.one_le_rpow hu ht.le
  rw [le_div_iff₀ ht]
  nlinarith [h1, h2]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.logu_add_two_le. -/
private lemma logu_add_two_le {u ε : ℝ} (hu : 1 ≤ u) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log u + 2 ≤ 6 * u ^ (ε / 4) / ε := by
  have hu0 : (0 : ℝ) < u := by linarith
  have ht : (0 : ℝ) < ε / 4 := by linarith
  have hP : (0 : ℝ) < u ^ (ε / 4) := Real.rpow_pos_of_pos hu0 _
  have h1 : Real.log u ≤ u ^ (ε / 4) / (ε / 4) := log_le_rpow_div hu ht
  have h2 : u ^ (ε / 4) / (ε / 4) = 4 * u ^ (ε / 4) / ε := by field_simp
  rw [h2] at h1
  have h3 : (1 : ℝ) ≤ u ^ (ε / 4) := Real.one_le_rpow hu ht.le
  have h5 : 2 ≤ 2 * u ^ (ε / 4) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [hP, h3, hε1]
  have h7 : 4 * u ^ (ε / 4) / ε + 2 * u ^ (ε / 4) / ε = 6 * u ^ (ε / 4) / ε := by ring
  linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.rpow_mul_self. -/
private lemma rpow_mul_self {X ε : ℝ} (hX : 0 ≤ X) (hε : 0 < ε) :
    (X ^ (4 / (3 * ε))) ^ ((3 * ε) / 4) = X := by
  rw [← Real.rpow_mul hX]
  rw [show 4 / (3 * ε) * ((3 * ε) / 4) = 1 by field_simp]
  rw [Real.rpow_one]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.rpow_threshold. -/
private lemma rpow_threshold {X ε u : ℝ} (hX : 0 ≤ X) (hε : 0 < ε)
    (hu : X ^ (4 / (3 * ε)) ≤ u) : X ≤ u ^ ((3 * ε) / 4) := by
  have h1 : (X ^ (4 / (3 * ε))) ^ ((3 * ε) / 4) ≤ u ^ ((3 * ε) / 4) := by
    apply Real.rpow_le_rpow (Real.rpow_nonneg hX _) hu
    positivity
  rwa [rpow_mul_self hX hε] at h1


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.remainder_le_majorant. -/
private lemma remainder_le_majorant (n : ℕ) (P Q Q0 : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P)
    (hPQ : P ≤ Q) :
    ‖(LeanLab.KumchevLiu2007.Task506aTask129.series2 n P - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q)
        - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P Q0 Q‖
      ≤ ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
  classical
  have hΔ := rem_eq_subset_tail n P Q Q0 hQ hP hPQ
  rw [hΔ, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  set S : Finset ℕ := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime with hSdef
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hsub : S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id)
      ⊆ S.powerset.filter (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨ht1, ?_⟩
    have hmax : ⌊Q0⌋₊ ≤ max ⌊P⌋₊ ⌊Q0⌋₊ := le_max_right _ _
    have h2 : (((max ⌊P⌋₊ ⌊Q0⌋₊ : ℕ)) : ℝ) < (((t.prod id : ℕ)) : ℝ) := by exact_mod_cast ht2
    have h3 : (((⌊Q0⌋₊ : ℕ)) : ℝ) ≤ (((max ⌊P⌋₊ ⌊Q0⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hmax
    linarith
  have hnn : ∀ t ∈ S.powerset.filter (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
      t ∉ S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id) →
      (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro t ht _
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hprime p (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hp)).two_le
    positivity
  calc (∑ t ∈ S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id),
        ‖U1534.A2 n (t.prod id)‖)
      ≤ ∑ t ∈ S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        exact A2_norm_le n t
          (fun p hp => hprime p (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hp))
    _ ≤ ∑ t ∈ S.powerset.filter (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.majorant_le. -/
private lemma majorant_le {Q Q0 : ℝ} (hQ1 : 1 ≤ Q) (hQ0 : 1 ≤ Q0) {σ : ℝ} (hσ : 0 < σ) :
    (∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
        (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
        ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      ≤ Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))
          + 7 * (Real.exp (σ * Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ))
            * (40 * (1 + Real.log (1 + Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ)))))) := by
  classical
  set S : Finset ℕ := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime with hSdef
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  set z : ℕ := ⌊Q⌋₊ + 1 with hzdef
  have hz2 : 2 ≤ z := by
    have h1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
    omega
  set L : ℝ := Real.log z with hLdef
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hQ0pos : (0 : ℝ) < (((⌊Q0⌋₊ : ℕ)) : ℝ) := by
    have h1 : 1 ≤ ⌊Q0⌋₊ := Nat.le_floor (by exact_mod_cast hQ0)
    exact_mod_cast (by omega : 0 < ⌊Q0⌋₊)
  have hSsub : S ⊆ Nat.primesLE z := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hplt : p < z := by
      have := Finset.mem_range.mp hp1.1
      omega
    exact Nat.mem_primesLE.mpr ⟨le_of_lt hplt, hp1.2⟩
  -- `p^(σ-1) ≤ exp(σ L)/p` for `p ∈ S`
  have hterm : ∀ p ∈ S, (p : ℝ) ^ (σ - 1) ≤ Real.exp (σ * L) * (1 / (p : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpz : (p : ℝ) ≤ (z : ℝ) := by
      have hplt : p < z := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        omega
      exact_mod_cast le_of_lt hplt
    have hlogp : Real.log (p : ℝ) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log hp0 hpz
    have hmono : Real.exp (Real.log (p : ℝ) * σ) ≤ Real.exp (L * σ) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hlogp, hσ.le]
    have hsplit : (p : ℝ) ^ (σ - 1) = (p : ℝ) ^ σ / (p : ℝ) := by
      rw [Real.rpow_sub hp0 σ 1, Real.rpow_one]
    have h2 : (p : ℝ) ^ σ / (p : ℝ) ≤ Real.exp (L * σ) / (p : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ hp0.le
      rw [Real.rpow_def_of_pos hp0 σ]
      exact hmono
    rw [hsplit]
    calc (p : ℝ) ^ σ / (p : ℝ) ≤ Real.exp (L * σ) / (p : ℝ) := h2
      _ = Real.exp (σ * L) * (1 / (p : ℝ)) := by
          rw [mul_comm L σ, div_eq_mul_one_div]
  have hPsum : (∑ p ∈ S, (p : ℝ) ^ (σ - 1))
      ≤ Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))) := by
    have h1 : (∑ p ∈ S, (p : ℝ) ^ (σ - 1))
        ≤ ∑ p ∈ S, Real.exp (σ * L) * (1 / (p : ℝ)) := Finset.sum_le_sum hterm
    have h2 : (∑ p ∈ S, Real.exp (σ * L) * (1 / (p : ℝ)))
        = Real.exp (σ * L) * ∑ p ∈ S, 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
    have h3 : (∑ p ∈ S, 1 / (p : ℝ)) ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun p hp _ => by positivity)
    have h4 := prime_sum_inv_le z hz2
    have h6 : (∑ p ∈ S, 1 / (p : ℝ)) ≤ 40 * (1 + Real.log (1 + Real.log z)) := h3.trans h4
    have h7 : Real.log (1 + Real.log z) = Real.log (1 + L) := by rw [hLdef]
    rw [h7] at h6
    calc (∑ p ∈ S, (p : ℝ) ^ (σ - 1))
        ≤ ∑ p ∈ S, Real.exp (σ * L) * (1 / (p : ℝ)) := h1
      _ = Real.exp (σ * L) * ∑ p ∈ S, 1 / (p : ℝ) := h2
      _ ≤ Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))) :=
          mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
  have hRankin := subset_tail_rankin S hprime (((⌊Q0⌋₊ : ℕ)) : ℝ) hQ0pos σ hσ
  have hEuler := euler_product_le S hprime σ hσ.le
  have hQ0pow : (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))) := by
    rw [Real.rpow_def_of_pos hQ0pos]
    congr 1
    ring
  have hLz : L = Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ) := by
    rw [hLdef, hzdef]
  calc (∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
        (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
        ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      ≤ (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) *
          ∏ p ∈ S, (1 + (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) := hRankin
    _ ≤ (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) *
          Real.exp (7 * ∑ p ∈ S, (p : ℝ) ^ (σ - 1)) :=
        mul_le_mul_of_nonneg_left hEuler (Real.rpow_nonneg hQ0pos.le _)
    _ ≤ (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) *
          Real.exp (7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hQ0pos.le _)
        exact Real.exp_le_exp.mpr (by linarith [hPsum])
    _ = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))) *
          Real.exp (7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) := by
        rw [hQ0pow]
    _ = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))
          + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) :=
        (Real.exp_add _ _).symm
    _ = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))
          + 7 * (Real.exp (σ * Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ))
            * (40 * (1 + Real.log (1 + Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ)))))) := by
        rw [hLz]


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.rpow_le_rpow_of_le_one. -/
private lemma rpow_le_rpow_of_le_one {u a b : ℝ} (hu : 1 ≤ u) (hab : a ≤ b) :
    u ^ a ≤ u ^ b := by
  rcases lt_or_eq_of_le hu with h | h
  · exact (Real.rpow_le_rpow_left_iff h).mpr hab
  · subst h
    simp


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.one_add_log_le. -/
private lemma one_add_log_le {ε u L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 2 ≤ u)
    (hL : 0 < L) (hLb : L ≤ 2 * u ^ (1 - ε)) : 1 + Real.log (1 + L) ≤ Real.log u + 2 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have h1 : u ^ (1 - ε) ≤ u := by
    calc u ^ (1 - ε) ≤ u ^ (1 : ℝ) := rpow_le_rpow_of_le_one hu1 (by linarith)
      _ = u := Real.rpow_one u
  have h2 : 1 + L ≤ (5 / 2) * u := by linarith
  have h3 : Real.log (1 + L) ≤ Real.log ((5 / 2) * u) := Real.log_le_log (by linarith) h2
  have h4 : Real.log ((5 / 2) * u) = Real.log (5 / 2) + Real.log u :=
    Real.log_mul (by norm_num) (ne_of_gt hu0)
  have h5 : Real.log (5 / 2) < 1 := by
    have h6 : Real.log (5 / 2) < Real.log (Real.exp 1) := by
      refine Real.log_lt_log (by norm_num) ?_
      linarith [Real.exp_one_gt_d9]
    rwa [Real.log_exp] at h6
  rw [h4] at h3
  linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.sigma_mul_le_one. -/
private lemma sigma_mul_le_one {A ε u L M : ℝ} (hA : 2 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : 2 ≤ u) (hL : 0 < L) (hM : 0 < M)
    (hLb : L ≤ 2 * u ^ (1 - ε)) (hMb : (ε / 6) * u ≤ M)
    (hthr : 400 * (A + 1000) / ε ^ 2 ≤ u ^ ((3 * ε) / 4)) :
    2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L ≤ M := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hlu : Real.log u + 2 ≤ 6 * u ^ (ε / 4) / ε := logu_add_two_le hu1 hε hε1
  have hA1 : 1 + Real.log (1 + L) ≤ Real.log u + 2 := one_add_log_le hε hε1 hu hL hLb
  -- step 1: `2 T ≤ (2A+1604)(log u + 2)`
  have hT2 : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2)
      ≤ (2 * A + 1604) * (Real.log u + 2) := by
    have h1 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have h2 : (0 : ℝ) ≤ A := by linarith
    have h3 : 800 * (1 + Real.log (1 + L)) ≤ 800 * (Real.log u + 2) :=
      mul_le_mul_of_nonneg_left hA1 (by norm_num)
    nlinarith [h3, h1, h2]
  -- step 2: multiply by `L ≤ 2 u^(1-ε)`
  have hpow1 : (0 : ℝ) < u ^ (ε / 4) := Real.rpow_pos_of_pos hu0 _
  have hpow2 : (0 : ℝ) < u ^ (1 - ε) := Real.rpow_pos_of_pos hu0 _
  have hmid : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L
      ≤ (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) * (2 * u ^ (1 - ε)) := by
    have h1 : (0 : ℝ) ≤ 2 * A + 1604 := by linarith
    have h2 : (0 : ℝ) < 6 * u ^ (ε / 4) / ε := by positivity
    have h3 : (0 : ℝ) < 2 * u ^ (1 - ε) := by positivity
    have h4 : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2)
        ≤ (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) :=
      hT2.trans (mul_le_mul_of_nonneg_left hlu h1)
    have h5 : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L
        ≤ ((2 * A + 1604) * (6 * u ^ (ε / 4) / ε)) * L :=
      mul_le_mul_of_nonneg_right h4 hL.le
    have h6 : ((2 * A + 1604) * (6 * u ^ (ε / 4) / ε)) * L
        ≤ ((2 * A + 1604) * (6 * u ^ (ε / 4) / ε)) * (2 * u ^ (1 - ε)) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    linarith [h5, h6]
  -- step 3: the right hand side is at most `(ε/6) u`
  have hexp : (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) * (2 * u ^ (1 - ε))
      = (12 * (2 * A + 1604) / ε) * (u ^ (ε / 4) * u ^ (1 - ε)) := by
    field_simp
    ring
  have hsplit : u ^ (ε / 4) * u ^ (1 - ε) = u ^ (1 - (3 * ε) / 4) := by
    rw [← Real.rpow_add hu0]
    congr 1
    ring
  have hkey : u ^ (1 - (3 * ε) / 4) * u ^ ((3 * ε) / 4) = u := by
    rw [← Real.rpow_add hu0]
    rw [show 1 - (3 * ε) / 4 + (3 * ε) / 4 = 1 by ring]
    rw [Real.rpow_one]
  have hw : (0 : ℝ) < u ^ ((3 * ε) / 4) := Real.rpow_pos_of_pos hu0 _
  have hcoef : 12 * (2 * A + 1604) / ε ≤ (ε / 6) * u ^ ((3 * ε) / 4) := by
    have h1 : 72 * (2 * A + 1604) / ε ^ 2 ≤ u ^ ((3 * ε) / 4) := by
      have h2 : 72 * (2 * A + 1604) ≤ 400 * (A + 1000) := by nlinarith
      have h3 : (0 : ℝ) < ε ^ 2 := by positivity
      calc 72 * (2 * A + 1604) / ε ^ 2 ≤ 400 * (A + 1000) / ε ^ 2 :=
            div_le_div_of_nonneg_right h2 h3.le
        _ ≤ u ^ ((3 * ε) / 4) := hthr
    have h5 : 12 * (2 * A + 1604) ≤ (ε ^ 2 / 6) * u ^ ((3 * ε) / 4) := by
      have h6 : (0 : ℝ) ≤ ε ^ 2 / 6 := by positivity
      have h7 := mul_le_mul_of_nonneg_left h1 h6
      have h8 : (ε ^ 2 / 6) * (72 * (2 * A + 1604) / ε ^ 2) = 12 * (2 * A + 1604) := by
        field_simp
        ring
      linarith [h7, h8]
    rw [div_le_iff₀ hε]
    nlinarith [h5]
  have hstep : (12 * (2 * A + 1604) / ε) * u ^ (1 - (3 * ε) / 4) ≤ (ε / 6) * u := by
    have h1 : (12 * (2 * A + 1604) / ε) * u ^ (1 - (3 * ε) / 4)
        ≤ ((ε / 6) * u ^ ((3 * ε) / 4)) * u ^ (1 - (3 * ε) / 4) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hu0.le _)
    have h2 : ((ε / 6) * u ^ ((3 * ε) / 4)) * u ^ (1 - (3 * ε) / 4) = (ε / 6) * u := by
      rw [mul_assoc, ← Real.rpow_add hu0,
        show (3 * ε) / 4 + (1 - (3 * ε) / 4) = 1 by ring, Real.rpow_one]
    linarith [h1, h2]
  calc 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L
      ≤ (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) * (2 * u ^ (1 - ε)) := hmid
    _ = (12 * (2 * A + 1604) / ε) * (u ^ (ε / 4) * u ^ (1 - ε)) := hexp
    _ = (12 * (2 * A + 1604) / ε) * u ^ (1 - (3 * ε) / 4) := by rw [hsplit]
    _ ≤ (ε / 6) * u := hstep
    _ ≤ M := hMb


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.exp_majorant_le. -/
private lemma exp_majorant_le {A u L M σ T : ℝ} (hA0 : 0 ≤ A) (hu : 1 ≤ u)
    (hX : 0 ≤ 1 + Real.log (1 + L)) (hσM : σ * M = 2 * T) (hσL : σ * L ≤ 1)
    (hT : T = A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) :
    Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ 1 / u ^ A := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : Real.exp (σ * L) ≤ Real.exp 1 := Real.exp_le_exp.mpr hσL
  have h2 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have h3 : 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
      ≤ 7 * (2.72 * (40 * (1 + Real.log (1 + L)))) := by
    have h4 : Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))
        ≤ 2.72 * (40 * (1 + Real.log (1 + L))) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) (by linarith)
    linarith
  have h5 : -(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
      ≤ -A * Real.log u - 1 := by
    rw [hσM, hT]
    nlinarith [h3, hlogu, hX, hA0]
  have h6 : Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ Real.exp (-A * Real.log u - 1) := Real.exp_le_exp.mpr h5
  have h7 : Real.exp (-A * Real.log u - 1) ≤ Real.exp (-A * Real.log u) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h8 : Real.exp (-A * Real.log u) = u ^ (-A) := by
    rw [Real.rpow_def_of_pos hu0]
    congr 1
    ring
  have h9 : u ^ (-A) = 1 / u ^ A := by
    rw [Real.rpow_neg hu0.le, one_div]
  calc Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ Real.exp (-A * Real.log u - 1) := h6
    _ ≤ Real.exp (-A * Real.log u) := h7
    _ = u ^ (-A) := h8
    _ = 1 / u ^ A := h9


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.interval_card_le. -/
theorem interval_card_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    ((intervalNumbers x y).card : ℝ) ≤ 2 * y := by
  rw [intervalNumbers, Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : x ≤ x + y))]
  have hu := Nat.floor_le (by linarith : 0 ≤ x + y)
  have hl := Nat.sub_one_lt_floor x
  linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.smooth_remainder_pointwise. -/
theorem smooth_remainder_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2 ≤
        C / Real.log x ^ A := by
  classical
  set U : ℝ := max 8 (max ((400 * (A + 1000) / ε ^ 2) ^ (4 / (3 * ε)))
    (max (6 * Real.log 2 / ε) (3 * Real.log 2 / ε + 1))) with hUdef
  have hU8 : 8 ≤ U := le_max_left _ _
  have hUrpow : (400 * (A + 1000) / ε ^ 2) ^ (4 / (3 * ε)) ≤ U :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hUlog : 6 * Real.log 2 / ε ≤ U :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hU8e : 3 * Real.log 2 / ε + 1 ≤ U :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨1, Real.exp U, one_pos, ?_, ?_⟩
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (2 : ℝ) ≤ Real.exp 1 := h2
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  intro x y P Q hx hy hyx hP hPQ hQ n
  have hu : U ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos U) hx
    rwa [Real.log_exp] at h
  have hu1 : 1 ≤ Real.log x := by linarith
  have hu2 : 2 ≤ Real.log x := by linarith
  have hu0 : 0 < Real.log x := by linarith
  have hx1 : (1 : ℝ) < x := by
    have h2 := Real.exp_le_exp.mpr hU8
    have h3 : (1 : ℝ) < Real.exp 8 := by
      have h4 : Real.exp 0 < Real.exp 8 := Real.exp_lt_exp.mpr (by norm_num)
      simpa using h4
    linarith
  by_cases hεle : ε ≤ 1
  · -- main case `ε ≤ 1`
    have h1me : 0 ≤ 1 - ε := by linarith
    have hy1 : 1 ≤ y := by
      have h := Real.one_le_rpow hx1.le hε.le
      linarith
    have hy0 : 0 < y := by linarith
    have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le hP hPQ
    have hQ0pos : 0 < ⌊y ^ (1 / 3 : ℝ)⌋₊ := by
      have h1 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
      exact Nat.le_floor (by exact_mod_cast h1)
    have hQ0R1 : (1 : ℝ) ≤ (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hQ0pos
    have hstep := remainder_le_majorant n P Q (y ^ (1 / 3 : ℝ)) hQpos.le hP hPQ
    by_cases hQsmall : ⌊Q⌋₊ = 0
    · -- `S` is empty, so the remainder vanishes
      have hSempty : (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime = ∅ := by
        rw [hQsmall]
        decide
      have htail0 : (∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => (⌊y ^ (1 / 3 : ℝ)⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2) = 0 := by
        refine Finset.sum_eq_zero (fun t ht => ?_)
        obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
        rw [hSempty, Finset.powerset_empty, Finset.mem_singleton] at ht1
        subst ht1
        exact absurd ht2 (by
          simp only [Finset.prod_empty, Nat.cast_one]
          linarith)
      have hzero : ‖(LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
            - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q)
          - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ = 0 := by
        rw [htail0] at hstep
        exact le_antisymm hstep (norm_nonneg _)
      rw [hzero]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · -- at least one prime below `Q`
      have hQ1 : 1 ≤ Q := by
        have h1 : 1 ≤ ⌊Q⌋₊ := by omega
        exact le_trans (by exact_mod_cast h1) (Nat.floor_le hQpos.le)
      set z : ℕ := ⌊Q⌋₊ + 1 with hzdef
      set L : ℝ := Real.log z with hLdef
      have hLpos : 0 < L := by
        rw [hLdef]
        exact Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hlog1L : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
      set M : ℝ := Real.log (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) with hMdef
      set T : ℝ := A * Real.log (Real.log x) + 800 * (1 + Real.log (1 + L)) + 2 with hTdef
      have hlogu : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hu1
      -- `L ≤ 2 (log x)^(1-ε)`
      have hLb : L ≤ 2 * (Real.log x) ^ (1 - ε) := by
        have h1 : L = Real.log (z : ℝ) := by rw [hLdef]
        rw [h1]
        have hzQ : (z : ℝ) ≤ 2 * Q := by
          rw [hzdef]
          push_cast
          have h8 : ((⌊Q⌋₊ : ℕ) : ℝ) + 1 ≤ Q + 1 := by
            have := Nat.floor_le hQpos.le
            linarith
          nlinarith [hQ1]
        have h2 : Real.log (z : ℝ) ≤ Real.log (2 * Q) := Real.log_le_log (by positivity) hzQ
        have h3 : Real.log (2 * Q) = Real.log 2 + Real.log Q :=
          Real.log_mul (by norm_num) (ne_of_gt hQpos)
        rw [h3] at h2
        have h4 : Real.log Q ≤ Real.log x ^ (1 - ε) := by
          have h := Real.log_le_log hQpos hQ
          rwa [Real.log_exp] at h
        have h6 : (1 : ℝ) ≤ (Real.log x) ^ (1 - ε) := Real.one_le_rpow hu1 h1me
        have h5 : Real.log 2 ≤ (Real.log x) ^ (1 - ε) := by
          linarith [Real.log_two_lt_d9]
        linarith
      -- `M ≥ (ε/6) log x`
      have hMb : (ε / 6) * Real.log x ≤ M := by
        rw [hMdef]
        have h3 : Real.log (y ^ (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log y := Real.log_rpow hy0 _
        have h4 : (y ^ (1 / 3 : ℝ)) / 2 ≤ (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by
          have h5 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
          have h6 : y ^ (1 / 3 : ℝ) - 1 < (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by
            have h7 := Nat.lt_floor_add_one (y ^ (1 / 3 : ℝ))
            linarith
          linarith
        have h8 : Real.log ((y ^ (1 / 3 : ℝ)) / 2)
            ≤ Real.log ((((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ)) :=
          Real.log_le_log (by positivity) h4
        have h9 : Real.log ((y ^ (1 / 3 : ℝ)) / 2)
            = Real.log (y ^ (1 / 3 : ℝ)) - Real.log 2 := Real.log_div (by positivity) (by norm_num)
        rw [h9, h3] at h8
        have h11 : Real.log (x ^ ε) ≤ Real.log y := Real.log_le_log (by positivity) hy
        rw [Real.log_rpow (by linarith : (0 : ℝ) < x)] at h11
        have h13 : Real.log 2 ≤ (ε / 6) * Real.log x := by
          have h14 : 6 * Real.log 2 / ε ≤ Real.log x := le_trans hUlog hu
          rw [div_le_iff₀ hε] at h14
          nlinarith [h14, hε]
        linarith
      have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hMb
      have hthr : 400 * (A + 1000) / ε ^ 2 ≤ (Real.log x) ^ ((3 * ε) / 4) :=
        rpow_threshold (by positivity) hε (hUrpow.trans hu)
      -- `σ L ≤ 1`
      have hTL : 2 * T * L ≤ M := by
        rw [hTdef]
        exact sigma_mul_le_one hA hε hεle hu2 hLpos hMpos hLb hMb hthr
      set σ : ℝ := 2 * T / M with hσdef
      have hσpos : 0 < σ := by rw [hσdef]; positivity
      have hσM : σ * M = 2 * T := by
        rw [hσdef]
        field_simp
      have hσL : σ * L ≤ 1 := by
        rw [hσdef, div_mul_eq_mul_div, div_le_one hMpos]
        linarith [hTL]
      have hy13 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
      have hmaj := majorant_le (Q := Q) (Q0 := y ^ (1 / 3 : ℝ)) hQ1 hy13 hσpos
      rw [← hMdef, ← hzdef, ← hLdef] at hmaj
      have hX0 : (0 : ℝ) ≤ 1 + Real.log (1 + L) := by linarith
      have hexp := exp_majorant_le (A := A) (u := Real.log x) (L := L) (M := M) (σ := σ)
        (T := T) (by linarith) hu1 hX0 hσM hσL hTdef
      have hfinal : ‖(LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
            - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q)
          - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P (y ^ (1 / 3 : ℝ)) Q‖
          ≤ 1 / Real.log x ^ A := hstep.trans (hmaj.trans hexp)
      have hsq : ‖(LeanLab.KumchevLiu2007.Task506aTask129.series2 n P
            - LeanLab.KumchevLiu2007.Task506aTask129b.product2 n Q)
          - LeanLab.KumchevLiu2007.Task506aTask129b.tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2
          ≤ 1 / Real.log x ^ A := by
        have h1 : (1 / Real.log x ^ A) ^ 2 ≤ 1 / Real.log x ^ A := by
          have h2 : (0 : ℝ) < Real.log x := hu0
          have h3 : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos h2 A
          rw [div_pow]
          rw [div_le_div_iff₀ (by positivity) h3]
          have h4 : Real.log x ^ A * 1 ≤ Real.log x ^ A * Real.log x ^ A := by
            have h5 : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hu1 (by linarith)
            nlinarith [h5, h3]
          nlinarith [h4, h3]
        calc _ ≤ (1 / Real.log x ^ A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfinal 2
          _ ≤ 1 / Real.log x ^ A := h1
      exact hsq
  · -- vacuous case: `1 < ε` and `x > 1` are incompatible with `x^ε ≤ y ≤ x`
    exfalso
    push_neg at hεle
    have h2 : x < x ^ ε := by
      simpa using (Real.rpow_lt_rpow_left_iff hx1).mpr hεle
    linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask271a.truncation_from_pointwise. -/
theorem truncation_from_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_remainder_pointwise A ε hA hε
  refine ⟨2 * C, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y, C / Real.log x ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      exact hb x y P Q hx hy hyx hP hPQ hQ n
    _ = ((intervalNumbers x y).card : ℝ) * (C / Real.log x ^ A) := by simp
    _ ≤ (2 * y) * (C / Real.log x ^ A) := by
      exact mul_le_mul_of_nonneg_right (interval_card_le (by linarith) hy1)
        (by positivity)
    _ = (2 * C) * (y / Real.log x ^ A) := by ring


end LeanLab.KumchevLiu2007.Task506aTask271a

namespace LeanLab.KumchevLiu2007.Task506aTask271b

open Real Complex Task506aTask129 Task506aTask129b
open scoped BigOperators

                                                                       
                                                    

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask271b.norm_sum_sq_split. -/
theorem norm_sum_sq_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      (∑ i ∈ s, ‖f i‖ ^ 2) +
      ∑ i ∈ s, ∑ j ∈ s.erase i, (f i * (starRingEnd ℂ) (f j)).re := by
  classical
  have full : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * (starRingEnd ℂ) (f j)).re := by
    rw [Complex.sq_norm]
    have h := congrArg Complex.re (Complex.mul_conj (∑ i ∈ s, f i))
    simp only [Complex.ofReal_re] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
  rw [full, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add _ _ hi]
  have h : (f i * (starRingEnd ℂ) (f i)).re = ‖f i‖ ^ 2 := by
    simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using
      congrArg Complex.re (Complex.mul_conj (f i))
  rw [h, add_comm]


/-- Page 13 through page 15, copied proof helper from Task506aTask271b.smoothWeight_norm_le_one. -/
theorem smoothWeight_norm_le_one (q : ℕ) (Q : ℝ) :
    ‖(smoothWeight q Q : ℂ)‖ ≤ 1 := by
  classical
  unfold smoothWeight
  split <;> simp


/-- Page 13 through page 15, copied proof helper from Task506aTask271b.sum_inv_sq_Ioc_le. -/
theorem sum_inv_sq_Ioc_le (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, (1 / (q : ℝ) ^ 2)) ≤
      1 / (a : ℝ) - 1 / (b : ℝ) := by
  induction b generalizing a with
  | zero =>
      omega
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · simp only [Finset.Ioc_eq_empty_of_le (Nat.le_refl _), Finset.sum_empty]
        norm_num
      · have hab' : a ≤ b := by omega
        have hnot : b + 1 ∉ Finset.Ioc a b := by
          simp only [Finset.mem_Ioc]
          omega
        have heq : insert (b + 1) (Finset.Ioc a b) = Finset.Ioc a (b + 1) := by
          simpa using Finset.insert_Ioc_right_eq_Ioc_succ hab'
        rw [← heq, Finset.sum_insert hnot]
        have hi := ih a ha hab'
        push_cast at hi ⊢
        have hterm : 1 / (b + 1 : ℝ) ^ 2 ≤ 1 / (b : ℝ) - 1 / (b + 1 : ℝ) := by
          have hb_nat : 1 ≤ b := by omega
          have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb_nat
          field_simp
          nlinarith
        calc
          1 / (b + 1 : ℝ) ^ 2 + (∑ q ∈ Finset.Ioc a b, (1 / (q : ℝ) ^ 2))
              ≤ 1 / (b + 1 : ℝ) ^ 2 + (1 / (a : ℝ) - 1 / (b : ℝ)) := by
                simpa only [add_comm] using
                  add_le_add_right hi (1 / (b + 1 : ℝ) ^ 2)
          _ ≤ (1 / (b : ℝ) - 1 / (b + 1 : ℝ)) + (1 / (a : ℝ) - 1 / (b : ℝ)) := by
                gcongr
          _ = 1 / (a : ℝ) - 1 / (b + 1 : ℝ) := by ring


/-- Page 13 through page 15, copied proof helper from Task506aTask271b.quarter_power_absorption. -/
theorem quarter_power_absorption (A ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → x ^ ε ≤ y →
      y ^ (3 / 4 : ℝ) ≤ y / Real.log x ^ A := by
  obtain ⟨x0, hb⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop A (show 0 < ε / 4 by linarith)).bound zero_lt_one)
  refine ⟨max x0 2, le_max_right _ _, ?_⟩
  intro x y hx hy
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hxp : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hyp : 0 < y := (Real.rpow_pos_of_pos hxp ε).trans_le hy
  have hl : Real.log x ^ A ≤ x ^ (ε / 4) := by
    have h := hb x ((le_max_left _ _).trans hx)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog A),
      abs_of_pos (Real.rpow_pos_of_pos hxp (ε / 4)), one_mul] using h
  have hp : x ^ (ε / 4) ≤ y ^ (1 / 4 : ℝ) := by
    calc
      _ = (x ^ ε) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hxp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hxp.le _) hy (by norm_num)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog A)]
  calc
    _ ≤ y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (hl.trans hp) (Real.rpow_nonneg hyp.le _)
    _ = y := by rw [← Real.rpow_add hyp]; norm_num


end LeanLab.KumchevLiu2007.Task506aTask271b

namespace LeanLab.KumchevLiu2007.Task506aTask292a

open Real Complex Task506aTask129b
open scoped BigOperators

                                                                        

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask292a.localMajorant. -/
noncomputable def localMajorant (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.ee_add_292a. -/
private lemma ee_add_292a (s t : ℝ) : U1534.ee s * U1534.ee t = U1534.ee (s + t) := by
  unfold U1534.ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.A2_pair_form. -/
private lemma A2_pair_form (n q : ℕ) (hq : 0 < q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) := by
  classical
  set S : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q) with hS
  have hstep : ∀ a ∈ S,
      U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ)))
        = ∑ x ∈ S, U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) := by
    intro a ha
    unfold U1534.gaussS
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have harg : ((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ) + (-(((a * n : ℕ) : ℝ) / (q : ℝ)))
        = ((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ) := by
      push_cast
      ring
    rw [← harg, ee_add_292a]
  calc (∑ a ∈ S, U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ a ∈ S, ∑ x ∈ S, U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) :=
        Finset.sum_congr rfl hstep
    _ = ∑ x ∈ S, ∑ a ∈ S, U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) :=
        Finset.sum_comm


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.ee_eq_stdAddChar_292a. -/
private lemma ee_eq_stdAddChar_292a (q : ℕ) [NeZero q] (j : ℤ) :
    U1534.ee ((j : ℝ) / (q : ℝ)) = ZMod.stdAddChar (N := q) (j : ZMod q) := by
  rw [ZMod.stdAddChar_coe]
  unfold U1534.ee
  congr 1
  push_cast
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.sum_units_eq_sum_zmod_units. -/
private lemma sum_units_eq_sum_zmod_units (q : ℕ) [NeZero q] (g : ℕ → ℂ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), g a)
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y), g y.val := by
  classical
  refine Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ha ⊢
    rw [ZMod.isUnit_iff_coprime]
    exact ha.2
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    have h := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt ha1.1, ZMod.val_natCast_of_lt ha2.1] at h
  · intro y hy
    refine ⟨y.val, ?_, ZMod.natCast_zmod_val y⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt y, ?_⟩
    have hy' : IsUnit y := (Finset.mem_filter.mp hy).2
    rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime] at hy'
    exact hy'
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.val_natCast_of_lt ha.1]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.stdAddChar_crt_split. -/
private lemma stdAddChar_crt_split (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (k : ℤ) :
    ZMod.stdAddChar (N := q1 * q2) (k : ZMod (q1 * q2))
      = ZMod.stdAddChar (N := q1) ((k : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
        * ZMod.stdAddChar (N := q2) ((k : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2)) := by
  rw [ZMod.stdAddChar_coe]
  have hm1 : ((k : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
      = (((k * Nat.gcdB q1 q2 : ℤ)) : ZMod q1) := by push_cast; ring
  have hm2 : ((k : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2))
      = (((k * Nat.gcdA q1 q2 : ℤ)) : ZMod q2) := by push_cast; ring
  rw [hm1, hm2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hbez : ((q1 : ℤ)) * Nat.gcdA q1 q2 + ((q2 : ℤ)) * Nat.gcdB q1 q2 = 1 := by
    have h := Nat.gcd_eq_gcd_ab q1 q2
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have hbezC : ((q1 : ℕ) : ℂ) * ((Nat.gcdA q1 q2 : ℤ) : ℂ)
      + ((q2 : ℕ) : ℂ) * ((Nat.gcdB q1 q2 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hbez
  have hq1n : (((q1 : ℕ)) : ℂ) ≠ 0 := by
    have h : 0 < q1 := NeZero.pos q1
    exact_mod_cast h.ne'
  have hq2n : (((q2 : ℕ)) : ℂ) ≠ 0 := by
    have h : 0 < q2 := NeZero.pos q2
    exact_mod_cast h.ne'
  push_cast
  field_simp
  linear_combination (-(↑k : ℂ)) * hbezC


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.stdAddChar_crt_split'. -/
private lemma stdAddChar_crt_split' (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (w : ZMod (q1 * q2)) :
    ZMod.stdAddChar (N := q1 * q2) w
      = ZMod.stdAddChar (N := q1) ((ZMod.cast w : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
        * ZMod.stdAddChar (N := q2) ((ZMod.cast w : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2)) := by
  have hwz : (((w.val : ℤ)) : ZMod (q1 * q2)) = w := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val w
  rw [← hwz, stdAddChar_crt_split q1 q2 hcop (w.val : ℤ)]
  have e1 : (ZMod.cast (((w.val : ℤ)) : ZMod (q1 * q2)) : ZMod q1)
      = (((w.val : ℤ)) : ZMod q1) := by
    rw [show (((w.val : ℤ)) : ZMod (q1 * q2)) = ((w.val : ℕ) : ZMod (q1 * q2)) by rw [Int.cast_natCast]]
    rw [ZMod.cast_natCast (R := ZMod q1) (dvd_mul_right q1 q2) w.val]
    exact (Int.cast_natCast w.val).symm
  have e2 : (ZMod.cast (((w.val : ℤ)) : ZMod (q1 * q2)) : ZMod q2)
      = (((w.val : ℤ)) : ZMod q2) := by
    rw [show (((w.val : ℤ)) : ZMod (q1 * q2)) = ((w.val : ℕ) : ZMod (q1 * q2)) by rw [Int.cast_natCast]]
    rw [ZMod.cast_natCast (R := ZMod q2) (dvd_mul_left q2 q1) w.val]
    exact (Int.cast_natCast w.val).symm
  rw [e1, e2]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.pair_form_zmod. -/
private lemma pair_form_zmod (n q : ℕ) [NeZero q] :
    (∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)))
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q) (z * (y * y - (n : ZMod q))) := by
  classical
  rw [sum_units_eq_sum_zmod_units q
    (fun x => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)))]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [sum_units_eq_sum_zmod_units q
    (fun a => U1534.ee (((((a : ℤ) * ((y.val : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)))]
  refine Finset.sum_congr rfl ?_
  intro z _
  have h := ee_eq_stdAddChar_292a q (((z.val : ℤ) * ((y.val : ℤ) ^ 2 - (n : ℤ))))
  rw [h]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val z, ZMod.natCast_zmod_val y]
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.sum_units_mul_shift. -/
private lemma sum_units_mul_shift (q : ℕ) [NeZero q] (u : ZMod q) (hu : IsUnit u)
    (G : ZMod q → ℂ) :
    (∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z), G (z * u))
      = ∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z), G z := by
  classical
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvu : v * u = 1 := by rw [mul_comm]; exact hv
  have hvU : IsUnit v := isUnit_iff_exists.mpr ⟨u, hvu, hv⟩
  refine Finset.sum_bij (fun (z : ZMod q) _ => z * u) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.mul hu
  · intro z1 hz1 z2 hz2 heq
    have h : z1 * u * v = z2 * u * v := by rw [heq]
    rwa [mul_assoc, mul_assoc, hv, mul_one, mul_one] at h
  · intro z hz
    refine ⟨z * v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.mul hvU
    · rw [mul_assoc, hvu, mul_one]
  · intro z hz
    rfl


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.gcdB_isUnit. -/
private lemma gcdB_isUnit (q1 q2 : ℕ) [NeZero q1] (hcop : q1.Coprime q2) :
    IsUnit (((Nat.gcdB q1 q2 : ℤ)) : ZMod q1) := by
  have hbez : ((q1 : ℤ)) * Nat.gcdA q1 q2 + ((q2 : ℤ)) * Nat.gcdB q1 q2 = 1 := by
    have h := Nat.gcd_eq_gcd_ab q1 q2
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have h0 : (((q1 : ℤ)) : ZMod q1) = 0 := by push_cast; exact ZMod.natCast_self q1
  have hcast : ((q2 : ℤ) : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q1)) hbez
    push_cast at h
    simpa [h0] using h
  exact isUnit_iff_exists.mpr ⟨((q2 : ℤ) : ZMod q1), by rwa [mul_comm], hcast⟩


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.gcdA_isUnit. -/
private lemma gcdA_isUnit (q1 q2 : ℕ) [NeZero q2] (hcop : q1.Coprime q2) :
    IsUnit (((Nat.gcdA q1 q2 : ℤ)) : ZMod q2) := by
  have hbez : ((q1 : ℤ)) * Nat.gcdA q1 q2 + ((q2 : ℤ)) * Nat.gcdB q1 q2 = 1 := by
    have h := Nat.gcd_eq_gcd_ab q1 q2
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have h0 : (((q2 : ℤ)) : ZMod q2) = 0 := by push_cast; exact ZMod.natCast_self q2
  have hcast : ((q1 : ℤ) : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q2)) hbez
    push_cast at h
    simpa [h0] using h
  exact isUnit_iff_exists.mpr ⟨((q1 : ℤ) : ZMod q2), by rwa [mul_comm], hcast⟩


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.sum_units_crt_transport. -/
private lemma sum_units_crt_transport (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (G : ZMod (q1 * q2) → ZMod (q1 * q2) → ℂ) :
    (∑ y ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun y => IsUnit y),
        ∑ z ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun z => IsUnit z), G y z)
      = ∑ p ∈ (Finset.univ : Finset (ZMod q1 × ZMod q2)).filter (fun p => IsUnit p),
          ∑ r ∈ (Finset.univ : Finset (ZMod q1 × ZMod q2)).filter (fun r => IsUnit r),
            G ((ZMod.chineseRemainder hcop).symm p) ((ZMod.chineseRemainder hcop).symm r) := by
  classical
  set e := ZMod.chineseRemainder hcop with he
  have hmem : ∀ p : ZMod q1 × ZMod q2, IsUnit p → IsUnit (e.symm p) := fun p hp =>
    IsUnit.map (e.symm : ZMod q1 × ZMod q2 →+* ZMod (q1 * q2)) hp
  have hmem' : ∀ p : ZMod (q1 * q2), IsUnit p → IsUnit (e p) := fun p hp =>
    IsUnit.map (e : ZMod (q1 * q2) →+* ZMod q1 × ZMod q2) hp
  have hinner : ∀ y : ZMod (q1 * q2),
      (∑ z ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun z => IsUnit z), G y z)
        = ∑ r ∈ (Finset.univ : Finset (ZMod q1 × ZMod q2)).filter (fun r => IsUnit r),
            G y (e.symm r) := by
    intro y
    refine Finset.sum_bij (fun (z : ZMod (q1 * q2)) _ => e z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hmem' z hz
    · intro z1 hz1 z2 hz2 heq
      exact e.injective heq
    · intro r hr
      refine ⟨e.symm r, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hmem r hr
    · intro z hz
      simp only [RingEquiv.symm_apply_apply]
  simp only [hinner]
  refine Finset.sum_bij (fun (y : ZMod (q1 * q2)) _ => e y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hmem' y hy
  · intro y1 hy1 y2 hy2 heq
    exact e.injective heq
  · intro p hp
    refine ⟨e.symm p, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hmem p hp
  · intro y hy
    simp only [RingEquiv.symm_apply_apply]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.cast_crt_symm_fst. -/
private lemma cast_crt_symm_fst (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (p : ZMod q1 × ZMod q2) :
    (ZMod.cast ((ZMod.chineseRemainder hcop).symm p) : ZMod q1) = p.1 := by
  have h : ZMod.chineseRemainder hcop ((ZMod.chineseRemainder hcop).symm p) = p :=
    RingEquiv.apply_symm_apply _ _
  have h1 := congrArg Prod.fst h
  rw [← h1]
  simp [ZMod.chineseRemainder, ZMod.castHom_apply]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.cast_crt_symm_snd. -/
private lemma cast_crt_symm_snd (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (p : ZMod q1 × ZMod q2) :
    (ZMod.cast ((ZMod.chineseRemainder hcop).symm p) : ZMod q2) = p.2 := by
  have h : ZMod.chineseRemainder hcop ((ZMod.chineseRemainder hcop).symm p) = p :=
    RingEquiv.apply_symm_apply _ _
  have h1 := congrArg Prod.snd h
  rw [← h1]
  simp [ZMod.chineseRemainder, ZMod.castHom_apply]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.quadruple_sum_mul. -/
private lemma quadruple_sum_mul {α β : Type*} (F1 : Finset α) (F2 : Finset β)
    (A : α → α → ℂ) (B : β → β → ℂ) :
    (∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2, A p1 r1 * B p2 r2)
      = (∑ p1 ∈ F1, ∑ r1 ∈ F1, A p1 r1) * (∑ p2 ∈ F2, ∑ r2 ∈ F2, B p2 r2) := by
  rw [Finset.sum_mul_sum F1 F2 (fun p1 => ∑ r1 ∈ F1, A p1 r1)
    (fun p2 => ∑ r2 ∈ F2, B p2 r2)]
  refine Finset.sum_congr rfl ?_
  intro p1 _
  refine Finset.sum_congr rfl ?_
  intro p2 _
  rw [Finset.sum_mul_sum]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.V_term_factor. -/
private lemma V_term_factor (n q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (p1 : ZMod q1) (p2 : ZMod q2) (r1 : ZMod q1) (r2 : ZMod q2) :
    ZMod.stdAddChar (N := q1 * q2)
        ((ZMod.chineseRemainder hcop).symm (r1, r2)
          * ((ZMod.chineseRemainder hcop).symm (p1, p2)
              * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2))))
      = ZMod.stdAddChar (N := q1)
          (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1))))
        * ZMod.stdAddChar (N := q2)
          (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))) := by
  have hd1 : q1 ∣ q1 * q2 := dvd_mul_right q1 q2
  have hd2 : q2 ∣ q1 * q2 := dvd_mul_left q2 q1
  have hn1 : (ZMod.cast ((n : ℕ) : ZMod (q1 * q2)) : ZMod q1) = ((n : ℕ) : ZMod q1) :=
    ZMod.cast_natCast (R := ZMod q1) hd1 n
  have hn2 : (ZMod.cast ((n : ℕ) : ZMod (q1 * q2)) : ZMod q2) = ((n : ℕ) : ZMod q2) :=
    ZMod.cast_natCast (R := ZMod q2) hd2 n
  have hcw1 : (ZMod.cast ((ZMod.chineseRemainder hcop).symm (r1, r2)
      * ((ZMod.chineseRemainder hcop).symm (p1, p2)
          * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))) : ZMod q1)
      = r1 * (p1 * p1 - (n : ZMod q1)) := by
    rw [ZMod.cast_mul hd1, ZMod.cast_sub hd1, ZMod.cast_mul hd1, hn1]
    simp only [cast_crt_symm_fst, Prod.fst, Prod.snd]
  have hcw2 : (ZMod.cast ((ZMod.chineseRemainder hcop).symm (r1, r2)
      * ((ZMod.chineseRemainder hcop).symm (p1, p2)
          * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))) : ZMod q2)
      = r2 * (p2 * p2 - (n : ZMod q2)) := by
    rw [ZMod.cast_mul hd2, ZMod.cast_sub hd2, ZMod.cast_mul hd2, hn2]
    simp only [cast_crt_symm_snd, Prod.fst, Prod.snd]
  rw [stdAddChar_crt_split' q1 q2 hcop
    ((ZMod.chineseRemainder hcop).symm (r1, r2)
      * ((ZMod.chineseRemainder hcop).symm (p1, p2)
          * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))), hcw1, hcw2]
  rw [mul_comm (r1 * (p1 * p1 - (n : ZMod q1))) (((Nat.gcdB q1 q2 : ℤ) : ZMod q1)),
    mul_comm (r2 * (p2 * p2 - (n : ZMod q2))) (((Nat.gcdA q1 q2 : ℤ) : ZMod q2))]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.V_coprime_mul. -/
private lemma V_coprime_mul (n q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) :
    (∑ y ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun y => IsUnit y),
        ∑ z ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun z => IsUnit z),
          ZMod.stdAddChar (N := q1 * q2) (z * (y * y - (n : ZMod (q1 * q2)))))
      = (∑ y ∈ (Finset.univ : Finset (ZMod q1)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q1)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q1) (z * (y * y - (n : ZMod q1))))
        * (∑ y ∈ (Finset.univ : Finset (ZMod q2)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q2)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q2) (z * (y * y - (n : ZMod q2)))) := by
  classical
  set F1 : Finset (ZMod q1) := Finset.univ.filter (fun a => IsUnit a) with hF1
  set F2 : Finset (ZMod q2) := Finset.univ.filter (fun a => IsUnit a) with hF2
  have hF' : (Finset.univ.filter (fun p : ZMod q1 × ZMod q2 => IsUnit p)) = F1 ×ˢ F2 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, hF1, hF2]
    exact Prod.isUnit_iff
  -- strip the Bezout twist from each of the two right-hand factors
  have hkey1 : (∑ p1 ∈ F1, ∑ r1 ∈ F1,
        ZMod.stdAddChar (N := q1) (r1 * (p1 * p1 - (n : ZMod q1))))
      = ∑ p1 ∈ F1, ∑ r1 ∈ F1, ZMod.stdAddChar (N := q1)
          (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1)))) := by
    refine Finset.sum_congr rfl (fun p1 _ => ?_)
    have h := sum_units_mul_shift q1 (((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
      (gcdB_isUnit q1 q2 hcop)
      (fun z => ZMod.stdAddChar (N := q1) (z * (p1 * p1 - (n : ZMod q1))))
    rw [← h]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    ring
  have hkey2 : (∑ p2 ∈ F2, ∑ r2 ∈ F2,
        ZMod.stdAddChar (N := q2) (r2 * (p2 * p2 - (n : ZMod q2))))
      = ∑ p2 ∈ F2, ∑ r2 ∈ F2, ZMod.stdAddChar (N := q2)
          (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))) := by
    refine Finset.sum_congr rfl (fun p2 _ => ?_)
    have h := sum_units_mul_shift q2 (((Nat.gcdA q1 q2 : ℤ) : ZMod q2))
      (gcdA_isUnit q1 q2 hcop)
      (fun z => ZMod.stdAddChar (N := q2) (z * (p2 * p2 - (n : ZMod q2))))
    rw [← h]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    ring
  rw [hkey1, hkey2]
  clear hkey1 hkey2
  rw [sum_units_crt_transport q1 q2 hcop
    (fun y z => ZMod.stdAddChar (N := q1 * q2) (z * (y * y - (n : ZMod (q1 * q2)))))]
  rw [hF']
  have hmix : (∑ p ∈ F1 ×ˢ F2, ∑ r ∈ F1 ×ˢ F2,
        ZMod.stdAddChar (N := q1 * q2)
          ((ZMod.chineseRemainder hcop).symm r
            * ((ZMod.chineseRemainder hcop).symm p
                * (ZMod.chineseRemainder hcop).symm p - (n : ZMod (q1 * q2)))))
      = ∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2,
          ZMod.stdAddChar (N := q1 * q2)
            ((ZMod.chineseRemainder hcop).symm (r1, r2)
              * ((ZMod.chineseRemainder hcop).symm (p1, p2)
                  * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun p2 _ => ?_))
    rw [Finset.sum_product]
  rw [hmix]
  clear hmix
  have hstep : (∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2,
        ZMod.stdAddChar (N := q1 * q2)
          ((ZMod.chineseRemainder hcop).symm (r1, r2)
            * ((ZMod.chineseRemainder hcop).symm (p1, p2)
                * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))))
      = ∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2,
          ZMod.stdAddChar (N := q1)
              (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1))))
            * ZMod.stdAddChar (N := q2)
              (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))) := by
    refine Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun p2 _ =>
      Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun r2 _ => ?_))))
    exact V_term_factor n q1 q2 hcop p1 p2 r1 r2
  rw [hstep, quadruple_sum_mul F1 F2
    (fun p1 r1 => ZMod.stdAddChar (N := q1)
      (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1)))))
    (fun p2 r2 => ZMod.stdAddChar (N := q2)
      (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))))]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.A2_sum_eq_V. -/
private lemma A2_sum_eq_V (n q : ℕ) (hq : 0 < q) [NeZero q] :
    (∑ p ∈ (Finset.range q).filter (fun p => Nat.Coprime p q),
        U1534.gaussS q p * U1534.ee (-(((p * n : ℕ) : ℝ)) / (q : ℝ)))
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q) (z * (y * y - (n : ZMod q))) := by
  simp only [neg_div]
  exact (A2_pair_form n q hq).trans (pair_form_zmod n q)


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.A2_zero_292a. -/
private lemma A2_zero_292a (n : ℕ) : U1534.A2 n 0 = 0 := by
  simp [U1534.A2]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.A2_coprime_mul. -/
theorem A2_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    U1534.A2 n (a * b) = U1534.A2 n a * U1534.A2 n b := by

  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb
    rw [zero_mul, A2_zero_292a, U1534.A2_one, mul_one]
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · have ha : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha
    rw [mul_zero, A2_zero_292a, U1534.A2_one, one_mul]
  by_cases ha1 : a = 1
  · subst ha1
    rw [one_mul, U1534.A2_one, one_mul]
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one, U1534.A2_one, mul_one]
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp hapos⟩
  haveI : NeZero b := ⟨Nat.pos_iff_ne_zero.mp hbpos⟩
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)
  haveI : NeZero (a * b) := ⟨hab0⟩
  have hmulpos : 0 < a * b := Nat.pos_of_ne_zero hab0
  rw [U1534.A2, U1534.A2, U1534.A2, A2_sum_eq_V n (a * b) hmulpos,
    A2_sum_eq_V n a hapos, A2_sum_eq_V n b hbpos,
    V_coprime_mul n a b hab,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab,
    Nat.totient_mul hab]
  push_cast
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.prime_coefficient_bound. -/
theorem prime_coefficient_bound (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖U1534.A2 n p‖ ≤ 1 / (p : ℝ) + 6 / (p : ℝ) ^ 2 := by
  exact A2_prime_norm_le_inv_add p n


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.squarefree_factorization. -/
theorem squarefree_factorization (n q : ℕ) (hq : Squarefree q) :
    U1534.A2 n q = ∏ p ∈ q.primeFactors, U1534.A2 n p := by
  let f : ArithmeticFunction ℂ := ⟨U1534.A2 n, by simp [U1534.A2]⟩
  have hf : f.IsMultiplicative :=
    ⟨U1534.A2_one n, fun {a b} hab => A2_coprime_mul n a b hab⟩
  exact (hf.prod_primeFactors hq).symm


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.coefficient_product_bound. -/
theorem coefficient_product_bound (n q : ℕ) (hq : 0 < q) :
    ‖U1534.A2 n q‖ ≤ localMajorant q / (q : ℝ) := by
  classical
  by_cases hs : Squarefree q
  · rw [squarefree_factorization n q hs, norm_prod]
    calc
      _ ≤ ∏ p ∈ q.primeFactors, ((1 + 6 / (p : ℝ)) / (p : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro p hp; exact norm_nonneg _
        · intro p hp
          haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
          convert prime_coefficient_bound p n using 1 <;> field_simp [hp0] <;> ring
      _ = localMajorant q / (q : ℝ) := by
        rw [Finset.prod_div_distrib]
        have he : (∏ p ∈ q.primeFactors, (p : ℝ)) = q := by
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.prod_primeFactors_of_squarefree hs
        rw [he]
        rfl
  · rw [A2_eq_zero_of_not_squarefree n q hs, norm_zero]
    exact div_nonneg (Finset.prod_nonneg (fun p _ => by positivity)) (Nat.cast_nonneg q)


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.pi_upper. -/
private lemma pi_upper (p : ℕ) (hp : p.Prime) :
    (p.primeCounting : ℝ) ≤ 6 * (p:ℝ) / Real.log p := by
  have hp2 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hL : 0 < Real.log (p:ℝ) := Real.log_pos hp2
  have h := Chebyshev.pi_le_log4_mul_div (x := (p:ℝ)) hp2
  rw [Nat.floor_natCast, Real.log_sqrt hp0.le] at h
  have hsp : 0 < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp0
  have hlogsp : Real.log (Real.sqrt (p:ℝ)) ≤ Real.sqrt (p:ℝ) := by
    have := Real.log_le_sub_one_of_pos hsp
    linarith
  have hlog2 : Real.log (p:ℝ) ≤ 2 * Real.sqrt (p:ℝ) := by
    have hh : Real.log (p:ℝ) = 2 * Real.log (Real.sqrt (p:ℝ)) := by
      rw [Real.log_sqrt hp0.le]; ring
    rw [hh]; linarith
  have hsq : Real.sqrt (p:ℝ) ≤ 2 * (p:ℝ) / Real.log (p:ℝ) := by
    rw [le_div_iff₀ hL]
    nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg (p:ℝ)]
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4:ℝ) = 2^2 := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_lt_d9]
  have hkey : Real.log 4 * (p:ℝ) / (Real.log (p:ℝ) / 2)
      = 2 * Real.log 4 * ((p:ℝ) / Real.log (p:ℝ)) := by
    field_simp
  rw [hkey] at h
  have hnn : (0:ℝ) ≤ (p:ℝ) / Real.log (p:ℝ) := by positivity
  have hstep : 2 * Real.log 4 * ((p:ℝ) / Real.log (p:ℝ)) ≤ 4 * ((p:ℝ) / Real.log (p:ℝ)) := by
    nlinarith
  set t : ℝ := (p:ℝ) / Real.log (p:ℝ) with ht
  have ht0 : 0 ≤ t := hnn
  have hsq' : Real.sqrt (p:ℝ) ≤ 2 * t := by
    rw [ht, ← mul_div_assoc]
    exact hsq
  have hstep' : 2 * Real.log 4 * t ≤ 4 * t := hstep
  have h' : (p.primeCounting : ℝ) ≤ 2 * Real.log 4 * t + Real.sqrt (p:ℝ) := h
  calc (p.primeCounting : ℝ) ≤ 2 * Real.log 4 * t + Real.sqrt (p:ℝ) := h'
    _ ≤ 4 * t + 2 * t := by linarith [hstep', hsq']
    _ = 6 * t := by ring
    _ = 6 * (p:ℝ) / Real.log p := by rw [ht]; ring


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.pi_log_le. -/
private lemma pi_log_le (p : ℕ) (hp : p.Prime) :
    (p.primeCounting : ℝ) * Real.log ((p.primeCounting : ℝ) + 1) ≤ 12 * (p:ℝ) := by
  have hp2n : 2 ≤ p := hp.two_le
  have hp2 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hL : 0 < Real.log (p:ℝ) := Real.log_pos hp2
  have h1 : (p.primeCounting : ℝ) ≤ 6 * (p:ℝ) / Real.log p := pi_upper p hp
  have hpi1 : 1 ≤ p.primeCounting := by
    have hne : p.primeCounting ≠ 0 := by
      intro h
      have hle := (Nat.primeCounting_eq_zero_iff).mp h
      omega
    omega
  have hnn : (0:ℝ) ≤ (p.primeCounting : ℝ) := by positivity
  have hcard : p.primeCounting ≤ p + 1 := by
    have hsub : Nat.primesLE p ⊆ Finset.range (p+1) := by
      intro x hx
      rw [Nat.mem_primesLE] at hx
      simp only [Finset.mem_range]
      omega
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hp2r : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2n
  have hsq : (p.primeCounting : ℝ) + 1 ≤ (p:ℝ)^2 := by
    have hc : (p.primeCounting : ℝ) ≤ (p:ℝ) + 1 := by exact_mod_cast hcard
    nlinarith
  have hlog0 : 0 < (p.primeCounting : ℝ) + 1 := by linarith
  have hlog : Real.log ((p.primeCounting : ℝ) + 1) ≤ 2 * Real.log (p:ℝ) := by
    have h := Real.log_le_log hlog0 hsq
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlog0' : 0 ≤ Real.log ((p.primeCounting : ℝ) + 1) := Real.log_nonneg (by linarith)
  calc (p.primeCounting : ℝ) * Real.log ((p.primeCounting : ℝ) + 1)
      ≤ (6 * (p:ℝ) / Real.log p) * (2 * Real.log (p:ℝ)) := by
        apply mul_le_mul h1 hlog hlog0' (by positivity)
    _ = 12 * (p:ℝ) := by
        field_simp
        ring


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.sum_inv_prime_le. -/
private lemma sum_inv_prime_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, 1/(p:ℝ)) ≤
      12 * ∑ i ∈ Finset.range (S.card + 1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hS a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hnotmem : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
    have ihs := ih hs
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem hnotmem
    rw [Finset.sum_insert hnotmem]
    have hrange : (insert a s).card + 1 = (s.card + 1) + 1 := by rw [hcard]
    rw [hrange, Finset.sum_range_succ]
    have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha.pos
    have hkpos : (0:ℝ) < ((s.card+1 : ℕ):ℝ) := by
      have : 0 < s.card + 1 := Nat.succ_pos _
      exact_mod_cast this
    have hX0 : (0:ℝ) < ((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1) := by
      apply mul_pos hkpos
      apply Real.log_pos
      have : (1:ℝ) < ((s.card+1 : ℕ):ℝ) + 1 := by push_cast; linarith
      linarith
    have hsub : insert a s ⊆ Nat.primesLE a := by
      intro x hx
      rw [Nat.mem_primesLE]
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact ⟨le_rfl, ha⟩
      · exact ⟨le_of_lt (hlt x hxs), hs x hxs⟩
    have hcardle : s.card + 1 ≤ a.primeCounting := by
      rw [← hcard]
      calc (insert a s).card ≤ (Nat.primesLE a).card := Finset.card_le_card hsub
        _ = a.primeCounting := Nat.primesLE_card_eq_primeCounting a
    have hb1 : ((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1) ≤ 12*(a:ℝ) := by
      have hk : ((s.card+1 : ℕ):ℝ) ≤ (a.primeCounting:ℝ) := by exact_mod_cast hcardle
      have hlogle : Real.log (((s.card+1 : ℕ):ℝ)+1) ≤ Real.log ((a.primeCounting:ℝ)+1) := by
        apply Real.log_le_log
        · have : (0:ℝ) < ((s.card+1:ℕ):ℝ) + 1 := by push_cast; linarith
          linarith
        · linarith
      have hlg0 : 0 ≤ Real.log (((s.card+1 : ℕ):ℝ)+1) := Real.log_nonneg (by push_cast; linarith)
      calc ((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1)
          ≤ (a.primeCounting:ℝ) * Real.log ((a.primeCounting:ℝ)+1) := by
            apply mul_le_mul hk hlogle hlg0 (by positivity)
        _ ≤ 12*(a:ℝ) := pi_log_le a ha
    have hstep : 1/(a:ℝ) ≤ 12 * (1/(((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1))) := by
      rw [mul_one_div, div_le_div_iff₀ ha0 hX0]
      have hb1' : 1 * (((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1)) ≤ 12 * (a:ℝ) := by
        linarith
      exact hb1'
    nlinarith [ihs, hstep]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.log_sub_log_ge. -/
private lemma log_sub_log_ge (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : y ≤ x) :
    (x - y)/x ≤ Real.log x - Real.log y := by
  have hpos : 0 < y/x := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div hy.ne' hx.ne'] at h
  have h2 : y/x - 1 = (y - x)/x := by field_simp
  rw [h2] at h
  have h3 : 1 - y/x = (x - y)/x := by field_simp
  linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.inv_log_step. -/
private lemma inv_log_step (j : ℕ) (hj : 2 ≤ j) :
    1/(((j+1:ℕ):ℝ) * Real.log (((j+1:ℕ):ℝ))) ≤
      Real.log (Real.log (((j+1:ℕ):ℝ))) - Real.log (Real.log ((j:ℝ))) := by
  have hj2 : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) < (j:ℝ) := by linarith
  have hj10 : (0:ℝ) < (j:ℝ) + 1 := by linarith
  have hbj : 0 < Real.log (j:ℝ) := Real.log_pos (by linarith)
  have haj : 0 < Real.log ((j:ℝ)+1) := Real.log_pos (by linarith)
  push_cast
  have hb0 : (0:ℝ) < Real.log (j:ℝ) := hbj
  have step1 : 1/((j:ℝ)+1) ≤ Real.log ((j:ℝ)+1) - Real.log (j:ℝ) := by
    have h := log_sub_log_ge ((j:ℝ)+1) (j:ℝ) hj10 hj0 (by linarith)
    convert h using 2 <;> ring
  have step2 : (Real.log ((j:ℝ)+1) - Real.log (j:ℝ))/Real.log ((j:ℝ)+1)
      ≤ Real.log (Real.log ((j:ℝ)+1)) - Real.log (Real.log (j:ℝ)) :=
    log_sub_log_ge (Real.log ((j:ℝ)+1)) (Real.log (j:ℝ)) haj hbj
      (Real.log_le_log hj0 (by linarith))
  calc 1/(((j:ℝ)+1) * Real.log ((j:ℝ)+1))
      = (1/((j:ℝ)+1))/Real.log ((j:ℝ)+1) := by field_simp
    _ ≤ (Real.log ((j:ℝ)+1) - Real.log (j:ℝ))/Real.log ((j:ℝ)+1) := by
        apply div_le_div_of_nonneg_right step1 haj.le
    _ ≤ _ := step2


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.range_H_le. -/
private lemma range_H_le (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k-2), 1/(((3+i:ℕ):ℝ) * Real.log ((3+i:ℕ):ℝ)))
      ≤ Real.log (Real.log (k:ℝ)) - Real.log (Real.log 2) := by
  have hsub := Finset.sum_range_sub (fun i : ℕ => Real.log (Real.log (((i+2:ℕ)):ℝ))) (n := k-2)
  have hstep : ∀ i ∈ Finset.range (k-2),
      1/(((3+i:ℕ):ℝ) * Real.log ((3+i:ℕ):ℝ))
        ≤ Real.log (Real.log (((i+1)+2:ℕ):ℝ)) - Real.log (Real.log (((i+2:ℕ)):ℝ)) := by
    intro i _
    have h := inv_log_step (i+2) (by omega)
    have e1 : ((i+2:ℕ)+1) = (3+i : ℕ) := by omega
    rw [e1] at h
    have e2 : ((i+1)+2 : ℕ) = (3+i : ℕ) := by omega
    rw [e2]
    exact h
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [hsub]
  have e3 : k - 2 + 2 = k := by omega
  rw [e3]
  norm_num


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.V_bound. -/
private lemma V_bound (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)))
      ≤ Real.log (Real.log (k:ℝ)) + 4 := by
  have hlog2 : (0:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  set a : ℕ → ℝ := fun i => 1/((i:ℝ) * Real.log ((i:ℝ)+1)) with ha
  set b : ℕ → ℝ := fun i => 1/((i:ℝ) * Real.log (i:ℝ)) with hb
  have hsplit := Finset.sum_range_add a 2 (k-1)
  rw [show 2 + (k-1) = k + 1 by omega] at hsplit
  rw [hsplit]
  have hfirst : (∑ x ∈ Finset.range 2, a x) = 1/Real.log 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [ha]
    norm_num
  rw [hfirst]
  have hshift : ∀ x ∈ Finset.range (k-1), a (2+x) ≤ b (2+x) := by
    intro x hx
    simp only [ha, hb]
    push_cast
    have hx0 : (0:ℝ) < 2 + (x:ℝ) := by positivity
    have hlogx : 0 < Real.log (2 + (x:ℝ)) := Real.log_pos (by linarith)
    have hlogx1 : Real.log (2 + (x:ℝ)) ≤ Real.log (2 + (x:ℝ) + 1) :=
      Real.log_le_log hx0 (by linarith)
    have hd1 : (0:ℝ) < (2 + (x:ℝ)) * Real.log (2 + (x:ℝ) + 1) :=
      mul_pos hx0 (Real.log_pos (by linarith))
    have hd2 : (0:ℝ) < (2 + (x:ℝ)) * Real.log (2 + (x:ℝ)) := mul_pos hx0 hlogx
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith [hlogx1, hx0]
  have hbound1 : (∑ x ∈ Finset.range (k-1), a (2+x)) ≤ ∑ x ∈ Finset.range (k-1), b (2+x) :=
    Finset.sum_le_sum hshift
  have hAB : 1/Real.log 2 + (∑ x ∈ Finset.range (k-1), a (2+x))
      ≤ 1/Real.log 2 + ∑ x ∈ Finset.range (k-1), b (2+x) := by linarith
  refine hAB.trans ?_
  have hsplit2 : (∑ x ∈ Finset.range (k-1), b (2+x))
      = (∑ x ∈ Finset.range 1, b (2+x)) + ∑ x ∈ Finset.range (k-2), b (2+(1+x)) := by
    have hrw2 : k - 1 = 1 + (k-2) := by omega
    conv_lhs => rw [hrw2]
    exact Finset.sum_range_add (fun x => b (2+x)) 1 (k-2)
  rw [hsplit2]
  have hb1 : (∑ x ∈ Finset.range 1, b (2+x)) = 1/((2:ℝ) * Real.log 2) := by
    rw [Finset.sum_range_one]
    simp only [hb]
    norm_num
  rw [hb1]
  have hb2 : (∑ x ∈ Finset.range (k-2), b (2+(1+x)))
      = ∑ x ∈ Finset.range (k-2), 1/(((3+x:ℕ):ℝ) * Real.log ((3+x:ℕ):ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp only [hb]
    have e : (2+(1+x:ℕ)) = (3+x : ℕ) := by omega
    rw [e]
  rw [hb2]
  have hH := range_H_le k hk
  have hA : 1/Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2]
    have := Real.log_two_gt_d9; linarith
  have hB : 1/((2:ℝ) * Real.log 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Real.log_two_gt_d9; linarith
  have hC : -Real.log (Real.log 2) ≤ 1 := by
    have hp : (0:ℝ) < 1/Real.log 2 := by positivity
    have h := Real.log_le_sub_one_of_pos hp
    rw [Real.log_div one_ne_zero hlog2.ne'] at h
    simp only [Real.log_one] at h
    linarith
  linarith [hH]


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.V_le_four. -/
private lemma V_le_four (k : ℕ) (hk : k ≤ 1) :
    (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1))) ≤ 4 := by
  have hlog2 : (0:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  interval_cases k
  · norm_num
  · have hsum : (∑ i ∈ Finset.range (1+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1))) = 1/Real.log 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [hsum, div_le_iff₀ hlog2]
    have := Real.log_two_gt_d9
    linarith


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.core. -/
private lemma core (q : ℕ) (hq : 1 ≤ q) :
    localMajorant q ^ 2 ≤
      Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ) + 2) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  set k : ℕ := q.primeFactors.card with hk
  have hfpos : 0 < localMajorant q := by
    rw [localMajorant]; exact Finset.prod_pos (fun p hp => by positivity)
  have hlogf : Real.log (localMajorant q)
      = ∑ p ∈ q.primeFactors, Real.log (1 + 6/(p:ℝ)) := by
    rw [localMajorant]
    exact Real.log_prod (fun p hp => by positivity)
  have hterm : ∀ p ∈ q.primeFactors, Real.log (1 + 6/(p:ℝ)) ≤ 6 * (1/(p:ℝ)) := by
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    have hpos : (0:ℝ) < 1 + 6/(p:ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have heq : 1 + 6/(p:ℝ) - 1 = 6/(p:ℝ) := by ring
    rw [heq] at h
    rw [mul_one_div]
    exact h
  have hsum_le : Real.log (localMajorant q) ≤ 6 * ∑ p ∈ q.primeFactors, 1/(p:ℝ) := by
    rw [hlogf, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsum12 : (∑ p ∈ q.primeFactors, 1/(p:ℝ))
      ≤ 12 * ∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)) := by
    rw [hk]
    exact sum_inv_prime_le q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  by_cases hk1 : k ≤ 1
  · -- few primes
    have hV : (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1))) ≤ 4 := V_le_four k hk1
    have hf : localMajorant q ≤ Real.exp 288 := by
      have h1 : Real.log (localMajorant q) ≤ 288 := by
        have := hsum_le.trans (mul_le_mul_of_nonneg_left (hsum12.trans (mul_le_mul_of_nonneg_left hV (by norm_num))) (by norm_num : (0:ℝ) ≤ 6))
        linarith
      calc localMajorant q ≤ Real.exp (Real.log (localMajorant q)) := (Real.exp_log hfpos).ge
        _ ≤ Real.exp 288 := Real.exp_le_exp.mpr h1
    have hsq : localMajorant q ^ 2 ≤ Real.exp 576 := by
      have := pow_le_pow_left₀ hfpos.le hf 2
      calc localMajorant q ^ 2 ≤ (Real.exp 288)^2 := this
        _ = Real.exp 576 := by
            rw [← Real.exp_nat_mul]
            norm_num
    have hK4 : Real.exp 576 ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * 2 := by
      have h1 : (1:ℝ) ≤ ((Nat.factorial 144 : ℕ) : ℝ) := by
        have : 1 ≤ Nat.factorial 144 := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 144)
        exact_mod_cast this
      have := Real.exp_pos 576
      nlinarith
    have h2 : (2:ℝ) ≤ Real.log (q:ℝ) + 2 := by
      have : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast hq)
      linarith
    calc localMajorant q ^ 2 ≤ Real.exp 576 := hsq
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * 2 := hK4
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ) + 2) := by
          have h1 : (0:ℝ) ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 := by positivity
          exact mul_le_mul_of_nonneg_left h2 h1
  · -- at least two primes
    have hk2 : 2 ≤ k := by omega
    have hV : (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)))
        ≤ Real.log (Real.log (k:ℝ)) + 4 := V_bound k hk2
    have hkr : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    have hlogk : 0 < Real.log (k:ℝ) := Real.log_pos (by linarith)
    -- k <= 2 log q
    have h2k : (2:ℕ)^k ≤ q := by
      have hdvd := Nat.prod_primeFactors_dvd q
      have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) hdvd
      have h2 : (2:ℕ)^k ≤ ∏ p ∈ q.primeFactors, p := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun p hp => Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
      exact h2.trans hle
    have hklq : (k:ℝ) ≤ 2 * Real.log (q:ℝ) := by
      have h1 : ((2:ℕ)^k : ℝ) ≤ (q:ℝ) := by exact_mod_cast h2k
      have h2 : ((2:ℕ)^k : ℝ) = (2:ℝ)^k := by push_cast; ring
      rw [h2] at h1
      have h3 : Real.log ((2:ℝ)^k) ≤ Real.log (q:ℝ) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h3
      have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith
    -- exponential chain
    have hlogf_le : Real.log (localMajorant q) ≤ 72 * Real.log (Real.log (k:ℝ)) + 288 := by
      have hA : 6 * ∑ p ∈ q.primeFactors, 1/(p:ℝ) ≤ 72 * (Real.log (Real.log (k:ℝ)) + 4) := by
        have := hsum12.trans (mul_le_mul_of_nonneg_left hV (by norm_num : (0:ℝ) ≤ 12))
        nlinarith
      linarith
    have hexp : Real.exp (72 * Real.log (Real.log (k:ℝ)) + 288)
        = Real.exp 288 * (Real.log (k:ℝ))^72 := by
      rw [Real.exp_add]
      have hc : (72:ℝ) = ((72:ℕ):ℝ) := by norm_num
      have h : Real.exp (72 * Real.log (Real.log (k:ℝ))) = (Real.log (k:ℝ))^72 := by
        rw [hc, Real.exp_nat_mul, Real.exp_log hlogk]
      rw [h]
      ring
    have hf : localMajorant q ≤ Real.exp 288 * (Real.log (k:ℝ))^72 := by
      have := (Real.log_le_iff_le_exp hfpos).mp hlogf_le
      rwa [hexp] at this
    have hf2 : localMajorant q ^ 2 ≤ Real.exp 576 * (Real.log (k:ℝ))^144 := by
      have := pow_le_pow_left₀ (le_of_lt hfpos) hf 2
      calc localMajorant q ^ 2 ≤ (Real.exp 288 * (Real.log (k:ℝ))^72)^2 := this
        _ = Real.exp 576 * (Real.log (k:ℝ))^144 := by
            rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
            norm_num
    have hfac : (Real.log (k:ℝ))^144 ≤ ((Nat.factorial 144 : ℕ) : ℝ) * (k:ℝ) := by
      have h := Real.pow_div_factorial_le_exp (Real.log (k:ℝ)) hlogk.le 144
      rw [Real.exp_log (by linarith : (0:ℝ) < (k:ℝ))] at h
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ((Nat.factorial 144 : ℕ) : ℝ))] at h
      linarith
    calc localMajorant q ^ 2 ≤ Real.exp 576 * (Real.log (k:ℝ))^144 := hf2
      _ ≤ Real.exp 576 * (((Nat.factorial 144 : ℕ) : ℝ) * (k:ℝ)) := by
          exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * ((k:ℝ)/2) := by ring
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ)) := by
          have h1 : (0:ℝ) ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 := by positivity
          have hklq2 : (k:ℝ)/2 ≤ Real.log (q:ℝ) := by linarith
          exact mul_le_mul_of_nonneg_left hklq2 h1
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ) + 2) := by
          have h1 : (0:ℝ) ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 := by positivity
          have h2 : Real.log (q:ℝ) ≤ Real.log (q:ℝ) + 2 := by linarith
          exact mul_le_mul_of_nonneg_left h2 h1


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.localMajorant_log_bound. -/
theorem localMajorant_log_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ (x : ℝ) (q : ℕ),
      x0 ≤ x → 0 < q → (q : ℝ) ≤ x ^ (1 / 3 : ℝ) →
      localMajorant q ^ 2 ≤ C * Real.log x := by

  refine ⟨Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2, 100, by positivity, by norm_num, ?_⟩
  intro x q hx hq hqle
  have hx100 : (100:ℝ) ≤ x := hx
  have hx0 : (0:ℝ) < x := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hcore := core q (by omega)
  have hlog100 : (3:ℝ) ≤ Real.log 100 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 100)]
    have h1 : Real.exp 3 = (Real.exp 1)^3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h1]
    have he : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
    have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have h3 : (Real.exp 1)^3 ≤ (2.72:ℝ)^3 := pow_le_pow_left₀ he0.le he.le 3
    have h272 : (2.72:ℝ)^3 < 100 := by norm_num
    linarith
  have hlogx3 : (3:ℝ) ≤ Real.log x :=
    hlog100.trans (Real.log_le_log (by norm_num) hx100)
  have hlogq : Real.log (q:ℝ) ≤ Real.log x / 3 := by
    have h := Real.log_le_log hq0 hqle
    rw [Real.log_rpow hx0] at h
    linarith
  have h2 : Real.log (q:ℝ) + 2 ≤ Real.log x := by linarith
  refine hcore.trans ?_
  exact mul_le_mul_of_nonneg_left h2 (by positivity)


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.reciprocal_square_tail. -/
theorem reciprocal_square_tail (P : ℝ) (b : ℕ) (hP : 0 < P) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ b, 1 / (q : ℝ) ^ 2) ≤ 2 / P := by
  by_cases h : 0 < ⌊P⌋₊ ∧ ⌊P⌋₊ ≤ b
  · rcases h with ⟨hP0, hPb⟩
    have h1 := Task506aTask271b.sum_inv_sq_Ioc_le ⌊P⌋₊ b hP0 hPb
    calc
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ b, 1 / (q : ℝ) ^ 2) ≤ 1 / (⌊P⌋₊ : ℝ) - 1 / (b : ℝ) := h1
      _ ≤ 1 / (⌊P⌋₊ : ℝ) := sub_le_self _ (by positivity)
      _ ≤ 2 / P := by
        have hd : P < 2 * ⌊P⌋₊ := by
          have hpfloor : 1 ≤ (⌊P⌋₊ : ℝ) := Nat.one_le_cast.mpr hP0
          have : P < (⌊P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one P
          linarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
  · push Not at h
    by_cases hP0 : 0 < ⌊P⌋₊
    · have hbb : b < ⌊P⌋₊ := h hP0
      have : Finset.Ioc ⌊P⌋₊ b = ∅ := Finset.Ioc_eq_empty_of_le (le_of_lt hbb)
      rw [this, Finset.sum_empty]
      positivity
    · have hP0' : ⌊P⌋₊ = 0 := by omega
      have hp1 : P < 1 := Nat.floor_eq_zero.mp hP0'
      by_cases hb : 0 < b
      · have : Finset.Ioc ⌊P⌋₊ b = Finset.Ioc 0 b := by rw [hP0']
        rw [this]
        have h_eq : Finset.Ioc 0 b = insert 1 (Finset.Ioc 1 b) := by
          ext x
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        rw [h_eq, Finset.sum_insert (by simp)]
        have h_sum : (∑ q ∈ Finset.Ioc 1 b, 1 / (q : ℝ) ^ 2) ≤ 1 / (1 : ℝ) - 1 / (b : ℝ) := by
          exact_mod_cast Task506aTask271b.sum_inv_sq_Ioc_le 1 b (by omega) (by omega)
        calc
          1 / ((1 : ℕ) : ℝ) ^ 2 + ∑ q ∈ Finset.Ioc 1 b, 1 / (q : ℝ) ^ 2 ≤ 1 + (1 / (1 : ℝ) - 1 / (b : ℝ)) := by
            have : 1 / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
            rw [this]
            exact add_le_add le_rfl h_sum
          _ ≤ 2 := by linarith [show 0 ≤ 1 / (b : ℝ) by positivity]
          _ ≤ 2 / P := by
            rw [le_div_iff₀ hP]
            linarith
      · have : b = 0 := by omega
        have : Finset.Ioc ⌊P⌋₊ b = ∅ := by rw [this, hP0']; exact Finset.Ioc_eq_empty_of_le le_rfl
        rw [this, Finset.sum_empty]
        positivity


/-- Page 13 through page 15, copied proof helper from Task506aTask292a.diagonal_bound. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := localMajorant_log_bound
  refine ⟨4 * C, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hpoint (n q : ℕ) (hq : q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊) :
      ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2 ≤
        C * Real.log x * (1 / (q : ℝ) ^ 2) := by
    have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
    have hqy : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
    have hqx : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) := hqy.trans
      (Real.rpow_le_rpow (by linarith) hyx (by norm_num))
    have hcoef := coefficient_product_bound n q hqn
    have hprod := hb x q hx hqn hqx
    have hw : ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ≤ ‖U1534.A2 n q‖ := by
      rw [norm_mul, norm_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) (Task506aTask271b.smoothWeight_norm_le_one q Q)
    calc
      _ ≤ (localMajorant q / (q : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hw.trans hcoef) 2
      _ = localMajorant q ^ 2 * (1 / (q : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          C * Real.log x * (1 / (q : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun q hq => hpoint n q hq
    _ = ((intervalNumbers x y).card : ℝ) * (C * Real.log x *
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊, 1 / (q : ℝ) ^ 2) := by
      simp [Finset.mul_sum]
    _ ≤ (2 * y) * (C * Real.log x * (2 / P)) := by
      apply mul_le_mul
      · exact Task506aTask271a.interval_card_le (by linarith) hy
      · exact mul_le_mul_of_nonneg_left (reciprocal_square_tail P _ hP) (by positivity)
      · positivity
      · positivity
    _ = (4 * C) * (y / P * Real.log x) := by ring


end LeanLab.KumchevLiu2007.Task506aTask292a

namespace LeanLab.KumchevLiu2007.Task506aTask292b

open Real Complex Task506aTask129b Task506aTask292a
open scoped BigOperators

                                                             

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask292b.complete_period_majorant. -/
theorem complete_period_majorant {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    (∑ n ∈ Finset.range (q * r),
      ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖) ≤
        localMajorant q * localMajorant r := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    _ ≤ ∑ _n ∈ Finset.range (q * r),
        (localMajorant q / (q : ℝ)) * (localMajorant r / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_conj]
      exact mul_le_mul (coefficient_product_bound n q hq)
        (coefficient_product_bound n r hr) (norm_nonneg _)
        ((norm_nonneg _).trans (coefficient_product_bound n q hq))
    _ = localMajorant q * localMajorant r := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
      field_simp


end LeanLab.KumchevLiu2007.Task506aTask292b

namespace LeanLab.KumchevLiu2007.Task506aTask342a

open Real Complex
open scoped BigOperators

                                                                              

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask342a.reduced_sum_zmod. -/
theorem reduced_sum_zmod (q : ℕ) [NeZero q] (g : ℕ → ℂ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), g a) =
      ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y), g y.val := by
  classical
  refine Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ha ⊢
    rw [ZMod.isUnit_iff_coprime]
    exact ha.2
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    have h := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt ha1.1, ZMod.val_natCast_of_lt ha2.1] at h
  · intro y hy
    refine ⟨y.val, ?_, ZMod.natCast_zmod_val y⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt y, ?_⟩
    have hy' : IsUnit y := (Finset.mem_filter.mp hy).2
    rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime] at hy'
    exact hy'
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.val_natCast_of_lt ha.1]


/-- Page 13 through page 15, copied proof helper from Task506aTask342a.A2_zmod_formula. -/
theorem A2_zmod_formula (n q : ℕ) [NeZero q] :
    U1534.A2 n q =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) ^ 2 *
        ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
            ZMod.stdAddChar (N := q) (a * (x * x - (n : ZMod q))) := by
  classical
  unfold U1534.A2 U1534.gaussS
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  rw [reduced_sum_zmod]
  apply Finset.sum_congr rfl
  intro x hx
  rw [reduced_sum_zmod]
  apply Finset.sum_congr rfl
  intro a ha
  unfold U1534.ee
  rw [← Complex.exp_add]
  rw [show a * (x * x - (n : ZMod q)) =
      (((a.val : ℤ) * ((x.val : ℤ) ^ 2 - (n : ℤ)) : ℤ) : ZMod q) by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring


/-- Page 13 through page 15, copied proof helper from Task506aTask342a.unit_character_sum_conj. -/
theorem unit_character_sum_conj (q : ℕ) [NeZero q] (t : ZMod q) :
    (starRingEnd ℂ) (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * t)) =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        ZMod.stdAddChar (N := q) (a * t) := by
  classical
  rw [map_sum]
  simp_rw [AddChar.starComp_apply (by rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q : 0 < ringChar (ZMod q)),
    AddChar.inv_apply, ← neg_mul]
  refine Finset.sum_bij (fun (a : ZMod q) _ => -a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.neg
  · intro a ha b hb hab
    exact neg_injective hab
  · intro a ha
    refine ⟨-a, ?_, neg_neg a⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.neg
  · intro a ha
    rfl


/-- Page 13 through page 15, copied proof helper from Task506aTask342a.A2_conj. -/
theorem A2_conj (n q : ℕ) :
    (starRingEnd ℂ) (U1534.A2 n q) = U1534.A2 n q := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [U1534.A2]
  letI : NeZero q := ⟨hq⟩
  rw [A2_zmod_formula, map_mul, map_div₀, map_pow, map_intCast, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact unit_character_sum_conj q (x * x - (n : ZMod q))


end LeanLab.KumchevLiu2007.Task506aTask342a

namespace LeanLab.KumchevLiu2007.Task506aTask342b

open Real Complex Task506aTask292a
open scoped BigOperators

                                                                                                  

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask342b.local_factor_power. -/
theorem local_factor_power (ε : ℝ) (hε : 0 < ε) (p : ℕ)
    (hp : 1 ≤ p) (hlarge : (7 : ℝ) ^ ε⁻¹ ≤ (p : ℝ)) :
    1 + 6 / (p : ℝ) ≤ (p : ℝ) ^ ε := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hsmall : 1 + 6 / (p : ℝ) ≤ 7 := by
    have : 6 / (p : ℝ) ≤ 6 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 7 ^ ε⁻¹) hlarge hε.le
  rw [Real.rpow_inv_rpow (by norm_num) hε.ne'] at hpow
  exact hsmall.trans hpow


/-- Page 13 through page 15, copied proof helper from Task506aTask342b.localMajorant_power_bound. -/
theorem localMajorant_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q → localMajorant q ≤ K * (q : ℝ) ^ ε := by
  classical
  let N : ℕ := ⌈(7 : ℝ) ^ ε⁻¹⌉₊
  refine ⟨(7 : ℝ) ^ N, by positivity, ?_⟩
  intro q hq
  let S := q.primeFactors.filter (fun p => p < N)
  let T := q.primeFactors.filter (fun p => ¬ p < N)
  have hpos (p : ℕ) (hp : p ∈ q.primeFactors) : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hS : (∏ p ∈ S, (1 + 6 / (p : ℝ))) ≤ (7 : ℝ) ^ N := by
    calc
      _ ≤ ∏ _p ∈ S, (7 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun p hp => by positivity)
        intro p hp
        have hpR := hpos p (Finset.mem_filter.mp hp).1
        have : 6 / (p : ℝ) ≤ 6 := (div_le_iff₀ (by linarith)).mpr (by linarith)
        linarith
      _ = (7 : ℝ) ^ S.card := by simp
      _ ≤ (7 : ℝ) ^ N := by
        apply pow_le_pow_right₀ (by norm_num)
        have hsub : S ⊆ Finset.range N := by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
        simpa using Finset.card_le_card hsub
  have hT : (∏ p ∈ T, (1 + 6 / (p : ℝ))) ≤ (q : ℝ) ^ ε := by
    calc
      _ ≤ ∏ p ∈ T, (p : ℝ) ^ ε := by
        apply Finset.prod_le_prod₀ (fun p hp => by positivity)
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hpN⟩
        apply local_factor_power ε hε p (by exact_mod_cast hpos p hp)
        exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_of_not_gt hpN))
      _ = (∏ p ∈ T, (p : ℝ)) ^ ε :=
        Real.finsetProd_rpow T (fun p => (p : ℝ)) (fun p hp => by positivity) ε
      _ ≤ (q : ℝ) ^ ε := by
        apply Real.rpow_le_rpow (by positivity) _ hε.le
        have hprod : ∏ p ∈ T, p ≤ q := by
          apply Nat.le_of_dvd hq
          exact (Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p)
            (Finset.filter_subset _ _)).trans
            (Nat.prod_primeFactors_dvd q)
        have hc : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hprod
        simpa only [Nat.cast_prod] using hc
  rw [localMajorant, ← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => p < N)]
  exact mul_le_mul hS hT (by positivity) (by positivity)


/-- Page 13 through page 15, copied proof helper from Task506aTask342b.majorant_sum_bound. -/
theorem majorant_sum_bound (K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (hb : ∀ q : ℕ, 0 < q → localMajorant q ≤ K * (q : ℝ) ^ ε)
    (P Y : ℝ) (hY : 1 ≤ Y) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊, localMajorant q) ≤ K * Y ^ (1 + ε) := by
  have hpoint (q : ℕ) (hq : q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊) :
      localMajorant q ≤ K * Y ^ ε := by
    have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
    have hqY : (q : ℝ) ≤ Y :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by linarith))
    exact (hb q hqn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hqY hε) hK.le)
  calc
    _ ≤ ∑ _q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊, K * Y ^ ε :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊).card : ℝ) * (K * Y ^ ε) := by simp
    _ ≤ Y * (K * Y ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : (Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊).card ≤ ⌊Y⌋₊ := by
        simp only [Nat.card_Ioc]
        omega
      exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (by linarith))
    _ = K * Y ^ (1 + ε) := by rw [Real.rpow_add (by linarith), Real.rpow_one]; ring


/-- Page 13 through page 15, copied proof helper from Task506aTask342b.majorant_pair_sum. -/
theorem majorant_pair_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ y P : ℝ, 1 ≤ y → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          localMajorant q * localMajorant r) ≤ C * y ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨K, hK, hb⟩ := localMajorant_power_bound (1 / 8 : ℝ) (by norm_num)
  refine ⟨K ^ 2, by positivity, ?_⟩
  intro y P hy hP
  let S := Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊
  have hnonneg (q : ℕ) : 0 ≤ localMajorant q := by
    unfold localMajorant
    exact Finset.prod_nonneg (fun p hp => by positivity)
  have hsum0 : 0 ≤ ∑ q ∈ S, localMajorant q := Finset.sum_nonneg (fun q hq => hnonneg q)
  have hY : 1 ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy (by norm_num)
  have hsum := majorant_sum_bound K (1 / 8 : ℝ) hK (by norm_num) hb P _ hY
  change (∑ q ∈ S, ∑ r ∈ S.erase q, _) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ r ∈ S, localMajorant q * localMajorant r := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q S)
        (fun r hr hnot => mul_nonneg (hnonneg q) (hnonneg r))
    _ = (∑ q ∈ S, localMajorant q) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (K * (y ^ (1 / 3 : ℝ)) ^ (1 + (1 / 8 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hsum0 hsum 2
    _ = K ^ 2 * y ^ (3 / 4 : ℝ) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by linarith : 0 ≤ y)]
      norm_num


end LeanLab.KumchevLiu2007.Task506aTask342b

namespace LeanLab.KumchevLiu2007.Task506aTask342c

open Real Complex Task506aTask129b Task506aTask292a
open scoped BigOperators

                                                                                    

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask342c.A2_conjugate_interval_bound. -/
theorem A2_conjugate_interval_bound {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ ≤
      2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
  simpa only [Task506aTask342a.A2_conj] using A2_interval_bound hq hr hqr a b


/-- Page 13 through page 15, copied proof helper from Task506aTask342c.weighted_pair_interval. -/
theorem weighted_pair_interval {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (x y Q : ℝ) :
    (∑ n ∈ intervalNumbers x y,
      ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
        (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
      2 * (localMajorant q * localMajorant r) := by
  let u : ℂ := -(smoothWeight q Q : ℂ)
  let v : ℂ := -(smoothWeight r Q : ℂ)
  have hu : ‖u‖ ≤ 1 := by simpa [u] using Task506aTask271b.smoothWeight_norm_le_one q Q
  have hv : ‖v‖ ≤ 1 := by simpa [v] using Task506aTask271b.smoothWeight_norm_le_one r Q
  have huv : ‖u * (starRingEnd ℂ) v‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact mul_le_one₀ hu (norm_nonneg _) hv
  have heq : (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) =
      ((u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))).re := by
    rw [← Complex.re_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    ring
  change (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) ≤ _
  rw [heq]
  calc
    _ ≤ ‖(u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))‖ := Complex.re_le_norm _
    _ ≤ ‖∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) huv
    _ ≤ 2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using
        A2_conjugate_interval_bound hq hr hqr (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Task506aTask292b.complete_period_majorant hq hr) (by norm_num)


/-- Page 13 through page 15, copied proof helper from Task506aTask342c.off_diagonal_power_bound. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := Task506aTask342b.majorant_pair_sum
  refine ⟨2 * C, by positivity, ?_⟩
  intro x y P Q hx hy hP
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          2 * (localMajorant q * localMajorant r) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hrn : 0 < r := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hr)).1
      exact weighted_pair_interval hqn hrn (Finset.ne_of_mem_erase hr).symm x y Q
    _ ≤ (2 * C) * y ^ (3 / 4 : ℝ) := by
      simp only [← Finset.mul_sum]
      have h := hb y P hy hP
      simp only [← Finset.mul_sum] at h
      nlinarith [h]


/-- Page 13 through page 15, copied proof helper from Task506aTask342c.off_diagonal_bound. -/
theorem off_diagonal_bound (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ( (-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * (y / Real.log x ^ A) := by
  obtain ⟨C, hC, hb⟩ := off_diagonal_power_bound
  obtain ⟨x0, hx0, ha⟩ := Task506aTask271b.quarter_power_absorption A ε hε
  refine ⟨C, x0, hC, hx0, ?_⟩
  intro x y P Q hx hy _hyx hP _hPQ _hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  exact (hb x y P Q (by linarith) hy1 hP).trans
    (mul_le_mul_of_nonneg_left (ha x y hx hy) hC.le)


/-- Page 13 through page 15, copied proof helper from Task506aTask342c.tail_mean_square_input. -/
theorem tail_mean_square_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  obtain ⟨Cd, xd, hCd, hxd, hd⟩ := Task506aTask292a.diagonal_bound
  obtain ⟨Co, xo, hCo, hxo, ho⟩ := off_diagonal_bound A ε hA hε
  refine ⟨Cd + Co, max xd xo, by positivity, hxd.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxd' : xd ≤ x := (le_max_left _ _).trans hx
  have hxo' : xo ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hxd.trans hxd'
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hd' := hd x y P Q hxd' hy1 hyx hP
  have ho' := ho x y P Q hxo' hy hyx hP hPQ hQ
  have heq : (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) =
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) +
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) := by
    simp only [tail2, Task506aTask271b.norm_sum_sq_split, Finset.sum_add_distrib]
  rw [heq]
  have hm : 0 ≤ y / P * Real.log x := by positivity
  have he : 0 ≤ y / Real.log x ^ A := by positivity
  calc
    _ ≤ Cd * (y / P * Real.log x) + Co * (y / Real.log x ^ A) := add_le_add hd' ho'
    _ ≤ (Cd + Co) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith


end LeanLab.KumchevLiu2007.Task506aTask342c

namespace LeanLab.KumchevLiu2007.Task506aTask342e

open Real Complex Task506aTask129 Task506aTask129b
open scoped BigOperators

                                                                                                     

set_option maxHeartbeats 2000000

/-- Page 13 through page 15, copied proof helper from Task506aTask342e.truncation_input. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  exact Task506aTask271a.truncation_from_pointwise A ε hA hε


/-- Page 13 through page 15, copied proof helper from Task506aTask342e.lemma38_two_proved. -/
theorem lemma38_two_proved :
  ∀ A ε : ℝ, 2 ≤ A → 0 < ε → ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖series2 n P - product2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  intro A ε hA hε
  obtain ⟨Ce, Xe, hCe, hXe, he⟩ := truncation_input A ε hA hε
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := Task506aTask342c.tail_mean_square_input A ε hA hε
  refine ⟨2 * (Ce + Ct), max Xe Xt, by positivity,
    le_trans hXe (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxe : Xe ≤ x := le_trans (le_max_left _ _) hx
  have hxt : Xt ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := hXe.trans hxe
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have he' := he x y P Q hxe hy hyx hP hPQ hQ
  have ht' := ht x y P Q hxt hy hyx hP hPQ hQ
  have hs := mean_square_add (intervalNumbers x y)
    (fun n => tail2 n P (y ^ (1 / 3 : ℝ)) Q)
    (fun n => (series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q)
  simp only [add_sub_cancel] at hs
  have hmain : 0 ≤ y / P * Real.log x := by positivity
  have herr : Ce * (y / Real.log x ^ A) ≤
      Ce * (y / P * Real.log x + y / Real.log x ^ A) := by
    nlinarith
  calc _ ≤ 2 * (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) +
      2 * (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) := hs
    _ ≤ 2 * (Ct * (y / P * Real.log x + y / Real.log x ^ A)) +
      2 * (Ce * (y / Real.log x ^ A)) := by linarith
    _ ≤ 2 * (Ce + Ct) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith


end LeanLab.KumchevLiu2007.Task506aTask342e
