module

public import Mathlib

/-!
Perelli 1996, page 481 equation 3.
A nonnegative divisor expansion for the squared totient ratio.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.InverseTotient320
open Finset Real
noncomputable section

/-- Page 481 equation 3, derived Euler correction for the squared totient ratio. -/
def correction (n : ℕ) : ℝ :=
  if n = 1 then 1 else if Squarefree n then
    ∏ p ∈ n.primeFactors, (((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1) else 0

/-- The divisor expansion has its unit coefficient at one. -/
theorem correction_one : correction 1 = 1 := by simp [correction]

/-- The correction is supported on squarefree positive integers. -/
theorem correction_nonsquarefree {n : ℕ} (hn : ¬ Squarefree n) : correction n = 0 := by
  have hn1 : n ≠ 1 := by rintro rfl; exact hn (by simp)
  simp [correction, hn1, hn]

/-- The correction at a prime is the change in its squared Euler factor. -/
theorem correction_prime {p : ℕ} (hp : p.Prime) :
    correction p = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1 := by
  simp [correction, hp.ne_one, hp.squarefree, hp.primeFactors]

/-- Every correction coefficient is nonnegative. -/
theorem correction_nonneg (n : ℕ) : 0 ≤ correction n := by
  unfold correction
  split_ifs with hn1 hsq
  · norm_num
  · apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hratio : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    nlinarith
  · norm_num

/-- Coprime products multiply the correction coefficients. -/
theorem correction_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    correction (m * n) = correction m * correction n := by
  by_cases hm1 : m = 1
  · subst m; simp [correction_one]
  by_cases hn1 : n = 1
  · subst n; simp [correction_one]
  by_cases hms : Squarefree m
  · by_cases hns : Squarefree n
    · have hmn : m * n ≠ 1 := by intro h; exact hm1 (Nat.eq_one_of_dvd_one ⟨n, h.symm⟩)
      simp only [correction, if_neg hm1, if_neg hn1, if_neg hmn,
        if_pos hms, if_pos hns, if_pos ((Nat.squarefree_mul hcop).mpr ⟨hms, hns⟩),
        hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors]
    · rw [correction_nonsquarefree hns, mul_zero]
      exact correction_nonsquarefree (fun h => hns (h.of_mul_right))
  · rw [correction_nonsquarefree hms, zero_mul]
    exact correction_nonsquarefree (fun h => hms (h.of_mul_left))

/-- The sum of the correction coefficients over divisors is the squared totient ratio. -/
theorem sum_correction (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, correction d) = ((n : ℝ) / n.totient) ^ 2 := by
  let af : ArithmeticFunction ℝ := ⟨correction, correction_nonsquarefree (by simp)⟩
  have haf : af.IsMultiplicative := ⟨correction_one, fun {_ _} h => correction_mul h⟩
  let g := af * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative := haf.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hgval (k : ℕ) : g k = ∑ d ∈ k.divisors, correction d :=
    ArithmeticFunction.coe_mul_zeta_apply
  have hpp (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
      (∑ j ∈ range (e + 1), correction (p ^ j)) = 1 + correction p := by
    induction e, he using Nat.le_induction with
    | base => simp [Finset.sum_range_succ, correction_one]
    | succ e he ih =>
      rw [Finset.sum_range_succ, ih]
      have hns : ¬ Squarefree (p ^ (e + 1)) := by
        rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
        simp only [not_and]
        intro _
        omega
      rw [correction_nonsquarefree hns, add_zero]
  have hprod : (∑ d ∈ n.divisors, correction d) =
      ∏ p ∈ n.primeFactors, (1 + correction p) := by
    have hall : ∀ k : ℕ, k ≠ 0 → (∑ d ∈ k.divisors, correction d) =
        ∏ p ∈ k.primeFactors, (1 + correction p) := by
      intro k
      induction k using Nat.recOnPosPrimePosCoprime with
      | zero => intro h; exact (h rfl).elim
      | one => intro _; simp [correction_one]
      | prime_pow p e hp he =>
        intro _
        rw [Nat.primeFactors_prime_pow he.ne' hp, Finset.prod_singleton,
          Nat.sum_divisors_prime_pow hp]
        exact hpp p e hp he
      | coprime a b ha hb hab ia ib =>
        intro _
        rw [← hgval, hg.map_mul_of_coprime hab, hgval, hgval, ia (by omega), ib (by omega),
          hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]
    exact hall n hn.ne'
  rw [hprod]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hEuler : (n.totient : ℝ) = (n : ℝ) *
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  have hid : (∏ p ∈ n.primeFactors, (1 + correction p)) *
      (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 2 = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    rw [correction_prime hprime]
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hp0, hp1]
    ring
  have hcross : (∏ p ∈ n.primeFactors, (1 + correction p)) * (n.totient : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
    rw [hEuler, mul_pow]
    nlinarith [congrArg (fun x : ℝ => (n : ℝ) ^ 2 * x) hid]
  rw [div_pow]
  exact (eq_div_iff (pow_ne_zero 2 hφ.ne')).mpr hcross

/-- The prime correction is bounded by six over the prime. -/
theorem correction_prime_le {p : ℕ} (hp : p.Prime) :
    correction p ≤ 6 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [correction_prime hp]
  apply (le_div_iff₀ hp0).mpr
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hp1)).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sq_nonneg ((p : ℝ) - 1))]

/-- A squarefree Euler product gives a half power bound for the correction. -/
theorem correction_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → correction n ≤ C * (n : ℝ) ^ (-1 / 2 : ℝ) := by
  classical
  let A (p : ℕ) : ℝ := if p ≤ 36 then max 1 (correction p * Real.sqrt p) else 1
  let C : ℝ := ∏ p ∈ range 37, A p
  have hA (p : ℕ) : 1 ≤ A p := by dsimp [A]; split_ifs <;> simp
  have hC : 1 ≤ C := by
    calc (1 : ℝ) = ∏ _p ∈ range 37, (1 : ℝ) := by simp
      _ ≤ C := Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun p _ => hA p)
  have hprodA (s : Finset ℕ) : (∏ p ∈ s, A p) ≤ C := by
    have heq : (∏ p ∈ s ∩ range 37, A p) = ∏ p ∈ s, A p := by
      apply Finset.prod_subset Finset.inter_subset_left
      intro p hp hnot
      have hlarge : ¬ p ≤ 36 := by
        intro h
        exact hnot (Finset.mem_inter.mpr ⟨hp, Finset.mem_range.mpr (by omega)⟩)
      simp [A, hlarge]
    rw [← heq]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
      (fun p _ => le_trans (by norm_num) (hA p)) (fun p _ _ => hA p)
  have hprime (p : ℕ) (hp : p.Prime) : correction p ≤ A p * (p : ℝ) ^ (-1 / 2 : ℝ) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
    have heq : (p : ℝ) ^ (-1 / 2 : ℝ) = 1 / Real.sqrt (p : ℝ) := by
      simp only [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
        Real.rpow_neg hpR.le, one_div]
    rw [heq, ← mul_div_assoc, mul_one]
    apply (le_div_iff₀ hs).mpr
    by_cases hp36 : p ≤ 36
    · exact (le_max_right 1 (correction p * Real.sqrt p)).trans_eq (by simp [A, hp36])
    · have hp36R : (36 : ℝ) ≤ p := by exact_mod_cast (show 36 ≤ p by omega)
      have hs6 : 6 ≤ Real.sqrt (p : ℝ) := by
        exact (Real.le_sqrt (by norm_num) hpR.le).mpr (by nlinarith)
      have hsq := Real.sq_sqrt hpR.le
      have hbound := correction_prime_le hp
      have hmul := mul_le_mul_of_nonneg_right hbound hs.le
      have hrat : 6 / (p : ℝ) * Real.sqrt p ≤ 1 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hpR).mpr
        nlinarith
      calc correction p * Real.sqrt p ≤ 6 / (p : ℝ) * Real.sqrt p := hmul
        _ ≤ 1 := hrat
        _ = A p := by simp [A, hp36]
  let af : ArithmeticFunction ℝ := ⟨correction, correction_nonsquarefree (by simp)⟩
  have haf : af.IsMultiplicative := ⟨correction_one, fun {_ _} h => correction_mul h⟩
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro n hn
  by_cases hsq : Squarefree n
  · have hfactor : correction n = ∏ p ∈ n.primeFactors, correction p :=
      (haf.prod_primeFactors hsq).symm
    have hpow : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (-1 / 2 : ℝ)) = (n : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p),
        ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    calc correction n = ∏ p ∈ n.primeFactors, correction p := hfactor
      _ ≤ ∏ p ∈ n.primeFactors, A p * (p : ℝ) ^ (-1 / 2 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun p _ => correction_nonneg p)
        intro p hp
        exact hprime p (Nat.prime_of_mem_primeFactors hp)
      _ = (∏ p ∈ n.primeFactors, A p) * (n : ℝ) ^ (-1 / 2 : ℝ) := by
        rw [Finset.prod_mul_distrib, hpow]
      _ ≤ C * (n : ℝ) ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hprodA n.primeFactors) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [correction_nonsquarefree hsq]
    positivity

/-- The reciprocal weighted correction series converges absolutely. -/
theorem summable_correction_div : Summable (fun n : ℕ => correction n / n) := by
  obtain ⟨C, hC, hbound⟩ := correction_power_bound
  have hs : Summable (fun n : ℕ => C * (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left C
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (correction_nonneg n) (Nat.cast_nonneg _))
    (hf := hs)
  intro n
  by_cases hn : n = 0
  · subst n; simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc correction n / n ≤ C * (n : ℝ) ^ (-1 / 2 : ℝ) / n :=
      div_le_div_of_nonneg_right (hbound n (Nat.pos_of_ne_zero hn)) hnR.le
    _ = C * (n : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [mul_div_assoc]
      congr 1
      rw [show (-3 / 2 : ℝ) = -1 / 2 - 1 by norm_num,
        Real.rpow_sub hnR, Real.rpow_one]

/-- The reciprocal squares on any finite tail are at most two over its real cutoff. -/
theorem reciprocal_sq_tail (x : ℝ) (hx : 0 < x) (s : Finset ℕ)
    (hs : ∀ r ∈ s, x < (r : ℝ)) :
    (∑ r ∈ s, 1 / (r : ℝ) ^ 2) ≤ 2 / x := by
  have hsub : s ⊆ Ioo ⌊x⌋₊ (s.sup id + 1) := by
    intro r hr
    refine Finset.mem_Ioo.mpr ⟨?_, ?_⟩
    · have hfloor := Nat.floor_le hx.le
      have : (⌊x⌋₊ : ℝ) < (r : ℝ) := hfloor.trans_lt (hs r hr)
      exact_mod_cast this
    · have h := Finset.le_sup (f := id) hr
      dsimp at h
      omega
  calc
    _ ≤ ∑ r ∈ Ioo ⌊x⌋₊ (s.sup id + 1), 1 / (r : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / ((⌊x⌋₊ : ℝ) + 1) := by
      simpa only [one_div] using (sum_Ioo_inv_sq_le (α := ℝ) ⌊x⌋₊ (s.sup id + 1))
    _ ≤ 2 / x := div_le_div_of_nonneg_left (by norm_num) hx (Nat.lt_floor_add_one x).le

/-- Page 481 equation 3, the inverse totient squared tail with an absolute constant. -/
theorem inverse_totient_sq_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℝ, 0 < P → ∀ s : Finset ℕ,
      (∀ n ∈ s, 0 < n ∧ P < (n : ℝ)) →
      (∑ n ∈ s, 1 / (n.totient : ℝ) ^ 2) ≤ K / P := by
  classical
  let T := ∑' d : ℕ, correction d / d
  have hT : 0 ≤ T := tsum_nonneg (fun d => div_nonneg (correction_nonneg d) (Nat.cast_nonneg _))
  refine ⟨2 * (T + 1), by positivity, ?_⟩
  intro P hP s hs
  let D := s.biUnion Nat.divisors
  have hdpos (d : ℕ) (hd : d ∈ D) : 0 < d := by
    obtain ⟨n, hn, hdn⟩ := Finset.mem_biUnion.mp hd
    exact Nat.pos_of_mem_divisors hdn
  have hdouble : (∑ n ∈ s, 1 / (n.totient : ℝ) ^ 2) =
      ∑ d ∈ D, ∑ n ∈ s with d ∣ n, correction d / (n : ℝ) ^ 2 := by
    calc
      _ = ∑ n ∈ s, ∑ d ∈ n.divisors, correction d / (n : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [← Finset.sum_div, sum_correction n (hs n hn).1]
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (hs n hn).1.ne'
        have hφ : (n.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (hs n hn).1).ne'
        field_simp
      _ = ∑ n ∈ s, ∑ d ∈ D, if d ∣ n then correction d / (n : ℝ) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext d
          simp only [Finset.mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨hdn, hn0⟩
            exact ⟨Finset.mem_biUnion.mpr ⟨n, hn, Nat.mem_divisors.mpr ⟨hdn, hn0⟩⟩, hdn⟩
          · rintro ⟨_, hdn⟩
            exact ⟨hdn, (hs n hn).1.ne'⟩
        · intro d hd; rfl
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]
  have hinner (d : ℕ) (hd : d ∈ D) :
      (∑ n ∈ s with d ∣ n, correction d / (n : ℝ) ^ 2) ≤
        2 / P * (correction d / d) := by
    have hd0 := hdpos d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    let u := s.filter (fun n => d ∣ n)
    let t := u.image (fun n => n / d)
    have hdiv (n : ℕ) (hn : n ∈ u) : d ∣ n := (Finset.mem_filter.mp hn).2
    have hinj : Set.InjOn (fun n : ℕ => n / d) u := by
      intro n hn m hm heq
      have hn' := Nat.div_mul_cancel (hdiv n hn)
      have hm' := Nat.div_mul_cancel (hdiv m hm)
      calc n = (n / d) * d := hn'.symm
        _ = (m / d) * d := congrArg (fun x : ℕ => x * d) heq
        _ = m := hm'
    have ht : ∀ r ∈ t, P / (d : ℝ) < (r : ℝ) := by
      intro r hr
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
      apply (div_lt_iff₀ hdR).mpr
      have heq : ((n / d : ℕ) : ℝ) * d = (n : ℝ) := by exact_mod_cast Nat.div_mul_cancel (hdiv n hn)
      rw [heq]
      exact (hs n (Finset.mem_filter.mp hn).1).2
    have heq : (∑ n ∈ u, correction d / (n : ℝ) ^ 2) =
        correction d / (d : ℝ) ^ 2 * ∑ r ∈ t, 1 / (r : ℝ) ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro n hn
      have heq : (n : ℝ) = ((n / d : ℕ) : ℝ) * d := by
        exact_mod_cast (Nat.div_mul_cancel (hdiv n hn)).symm
      rw [heq]
      ring
    calc
      _ = correction d / (d : ℝ) ^ 2 * ∑ r ∈ t, 1 / (r : ℝ) ^ 2 := heq
      _ ≤ correction d / (d : ℝ) ^ 2 * (2 / (P / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left (reciprocal_sq_tail _ (div_pos hP hdR) t ht)
          (div_nonneg (correction_nonneg d) (sq_nonneg _))
      _ = _ := by field_simp <;> ring
  calc
    _ = ∑ d ∈ D, ∑ n ∈ s with d ∣ n, correction d / (n : ℝ) ^ 2 := hdouble
    _ ≤ ∑ d ∈ D, 2 / P * (correction d / d) := Finset.sum_le_sum hinner
    _ = 2 / P * ∑ d ∈ D, correction d / d := by rw [Finset.mul_sum]
    _ ≤ 2 / P * T := mul_le_mul_of_nonneg_left
      (summable_correction_div.sum_le_tsum D (fun d _ => div_nonneg (correction_nonneg d) (Nat.cast_nonneg _)))
      (by positivity)
    _ ≤ 2 * (T + 1) / P := by
      apply (le_div_iff₀ hP).mpr
      have hP0 : P ≠ 0 := hP.ne'
      field_simp
      linarith

end
end LeanLab.Perelli1996.InverseTotient320
