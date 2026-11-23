module

public import LeanLab.Perelli1996.InverseTotient320
public import LeanLab.Perelli1996.Tail320
public import LeanLab.Perelli1996.Sing

/-!
Perelli 1996, page 481 equations 2 and 3.
The Ramanujan expansion and its absolute tail at a positive frequency.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Series320
open Finset
noncomputable section

/-- Page 481 equations 2 and 3, the natural frequency Ramanujan coefficient. -/
def coefficient (m q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
    Ramanujan103.ramanujanSum q m

/-- The zero modulus contributes zero. -/
theorem coefficient_zero (m : ℕ) : coefficient m 0 = 0 := by simp [coefficient]

/-- The modulus one contributes one. -/
theorem coefficient_one (m : ℕ) : coefficient m 1 = 1 := by
  rw [coefficient, Ramanujan103.ramanujanSum_dvd 1 m (by norm_num) (one_dvd m)]
  simp

/-- The coefficient is multiplicative in its modulus. -/
theorem coefficient_mul (m q r : ℕ) (hcop : Nat.Coprime q r) :
    coefficient m (q * r) = coefficient m q * coefficient m r := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [coefficient_zero]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [coefficient_zero]
  unfold coefficient
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop, Ramanujan103.ramanujanSum_mul q r m hq hr hcop]
  push_cast
  ring

/-- The coefficient vanishes at nonsquarefree moduli. -/
theorem coefficient_nonsquarefree (m q : ℕ) (hq : ¬ Squarefree q) : coefficient m q = 0 := by
  simp [coefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

/-- The prime factor of the Ramanujan series is the prime factor of Sing. -/
theorem coefficient_prime (m p : ℕ) (hp : p.Prime) :
    1 + coefficient m p = (singF m ⟨p, hp⟩ : ℂ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1R : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp1 : (p : ℂ) - 1 ≠ 0 := by exact_mod_cast hp1R
  rw [coefficient, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp, Ramanujan103.ramanujanSum_prime p m hp]
  rw [Nat.cast_sub hp.one_le]
  simp only [Nat.cast_one, Int.cast_neg, Int.cast_one, neg_one_sq]
  unfold singF
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- The norm of every finite coefficient tail obeys the divisor totient majorant. -/
theorem sum_norm_tail (m : ℕ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℝ, 0 < P → ∀ s : Finset ℕ,
      (∀ q ∈ s, 0 < q ∧ P < (q : ℝ)) →
      (∑ q ∈ s, ‖coefficient m q‖) ≤
        K / P * ((m : ℝ) * m.divisors.card / m.totient) := by
  obtain ⟨K, hK, htail⟩ := InverseTotient320.inverse_totient_sq_tail
  refine ⟨K, hK, ?_⟩
  intro P hP s hs
  calc
    _ ≤ ∑ q ∈ s, 1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient) :=
      Finset.sum_le_sum (fun q hq => Ramanujan400.norm_weighted_ramanujanSum_le q m (hs q hq).1)
    _ ≤ _ := Tail320.finite_totient_tail m hm P K hP htail s hs

/-- The Ramanujan coefficient series is absolutely convergent at a positive frequency. -/
theorem summable_norm_coefficient (m : ℕ) (hm : 0 < m) :
    Summable (fun q : ℕ => ‖coefficient m q‖) := by
  obtain ⟨K, hK, htail⟩ := sum_norm_tail m hm
  apply summable_of_sum_le (fun q => norm_nonneg _) (c := K / (1 / 2) *
    ((m : ℝ) * m.divisors.card / m.totient))
  intro s
  have hfilter : (∑ q ∈ s, ‖coefficient m q‖) =
      ∑ q ∈ s.filter (fun q => 0 < q), ‖coefficient m q‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have hq0 : q = 0 := by simp only [Finset.mem_filter, hq, true_and] at hnot; omega
    simp [hq0, coefficient_zero]
  rw [hfilter]
  apply htail (1 / 2) (by norm_num)
  intro q hq
  have hpos := (Finset.mem_filter.mp hq).2
  refine ⟨hpos, ?_⟩
  have h : (1 : ℝ) ≤ q := by exact_mod_cast hpos
  linarith

/-- The full Ramanujan series is the existing prime product Sing. -/
theorem tsum_coefficient (m : ℕ) (hm : 0 < m) :
    (∑' q : ℕ, coefficient m q) = (Sing m : ℂ) := by
  have heuler := EulerProduct.eulerProduct_tprod (f := coefficient m) (coefficient_one m)
    (fun {_ _} h => coefficient_mul m _ _ h) (summable_norm_coefficient m hm) (coefficient_zero m)
  have hfactor (p : Nat.Primes) : (∑' e : ℕ, coefficient m (p.1 ^ e)) =
      (singF m p : ℂ) := by
    have hzero (e : ℕ) (he : e ∉ ({0, 1} : Finset ℕ)) : coefficient m (p.1 ^ e) = 0 := by
      apply coefficient_nonsquarefree
      have he2 : 2 ≤ e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
      rw [Nat.squarefree_pow_iff p.2.ne_one (by omega)]
      simp only [not_and]
      intro _
      omega
    rw [tsum_eq_sum hzero, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), pow_zero, pow_one,
      coefficient_one]
    simpa only [singF] using coefficient_prime m p.1 p.2
  calc
    _ = ∏' p : Nat.Primes, ∑' e : ℕ, coefficient m (p.1 ^ e) := heuler.symm
    _ = ∏' p : Nat.Primes, (singF m p : ℂ) := tprod_congr hfactor
    _ = (Sing m : ℂ) := by
      rw [sing_eq]
      exact ((sing_multipliable hm.ne').map_tprod Complex.ofRealHom Complex.continuous_ofReal).symm

/-- The finite singular series approximates Sing with the exact inverse cutoff loss. -/
theorem partial_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ P : ℝ, 1 ≤ P →
      ‖(Sing m : ℂ) - ∑ q ∈ Icc 1 ⌊P⌋₊, coefficient m q‖ ≤
        K * ((m : ℝ) * m.divisors.card / m.totient) / P := by
  obtain ⟨K, hK, htail⟩ := InverseTotient320.inverse_totient_sq_tail
  refine ⟨K, hK, ?_⟩
  intro m hm P hP
  have hP0 : 0 < P := by linarith
  have hnorm := summable_norm_coefficient m hm
  have hs := hnorm.of_norm
  let s := Icc 1 ⌊P⌋₊
  have hsplit := hs.sum_add_tsum_subtype_compl s
  rw [tsum_coefficient m hm] at hsplit
  have hid : (Sing m : ℂ) - ∑ q ∈ s, coefficient m q =
      ∑' q : {q : ℕ // q ∉ s}, coefficient m q := by
    rw [← hsplit]
    ring
  rw [hid]
  calc
    _ ≤ ∑' q : {q : ℕ // q ∉ s}, ‖coefficient m q‖ :=
      norm_tsum_le_tsum_norm (hnorm.subtype _)
    _ ≤ K * ((m : ℝ) * m.divisors.card / m.totient) / P := by
      apply Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
      intro u
      let v : Finset ℕ := (u.image Subtype.val).filter (fun q => 0 < q)
      have hmap : (∑ q ∈ u, ‖coefficient m q‖) = ∑ q ∈ v, ‖coefficient m q‖ := by
        calc
          _ = ∑ q ∈ u.image Subtype.val, ‖coefficient m q‖ :=
            (Finset.sum_image (f := fun q : ℕ => ‖coefficient m q‖)
              (fun a _ b _ h => Subtype.ext h)).symm
          _ = ∑ q ∈ v, ‖coefficient m q‖ := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro q hq hnot
            have hq0 : q = 0 := by simp only [Finset.mem_filter, hq, true_and] at hnot; omega
            simp [hq0, coefficient_zero]
      rw [hmap]
      have hv : ∀ q ∈ v, 0 < q ∧ P < (q : ℝ) := by
        intro q hq
        obtain ⟨hqmem, hqpos⟩ := Finset.mem_filter.mp hq
        obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hqmem
        have hnot := r.2
        have hqfloor : ⌊P⌋₊ < q := by
          simp only [s, Finset.mem_Icc] at hnot
          rw [hrq] at hnot
          omega
        refine ⟨hqpos, ?_⟩
        exact (Nat.lt_floor_add_one P).trans_le (by exact_mod_cast (show ⌊P⌋₊ + 1 ≤ q by omega))
      calc
        _ ≤ ∑ q ∈ v, 1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient) :=
          Finset.sum_le_sum (fun q hq => Ramanujan400.norm_weighted_ramanujanSum_le q m (hv q hq).1)
        _ ≤ K / P * ((m : ℝ) * m.divisors.card / m.totient) :=
          Tail320.finite_totient_tail m hm P K hP0 htail v hv
        _ = _ := by ring

end
end LeanLab.Perelli1996.Series320
