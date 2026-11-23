module

public import LeanLab.SchnirelmannGoldbach.S3

/-!
S2, mean square of the singular product is linear.
AI-written Lean code, Claude, 2026-10-16.
-/

@[expose] public section

open Finset Real
namespace LeanLab.SchnirelmannGoldbach

/-- `singProd n ≤ σ(n)/n`. -/
lemma singProd_le_sum_divisors (n : ℕ) (hn : n ≠ 0) :
    singProd n ≤ ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  classical
  unfold singProd
  have h1 : ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) =
      ∑ t ∈ n.primeFactors.powerset, 1 / (((∏ p ∈ t, p : ℕ)) : ℝ) := by
    rw [show (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) =
        ∏ p ∈ n.primeFactors, (1 / (p : ℝ) + 1) by simp [add_comm], Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    simp [Finset.prod_inv_distrib]
  rw [h1]
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (n.primeFactors.powerset : Set (Finset ℕ)) := by
    intro t ht t' ht' h
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at ht ht'
    have e1 := Nat.primeFactors_prod (s := t) (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))
    have e2 := Nat.primeFactors_prod (s := t') (fun p hp => Nat.prime_of_mem_primeFactors (ht' hp))
    simp only at h
    rw [← e1, ← e2, h]
  rw [← Finset.sum_image (f := fun d : ℕ => 1 / (d : ℝ)) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [mem_image, mem_powerset] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    rw [Nat.mem_divisors]
    exact ⟨(Finset.prod_dvd_prod_of_subset _ _ id ht).trans (Nat.prod_primeFactors_dvd n), hn⟩
  · intro _ _ _; positivity

/-- weight `1/(d √d)`. -/
noncomputable def g (d : ℕ) : ℝ := 1 / ((d : ℝ) * √(d : ℝ))

lemma g_nonneg (d : ℕ) : 0 ≤ g d := by unfold g; positivity

lemma g_summable : Summable g := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine Summable.of_nonneg_of_le g_nonneg (fun d => ?_) hs
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [g]
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have : (d : ℝ) ^ ((3 : ℝ) / 2) = (d : ℝ) * √(d : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hd',
        Real.rpow_one]
    rw [this, g, one_div]

lemma card_dvd (N d : ℕ) : (#{n ∈ Icc 1 N | d ∣ n} : ℝ) ≤ N / d := by
  have : (Icc 1 N) = Ioc 0 N := rfl
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

lemma pair_le_aux (N d1 d2 : ℕ) (h1 : 1 ≤ d1) :
    ∑ n ∈ Icc 1 N, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
      ≤ N / ((d1 : ℝ) * d2 * d2) := by
  have hd1 : (0 : ℝ) < d1 := by exact_mod_cast h1
  calc ∑ n ∈ Icc 1 N, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
      ≤ ∑ n ∈ Icc 1 N, 1 / (d1 : ℝ) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
        apply Finset.sum_le_sum; intro n _
        apply mul_le_mul_of_nonneg_right
        · split_ifs
          · exact le_rfl
          · positivity
        · split_ifs <;> positivity
    _ = 1 / (d1 : ℝ) * (1 / d2) * #{n ∈ Icc 1 N | d2 ∣ n} := by
        rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]; ring
    _ ≤ 1 / (d1 : ℝ) * (1 / d2) * (N / d2) := by
        gcongr; exact card_dvd N d2
    _ = N / ((d1 : ℝ) * d2 * d2) := by field_simp

lemma g_mul_bound (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 : ℝ) / (a * b * b) ≤ g a * g b := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb' : (1 : ℝ) ≤ b := ha'.trans hab'
  unfold g
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le
  · have : 0 < √(a : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have : 0 < √(b : ℝ) := Real.sqrt_pos.mpr (by linarith)
    positivity
  · have hs : √(a : ℝ) ≤ √(b : ℝ) := Real.sqrt_le_sqrt hab'
    have hbb : √(b : ℝ) * √(b : ℝ) = b := Real.mul_self_sqrt (by linarith)
    have h0 : 0 ≤ √(b : ℝ) := Real.sqrt_nonneg _
    have hab0 : (0 : ℝ) ≤ a * b := by positivity
    calc (a : ℝ) * √a * (b * √b) = a * b * (√a * √b) := by ring
      _ ≤ a * b * (√b * √b) := by gcongr
      _ = a * b * b := by rw [hbb]

lemma pair_le (N d1 d2 : ℕ) (h1 : 1 ≤ d1) (h2 : 1 ≤ d2) :
    ∑ n ∈ Icc 1 N, (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0)
      ≤ N * (g d1 * g d2) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases le_total d1 d2 with h | h
  · refine (pair_le_aux N d1 d2 h1).trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (g_mul_bound d1 d2 h1 h) hN
  · have := pair_le_aux N d2 d1 h2
    simp_rw [mul_comm (if d2 ∣ _ then _ else _)] at this
    refine this.trans ?_
    rw [div_eq_mul_one_div, mul_comm (g d1)]
    exact mul_le_mul_of_nonneg_left (g_mul_bound d2 d1 h2 h) hN

theorem S2_holds : S2 := by
  refine ⟨(∑' d, g d) ^ 2, fun N _ => ?_⟩
  have key : ∀ n ∈ Icc 1 N, singProd n ^ 2 ≤
      ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
    intro n hn
    rw [mem_Icc] at hn
    have hsum : ∑ d ∈ n.divisors, 1 / (d : ℝ) =
        ∑ d ∈ Icc 1 N, (if d ∣ n then 1 / (d : ℝ) else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
      · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
    rw [← Finset.sum_mul_sum, ← sq, ← hsum]
    gcongr
    · exact singProd_nonneg n
    · exact singProd_le_sum_divisors n (by omega)
  calc ∑ n ∈ Icc 1 N, singProd n ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) :=
        Finset.sum_le_sum key
    _ = ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro _ _; rw [Finset.sum_comm]
    _ ≤ ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N, (N : ℝ) * (g d1 * g d2) := by
        apply Finset.sum_le_sum; intro d1 hd1; apply Finset.sum_le_sum; intro d2 hd2
        exact pair_le N d1 d2 (mem_Icc.mp hd1).1 (mem_Icc.mp hd2).1
    _ = N * (∑ d ∈ Icc 1 N, g d) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro _ _; rw [Finset.mul_sum]
    _ ≤ N * (∑' d, g d) ^ 2 := by
        gcongr
        · exact Finset.sum_nonneg (fun d _ => g_nonneg d)
        · exact g_summable.sum_le_tsum _ (fun d _ => g_nonneg d)
    _ = (∑' d, g d) ^ 2 * N := by ring

end LeanLab.SchnirelmannGoldbach
