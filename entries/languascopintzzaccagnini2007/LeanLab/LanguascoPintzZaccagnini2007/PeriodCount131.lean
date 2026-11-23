module

public import LeanLab.LanguascoPintzZaccagnini2007.Truncation131

/-!
P0045 displays 18 to 20 on page 8. Counting in complete exponent periods.
The argument adapts the earlier LPZ2007.D4Count proof to this folder definitions.
Mathlib has no matching finite periodic sum lemma in the source search.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset

/-- One complete period repeated q times in the exponent interval of display 18. -/
theorem sum_Icc_mul131 {F : ℕ → ℕ} {ξ : ℕ} (hF : ∀ a, F (a + ξ) = F a) (q : ℕ) :
    ∑ a ∈ Icc 1 (q * ξ), F a = q * ∑ b ∈ Icc 1 ξ, F b := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Icc 1 ((q + 1) * ξ) = Icc 1 (q * ξ) ∪ Icc (q * ξ + 1) (q * ξ + ξ) := by
      ext a
      simp only [mem_union, mem_Icc]
      constructor
      · intro h
        by_cases ha : a ≤ q * ξ
        · exact Or.inl ⟨h.1, ha⟩
        · right; constructor <;> nlinarith
      · rintro (h | h) <;> constructor <;> nlinarith
    have hdisj : Disjoint (Icc 1 (q * ξ)) (Icc (q * ξ + 1) (q * ξ + ξ)) := by
      rw [disjoint_left]
      intro a h1 h2
      simp only [mem_Icc] at h1 h2
      omega
    have hshift : ∀ m : ℕ, ∑ a ∈ Icc (m * ξ + 1) (m * ξ + ξ), F a = ∑ b ∈ Icc 1 ξ, F b := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [← ihm]
        have he : Icc ((m + 1) * ξ + 1) ((m + 1) * ξ + ξ) =
            (Icc (m * ξ + 1) (m * ξ + ξ)).map (addRightEmbedding ξ) := by
          rw [map_add_right_Icc]
          congr 1 <;> ring
        rw [he, sum_map]
        exact sum_congr rfl (fun a _ => hF a)
    rw [hsplit, sum_union hdisj, ih, hshift q]
    ring

/-- A nonnegative periodic sum over an arbitrary initial interval lies between
q and q+1 complete periods, with q = floor(M/xi). -/
theorem sum_Icc_periodic131 {F : ℕ → ℕ} {ξ : ℕ} (hξ : 0 < ξ)
    (hF : ∀ a, F (a + ξ) = F a) (M : ℕ) :
    (M / ξ) * ∑ b ∈ Icc 1 ξ, F b ≤ ∑ a ∈ Icc 1 M, F a ∧
      ∑ a ∈ Icc 1 M, F a ≤ (M / ξ + 1) * ∑ b ∈ Icc 1 ξ, F b := by
  have h1 : M / ξ * ξ ≤ M := Nat.div_mul_le_self M ξ
  have h2 : M ≤ (M / ξ + 1) * ξ := by
    have := Nat.lt_div_mul_add hξ (a := M)
    nlinarith
  constructor
  · rw [← sum_Icc_mul131 hF]
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h1) (fun _ _ _ => Nat.zero_le _)
  · rw [← sum_Icc_mul131 hF]
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h2) (fun _ _ _ => Nat.zero_le _)

/-- The recursive tuple count depends only on the residue modulo d. -/
theorem Gcount_congr131 (d M k : ℕ) {r s : ℤ} (h : (d : ℤ) ∣ r - s) :
    Gcount d M k r = Gcount d M k s := by
  rw [← card_eq_Gcount, ← card_eq_Gcount]
  congr 1
  apply filter_congr
  intro ν _
  have he : r - ∑ i, (2 : ℤ) ^ ν i = (r - s) + (s - ∑ i, (2 : ℤ) ^ ν i) := by ring
  rw [he]
  exact ⟨fun ht => by simpa using dvd_sub ht h, fun ht => dvd_add h ht⟩

/-- Displays 18 to 20: q^k copies of the complete period count give a lower bound,
and q+1 to the kth power gives an upper bound, where q = floor(M/xi). -/
theorem Gcount_period_bounds131 {d ξ : ℕ} (hξ : 0 < ξ) (h2 : (d : ℤ) ∣ 1 - (2 : ℤ) ^ ξ)
    (M k : ℕ) (r : ℤ) :
    (M / ξ) ^ k * Gcount d ξ k r ≤ Gcount d M k r ∧
      Gcount d M k r ≤ (M / ξ + 1) ^ k * Gcount d ξ k r := by
  induction k generalizing r with
  | zero => simp [Gcount]
  | succ k ih =>
    have hper : ∀ a, Gcount d ξ k (r - 2 ^ (a + ξ)) = Gcount d ξ k (r - 2 ^ a) := by
      intro a
      apply Gcount_congr131
      have ht := dvd_mul_of_dvd_left h2 ((2 : ℤ) ^ a)
      convert ht using 1
      rw [pow_add]
      ring
    obtain ⟨hlo, hhi⟩ := sum_Icc_periodic131 (F := fun a => Gcount d ξ k (r - 2 ^ a)) hξ hper M
    change (M / ξ) ^ (k + 1) * (∑ a ∈ Icc 1 ξ, Gcount d ξ k (r - 2 ^ a)) ≤
        (∑ a ∈ Icc 1 M, Gcount d M k (r - 2 ^ a)) ∧
      (∑ a ∈ Icc 1 M, Gcount d M k (r - 2 ^ a)) ≤
        (M / ξ + 1) ^ (k + 1) * (∑ a ∈ Icc 1 ξ, Gcount d ξ k (r - 2 ^ a))
    constructor
    · calc (M / ξ) ^ (k + 1) * ∑ a ∈ Icc 1 ξ, Gcount d ξ k (r - 2 ^ a)
          = (M / ξ) ^ k * ((M / ξ) * ∑ a ∈ Icc 1 ξ, Gcount d ξ k (r - 2 ^ a)) := by ring
        _ ≤ (M / ξ) ^ k * ∑ a ∈ Icc 1 M, Gcount d ξ k (r - 2 ^ a) := Nat.mul_le_mul_left _ hlo
        _ = ∑ a ∈ Icc 1 M, (M / ξ) ^ k * Gcount d ξ k (r - 2 ^ a) := by rw [mul_sum]
        _ ≤ _ := sum_le_sum (fun a _ => (ih _).1)
    · calc ∑ a ∈ Icc 1 M, Gcount d M k (r - 2 ^ a)
          ≤ ∑ a ∈ Icc 1 M, (M / ξ + 1) ^ k * Gcount d ξ k (r - 2 ^ a) :=
            sum_le_sum (fun a _ => (ih _).2)
        _ = (M / ξ + 1) ^ k * ∑ a ∈ Icc 1 M, Gcount d ξ k (r - 2 ^ a) := by rw [mul_sum]
        _ ≤ (M / ξ + 1) ^ k * ((M / ξ + 1) * ∑ a ∈ Icc 1 ξ, Gcount d ξ k (r - 2 ^ a)) :=
            Nat.mul_le_mul_left _ hhi
        _ = _ := by ring

/-- The modular tuple count in display 17, with signed subtraction. -/
noncomputable def residueTupleCount131 (d k M N : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Icc 1 M)).filter
    (fun ν => (d : ℤ) ∣ (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i)).card

/-- The modular tuple count is exactly the existing recursive count. -/
theorem residueTupleCount_eq131 (d k M N : ℕ) :
    residueTupleCount131 d k M N = Gcount d M k N := card_eq_Gcount d M k N

/-- Display 20 before summing over d, with k+1 exponents to match the lab jcount convention. -/
theorem block_jcount_bounds131 {d : ℕ} (hd : Odd d) (k M N : ℕ) :
    (M / xi d) ^ (k + 1) * jcount d k N ≤ residueTupleCount131 d (k + 1) M N ∧
      residueTupleCount131 d (k + 1) M N ≤ (M / xi d + 1) ^ (k + 1) * jcount d k N := by
  rw [residueTupleCount_eq131, jcount_eq_Gcount]
  have ht : (d : ℤ) ∣ 1 - (2 : ℤ) ^ xi d := by
    have ht := Nat.modEq_iff_dvd.mp (xi_spec hd).2
    exact_mod_cast ht
  exact Gcount_period_bounds131 (xi_spec hd).1 ht M (k + 1) N

/-- Display 20: an explicit error for one modulus, uniform in the target residue N. -/
theorem block_jcount_error131 {d : ℕ} (hd : Odd d) (k M N : ℕ) :
    |(residueTupleCount131 d (k + 1) M N : ℝ) -
      (jcount d k N : ℝ) * ((M : ℝ) / xi d) ^ (k + 1)| ≤
        (jcount d k N : ℝ) * (k + 1) * ((M / xi d : ℕ) + (1 : ℝ)) ^ k := by
  let q := M / xi d
  let j := jcount d k N
  let x := (M : ℝ) / xi d
  have hxi : (0 : ℝ) < xi d := by exact_mod_cast (xi_spec hd).1
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hqx : (q : ℝ) ≤ x := by
    apply (le_div_iff₀ hxi).mpr
    exact_mod_cast Nat.div_mul_le_self M (xi d)
  have hxq : x ≤ (q : ℝ) + 1 := by
    apply (div_le_iff₀ hxi).mpr
    have h : M ≤ (q + 1) * xi d := by
      have ht := Nat.lt_div_mul_add ((xi_spec hd).1 : 0 < xi d) (a := M)
      dsimp [q]
      nlinarith
    exact_mod_cast h
  have hb := block_jcount_bounds131 hd k M N
  have hlo : (q : ℝ) ^ (k + 1) * j ≤ residueTupleCount131 d (k + 1) M N := by exact_mod_cast hb.1
  have hhi : (residueTupleCount131 d (k + 1) M N : ℝ) ≤ ((q : ℝ) + 1) ^ (k + 1) * j := by exact_mod_cast hb.2
  have hmidlo := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hqx (k + 1)) hj0
  have hmidhi := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hxq (k + 1)) hj0
  have hp := abs_pow_sub_pow_le (a := (q : ℝ) + 1) (b := (q : ℝ)) (n := k + 1)
  have hpow : (q : ℝ) ^ (k + 1) ≤ ((q : ℝ) + 1) ^ (k + 1) := pow_le_pow_left₀ hq0 (by linarith) _
  simp only [abs_of_nonneg (sub_nonneg.mpr hpow),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) + 1), abs_of_nonneg hq0,
    max_eq_left (by linarith : (q : ℝ) ≤ (q : ℝ) + 1), Nat.add_sub_cancel,
    add_sub_cancel_left, abs_one, one_mul, Nat.cast_add, Nat.cast_one] at hp
  have he : |(residueTupleCount131 d (k + 1) M N : ℝ) - j * x ^ (k + 1)| ≤
      j * (((q : ℝ) + 1) ^ (k + 1) - (q : ℝ) ^ (k + 1)) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hj0])

end LeanLab.LPZ2007
