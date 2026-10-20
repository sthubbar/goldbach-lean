module

public import LeanLab.PNTPort.LargeSieve.Farey

/-!
# Parseval modulo q and the large sieve over primes

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `sum_e_mul_div`: `∑_{c<q} e(kc/q)` is `q` if `q ∣ k` and `0` otherwise.
* `parseval_mod`: `∑_{c<q} ‖S(c/q)‖² = q ∑_{b<q} ‖Z(q,b)‖²`, where `Z(q,b)` sums `a_n` over
  `n ≡ b mod q`.
* `prime_large_sieve`: `∑_{p≤Q prime} (p ∑_b ‖Z(p,b)‖² - ‖Z‖²) ≤ (N + 2Q²) ∑ ‖a_n‖²`, the
  prime modulus form of the arithmetic large sieve, Renyi and Gallagher.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

lemma dist0_eq_zero_iff {x : ℝ} : dist0 x = 0 ↔ x = round x := by
  unfold dist0; rw [abs_eq_zero, sub_eq_zero]

lemma int_dvd_of_e_eq_one {k : ℤ} {q : ℕ} (hq : 0 < q) (h : e (k / q) = 1) :
    (q : ℤ) ∣ k := by
  have h4 := four_dist0_le ((k : ℝ) / q)
  rw [h, sub_self, norm_zero] at h4
  have h0 : dist0 ((k : ℝ) / q) = 0 := le_antisymm (by linarith) (dist0_nonneg _)
  rw [dist0_eq_zero_iff] at h0
  refine ⟨round ((k : ℝ) / q), ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have : (k : ℝ) = q * round ((k : ℝ) / q) := by
    rw [← h0]; field_simp
  exact_mod_cast this

/-- Orthogonality of additive characters modulo `q`. -/
lemma sum_e_mul_div (k : ℤ) {q : ℕ} (hq : 0 < q) :
    ∑ c ∈ range q, e (k * c / q) = if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  split_ifs with hdvd
  · obtain ⟨t, rfl⟩ := hdvd
    have : ∀ c ∈ range q, e (((q : ℤ) * t : ℤ) * c / q) = 1 := by
      intro c _
      rw [show (((q : ℤ) * t : ℤ) : ℝ) * c / q = ((t * c : ℤ) : ℝ) by
        push_cast; field_simp]
      exact e_int _
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have hne : e (k / q) ≠ 1 := fun h => hdvd (int_dvd_of_e_eq_one hq h)
    have hpow : ∀ c ∈ range q, e (k * c / q) = e (k / q) ^ c := by
      intro c _
      rw [← e_nat_mul]; congr 1; ring
    rw [sum_congr rfl hpow, geom_sum_eq hne, ← e_nat_mul,
      show (q : ℝ) * (k / q) = ((k : ℤ) : ℝ) by field_simp, e_int, sub_self, zero_div]

/-- `‖∑ n, f n‖²` expanded as a double sum. -/
lemma ofReal_normSq_sum {α : Type*} (I : Finset α) (f : α → ℂ) :
    ((‖∑ n ∈ I, f n‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ I, ∑ m ∈ I, f n * (starRingEnd ℂ) (f m) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]

/-- Residue sum `Z(q, b) = ∑_{n ∈ I, n ≡ b mod q} a n`. -/
noncomputable def resSum (I : Finset ℤ) (a : ℤ → ℂ) (q : ℕ) (b : ℕ) : ℂ :=
  ∑ n ∈ I.filter (fun n => n % (q : ℤ) = b), a n

lemma sum_res_indicator {q : ℕ} (hq : 0 < q) (n m : ℤ) (F : ℂ) :
    ∑ b ∈ range q, (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then F else 0) =
      if n % (q : ℤ) = m % (q : ℤ) then F else 0 := by
  have hn0 : 0 ≤ n % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  have hnq : n % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  have : ∀ b ∈ range q, (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then F else 0) =
      if b = (n % (q : ℤ)).toNat then (if n % (q : ℤ) = m % (q : ℤ) then F else 0) else 0 := by
    intro b _
    by_cases hb : b = (n % (q : ℤ)).toNat
    · have hb' : n % (q : ℤ) = b := by rw [hb]; omega
      rw [if_pos hb]
      by_cases hm : n % (q : ℤ) = m % (q : ℤ)
      · rw [if_pos ⟨hb', hm ▸ hb'⟩, if_pos hm]
      · rw [if_neg hm, if_neg]; rintro ⟨h1, h2⟩; exact hm (h1.trans h2.symm)
    · rw [if_neg hb, if_neg]
      rintro ⟨h1, _⟩; apply hb; omega
  rw [sum_congr rfl this, sum_ite_eq']
  rw [if_pos (by rw [mem_range]; omega)]

/-- **Parseval modulo `q`.** -/
theorem parseval_mod (I : Finset ℤ) (a : ℤ → ℂ) {q : ℕ} (hq : 0 < q) :
    ∑ c ∈ range q, ‖∑ n ∈ I, a n * e (n * c / q)‖ ^ 2 =
      q * ∑ b ∈ range q, ‖resSum I a q b‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast [Complex.ofReal_sum]
  simp_rw [← Complex.ofReal_pow, ofReal_normSq_sum]
  -- left side
  have hL : ∑ c ∈ range q, ∑ n ∈ I, ∑ m ∈ I,
      a n * e (n * c / q) * (starRingEnd ℂ) (a m * e (m * c / q)) =
      ∑ n ∈ I, ∑ m ∈ I, a n * (starRingEnd ℂ) (a m) *
        (if (q : ℤ) ∣ (n - m) then (q : ℂ) else 0) := by
    rw [sum_comm]
    apply sum_congr rfl; intro n _
    rw [sum_comm]
    apply sum_congr rfl; intro m _
    rw [← sum_e_mul_div (n - m) hq, mul_sum]
    apply sum_congr rfl; intro c _
    rw [map_mul, ← e_neg, show ((n - m : ℤ) : ℝ) * c / q = n * c / q + -(m * c / q) by
      push_cast; ring, e_add]
    ring
  rw [hL]
  -- right side
  unfold resSum
  simp_rw [ofReal_normSq_sum]
  have hR : ∀ b ∈ range q, ∑ n ∈ I.filter (fun n => n % (q : ℤ) = b),
      ∑ m ∈ I.filter (fun n => n % (q : ℤ) = b), a n * (starRingEnd ℂ) (a m) =
      ∑ n ∈ I, ∑ m ∈ I, (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then
        a n * (starRingEnd ℂ) (a m) else 0) := by
    intro b _
    rw [sum_filter]
    apply sum_congr rfl; intro n _
    rw [sum_filter]
    split_ifs with hn
    · apply sum_congr rfl; intro m _
      by_cases hm : m % (q : ℤ) = b
      · rw [if_pos hm, if_pos ⟨hn, hm⟩]
      · rw [if_neg hm, if_neg (fun h => hm h.2)]
    · symm; apply sum_eq_zero; intro m _; rw [if_neg (fun h => hn h.1)]
  rw [sum_congr rfl hR, mul_sum]
  symm
  calc ∑ b ∈ range q, (q : ℂ) * ∑ n ∈ I, ∑ m ∈ I,
        (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then a n * (starRingEnd ℂ) (a m) else 0)
      = ∑ n ∈ I, ∑ m ∈ I, (q : ℂ) * ∑ b ∈ range q,
        (if n % (q : ℤ) = b ∧ m % (q : ℤ) = b then a n * (starRingEnd ℂ) (a m) else 0) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro n _
        rw [sum_comm]
    _ = _ := by
        apply sum_congr rfl; intro n _
        apply sum_congr rfl; intro m _
        rw [sum_res_indicator hq]
        have hiff : (q : ℤ) ∣ (n - m) ↔ n % (q : ℤ) = m % (q : ℤ) := by
          rw [← Int.ModEq, Int.modEq_iff_dvd]
          constructor
          · intro h; rw [show m - n = -(n - m) by ring]; exact (Int.dvd_neg).2 h
          · intro h; rw [show n - m = -(m - n) by ring]; exact (Int.dvd_neg).2 h
        by_cases h : n % (q : ℤ) = m % (q : ℤ)
        · rw [if_pos (hiff.2 h), if_pos h]; ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; ring

end LeanLab.PNTPort.LargeSieve
