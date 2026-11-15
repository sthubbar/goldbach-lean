module

public import LeanLab.Tolev2009.CoefficientMoment314

/-!
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 18 to 19, the seven variable gcd substitution.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Gcd355

/-- Halupczok page 18, the two pairwise gcd quotients fit in the first modulus. -/
theorem gcd_quotient_product_dvd (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nat.gcd (Nat.gcd a b) c *
      (Nat.gcd a b / Nat.gcd (Nat.gcd a b) c) *
      (Nat.gcd a c / Nat.gcd (Nat.gcd a b) c) ∣ a := by
  let d := Nat.gcd (Nat.gcd a b) c
  have hd : 0 < d := Nat.gcd_pos_of_pos_left c (Nat.gcd_pos_of_pos_left b ha)
  have hab : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hac : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c ha
  have hdab : d ∣ Nat.gcd a b := Nat.gcd_dvd_left _ _
  have hdac : d ∣ Nat.gcd a c := by
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b))
      (Nat.gcd_dvd_right _ _)
  have hx : 0 < Nat.gcd a b / d := Nat.div_pos (Nat.le_of_dvd hab hdab) hd
  have hy : 0 < Nat.gcd a c / d := Nat.div_pos (Nat.le_of_dvd hac hdac) hd
  apply (Nat.factorization_le_iff_dvd (by positivity) ha.ne').mp
  intro p
  change (d * (Nat.gcd a b / d) * (Nat.gcd a c / d)).factorization p ≤ a.factorization p
  simp only [Nat.factorization_mul (Nat.mul_pos hd hx).ne' hy.ne',
    Nat.factorization_mul hd.ne' hx.ne', Nat.factorization_div hdab,
    Nat.factorization_div hdac, Finsupp.add_apply, Finsupp.tsub_apply]
  dsimp only [d]
  simp only [Nat.factorization_gcd ha.ne' hb.ne', Nat.factorization_gcd ha.ne' hc.ne',
    Nat.factorization_gcd hab.ne' hc.ne', Finsupp.inf_apply]
  omega

/-- Halupczok page 18, the prime valuations of the gcd denominator cancel exactly. -/
theorem gcd_lcm_identity (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nat.gcd a b * Nat.gcd a c * Nat.gcd b c * Nat.lcm (Nat.lcm a b) c =
      a * b * c * Nat.gcd (Nat.gcd a b) c := by
  have hab : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hac : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c ha
  have hbc : 0 < Nat.gcd b c := Nat.gcd_pos_of_pos_left c hb
  have hd : 0 < Nat.gcd (Nat.gcd a b) c := Nat.gcd_pos_of_pos_left c hab
  have hlab : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have hl : 0 < Nat.lcm (Nat.lcm a b) c := Nat.lcm_pos hlab hc
  apply Nat.eq_of_factorization_eq (by positivity) (by positivity)
  intro p
  simp only [Nat.factorization_mul (Nat.mul_pos (Nat.mul_pos hab hac) hbc).ne' hl.ne',
    Nat.factorization_mul (Nat.mul_pos hab hac).ne' hbc.ne',
    Nat.factorization_mul hab.ne' hac.ne',
    Nat.factorization_mul (Nat.mul_pos (Nat.mul_pos ha hb) hc).ne' hd.ne',
    Nat.factorization_mul (Nat.mul_pos ha hb).ne' hc.ne', Nat.factorization_mul ha.ne' hb.ne',
    Nat.factorization_gcd ha.ne' hb.ne', Nat.factorization_gcd ha.ne' hc.ne',
    Nat.factorization_gcd hb.ne' hc.ne', Nat.factorization_gcd hab.ne' hc.ne',
    Nat.factorization_lcm hlab.ne' hc.ne', Nat.factorization_lcm ha.ne' hb.ne',
    Finsupp.add_apply, Finsupp.inf_apply, Finsupp.sup_apply]
  omega

/-- Halupczok pages 18 to 19, the exact seven factor representation of three moduli.
The first four factors are fixed by their common and pairwise gcds. -/
theorem exists_gcd_factors (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ t : Fin 7 → ℕ, (∀ i, 1 ≤ t i) ∧
      a = t 0 * t 1 * t 2 * t 4 ∧ b = t 0 * t 1 * t 3 * t 5 ∧
      c = t 0 * t 2 * t 3 * t 6 ∧
      Nat.gcd a b = t 0 * t 1 ∧ Nat.gcd a c = t 0 * t 2 ∧
      Nat.gcd b c = t 0 * t 3 ∧ Nat.gcd (Nat.gcd a b) c = t 0 := by
  let d := Nat.gcd (Nat.gcd a b) c
  let x := Nat.gcd a b / d
  let y := Nat.gcd a c / d
  let z := Nat.gcd b c / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left c (Nat.gcd_pos_of_pos_left b ha)
  have hdab : d ∣ Nat.gcd a b := Nat.gcd_dvd_left _ _
  have hdac : d ∣ Nat.gcd a c :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b)) (Nat.gcd_dvd_right _ _)
  have hdbc : d ∣ Nat.gcd b c :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a b)) (Nat.gcd_dvd_right _ _)
  have hx : 0 < x := Nat.div_pos (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b ha) hdab) hd
  have hy : 0 < y := Nat.div_pos (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left c ha) hdac) hd
  have hz : 0 < z := Nat.div_pos (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left c hb) hdbc) hd
  have ha' : d * x * y ∣ a := gcd_quotient_product_dvd a b c ha hb hc
  have hb' : d * x * z ∣ b := by
    simpa only [Nat.gcd_comm b a] using gcd_quotient_product_dvd b a c hb ha hc
  have hc' : d * y * z ∣ c := by
    have he : Nat.gcd (Nat.gcd c a) b = d := by
      dsimp only [d]
      ac_rfl
    have H := gcd_quotient_product_dvd c a b hc ha hb
    rw [he] at H
    simpa only [Nat.gcd_comm c a, Nat.gcd_comm c b] using H
  let e := a / (d * x * y)
  let f := b / (d * x * z)
  let g := c / (d * y * z)
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd ha ha') (by positivity)
  have hf : 0 < f := Nat.div_pos (Nat.le_of_dvd hb hb') (by positivity)
  have hg : 0 < g := Nat.div_pos (Nat.le_of_dvd hc hc') (by positivity)
  refine ⟨![d, x, y, z, e, f, g], ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> assumption
  · exact (Nat.mul_div_cancel' ha').symm
  · exact (Nat.mul_div_cancel' hb').symm
  · exact (Nat.mul_div_cancel' hc').symm
  · exact (Nat.mul_div_cancel' hdab).symm
  · exact (Nat.mul_div_cancel' hdac).symm
  · exact (Nat.mul_div_cancel' hdbc).symm

/-- Halupczok pages 18 to 19, each positive factor stays below the original modulus cube. -/
theorem factors_le (t : Fin 7 → ℕ) (ht : ∀ i, 1 ≤ t i) (a b c N : ℕ)
    (ha : a = t 0 * t 1 * t 2 * t 4) (hb : b = t 0 * t 1 * t 3 * t 5)
    (hc : c = t 0 * t 2 * t 3 * t 6) (haN : a ≤ N) (hbN : b ≤ N) (hcN : c ≤ N) :
    ∀ i, t i ≤ N := by
  have hle (w x y z : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) : w ≤ w * x * y * z := by
    exact (Nat.le_mul_of_pos_right w hx).trans
      ((Nat.le_mul_of_pos_right (w * x) hy).trans (Nat.le_mul_of_pos_right (w * x * y) hz))
  have h0 : t 0 ≤ a := by rw [ha]; exact hle _ _ _ _ (ht 1) (ht 2) (ht 4)
  have h1 : t 1 ≤ a := by
    rw [ha]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hle (t 1) (t 0) (t 2) (t 4) (ht 0) (ht 2) (ht 4)
  have h2 : t 2 ≤ a := by
    rw [ha]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hle (t 2) (t 0) (t 1) (t 4) (ht 0) (ht 1) (ht 4)
  have h3 : t 3 ≤ b := by
    rw [hb]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hle (t 3) (t 0) (t 1) (t 5) (ht 0) (ht 1) (ht 5)
  have h4 : t 4 ≤ a := by
    rw [ha]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hle (t 4) (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2)
  have h5 : t 5 ≤ b := by
    rw [hb]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hle (t 5) (t 0) (t 1) (t 3) (ht 0) (ht 1) (ht 3)
  have h6 : t 6 ≤ c := by
    rw [hc]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hle (t 6) (t 0) (t 2) (t 3) (ht 0) (ht 2) (ht 3)
  intro i
  fin_cases i
  · exact h0.trans haN
  · exact h1.trans haN
  · exact h2.trans haN
  · exact h3.trans hbN
  · exact h4.trans haN
  · exact h5.trans hbN
  · exact h6.trans hcN

/-- Halupczok page 18, the divisor count of a four factor product is submultiplicative. -/
theorem divisor_count_four (w x y z : ℕ) :
    ((w * x * y * z).divisors.card : ℝ) ≤
      (w.divisors.card : ℝ) * x.divisors.card * y.divisors.card * z.divisors.card := by
  open LeanLab.HeathBrown1985 in
  calc
    _ ≤ ((w * x * y).divisors.card : ℝ) * z.divisors.card := by
      exact_mod_cast card_divisors_mul_le (w * x * y) z
    _ ≤ (((w * x).divisors.card : ℝ) * y.divisors.card) * z.divisors.card := by
      gcongr
      exact_mod_cast card_divisors_mul_le (w * x) y
    _ ≤ _ := by
      gcongr
      exact_mod_cast card_divisors_mul_le w x

end LeanLab.Tolev2009.Gcd355
