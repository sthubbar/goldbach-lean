module

public import LeanLab.PNTPort.LargeSieve.Dual

/-!
# The large sieve at Farey fractions

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

The reduced fractions `a/q` with `1 ≤ q ≤ Q`, `0 ≤ a < q`, `gcd(a, q) = 1` are `1/Q²`-spaced
modulo one, so

  `∑_{q ≤ Q} ∑_{a mod q, (a,q)=1} ‖∑_{M<n≤M+N} a_n e(n a/q)‖² ≤ (N + 2Q²) ∑_n ‖a_n‖²`.

This is the form used for Bombieri-Vinogradov; the sharp constant is `N - 1 + Q²`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

/-- The pairs `(q, a)` with `1 ≤ q ≤ Q`, `a < q`, `gcd(a, q) = 1`. -/
def farey (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q) ×ˢ (range Q)).filter (fun p => p.2 < p.1 ∧ Nat.Coprime p.2 p.1)

/-- The fraction `a/q` of a pair `(q, a)`. -/
noncomputable def fareyPt (p : ℕ × ℕ) : ℝ := (p.2 : ℝ) / p.1

lemma mem_farey {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ farey Q ↔ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1 := by
  unfold farey
  rw [mem_filter, mem_product, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, _⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, by omega⟩, h3, h4⟩

/-- Distinct reduced fractions with denominators at most `Q` are `1/Q²` apart mod one. -/
lemma farey_spaced (Q : ℕ) : Spaced (farey Q) fareyPt (1 / (Q : ℝ) ^ 2) := by
  rintro ⟨q, a⟩ hp ⟨q', a'⟩ hp' hne
  rw [mem_farey] at hp hp'
  obtain ⟨hq1, hqQ, haq, hcop⟩ := hp
  obtain ⟨hq1', hqQ', haq', hcop'⟩ := hp'
  simp only at hq1 hqQ haq hcop hq1' hqQ' haq' hcop'
  simp only [fareyPt]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqpos' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  set m : ℤ := round ((a : ℝ) / q - a' / q') with hm
  set j : ℤ := (a : ℤ) * q' - a' * q - m * q * q' with hj
  have hx : (a : ℝ) / q - a' / q' - m = j / (q * q') := by
    rw [hj]; push_cast; field_simp
  have hj0 : j ≠ 0 := by
    intro hj0
    rw [hj0, Int.cast_zero, zero_div, sub_eq_zero] at hx
    -- `a/q - a'/q'` is an integer of absolute value below one, hence zero
    have hlt1 : |(a : ℝ) / q - a' / q'| < 1 := by
      have h1 : (a : ℝ) / q < 1 := by
        rw [div_lt_one hqpos]; exact_mod_cast haq
      have h2 : (a' : ℝ) / q' < 1 := by
        rw [div_lt_one hqpos']; exact_mod_cast haq'
      have h3 : 0 ≤ (a : ℝ) / q := by positivity
      have h4 : 0 ≤ (a' : ℝ) / q' := by positivity
      rw [abs_lt]; constructor <;> linarith
    rw [hx] at hlt1
    have hm0 : m = 0 := by
      have : |(m : ℝ)| < 1 := hlt1
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at this
      have := abs_lt.1 this; omega
    rw [hm0, Int.cast_zero, sub_eq_zero, div_eq_div_iff hqpos.ne' hqpos'.ne'] at hx
    have hnat : a * q' = a' * q := by exact_mod_cast hx
    have hd1 : q ∣ q' := by
      have : q ∣ a * q' := ⟨a', by rw [hnat, mul_comm]⟩
      exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
    have hd2 : q' ∣ q := by
      have : q' ∣ a' * q := ⟨a, by rw [← hnat, mul_comm]⟩
      exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    subst hqq
    have haa : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) hnat
    exact hne (by rw [haa])
  have hdist : dist0 ((a : ℝ) / q - a' / q') = |(j : ℝ)| / (q * q') := by
    unfold dist0
    rw [← hm, hx, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  rw [hdist]
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hj0
  have hQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have : (q' : ℝ) ≤ Q := by exact_mod_cast hqQ'
    nlinarith
  calc 1 / (Q : ℝ) ^ 2 ≤ 1 / (q * q') := one_div_le_one_div_of_le (by positivity) hQ
    _ ≤ |(j : ℝ)| / (q * q') := div_le_div_of_nonneg_right hj1 (by positivity)

/-- **The large sieve at Farey fractions**, constant `N + 2Q²`. -/
theorem farey_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ p ∈ farey Q, ‖∑ n ∈ Ioc M (M + N), a n * e (n * fareyPt p)‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have := large_sieve hδ (farey_spaced Q) a M N
  rwa [show (2 : ℝ) / (1 / (Q : ℝ) ^ 2) = 2 * (Q : ℝ) ^ 2 by field_simp] at this

end LeanLab.PNTPort.LargeSieve
