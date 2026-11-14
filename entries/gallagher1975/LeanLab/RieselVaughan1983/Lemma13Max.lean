module

public import Mathlib

/-!
P0032 Riesel-Vaughan 1983, Lemma 13, page 66: the maximum of f(q)/(0.361 + log(z/q)) over
5 ≤ q ≤ w is at q = 5.
Unit U-1224, PC run 20261020T1103Z-23466. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Page 65: f(q) = Π_{p∣q} 1/(p(p − 2)) for odd squarefree q, else 0. Page 66:
F = max_{5 ≤ q ≤ w} f(q)/(0.361 + log(z/q)); α(0.361 + log(z/α)) increases for α ≤ z e^{−0.639},
in particular for α ≤ w = z/100; so for odd squarefree 7 ≤ q ≤ w,
f(q)/(0.361 + log(z/q)) ≤ (1/3)·1/(7(0.361 + log(z/7))) < 1/(15(0.361 + log(z/5))).

What is here, all PROVED unconditional:
* `fq`, `fq_five`: f and f(5) = 1/15.
* `fq_mul_le`: q f(q) = Π_{p∣q} 1/(p − 2) ≤ 1/3 for odd squarefree q ≥ 7.
* `incr`: 7(a + log(z/7)) ≤ q(a + log(z/q)) for 7 ≤ q ≤ z/100, a ≥ 0, by log(q/7) ≤ q/7 − 1.
* `seven_lt_five`: (1/3)/(7(a + log(z/7))) < (1/15)/(a + log(z/5)) once log z ≥ 3, a = 0.361.
* `lemma13_max`: for every natural 5 ≤ q ≤ z/100, f(q)/(0.361 + log(z/q)) ≤ f(5)/(0.361 + log(z/5)).
The paper uses log y > 350, so log z ≥ 3 holds with room. KNOWN mathematics.
-/

@[expose] public section

open Finset Real

noncomputable section
namespace LeanLab.RieselVaughan1983.Lemma13Max

/-- Page 65: `f(q) = Π_{p∣q} 1/(p(p − 2))` for odd squarefree `q`, else `0`. -/
def fq (q : ℕ) : ℝ :=
  if Odd q ∧ Squarefree q then ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) * ((p : ℝ) - 2)) else 0

theorem fq_five : fq 5 = 1 / 15 := by
  have h5 : Nat.Prime 5 := by norm_num
  unfold fq
  rw [if_pos ⟨by decide, h5.squarefree⟩, h5.primeFactors, prod_singleton]
  norm_num

lemma fq_nonneg (q : ℕ) : 0 ≤ fq q := by
  unfold fq
  split_ifs with h
  · apply prod_nonneg
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpo : Odd p := (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
      have : 3 ≤ p := by
        rcases hpp.eq_two_or_odd' with e | _
        · subst e; exact absurd hpo (by decide)
        · have := hpp.two_le
          rcases hpo with ⟨r, hr⟩; omega
      exact_mod_cast this
    apply div_nonneg zero_le_one; nlinarith
  · exact le_refl _

/-- `q f(q) = Π_{p∣q} 1/(p − 2) ≤ 1/3` for odd squarefree `q ≥ 7`. -/
theorem fq_mul_le {q : ℕ} (hq : 7 ≤ q) (ho : Odd q) (hs : Squarefree q) :
    (q : ℝ) * fq q ≤ 1 / 3 := by
  unfold fq
  rw [if_pos ⟨ho, hs⟩]
  have hq0 : q ≠ 0 := by omega
  -- q = Π_{p ∣ q} p
  have hprod : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hs]
  have h3 : ∀ p ∈ q.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpo : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    rcases hpp.eq_two_or_odd' with e | _
    · subst e; exact absurd hpo (by decide)
    · have := hpp.two_le
      rcases hpo with ⟨r, hr⟩; omega
  rw [hprod, ← prod_mul_distrib]
  have hterm : ∀ p ∈ q.primeFactors, (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 2))) = 1 / ((p : ℝ) - 2) := by
    intro p hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3 p hp
    field_simp
  rw [prod_congr rfl hterm]
  -- some prime factor is at least 5
  have hbig : ∃ p0 ∈ q.primeFactors, 5 ≤ p0 := by
    by_contra hc
    push_neg at hc
    have hsub : q.primeFactors ⊆ {3} := by
      intro p hp
      have := h3 p hp
      have := hc p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      rw [mem_singleton]
      interval_cases p
      · rfl
      · exact absurd hpp (by decide)
    have : q ∣ 3 := by
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      calc ∏ p ∈ q.primeFactors, p ∣ ∏ p ∈ ({3} : Finset ℕ), p := prod_dvd_prod_of_subset _ _ _ hsub
        _ = 3 := by simp
    have := Nat.le_of_dvd (by norm_num) this
    omega
  obtain ⟨p0, hp0, hp05⟩ := hbig
  rw [← mul_prod_erase _ _ hp0]
  have h1 : 1 / ((p0 : ℝ) - 2) ≤ 1 / 3 := by
    have : (5 : ℝ) ≤ p0 := by exact_mod_cast hp05
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2 : ∏ p ∈ q.primeFactors.erase p0, 1 / ((p : ℝ) - 2) ≤ 1 := by
    apply prod_le_one₀
    · intro p hp
      have : (3 : ℝ) ≤ p := by exact_mod_cast h3 p (mem_of_mem_erase hp)
      apply div_nonneg zero_le_one; linarith
    · intro p hp
      have : (3 : ℝ) ≤ p := by exact_mod_cast h3 p (mem_of_mem_erase hp)
      rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ 1 / ((p0 : ℝ) - 2) := by
    have : (5 : ℝ) ≤ p0 := by exact_mod_cast hp05
    apply div_nonneg zero_le_one; linarith
  calc 1 / ((p0 : ℝ) - 2) * ∏ p ∈ q.primeFactors.erase p0, 1 / ((p : ℝ) - 2)
      ≤ 1 / ((p0 : ℝ) - 2) * 1 := mul_le_mul_of_nonneg_left h2 h0
    _ ≤ 1 / 3 := by rw [mul_one]; exact h1

/-- Page 66: `α(a + log(z/α))` increases on `[7, z/100]`: `7(a + log(z/7)) ≤ q(a + log(z/q))`. -/
theorem incr {a z q : ℝ} (ha : 0 ≤ a) (hq : 7 ≤ q) (hqz : q ≤ z / 100) :
    7 * (a + Real.log (z / 7)) ≤ q * (a + Real.log (z / q)) := by
  have hq0 : 0 < q := by linarith
  have hz0 : 0 < z := by linarith
  have hl : Real.log (q / 7) ≤ q / 7 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hq0.ne' (by norm_num)] at hl
  have h100 : Real.log 100 ≤ Real.log (z / q) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hq0]; linarith
  have hl100 : 1 < Real.log 100 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have he : Real.exp 1 < 100 := by have := Real.exp_one_lt_d9; linarith
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact he
  rw [Real.log_div hz0.ne' hq0.ne'] at h100
  rw [Real.log_div hz0.ne' (by norm_num), Real.log_div hz0.ne' hq0.ne']
  -- q(a + log z − log q) − 7(a + log z − log 7) = (q − 7)(a + log z − log q) − 7(log q − log 7)
  have key : 7 * (Real.log q - Real.log 7) ≤ q - 7 := by linarith
  nlinarith

/-- Page 66: `(1/3)/(7(a + log(z/7))) < (1/15)/(a + log(z/5))` for `a = 0.361`, `log z ≥ 3`. -/
theorem seven_lt_five {z : ℝ} (hz : 3 ≤ Real.log z) :
    1 / 3 / (7 * (0.361 + Real.log (z / 7))) < 1 / 15 / (0.361 + Real.log (z / 5)) := by
  have hz0 : z ≠ 0 := by rintro rfl; rw [Real.log_zero] at hz; linarith
  rw [Real.log_div hz0 (by norm_num), Real.log_div hz0 (by norm_num)]
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hE2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h7 : Real.log 7 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), hE2]
    have : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he1.le 2
    have : (7 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by norm_num
    linarith
  have h5' : Real.log 5 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), hE2]
    have : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he1.le 2
    have : (5 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by norm_num
    linarith
  have h5 : 8 / 5 < Real.log 5 := by
    have h3125 : Real.log (5 ^ 5 : ℝ) = 5 * Real.log 5 := by rw [Real.log_pow]; norm_num
    have hE8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have : 8 < Real.log (5 ^ 5 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num), hE8]
      have : Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he2.le 8
      have : (2.7182818286 : ℝ) ^ 8 < 5 ^ 5 := by norm_num
      linarith
    linarith
  have hA : 0 < 0.361 + (Real.log z - Real.log 7) := by norm_num; linarith
  have hB : 0 < 0.361 + (Real.log z - Real.log 5) := by norm_num; linarith
  rw [div_div, div_lt_div_iff₀ (by positivity) hB]
  nlinarith

/-- **Lemma 13's maximisation**, page 66: for natural `5 ≤ q ≤ z/100` and `log z ≥ 3`,
`f(q)/(0.361 + log(z/q)) ≤ f(5)/(0.361 + log(z/5))`. -/
theorem lemma13_max {z : ℝ} (hz : 3 ≤ Real.log z) {q : ℕ} (h5 : 5 ≤ q) (hqz : (q : ℝ) ≤ z / 100) :
    fq q / (0.361 + Real.log (z / q)) ≤ fq 5 / (0.361 + Real.log (z / 5)) := by
  have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast h5
  have hz0 : 0 < z := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hden : 0 < 0.361 + Real.log (z / q) := by
    have : Real.log 100 ≤ Real.log (z / q) := by
      apply Real.log_le_log (by norm_num); rw [le_div_iff₀ hq0]; linarith
    have : 0 < Real.log 100 := Real.log_pos (by norm_num)
    norm_num; linarith
  rw [fq_five]
  rcases Nat.lt_or_ge q 7 with h | h
  · -- q ∈ {5, 6}
    interval_cases q
    · norm_num [fq_five]
    · have : fq 6 = 0 := by unfold fq; rw [if_neg (by decide)]
      rw [this, zero_div]
      have hz5 : 0 < 0.361 + Real.log (z / 5) := by
        have : Real.log 100 ≤ Real.log (z / 5) := by
          apply Real.log_le_log (by norm_num); rw [le_div_iff₀ (by norm_num)]; push_cast at hqz; linarith
        have : 0 < Real.log 100 := Real.log_pos (by norm_num)
        norm_num; linarith
      positivity
  · by_cases hos : Odd q ∧ Squarefree q
    · have hf := fq_mul_le h hos.1 hos.2
      have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast h
      have hinc := incr (a := 0.361) (z := z) (q := q) (by norm_num) hq7 hqz
      have hlt := seven_lt_five hz
      have h7pos : 0 < 7 * (0.361 + Real.log (z / 7)) := by
        have : Real.log 100 ≤ Real.log (z / 7) := by
          apply Real.log_le_log (by norm_num); rw [le_div_iff₀ (by norm_num)]; linarith
        have : 0 < Real.log 100 := Real.log_pos (by norm_num)
        norm_num; linarith
      have hfq0 := fq_nonneg q
      -- fq q / D_q = (q fq q) / (q D_q) ≤ (1/3) / (7 D_7)
      have step : fq q / (0.361 + Real.log (z / q)) ≤ 1 / 3 / (7 * (0.361 + Real.log (z / 7))) := by
        rw [div_le_div_iff₀ hden h7pos]
        have e : fq q * (7 * (0.361 + Real.log (z / 7))) ≤ fq q * (q * (0.361 + Real.log (z / q))) :=
          mul_le_mul_of_nonneg_left hinc hfq0
        have e2 : fq q * (q * (0.361 + Real.log (z / q))) = (q * fq q) * (0.361 + Real.log (z / q)) := by
          ring
        have e3 : (q * fq q) * (0.361 + Real.log (z / q)) ≤ 1 / 3 * (0.361 + Real.log (z / q)) :=
          mul_le_mul_of_nonneg_right hf hden.le
        linarith
      linarith
    · have : fq q = 0 := by unfold fq; rw [if_neg hos]
      rw [this, zero_div]
      have hz5 : 0 < 0.361 + Real.log (z / 5) := by
        have : Real.log 100 ≤ Real.log (z / 5) := by
          apply Real.log_le_log (by norm_num); rw [le_div_iff₀ (by norm_num)]
          have : (5 : ℝ) ≤ q := by exact_mod_cast h5
          linarith
        have : 0 < Real.log 100 := Real.log_pos (by norm_num)
        norm_num; linarith
      positivity

end LeanLab.RieselVaughan1983.Lemma13Max
