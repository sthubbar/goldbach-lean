module

public import LeanLab.PNTPort.Vinogradov.TernaryAssembly

/-!
# The truncated ternary singular series in Ramanujan sum form

Lab proof, unit U-5257. AI wrote this file. Known mathematics, no cited input.

* `ramanujan_sum`: `∑_{r < q, (r, q) = 1} e(nr/q) = c_q(n) = ∑_{d ∣ (n, q)} d μ(q/d)`, the lab's
  `HeathBrown1985.ramanujan`.
* `singP_eq`: `𝔖_P(n) = ∑_{q ≤ P} μ(q)³ c_q(n) / φ(q)³`, real.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve

/-- The Ramanujan sum by Möbius inversion. -/
theorem ramanujan_sum {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), e (n * r / q) =
      (HeathBrown1985.ramanujan q n : ℂ) := by
  rw [sum_filter]
  have step1 : ∀ r ∈ range q, (if Nat.Coprime r q then e (n * r / q) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (μ d : ℂ) * e (n * r / q) := by
    intro r _
    rw [← sum_mul, sum_moebius_divisors]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl step1]
  rw [sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun r => d ∣ r))]
  · have step2 : ∀ d ∈ q.divisors, ∑ r ∈ (range q).filter (fun r => d ∣ r), (μ d : ℂ) * e (n * r / q)
        = (μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ (n : ℤ) then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← mul_sum, ← sum_e_mul_div (n : ℤ) hqd]
      congr 1
      refine sum_nbij' (fun r => r / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [mem_filter, mem_range] at hr
        rw [mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [mem_range] at hs
        rw [mem_filter, mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro r hr
        rw [mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        rw [mem_filter] at hr
        obtain ⟨s, rfl⟩ := hr.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [sum_congr rfl step2]
    -- reindex d ↦ q / d onto the divisors of gcd(n, q)
    unfold HeathBrown1985.ramanujan
    rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_intCast]
    rw [← sum_filter_add_sum_filter_not q.divisors (fun d => ((q / d : ℕ) : ℤ) ∣ (n : ℤ))]
    rw [sum_eq_zero (s := q.divisors.filter (fun d => ¬ ((q / d : ℕ) : ℤ) ∣ (n : ℤ)))
      (fun d hd => by rw [mem_filter] at hd; rw [if_neg hd.2, mul_zero]), add_zero]
    refine sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mem_divisors]
      refine ⟨Nat.dvd_gcd (by exact_mod_cast hd.2) (Nat.div_dvd_of_dvd hd.1.1), ?_⟩
      exact (Nat.gcd_pos_of_pos_right n (by omega)).ne'
    · intro e he
      rw [Nat.mem_divisors] at he
      have heq : e ∣ q := (Nat.dvd_gcd_iff.1 he.1).2
      have hen : e ∣ n := (Nat.dvd_gcd_iff.1 he.1).1
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos heq (by omega)
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd heq, by omega⟩, ?_⟩
      rw [Nat.div_div_self heq (by omega)]; exact_mod_cast hen
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro e he
      rw [Nat.mem_divisors] at he
      exact Nat.div_div_self (Nat.dvd_gcd_iff.1 he.1).2 (by omega)
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [if_pos hd.2, Nat.div_div_self hd.1.1 (by omega)]
      ring
  · intro r d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, by omega⟩

/-- `𝔖_P(n)` in Ramanujan sum form. -/
theorem singP_eq (P n : ℕ) :
    singP P n = ((∑ q ∈ Icc 1 P, (μ q : ℝ) ^ 3 * HeathBrown1985.ramanujan q n /
      (q.totient : ℝ) ^ 3 : ℝ) : ℂ) := by
  unfold singP majIdx
  rw [sum_filter, sum_product]
  push_cast
  refine sum_congr rfl fun q hq => ?_
  rw [mem_Icc] at hq
  have hset : ∀ a ∈ range P, (if a < q ∧ Nat.Coprime a q then
      ((μ q : ℂ) / q.totient) ^ 3 * e (n * ((a : ℝ) / q)) else 0) =
      if a ∈ (range q).filter (fun r => Nat.Coprime r q) then
        ((μ q : ℂ) / q.totient) ^ 3 * e (n * a / q) else 0 := by
    intro a _
    simp only [mem_filter, mem_range]
    split_ifs <;> first | rfl | (congr 2; ring)
  rw [sum_congr rfl hset, ← sum_filter]
  have hsub : (range P).filter (fun a => a ∈ (range q).filter (fun r => Nat.Coprime r q)) =
      (range q).filter (fun r => Nat.Coprime r q) := by
    ext a; simp only [mem_filter, mem_range]; constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨by omega, h⟩
  rw [hsub, ← mul_sum, ramanujan_sum hq.1 n]
  ring

end LeanLab.PNTPort.Vinogradov

