module

public import LeanLab.PNTSieve.MertensUpper

/-!
# `Σ_{p ≤ n} log p/p ≥ log n - 7`

Unit U-5505, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics, Mertens 1874,
the lower half of his first theorem in a weak explicit form; with `C_le` it gives
`|C(n) - log n| ≤ 7`, so the sum of `1/p` over a block `(y, w]` is at most
`(log(w/y) + 14)/log y`, the bounded block sums the fundamental lemma needs, IDEAS I-5051.

Proof: `n log n - n ≤ log n!` from `n^n/n! ≤ e^n`; Legendre's `v_p(n!) ≤ n/(p - 1)` gives
`log n! ≤ n C(n) + n Σ_p log p/(p(p - 1))`; and `log m/(m(m - 1)) ≤ 6(1/√(m - 1) - 1/√m)`, which
telescopes to at most `6`.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Mertens

open Finset Real

/-- `1/(√m (m - 1)) ≤ 3 (1/√(m - 1) - 1/√m)` for `m ≥ 2`. -/
lemma inv_sqrt_tele (m : ℕ) (hm : 2 ≤ m) :
    1 / (Real.sqrt m * ((m : ℝ) - 1)) ≤ 3 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set a := Real.sqrt ((m : ℝ) - 1) with ha
  set b := Real.sqrt (m : ℝ) with hb
  have ha2 : a ^ 2 = (m : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  -- b ≤ 2a since b² = a² + 1 ≤ 4a²
  have hb2a : b ≤ 2 * a := by nlinarith
  rw [← ha2]
  rw [div_le_iff₀ (by positivity)]
  have key : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    field_simp
    nlinarith
  rw [key]
  rw [show 3 * (1 / (a * b * (a + b))) * (b * a ^ 2) = 3 * a / (a + b) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `log m/(m(m - 1)) ≤ 6 (1/√(m - 1) - 1/√m)` for `m ≥ 2`. -/
lemma log_term_le (m : ℕ) (hm : 2 ≤ m) :
    Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤
      6 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : Real.log m ≤ 2 * Real.sqrt m := by
    have := Real.log_le_rpow_div (x := (m : ℝ)) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hs0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (m : ℝ) * Real.sqrt m = m := Real.mul_self_sqrt (by linarith)
  have h1 : Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 2 * (1 / (Real.sqrt m * ((m : ℝ) - 1))) := by
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    rw [div_le_iff₀ (by nlinarith)]
    have e : 2 * (1 / (Real.sqrt m * ((m : ℝ) - 1))) * ((m : ℝ) * ((m : ℝ) - 1)) =
        2 * Real.sqrt m := by
      field_simp
      linarith [hss]
    rw [e]
    exact hlog
  have h2 := inv_sqrt_tele m hm
  linarith

/-- Telescoping: `Σ_{1 < m ≤ n} (g(m - 1) - g(m)) = g 1 - g n`. -/
lemma tele_Ioc (g : ℕ → ℝ) : ∀ n : ℕ, 1 ≤ n →
    ∑ m ∈ Ioc 1 n, (g (m - 1) - g m) = g 1 - g n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ioc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- `Σ_{p ≤ n} log p/(p(p - 1)) ≤ 6`. -/
lemma sum_log_div_pred_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 6 := by
  rcases Nat.lt_or_ge n 1 with h | h
  · have : n = 0 := by omega
    subst this
    rw [show Nat.primesLE 0 = ∅ by decide]
    simp
  have hsub : Nat.primesLE n ⊆ Ioc 1 n := by
    intro p hp
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc] at hp
    rw [mem_Ioc]; exact ⟨hp.2.one_lt, hp.1.2⟩
  have hnn : ∀ m ∈ Ioc 1 n, 0 ≤ Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
    intro m hm
    rw [mem_Ioc] at hm
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
  calc ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ m ∈ Ioc 1 n, Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => hnn m hm)
    _ ≤ ∑ m ∈ Ioc 1 n, 6 * ((fun k : ℕ => 1 / Real.sqrt (k : ℝ)) (m - 1) -
          (fun k : ℕ => 1 / Real.sqrt (k : ℝ)) m) := by
        apply sum_le_sum
        intro m hm
        rw [mem_Ioc] at hm
        have := log_term_le m (by omega)
        simp only
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        simpa using this
    _ = 6 * (1 - 1 / Real.sqrt n) := by
        rw [← mul_sum, tele_Ioc (fun k : ℕ => 1 / Real.sqrt (k : ℝ)) n h]
        simp
    _ ≤ 6 := by
        have : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
        linarith

/-- `n log n - n ≤ log n!`. -/
lemma log_factorial_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 := Real.pow_div_factorial_le_exp (n : ℝ) hn.le n
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h2
  linarith

/-- **Mertens' first theorem, lower half**: `C(n) = Σ_{p ≤ n} log p/p ≥ log n - 7`. -/
theorem C_ge (n : ℕ) : Real.log n - 7 ≤ C n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [C]
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  rw [C_eq]
  have hleg := LeanLab.AlmostPrimes.RSLogSum.log_factorial_eq n
  have hup : ∀ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤
      (n : ℝ) * (Real.log p / p) + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter] at hp
    have hpp := hp.2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hv := Nat.factorization_factorial_le_div_pred hpp n
    have hv' : ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      have h1 : ((n.factorial.factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
        exact_mod_cast hv
      refine h1.trans ?_
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := p - 1)
      rwa [Nat.cast_sub hpp.one_le, Nat.cast_one] at this
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤ (n : ℝ) / ((p : ℝ) - 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hv' hl
      _ = (n : ℝ) * (Real.log p / p) + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          field_simp
          ring
  have hsum := sum_le_sum hup
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← hleg] at hsum
  have h6 := sum_log_div_pred_le n
  have hlf := log_factorial_ge n
  have : (n : ℝ) * (Real.log n - 7) ≤ (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hn

/-- **Block sums of `1/p` are bounded**: for `2 ≤ y ≤ w`,
`Σ_{y < p ≤ w} 1/p ≤ (log w - log y + 14)/log y`. -/
theorem sum_inv_primes_block (y w : ℕ) (hy : 2 ≤ y) (hyw : y ≤ w) :
    ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p ≤
      (Real.log w - Real.log y + 14) / Real.log y := by
  have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  -- Σ_{y < n ≤ w} c n = C w - C y
  have hsplit : C w = C y + ∑ n ∈ Ioc y w, c n := by
    unfold C
    rw [← sum_union]
    · congr 1
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    · rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  have hCw := C_le w (by omega)
  have hCy := C_ge y
  have hblock : ∑ n ∈ Ioc y w, c n ≤ Real.log w - Real.log y + 14 := by linarith
  have hle : ∀ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p ≤ c p / Real.log y := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    have hp' : (y : ℝ) < p := by exact_mod_cast hp.1.1
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : Real.log y ≤ Real.log p := Real.log_le_log (by linarith) hp'.le
    unfold c
    rw [if_pos hp.2, div_div, le_div_iff₀ (by positivity)]
    rw [show (1 : ℝ) / p * (p * Real.log y) = Real.log y by field_simp]
    have e : Real.log p / p * p = Real.log p := div_mul_cancel₀ _ hp0.ne'
    have e2 : Real.log p * p * (p : ℝ)⁻¹ = Real.log p := by
      rw [mul_assoc, mul_inv_cancel₀ hp0.ne', mul_one]
    first
      | linarith
      | (field_simp; linarith)
      | (simp only [div_eq_mul_inv] at *; linarith)
  calc ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, c p / Real.log y := sum_le_sum hle
    _ = (∑ p ∈ (Ioc y w).filter Nat.Prime, c p) / Real.log y := by rw [sum_div]
    _ = (∑ n ∈ Ioc y w, c n) / Real.log y := by
        congr 1
        rw [sum_filter]
        refine sum_congr rfl (fun n _ => ?_)
        unfold c; split_ifs <;> simp
    _ ≤ (Real.log w - Real.log y + 14) / Real.log y :=
        div_le_div_of_nonneg_right hblock hly.le

end LeanLab.PNTSieve.Mertens

