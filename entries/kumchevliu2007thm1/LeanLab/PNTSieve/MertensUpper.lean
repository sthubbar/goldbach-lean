module

public import LeanLab.AlmostPrimes.RSLogSum

/-!
# `Σ_{p ≤ N} 1/p ≤ log log N + 12`

Lab proof, unit U-5327, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Mertens 1874 in a weak explicit form. From the lab's `Σ_{p ≤ n} log p/p < log n` for `n ≥ 1000`,
AlmostPrimes/RSLogSum.lean, by discrete partial summation and the telescoping inequality
`1 - log n/log(n + 1) ≤ log log(n + 1) - log log n`. The input of the Mertens product lower bound that
Rényi's theorem needs, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Mertens

open Finset Real

/-- `c(n) = log n/n` on primes, `0` elsewhere. -/
noncomputable def c (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

/-- `C(N) = Σ_{n ≤ N} c(n) = Σ_{p ≤ N} log p/p`. -/
noncomputable def C (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, c n

/-- `E(N) = Σ_{n ≤ N} c(n)/log n = Σ_{p ≤ N} 1/p`. -/
noncomputable def E (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, c n / Real.log n

lemma c_one : c 1 = 0 := by simp [c, Nat.not_prime_one]

lemma C_eq (N : ℕ) : C N = ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  unfold C c
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_filter, mem_Icc, Nat.primesLE, Nat.primesBelow, mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h1, hp⟩; exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩

lemma E_eq (N : ℕ) : E N = ∑ p ∈ (Icc 1 N).filter Nat.Prime, (1 : ℝ) / p := by
  unfold E c
  rw [sum_filter]
  refine sum_congr rfl (fun n hn => ?_)
  split_ifs with hp
  · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hp.one_lt)
    field_simp
  · simp

lemma C_le (N : ℕ) (hN : 1 ≤ N) : C N ≤ Real.log N + 7 := by
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rcases le_or_gt 1000 N with h | h
  · rw [C_eq]; linarith [LeanLab.AlmostPrimes.RSLogSum.sum_log_div_lt_log N h]
  · have hmono : C N ≤ C 1000 := by
      unfold C
      apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h.le)
      intro n _ _; unfold c; split_ifs <;> positivity
    have h1000 : C 1000 < Real.log 1000 := by
      rw [C_eq]; exact_mod_cast LeanLab.AlmostPrimes.RSLogSum.sum_log_div_lt_log 1000 le_rfl
    have hlog : Real.log 1000 < 7 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      calc (1000 : ℝ) < 2.7182818283 ^ 7 := by norm_num
        _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he.le 7
        _ = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
    linarith

lemma abel (N : ℕ) (hN : 2 ≤ N) :
    E N = C N / Real.log N + ∑ n ∈ Ico 2 N, C n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
  induction N, hN using Nat.le_induction with
  | base =>
      have h12 : Icc 1 2 = {1, 2} := by decide
      simp [E, C, h12, c_one]
  | succ N hN ih =>
      have h1 : E (N + 1) = E N + c (N + 1) / Real.log ((N : ℝ) + 1) := by
        unfold E; rw [sum_Icc_succ_top (by omega)]; push_cast; ring
      have h2 : C (N + 1) = C N + c (N + 1) := by
        unfold C; rw [sum_Icc_succ_top (by omega)]
      rw [h1, h2, ih, sum_Ico_succ_top hN]
      push_cast
      ring

lemma diff_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le hl (Real.log_le_log (by linarith) (by linarith))

lemma tele_sum (N : ℕ) (hN : 2 ≤ N) (g : ℕ → ℝ) :
    ∑ n ∈ Ico 2 N, (g (n + 1) - g n) = g N - g 2 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [sum_Ico_succ_top hN, ih]; ring

/-- `Σ_{p ≤ N} 1/p ≤ log log N + 12` for `N ≥ 2`. -/
theorem sum_inv_primes_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ (Icc 1 N).filter Nat.Prime, (1 : ℝ) / p ≤ Real.log (Real.log N) + 12 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hLN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hL0 : 0 < Real.log N := by linarith
  rw [← E_eq, abel N hN]
  -- the boundary term
  have hb : C N / Real.log N ≤ 1 + 7 / Real.log N := by
    rw [div_le_iff₀ hL0, add_mul, one_mul, div_mul_cancel₀ _ hL0.ne']
    linarith [C_le N (by omega)]
  -- the sum, termwise
  have hterm : ∀ n ∈ Ico 2 N, C n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
      (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)) +
        7 * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    have hl1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hd := diff_nonneg hn.1
    have hC := C_le n (by omega)
    have h1 : C n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
        (Real.log n + 7) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hC hd
    have h2 : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
        Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
      rw [← Real.log_div hl1.ne' hl.ne']
      have := Real.one_sub_inv_le_log_of_pos (div_pos hl1 hl)
      rw [inv_div] at this
      have e : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
          1 - Real.log n / Real.log ((n : ℝ) + 1) := by field_simp
      rw [e]; exact this
    nlinarith
  have hs := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hs
  have ht1 : ∑ n ∈ Ico 2 N, (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)) =
      Real.log (Real.log N) - Real.log (Real.log 2) := by
    have := tele_sum N hN (fun n => Real.log (Real.log n))
    push_cast at this
    exact this
  have ht2 : ∑ n ∈ Ico 2 N, (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
      1 / Real.log 2 - 1 / Real.log N := by
    have := tele_sum N hN (fun n => -(1 / Real.log n))
    push_cast at this
    rw [show ∑ n ∈ Ico 2 N, (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
        ∑ n ∈ Ico 2 N, (-(1 / Real.log ((n : ℝ) + 1)) - -(1 / Real.log n)) from
      sum_congr rfl (fun n _ => by ring), this]
    ring
  rw [ht1, ht2] at hs
  have hl2a : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h7 : 7 / Real.log 2 ≤ 10.11 := by rw [div_le_iff₀ hlog2]; linarith
  have hll2 : -Real.log (Real.log 2) ≤ 0.45 := by
    have := Real.one_sub_inv_le_log_of_pos hlog2
    have hinv : (Real.log 2)⁻¹ ≤ 1.443 := by
      rw [inv_le_comm₀ hlog2 (by norm_num)]; norm_num; linarith
    linarith
  have e1 : 7 / Real.log N = 7 * (1 / Real.log N) := by ring
  have e2 : 7 / Real.log 2 = 7 * (1 / Real.log 2) := by ring
  linarith

end LeanLab.PNTSieve.Mertens

