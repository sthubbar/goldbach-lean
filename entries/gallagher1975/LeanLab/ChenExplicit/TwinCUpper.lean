module

public import LeanLab.ChenExplicit.TwinCNumeric

/-!
Run 20261019T1902Z-2936, unit U-1103. AI-written Lean code, Claude. Checked only by the Lean kernel.

**The twin prime constant is at most 0.66017.** `twinC ≤ ∏_{2 < p < 10⁴} (1 - 1/(p - 1)²)`
because every omitted factor lies in (0, 1]; the 1228-factor product is bounded by a rounded-up
chain `a₀ = 10¹⁵, aₙ₊₁ = ⌈aₙ ((n - 1)² - 1)/(n - 1)²⌉` at odd primes n, `aₙ₊₁ = aₙ` otherwise,
computed by the kernel to n = 10⁴ with last value 660168296506129, so the product is at most
0.660168296506129. Primes are recognised by trial division up to the square root, `primeB`,
proved equivalent to `Nat.Prime`. True value 0.6601618158.
This removes the hypothesis `C₀ ≤ 0.66017` used by Linnik/JTK7Levers.lean.
Generator: gen/twinc_chain_U1103.py. KNOWN mathematics. Goldbach is open.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace LeanLab.ChenExplicit.TwinCUpper
open Real Finset LeanLab.ChenExplicit


/-- Trial division up to `√n`. -/
def primeB (n : ℕ) : Bool :=
  2 ≤ n && (List.range' 2 (Nat.sqrt n - 1)).all (fun d => n % d != 0)

theorem primeB_iff (n : ℕ) : primeB n = true ↔ n.Prime := by
  unfold primeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hn0 : 0 < n := by omega
    have hsq := Nat.minFac_sq_le_self hn0 hnp
    have hm2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
    have hle : n.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hsq
    have hs1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn0
    exact hall n.minFac ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d hd hmod => ?_⟩
    have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have hs1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by have := hp.two_le; omega)
    have hdle : d ≤ Nat.sqrt n := by omega
    have hdsq : d * d ≤ n := Nat.le_sqrt.mp hdle
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · omega
    · subst h; nlinarith [hp.two_le]

/-- The odd primes. -/
def oddP (n : ℕ) : Prop := n.Prime ∧ 2 < n

instance : DecidablePred oddP := fun n =>
  decidable_of_iff (primeB n = true ∧ 2 < n) (by rw [primeB_iff]; rfl)

/-- One rounded-up step of the chain at `n`. -/
def step (a n : ℕ) : ℕ :=
  if primeB n && decide (2 < n) then
    (a * ((n - 1) * (n - 1) - 1) + (n - 1) * (n - 1) - 1) / ((n - 1) * (n - 1))
  else a

/-- The chain `a₀ = 10¹⁵`, `aₙ₊₁ = step aₙ n`. -/
def chainA : ℕ → ℕ
  | 0 => 10 ^ 15
  | n + 1 => step (chainA n) n

lemma gT_eq {p : ℕ} (hp : 3 ≤ p) : gT p = (((p : ℝ) - 1) ^ 2 - 1) / ((p : ℝ) - 1) ^ 2 := by
  unfold gT
  have : ((p : ℝ) - 1) ^ 2 ≠ 0 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  rw [sub_div, div_self this]

lemma gT_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ gT p := (gT_pos (by omega)).le

/-- The rounding goes up: `a gT(n) ≤ step a n` at an odd prime `n`. -/
lemma step_ge {a n : ℕ} (hn : 3 ≤ n) :
    (a : ℝ) * gT n ≤ ((a * ((n - 1) * (n - 1) - 1) + (n - 1) * (n - 1) - 1) /
      ((n - 1) * (n - 1)) : ℕ) := by
  set q := (n - 1) * (n - 1) with hq
  have hq1 : 4 ≤ q := by rw [hq]; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hdiv : a * (q - 1) ≤ (a * (q - 1) + q - 1) / q * q := by
    have h := Nat.div_add_mod' (a * (q - 1) + q - 1) q
    have hm := Nat.mod_lt (a * (q - 1) + q - 1) (by omega : 0 < q)
    generalize a * (q - 1) = P at h hm ⊢
    generalize (P + q - 1) / q * q = Z at h ⊢
    omega
  have hqr : (q : ℝ) = ((n : ℝ) - 1) ^ 2 := by
    rw [hq]; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  rw [gT_eq hn, ← hqr]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [mul_div_assoc', div_le_iff₀ hqpos]
  have hc : ((a * (q - 1) : ℕ) : ℝ) ≤ (((a * (q - 1) + q - 1) / q * q : ℕ) : ℝ) := by
    exact_mod_cast hdiv
  push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at hc
  linarith

/-- **The chain bound.** `10¹⁵ ∏_{2 < p < n} gT(p) ≤ aₙ`. -/
theorem chain_bound (n : ℕ) :
    ((10 ^ 15 : ℕ) : ℝ) * ∏ k ∈ (range n).filter oddP, gT k ≤ chainA n := by
  induction n with
  | zero => simp [chainA]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : oddP n
    · have hn3 : 3 ≤ n := h.2
      rw [if_pos h, Finset.prod_insert (by simp)]
      have hstep : step (chainA n) n =
          (chainA n * ((n - 1) * (n - 1) - 1) + (n - 1) * (n - 1) - 1) / ((n - 1) * (n - 1)) := by
        unfold step
        rw [if_pos (by simp [(primeB_iff n).mpr h.1, h.2])]
      simp only [chainA, hstep]
      calc ((10 ^ 15 : ℕ) : ℝ) * (gT n * ∏ k ∈ (range n).filter oddP, gT k)
          = gT n * (((10 ^ 15 : ℕ) : ℝ) * ∏ k ∈ (range n).filter oddP, gT k) := by ring
        _ ≤ gT n * (chainA n : ℝ) := mul_le_mul_of_nonneg_left ih (gT_nonneg hn3)
        _ = (chainA n : ℝ) * gT n := by ring
        _ ≤ _ := step_ge hn3
    · rw [if_neg h]
      have hstep : step (chainA n) n = chainA n := by
        unfold step
        rw [if_neg]
        intro hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        exact h ⟨(primeB_iff n).mp hb.1, hb.2⟩
      simp only [chainA, hstep]
      exact ih

theorem chain_last : chainA 10000 = 660168296506129 := by decide +kernel

lemma filter_eq (M : ℕ) : (range M).filter (fun n => n.Prime ∧ 2 < n) = (range M).filter oddP := by
  ext n; simp [Finset.mem_filter, oddP]

/-- `exp` of a head log sum is the head product. -/
lemma exp_head' (M : ℕ) : Real.exp (∑ n ∈ range M, aT n) =
    ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 2 < n), gT n := by
  unfold aT
  rw [← Finset.sum_filter, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro n hn
  exact Real.exp_log (gT_pos (mem_filter.mp hn).2.2)

/-- `twinC` is at most any head product. -/
lemma twinC_le_head (M : ℕ) :
    twinC ≤ ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 2 < n), gT n := by
  rw [twinC_eq_exp, ← summable_aT.sum_add_tsum_nat_add M, Real.exp_add, exp_head']
  have ht : ∑' n, aT (n + M) ≤ 0 := tsum_nonpos fun n => aT_nonpos _
  have he : Real.exp (∑' n, aT (n + M)) ≤ 1 := Real.exp_le_one_iff.mpr ht
  have hP0 : 0 ≤ ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 2 < n), gT n :=
    prod_nonneg fun n hn => (gT_pos (mem_filter.mp hn).2.2).le
  nlinarith

/-- **The twin prime constant is at most 0.66017.** No placeholder proof. True value 0.6601618. -/
theorem twinC_le_066017 : twinC ≤ (66017 / 100000 : ℝ) := by
  have hc := chain_bound 10000
  rw [chain_last] at hc
  have hD : (0 : ℝ) < ((10 ^ 15 : ℕ) : ℝ) := by positivity
  have hprod : ∏ k ∈ (range 10000).filter oddP, gT k ≤ (66017 / 100000 : ℝ) := by
    have : ∏ k ∈ (range 10000).filter oddP, gT k ≤ (660168296506129 : ℝ) / (10 ^ 15 : ℕ) := by
      rw [le_div_iff₀ hD, mul_comm]; exact_mod_cast hc
    calc _ ≤ (660168296506129 : ℝ) / (10 ^ 15 : ℕ) := this
      _ ≤ _ := by norm_num
  calc twinC ≤ ∏ n ∈ (range 10000).filter (fun n => n.Prime ∧ 2 < n), gT n := twinC_le_head 10000
    _ = ∏ k ∈ (range 10000).filter oddP, gT k := by rw [filter_eq]
    _ ≤ _ := hprod

end LeanLab.ChenExplicit.TwinCUpper
