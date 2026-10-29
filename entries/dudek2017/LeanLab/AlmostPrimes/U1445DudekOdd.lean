module

public import LeanLab.AlmostPrimes.DudekFrom1e9

/-!
# Dudek 2017, the odd half from `10⁹`, U-1445, run 20261021T2003Z-599, P0048 I-5067

AI wrote the Lean code. KNOWN mathematics, Dudek 2017 Theorem 1, arXiv 1410.7459. Goldbach is OPEN.

For odd `N` and odd `p`, `N - p` is even, so `N - p` square-free forces `p ≡ N + 2 mod 4`. The
primes `p ≤ N` in that class number more than `N/(2 log N)` by the cited
`BMORCor16`, Bennett, Martin, O'Bryant, Rechnitzer 2018 Corollary 1.6 at `q = 4`. A bad `p` has
`r² ∣ N - p` for an odd prime `r`:
* `3 ≤ r ≤ 17`: `p` is in the class `N + 2r² mod 4r²`, `4r² ≤ 1156 ≤ 1200`, and the upper half of
  `BMORCor16` bounds it by `N/(2r(r - 1) log N) · (1 + 5/(2 log N))`;
* `19 ≤ r ≤ 80⌈log N⌉`: `p` is in the class `N mod r²`, the lab's large sieve
  Brun-Titchmarsh `brun_titchmarsh_ap_pow` as in `DudekFrom1e9.bad_sum_le9`;
* larger `r`: at most `N/r²` choices, the tail `N/Q`.
The budget is `0.146 + 0.11 < 0.5` times `N / log N`, plus `6`.

`dudek_odd_from_1e9`: every odd `N > 10⁹` is `p + m`, `p` prime, `m ≥ 1` square-free,
CONDITIONAL ON `BMORCor16`. No other cited input: the Brun-Titchmarsh used is PROVED in the lab.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.U1445DudekOdd

open LeanLab.AlmostPrimes.DudekLarge LeanLab.AlmostPrimes.DudekFrom4e18
open LeanLab.AlmostPrimes.DudekGroups LeanLab.AlmostPrimes.DudekFrom1e9

/-- `π(x; q, a)` at an integer `x`: the primes `p ≤ x` with `p ≡ a mod q`. -/
def primesAP (x q a : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun p => p.Prime ∧ p % q = a % q)

/-- **Cited input.** Bennett, Martin, O'Bryant, Rechnitzer, *Explicit bounds for primes in
arithmetic progressions*, Illinois J. Math. 62 (2018), arXiv 1802.00085, Corollary 1.6: for
`1 ≤ q ≤ 1200`, `gcd(a, q) = 1` and all `x ≥ 50 q²`,
`x/(φ(q) log x) < π(x; q, a) < x/(φ(q) log x) · (1 + 5/(2 log x))`.
Stated here at integer `x` only, which the published statement for real `x` implies. -/
def BMORCor16 : Prop :=
  ∀ q a x : ℕ, 1 ≤ q → q ≤ 1200 → Nat.Coprime a q → 50 * q ^ 2 ≤ x →
    (x : ℝ) / ((q.totient : ℝ) * Real.log x) < ((primesAP x q a).card : ℝ) ∧
      ((primesAP x q a).card : ℝ) <
        (x : ℝ) / ((q.totient : ℝ) * Real.log x) * (1 + 5 / (2 * Real.log x))

/-- A class not coprime to the modulus holds at most one prime. -/
lemma card_primesAP_le_one {x q a : ℕ} (h : ¬ Nat.Coprime a q) : (primesAP x q a).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ p ∈ primesAP x q a, p = Nat.gcd q a := by
    intro p hp
    rw [primesAP, mem_filter] at hp
    obtain ⟨-, hpp, hpa⟩ := hp
    have hg : Nat.gcd q p = Nat.gcd q a := by
      rw [Nat.gcd_rec q p, hpa, ← Nat.gcd_rec q a]
    have hdvd : Nat.gcd q a ∣ p := hg ▸ Nat.gcd_dvd_right q p
    have hne : Nat.gcd q a ≠ 1 := by
      intro h1; exact h (by rw [Nat.Coprime, Nat.gcd_comm]; exact h1)
    rcases (Nat.dvd_prime hpp).mp hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1.symm
  intro a1 h1 a2 h2
  rw [key a1 h1, key a2 h2]

/-- `φ(4r²) = 2r(r - 1)` for an odd prime `r`. -/
lemma totient_four_sq {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    (4 * r ^ 2).totient = 2 * r * (r - 1) := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hc : Nat.Coprime 4 (r ^ 2) := by
    have : Nat.Coprime (2 ^ 2) r := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    exact Nat.Coprime.pow_right 2 this
  have h4 : Nat.totient 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.totient_prime_pow Nat.prime_two two_pos]; norm_num
  rw [Nat.totient_mul hc, h4, Nat.totient_prime_pow hr two_pos, show 2 - 1 = 1 from rfl, pow_one]
  ring

/-- The class of a bad `p`: `p ≡ N + 2 mod 4` and `r² ∣ N - p`, `r` odd, give
`p ≡ N + 2r² mod 4r²`. -/
lemma mem_class4 {N p r : ℕ} (hr : Odd r) (hp : p ≤ N) (h4 : p % 4 = (N + 2) % 4)
    (hd : r ^ 2 ∣ N - p) : p % (4 * r ^ 2) = (N + 2 * r ^ 2) % (4 * r ^ 2) := by
  have hc : Nat.Coprime 4 (r ^ 2) := by
    have : Nat.Coprime (2 ^ 2) r := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hr)
    exact Nat.Coprime.pow_right 2 this
  have h1 : p ≡ N + 2 * r ^ 2 [MOD 4] := by
    obtain ⟨j, rfl⟩ := hr
    have e : N + 2 * (2 * j + 1) ^ 2 = N + 2 + 8 * (j * j + j) := by ring
    rw [e]
    generalize j * j + j = m
    unfold Nat.ModEq; omega
  have h2 : p ≡ N + 2 * r ^ 2 [MOD r ^ 2] := by
    rw [Nat.modEq_iff_dvd' (by omega)]
    have e : N + 2 * r ^ 2 - p = (N - p) + r ^ 2 * 2 := by
      have := Nat.sub_add_cancel hp; ring_nf; omega
    rw [e]
    exact dvd_add hd (dvd_mul_right _ _)
  exact (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h1, h2⟩

/-- `20.7 ≤ log N` for `N ≥ 10⁹`. -/
lemma log_ge_207 {N : ℕ} (hN : (10 ^ 9 : ℝ) ≤ N) : 20.7 ≤ Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Real.le_log_iff_exp_le hNpos]
  refine le_trans ?_ hN
  have h207 : exp 20.7 ^ 10 = exp 207 := by rw [← Real.exp_nat_mul]; norm_num
  have h207' : exp 207 ≤ (2.7182818286 : ℝ) ^ 207 := by
    have := Real.exp_nat_mul 1 207
    rw [mul_one] at this
    rw [show (207 : ℝ) = ((207 : ℕ) : ℝ) by norm_num, this]
    exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 207
  by_contra hc
  push Not at hc
  have : ((10 : ℝ) ^ 9) ^ 10 ≤ exp 20.7 ^ 10 := pow_le_pow_left₀ (by positivity) hc.le 10
  rw [h207] at this
  have := this.trans h207'
  norm_num at this

/-- The primes `19 ≤ r ≤ 31`, once `Q ≥ 31`. -/
lemma primes_18_31 {Q : ℕ} (hQ : 31 ≤ Q) :
    ((Icc 18 Q).filter Nat.Prime).filter (· ≤ 31) = {19, 23, 29, 31} := by
  have : ((Icc 18 Q).filter Nat.Prime).filter (· ≤ 31) = (Icc 18 31).filter Nat.Prime := by
    ext r; simp only [mem_filter, mem_Icc]; constructor
    · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨⟨h1, by omega⟩, h2⟩, h3⟩
  rw [this]; decide

set_option maxHeartbeats 16000000 in
/-- **The bad-prime budget for `r ≥ 19`, from `10⁹`.** A copy of `DudekFrom1e9.bad_sum_le9` with
the groups `3`, `5`, `7`, `{11, 13}` removed and `17` dropped from the fifth group: for `N ≥ 10⁹`,
with `Q = 80⌈log N⌉`, the classes `N mod r²` of the primes `19 ≤ r ≤ Q` and the tail total at most
`0.11 N / log N`. -/
theorem bad_sum_ge19 (N : ℕ) (hN : (10 ^ 9 : ℝ) ≤ N) :
    (∑ r ∈ (Icc 18 (80 * ⌈Real.log N⌉₊)).filter Nat.Prime, ((cls N r).card : ℝ)) +
      ∑ n ∈ Ioc (80 * ⌈Real.log N⌉₊) N, ((N / n ^ 2 : ℕ) : ℝ) ≤ 0.11 * N / Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set L := Real.log N with hLdef
  have hL : 20.7 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hNpos]
    refine le_trans ?_ hN
    have h207 : exp 20.7 ^ 10 = exp 207 := by rw [← Real.exp_nat_mul]; norm_num
    have h207' : exp 207 ≤ (2.7182818286 : ℝ) ^ 207 := by
      have := Real.exp_nat_mul 1 207
      rw [mul_one] at this
      rw [show (207 : ℝ) = ((207 : ℕ) : ℝ) by norm_num, this]
      exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 207
    by_contra hc
    push Not at hc
    have : ((10 : ℝ) ^ 9) ^ 10 ≤ exp 20.7 ^ 10 := pow_le_pow_left₀ (by positivity) hc.le 10
    rw [h207] at this
    have := this.trans h207'
    norm_num at this
  have hLpos : 0 < L := by linarith
  have hexpL : exp L = N := Real.exp_log hNpos
  -- `12800 (L + 1)² ≤ N`
  have hNbig : 12800 * (L + 1) ^ 2 ≤ (N : ℝ) := by
    have hq := Real.quadratic_le_exp_of_nonneg (x := L - 20) (by linarith)
    have he : exp L = exp ((20 : ℕ) : ℝ) * exp (L - 20) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have h20 : (4.8e8 : ℝ) ≤ exp ((20 : ℕ) : ℝ) := le_trans (by norm_num) (exp_nat_ge 20)
    rw [← hexpL, he]
    have := mul_le_mul h20 hq (by nlinarith) (exp_pos _).le
    calc 12800 * (L + 1) ^ 2 = 12800 * ((L - 20) ^ 2 + 42 * (L - 20) + 441) := by ring
      _ ≤ 4.8e8 * (1 + (L - 20) + (L - 20) ^ 2 / 2) := by nlinarith [sq_nonneg (L - 20)]
      _ ≤ _ := this
  set Q : ℕ := 80 * ⌈L⌉₊ with hQdef
  have hQr : (Q : ℝ) = 80 * (⌈L⌉₊ : ℝ) := by rw [hQdef]; push_cast; ring
  have hceil1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hceil2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hQlo : 80 * L ≤ (Q : ℝ) := by rw [hQr]; linarith
  have hQhi : (Q : ℝ) ≤ 80 * (L + 1) := by rw [hQr]; linarith
  have hQ31 : 31 ≤ Q := by
    have : (31 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have hQ1 : 1 ≤ Q := by omega
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hsq : ∀ r : ℕ, r ≤ Q → 2 * r ^ 2 ≤ N + 1 := by
    intro r hr
    have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
    have : (2 : ℝ) * (r : ℝ) ^ 2 ≤ N := by
      have h0 : (0 : ℝ) ≤ r := by positivity
      have : (r : ℝ) ^ 2 ≤ (80 * (L + 1)) ^ 2 := pow_le_pow_left₀ h0 (hr'.trans hQhi) 2
      nlinarith
    have : 2 * r ^ 2 ≤ N := by exact_mod_cast this
    omega
  -- the split
  set S := (Icc 18 Q).filter Nat.Prime with hS
  have hmemS : ∀ r ∈ S, r.Prime ∧ r ≤ Q := by
    intro r hr; rw [hS, mem_filter, mem_Icc] at hr; exact ⟨hr.2, hr.1.2⟩
  have hsplit0 := (sum_filter_add_sum_filter_not S (· ≤ 31) (fun r => ((cls N r).card : ℝ))).symm
  rw [primes_18_31 hQ31] at hsplit0
  set R := S.filter (fun r => ¬ r ≤ 31) with hR
  set R1 := R.filter (· ≤ 127) with hR1
  set R' := R.filter (fun r => ¬ r ≤ 127) with hR'
  set R2 := R'.filter (· ≤ 511) with hR2
  set R'' := R'.filter (fun r => ¬ r ≤ 511) with hR''
  set R3 := R''.filter (· ≤ 2047) with hR3
  set RQ := R''.filter (fun r => ¬ r ≤ 2047) with hRQ
  have hsR := (sum_filter_add_sum_filter_not R (· ≤ 127) (fun r => ((cls N r).card : ℝ))).symm
  have hsR' := (sum_filter_add_sum_filter_not R' (· ≤ 511) (fun r => ((cls N r).card : ℝ))).symm
  have hsR'' := (sum_filter_add_sum_filter_not R'' (· ≤ 2047)
    (fun r => ((cls N r).card : ℝ))).symm
  have mR : ∀ r ∈ R, r.Prime ∧ r ≤ Q ∧ 31 < r := by
    intro r hr; rw [hR, mem_filter] at hr
    exact ⟨(hmemS r hr.1).1, (hmemS r hr.1).2, by omega⟩
  have mR1 : ∀ r ∈ R1, r.Prime ∧ r ≤ Q ∧ 31 < r ∧ r ≤ 127 := by
    intro r hr; rw [hR1, mem_filter] at hr; exact ⟨(mR r hr.1).1, (mR r hr.1).2.1, (mR r hr.1).2.2, hr.2⟩
  have mR' : ∀ r ∈ R', r.Prime ∧ r ≤ Q ∧ 127 < r := by
    intro r hr; rw [hR', mem_filter] at hr; exact ⟨(mR r hr.1).1, (mR r hr.1).2.1, by omega⟩
  have mR2 : ∀ r ∈ R2, r.Prime ∧ r ≤ Q ∧ 127 < r ∧ r ≤ 511 := by
    intro r hr; rw [hR2, mem_filter] at hr; exact ⟨(mR' r hr.1).1, (mR' r hr.1).2.1, (mR' r hr.1).2.2, hr.2⟩
  have mR'' : ∀ r ∈ R'', r.Prime ∧ r ≤ Q ∧ 511 < r := by
    intro r hr; rw [hR'', mem_filter] at hr; exact ⟨(mR' r hr.1).1, (mR' r hr.1).2.1, by omega⟩
  have mR3 : ∀ r ∈ R3, r.Prime ∧ r ≤ Q ∧ 511 < r ∧ r ≤ 2047 := by
    intro r hr; rw [hR3, mem_filter] at hr; exact ⟨(mR'' r hr.1).1, (mR'' r hr.1).2.1, (mR'' r hr.1).2.2, hr.2⟩
  have mRQ : ∀ r ∈ RQ, r.Prime ∧ r ≤ Q ∧ 2047 < r := by
    intro r hr; rw [hRQ, mem_filter] at hr; exact ⟨(mR'' r hr.1).1, (mR'' r hr.1).2.1, by omega⟩
  -- weights of the large groups
  have wpos : ∀ r : ℕ, 2 ≤ r → (0 : ℝ) ≤ 1 / ((r : ℝ) * ((r : ℝ) - 1)) := by
    intro r hr
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  have hw1 : ∑ r ∈ R1, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.004976 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := (Ioc 31 127).filter Nat.Prime) ?_ ?_)
      wsum_31_127
    · intro r hr; have := mR1 r hr; rw [mem_filter, mem_Ioc]; exact ⟨⟨this.2.2.1, this.2.2.2⟩, this.1⟩
    · intro r hr _; rw [mem_filter] at hr; exact wpos r hr.2.two_le
  have hw2 : ∑ r ∈ R2, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.0010544 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := (Ioc 127 511).filter Nat.Prime) ?_ ?_)
      wsum_127_511
    · intro r hr; have := mR2 r hr; rw [mem_filter, mem_Ioc]; exact ⟨⟨this.2.2.1, this.2.2.2⟩, this.1⟩
    · intro r hr _; rw [mem_filter] at hr; exact wpos r hr.2.two_le
  have hw3 : ∑ r ∈ R3, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 0.00020883 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := (Ioc 511 2047).filter Nat.Prime) ?_ ?_)
      wsum_511_2047
    · intro r hr; have := mR3 r hr; rw [mem_filter, mem_Ioc]; exact ⟨⟨this.2.2.1, this.2.2.2⟩, this.1⟩
    · intro r hr _; rw [mem_filter] at hr; exact wpos r hr.2.two_le
  have hwQ : ∑ r ∈ RQ, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 1 / 2047 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (t := Ioc 2047 Q) ?_ ?_) ?_
    · intro r hr; have := mRQ r hr; rw [mem_Ioc]; exact ⟨this.2.2, this.2.1⟩
    · intro r hr _; rw [mem_Ioc] at hr; exact wpos r (by omega)
    · have := sum_Ioc_inv_mul_pred_le (a := 2047) (by norm_num) Q
      push_cast at this; exact this
  -- cards
  have hc1 : R1.card ≤ 96 := by
    calc R1.card ≤ (Ioc 31 127).card := card_le_card (fun r hr => by
          have := mR1 r hr; rw [mem_Ioc]; exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 96 := by simp
  have hc2 : R2.card ≤ 384 := by
    calc R2.card ≤ (Ioc 127 511).card := card_le_card (fun r hr => by
          have := mR2 r hr; rw [mem_Ioc]; exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 384 := by simp
  have hc3 : R3.card ≤ 1536 := by
    calc R3.card ≤ (Ioc 511 2047).card := card_le_card (fun r hr => by
          have := mR3 r hr; rw [mem_Ioc]; exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 1536 := by simp
  have hcQ : RQ.card ≤ Q := by
    calc RQ.card ≤ (Ioc 0 Q).card := card_le_card (fun r hr => by
          have := mRQ r hr; rw [mem_Ioc]; exact ⟨by omega, this.2.1⟩)
      _ = Q := by simp
  have hl2 := Real.log_two_lt_d9
  -- group 31
  have lb31 : Real.log 32 ≤ 3.4658 := by
    have := log_le_pow2 32 (by norm_num) 1 5 (by norm_num) (by norm_num)
    linarith [show (5 : ℝ) / 1 * 0.6931471808 ≤ 3.4658 by norm_num]
  have G31 := group_le hN1 hL ({19, 23, 29, 31} : Finset ℕ) (b := 32) (lb := 3.4658) (θ := 19/50) (F := 1.0738)
    (k := 1.5035) (w := 0.007208) (by intro r hr; simp only [mem_insert, mem_singleton] at hr; rcases hr with h | h | h | h <;> subst h <;> exact ⟨by norm_num, hsq _ (by omega), by norm_num⟩)
    (by push_cast; exact lb31) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 13 (x := lam) (y₀ := (20.7 - 2 * 3.4658)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (19/50 : ℝ)) * lam)
        (y₀ := (1 - 2 * (19/50 : ℝ)) * (20.7 - 2 * 3.4658)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 13 * (1 + ((20.7 - 2 * 3.4658) - (13 : ℕ)) +
          ((20.7 - 2 * 3.4658) - (13 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (19/50 : ℝ)) * (20.7 - 2 * 3.4658) - (3 : ℕ)) +
          ((1 - 2 * (19/50 : ℝ)) * (20.7 - 2 * 3.4658) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0738 := by norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_insert, Finset.sum_singleton])
  have C31 := count_term hNpos hLdef hL ({19, 23, 29, 31} : Finset ℕ) 4 (by decide)
    (cnt_le' 4 (a := 1 - 19/50) (c := 0.004923315) (E₀ := 355094) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 12 (y := (1 - 19/50) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 127
  have lb127 : Real.log 128 ≤ 4.8521 := by
    have := log_le_pow2 128 (by norm_num) 1 7 (by norm_num) (by norm_num)
    linarith [show (7 : ℝ) / 1 * 0.6931471808 ≤ 4.8521 by norm_num]
  have G127 := group_le hN1 hL R1 (b := 128) (lb := 4.8521) (θ := 17/50) (F := 1.0603)
    (k := 1.8826) (w := 0.004976) (fun r hr => ⟨(mR1 r hr).1, hsq r (mR1 r hr).2.1, by have := (mR1 r hr).2.2.2; exact_mod_cast (by omega : r ≤ 128)⟩)
    (by push_cast; exact lb127) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 10 (x := lam) (y₀ := (20.7 - 2 * 4.8521)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (17/50 : ℝ)) * lam)
        (y₀ := (1 - 2 * (17/50 : ℝ)) * (20.7 - 2 * 4.8521)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 10 * (1 + ((20.7 - 2 * 4.8521) - (10 : ℕ)) +
          ((20.7 - 2 * 4.8521) - (10 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (17/50 : ℝ)) * (20.7 - 2 * 4.8521) - (3 : ℕ)) +
          ((1 - 2 * (17/50 : ℝ)) * (20.7 - 2 * 4.8521) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0603 := by norm_num
      linarith)
    (by norm_num) (by norm_num) hw1
  have C127 := count_term hNpos hLdef hL R1 96 hc1
    (cnt_le' 96 (a := 1 - 17/50) (c := 0.050415859) (E₀ := 832233) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 13 (y := (1 - 17/50) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 511
  have lb511 : Real.log 512 ≤ 6.2384 := by
    have := log_le_pow2 512 (by norm_num) 1 9 (by norm_num) (by norm_num)
    linarith [show (9 : ℝ) / 1 * 0.6931471808 ≤ 6.2384 by norm_num]
  have G511 := group_le hN1 hL R2 (b := 512) (lb := 6.2384) (θ := 13/50) (F := 1.0422)
    (k := 2.5173) (w := 0.0010544) (fun r hr => ⟨(mR2 r hr).1, hsq r (mR2 r hr).2.1, by have := (mR2 r hr).2.2.2; exact_mod_cast (by omega : r ≤ 512)⟩)
    (by push_cast; exact lb511) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 8 (x := lam) (y₀ := (20.7 - 2 * 6.2384)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (13/50 : ℝ)) * lam)
        (y₀ := (1 - 2 * (13/50 : ℝ)) * (20.7 - 2 * 6.2384)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 8 * (1 + ((20.7 - 2 * 6.2384) - (8 : ℕ)) +
          ((20.7 - 2 * 6.2384) - (8 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (13/50 : ℝ)) * (20.7 - 2 * 6.2384) - (3 : ℕ)) +
          ((1 - 2 * (13/50 : ℝ)) * (20.7 - 2 * 6.2384) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0422 := by norm_num
      linarith)
    (by norm_num) (by norm_num) hw2
  have C511 := count_term hNpos hLdef hL R2 384 hc2
    (cnt_le' 384 (a := 1 - 13/50) (c := 0.03751375) (E₀ := 4473852) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 15 (y := (1 - 13/50) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group 2047
  have lb2047 : Real.log 2048 ≤ 7.6247 := by
    have := log_le_pow2 2048 (by norm_num) 1 11 (by norm_num) (by norm_num)
    linarith [show (11 : ℝ) / 1 * 0.6931471808 ≤ 7.6247 by norm_num]
  have G2047 := group_le hN1 hL R3 (b := 2048) (lb := 7.6247) (θ := 1/5) (F := 1.0849)
    (k := 3.7978) (w := 0.00020883) (fun r hr => ⟨(mR3 r hr).1, hsq r (mR3 r hr).2.1, by have := (mR3 r hr).2.2.2; exact_mod_cast (by omega : r ≤ 2048)⟩)
    (by push_cast; exact lb2047) (by norm_num) (by norm_num) (by norm_num)
    (fun lam hlam => by
      have e1 := exp_neg_le2 5 (x := lam) (y₀ := (20.7 - 2 * 7.6247)) (by norm_num) hlam
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (1/5 : ℝ)) * lam)
        (y₀ := (1 - 2 * (1/5 : ℝ)) * (20.7 - 2 * 7.6247)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 5 * (1 + ((20.7 - 2 * 7.6247) - (5 : ℕ)) +
          ((20.7 - 2 * 7.6247) - (5 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (1/5 : ℝ)) * (20.7 - 2 * 7.6247) - (3 : ℕ)) +
          ((1 - 2 * (1/5 : ℝ)) * (20.7 - 2 * 7.6247) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0849 := by norm_num
      linarith)
    (by norm_num) (by norm_num) hw3
  have C2047 := count_term hNpos hLdef hL R3 1536 hc3
    (cnt_le' 1536 (a := 1 - 1/5) (c := 0.044004864) (E₀ := 15255674) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 16 (y := (1 - 1/5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- group Q
  have hlogQ : Real.log Q ≤ 5 / 128 * (L + 1) + 6.62465 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (Q : ℝ) / 2048) (by positivity)
    rw [Real.log_div hQ0.ne' (by norm_num)] at h1
    have h2048 : Real.log 2048 = 11 * Real.log 2 := by
      rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; push_cast; ring
    have : (Q : ℝ) / 2048 ≤ 80 * (L + 1) / 2048 := by linarith
    linarith
  set lbQ : ℝ := 5 / 128 * (L + 1) + 6.62465 with hlbQ
  set lamQ : ℝ := L - 2 * lbQ with hlamQ
  have hlamQ0 : 20.7 - 5 / 64 * 21.7 - 13.2493 ≤ lamQ := by rw [hlamQ, hlbQ]; linarith
  have hpQ : 0 < lamQ := lt_of_lt_of_le (by norm_num) hlamQ0
  have hRQb : ∀ r ∈ RQ, r.Prime ∧ 2 * r ^ 2 ≤ N + 1 ∧ (r : ℝ) ≤ Q :=
    fun r hr => ⟨(mRQ r hr).1, hsq r (mRQ r hr).2.1, by exact_mod_cast (mRQ r hr).2.1⟩
  have hperQ : ∀ r ∈ RQ, ((cls N r).card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 5) +
      1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ * ((1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1))) := by
    intro r hr
    obtain ⟨hp, h2, hrb⟩ := hRQb r hr
    have hlog := log_cls_ge (N := N) hN1 hp.one_lt.le hrb
    have hc := cls_card_pow_gen hp h2 hN1 (θ := 1 / 5) (by norm_num) (by norm_num) hpQ
      (by rw [hlamQ]; linarith)
    have hF : 1 + 2 * exp (-lamQ) + 2 * exp (-((1 - 2 * (1 / 5 : ℝ)) * lamQ)) ≤ 1.0706 := by
      have e1 := exp_neg_le2 5 (x := lamQ) (y₀ := 20.7 - 5 / 64 * 21.7 - 13.2493) (by norm_num) hlamQ0
      have e2 := exp_neg_le2 3 (x := (1 - 2 * (1 / 5 : ℝ)) * lamQ)
        (y₀ := (1 - 2 * (1 / 5 : ℝ)) * (20.7 - 5 / 64 * 21.7 - 13.2493)) (by norm_num) (by nlinarith)
      have : 1 + 2 * (1 / ((2.7182818283 : ℝ) ^ 5 * (1 + ((20.7 - 5 / 64 * 21.7 - 13.2493) - (5 : ℕ)) +
          ((20.7 - 5 / 64 * 21.7 - 13.2493) - (5 : ℕ)) ^ 2 / 2))) +
        2 * (1 / ((2.7182818283 : ℝ) ^ 3 * (1 + ((1 - 2 * (1 / 5 : ℝ)) * (20.7 - 5 / 64 * 21.7 - 13.2493) - (3 : ℕ)) +
          ((1 - 2 * (1 / 5 : ℝ)) * (20.7 - 5 / 64 * 21.7 - 13.2493) - (3 : ℕ)) ^ 2 / 2))) ≤ 1.0706 := by norm_num
      linarith
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hp.two_le
    have hrr : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    calc ((cls N r).card : ℝ) ≤ _ := hc
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 /
            (lamQ * ((r : ℝ) * ((r : ℝ) - 1))) := by gcongr
      _ = _ := by field_simp
  have GQ : ∑ r ∈ RQ, ((cls N r).card : ℝ) ≤ RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) +
      1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047) * 3.5967 / L := by
    calc ∑ r ∈ RQ, ((cls N r).card : ℝ) ≤ ∑ r ∈ RQ, ((N : ℝ) ^ ((1 : ℝ) / 5) +
          1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ * ((1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)))) :=
          sum_le_sum hperQ
      _ = RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ *
            ∑ r ∈ RQ, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
      _ ≤ RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ *
            (1 / 2047) := by gcongr
      _ ≤ _ := by
          have hkl : L ≤ 3.5967 * lamQ := by rw [hlamQ, hlbQ]; linarith
          have : 1 / lamQ ≤ 3.5967 / L := by rw [div_le_div_iff₀ hpQ hLpos]; linarith
          have hA : 0 ≤ 1 / (1 / 5 : ℝ) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047) := by positivity
          calc RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) + 1 / (1 / 5) * ((N : ℝ) + 1) * 1.0706 / lamQ * (1 / 2047)
              = RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) +
                  (1 / (1 / 5 : ℝ) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047)) * (1 / lamQ) := by ring
            _ ≤ RQ.card * (N : ℝ) ^ ((1 : ℝ) / 5) +
                  (1 / (1 / 5 : ℝ) * ((N : ℝ) + 1) * 1.0706 * (1 / 2047)) * (3.5967 / L) := by gcongr
            _ = _ := by ring
  have CQ : (RQ.card : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 5) * L ≤ 0.002406516 * N := by
    have hcard : (RQ.card : ℝ) * L ≤ 84 * L ^ 2 := by
      have h1 : (RQ.card : ℝ) ≤ Q := by exact_mod_cast hcQ
      have h2 : (RQ.card : ℝ) ≤ 84 * L := by linarith
      nlinarith
    have hc := cnt_le' 84 (a := 1 - 1 / 5) (c := 0.002406516) (E₀ := 15255674) (by norm_num) (by norm_num) hL
      (le_trans (by norm_num) (exp_ge_q 16 (y := (1 - 1 / 5) * 20.7) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    push_cast at hc
    have hNθ : (N : ℝ) ^ ((1 : ℝ) / 5) = exp (L * (1 / 5)) := by
      rw [Real.rpow_def_of_pos hNpos]
    have hE := exp_pos (L * (1 / 5))
    rw [hNθ]
    calc (RQ.card : ℝ) * exp (L * (1 / 5)) * L = ((RQ.card : ℝ) * L) * exp (L * (1 / 5)) := by ring
      _ ≤ (84 * L ^ 2) * exp (L * (1 / 5)) := mul_le_mul_of_nonneg_right hcard hE.le
      _ ≤ 0.002406516 * exp ((1 - 1 / 5) * L) * exp (L * (1 / 5)) :=
          mul_le_mul_of_nonneg_right hc hE.le
      _ = 0.002406516 * N := by
          rw [mul_assoc, ← Real.exp_add, show (1 - 1 / 5) * L + L * (1 / 5) = L by ring, hexpL]
  -- assemble
  have htail := tail_le (N := N) hQ1
  have hNQ : (N : ℝ) / Q * L ≤ N / 80 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hQ0 (by norm_num)]
    have := mul_le_mul_of_nonneg_left hQlo hNpos.le
    linarith
  have htailL := mul_le_mul_of_nonneg_right htail hLpos.le
  have G31' := mul_le_mul_of_nonneg_right G31 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G31'
  have G127' := mul_le_mul_of_nonneg_right G127 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G127'
  have G511' := mul_le_mul_of_nonneg_right G511 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G511'
  have G2047' := mul_le_mul_of_nonneg_right G2047 hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at G2047'
  have GQ' := mul_le_mul_of_nonneg_right GQ hLpos.le
  rw [add_mul, div_mul_cancel₀ _ hLpos.ne'] at GQ'
  rw [le_div_iff₀ hLpos, hsplit0, hsR, hsR', hsR'']
  simp only [add_mul]
  push_cast at C31 C127 C511 C2047
  linarith

/-- **Counting step, odd `N`.** If no prime `p < N` has `N - p` square-free, the primes `p ≤ N`
with `p ≡ N + 2 mod 4` lie in the classes `N + 2r² mod 4r²` for the primes `3 ≤ r ≤ 17`, the
classes `N mod r²` for the primes `18 ≤ r ≤ Q`, or the tail. -/
theorem card_le_of_no_rep_odd {N : ℕ} (Q : ℕ) (hO : Odd N)
    (hno : ¬ ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p)) :
    ((primesAP N 4 (N + 2)).card : ℝ) ≤
      ∑ r ∈ (Icc 3 17).filter Nat.Prime, ((primesAP N (4 * r ^ 2) (N + 2 * r ^ 2)).card : ℝ) +
      ∑ r ∈ (Icc 18 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
        ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by
  classical
  set A := primesAP N 4 (N + 2) with hA
  set B0 := ((Icc 3 17).filter Nat.Prime).biUnion
    (fun r => primesAP N (4 * r ^ 2) (N + 2 * r ^ 2)) with hB0
  set B1 := ((Icc 18 Q).filter Nat.Prime).biUnion (fun r => cls N r) with hB1
  set B2 := (Ioc Q N).biUnion (fun n => (range N).filter (fun p => n ^ 2 ∣ N - p)) with hB2
  have hNo : N % 2 = 1 := Nat.odd_iff.mp hO
  have hsub : A ⊆ B0 ∪ B1 ∪ B2 := by
    intro p hp
    rw [hA, primesAP, mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hp, h4⟩ := hp
    have hpne : p ≠ N := by rintro rfl; omega
    have hpN' : p < N := lt_of_le_of_ne hpN hpne
    have hm : ¬ Squarefree (N - p) := fun hsq => hno ⟨p, hp, hpN', hsq⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hm
    push Not at hm
    obtain ⟨r, hr, hrr⟩ := hm
    have hr2 : r ≠ 2 := by
      rintro rfl
      have : 4 ∣ N - p := hrr
      omega
    have hr3 : 3 ≤ r := by have := hr.two_le; omega
    have hrr' : r ^ 2 ∣ N - p := by rw [sq]; exact hrr
    rw [mem_union, mem_union]
    by_cases h17 : r ≤ 17
    · left; left
      rw [hB0, mem_biUnion]
      refine ⟨r, by rw [mem_filter, mem_Icc]; exact ⟨⟨hr3, h17⟩, hr⟩, ?_⟩
      rw [primesAP, mem_filter, mem_Icc]
      exact ⟨⟨hp1, hpN⟩, hp, mem_class4 (hr.odd_of_ne_two hr2) hpN h4 hrr'⟩
    · by_cases hQr : r ≤ Q
      · left; right
        rw [hB1, mem_biUnion]
        refine ⟨r, by rw [mem_filter, mem_Icc]; exact ⟨⟨by omega, hQr⟩, hr⟩, ?_⟩
        rw [cls, mem_filter, mem_Icc]
        refine ⟨⟨hp1, by omega⟩, hp, ?_⟩
        exact ((Nat.modEq_iff_dvd' hpN).mpr hrr')
      · right
        rw [hB2, mem_biUnion]
        have hpos : 0 < N - p := by omega
        have hrle : r ≤ N - p := by
          have := Nat.le_of_dvd hpos hrr
          nlinarith
        refine ⟨r, by rw [mem_Ioc]; omega, ?_⟩
        rw [mem_filter, mem_range]
        exact ⟨hpN', hrr'⟩
  have hcard : A.card ≤
      ∑ r ∈ (Icc 3 17).filter Nat.Prime, (primesAP N (4 * r ^ 2) (N + 2 * r ^ 2)).card +
      ∑ r ∈ (Icc 18 Q).filter Nat.Prime, (cls N r).card + ∑ n ∈ Ioc Q N, N / n ^ 2 := by
    calc A.card ≤ (B0 ∪ B1 ∪ B2).card := card_le_card hsub
      _ ≤ (B0 ∪ B1).card + B2.card := card_union_le _ _
      _ ≤ B0.card + B1.card + B2.card := by
          have := card_union_le B0 B1; omega
      _ ≤ _ := by
        apply add_le_add (add_le_add card_biUnion_le card_biUnion_le)
        exact card_biUnion_le.trans (sum_le_sum fun n _ => card_dvd_sub_le N n)
  exact_mod_cast hcard

/-- One small modulus `4r²`, `3 ≤ r ≤ 17`, from the upper half of `BMORCor16`. -/
lemma small_class_le (hB : BMORCor16) {N r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr17 : r ≤ 17)
    (hN : 10 ^ 9 ≤ N) :
    ((primesAP N (4 * r ^ 2) (N + 2 * r ^ 2)).card : ℝ) ≤
      1 / (2 * (r : ℝ) * ((r : ℝ) - 1)) *
        ((N : ℝ) / Real.log N * (1 + 5 / (2 * Real.log N))) + 1 := by
  have hNR : (10 ^ 9 : ℝ) ≤ N := by exact_mod_cast hN
  have hL := log_ge_207 hNR
  have hLpos : 0 < Real.log N := by linarith
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by have := hr.two_le; omega)
  have hmain0 : 0 ≤ 1 / (2 * (r : ℝ) * ((r : ℝ) - 1)) *
      ((N : ℝ) / Real.log N * (1 + 5 / (2 * Real.log N))) := by
    have : 0 < 2 * (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  by_cases hc : Nat.Coprime (N + 2 * r ^ 2) (4 * r ^ 2)
  · have hq1 : 1 ≤ 4 * r ^ 2 := by have := hr.two_le; nlinarith
    have hr2' : r ^ 2 ≤ 289 := by
      calc r ^ 2 ≤ 17 ^ 2 := Nat.pow_le_pow_left hr17 2
        _ = 289 := by norm_num
    have hq2 : 4 * r ^ 2 ≤ 1200 := by omega
    have hq3 : 50 * (4 * r ^ 2) ^ 2 ≤ N := by
      have : (4 * r ^ 2) ^ 2 ≤ 1156 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h := (hB (4 * r ^ 2) (N + 2 * r ^ 2) N hq1 hq2 hc hq3).2
    rw [totient_four_sq hr hr2] at h
    have hcast : (((2 * r * (r - 1) : ℕ)) : ℝ) = 2 * (r : ℝ) * ((r : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hr.one_lt.le]; push_cast; ring
    rw [hcast] at h
    have e : (N : ℝ) / (2 * (r : ℝ) * ((r : ℝ) - 1) * Real.log N) * (1 + 5 / (2 * Real.log N)) =
        1 / (2 * (r : ℝ) * ((r : ℝ) - 1)) *
          ((N : ℝ) / Real.log N * (1 + 5 / (2 * Real.log N))) := by
      have : (2 * (r : ℝ) * ((r : ℝ) - 1)) ≠ 0 := by nlinarith
      field_simp
    rw [e] at h
    linarith
  · have := card_primesAP_le_one (x := N) hc
    have : ((primesAP N (4 * r ^ 2) (N + 2 * r ^ 2)).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith

/-- **Dudek 2017 for odd `N > 10⁹`, CONDITIONAL ON `BMORCor16`.** Every odd `N > 10⁹` is
`p + (N - p)` with `p < N` prime and `N - p` square-free. -/
theorem dudek_odd_from_1e9 (hB : BMORCor16) (N : ℕ) (hO : Odd N) (hN : 10 ^ 9 < N) :
    ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) := by
  by_contra hno
  have hNR : (10 ^ 9 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 20.7 ≤ L := log_ge_207 hNR
  have hLpos : 0 < L := by linarith
  -- the lower bound for the class `N + 2 mod 4`
  have hc4 : Nat.Coprime (N + 2) 4 := by
    have ho : Odd (N + 2) := by rcases hO with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have : Nat.Coprime (N + 2) (2 ^ 2) := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ho)
    simpa using this
  have hlow := (hB 4 (N + 2) N (by norm_num) (by norm_num) hc4 (by omega)).1
  have ht4 : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.totient_prime_pow Nat.prime_two two_pos]; norm_num
  rw [ht4] at hlow
  -- the count
  have hQ : 17 ≤ 80 * ⌈L⌉₊ := by
    have : (1 : ℝ) ≤ ⌈L⌉₊ := le_trans (by linarith) (Nat.le_ceil L)
    have : 1 ≤ ⌈L⌉₊ := by exact_mod_cast this
    omega
  have hcount := card_le_of_no_rep_odd (80 * ⌈L⌉₊) hO hno
  have hbad := bad_sum_ge19 N hNR
  rw [← hLdef] at hbad
  have hsmall : (Icc 3 17).filter Nat.Prime = {3, 5, 7, 11, 13, 17} := by decide
  rw [hsmall] at hcount
  set Y := (N : ℝ) / L * (1 + 5 / (2 * L)) with hY
  have s3 := small_class_le hB (r := 3) (by norm_num) (by norm_num) (by norm_num) hN.le
  have s5 := small_class_le hB (r := 5) (by norm_num) (by norm_num) (by norm_num) hN.le
  have s7 := small_class_le hB (r := 7) (by norm_num) (by norm_num) (by norm_num) hN.le
  have s11 := small_class_le hB (r := 11) (by norm_num) (by norm_num) (by norm_num) hN.le
  have s13 := small_class_le hB (r := 13) (by norm_num) (by norm_num) (by norm_num) hN.le
  have s17 := small_class_le hB (r := 17) (by norm_num) (by norm_num) (by norm_num) hN.le
  rw [← hLdef, ← hY] at s3 s5 s7 s11 s13 s17
  norm_num at s3 s5 s7 s11 s13 s17
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton] at hcount
  -- `Y ≤ 1.1208 N / L` and `N / L ≥ 600`
  set X := (N : ℝ) / L with hX
  have hX0 : 0 ≤ X := by positivity
  have hYX : Y ≤ X * 1.1208 := by
    rw [hY]
    have : 5 / (2 * L) ≤ 0.1208 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  have hLle : L ≤ N / 1000 + 7 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (N : ℝ) / 1000) (by positivity)
    rw [Real.log_div hNpos.ne' (by norm_num)] at h1
    have : Real.log 1000 ≤ 10 * Real.log 2 := by
      have h := Real.log_le_log (x := 1000) (y := (2 : ℝ) ^ 10) (by norm_num) (by norm_num)
      rw [Real.log_pow] at h; push_cast at h; exact h
    linarith [Real.log_two_lt_d9]
  have hX600 : 600 ≤ X := by
    rw [hX, le_div_iff₀ hLpos]; linarith
  have hlow' : X / 2 < ((primesAP N 4 (N + 2)).card : ℝ) := by
    have e : (N : ℝ) / (2 * L) = X / 2 := by rw [hX]; field_simp
    rw [← e]; exact hlow
  have hbad' : (∑ r ∈ (Icc 18 (80 * ⌈L⌉₊)).filter Nat.Prime, ((cls N r).card : ℝ)) +
      ∑ n ∈ Ioc (80 * ⌈L⌉₊) N, ((N / n ^ 2 : ℕ) : ℝ) ≤ 0.11 * X := by
    rw [hX, ← mul_div_assoc]; exact hbad
  have hYnn : 0 ≤ Y := by
    rw [hY]; positivity
  linarith

end LeanLab.AlmostPrimes.U1445DudekOdd
