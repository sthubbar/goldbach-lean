module

public import LeanLab.Verifications.Top50.P32

/-!
U-1437, run 20261021T1603Z-28836, I-5067, Dudek 2017. A cheap kernel checker for the finite
part of Dudek's theorem: every N with 3 ≤ N ≤ B is p + m, p prime, m ≥ 1 square-free.

Design, against the Goldbach windows of Top50/BitSieve2.lean:
* the window bitmap marks NON square-free numbers, so only primes r with r² below the window
  end are sieved, by the pattern of multiples of r²; for r² > W at most one bit, and the branch
  is skipped with a small-number comparison when the window holds no multiple, so a window of
  W bits costs about 170 + 140 big operations near 10^9, not 3400 as for the prime bitmap;
* no `%` on big numbers: `&&& (2^W - 1)` masks the bitmap, the target mask is
  `(2^(B-A+1) - 1) <<< (A - lo)`;
* both parities at once, so the same windows cover odd N, the first 16 primes q ≤ 53 suffice
  for every N ≤ 1.004e9, against 280 primes for Goldbach.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Verifications.U1437Fast

open LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- Every `N` with `3 ≤ N ≤ B` is `p + (N - p)` with `p < N` prime and `N - p` square-free. -/
def SqfUpTo (B : ℕ) : Prop :=
  ∀ N, 3 ≤ N → N ≤ B → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p)

/-- Non square-free marks on the window `[lo, lo + W)`, bit `m - lo`, from the primes in the list.
For `r² ≤ W` the full pattern of multiples of `r²`; otherwise the one multiple, if any. -/
def nsq (lo W : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: t =>
    if r * r ≤ W then (rep (r * r) (jOf (r * r) W) <<< (firstMul (r * r) lo - lo)) ||| nsq lo W t
    else if firstMul (r * r) lo - lo < W then (1 <<< (firstMul (r * r) lo - lo)) ||| nsq lo W t
    else nsq lo W t

theorem nsq_of_dvd (lo W m r : ℕ) (hr : 1 ≤ r) (hlo : lo ≤ m) (hmW : m < lo + W)
    (hdv : r * r ∣ m) : ∀ L : List ℕ, r ∈ L → (nsq lo W L).testBit (m - lo) = true := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro hmem
    by_cases har : a = r
    · rw [har]
      simp only [nsq]
      generalize hd : r * r = d at hdv ⊢
      have hd1 : 1 ≤ d := by rw [← hd]; simpa using Nat.mul_le_mul hr hr
      obtain ⟨k, hk⟩ := hdv
      have hf1 := le_firstMul d lo hd1
      have hf2 := firstMul_le d lo k hd1 (by omega)
      have hfd := dvd_firstMul d lo
      have hdiff : d ∣ m - firstMul d lo := Nat.dvd_sub ⟨k, hk⟩ hfd
      split_ifs with h1 h2
      · simp only [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true,
          decide_eq_true_eq]
        left
        have hJ := lt_jOf d W hd1
        refine ⟨by omega, (testBit_rep d hd1 _ _).mpr ⟨by omega, ?_⟩⟩
        rw [show m - lo - (firstMul d lo - lo) = m - firstMul d lo by omega]
        exact hdiff
      · have h0 : m - firstMul d lo = 0 := by
          obtain ⟨c, hc⟩ := hdiff
          rcases c with _ | c
          · simpa using hc
          · have : d * (c + 1) ≥ d := Nat.le_mul_of_pos_right d (by omega)
            omega
        simp only [Nat.testBit_or, Bool.or_eq_true]
        left
        rw [show m - lo = firstMul d lo - lo by omega, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
      · exfalso
        omega
    · have hmem' : r ∈ t := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm har
        · exact h
      have := ih hmem'
      simp only [nsq]
      split_ifs <;> simp [Nat.testBit_or, this]

/-- `31700²`, the bound up to which `P32` gives every sieving prime. -/
def BB : ℕ := 31700 * 31700

/-- The sieving primes, those `r` in `P32` with `r * r < L`. -/
def SR (L : ℕ) : List ℕ := P32.filter (fun r => r * r < L)

theorem mem_SR {L r : ℕ} (hL : L ≤ BB) (hp : r.Prime) (hrL : r * r < L) : r ∈ SR L := by
  unfold SR
  rw [List.mem_filter]
  refine ⟨P32_complete r ?_ hp, by simpa using hrL⟩
  by_contra h
  have h := not_lt.mp h
  have : 31700 * 31700 ≤ r * r := Nat.mul_le_mul h h
  unfold BB at hL
  omega

/-- Square-free bitmap of `[lo, lo + W)`: bit `i` set iff `i < W` and `lo + i` is not marked. -/
def sfm (lo W : ℕ) : ℕ := (nsq lo W (SR (lo + W)) &&& (2 ^ W - 1)) ^^^ (2 ^ W - 1)

theorem sqf_of_sfm {lo W i : ℕ} (h1 : 1 ≤ lo) (hW : lo + W ≤ BB)
    (h : (sfm lo W).testBit i = true) : Squarefree (lo + i) := by
  simp only [sfm, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one] at h
  by_cases hiW : i < W
  · simp only [hiW, decide_true, Bool.and_true] at h
    rw [Nat.squarefree_iff_prime_squarefree]
    intro r hr hdv
    have hm0 : 0 < lo + i := by omega
    have hrr : r * r ≤ lo + i := Nat.le_of_dvd hm0 hdv
    have hb := nsq_of_dvd lo W (lo + i) r hr.one_lt.le (by omega) (by omega) hdv
      (SR (lo + W)) (mem_SR hW hr (by omega))
    rw [show lo + i - lo = i by omega] at hb
    rw [hb] at h
    simp at h
  · simp [hiW] at h

/-- Target mask: bit `N - lo` for `A ≤ N ≤ B`. -/
def tm (lo A B : ℕ) : ℕ := (2 ^ (B - A + 1) - 1) <<< (A - lo)

theorem testBit_tm {lo A B N : ℕ} (hlo : lo ≤ A) (hA : A ≤ N) (hB : N ≤ B) :
    (tm lo A B).testBit (N - lo) = true := by
  simp only [tm, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

/-- Soundness of one window check. -/
theorem sqf_of_wcheck {lo W A B : ℕ} {Q : List ℕ} (h1 : 1 ≤ lo) (hW : lo + W ≤ BB)
    (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (h : tm lo A B &&& gm (sfm lo W) Q = tm lo A B) :
    ∀ N, A ≤ N → N ≤ B → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) := by
  intro N hA hB
  have ht := testBit_tm hlo hA hB
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at ht
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ Q _ ht.2
  have hs := sqf_of_sfm h1 hW hp
  refine ⟨q, hQ q hq, by omega, ?_⟩
  rw [show N - q = lo + (N - lo - q) by omega]
  exact hs

/-- Extend `SqfUpTo a` by one window `[A, B]`, `A = a + 1` as a numeral. -/
theorem sqf_extend {lo W a A B : ℕ} {Q : List ℕ} (ha : SqfUpTo a) (hA : a + 1 = A)
    (h1 : 1 ≤ lo) (hW : lo + W ≤ BB) (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (h : tm lo A B &&& gm (sfm lo W) Q = tm lo A B) : SqfUpTo B := by
  intro N h3 hNB
  by_cases hNa : N ≤ a
  · exact ha N h3 hNa
  · exact sqf_of_wcheck h1 hW hlo hQ h N (by omega) hNB

theorem sqfUpTo_two : SqfUpTo 2 := fun N h3 h2 => absurd (le_trans h3 h2) (by norm_num)

theorem sqf_mono {a b : ℕ} (h : SqfUpTo b) (hab : a ≤ b) : SqfUpTo a :=
  fun N h3 hN => h N h3 (le_trans hN hab)

/-- The 16 test primes `q ≤ 53`, prime. -/
theorem q16_prime : ∀ q ∈ P10k.take 16, q.Prime := take_prime 16

/-- Small sanity check: every `N` from 3 to 10000. -/
theorem check_1e4 : tm 1 3 10000 &&& gm (sfm 1 10000) (P10k.take 16) = tm 1 3 10000 := by
  decide +kernel

theorem sqfUpTo_1e4 : SqfUpTo 10000 :=
  sqf_extend (a := 2) (A := 3) (lo := 1) (W := 10000) (B := 10000) sqfUpTo_two rfl (by norm_num) (by norm_num [BB]) (by norm_num) q16_prime check_1e4

end LeanLab.Verifications.U1437Fast
