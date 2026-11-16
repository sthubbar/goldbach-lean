module

public import Mathlib
public import LeanLab.GvLtR1989.Sieve

/-!
# Least Goldbach primes and the ratio bound on one block

* `minGB n`: the least prime `p` with `n - p` prime, and `0` when there is none.
* `GBBound A B q`: every even `n` in `[A, B]` is `p + (n - p)` with `p ≤ q` and both prime.
* `gbBound_of_owcheck`: one window equality of `Core.lean` gives such a bound.
* `le_log_of`: certified lower bounds for `log` from a Taylor upper bound for `exp`.
* `goodRatio_of_bound`: a bound `q` and certified `r ≤ log A`, `s ≤ log r` give, for every
  even `n` in `[A, B]`, that `minGB n` and `n - minGB n` are prime and
  `minGB n < c · log² n · log log n`.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

open Finset

/-- The least prime `p` with `n - p` prime, and `0` when there is no such prime. -/
noncomputable def minGB (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, p.Prime ∧ (n - p).Prime then Nat.find h else 0

/-- With a Goldbach partition `n = p + (n - p)` in hand, `minGB n` is prime, `n - minGB n` is
prime and `minGB n ≤ p`. -/
theorem minGB_spec {n p : ℕ} (hp : p.Prime) (hnp : (n - p).Prime) :
    (minGB n).Prime ∧ (n - minGB n).Prime ∧ minGB n ≤ p := by
  classical
  have hex : ∃ p, p.Prime ∧ (n - p).Prime := ⟨p, hp, hnp⟩
  unfold minGB
  rw [dif_pos hex]
  exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, Nat.find_min' hex ⟨hp, hnp⟩⟩

/-- Every even `n` with `A ≤ n ≤ B` has a Goldbach partition whose smaller prime is at most
`q`. -/
def GBBound (A B q : ℕ) : Prop :=
  ∀ n : ℕ, Even n → A ≤ n → n ≤ B → ∃ p, p.Prime ∧ (n - p).Prime ∧ p ≤ q

theorem take_le (K q : ℕ) (h : (QKo K).all (fun x => decide (x ≤ q)) = true) :
    ∀ x ∈ QKo K, x ≤ q := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simpa using this

/-- One window check bounds the least Goldbach prime on `[A, B]`. -/
theorem gbBound_of_owcheck {lo Wb A B K q : ℕ} (h3 : 3 ≤ lo) (hlo1 : lo % 2 = 1)
    (hW : lo + 2 * Wb ≤ 20000 * 20000) (hlo : lo < A) (hAe : A % 2 = 0)
    (hq : ∀ x ∈ QKo K, x ≤ q)
    (h : oem lo A B &&& gmo (opm lo Wb) (QKo K) = oem lo A B) : GBBound A B q := by
  intro n hn hA hB
  obtain ⟨x, hx, hpr⟩ := partition_of_owcheck h3 hlo1 hW hlo hAe h n hA hB (Nat.even_iff.mp hn)
  exact ⟨x, (QKo_prime K x hx).1, hpr, hq x hx⟩

/-- Join two adjacent ranges of even numbers. -/
theorem join {P : ℕ → Prop} {A B A' C : ℕ}
    (h1 : ∀ n, Even n → A ≤ n → n ≤ B → P n) (h2 : ∀ n, Even n → A' ≤ n → n ≤ C → P n)
    (hBA : B + 2 = A') (hB : Even B) : ∀ n, Even n → A ≤ n → n ≤ C → P n := by
  intro n hn hA hC
  by_cases h : n ≤ B
  · exact h1 n hn hA h
  · apply h2 n hn _ hC
    obtain ⟨k, hk⟩ := hn
    obtain ⟨j, hj⟩ := hB
    omega

/-- Join two adjacent bounds. -/
theorem GBBound.join {A B A' C q : ℕ} (h1 : GBBound A B q) (h2 : GBBound A' C q)
    (hBA : B + 2 = A') (hB : Even B) : GBBound A C q := by
  unfold GBBound at *
  exact LeanLab.GvLtR1989.join h1 h2 hBA hB

/-! ### Certified lower bounds for log -/

/-- Taylor polynomial of exp with 12 terms plus the Mathlib remainder bound. -/
noncomputable def expUp (f : ℝ) : ℝ :=
  (∑ i ∈ range 12, f ^ i / (Nat.factorial i : ℝ)) + f ^ 12 * ((13 : ℝ) / ((Nat.factorial 12 : ℝ) * 12))

theorem exp_le_expUp {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) : Real.exp f ≤ expUp f := by
  have hb := Real.exp_bound (x := f) (by rw [abs_of_nonneg h0]; exact h1) (n := 12) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have := (abs_le.mp hb).2
  unfold expUp
  push_cast at this ⊢
  linarith

/-- `a + f ≤ log x` from `e^a · expUp f ≤ x`, with `e < 2.7182818286`. -/
theorem le_log_of {x : ℝ} (a : ℕ) {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : (2.7182818286 : ℝ) ^ a * expUp f ≤ x) : (a : ℝ) + f ≤ Real.log x := by
  have hpos : 0 < Real.exp ((a : ℝ) + f) := Real.exp_pos _
  have hea : Real.exp (a : ℝ) ≤ (2.7182818286 : ℝ) ^ a := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le a
  have hle : Real.exp ((a : ℝ) + f) ≤ x := by
    rw [Real.exp_add]
    calc Real.exp a * Real.exp f ≤ (2.7182818286 : ℝ) ^ a * expUp f :=
          mul_le_mul hea (exp_le_expUp h0 h1) (Real.exp_pos _).le (by positivity)
      _ ≤ x := h
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le hpos hle)]
  exact hle

/-- The claim at `n` with constant `c`: `minGB n` and `n - minGB n` are prime, and
`minGB n < c · log² n · log log n`. -/
def GoodRatio (c : ℝ) (n : ℕ) : Prop :=
  (minGB n).Prime ∧ (n - minGB n).Prime ∧
    (minGB n : ℝ) < c * Real.log n ^ 2 * Real.log (Real.log n)

/-- The ratio bound on one block. -/
theorem goodRatio_of_bound {A B q : ℕ} {c r s : ℝ} (hc : 0 ≤ c) (hr0 : 1 < r)
    (hr : r ≤ Real.log A) (hs : s ≤ Real.log r) (hs0 : 0 < s) (hq : (q : ℝ) < c * r ^ 2 * s)
    (hb : GBBound A B q) : ∀ n : ℕ, Even n → A ≤ n → n ≤ B → GoodRatio c n := by
  intro n hn hA hB
  obtain ⟨p, hp, hnp, hpq⟩ := hb n hn hA hB
  obtain ⟨hm1, hm2, hm3⟩ := minGB_spec hp hnp
  refine ⟨hm1, hm2, ?_⟩
  have hA0 : (0 : ℝ) < A := by
    by_contra h
    push_neg at h
    have : Real.log (A : ℝ) ≤ 0 := by
      rw [show (A : ℝ) = 0 by exact le_antisymm h (Nat.cast_nonneg A)]; simp
    linarith
  have hlogn : r ≤ Real.log n :=
    le_trans hr (Real.log_le_log hA0 (by exact_mod_cast hA))
  have hll : s ≤ Real.log (Real.log n) :=
    le_trans hs (Real.log_le_log (by linarith) hlogn)
  have hq' : ((minGB n : ℕ) : ℝ) ≤ q := by exact_mod_cast le_trans hm3 hpq
  have : c * r ^ 2 * s ≤ c * Real.log n ^ 2 * Real.log (Real.log n) := by
    apply mul_le_mul _ hll hs0.le (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlogn 2) hc
  linarith

end LeanLab.GvLtR1989
