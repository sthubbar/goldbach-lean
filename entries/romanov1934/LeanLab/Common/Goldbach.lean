module

public import Mathlib

/-!
Shared Goldbach definitions for the Lean Lab.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `n` is a sum of three primes. -/
def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- Binary Goldbach holds for every even `n` with `4 ≤ n ≤ N`. -/
def EvenGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ N → IsGoldbachSum n

/-- Ternary Goldbach holds for every odd `n` with `7 ≤ n ≤ N`. -/
def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Odd n → 7 ≤ n → n ≤ N → IsTernarySum n

/-- The binary Goldbach conjecture. OPEN. -/
def BinaryGoldbach : Prop := ∀ n, Even n → 4 ≤ n → IsGoldbachSum n

/-- The ternary Goldbach statement, proved by Helfgott 2013. -/
def TernaryGoldbach : Prop := ∀ n, Odd n → 7 ≤ n → IsTernarySum n

/-! ### A kernel-checkable primality test, proved sound -/

/-- `noDivFrom n fuel d` is `true` when no `m` with `d ≤ m` and `m * m ≤ n` divides `n`,
provided enough fuel. Structural recursion on fuel so `decide +kernel` can run it. -/
def noDivFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else noDivFrom n fuel (d + 1)

/-- Boolean primality by trial division up to the square root. -/
def primeB (n : ℕ) : Bool := 2 ≤ n && noDivFrom n n 2

theorem noDivFrom_sound (n : ℕ) : ∀ fuel d, noDivFrom n fuel d = true →
    ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDivFrom] at h
  | succ k ih =>
    intro d h m hdm hmm hdiv
    simp only [noDivFrom] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · exact h2 (Nat.mod_eq_zero_of_dvd hdiv)
        · exact ih (d + 1) h m hlt hmm hdiv

theorem primeB_sound {n : ℕ} (h : primeB n = true) : n.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hdiv => ?_⟩
  exact noDivFrom_sound n n 2 hnd m hm (Nat.le_sqrt.mp hms) hdiv

/-! ### A kernel-checkable binary Goldbach checker, proved sound -/

/-- Search `p = d, d+1, ...` for a prime `p` with `n - p` prime, while `p ≤ n`. -/
def gbFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, p => if n < p then false
      else if primeB p && primeB (n - p) then true else gbFrom n fuel (p + 1)

theorem gbFrom_sound (n : ℕ) : ∀ fuel p, gbFrom n fuel p = true → IsGoldbachSum n := by
  intro fuel
  induction fuel with
  | zero => intro p h; simp [gbFrom] at h
  | succ k ih =>
    intro p h
    simp only [gbFrom] at h
    by_cases h1 : n < p
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (primeB p && primeB (n - p)) = true
      · simp only [Bool.and_eq_true] at h2
        exact ⟨p, n - p, primeB_sound h2.1, primeB_sound h2.2, by omega⟩
      · rw [if_neg h2] at h; exact ih (p + 1) h

/-- Check every even `n` from `4` to `N`. -/
def allEvenGB : ℕ → Bool
  | 0 => true
  | n + 1 => (if (n + 1) % 2 = 0 && 4 ≤ n + 1 then gbFrom (n + 1) (n + 1) 2 else true) && allEvenGB n

theorem allEvenGB_sound : ∀ N, allEvenGB N = true → EvenGoldbachUpTo N := by
  intro N
  induction N with
  | zero => intro _ n _ h4 hn; omega
  | succ k ih =>
    intro h n hev h4 hn
    simp only [allEvenGB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact ih h2 n hev h4 (by omega)
    · have hn' : n = k + 1 := by omega
      subst hn'
      split_ifs at h1 with hc
      · exact gbFrom_sound _ _ _ h1
      · exfalso; apply hc
        simp only [decide_eq_true_eq]
        exact ⟨Nat.even_iff.mp hev, h4⟩

end LeanLab
