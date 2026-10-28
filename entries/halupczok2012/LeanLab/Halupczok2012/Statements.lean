module

public import Mathlib

/-!
# Halupczok 2012: basic objects and the statement of Theorem 1.2

K. Halupczok, *Goldbach's problem with primes in arithmetic progressions and in short intervals*,
J. Théor. Nombres Bordeaux 25, 2013, no. 2, 331 to 351, arXiv 1212.4406. This file defines the
sums, the singular series `S` and `T` and the statement `Theorem2` of the paper's Theorem 1.2,
called Theorem 2 in the arXiv version, in its coprime reading. AI wrote the Lean code, Claude,
Anthropic; it was checked by the Lean kernel. Binary Goldbach is open; ternary Goldbach is a
theorem, Helfgott 2013.

Conventions, following the paper's notation section.
* `[X, X+Y]` is the set of integers `m` with `X < m ≤ X + Y`.
* `L = log Y`.
* Every `≪`, `≫`, `≍` in a hypothesis is encoded by a universally quantified constant `c > 0`;
  every `≪` in a conclusion by an existential constant `C`, and "sufficiently large" by an
  existential threshold `Y0`. These may depend on `A`, the `ε`'s, the hypothesis constants and
  the fixed residue `a`. `B = B(A)` is existential after `A`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.Halupczok2012

/-! ### Basic objects -/

/-- The integers `k` in the paper's interval `[X, X+R]`, that is `X < k ≤ X + R`. -/
noncomputable def kRange (X R : ℝ) : Finset ℕ :=
  (Icc 0 ⌈X + R⌉₊).filter (fun k => X < k ∧ (k : ℝ) ≤ X + R)

/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`, with the extra condition `p2 ≡ a2 (q2)`. -/
noncomputable def binSumAP (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧
      (p : ℤ) ≡ a2 [ZMOD q2]),
    Real.log p * Real.log ((m - p : ℕ) : ℝ)

/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`. -/
noncomputable def binSum (X2 Y : ℝ) (m : ℕ) : ℝ := binSumAP X2 Y 1 0 m

/-- The twin prime type constant `∏_{p ≠ 2} (1 - 1/(p-1)^2)`, as a `tprod` over all primes.
The product converges absolutely, so `tprod` is its value. -/
noncomputable def twinC : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The binary singular series `S(r)` of the paper, display 2. -/
noncomputable def S (r : ℕ) : ℝ :=
  if Even r then 2 * twinC * ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- The ternary singular series `T(n,q,a)` with one prime in an arithmetic progression,
as displayed after Theorem 2, written as a `tprod` over all primes of the local factor. -/
noncomputable def T (n q : ℕ) (a : ℤ) : ℝ :=
  (1 / (Nat.totient q : ℝ)) * ∏' p : Nat.Primes,
    (if ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q) ∨ (¬ ((p : ℕ) : ℤ) ∣ (n - a) ∧ (p : ℕ) ∣ q) then
        1 - 1 / ((p : ℝ) - 1) ^ 2
      else if ¬ (p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q then 1 + 1 / ((p : ℝ) - 1) ^ 3
      else (p : ℝ) / ((p : ℝ) - 1))

/-- `∑_{p1+p2+p3 = n, p_i ∈ [X_i, X_i+Y_i], p1 ≡ a (q)} log p1 log p2 log p3`. -/
noncomputable def ternSum (n : ℕ) (X1 Y1 X2 Y2 : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ x ∈ ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun x =>
      x.1.Prime ∧ x.2.Prime ∧ x.1 + x.2 ≤ n ∧ (n - x.1 - x.2).Prime ∧
      X1 < x.1 ∧ (x.1 : ℝ) ≤ X1 + Y1 ∧ X2 < x.2 ∧ (x.2 : ℝ) ≤ X2 + Y2 ∧ (x.1 : ℤ) ≡ a [ZMOD q]),
    Real.log x.1 * Real.log x.2 * Real.log ((n - x.1 - x.2 : ℕ) : ℝ)

/-! ### Theorem 2, ternary, one prime in an AP, two primes in short intervals -/

/-- The common hypotheses of Theorem 2, with hypothesis constants `c`, `B`, and `L = log Y2`. -/
def Thm2Hyp (ε ε1 ε2 B : ℝ) (c : Fin 7 → ℝ) (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ) : Prop :=
  Odd n ∧ Y1 ≤ X1 ∧ c 0 * X1 ^ (3 / 5 + ε1) ≤ Y1 ∧ Y2 ≤ X2 ∧ c 1 * X2 ^ (7 / 12 + ε2) ≤ Y2 ∧
  c 2 * Y2 ^ (1 / 3 + ε) ≤ Y1 ∧ Y1 ≤ c 3 * Y2 ∧
  0 ≤ (n : ℝ) - X1 - Y1 - X2 - Y2 ∧ c 4 * Y2 ≤ (n : ℝ) - X1 - Y1 - X2 - Y2 ∧
  (n : ℝ) - X1 - Y1 - X2 - Y2 ≤ c 5 * Y2 ∧
  1 ≤ Q ∧ Q ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-B)

/-- Theorem 2: under `Thm2Hyp`, `Q ≪ Y1^{3/2} (n - X1)^{-1/2}` and a fixed integer
`a ≤ n - X1 - Y1`,
`∑_{q ≤ Q} |∑_{p1+p2+p3=n, p_i ∈ [X_i,X_i+Y_i], p1 ≡ a (q)} log p1 log p2 log p3
  - T(n,q,a) Y1 Y2| ≪ Y1 Y2 L^{-A}`.
READING: the sum over `q` is restricted to `(a, q) = 1`. For `(a, q) > 1` the paper's `T(n,q,a)`
is in general nonzero while the prime sum is empty for `q < X1`, see `prime_cong_noncoprime`;
the proof says it assumes `(q, a) = 1` without loss of generality. -/
def Theorem2 : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ, ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2| ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A)

/-- Support for the reading of Theorem 2: if a prime `d` divides both `q` and `a`, then a prime
`p1 ≡ a (q)` equals `d`. So for `(a, q) > 1` and `q < X1` the prime sum in Theorem 2 is empty. -/
theorem prime_cong_noncoprime {p1 q d : ℕ} {a : ℤ} (hp : p1.Prime) (hd : d.Prime)
    (hc : (p1 : ℤ) ≡ a [ZMOD q]) (hdq : d ∣ q) (hda : (d : ℤ) ∣ a) : p1 = d := by
  have h1 : (q : ℤ) ∣ a - p1 := (Int.ModEq.dvd hc)
  have h2 : (d : ℤ) ∣ a - p1 := (Int.natCast_dvd_natCast.mpr hdq).trans h1
  have h3 : (d : ℤ) ∣ (p1 : ℤ) := by
    have := dvd_sub hda h2
    simpa using this
  exact ((Nat.prime_dvd_prime_iff_eq hd hp).mp (Int.natCast_dvd_natCast.mp h3)).symm

end LeanLab.Halupczok2012
