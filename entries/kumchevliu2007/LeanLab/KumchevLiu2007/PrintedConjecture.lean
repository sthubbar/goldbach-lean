module

public import Mathlib

/-!
# The printed conjecture of Kumchev and Liu on primes plus squares of primes

A. V. Kumchev and J. Y. Liu, Sums of primes and squares of primes in short intervals,
arXiv 0801.0130 v1, 2007, page 1: with `ℋ₂ = {n ∈ ℕ : n ≢ 1 (mod 3), 2 ∣ n}`, "it is
conjectured that every sufficiently large `n ∈ ℋ₂` can be represented as the sum of a prime and
the square of another prime".

As printed this is false. If `m² = p + q²` with `p, q` prime, then `p = (m - q)(m + q)`, so
`m - q = 1`, `q = m - 1` and `p = 2m - 1`. For `m = 30 t + 6` the number `m²` lies in `ℋ₂`, but
`m - 1 = 5 (6 t + 1)` is not prime. Squares must be excluded, as in Hardy and Littlewood's
Conjecture H.

The definitions `IsPrimePlusPrimeSq` and `InH2` are copied from the lab file
`LeanLab/KumchevLiu2007/Statements.lean`; the rest is copied from the lab file
`LeanLab/KumchevLiu2007/Novelty1612.lean`. See `PORTING.md`.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007

/-- `n = p₁ + p₂²` with `p₁, p₂` prime. The paper's conjecture says "another prime", but its
counting function `R₂` and the sets `E₂` do not require `p₁ ≠ p₂`; we follow `E₂`. -/
def IsPrimePlusPrimeSq (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q ^ 2

/-- The paper's `ℋ₂ = {n ∈ ℕ : n ≢ 1 (mod 3), 2 ∣ n}`. -/
def InH2 (n : ℕ) : Prop := n % 3 ≠ 1 ∧ 2 ∣ n

end LeanLab.KumchevLiu2007

namespace LeanLab.KumchevLiu2007.Novelty1612

/-- A square in the form forces the two factors of `p = (m - q)(m + q)`. No hypothesis. -/
theorem sq_form {m : ℕ} (h : IsPrimePlusPrimeSq (m ^ 2)) :
    (m - 1).Prime ∧ (2 * m - 1).Prime := by
  obtain ⟨p, q, hp, hq, e⟩ := h
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  have hqm : q < m := by
    by_contra hc
    have hc' : m ≤ q := not_lt.mp hc
    have : m ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hc' 2
    omega
  obtain ⟨d, rfl⟩ : ∃ d, m = q + d := ⟨m - q, by omega⟩
  have hd : 0 < d := by omega
  have hpd : p = d * (2 * q + d) := by
    have : (q + d) ^ 2 = d * (2 * q + d) + q ^ 2 := by ring
    omega
  have hd1 : d = 1 := by
    rcases (Nat.prime_mul_iff.mp (hpd ▸ hp)) with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · exact h
  subst hd1
  have h1 : q + 1 - 1 = q := by omega
  have h2 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  rw [h1, h2]
  refine ⟨hq, ?_⟩
  have : p = 2 * q + 1 := by omega
  exact this ▸ hp

/-- The conjecture as printed on p. 1 of the paper, with `p₁ = p₂` allowed. -/
def conjecture_printed : Prop := ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → InH2 n → IsPrimePlusPrimeSq n

/-- The family: `m = 30 t + 6` gives `m²` in H₂. -/
theorem inH2_family (t : ℕ) : InH2 ((30 * t + 6) ^ 2) := by
  constructor
  · have : (30 * t + 6) ^ 2 = 3 * (300 * t ^ 2 + 120 * t + 12) := by ring
    omega
  · exact ⟨2 * (15 * t + 3) ^ 2, by ring⟩

/-- For `t ≥ 1`, `(30 t + 6)²` is not a prime plus the square of a prime. -/
theorem not_form_family {t : ℕ} (ht : 1 ≤ t) : ¬ IsPrimePlusPrimeSq ((30 * t + 6) ^ 2) := by
  intro h
  have h1 := (sq_form h).1
  have e : 30 * t + 6 - 1 = 5 * (6 * t + 1) := by omega
  rw [e] at h1
  exact Nat.not_prime_mul (by norm_num) (by omega) h1

/-- **The printed conjecture is false.** No hypothesis. -/
theorem conjecture_printed_false : ¬ conjecture_printed := by
  rintro ⟨N₀, h⟩
  have hge : N₀ ≤ (30 * (N₀ + 1) + 6) ^ 2 := by nlinarith
  exact not_form_family (Nat.succ_pos N₀) (h _ hge (inH2_family _))

end LeanLab.KumchevLiu2007.Novelty1612
