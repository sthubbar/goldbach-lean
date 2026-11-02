module

public import Mathlib

/-!
# Saouter 1998, Lemma 1, the statement

The statement of Lemma 1 on page 864. The paper's phrase "the entire factorization of `F` is known"
concerns how the certificate is built and is no restriction on the natural number `F`.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.BLS

/-- Lemma 1 on page 864 of Saouter's paper, his form of Theorem 5 of Brillhart, Lehmer and Selfridge
1975, Math. Comp. 29: `N = R F + 1` odd, `F` even, `gcd(R, F) = 1`, an integer `a` with
`a^(N-1) ≡ 1 mod N` and `gcd(a^((N-1)/p) - 1, N) = 1` for every prime `p ∣ F`, and `N < 2 F^3`.
Then with `R = 2 F s + r` and `0 ≤ r < 2 F`, the number `N` is prime iff `s = 0` or `r^2 - 8 s` is
not a square. Proved as `GoldbachLean.Saouter1998.BLS.lemma1`. -/
def Lemma1 : Prop :=
  ∀ F R : ℕ, ∀ a : ℤ,
    Odd (R * F + 1) → Even F → Nat.Coprime R F →
    (a : ZMod (R * F + 1)) ^ (R * F) = 1 →
    (∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ (R * F / p) - 1) (R * F + 1) = 1) →
    R * F + 1 < 2 * F ^ 3 →
    ((R * F + 1).Prime ↔
      R / (2 * F) = 0 ∨
        ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)))

end GoldbachLean.Saouter1998.BLS
