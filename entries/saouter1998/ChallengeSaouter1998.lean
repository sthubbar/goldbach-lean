module

public import Mathlib

/-!
# Checking the odd Goldbach conjecture up to 10^20

Y. Saouter, *Checking the odd Goldbach conjecture up to 10^20*, Math. Comp. 67, 1998, 863 to 866.
The statements below are compared with the solution.

From the paper, proved here:

* Lemma 1, `BLS.lemma1`, the paper's form of Theorem 5 of Brillhart, Lehmer and Selfridge 1975, for
  every even `F`, with no cited input.
* Theorem 1, `Thm1.theorem1` for a natural base and `Thm1.theorem1_int` for an integer base.
* Lemma 2, `Paper.lemma2`, by quadratic reciprocity.
* Theorem 2, `Thm2.theorem2`, base 5, in both directions.
* The first 100 rungs of the paper's Table 1, `Table1Thm2.table1_prime_thm2`, and the first and
  last primes printed in the paper, `Thm2.first_prime` and `Thm2.last_prime`.

A misprint repaired: page 865 prints `N = 5 * 2^23 * k + 1258213`, where `12582913` is meant. The
statements `Paper.printed_three_ne`, `Paper.printed_not_form`, `Paper.printed_gap` and
`Table1.printed_three_composite` show the printed formula fails, while `Paper.N_form`, `Paper.N_three`
and `Paper.last_prime_form` show the corrected one fits the paper.

Derived result of this entry, not the paper's computation:
`ProthLadder.ternaryGoldbachUpTo_1e20_of_even`, every odd number from 7 to `10^20` is a sum of three
primes, with `EvenGoldbachUpTo (4 * 10^18)` as an explicit hypothesis, never an axiom. That
hypothesis is the published computation of Oliveira e Silva, Herzog and Pardi, Math. Comp. 83,
2014; it is not proved here. The proof is Saouter's prime ladder with 25 Proth rungs as in Helfgott
and Platt. Saouter's own ladder of about `250 * 10^6` rungs on the even range `4 * 10^11` is not
reverified beyond Table 1. `ProthLadder.ternaryGoldbachUpTo_293_vacuity` runs the same ladder lemma
at a small bound with nothing assumed.

Ternary Goldbach is Helfgott's theorem, from his 2013 preprint. Binary Goldbach is open and is not
claimed. AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof.
-/

@[expose] public section

namespace GoldbachLean

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

end GoldbachLean

namespace GoldbachLean.Saouter1998.Paper

/-- The ladder primes as the paper intends them, `N k = 5 * 2^23 * k + 12582913`. -/
def N (k : ℕ) : ℕ := 5 * 2 ^ 23 * k + 12582913

/-- The formula as printed on page 865, `N = 5 * 2^23 * k + 1258213`, with one digit 9 missing. -/
def Nprinted (k : ℕ) : ℕ := 5 * 2 ^ 23 * k + 1258213

/-- The corrected formula has the shape of Theorem 2, `2^22 * R + 1` with `R = 10 k + 3`. -/
theorem N_form (k : ℕ) : N k = 2 ^ 22 * (10 * k + 3) + 1 := sorry

/-- Table 1 starts at `k = 3`, which gives the paper's first prime `138412033 = 33 * 2^22 + 1`. -/
theorem N_three : N 3 = 138412033 ∧ 138412033 = 33 * 2 ^ 22 + 1 := sorry

/-- The printed formula misses the first prime of the paper. -/
theorem printed_three_ne : Nprinted 3 = 127087333 ∧ Nprinted 3 ≠ 138412033 := sorry

/-- The printed formula never has the shape `2^22 * R + 1` that Theorem 2 needs. -/
theorem printed_not_form (k : ℕ) : Nprinted k % 2 ^ 22 ≠ 1 := sorry

/-- The printed and intended formulas differ by a constant, for every `k`. -/
theorem printed_gap (k : ℕ) : N k = Nprinted k + 11324700 := sorry

/-- The last prime of the sequence, page 865, is the corrected formula at `k = 2384185796007`, so
it has the shape of Theorem 2, and it passes `10^20` while staying below `2 * (2^22)^3`. -/
theorem last_prime_form :
    N 2384185796007 = 100000000209366024193 ∧
      100000000209366024193 = 2 ^ 22 * 23841857960073 + 1 ∧ 23841857960073 % 2 = 1 ∧
      10 ^ 20 < 100000000209366024193 ∧ 100000000209366024193 < 2 * (2 ^ 22) ^ 3 := sorry

/-- Lemma 2, page 864: for a prime `p ≡ 3 mod 10`, `5^((p-1)/2) ≡ -1 mod p`. -/
theorem lemma2 (p : ℕ) [hp : Fact p.Prime] (h : p % 10 = 3) :
    (5 : ZMod p) ^ ((p - 1) / 2) = -1 := sorry

/-- Theorem 2, page 864, the Brillhart, Lehmer and Selfridge criterion specialised to `F = 2^22` and
base 5: for `N = 2^22 R + 1 < 10^20`, `N ≡ 3 mod 10`, `R` odd and `5^((N-1)/2) ≡ -1 mod N`, with
`R = 2 F s + r` and `0 ≤ r < 2 F`, the number `N` is prime iff `s = 0` or `r^2 - 8 s` is not a
square. Proved as `GoldbachLean.Saouter1998.Thm2.theorem2`. -/
def Theorem2 : Prop :=
  ∀ R : ℕ, R % 2 = 1 → 2 ^ 22 * R + 1 < 10 ^ 20 → (2 ^ 22 * R + 1) % 10 = 3 →
    (5 : ZMod (2 ^ 22 * R + 1)) ^ ((2 ^ 22 * R) / 2) = -1 →
      ((2 ^ 22 * R + 1).Prime ↔
        (R / (2 * 2 ^ 22) = 0 ∨
          ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))))

end GoldbachLean.Saouter1998.Paper

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

/-- Lemma 1 of the paper, proved. -/
theorem lemma1 : Lemma1 := sorry

end GoldbachLean.Saouter1998.BLS

namespace GoldbachLean.Saouter1998.Thm2

/-- Theorem 2 of the paper, as stated in `Paper.Theorem2`. -/
theorem theorem2 : GoldbachLean.Saouter1998.Paper.Theorem2 := sorry

/-- Page 865: the last prime of Saouter's ladder, `100000000209366024193`, above `10^20`, is prime. -/
theorem last_prime : (100000000209366024193 : ℕ).Prime := sorry

/-- The first rung, `138412033`, is prime. -/
theorem first_prime : (138412033 : ℕ).Prime := sorry

end GoldbachLean.Saouter1998.Thm2

namespace GoldbachLean.Saouter1998.Thm1

/-- Theorem 1 on page 864, with a natural number as the base `a`. -/
theorem theorem1 (R a : ℕ) (hR : R % 2 = 1) (hlt : 2 ^ 22 * R + 1 < 10 ^ 20)
    (ha : (a : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1) :
    (2 ^ 22 * R + 1).Prime ↔
      (R / (2 * 2 ^ 22) = 0 ∨
        ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))) := sorry

/-- Theorem 1 for an integer base, as in the paper. -/
theorem theorem1_int (R : ℕ) (a : ℤ) (hR : R % 2 = 1)
    (hlt : 2 ^ 22 * R + 1 < 10 ^ 20)
    (ha : (a : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1) :
    (2 ^ 22 * R + 1).Prime ↔
      (R / (2 * 2 ^ 22) = 0 ∨
        ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))) := sorry

end GoldbachLean.Saouter1998.Thm1

namespace GoldbachLean.Saouter1998.Table1

open GoldbachLean.Saouter1998 GoldbachLean.Saouter1998.Paper

/-- The 100 values of `k` in Table 1, page 865, as printed. -/
def T1 : List Nat :=
  [3, 9537, 19059, 28575, 38107, 47622, 57147, 66651, 76182, 85713, 95230, 104764, 114297,
   123819, 133347, 142879, 152415, 161950, 171471, 181003, 190501, 200022, 209541, 219066,
   228594, 238104, 247624, 257157, 266683, 276219, 285727, 295258, 304785, 314305, 323839,
   333355, 342882, 352405, 361941, 371467, 381000, 390522, 400048, 409575, 419098, 428604,
   438132, 447663, 457194, 466710, 476242, 485761, 495291, 504813, 514347, 523878, 533397,
   542932, 552466, 561991, 571519, 581038, 590565, 600090, 609625, 619159, 628675, 638196,
   647704, 657232, 666751, 676285, 685821, 695353, 704887, 714405, 723936, 733452, 742983,
   752485, 761989, 771520, 781054, 790588, 800116, 809623, 819151, 828679, 838198, 847726,
   857232, 866748, 876268, 885804, 895333, 904851, 914377, 923910, 933445, 942973]

/-- Table 1 starts at the paper's first prime `138412033`. -/
theorem table1_head : (T1.map N).head? = some 138412033 := sorry

/-- Every gap between Table 1 rungs is below Sinisalo's `4 * 10^11`, as the paper's method needs. -/
theorem table1_gaps :
    List.IsChain (fun a b => a < b ∧ b - a < 4 * 10 ^ 11) (T1.map N) := sorry

/-- The printed formula at `k = 3` is composite, `127087333 = 19 * 6688807`. -/
theorem printed_three_composite : ¬ (Nprinted 3).Prime := sorry

end GoldbachLean.Saouter1998.Table1

namespace GoldbachLean.Saouter1998.Table1Thm2

open GoldbachLean.Saouter1998.Paper GoldbachLean.Saouter1998.Thm2

/-- Every Table 1 rung is prime, by the paper's Theorem 2 test. -/
theorem table1_prime_thm2 : ∀ k ∈ GoldbachLean.Saouter1998.Table1.T1, (N k).Prime := sorry

end GoldbachLean.Saouter1998.Table1Thm2

namespace GoldbachLean.Saouter1998.ProthLadder

/-- Derived result of this entry, not the paper's computation: every odd number from 7 to `10^20`
is a sum of three primes, conditional on binary Goldbach up to `4e18`, the computation of Oliveira
e Silva, Herzog and Pardi, taken as the hypothesis `h`. -/
theorem ternaryGoldbachUpTo_1e20_of_even (h : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    TernaryGoldbachUpTo (10 ^ 20) := sorry

/-- Vacuity instance: the same ladder lemma at `B = 100`, with its even input checked by the
kernel, gives ternary Goldbach up to 293. -/
theorem ternaryGoldbachUpTo_293_vacuity : TernaryGoldbachUpTo 293 := sorry

end GoldbachLean.Saouter1998.ProthLadder
