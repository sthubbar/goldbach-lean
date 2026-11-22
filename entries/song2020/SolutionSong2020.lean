module

public import LeanLab.Song2020.Palomar1122Song

/-!
# Proof of the Song 2020 Theorem 1 entry

`LeanLab/Song2020/Palomar1122Song.lean` proves Theorem 1 of Yanbo Song, The ternary
Goldbach-Vinogradov theorem with almost equal Piatetski-Shapiro primes, arXiv 2012.06322 v1,
2020, Section 4, page 9, from the paper's Lemma 3, which is Theorem 3 of C. D. Pan and
C. B. Pan, Goldbach Conjecture, Science Press, Beijing, 1988, taken at the exponent 7/8 as the
explicit hypothesis `Lemma3 (7 / 8)`.

`songWindow_margin_of_lemma3` and `asymptotic_margin_of_lemma3` give Theorem 1 and the page 9
asymptotic formula for every window `y > n^{(52 - 45γ)/8 + δ}` with `δ > 0`, from that
one hypothesis; Lemmas 4 and 5 of the paper are proved. `songTheorem1_of_lemma3_logTransfer`
gives Theorem 1 at the exact window and also takes the transfer step of page 9 at the exact
threshold, `Flag1734.LogTransferDQ`, as a hypothesis. Binary Goldbach is open and is not
claimed. AI agents wrote the Lean code, see `PORTING.md`; it was checked by the Lean kernel.
-/
