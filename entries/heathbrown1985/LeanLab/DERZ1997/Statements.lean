module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Ternary Goldbach under GRH.
P0011 Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, 99-104,
  "A complete Vinogradov 3-primes theorem under the Riemann hypothesis".
  Statements copied from the LaTeX source on EMIS, 1997-01-015.tex.html.
P0097 Zinoviev 1997, J. Number Theory 65, "On Vinogradov's constant in Goldbach's ternary
  problem", as quoted in P0011.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
A `sorry` marks a cited analytic result or a computation the lab does not redo.
Ternary Goldbach is now an unconditional theorem, Helfgott 2013; this module records the
older conditional route.
-/

@[expose] public section

namespace LeanLab.DERZ1997

/-- GRH for Dirichlet L-functions, as P0011 states it: all non-trivial zeros of all
Dirichlet L-functions have real part 1/2. Zeros are taken in the open strip `0 < Re s < 1`;
for an imprimitive character the extra Euler factor zeros lie on `Re s = 0`, so they are
excluded, and `q = 1` gives the Riemann zeta function. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2




/-! ### The paper's assembly, proved with zero sorry -/

/-- P0011 main theorem from its three inputs: assuming GRH, every odd number greater than 5
is a sum of three primes. Small `n` use `3` plus `dtr`; middle `n` use the lemma, whose
prime is then odd, plus `dtr`; large `n` use Zinoviev. -/
theorem derz_main_of
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9)
    (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach := by
  intro hG n ho h7
  rcases Nat.lt_or_ge (10 ^ 20) n with hbig | hsmall
  · exact hZ hG n ho hbig
  rcases Nat.lt_or_ge n (10 ^ 13 + 4) with hlow | hmid
  · -- n = 3 + (n - 3)
    have hev : Even (n - 3) := Nat.Odd.sub_odd ho (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩
  · obtain ⟨p, hp, h4, hle⟩ := hL hG n (by omega) hsmall
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (1615 : ℕ) * 10 ^ 9 < n - 2 := by norm_num at hmid ⊢; omega
      omega
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    have hev : Even (n - p) := Nat.Odd.sub_odd ho hpodd
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - p) hev h4 (by norm_num at hle ⊢; omega)
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

/-! ### Links to the rest of the lab, zero sorry -/

/-- Any later even verification gives the paper's `10^13` range, for example
Oliveira e Silva, Herzog, Pardi 2014 to `4 · 10^18`, `LeanLab.Verifications.oesilva_even`. -/
theorem dtr_of {N : ℕ} (h : EvenGoldbachUpTo N) (hN : 10 ^ 13 ≤ N) :
    EvenGoldbachUpTo (10 ^ 13) := fun n he h4 hn => h n he h4 (hn.trans hN)

/-- Saouter's unconditional check to `10^20`, P0018, replaces the lemma and the even range:
Zinoviev plus Saouter already give the GRH theorem. -/
theorem derz_main_of_saouter
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hS : TernaryGoldbachUpTo (10 ^ 20)) : GRH → TernaryGoldbach := by
  intro hG n ho h7
  rcases Nat.lt_or_ge (10 ^ 20) n with hbig | hsmall
  · exact hZ hG n ho hbig
  · exact hS n ho h7 hsmall

/-- Helfgott's unconditional theorem makes the GRH hypothesis unnecessary. -/
theorem derz_main_of_helfgott (h : TernaryGoldbach) : GRH → TernaryGoldbach := fun _ => h

/-- GRH contains RH in the critical strip: the `q = 1` case is the Riemann zeta function. -/
theorem zeta_strip_of_GRH (hG : GRH) (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) : s.re = 1 / 2 := by
  have := hG 1 (1 : DirichletCharacter ℂ 1) s
  rw [DirichletCharacter.LFunction_modOne_eq] at this
  exact this hs h0 h1

end LeanLab.DERZ1997
