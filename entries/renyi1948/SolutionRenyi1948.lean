module

public import LeanLab.PNTPort.BVMax.Renyi8Main
public import LeanLab.PNTPort.BVMax.TwinRenyi

/-!
# Proof of the Rényi 1948 entry

`LeanLab/PNTPort/BVMax/RenyiFixedK.lean` proves Rényi's theorem with `K = 13000` by a Brun type
block sieve on `{N - p : p < N}`: blocks of primes `p ∤ N` in `(2^{2^j}, 2^{2^{j+1}}]` with
Bonferroni levels rising block by block, `LeanLab/PNTSieve/`, the sieve remainders controlled by
the lab's Bombieri-Vinogradov theorem for `π(y; q, a)`, `LeanLab/PNTPort/BVMax/PrimesUncond.lean`,
and Mertens' estimates. `TwinRenyi.lean` runs the same sieve on `{p + 2}` to prove `twin_renyi_count`, a derived
analogue proved in this entry by the same sieve method, a twin-prime analogue of Rényi's theorem,
not a result of Rényi 1948. `RenyiAssembly`,
`RenyiPaired`, `RenyiWeighted`, `RenyiRealBase`, `RenyiSmallK` and `Renyi20`, `Renyi14`,
`Renyi10`, `Renyi9`, `Renyi8` sharpen the sieve step by step down to `K = 8`, and `Renyi8Main.lean`
proves `renyi8_fixedK`. The Bombieri-Vinogradov theorem rests on the large sieve, Vaughan's
identity and the Siegel-Walfisz theorem, and on analytic number theory of ζ(s) ported from
PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. The compared theorems other than the last
are proved in those files; the last restates `renyi8_fixedK` with Mathlib's
`Nat.IsAtMostAlmostPrime`, whose condition `m ≠ 0` matches the lab's `0 < m`. AI wrote the
lab's Lean code and did the port, Claude, Anthropic; it was checked by the Lean kernel.
Binary Goldbach is open; nothing here claims it.
-/

@[expose] public section

namespace LeanLab.PNTPort.BVMax

/-- Rényi's theorem with `K = 8`, stated with Mathlib's `Nat.IsAtMostAlmostPrime`. -/
theorem renyi8_isAtMostAlmostPrime : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ Nat.IsAtMostAlmostPrime 8 m ∧ N = p + m := by
  obtain ⟨N₀, h⟩ := renyi8_fixedK
  exact ⟨N₀, fun N hN hE => by
    obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hE
    exact ⟨p, m, hp, ⟨Nat.pos_iff_ne_zero.mp hm, hΩ⟩, hNpm⟩⟩

end LeanLab.PNTPort.BVMax
