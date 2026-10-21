module

public import LeanLab.PNTPort.BVMax.Renyi8

/-!
# Rényi's theorem with `K = 8`, the unconditional statements

Unit U-6757, CLOUD 20261020T2317Z-cloud53. AI wrote the Lean code. Known mathematics, Rényi 1948
type with a small explicit `K`; Pan K = 4 and Chen 1973 K = 2 are far stronger, so nothing here is
new mathematics. Ineffective `N₀`, through Siegel-Walfisz inside the lab's Bombieri-Vinogradov
`bvPi`. Binary Goldbach is `Ω(m) = 1` and stays OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

open Filter in
/-- **Rényi's theorem with the count and `K = 8`, PROVED unconditional**: for every large even
`N`, `#{p < N prime : Ω(N - p) ≤ 8} ≥ e^{-36} N/(2 log² N)`. Ineffective. -/
theorem renyi8_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    Real.exp (-36) * N / (2 * Real.log N ^ 2) ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 8)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_rem_family 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B (100 * |K|)
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 2100)))
  refine ⟨max ⌈max (max X X₂) Y⌉₊ 2, fun N hN hE => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact renyi8_count N (hK N hN2) hE (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's theorem with `K = 8`, PROVED unconditional.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 8`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN; Chen 1973 has `Ω(m) ≤ 2`. -/
theorem renyi8_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 8 := by
  obtain ⟨N₀, hN₀⟩ := renyi8_fixedK_count
  refine ⟨max N₀ 4, fun N hN hE => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) hE
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < Real.exp (-36) * N / (2 * Real.log N ^ 2) := by positivity
  have hc : 0 < (((range N).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 8)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨p, hp⟩ := card_pos.mp hc
  simp only [mem_filter, mem_range] at hp
  obtain ⟨⟨hpN, hpp⟩, hΩ⟩ := hp
  exact ⟨p, N - p, hpp, by omega, by omega, hΩ⟩

end LeanLab.PNTPort.BVMax
