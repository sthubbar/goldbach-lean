module

public import Mathlib
public import LeanLab.Linnik.Gallagher1975Thm2Full

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142: the counting identity
of p.140, `r''_k(N) = Σ_{m+n=N} r'_i(m) r'_j(n)` for `k = i + j`, and Theorem 2, display (4),
p.125, for g = 2, from the page images of papers/P0094.pdf, PDF pages 2 and 17.
Unit U-6834, CLOUD 20261021T0217Z-cloud56. AI-written Lean code, Claude, 2026-10-21.
Checked only by the Lean kernel. Binary Goldbach is OPEN.

* `rpp k N`: Gallagher's `r''_k(N)`, p.125: the representations
  `N = p₁ + p₂ + 2^{ν1} + ... + 2^{νk}`, `p₁`, `p₂` prime, `1 ≤ νi ≤ L = [log₂ N]`, the range of
  `G` on p.132, counted as ordered triples `(p₁, p₂, ν)`.
* `rpp_add_eq`: PROVED, `r''_{i+j}(N) = Σ_{m ≤ N} r'_i(m) r'_j(N - m)`, by splitting the
  exponent tuple with `Fin.append`.
* `theorem2`: PROVED, CONDITIONAL ON `Theorem1` and `Lemma14`: an absolute `K` with
  `|r''_k(N) - 2 N L^k / log² N| ≤ K (log² k / k) · 2 N L^k / log² N` for `k ≥ 2`, even
  `N ≥ N_k`, which is display (4).
-/

@[expose] public section

open Finset Real

noncomputable section
namespace LeanLab.Linnik.Gallagher1975Thm2

open LeanLab.Linnik.Gallagher1975
open LeanLab.LPZ2007 (tuples pow2sum)

/-- Gallagher's `r''_k(N)`, p.125, `g = 2`, `L = [log₂ N]`. -/
def rpp (k N : ℕ) : ℕ :=
  #{x ∈ (range (N + 1) ×ˢ range (N + 1)) ×ˢ tuples k (Nat.log 2 N) |
    x.1.1.Prime ∧ x.1.2.Prime ∧ N = x.1.1 + x.1.2 + pow2sum x.2}

/-- The finset counted by `r'_i(m)`. -/
def rkSet (i N m : ℕ) : Finset (ℕ × (Fin i → ℕ)) :=
  {x ∈ range (m + 1) ×ˢ tuples i (Nat.log 2 N) | x.1.Prime ∧ m = x.1 + pow2sum x.2}

theorem rk_eq_card (i N m : ℕ) : rk i N m = #(rkSet i N m) := rfl

theorem pow2sum_append {i j : ℕ} (u : Fin i → ℕ) (v : Fin j → ℕ) :
    pow2sum (Fin.append u v) = pow2sum u + pow2sum v := by
  unfold pow2sum
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem mem_tuples_append {i j L : ℕ} {u : Fin i → ℕ} {v : Fin j → ℕ} :
    Fin.append u v ∈ tuples (i + j) L ↔ u ∈ tuples i L ∧ v ∈ tuples j L := by
  simp only [tuples, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨fun a => ?_, fun b => ?_⟩
    · simpa [Fin.append_left] using h (Fin.castAdd j a)
    · simpa [Fin.append_right] using h (Fin.natAdd i b)
  · rintro ⟨hu, hv⟩ a
    refine Fin.addCases (fun a => ?_) (fun b => ?_) a
    · simpa [Fin.append_left] using hu a
    · simpa [Fin.append_right] using hv b

/-- **The counting identity of p.140**, PROVED: `r''_{i+j}(N) = Σ_{m ≤ N} r'_i(m) r'_j(N - m)`. -/
theorem rpp_add_eq (i j N : ℕ) :
    rpp (i + j) N = ∑ m ∈ range (N + 1), rk i N m * rk j N (N - m) := by
  classical
  have hR : ∑ m ∈ range (N + 1), rk i N m * rk j N (N - m) =
      #((range (N + 1)).sigma fun m => rkSet i N m ×ˢ rkSet j N (N - m)) := by
    rw [card_sigma]; simp [rk_eq_card, card_product]
  rw [hR, rpp]
  symm
  apply card_nbij'
    (fun x => ((x.2.1.1, x.2.2.1), Fin.append x.2.1.2 x.2.2.2))
    (fun y => ⟨y.1.1 + pow2sum (fun a => y.2 (Fin.castAdd j a)),
      ((y.1.1, fun a => y.2 (Fin.castAdd j a)), (y.1.2, fun b => y.2 (Fin.natAdd i b)))⟩)
  · rintro ⟨m, ⟨p1, u⟩, ⟨p2, v⟩⟩ hx
    simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, rkSet, coe_product,
      coe_filter, Set.mem_prod, mem_product, mem_range, Set.mem_ofPred_eq] at hx
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq, mem_tuples_append,
      pow2sum_append]
    obtain ⟨hm, ⟨⟨h1, hu⟩, hp1, he1⟩, ⟨⟨h2, hv⟩, hp2, he2⟩⟩ := hx
    exact ⟨⟨⟨by omega, by omega⟩, hu, hv⟩, hp1, hp2, by omega⟩
  · rintro ⟨⟨p1, p2⟩, ν⟩ hy
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hy
    obtain ⟨⟨⟨h1, h2⟩, hν⟩, hp1, hp2, he⟩ := hy
    rw [← Fin.append_castAdd_natAdd (f := ν), mem_tuples_append] at hν
    rw [← Fin.append_castAdd_natAdd (f := ν), pow2sum_append] at he
    simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, rkSet, coe_product,
      coe_filter, Set.mem_prod, mem_product, mem_range, Set.mem_ofPred_eq]
    exact ⟨by omega, ⟨⟨by omega, hν.1⟩, hp1, trivial⟩, ⟨⟨by omega, hν.2⟩, hp2, by omega⟩⟩
  · rintro ⟨m, ⟨p1, u⟩, ⟨p2, v⟩⟩ hx
    simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, rkSet, coe_product,
      coe_filter, Set.mem_prod, mem_product, mem_range, Set.mem_ofPred_eq] at hx
    have he1 := hx.2.1.2.2
    simp only [Fin.append_left, Fin.append_right]
    rw [← he1]
  · rintro ⟨⟨p1, p2⟩, ν⟩ _
    simp only [Fin.append_castAdd_natAdd]

/-- **Gallagher 1975, Theorem 2, display (4), p.125, g = 2**, PROVED, CONDITIONAL ON
`Theorem1` and `Lemma14`: for `k ≥ 2` and even `N ≥ N_k`,
`r''_k(N) = (2 N L^k / log² N)(1 + O(log² k / k))`, with an absolute `O`. -/
theorem theorem2 (h1 : Theorem1) (h14 : Lemma14) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(rpp k N : ℝ) - 2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) := by
  obtain ⟨K, hK⟩ := theorem2_conv h1 h14
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨Nk, hNk⟩ := hK k hk
  refine ⟨Nk, fun N hN hev => ?_⟩
  have h := hNk N hN hev
  have hid : (rpp k N : ℝ) = conv (k - k / 2) (k / 2) N := by
    have := rpp_add_eq (k - k / 2) (k / 2) N
    rw [show k - k / 2 + k / 2 = k by omega] at this
    rw [this, conv]; push_cast; rfl
  rw [hid]; exact h

/-- Vacuity: `8 = 3 + 3 + 2`, so `r''_1(8) > 0` with `L = 3`. -/
theorem rpp_one_eight_pos : 0 < rpp 1 8 := by
  unfold rpp
  apply card_pos.2
  refine ⟨((3, 3), fun _ => 1), ?_⟩
  simp only [mem_filter, mem_product, mem_range, tuples, Fintype.mem_piFinset, mem_Icc]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, fun _ => ⟨le_rfl, ?_⟩⟩, Nat.prime_three, Nat.prime_three, ?_⟩
  · have : Nat.log 2 8 = 3 := by decide
    omega
  · simp [pow2sum]

end LeanLab.Linnik.Gallagher1975Thm2

