module

public import Mathlib

/-!
P0055 D. I. Tolev, "The ternary Goldbach problem with primes from arithmetic progressions",
arXiv 0902.2669.
Statement of the main Theorem, a Bombieri-Vinogradov type average of the error
`Δ_{k,l}(N) = R_{k,l}(N) − M_{k,l}(N)` over `k₁, k₂ ≤ √N L^{-B}` and `k₃ ≤ N^{1/3} L^{-B}`,
with cheap links.
The singular series `𝔖_{k,l}(N)` is deferred by the paper to Halupczok; here it is a
parameter `S`, so the Theorem is stated for the paper's `S`, which this file does not define.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is proved; ternary Goldbach is a theorem, Helfgott 2013.
Every result below is proved. The repository copy omits the lab's opaque placeholder
series and its cited statement; the explicit series is `SeriesIdentification.halupczokSeries`.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009

/-- The weighted count `R_{k,l}(N) = Σ log p₁ log p₂ log p₃` over primes
`p₁ + p₂ + p₃ = N` with `pᵢ ≡ lᵢ (mod kᵢ)`. -/
noncomputable def R (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter
      (fun p => p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N ∧
        p.1 % k 0 = l 0 % k 0 ∧ p.2.1 % k 1 = l 1 % k 1 ∧ p.2.2 % k 2 = l 2 % k 2),
    Real.log p.1 * Real.log p.2.1 * Real.log p.2.2

/-- The type of a singular series `𝔖_{k,l}(N)`. -/
abbrev SSeries := (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ

/-- The main term `M_{k,l}(N) = N² 𝔖_{k,l}(N) / (2 φ(k₁) φ(k₂) φ(k₃))`, for a given
singular series `S`. -/
noncomputable def M (S : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * S k l N / (2 * (k 0).totient * (k 1).totient * (k 2).totient)

noncomputable def Δ (S : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  R k l N - M S k l N

/-- Admissible residues for a modulus. -/
def residues (k : ℕ) : Finset ℕ := (range k).filter (fun l => Nat.Coprime l k)

/-- The inner quantity of `𝓔*` for fixed `k₁, k₂`: the max over admissible `l₁, l₂` of
`|Σ_{k₃ ≤ K₃, (k₃, l₃) = 1} λ(k₃) Δ|`, written as a supremum over finite sets. -/
noncomputable def inner (S : SSeries) (lam : ℕ → ℝ) (l₃ K₃ k₁ k₂ N : ℕ) : ℝ :=
  ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
    |∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
        lam k₃ * Δ S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|

/-- `𝓔*`, with `K₁₂ = ⌊√N L^{-B}⌋` and `K₃ = ⌊N^{1/3} L^{-B}⌋`. -/
noncomputable def Estar (S : SSeries) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) : ℝ :=
  let L := Real.log N
  let K₁₂ := ⌊Real.sqrt N * L ^ (-B)⌋₊
  let K₃ := ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * L ^ (-B)⌋₊
  ∑ k₁ ∈ Icc 1 K₁₂, ∑ k₂ ∈ Icc 1 K₁₂, inner S lam l₃ K₃ k₁ k₂ N

/-- The Theorem, for a given singular series `S`: for every `A > 0` there is `B = B(A)` so
that, for each fixed `l₃ ≥ 1`, uniformly in `|λ(k)| ≤ 1`, `𝓔* ≪ N² L^{-A}` for odd `N`. -/
def TheTheorem (S : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
    (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
      Estar S lam l₃ B N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)

/-! ### Links -/

theorem R_nonneg (k l : Fin 3 → ℕ) (N : ℕ) : 0 ≤ R k l N := by
  unfold R
  refine sum_nonneg fun p _ => ?_
  have := Real.log_natCast_nonneg p.1; have := Real.log_natCast_nonneg p.2.1
  have := Real.log_natCast_nonneg p.2.2
  positivity

/-- `R > 0` gives a representation. -/
theorem rep_of_R_pos {k l : Fin 3 → ℕ} {N : ℕ} (h : 0 < R k l N) :
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N ∧
      p₁ % k 0 = l 0 % k 0 ∧ p₂ % k 1 = l 1 % k 1 ∧ p₃ % k 2 = l 2 % k 2 := by
  unfold R at h
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt h)
  rw [mem_filter] at hp
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  exact ⟨p.1, p.2.1, p.2.2, h1, h2, h3, h4, h5, h6, h7⟩

/-- A representation gives `R > 0`. -/
theorem R_pos_of_rep {k l : Fin 3 → ℕ} {N : ℕ} {p₁ p₂ p₃ : ℕ} (h1 : p₁.Prime) (h2 : p₂.Prime)
    (h3 : p₃.Prime) (hs : p₁ + p₂ + p₃ = N) (c1 : p₁ % k 0 = l 0 % k 0)
    (c2 : p₂ % k 1 = l 1 % k 1) (c3 : p₃ % k 2 = l 2 % k 2) : 0 < R k l N := by
  unfold R
  have hmem : ((p₁, p₂, p₃) : ℕ × ℕ × ℕ) ∈ (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter
      (fun p => p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N ∧
        p.1 % k 0 = l 0 % k 0 ∧ p.2.1 % k 1 = l 1 % k 1 ∧ p.2.2 % k 2 = l 2 % k 2) := by
    simp only [mem_filter, mem_product, mem_range]
    exact ⟨⟨by omega, by omega, by omega⟩, h1, h2, h3, hs, c1, c2, c3⟩
  have hpos : ∀ q : ℕ, q.Prime → 0 < Real.log q := fun q hq =>
    Real.log_pos (by exact_mod_cast hq.one_lt)
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun p : ℕ × ℕ × ℕ =>
    Real.log p.1 * Real.log p.2.1 * Real.log p.2.2) (fun p _ => ?_) hmem)
  · have := hpos _ h1; have := hpos _ h2; have := hpos _ h3; positivity
  · have := Real.log_natCast_nonneg p.1; have := Real.log_natCast_nonneg p.2.1
    have := Real.log_natCast_nonneg p.2.2; positivity

/-- The local condition for one common modulus: a representation forces
`N ≡ l₁ + l₂ + l₃ (mod k)`, so `R = 0` otherwise. -/
theorem local_condition {k : ℕ} {l : Fin 3 → ℕ} {N : ℕ} (h : 0 < R ![k, k, k] l N) :
    N % k = (l 0 + l 1 + l 2) % k := by
  obtain ⟨p₁, p₂, p₃, -, -, -, hs, c1, c2, c3⟩ := rep_of_R_pos h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at c1 c2 c3
  rw [← hs]
  exact Nat.ModEq.add (Nat.ModEq.add (c1 : p₁ ≡ l 0 [MOD k]) c2) c3

theorem R_eq_zero_of_not_local {k : ℕ} {l : Fin 3 → ℕ} {N : ℕ}
    (h : N % k ≠ (l 0 + l 1 + l 2) % k) : R ![k, k, k] l N = 0 :=
  le_antisymm (not_lt.mp fun hp => h (local_condition hp)) (R_nonneg _ _ _)

/-- With `λ` the indicator of one admissible `k₀ ≤ K₃`, the inner sum is the single error
`Δ` at `k₃ = k₀`: the Theorem contains the fixed `k₃` case. -/
theorem inner_sum_indicator (S : SSeries) (l₃ K₃ k₀ k₁ k₂ l₁ l₂ N : ℕ)
    (hk : k₀ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃)) :
    ∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
        (if k₃ = k₀ then (1 : ℝ) else 0) * Δ S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N
      = Δ S ![k₁, k₂, k₀] ![l₁, l₂, l₃] N := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq' _ k₀]; simp [hk]

/-- The indicator weight satisfies `|λ| ≤ 1`. -/
theorem indicator_bounded (k₀ : ℕ) : ∀ k, |(if k = k₀ then (1 : ℝ) else 0)| ≤ 1 := by
  intro k; split_ifs <;> simp

end LeanLab.Tolev2009
