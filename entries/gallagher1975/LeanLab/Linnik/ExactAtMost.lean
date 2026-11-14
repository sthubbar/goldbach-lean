module

public import Mathlib
public import LeanLab.Linnik.Statements

/-!
Linnik's problem, two primes plus K powers of 2: "exactly K" against "at most K" for all large
even N. Proved here, no placeholder proof:
* `exact_succ`: exactly K for all large even N gives exactly K + 1, by N − 2.
* `pow_split`: 2^L is a sum of exactly r powers of 2, each exponent ≥ 1, for 1 ≤ r ≤ 2^(L−1).
* `exact_succ_of_atMost`: at most K for all large even N gives exactly K + 1, by N − 2^(K+2)
  and splitting 2^(K+2) into the missing number of pieces.
So the two forms differ by at most one power of 2. Elementary and KNOWN in spirit; new to us as
a machine-checked statement. AI-written Lean code, Claude, run 20261017T0903Z-2557.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik

open Finset

/-- Concatenating two families of powers. -/
theorem exact_append {a b N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ν₁ : Fin a → ℕ)
    (ν₂ : Fin b → ℕ) (h₁ : ∀ i, 1 ≤ ν₁ i) (h₂ : ∀ i, 1 ≤ ν₂ i)
    (hN : N = p + q + (∑ i, 2 ^ ν₁ i) + ∑ i, 2 ^ ν₂ i) : LinnikExact (a + b) N := by
  refine ⟨p, q, hp, hq, Fin.append ν₁ ν₂, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h₁ j
    · rw [Fin.append_right]; exact h₂ j
  · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]; rw [hN]; ring

theorem exact_cast {a b N : ℕ} (h : a = b) (hN : LinnikExact a N) : LinnikExact b N := h ▸ hN

/-- Exactly `K` for all large even `N` gives exactly `K + 1`. -/
theorem exact_succ {K : ℕ} (h : AllLargeEven (LinnikExact K)) :
    AllLargeEven (LinnikExact (K + 1)) := by
  obtain ⟨N0, hN0⟩ := h
  refine ⟨N0 + 2, fun N hev hN => ?_⟩
  obtain ⟨p, q, hp, hq, ν, hν, hM⟩ := hN0 (N - 2) (by
    obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by omega⟩) (by omega)
  have := exact_append hp hq ν (fun _ : Fin 1 => 1) hν (fun _ => le_rfl)
    (N := N) (by simp; omega)
  exact this

theorem exact_mono {K K' : ℕ} (hK : K ≤ K') (h : AllLargeEven (LinnikExact K)) :
    AllLargeEven (LinnikExact K') := by
  induction K', hK using Nat.le_induction with
  | base => exact h
  | succ K' _ ih => exact exact_succ ih

/-- `2^L` as a sum of exactly `r` powers of 2 with exponents at least 1, `1 ≤ r ≤ 2^(L−1)`. -/
theorem pow_split : ∀ L : ℕ, 1 ≤ L → ∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ (L - 1) →
    ∃ ν : Fin r → ℕ, (∀ i, 1 ≤ ν i) ∧ ∑ i, 2 ^ ν i = 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    intro r hr1 hr2
    have : r = 1 := by simp at hr2; omega
    subst this
    exact ⟨fun _ => 1, fun _ => le_rfl, by simp⟩
  | succ L hL ih =>
    intro r hr1 hr2
    rcases Nat.lt_or_ge r 2 with hr | hr
    · have : r = 1 := by omega
      subst this
      exact ⟨fun _ => L + 1, fun _ => Nat.le_add_left 1 L, by simp⟩
    · have hpow : 2 ^ (L + 1 - 1) = 2 * 2 ^ (L - 1) := by
        rw [show L + 1 - 1 = (L - 1) + 1 by omega, pow_succ]; ring
      rw [hpow] at hr2
      obtain ⟨ν₁, h₁, s₁⟩ := ih (r / 2) (by omega) (by omega)
      obtain ⟨ν₂, h₂, s₂⟩ := ih (r - r / 2) (by omega) (by omega)
      have hr' : r / 2 + (r - r / 2) = r := by omega
      have key : ∃ ν : Fin (r / 2 + (r - r / 2)) → ℕ, (∀ i, 1 ≤ ν i) ∧
          ∑ i, 2 ^ ν i = 2 ^ (L + 1) := by
        refine ⟨Fin.append ν₁ ν₂, ?_, ?_⟩
        · intro i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · rw [Fin.append_left]; exact h₁ j
          · rw [Fin.append_right]; exact h₂ j
        · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]
          rw [s₁, s₂, pow_succ]; ring
      rw [hr'] at key
      exact key

/-- **At most `K` for all large even `N` gives exactly `K + 1`.** -/
theorem exact_succ_of_atMost {K : ℕ} (h : AllLargeEven (LinnikAtMost K)) :
    AllLargeEven (LinnikExact (K + 1)) := by
  obtain ⟨N0, hN0⟩ := h
  set L := K + 2
  refine ⟨N0 + 2 ^ L, fun N hev hN => ?_⟩
  have hLe : Even (2 ^ L) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  obtain ⟨k, hk, p, q, hp, hq, ν, hν, hM⟩ := hN0 (N - 2 ^ L)
    ((Nat.even_sub (show 2 ^ L ≤ N by omega)).mpr (iff_of_true hev hLe))
    (by omega)
  have hbig : K + 1 - k ≤ 2 ^ (L - 1) := by
    have : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
    simp only [L, show K + 2 - 1 = K + 1 by omega]; omega
  obtain ⟨μ, hμ, hs⟩ := pow_split L (by omega) (K + 1 - k) (by omega) hbig
  have := exact_append hp hq ν μ hν hμ (N := N) (by rw [hs]; omega)
  exact exact_cast (by omega) this

/-- Hence the "at most" and "exactly" thresholds differ by at most one. -/
theorem exact_iff_atMost_up_to_one (K : ℕ) :
    (AllLargeEven (LinnikExact K) → AllLargeEven (LinnikAtMost K)) ∧
    (AllLargeEven (LinnikAtMost K) → AllLargeEven (LinnikExact (K + 1))) :=
  ⟨fun h => allLargeEven_mono (fun _ => atMost_of_exact) h, exact_succ_of_atMost⟩

end LeanLab.Linnik
