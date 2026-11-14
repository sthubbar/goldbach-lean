module

public import Mathlib
public import LeanLab.Linnik.U7204Theorem1
public import LeanLab.Linnik.U1434Lemma21

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142: display (4) of the
proof of Lemma 13, p.138, and the reduction of Lemma 13 to display (6), p.139, read from the page
images, PDF pages 4, 9, 15 and 16. Unit U-7204, CLOUD MANUAL-N2, 2026-10-21.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Notation of the paper: `S(α) = Σ_{p ≤ N} e(pα)`, p.127, and `G(α) = Σ_{ν=1}^{L} e(2^ν α)`,
p.132, `L = [log₂ N]`.

* `SG_eq`: PROVED, `S(α) G(α)^k = Σ_{n < R} c(n) e(nα)`, where `c(n)` counts `p ≤ N` prime and
  `1 ≤ νᵢ ≤ L` with `n = p + 2^{ν₁} + ... + 2^{ν_k}`.
* `rk_le_cf`: PROVED, `r'_k(n) ≤ c(n)` for `n ≤ N`, the paper's `S G^k = Σ_{n ≤ N} r'_k(n) e(nα) + Σ_{n > N}`.
* `display4`: PROVED, display (4): `Σ_{n ≤ N} r'_k(n)² ≤ ∫_0^1 |S(α) G^k(α)|² dα`.
* `Display6`: display (6), p.139, cited as a `Prop`, NOT proved here: the circle method bound
  `∫_0^1 |S G^k|² ≤ (D/φ(D)) (N L^{2k} / log² N)(1 + O(log² 2k / k))`, `D/φ(D) = 2`. The paper
  proves it for `k ≥ k₀` from (5), Lemmas 2, 11 and 12, and says that for `1 ≤ k < k₀` it
  follows easily from Lemma 12; the `Prop` states the combined claim for every `k ≥ 1`.
* `lemma13_of_display6`: PROVED, `Display6 → Lemma13`.
* `theorem1_of_display6`, `theorem2_of_display6`: Theorems 1 and 2, CONDITIONAL ON `Display6` alone.
-/

@[expose] public section

open Finset Real MeasureTheory

noncomputable section
namespace LeanLab.Linnik.U7204

open LeanLab.Linnik.Gallagher1975 LeanLab.Linnik.Gallagher1975Thm2 LeanLab.Linnik.U7201
open LeanLab.Linnik.U1412Display53 (eC)
open LeanLab.Linnik.LiLiuLemma43 (SA)
open LeanLab.Linnik.U1426ChainWire (Gs parseval)
open LeanLab.Linnik.U1434Lemma21 (sv Gs_pow e_eq_eC eC_add sv_le)
open LeanLab.LPZ2007 (tuples pow2sum)

/-- The primes `p ≤ N`. -/
def primesLe (N : ℕ) : Finset ℕ := {p ∈ range (N + 1) | p.Prime}

/-- Gallagher's `S(α) = Σ_{p ≤ N} e(pα)`, p.127. -/
def Sg (N : ℕ) (α : ℝ) : ℂ := SA (primesLe N) (fun _ => 1) α

/-- `c(n)`: the representations `n = p + 2^{ν₁} + ... + 2^{ν_k}`, `p ≤ N`, `1 ≤ νᵢ ≤ L`. -/
def cf (k N L n : ℕ) : ℝ :=
  ∑ p ∈ primesLe N, ∑ ν : Fin k → Fin L, if p + sv ν = n then (1 : ℝ) else 0

theorem cf_nonneg (k N L n : ℕ) : 0 ≤ cf k N L n :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- `S(α) G(α)^k = Σ_{n < R} c(n) e(nα)` for `R > N + k 2^L`. -/
theorem SG_eq (k N L R : ℕ) (hR : N + k * 2 ^ L < R) (α : ℝ) :
    Sg N α * Gs L α ^ k = SA (range R) (fun n => ((cf k N L n : ℝ) : ℂ)) α := by
  rw [Gs_pow]
  unfold Sg SA cf
  simp_rw [e_eq_eC]
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  have hpN : p ≤ N := by
    have := (mem_filter.mp hp).1; rw [Finset.mem_range] at this; omega
  refine sum_congr rfl fun ν _ => ?_
  have hmem : p + sv ν ∈ range R := Finset.mem_range.mpr (by have := sv_le ν; omega)
  rw [Finset.sum_eq_single_of_mem (p + sv ν) hmem (fun x _ hx => by
    rw [if_neg (Ne.symm hx)]; simp), if_pos rfl, one_mul, ← eC_add]
  push_cast
  rw [one_mul]
  congr 1; ring

/-- Parseval: `∫_0^1 |S G^k|² = Σ_{n < R} c(n)²`. -/
theorem integral_SG (k N L R : ℕ) (hR : N + k * 2 ^ L < R) :
    ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs L α ^ k‖ ^ 2 = ∑ n ∈ range R, cf k N L n ^ 2 := by
  simp_rw [SG_eq k N L R hR]
  exact parseval _ _

/-- `r'_k(n) ≤ c(n)` for `n ≤ N`: each representation counted by `r'_k(n)` has `p ≤ n ≤ N`. -/
theorem rk_le_cf (k N n : ℕ) (hn : n ≤ N) : (rk k N n : ℝ) ≤ cf k N (Nat.log 2 N) n := by
  classical
  set L := Nat.log 2 N
  have hcf : cf k N L n =
      (#{x ∈ primesLe N ×ˢ (univ : Finset (Fin k → Fin L)) | x.1 + sv x.2 = n} : ℕ) := by
    unfold cf
    rw [card_filter, ← sum_product']
    push_cast
    rfl
  rw [hcf]
  unfold rk
  have key := card_le_card_of_surjOn
    (s := {x ∈ primesLe N ×ˢ (univ : Finset (Fin k → Fin L)) | x.1 + sv x.2 = n})
    (t := {x ∈ range (n + 1) ×ˢ tuples k L | x.1.Prime ∧ n = x.1 + pow2sum x.2})
    (fun x => (x.1, fun i => ((x.2 i : ℕ) + 1)))
    (by
      intro y hy
      simp only [coe_filter, mem_product, Finset.mem_range, tuples, Fintype.mem_piFinset,
        Finset.mem_Icc, Set.mem_ofPred_eq] at hy
      obtain ⟨⟨hy1, hy2⟩, hp, hyn⟩ := hy
      refine ⟨(y.1, fun i => ⟨y.2 i - 1, by have := hy2 i; omega⟩), ?_, ?_⟩
      · simp only [coe_filter, mem_product, primesLe, mem_filter, Finset.mem_range, Finset.mem_univ, and_true,
          Set.mem_ofPred_eq]
        refine ⟨⟨by omega, hp⟩, ?_⟩
        rw [hyn]; unfold sv pow2sum
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hy2 i; congr 1; simp only; omega
      · ext
        · rfl
        · simp only; have := hy2 ‹_›; omega)
  exact_mod_cast key

/-- **Display (4)**, p.138, PROVED: `Σ_{n ≤ N} r'_k(n)² ≤ ∫_0^1 |S(α) G^k(α)|² dα`. -/
theorem display4 (k N : ℕ) :
    ∑ n ∈ range (N + 1), (rk k N n : ℝ) ^ 2 ≤
      ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 := by
  rw [integral_SG k N (Nat.log 2 N) (N + k * 2 ^ Nat.log 2 N + 1) (by omega)]
  calc ∑ n ∈ range (N + 1), (rk k N n : ℝ) ^ 2
      ≤ ∑ n ∈ range (N + 1), cf k N (Nat.log 2 N) n ^ 2 := by
        refine sum_le_sum fun n hn => ?_
        have hn' : n ≤ N := by rw [Finset.mem_range] at hn; omega
        exact pow_le_pow_left₀ (by positivity) (rk_le_cf k N n hn') 2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (range_subset_range.mpr (by omega)) (fun _ _ _ => by positivity)

/-- **Gallagher 1975, display (6)**, p.139, `g = 2`, cited: for `k ≥ 1` and `N ≥ N_k`,
`∫_0^1 |S G^k|² ≤ (2 N L^{2k} / log² N)(1 + O(log² 2k / k))`, absolute `O`. -/
def Display6 : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 * (1 + C * (Real.log (2 * k) ^ 2 / k))

/-- PROVED: display (6) and display (4) give Lemma 13, p.138. -/
theorem lemma13_of_display6 (h6 : Display6) : Lemma13 := by
  obtain ⟨C, hC⟩ := h6
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨Nk, hNk⟩ := hC k hk
  exact ⟨Nk, fun N hN => (display4 k N).trans (hNk N hN)⟩

/-- **Gallagher 1975, Theorem 1**, display (3), CONDITIONAL ON `Display6` alone. -/
theorem theorem1_of_display6 (h6 : Display6) : Theorem1 :=
  theorem1_of_lemma13 (lemma13_of_display6 h6)

/-- **Gallagher 1975, Theorem 2**, display (4) of p.125, `g = 2`, CONDITIONAL ON `Display6` alone. -/
theorem theorem2_of_display6 (h6 : Display6) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(rpp k N : ℝ) - 2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  theorem2_of_lemma13 (lemma13_of_display6 h6)

end LeanLab.Linnik.U7204

