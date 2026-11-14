module

public import Mathlib
public import LeanLab.Linnik.U7204Display4

/-!
P0094 Gallagher 1975, "Primes and Powers of 2", Invent. Math. 29, 125-142: Lemma 12, p.138,
and display (6) for `1 ≤ k < k₀`, p.139, read from the page images, PDF pages 15 and 16.
Unit U-7206, CLOUD MANUAL-N2, 2026-10-21.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

* `Lemma12`: Lemma 12, p.138, cited as a `Prop`, NOT proved here:
  `∫_0^1 |S(α) G(α)|² dα ≪ N`, `S(α) = Σ_{p ≤ N} e(pα)`, `G(α) = Σ_{ν=1}^{L} e(2^ν α)`,
  `L = [log₂ N]`. The paper proves it by the Brun-Selberg sieve.
* `norm_Gs_le`: PROVED, `|G(α)| ≤ L`.
* `arc_bound`: PROVED, the step of p.139 that uses Lemma 12: on any measurable `A ⊆ [0,1]` with
  `|G| ≤ M` on `A`, `∫_A |S G^k|² ≤ M^{2k-2} ∫_0^1 |S G|²`. With `A = C(𝔐) ∩ C(ℰ)` and
  `M = (1-η)L` this is the printed inequality; with `M = L`, `A = [0,1]` it is the small `k` case.
* `display6_small`: PROVED from `Lemma12`, display (6) for each fixed `k ≥ 1` with the constant
  depending on `k`, which is the paper's "for `1 ≤ k < k₀` this follows easily from Lemma 12".
* `Display6Large`: display (6) for `k ≥ k₀`, cited as a `Prop`, NOT proved here; the paper gets it
  from (5), Lemmas 2, 11 and 12.
* `display6_of`: PROVED, `Display6Large ∧ Lemma12 → Display6`.
* `theorem1_of_large`, `theorem2_of_large`: Theorems 1 and 2, CONDITIONAL ON `Display6Large` and
  `Lemma12` only.
-/

@[expose] public section

open Finset Real MeasureTheory

noncomputable section
namespace LeanLab.Linnik.U7206

open LeanLab.Linnik.Gallagher1975 LeanLab.Linnik.Gallagher1975Thm2 LeanLab.Linnik.U7201
open LeanLab.Linnik.U7204
open LeanLab.Linnik.U1412Display53 (eC norm_eC)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs continuous_SA)

/-- **Gallagher 1975, Lemma 12**, p.138, cited: `∫_0^1 |S(α) G(α)|² dα ≪ N`, `L = [log₂ N]`. -/
def Lemma12 : Prop :=
  ∃ C : ℝ, ∀ N : ℕ,
    ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α‖ ^ 2 ≤ C * N

/-- **Display (6) for `k ≥ k₀`**, p.139, `g = 2`, cited: the large `k` half of `Display6`. -/
def Display6Large : Prop :=
  ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 * (1 + C * (Real.log (2 * k) ^ 2 / k))

/-- PROVED: `|G(α)| ≤ L`. -/
theorem norm_Gs_le (L : ℕ) (α : ℝ) : ‖Gs L α‖ ≤ L := by
  unfold Gs
  calc ‖∑ ν ∈ Finset.Icc 1 L, eC (2 ^ ν * α)‖ ≤ ∑ ν ∈ Finset.Icc 1 L, ‖eC (2 ^ ν * α)‖ :=
        norm_sum_le _ _
    _ = L := by simp [norm_eC]

theorem continuous_Sg (N : ℕ) : Continuous (Sg N) := continuous_SA _ _

/-- PROVED, pointwise: `|S G^k|² ≤ M^{2k-2} |S G|²` when `|G| ≤ M`, `k ≥ 1`. -/
theorem pointwise {k : ℕ} (hk : 1 ≤ k) {s g : ℂ} {M : ℝ} (hg : ‖g‖ ≤ M) :
    ‖s * g ^ k‖ ^ 2 ≤ M ^ (2 * k - 2) * ‖s * g‖ ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) - 2 = 2 * j by omega, norm_mul, norm_pow, norm_mul]
  have h2 : ‖g‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  calc (‖s‖ * ‖g‖ ^ (j + 1)) ^ 2 = (‖s‖ * ‖g‖) ^ 2 * (‖g‖ ^ 2) ^ j := by ring
    _ ≤ (‖s‖ * ‖g‖) ^ 2 * (M ^ 2) ^ j :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 j) (by positivity)
    _ = M ^ (2 * j) * (‖s‖ * ‖g‖) ^ 2 := by rw [pow_mul]; ring

/-- PROVED, the step of p.139 that uses Lemma 12: on a measurable `A ⊆ [0,1]` with `|G| ≤ M`,
`∫_A |S G^k|² ≤ M^{2k-2} ∫_0^1 |S G|²`. -/
theorem arc_bound {k : ℕ} (hk : 1 ≤ k) (N L : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (hAs : A ⊆ Set.Icc 0 1) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ α ∈ A, ‖Gs L α‖ ≤ M) :
    ∫ α in A, ‖Sg N α * Gs L α ^ k‖ ^ 2 ≤
      M ^ (2 * k - 2) * ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs L α‖ ^ 2 := by
  have c1 : Continuous fun α => ‖Sg N α * Gs L α ^ k‖ ^ 2 :=
    ((continuous_Sg N).mul ((continuous_Gs L).pow k)).norm.pow 2
  have c2 : Continuous fun α => ‖Sg N α * Gs L α‖ ^ 2 :=
    ((continuous_Sg N).mul (continuous_Gs L)).norm.pow 2
  have i1 : IntegrableOn (fun α => ‖Sg N α * Gs L α ^ k‖ ^ 2) A :=
    c1.integrableOn_Icc.mono_set hAs
  have i2' : IntegrableOn (fun α => ‖Sg N α * Gs L α‖ ^ 2) (Set.Icc 0 1) := c2.integrableOn_Icc
  have i2 : IntegrableOn (fun α => M ^ (2 * k - 2) * ‖Sg N α * Gs L α‖ ^ 2) A :=
    (i2'.mono_set hAs).const_mul _
  calc ∫ α in A, ‖Sg N α * Gs L α ^ k‖ ^ 2
      ≤ ∫ α in A, M ^ (2 * k - 2) * ‖Sg N α * Gs L α‖ ^ 2 :=
        setIntegral_mono_on i1 i2 hA fun α hα => pointwise hk (hM α hα)
    _ = M ^ (2 * k - 2) * ∫ α in A, ‖Sg N α * Gs L α‖ ^ 2 := integral_const_mul _ _
    _ ≤ M ^ (2 * k - 2) * ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs L α‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM0 _)
        exact setIntegral_mono_set i2' (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall fun x (hx : x ∈ A) => hAs hx)

/-- PROVED: `log N ≤ [log₂ N]` for `N ≥ 8`. -/
theorem log_le_L {N : ℕ} (hN : 8 ≤ N) : Real.log N ≤ (Nat.log 2 N : ℝ) := by
  have hL3 : 3 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlt : (N : ℝ) < 2 ^ (Nat.log 2 N + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log N < (Nat.log 2 N + 1 : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]; exact Real.log_lt_log hNpos hlt
  have h2 := Real.log_two_lt_d9
  have hL3' : (3 : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hL3
  push_cast at hlog
  nlinarith

/-- **Display (6) for fixed `k`**, PROVED from `Lemma12`: for `1 ≤ k` and `N ≥ 8`,
`∫_0^1 |S G^k|² ≤ 2 N L^{2k} / log² N · (1 + C' log² 2k / k)` whenever `C' log² 2k / k ≥ |C|`. -/
theorem display6_small {C : ℝ}
    (h12 : ∀ N : ℕ, ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α‖ ^ 2 ≤ C * N)
    {k : ℕ} (hk : 1 ≤ k) {C' : ℝ} (hC' : |C| ≤ C' * (Real.log (2 * k) ^ 2 / k))
    {N : ℕ} (hN : 8 ≤ N) :
    ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 * (1 + C' * (Real.log (2 * k) ^ 2 / k)) := by
  set Lr : ℝ := (Nat.log 2 N : ℝ)
  set x : ℝ := C' * (Real.log (2 * k) ^ 2 / k)
  set P : ℝ := Lr ^ (2 * k - 2)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlg : 0 < Real.log N := Real.log_pos hN1
  have hLge := log_le_L hN
  have hP : 0 ≤ P := by positivity
  have hNn : (0 : ℝ) ≤ N := by positivity
  have hq : 1 ≤ Lr ^ 2 / Real.log N ^ 2 :=
    (one_le_div (by positivity)).mpr (pow_le_pow_left₀ hlg.le hLge 2)
  have hpow : Lr ^ (2 * k) = P * Lr ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hx : |C| ≤ x := hC'
  have hC0 := abs_nonneg C
  have step1 := arc_bound hk N (Nat.log 2 N) measurableSet_Icc subset_rfl (Nat.cast_nonneg _)
    (fun α _ => norm_Gs_le (Nat.log 2 N) α)
  calc ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2
      ≤ P * ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α * Gs (Nat.log 2 N) α‖ ^ 2 := step1
    _ ≤ P * (|C| * N) :=
        mul_le_mul_of_nonneg_left ((h12 N).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) hNn)) hP
    _ = (P * N) * |C| := by ring
    _ ≤ (P * N) * (2 * (1 + x)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * N * P * 1 * (1 + x) := by ring
    _ ≤ 2 * N * P * (Lr ^ 2 / Real.log N ^ 2) * (1 + x) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 2 * N * Lr ^ (2 * k) / Real.log N ^ 2 * (1 + x) := by rw [hpow]; ring

/-- PROVED: `Display6Large` and `Lemma12` give `Display6`. -/
theorem display6_of (hL : Display6Large) (h12 : Lemma12) : Display6 := by
  obtain ⟨C, k₀, hC⟩ := hL
  obtain ⟨C12, h12⟩ := h12
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C (|C12| * k₀ / Real.log 2 ^ 2), fun k hk => ?_⟩
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx0 : 0 ≤ Real.log (2 * k) ^ 2 / k := by positivity
  by_cases hkk : k₀ ≤ k
  · obtain ⟨Nk, hN⟩ := hC k hkk
    refine ⟨Nk, fun N hN' => (hN N hN').trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_right (le_max_left C (|C12| * k₀ / Real.log 2 ^ 2)) hx0
    linarith
  · push Not at hkk
    refine ⟨8, fun N hN => display6_small h12 hk ?_ hN⟩
    have hk0 : (k : ℝ) < k₀ := by exact_mod_cast hkk
    have hlog2k : Real.log 2 ≤ Real.log (2 * k) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hsq : Real.log 2 ^ 2 ≤ Real.log (2 * k) ^ 2 := pow_le_pow_left₀ hl2.le hlog2k 2
    have hratio : Real.log 2 ^ 2 / k₀ ≤ Real.log (2 * k) ^ 2 / k := by
      apply div_le_div₀ (by positivity) hsq (by positivity) hk0.le
    have hk0pos : (0 : ℝ) < k₀ := by linarith
    calc |C12| = (|C12| * k₀ / Real.log 2 ^ 2) * (Real.log 2 ^ 2 / k₀) := by
          field_simp
      _ ≤ max C (|C12| * k₀ / Real.log 2 ^ 2) * (Real.log (2 * k) ^ 2 / k) :=
          mul_le_mul (le_max_right _ _) hratio (by positivity)
            (le_max_of_le_right (by positivity))

/-- **Gallagher 1975, Theorem 1**, CONDITIONAL ON `Display6Large` and `Lemma12` only. -/
theorem theorem1_of_large (hL : Display6Large) (h12 : Lemma12) : Theorem1 :=
  theorem1_of_display6 (display6_of hL h12)

/-- **Gallagher 1975, Theorem 2**, `g = 2`, CONDITIONAL ON `Display6Large` and `Lemma12` only. -/
theorem theorem2_of_large (hL : Display6Large) (h12 : Lemma12) :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(rpp k N : ℝ) - 2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  theorem2_of_display6 (display6_of hL h12)

end LeanLab.Linnik.U7206

