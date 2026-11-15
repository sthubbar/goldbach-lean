module

public import LeanLab.Tolev2009.PublishedTheorem
public import LeanLab.Tolev2009.Sup83Split
public import LeanLab.Tolev2009.Major83

/-!
AI wrote this Lean code. Codex task83.
Binary Goldbach is open.
Source records: https://arxiv.org/abs/0902.2669 pages 3, 4 and 7.
The two analytic leaves, major_arc_leaf and minor_arc_sup_leaf, are proved in the lab files
this module imports, so published_assembly is unconditional.
-/

@[expose] public section

namespace LeanLab.Tolev2009.Decomp83

open Finset Real
open LeanLab.Tolev2009.Sup83Split (bilinear tau5)
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Dyadic

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.SeriesIdentification

/-- Page 2 display 5, invariance under equality on admissible inputs.
This is an implementation fact. Only positive moduli and reduced residues contribute. -/
theorem Estar_congr_admissible (S T : SSeries)
    (h : ∀ k l N, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      S k l N = T k l N)
    (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    Estar S lam l₃ B N = Estar T lam l₃ B N := by
  unfold Estar inner
  refine Finset.sum_congr rfl fun k₁ hk₁ => Finset.sum_congr rfl fun k₂ hk₂ => ?_
  congr 1
  funext l₁
  congr 1
  funext hl₁
  congr 1
  funext l₂
  congr 1
  funext hl₂
  congr 1
  refine Finset.sum_congr rfl fun k₃ hk₃ => ?_
  have h1 : 1 ≤ k₁ := (Finset.mem_Icc.mp hk₁).1
  have h2 : 1 ≤ k₂ := (Finset.mem_Icc.mp hk₂).1
  have h3 : 1 ≤ k₃ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk₃).1).1
  have hc1 : Nat.Coprime l₁ k₁ := (Finset.mem_filter.mp hl₁).2
  have hc2 : Nat.Coprime l₂ k₂ := (Finset.mem_filter.mp hl₂).2
  have hc3 : Nat.Coprime l₃ k₃ := (Finset.mem_filter.mp hk₃).2.symm
  have he := h ![k₁, k₂, k₃] ![l₁, l₂, l₃] N
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
  simp only [Δ, M, he]

/-- Page 2 display 5, the same estimate for two series agreeing on admissible data.
Derived from the stated agreement and the theorem for T. -/
theorem theorem_transfer_admissible (S T : SSeries)
    (h : ∀ k l N, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      S k l N = T k l N)
    (hT : TheTheorem T) : TheTheorem S := by
  intro A hA
  obtain ⟨B, hB, hb⟩ := hT A hA
  refine ⟨B, hB, fun l₃ hl₃ => ?_⟩
  obtain ⟨C, N₀, hc⟩ := hb l₃ hl₃
  refine ⟨C, N₀, fun lam hlam N hodd hN => ?_⟩
  rw [Estar_congr_admissible S T h]
  exact hc lam hlam N hodd hN

/-- Page 4 display 9. Major arc mean bound.
Published inputs: Tolev 1999 sections 4 and 5 and Halupczok 2008 Theorem 3.
The source references were reviewed by task45. Task83 checked the rendered paper page after network access was restored.
Split 2026-11-12 into the three errors of Major83, all three proved. -/
theorem major_arc_leaf : BoundE1 := by
  exact Major83.major_arc_of_three

/-- Page 4 display 12, supremum half only.
Published input: the adaptation of Tolev 1999 Lemma 12 cited by Tolev 2009.
The L2 half is already proved in L2Bound.display12_L2_cutoff.
The adaptation to general fixed l3 is proved here.
SPLIT 2026-11-12 route burst, AI wrote this proof: derived from Sup83Split.typeI_estimate,
Tolev 1999 page 86 displays 64 to 66, Sup83Split.typeII_estimate, pages 83 to 86 displays
55 to 63, both proved, and Sup83Split.prime_decomposition, page 71 Lemma 4 and page 82
display 52, proved in route burst 7. The block count C log N to 7 times the block bound log N to 330 minus 4A
gives the exponent 350 minus 4A. -/
theorem minor_arc_sup_leaf : Sup12Uniform := by
  intro A hA l₃ hl₃
  obtain ⟨Cᵢ, Nᵢ, hCᵢ, hI⟩ := Sup83Split.typeI_estimate A hA l₃ hl₃
  obtain ⟨Cᵢᵢ, Nᵢᵢ, hCᵢᵢ, hII⟩ := Sup83Split.typeII_estimate A hA l₃ hl₃
  obtain ⟨D, ND, hD, hdec⟩ := Sup83Split.prime_decomposition A hA l₃ hl₃
  refine ⟨D + D ^ 2 * (Cᵢ + Cᵢᵢ), max (max Nᵢ Nᵢᵢ) (max ND 3), by positivity, ?_⟩
  intro lam hlam N hodd hN α hα hminor
  have hNᵢ : Nᵢ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNᵢᵢ : Nᵢᵢ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hND : ND ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : (3 : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  obtain ⟨J, hJ, r, hr, x, M, M₁, H, H₁, a, b, c, he, hb⟩ :=
    hdec N hodd hND lam hlam α
  have hterm : ∀ j : Fin J,
      ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
        (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
        (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A) := by
    intro j
    rcases hb j with ⟨hc, hxlo, hxhi, hx, hM, hMM₁, hM₁, hH, hHH₁, hH₁,
      hprodlo, hprodhi, ha, htype⟩
    rcases htype with ⟨hsize, hbI⟩ | ⟨hlo, hhi, hbII⟩
    · have hi := hI N hodd hNᵢ lam hlam α hα hminor
        (x j) (M j) (M₁ j) (H j) (H₁ j)
        hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize (a j) (b j) ha hbI
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCᵢᵢ) (Nat.cast_nonneg N))
        (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
    · have hi := hII N hodd hNᵢᵢ lam hlam α hα hminor
        (x j) (M j) (M₁ j) (H j) (H₁ j)
        hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi (a j) (b j) ha hbII
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCᵢ) (Nat.cast_nonneg N))
        (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
  have hsum : ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
      (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
      (J : ℝ) * (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j : Fin J, D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A)) := by
        apply sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hb j).1 (hterm j) (norm_nonneg _) hD
      _ = _ := by simp
  have hpow : Real.log N ^ (7 : ℕ) * Real.log N ^ (330 - 4 * A) ≤
      Real.log N ^ (350 - 4 * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith)
  have hpow0 : Real.log N ^ (330 - 4 * A) ≤ Real.log N ^ (350 - 4 * A) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hsum' : ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
      (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
      D ^ 2 * (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (350 - 4 * A) := by
    calc
      _ ≤ (J : ℝ) * (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) := hsum
      _ ≤ (D * Real.log N ^ (7 : ℕ)) *
          (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = D ^ 2 * (Cᵢ + Cᵢᵢ) * N *
          (Real.log N ^ (7 : ℕ) * Real.log N ^ (330 - 4 * A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hpow0
    (show 0 ≤ D * (N : ℝ) by positivity))
  rw [he]
  calc
    _ ≤ ‖r‖ + ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
        (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ := norm_add_le _ _
    _ ≤ D * N * Real.log N ^ (350 - 4 * A) +
        D ^ 2 * (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (350 - 4 * A) := add_le_add hr' hsum'
    _ = _ := by ring

/-- Page 7, conclusion after display 20.
Unconditional: both analytic inputs, `major_arc_leaf` and `minor_arc_sup_leaf`, are proved.
All dyadic, divisor moment, L2 and minor arc bookkeeping is reused from task45.
The repository copy omits the lab's two legacy transfer theorems about an opaque series. -/
theorem published_assembly : TheTheorem halupczokSeries :=
  PublishedTheorem.publishedTheorem_of_display9_sup12 major_arc_leaf minor_arc_sup_leaf

end LeanLab.Tolev2009.Decomp83
