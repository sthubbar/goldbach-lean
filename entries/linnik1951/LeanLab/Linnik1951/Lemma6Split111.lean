module

public import LeanLab.Linnik1951.Decomp519a

/-!
P0093 page 166, Section 9: equation 9.1, Lemma 6 and the count of Lemma 7, equation 9.3.
Burst 8 p3 split of covered_square_split111 of Decomp111.
AI wrote the Lean code. Binary Goldbach is open.

The GRH content of covered_square_split111 is isolated here as one leaf, the single
system estimate system_mass_split111, which is what 9.1 gives for one system F_q with
q between Q and tau. Lemma 6, the Dirichlet choice of q, and the finite cover count are
proved here and assembled in Decomp111.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open MeasureTheory

/-- P0093 page 166, the system F_q of the phi of q segments of half width 2 over q tau
around the reduced fractions a over q. Rationals carry reduced numerators, so r.den
equal to q means a coprime to q. Local copy of arcSystem111 of Decomp111b, which sits
downstream of Decomp111. -/
def arcSystemSplit111 (q : ℕ) (τ : ℝ) : Set ℝ :=
  {x | ∃ r : ℚ, r.den = q ∧ |x - r| ≤ 2 / ((q : ℝ) * τ)}

/-- P0093 page 166 proof of Lemma 7, equation 9.3: a finite cover bounds the integral of
a nonnegative function by the sum of its integrals over the covering sets, which need
not be disjoint. Same proof as finite_cover_integral376 of Decomp376c, with any index
type. Proved. -/
theorem finite_cover_integral_split111 {ι : Type*} (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (S : Finset ι) (t : ι → Set ℝ)
    (hi : ∀ q ∈ S, IntegrableOn f (t q))
    (hcover : s ⊆ ⋃ q ∈ S, t q) :
    (∫ x in s, f x) ≤ ∑ q ∈ S, ∫ x in t q, f x := by
  classical
  have hUnion : (∫ x in ⋃ q ∈ S, t q, f x) ≤ ∑ q ∈ S, ∫ x in t q, f x := by
    clear hcover
    induction S using Finset.induction_on with
    | empty => simp
    | @insert q S hq ih =>
      have hiq := hi q (Finset.mem_insert_self q S)
      have hiS : ∀ i ∈ S, IntegrableOn f (t i) :=
        fun i hi' => hi i (Finset.mem_insert_of_mem hi')
      have hiU : IntegrableOn f (⋃ i ∈ S, t i) := integrableOn_finset_iUnion.mpr hiS
      have hle := integral_mono_measure
        (Measure.restrict_union_le (μ := volume) (t q) (⋃ i ∈ S, t i))
        (ae_of_all _ hf) (integrable_add_measure.mpr ⟨hiq, hiU⟩)
      rw [integral_add_measure hiq hiU] at hle
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert hq]
      exact hle.trans (add_le_add le_rfl (ih hiS))
  have hiU : IntegrableOn f (⋃ q ∈ S, t q) := integrableOn_finset_iUnion.mpr hi
  exact (setIntegral_mono_set hiU (ae_of_all _ hf) (ae_of_all _ hcover)).trans hUnion

/-- P0093 page 165 Section 8 and page 166 Section 9: every point theta of the unit
interval has the Dirichlet form a over q plus alpha with q at most tau and alpha at most
1 over q tau. If theta is not on a major arc, then q is above Q. Proved from Mathlib
Real.exists_rat_abs_sub_le_and_den_le. -/
theorem dirichlet_minor_split111 (N : ℕ) (hN : 1 ≤ N) (θ : ℝ)
    (hθm : ¬ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
      |θ - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) :
    ∃ r : ℚ, (N : ℝ) ^ (1 / 10 : ℝ) < (r.den : ℝ) ∧ (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) ∧
      |θ - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) := by
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hN1 (by norm_num)
  have hn : 0 < ⌊τ⌋₊ := Nat.floor_pos.mpr hτ1
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hn
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hτlt : τ ≤ (⌊τ⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one τ).le
  have hclose : |θ - r| ≤ 1 / ((r.den : ℝ) * τ) := by
    refine hr.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    rw [mul_comm (r.den : ℝ) τ]
    exact mul_le_mul_of_nonneg_right hτlt hdpos.le
  have hdτ : (r.den : ℝ) ≤ τ := by
    have h1 : (r.den : ℝ) ≤ (⌊τ⌋₊ : ℝ) := by exact_mod_cast hden
    exact h1.trans (Nat.floor_le (by linarith))
  refine ⟨r, ?_, hdτ, hclose⟩
  by_contra hle
  exact hθm ⟨r, not_lt.mp hle, hclose⟩

/-- P0093 page 166, Lemma 6: a segment of length N to the minus 0.99 that meets a minor
point theta lies in the single system F_q, where a over q is the Dirichlet fraction of
theta, because N to the minus 0.99 is at most 1 over q tau, as q tau is at most tau
squared, N to the two sevenths. Proved. -/
theorem lemma6_split111 (N : ℕ) (hN : 1 ≤ N) (c θ : ℝ)
    (hθc : θ ∈ Set.Icc (c - 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))
      (c + 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ))))
    (hθm : ¬ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
      |θ - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) :
    ∃ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) ∧
      Set.Icc (c - 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))
        (c + 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ))) ⊆
        arcSystemSplit111 q ((N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨r, hQ, hτ, hclose⟩ := dirichlet_minor_split111 N hN θ hθm
  refine ⟨r.den, hQ, hτ, ?_⟩
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hN1 (by norm_num)
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  set h : ℝ := 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)) with hhdef
  -- the segment length 2 h is at most 1 over q tau
  have hqτ : (r.den : ℝ) * τ ≤ (N : ℝ) ^ (99 / 100 : ℝ) := by
    calc (r.den : ℝ) * τ ≤ τ * τ := mul_le_mul_of_nonneg_right hτ (by linarith)
      _ = (N : ℝ) ^ (2 / 7 : ℝ) := by
          rw [hτdef, ← Real.rpow_add hNp]; norm_num
      _ ≤ (N : ℝ) ^ (99 / 100 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h2h : 2 * h ≤ 1 / ((r.den : ℝ) * τ) := by
    have hpos : 0 < (N : ℝ) ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hNp _
    rw [hhdef]
    calc 2 * (1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ))) = 1 / (N : ℝ) ^ (99 / 100 : ℝ) := by
          field_simp
      _ ≤ 1 / ((r.den : ℝ) * τ) :=
          one_div_le_one_div_of_le (by positivity) hqτ
  intro x hx
  refine ⟨r, rfl, ?_⟩
  have hxθ : |x - θ| ≤ 2 * h := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hθc.1, hθc.2]
  calc |x - r| = |(x - θ) + (θ - r)| := by ring_nf
    _ ≤ |x - θ| + |θ - r| := abs_add_le _ _
    _ ≤ 1 / ((r.den : ℝ) * τ) + 1 / ((r.den : ℝ) * τ) := add_le_add (hxθ.trans h2h) hclose
    _ = 2 / ((r.den : ℝ) * τ) := by ring

end LeanLab.Linnik1951
