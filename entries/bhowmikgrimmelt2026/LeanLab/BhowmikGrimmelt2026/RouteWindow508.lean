module

public import LeanLab.BhowmikGrimmelt2026.RouteReflect508
public import LeanLab.BhowmikGrimmelt2026.RouteRight508

/-!
ROUTE for `oscillatory_zero_modes508`, part eight: the full window count of zeros.
Source: P0029, the Bhowmik and Grimmelt survey, page 11 display 3.7, which uses the count of
zeros in a window of height one without stating it. The count is that of Davenport,
Multiplicative Number Theory, chapter 16, by Jensen's formula, for the right half of the
strip, and chapter 9, the functional equation, to carry the left half to the right half of
the inverse character.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- P0029 page 11 display 3.7, the left half of the zero count, from Davenport chapter 9:
the zeros of `L (s, χ)` with `0 < Re ρ < 1/2` and ordinate within one of `t` are carried by
`ρ ↦ 1 - ρ`, injectively and with the same multiplicity, to zeros of `L (s, χ⁻¹)` with
`1/2 ≤ Re < 1` and ordinate within one of `-t`, so any bound for the right half of the
inverse character at `-t` bounds them. -/
theorem left_window_reflect508 {A : ℝ}
    (hA : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧
        |ρ.im - t| ≤ 1) →
      ∑ ρ ∈ Z, (mult χ ρ : ℝ) ≤ A * Real.log ((q : ℝ) * (|t| + 2)))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧
      |ρ.im - t| ≤ 1) :
    ∑ ρ ∈ Z, (mult χ ρ : ℝ) ≤ A * Real.log ((q : ℝ) * (|t| + 2)) := by
  have himg : ∑ ρ ∈ Z.image (fun ρ : ℂ => 1 - ρ), (mult χ⁻¹ ρ : ℝ) =
      ∑ ρ ∈ Z, (mult χ ρ : ℝ) := by
    rw [Finset.sum_image (fun a _ b _ h => sub_right_injective h)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    obtain ⟨-, h0, h1, -⟩ := hZ ρ hρ
    rw [character_mult_reflection508 χ h0 (by linarith)]
  rw [← himg]
  have h := hA q χ⁻¹ (-t) (Z.image (fun ρ : ℂ => 1 - ρ)) (by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨ρ, hρ, rfl⟩ := hw
    obtain ⟨hz, h0, h1, him⟩ := hZ ρ hρ
    refine ⟨character_zero_reflection508 χ hz h0 (by linarith), ?_, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im]
      rw [abs_le] at him ⊢
      constructor <;> linarith)
  rwa [abs_neg] at h

/-- P0029 page 11 display 3.7, the zero count behind the bound of the zero sum, which the
survey uses without stating it, from Davenport, Multiplicative Number Theory, chapters 9
and 16: the zeros of `L (s, χ)` in the open critical strip with ordinate within one of `t`,
counted with multiplicity, number at most a constant times `log (q (|t| + 2))`. The zeros
with real part at least one half are counted by `right_window_count508`, the Jensen count;
the others are reflected by the functional equation to the inverse character. -/
theorem zero_window_count_full508 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
      (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im - t| ≤ 1) →
      ∑ ρ ∈ Z, (mult χ ρ : ℝ) ≤ A * Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨A, hA0, hA⟩ := right_window_count508
  refine ⟨2 * A, by positivity, ?_⟩
  intro q _ χ t S hS
  have h1 : ∑ ρ ∈ S with 1 / 2 ≤ ρ.re, (mult χ ρ : ℝ) ≤
      A * Real.log ((q : ℝ) * (|t| + 2)) := by
    apply hA q χ t
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, -, h1, him⟩ := hS ρ hρ.1
    exact ⟨hz, hρ.2, h1, him⟩
  have h2 : ∑ ρ ∈ S with ¬ 1 / 2 ≤ ρ.re, (mult χ ρ : ℝ) ≤
      A * Real.log ((q : ℝ) * (|t| + 2)) := by
    apply left_window_reflect508 hA χ t
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, h0, -, him⟩ := hS ρ hρ.1
    exact ⟨hz, h0, not_le.mp hρ.2, him⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ => 1 / 2 ≤ ρ.re)
    (fun ρ => (mult χ ρ : ℝ))
  linarith

end LeanLab.BhowmikGrimmelt2026
