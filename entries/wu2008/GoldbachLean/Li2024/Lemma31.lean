module

public import GoldbachLean.Wu2008.Err

/-!
# Li 2024, Lemma 3.1, with the range of S₁₅ repaired

R. Li, *On Chen's theorem, Goldbach's conjecture and almost prime twins II*, arXiv 2405.05727 v4,
Mathematical Reports 2026, Lemma 3.1. Li's Lemma 3.1 is Wu 2008, Lemma 2.2, at
κ₁ = 1/11.49 and κ₂ = 1/6.18, with the same gap in the range of the last sum, Li's S₁₅, Wu's Υ₁₁.
Li's parameters satisfy Wu's hypotheses, `li_admissible`, so the repaired Wu lemma
`GoldbachLean.Wu2008.WuSum.lemma22_wuA` gives Li's Lemma 3.1 with the range repaired to
p₄ < N^{1/2−3/11.49}, for A = {N − p}, with the explicit error 4N/(N^κ₁ − 1): `lemma31_repaired`.
AI wrote the Lean code, Claude, Anthropic; it was checked by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace GoldbachLean.Li2024.Lemma31

open GoldbachLean.Wu2008.WuReal GoldbachLean.Wu2008.WuSum

/-- Li's κ₁ = 1/11.49. -/
def lk1 : ℝ := 100 / 1149
/-- Li's κ₂ = 1/6.18. -/
def lk2 : ℝ := 100 / 618

/-- Li's parameters satisfy Wu's hypotheses. -/
theorem li_admissible : Admissible lk1 lk2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [lk1, lk2] <;> norm_num

/-- **Li 2024, Lemma 3.1, with S₁₅'s range repaired**, for A = {N − p}, explicit error. -/
theorem lemma31_repaired (N : ℕ) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ lk1) :
    (3 * Y1 (wuA N) N lk1 + Y2 (wuA N) N lk2 + Y5 (wuA N) N lk1 lk2 + Y6 (wuA N) N lk1 lk2 : ℝ)
      - Y3 (wuA N) N lk1 - Y4 (wuA N) N lk1 - 2 * Y7 (wuA N) N lk1 - Y8 (wuA N) N lk1
      - Y9 (wuA N) N lk1 lk2 - Y10 (wuA N) N lk1 lk2 - Y11 (wuA N) N lk1 lk2
      ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ lk1 - 1)) :=
  lemma22_wuA N lk1 lk2 li_admissible hN hNk

end GoldbachLean.Li2024.Lemma31
end
