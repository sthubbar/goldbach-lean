module

public import LeanLab.Tolev2009.Decomp341a
public import LeanLab.Tolev2009.Decomp336a

/-!
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 83 to 84 before display 56.
Two compatible congruences give one finite progression of lcm step.
-/

@[expose] public section

open Finset Real ComplexConjugate
namespace LeanLab.Tolev2009.Progressions341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp341a LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Decomp310a

/-- The affine progression for V on Tolev 1999 pages 83 to 84.
The pair of congruences is either empty or one progression of lcm step.
All product truncations remain in the progression. -/
theorem correlation_affine (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ)
    (hi : 1 ≤ i.2) (hj : 1 ≤ j.2)
    (hci : Nat.Coprime i.2 l₃) (hcj : Nat.Coprime j.2 l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    ∃ β : ℝ, ∃ J : ℕ,
      correlation l₃ N α x M M₁ i j =
        ∑ r ∈ range J, ee (β + (r : ℝ) *
          (α * (Nat.lcm i.2 j.2 : ℝ) * ((i.1 : ℝ) - j.1))) ∧
      (J : ℝ) ≤ 2 * M / Nat.lcm i.2 j.2 + 1 := by
  classical
  let h := Nat.lcm i.2 j.2
  have hh : 0 < h := Nat.lcm_pos (by omega) (by omega)
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  let s := (Ioc ⌊M⌋₊ ⌊M₁⌋₊).filter (fun m =>
    ((x < (m * i.1 : ℕ) ∧ (m * i.1 : ℕ) ≤ 2 * x ∧ m * i.1 ≤ N) ∧
      (m * i.1) % i.2 = l₃ % i.2) ∧
    ((x < (m * j.1 : ℕ) ∧ (m * j.1 : ℕ) ≤ 2 * x ∧ m * j.1 ≤ N) ∧
      (m * j.1) % j.2 = l₃ % j.2))
  have he : correlation l₃ N α x M M₁ i j =
      ∑ m ∈ s, ee (α * m * ((i.1 : ℝ) - j.1)) := by
    rw [correlation_eq_phase, ← sum_filter]
  by_cases hne : s.Nonempty
  · let a := s.min' hne
    let b := s.max' hne
    have ha : a ∈ s := s.min'_mem hne
    have hb : b ∈ s := s.max'_mem hne
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    have hab : a ≤ b := s.min'_le b hb
    have hki : Nat.Coprime i.2 i.1 := by
      have ht : Nat.Coprime i.2 (a * i.1) := by
        change Nat.gcd i.2 (a * i.1) = 1
        rw [Nat.gcd_rec, ha'.2.1.2, ← Nat.gcd_rec]
        exact hci
      exact ht.of_dvd_right (dvd_mul_left i.1 a)
    have hkj : Nat.Coprime j.2 j.1 := by
      have ht : Nat.Coprime j.2 (a * j.1) := by
        change Nat.gcd j.2 (a * j.1) = 1
        rw [Nat.gcd_rec, ha'.2.2.2, ← Nat.gcd_rec]
        exact hcj
      exact ht.of_dvd_right (dvd_mul_left j.1 a)
    have hmod : ∀ m ∈ s, a ≡ m [MOD h] := by
      intro m hm
      have hm' := mem_filter.mp hm
      apply Nat.mod_lcm
      · apply Nat.ModEq.cancel_left_of_coprime hki
        simpa only [Nat.mul_comm] using (show a * i.1 ≡ m * i.1 [MOD i.2] from
          ha'.2.1.2.trans hm'.2.1.2.symm)
      · apply Nat.ModEq.cancel_left_of_coprime hkj
        simpa only [Nat.mul_comm] using (show a * j.1 ≡ m * j.1 [MOD j.2] from
          ha'.2.2.2.trans hm'.2.2.2.symm)
    have hdiv : h ∣ b - a := (hmod b hb).dvd'
    have hbe : b = a + ((b - a) / h) * h := by
      rw [Nat.div_mul_cancel hdiv]
      omega
    let J := (b - a) / h + 1
    have hbetween : ∀ r < J, a ≤ a + r * h ∧ a + r * h ≤ b := by
      intro r hr
      dsimp [J] at hr
      constructor
      · omega
      · have ht := Nat.mul_le_mul_right h (show r ≤ (b - a) / h by omega)
        omega
    have hmem : ∀ r < J, a + r * h ∈ s := by
      intro r hr
      obtain ⟨hlo, hhi⟩ := hbetween r hr
      have ht : a ≡ a + r * h [MOD h] := by
        simp [Nat.ModEq, Nat.add_mod]
      have hti := (ht.of_dvd (Nat.dvd_lcm_left i.2 j.2)).mul_right i.1
      have htj := (ht.of_dvd (Nat.dvd_lcm_right i.2 j.2)).mul_right j.1
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp ha'.1).1.trans_le hlo,
        hhi.trans (mem_Ioc.mp hb'.1).2⟩, ?_, ?_⟩
      · have hpi := Nat.mul_le_mul_right i.1 hlo
        have hqi := Nat.mul_le_mul_right i.1 hhi
        refine ⟨⟨ha'.2.1.1.1.trans_le (by exact_mod_cast hpi),
          (by exact_mod_cast hqi : (((a + r * h) * i.1 : ℕ) : ℝ) ≤ (b * i.1 : ℕ)).trans hb'.2.1.1.2.1,
          hqi.trans hb'.2.1.1.2.2⟩, hti.symm.trans ha'.2.1.2⟩
      · have hpj := Nat.mul_le_mul_right j.1 hlo
        have hqj := Nat.mul_le_mul_right j.1 hhi
        refine ⟨⟨ha'.2.2.1.1.trans_le (by exact_mod_cast hpj),
          (by exact_mod_cast hqj : (((a + r * h) * j.1 : ℕ) : ℝ) ≤ (b * j.1 : ℕ)).trans hb'.2.2.1.2.1,
          hqj.trans hb'.2.2.1.2.2⟩, htj.symm.trans ha'.2.2.2⟩
    have hs : s = (range J).image (fun r => a + r * h) := by
      ext m
      constructor
      · intro hm
        have ham : a ≤ m := s.min'_le m hm
        have hmb : m ≤ b := s.le_max' m hm
        have hdm : h ∣ m - a := (hmod m hm).dvd'
        refine mem_image.mpr ⟨(m - a) / h, mem_range.mpr ?_, ?_⟩
        · dsimp [J]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : m - a ≤ b - a))
        · rw [Nat.div_mul_cancel hdm]
          omega
      · intro hm
        obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
        exact hmem r (mem_range.mp hr)
    refine ⟨α * a * ((i.1 : ℝ) - j.1), J, ?_, ?_⟩
    · rw [he, hs, sum_image]
      · apply sum_congr rfl
        intro r hr
        congr 1
        push_cast
        ring
      · intro r hr r' hr' heq
        exact Nat.mul_right_cancel hh (Nat.add_left_cancel heq)
    · have hbpos : 0 < b := lt_of_lt_of_le (by have := (mem_Ioc.mp ha'.1).1; omega : 0 < a) hab
      have hM₁0 : 0 ≤ M₁ := by
        by_contra hn
        have hz := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hn))
        rw [hz] at hb'
        have := (mem_Ioc.mp hb'.1).2
        omega
      have hble : (b : ℝ) ≤ 2 * M :=
        (show (b : ℝ) ≤ ⌊M₁⌋₊ by exact_mod_cast (mem_Ioc.mp hb'.1).2).trans
          ((Nat.floor_le hM₁0).trans hM₁)
      have hbeR : (b : ℝ) = a + ((b - a) / h : ℕ) * (h : ℝ) := by exact_mod_cast hbe
      have hJR : (J : ℝ) = ((b - a) / h : ℕ) + 1 := by simp [J]
      have hnum : ((J : ℝ) - 1) * h ≤ 2 * M := by
        rw [hJR]
        nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
      have hquot := (le_div_iff₀ hhr).mpr hnum
      change (J : ℝ) ≤ 2 * M / h + 1
      linarith
  · refine ⟨0, 0, ?_, ?_⟩
    · rw [he, not_nonempty_iff_eq_empty.mp hne]
      simp
    · simp only [Nat.cast_zero]
      exact add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) zero_le_one

/-- The geometric bound for V before Tolev 1999 display 56.
The resonance case and one endpoint term are retained. -/
theorem correlation_bound (l₃ N : ℕ) (α x M M₁ : ℝ) (i j : ℕ × ℕ)
    (hi : 1 ≤ i.2) (hj : 1 ≤ j.2)
    (hci : Nat.Coprime i.2 l₃) (hcj : Nat.Coprime j.2 l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    ‖correlation l₃ N α x M M₁ i j‖ ≤
      Decomp336a.phaseCap (α * ((i.1 : ℝ) - j.1)) M (Nat.lcm i.2 j.2) := by
  obtain ⟨β, J, he, hJ⟩ := correlation_affine l₃ N α x M M₁ i j hi hj hci hcj hM hM₁
  have ht : α * (Nat.lcm i.2 j.2 : ℝ) * ((i.1 : ℝ) - j.1) =
      (α * ((i.1 : ℝ) - j.1)) * (Nat.lcm i.2 j.2 : ℝ) := by ring
  rw [he]
  simp only [ht]
  unfold Decomp336a.phaseCap
  split_ifs with hθ
  · apply le_trans (norm_sum_le _ _)
    simpa only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one] using hJ
  · exact (progression_phase_bound β _ J hθ).trans (min_le_min hJ le_rfl)

/-- The diagonal count bound before Tolev 1999 display 56.
No assumption comparing M with the lcm has been inserted. -/
theorem correlation_diagonal_bound (l₃ N : ℕ) (α x M M₁ : ℝ) (l k₁ k₂ : ℕ)
    (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (hc₁ : Nat.Coprime k₁ l₃) (hc₂ : Nat.Coprime k₂ l₃)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) :
    ‖correlation l₃ N α x M M₁ (l, k₁) (l, k₂)‖ ≤
      2 * M / Nat.lcm k₁ k₂ + 1 := by
  simpa [Decomp336a.phaseCap, ee_zero] using
    correlation_bound l₃ N α x M M₁ (l, k₁) (l, k₂) h₁ h₂ hc₁ hc₂ hM hM₁

end LeanLab.Tolev2009.Progressions341
