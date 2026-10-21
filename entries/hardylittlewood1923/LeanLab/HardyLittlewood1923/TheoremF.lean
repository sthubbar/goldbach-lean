module

public import LeanLab.HardyLittlewood1923.TheoremFCount
public import LeanLab.HardyLittlewood1923.TheoremFMean

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5903, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem F, (4.21) to (4.23)

Read from `papers/P0004.pdf`, Acta Math. 44, p. 34, Theorem F: suppose
`N₂(n) ∼ A n/(log n)² ∏_{p ∣ n, p odd} (p-1)/(p-2)` for even `n`, (4.21), and
`N₂(n) = o(n/(log n)²)` for odd `n`, (4.22). Then `A = 2 C₂`, `C₂ = ∏_{ϖ ≥ 3} (1 - 1/(ϖ-1)²)`, (4.23).
So the only constant an asymptotic of the conjectured shape can carry is the one of Conjecture A;
the paper uses this to refute the formulas of Sylvester and Stäckel. Here `N₂ = Nr 2`, the product
is `Br 2 n` and `C₂ = Cr 2`, both as defined in `TheoremB34.lean`.

Proof, as in the paper by averaging: `Σ_{n ≤ N} N₂(n) (log n)² ∼ N²/2`, `TheoremFCount.lean`, from the
prime number theorem, and `Σ_{n ≤ N, n even} n Br 2 n ∼ N²/(4 C₂)`, `TheoremFMean.lean`. PROVED with
no hypothesis beyond (4.21) and (4.22), which are the theorem's own hypotheses.

Conjecture A itself, binary Goldbach with the asymptotic, is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- The main term of (4.21), `n/(log n)² ∏_{p ∣ n, p odd} (p-1)/(p-2)`. -/
noncomputable def M2 (n : ℕ) : ℝ := (n : ℝ) / Real.log n ^ 2 * Br 2 n

/-- (4.21) with the constant `A`, in the `ε` form of `∼`. -/
def hyp421 (A : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, Even n → n₀ ≤ n → |(Nr 2 n : ℝ) - A * M2 n| ≤ ε * M2 n

/-- (4.22), `N₂(n) = o(n/(log n)²)` for odd `n`. -/
def hyp422 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, ¬ Even n → n₀ ≤ n → (Nr 2 n : ℝ) ≤ ε * ((n : ℝ) / Real.log n ^ 2)

lemma Br2_nonneg (n : ℕ) : 0 ≤ Br 2 n := by
  unfold Br
  refine prod_nonneg fun p hp => ?_
  rw [mem_filter] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hpp hp.2
  apply div_nonneg <;> nlinarith

lemma M2_mul_log (n : ℕ) (hn : 2 ≤ n) : M2 n * Real.log n ^ 2 = (n : ℝ) * Br 2 n := by
  have hL : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  unfold M2; field_simp

/-- **Hardy-Littlewood 1923, Theorem F**: (4.21) and (4.22) force `A = 2 C₂`, (4.23). -/
theorem theoremF (A : ℝ) (h1 : hyp421 A) (h2 : hyp422) : A = 2 * Cr 2 := by
  have hC := Cr2_pos
  set c := 1 / (4 * Cr 2) with hcdef
  have hc : 0 < c := by positivity
  -- it suffices that |1/2 - A c| ≤ η for every η > 0
  suffices hη : ∀ η : ℝ, 0 < η → η ≤ 1 → |1 / 2 - A * c| ≤ η by
    have h0 : 1 / 2 - A * c = 0 := by
      by_contra hne
      have hp := abs_pos.mpr hne
      have := hη (min (|1 / 2 - A * c| / 2) 1) (by positivity) (min_le_right _ _)
      have := min_le_left (|1 / 2 - A * c| / 2) 1
      linarith
    rw [hcdef] at h0
    field_simp at h0
    linarith
  intro η hη hη1
  set ε := η / (4 * (4 + |A| + c)) with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]
    nlinarith [abs_nonneg A, hc.le]
  obtain ⟨n₁, hn₁⟩ := h1 ε hε
  obtain ⟨n₂, hn₂⟩ := h2 ε hε
  set n₀ := max (max n₁ n₂) 2 with hn₀def
  set D : ℕ → ℝ := fun n => (Nr 2 n : ℝ) * Real.log n ^ 2 - A * (if Even n then (n : ℝ) * Br 2 n else 0)
    with hDdef
  set C := ∑ n ∈ Finset.range n₀, |D n| with hCdef
  have hC0 : 0 ≤ C := sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨N₃, hN₃⟩ := sum_N2_log_sq ε hε
  obtain ⟨N₄, hN₄⟩ := mean_even_Br2 ε hε
  -- N large enough that C ≤ (η/4) N²
  obtain ⟨N₅, hN₅⟩ : ∃ N₅ : ℕ, ∀ N : ℕ, N₅ ≤ N → C ≤ η / 4 * (N : ℝ) ^ 2 := by
    obtain ⟨N₅, h⟩ := exists_nat_ge (4 * C / η)
    refine ⟨N₅, fun N hN => ?_⟩
    have h5 : (N₅ : ℝ) ≤ N := by exact_mod_cast hN
    have h6 : 4 * C / η ≤ (N : ℝ) := h.trans h5
    have h7 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos N with rfl | hN0
      · simp
      · have : (1 : ℝ) ≤ N := by exact_mod_cast hN0
        nlinarith
    rw [div_le_iff₀ hη] at h6
    nlinarith
  set N := max (max n₀ N₃) (max N₄ (max N₅ 1)) with hNdef
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hNn₀ : n₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS1 := hN₃ N (le_trans (le_max_right _ _) (le_max_left _ _))
  have hS2 := hN₄ N (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCN := hN₅ N (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  set S1 := ∑ n ∈ Finset.range (N + 1), (Nr 2 n : ℝ) * Real.log n ^ 2
  set S2 := ∑ n ∈ (Finset.range (N + 1)).filter Even, (n : ℝ) * Br 2 n
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  -- S1 - A S2 = Σ D
  have hdiff : S1 - A * S2 = ∑ n ∈ Finset.range (N + 1), D n := by
    simp only [hDdef]
    rw [sum_sub_distrib, ← mul_sum, ← sum_filter]
  -- bound Σ D
  have hsplit : ∑ n ∈ Finset.range (N + 1), D n =
      ∑ n ∈ Finset.range n₀, D n + ∑ n ∈ Finset.Ico n₀ (N + 1), D n :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  have htail : |∑ n ∈ Finset.Ico n₀ (N + 1), D n| ≤ ε * S2 + 2 * ε * (N : ℝ) ^ 2 := by
    have hpt : ∀ n ∈ Finset.Ico n₀ (N + 1),
        |D n| ≤ ε * (if Even n then (n : ℝ) * Br 2 n else 0) + ε * (n : ℝ) := by
      intro n hn
      rw [mem_Ico] at hn
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn.1
      have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      by_cases he : Even n
      · have := hn₁ n he (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn.1)
        simp only [hDdef, if_pos he]
        rw [← M2_mul_log n hn2, ← mul_assoc, ← sub_mul, abs_mul, abs_of_pos (pow_pos hL 2)]
        have h' : |(Nr 2 n : ℝ) - A * M2 n| * Real.log n ^ 2 ≤ ε * M2 n * Real.log n ^ 2 :=
          mul_le_mul_of_nonneg_right this (by positivity)
        rw [mul_assoc ε, M2_mul_log n hn2] at h'
        nlinarith
      · have := hn₂ n he (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn.1)
        simp only [hDdef, if_neg he, mul_zero, sub_zero]
        rw [abs_of_nonneg (by positivity)]
        have h' := mul_le_mul_of_nonneg_right this (le_of_lt (pow_pos hL 2))
        rw [mul_assoc, div_mul_cancel₀ _ (pow_pos hL 2).ne'] at h'
        linarith
    have hsumn : ∑ n ∈ Finset.range (N + 1), (n : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by
      have : ∑ n ∈ Finset.range (N + 1), (n : ℝ) ≤ ∑ n ∈ Finset.range (N + 1), (N : ℝ) :=
        sum_le_sum fun n hn => by
          rw [mem_range] at hn; exact_mod_cast (by omega : n ≤ N)
      rw [sum_const, card_range, nsmul_eq_mul] at this
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      push_cast at this
      nlinarith
    calc |∑ n ∈ Finset.Ico n₀ (N + 1), D n|
        ≤ ∑ n ∈ Finset.Ico n₀ (N + 1), |D n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico n₀ (N + 1),
          (ε * (if Even n then (n : ℝ) * Br 2 n else 0) + ε * (n : ℝ)) := sum_le_sum hpt
      _ ≤ ∑ n ∈ Finset.range (N + 1),
          (ε * (if Even n then (n : ℝ) * Br 2 n else 0) + ε * (n : ℝ)) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
          · intro n hn; rw [mem_Ico] at hn; rw [mem_range]; omega
          · have := Br2_nonneg n
            split_ifs <;> positivity
      _ = ε * S2 + ε * ∑ n ∈ Finset.range (N + 1), (n : ℝ) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter]
      _ ≤ ε * S2 + ε * (2 * (N : ℝ) ^ 2) := by gcongr
      _ = ε * S2 + 2 * ε * (N : ℝ) ^ 2 := by ring
  have hhead : |∑ n ∈ Finset.range n₀, D n| ≤ C := abs_sum_le_sum_abs _ _
  have hS1A : |S1 - A * S2| ≤ C + ε * S2 + 2 * ε * (N : ℝ) ^ 2 := by
    rw [hdiff, hsplit]
    have := abs_add_le (∑ n ∈ Finset.range n₀, D n) (∑ n ∈ Finset.Ico n₀ (N + 1), D n)
    linarith
  have hcN : c * (N : ℝ) ^ 2 = (N : ℝ) ^ 2 / (4 * Cr 2) := by rw [hcdef]; ring
  rw [← hcN] at hS2
  have hS2le : S2 ≤ (c + 1) * (N : ℝ) ^ 2 := by
    rw [abs_le] at hS2; nlinarith
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hid : (1 / 2 - A * c) * (N : ℝ) ^ 2 =
      ((N : ℝ) ^ 2 / 2 - S1) + (S1 - A * S2) + A * (S2 - c * (N : ℝ) ^ 2) := by ring
  have hbound : |1 / 2 - A * c| * (N : ℝ) ^ 2 ≤ η * (N : ℝ) ^ 2 := by
    rw [← abs_of_pos hN2, ← abs_mul, abs_of_pos hN2, hid]
    have t1 := abs_add_le (((N : ℝ) ^ 2 / 2 - S1) + (S1 - A * S2)) (A * (S2 - c * (N : ℝ) ^ 2))
    have t2 := abs_add_le ((N : ℝ) ^ 2 / 2 - S1) (S1 - A * S2)
    have t3 : |(N : ℝ) ^ 2 / 2 - S1| ≤ ε * (N : ℝ) ^ 2 := by rw [abs_sub_comm]; exact hS1
    have t4 : |A * (S2 - c * (N : ℝ) ^ 2)| ≤ |A| * (ε * (N : ℝ) ^ 2) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hS2 (abs_nonneg A)
    have t5 : ε * S2 ≤ ε * ((c + 1) * (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hS2le hε.le
    have t6 : ε * (4 + |A| + c) = η / 4 := by
      rw [hεdef]; field_simp
    have t7 : ε * (4 + |A| + c) * (N : ℝ) ^ 2 = η / 4 * (N : ℝ) ^ 2 := by rw [t6]
    nlinarith [abs_nonneg A]
  exact le_of_mul_le_mul_right hbound hN2

/-- The printed (4.23) reads `A = 2 C₂ = ∏_{ϖ ≥ 3} (1 - 1/(ϖ-1)²)`; the second equality is a misprint,
since the product is `C₂` itself, (4.12), and `2 C₂ ≠ C₂` as `C₂ > 0`. F-5028, cosmetic. -/
theorem printed_423_false : 2 * Cr 2 ≠ Cr 2 := by
  have := Cr2_pos; intro h; linarith

end LeanLab.HardyLittlewood1923

