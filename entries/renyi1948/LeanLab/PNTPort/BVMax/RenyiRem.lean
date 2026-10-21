module

public import LeanLab.PNTPort.BVMax.RenyiCount
public import LeanLab.PNTPort.BVMax.RenyiPrep
public import LeanLab.PNTPort.BVMax.PrimesUncond
public import LeanLab.PNTSieve.BrunPure

/-!
# The remainder sum of Brun's pure sieve on `{N - p}`

Lab proof, unit U-5334, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

`renyi_rem`: for every `A > 0` there are `B > 0` and `K` such that for every `N ≥ 2`, every finset
`P` of primes `p ≥ 3` not dividing `N` and every `r` with `∏ T ≤ √N/(log N)^B` for all `T ⊆ P`,
`|T| ≤ r`: `Σ_{T ⊆ P, |T| ≤ r} |R_T| ≤ K N/(log N)^A`, where `R_T = #{m ∈ {N - p} : ∏T ∣ m} -
liD(N - 1) ∏_{p ∈ T} 1/(p - 1)` are the remainders of `Bonferroni.brun_pure_lower` with
`X = liD(N - 1)` and `x_p = 1/(p - 1)`. From `bvPi`, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset

/-- The densities `x_p = 1/(p - 1)` for `p ≥ 3`, `0` below. -/
noncomputable def xDen (p : ℕ) : ℝ := if 3 ≤ p then 1 / ((p : ℝ) - 1) else 0

theorem renyi_rem (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ r : ℕ,
    (∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
    ∑ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      |LeanLab.PNTSieve.Bonferroni.rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun N hN P hP r hTQ => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set Q := ⌊Real.sqrt N / Real.log N ^ B⌋₊ with hQ
  set y : ℝ := ((N - 1 : ℕ) : ℝ) with hy
  set a : ℕ → ℕ := fun d => if Nat.Coprime N d then N else 1 with ha
  have hacop : ∀ d, Nat.Coprime (a d) d := by
    intro d; simp only [ha]; split_ifs with h
    · exact h
    · exact Nat.coprime_one_left d
  have hbv := hK N hN2 a hacop (fun _ => y)
    (fun _ => ⟨Nat.cast_nonneg _, by rw [hy]; exact_mod_cast Nat.sub_le N 1⟩)
  set E : ℕ → ℝ := fun d => |piAP y d (a d) - liD y / d.totient| with hE
  -- each remainder is the Bombieri-Vinogradov error at d = ∏ T
  have hrem : ∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      |LeanLab.PNTSieve.Bonferroni.rem (goldbachSeq N) xDen (liD y) T| = E (∏ p ∈ T, p) := by
    intro T hT
    rw [mem_filter, mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => (hP p (hT.1 hp)).1
    have hTN : ∀ p ∈ T, p.Prime ∧ ¬ p ∣ N := fun p hp => ⟨(hP p (hT.1 hp)).1, (hP p (hT.1 hp)).2.1⟩
    have hcop : Nat.Coprime N (∏ p ∈ T, p) := (coprime_prod_primes T N hTN).symm
    have hx : ∏ p ∈ T, xDen p = 1 / ((∏ p ∈ T, p).totient : ℝ) := by
      rw [inv_totient_prod_primes T hTp]
      refine prod_congr rfl (fun p hp => ?_)
      simp only [xDen, if_pos (hP p (hT.1 hp)).2.2]
    have hpi : piAP y (∏ p ∈ T, p) (a (∏ p ∈ T, p)) = piN (N - 1) (∏ p ∈ T, p) N := by
      simp only [ha, if_pos hcop]; unfold piAP; rw [hy, Nat.floor_natCast]
    unfold LeanLab.PNTSieve.Bonferroni.rem LeanLab.PNTSieve.Bonferroni.cnt
    rw [card_dvd_goldbachSeq, hx, hE]
    simp only
    rw [hpi, mul_one_div]
  rw [sum_congr rfl hrem]
  -- reindex by d = ∏ T, injective on sets of primes
  have hinj : ∀ T₁ ∈ P.powerset.filter (fun T => T.card ≤ r),
      ∀ T₂ ∈ P.powerset.filter (fun T => T.card ≤ r), ∏ p ∈ T₁, p = ∏ p ∈ T₂, p → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ he
    rw [mem_filter, mem_powerset] at h₁ h₂
    rw [← Nat.primeFactors_prod (fun p hp => (hP p (h₁.1 hp)).1),
      ← Nat.primeFactors_prod (fun p hp => (hP p (h₂.1 hp)).1), he]
  rw [← sum_image hinj]
  refine le_trans ?_ hbv
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
  intro d hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
  rw [mem_Icc]
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, hTQ T hT⟩
  rw [mem_filter, mem_powerset] at hT
  exact prod_ne_zero_iff.mpr (fun p hp => (hP p (hT.1 hp)).1.ne_zero)

lemma xDen_nonneg (p : ℕ) : 0 ≤ xDen p := by
  unfold xDen; split_ifs with h
  · have : (3 : ℝ) ≤ p := by exact_mod_cast h
    exact div_nonneg zero_le_one (by linarith)
  · exact le_rfl

lemma xDen_le_one (p : ℕ) : xDen p ≤ 1 := by
  unfold xDen; split_ifs with h
  · have : (3 : ℝ) ≤ p := by exact_mod_cast h
    rw [div_le_one (by linarith)]; linarith
  · norm_num

/-- Brun's pure sieve on `{N - p}` with the Bombieri-Vinogradov remainders: for odd `r` below the
level, `S({N - p}, P) ≥ X ∏_P (1 - x_p) - X (Σ_P x_p)^{r+1}/(r+1)! - K N/(log N)^A`,
`X = liD(N - 1)`, `x_p = 1/(p - 1)`. -/
theorem renyi_sieve_lower (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ r : ℕ, Odd r →
    (∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
    liD ((N - 1 : ℕ) : ℝ) * ∏ p ∈ P, (1 - xDen p) -
      liD ((N - 1 : ℕ) : ℝ) * ((∑ p ∈ P, xDen p) ^ (r + 1) / (r + 1).factorial) -
      K * N / Real.log N ^ A ≤ (LeanLab.PNTSieve.Bonferroni.sifted (goldbachSeq N) P : ℝ) := by
  obtain ⟨B, hB, K, hK⟩ := renyi_rem A hA
  refine ⟨B, hB, K, fun N hN P hP r hr hTQ => ?_⟩
  have hX : 0 ≤ liD ((N - 1 : ℕ) : ℝ) := by
    unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have h1 := LeanLab.PNTSieve.Bonferroni.brun_pure_lower (goldbachSeq N) P
    (fun p hp => (hP p hp).1) xDen xDen_nonneg xDen_le_one _ hX hr
  have h2 := hK N hN P hP r hTQ
  linarith

end LeanLab.PNTPort.BVMax

