module

public import LeanLab.PNTPort.BVMax.RenyiRem
public import LeanLab.PNTSieve.BrunBlocksRel

/-!
# Brun's block sieve on `{N - p}` with Bombieri-Vinogradov remainders

Unit U-5507, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics.

* `renyi_rem_family`: `renyi_rem` for any family `F ⊆ 2^P` of sets whose products lie below the
  level, the same proof with the truncation filter replaced by `F`;
* `renyi_blocks_lower`: for good blocks of odd primes not dividing `N` with `lev Bs` below the level,
  `S({N - p}, Ω) ≥ X (∏_Ω (1 - x_p) - eL) - 3^{#blocks} K N/(log N)^A`, `X = liD(N - 1)`,
  `x_p = 1/(p - 1)`. The input of Rényi's theorem with a fixed `K`, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset

theorem renyi_rem_family (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
    F ⊆ P.powerset →
    (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
    ∑ T ∈ F,
      |LeanLab.PNTSieve.Bonferroni.rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun N hN P hP F hF hTQ => ?_⟩
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
  have hrem : ∀ T ∈ F,
      |LeanLab.PNTSieve.Bonferroni.rem (goldbachSeq N) xDen (liD y) T| = E (∏ p ∈ T, p) := by
    intro T hT
    have hT : T ⊆ P ∧ True := ⟨mem_powerset.mp (hF hT), trivial⟩
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
  have hinj : ∀ T₁ ∈ F, ∀ T₂ ∈ F, ∏ p ∈ T₁, p = ∏ p ∈ T₂, p → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ he
    have h₁ : T₁ ⊆ P ∧ True := ⟨mem_powerset.mp (hF h₁), trivial⟩
    have h₂ : T₂ ⊆ P ∧ True := ⟨mem_powerset.mp (hF h₂), trivial⟩
    rw [← Nat.primeFactors_prod (fun p hp => (hP p (h₁.1 hp)).1),
      ← Nat.primeFactors_prod (fun p hp => (hP p (h₂.1 hp)).1), he]
  rw [← sum_image hinj]
  refine le_trans ?_ hbv
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
  intro d hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
  rw [mem_Icc]
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, hTQ T hT⟩
  have hT : T ⊆ P ∧ True := ⟨mem_powerset.mp (hF hT), trivial⟩
  exact prod_ne_zero_iff.mpr (fun p hp => (hP p (hT.1 hp)).1.ne_zero)


open LeanLab.PNTSieve.Bonferroni in
/-- **Brun's block sieve on `{N - p}`.** -/
theorem renyi_blocks_lower (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
    lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ →
    liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p) - eL xDen Bs) -
      3 ^ Bs.length * (K * N / Real.log N ^ A) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ) := by
  obtain ⟨B, hB, K, hK⟩ := renyi_rem_family A hA
  refine ⟨B, hB, K, fun N hN Bs hG hBs hlev => ?_⟩
  have hX : 0 ≤ liD ((N - 1 : ℕ) : ℝ) := by
    unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have h1 := blocks_main_level (goldbachSeq N) Bs hG xDen xDen_nonneg xDen_le_one _ hX
  have hP : ∀ p ∈ univB Bs, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p :=
    fun p hp => ⟨univB_prime Bs hG p hp, (hBs p hp).1, (hBs p hp).2⟩
  have h2 := hK N hN (univB Bs) hP ((univB Bs).powerset.filter (fun S => cL Bs S ≠ 0))
    (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      exact (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans hlev)
  have h3 : (0 : ℝ) ≤ 3 ^ Bs.length := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

lemma xDen_lt_one (p : ℕ) : xDen p < 1 := by
  unfold xDen; split_ifs with h
  · have : (3 : ℝ) ≤ p := by exact_mod_cast h
    rw [div_lt_one (by linarith)]; linarith
  · norm_num

open LeanLab.PNTSieve.Bonferroni in
/-- **Brun's block sieve on `{N - p}`, relative form**, unit U-5509: if `Σ ρ_B ≤ 1/10`,
`S({N - p}, Ω) ≥ X V (1 - 5 Σ ρ_B) - 3^{#blocks} K N/(log N)^A`. -/
theorem renyi_blocks_rel (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
    lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
    liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
      3 ^ Bs.length * (K * N / Real.log N ^ A) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ) := by
  obtain ⟨B, hB, K, hK⟩ := renyi_rem_family A hA
  refine ⟨B, hB, K, fun N hN Bs hG hBs hlev hρ => ?_⟩
  have hX : 0 ≤ liD ((N - 1 : ℕ) : ℝ) := by
    unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have h1 := blocks_main_rel (goldbachSeq N) Bs hG xDen xDen_nonneg xDen_lt_one _ hX hρ
  have hP : ∀ p ∈ univB Bs, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p :=
    fun p hp => ⟨univB_prime Bs hG p hp, (hBs p hp).1, (hBs p hp).2⟩
  have h2 := hK N hN (univB Bs) hP ((univB Bs).powerset.filter (fun S => cL Bs S ≠ 0))
    (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      exact (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans hlev)
  have h3 : (0 : ℝ) ≤ 3 ^ Bs.length := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

end LeanLab.PNTPort.BVMax

