module

public import LeanLab.PNTPort.BVMax.PrimesUncond

/-!
# The divisor analogue of binary Goldbach, `Σ_{p<N} τ(N - p)`, from Bombieri-Vinogradov

Lab proof, unit U-5303, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics:
the asymptotic `Σ_{p<N} τ(N - p) ~ c(N) N` is due to Linnik's dispersion method and, by
Bombieri-Vinogradov, Halberstam 1967; this file proves the lower bound half in main term form.

Binary Goldbach asks for `Σ_{p<N} Λ(N - p) > 0`. Replacing `Λ` by the divisor function `τ` gives a
binary problem the sieve can solve: `τ(N - p) ≥ #{d ≤ D : d ∣ N - p}`, and counting by `d` turns
the sum into `Σ_{d ≤ D} π(N - 1; d, N)`, which Bombieri-Vinogradov evaluates for `D` up to
`√N/(log N)^B`. Parity does not arise because `τ` is not a prime detector.

* `tauSum N = Σ_{p < N, p prime} τ(N - p)`;
* `sum_piN_le_tauSum`: `Σ_{d ≤ D, (d,N)=1} π(N - 1; d, N) ≤ tauSum N`, double counting;
* `tauSum_lower`: for every `A > 0` there are `B > 0` and `K` with
  `tauSum N ≥ liD(N - 1) Σ_{d ≤ √N/(log N)^B, (d,N)=1} 1/φ(d) - K N/(log N)^A` for every `N ≥ 2`,
  unconditional, from `bvPi`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real

/-- `Σ_{p < N, p prime} τ(N - p)`. -/
noncomputable def tauSum (N : ℕ) : ℝ :=
  ∑ p ∈ (range N).filter Nat.Prime, ((N - p).divisors.card : ℝ)

/-- Double counting: `Σ_{d ≤ D, (d,N)=1} π(N - 1; d, N) ≤ Σ_{p<N} τ(N - p)`. -/
lemma sum_piN_le_tauSum (N D : ℕ) :
    ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d N), piN (N - 1) d N ≤ tauSum N := by
  unfold piN tauSum
  have key : ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d N),
      ((Icc 1 (N - 1)).filter (fun n => n % d = N % d ∧ n.Prime)).card ≤
      ∑ p ∈ (range N).filter Nat.Prime, (N - p).divisors.card := by
    calc ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d N),
          ((Icc 1 (N - 1)).filter (fun n => n % d = N % d ∧ n.Prime)).card
        ≤ ∑ d ∈ Icc 1 D, (((range N).filter Nat.Prime).filter (fun p => d ∣ N - p)).card := by
          refine (sum_le_sum (fun d _ => card_le_card ?_)).trans
            (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _))
          intro n hn
          simp only [mem_filter, mem_Icc, mem_range] at hn ⊢
          refine ⟨⟨by omega, hn.2.2⟩, ?_⟩
          exact (Nat.modEq_iff_dvd' (by omega)).mp hn.2.1
      _ = ∑ p ∈ (range N).filter Nat.Prime, ((Icc 1 D).filter (fun d => d ∣ N - p)).card :=
          sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun d p => d ∣ N - p)
      _ ≤ ∑ p ∈ (range N).filter Nat.Prime, (N - p).divisors.card := by
          refine sum_le_sum (fun p hp => card_le_card ?_)
          intro d hd
          simp only [mem_filter, mem_range, mem_Icc] at hp hd
          exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this
  exact this

/-- The divisor analogue of binary Goldbach, lower bound in main term form, unconditional. -/
theorem tauSum_lower (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    liD ((N - 1 : ℕ) : ℝ) * ∑ d ∈ (Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
        (fun d => Nat.Coprime d N), (1 : ℝ) / d.totient - K * N / Real.log N ^ A ≤ tauSum N := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set y : ℝ := ((N - 1 : ℕ) : ℝ) with hy
  set Q := ⌊Real.sqrt N / Real.log N ^ B⌋₊ with hQ
  have hy0 : 0 ≤ y := Nat.cast_nonneg _
  have hyN : y ≤ N := by rw [hy]; exact_mod_cast Nat.sub_le N 1
  set a : ℕ → ℕ := fun d => if Nat.Coprime N d then N else 1 with ha
  have hacop : ∀ d, Nat.Coprime (a d) d := by
    intro d; simp only [ha]; split_ifs with h
    · exact h
    · exact Nat.coprime_one_left d
  have hbv := hK N hN2 a hacop (fun _ => y) (fun _ => ⟨hy0, hyN⟩)
  have hfl : ⌊y⌋₊ = N - 1 := by rw [hy]; exact Nat.floor_natCast _
  have hterm : ∀ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N),
      liD y * ((1 : ℝ) / d.totient) ≤ piN (N - 1) d N + |piAP y d (a d) - liD y / d.totient| := by
    intro d hd
    simp only [mem_filter] at hd
    have had : a d = N := by simp only [ha]; rw [if_pos hd.2.symm]
    have hp : piAP y d (a d) = piN (N - 1) d N := by rw [had]; unfold piAP; rw [hfl]
    rw [hp, mul_one_div]
    have := le_abs_self (liD y / d.totient - piN (N - 1) d N)
    rw [abs_sub_comm] at this
    linarith
  have h1 := sum_le_sum hterm
  rw [← mul_sum, sum_add_distrib] at h1
  have h2 : ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N),
      |piAP y d (a d) - liD y / d.totient| ≤ K * N / Real.log N ^ A :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)).trans hbv
  have h3 := sum_piN_le_tauSum N Q
  linarith

end LeanLab.PNTPort.BVMax

