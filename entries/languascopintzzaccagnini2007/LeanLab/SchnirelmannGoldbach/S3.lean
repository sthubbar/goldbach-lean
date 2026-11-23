module

public import LeanLab.SchnirelmannGoldbach.Statements
public import LeanLab.SchnirelmannGoldbach.Chebyshev

/-!
S3 from a uniform sieve bound S1u, the mean square bound S2 and Chebyshev.
AI-written Lean code, Claude, 2026-10-16.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannGoldbach

/-- S1u, the uniform form of the sieve bound actually used: for `n ≤ N`,
`r n ≤ C N / log² N · singProd n`. -/
def S1u : Prop := ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → ∀ n ∈ Icc 1 N,
    (r n : ℝ) ≤ C * N / (Real.log N) ^ 2 * singProd n

/-- S2 as a proposition. -/
def S2 : Prop := ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ C * N

lemma singProd_nonneg (n : ℕ) : 0 ≤ singProd n :=
  Finset.prod_nonneg fun p _ => by positivity

/-- Lower bound for the first moment: pairs of primes up to `m` give sums up to `2m`. -/
lemma sum_r_ge (m N : ℕ) (hmN : 2 * m ≤ N) :
    (Nat.primeCounting m) ^ 2 ≤ ∑ n ∈ Icc 1 N, r n := by
  have hcard : Nat.primeCounting m = #(Nat.primesBelow (m + 1)) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [hcard, sq, ← Finset.card_product]
  unfold r
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun pq => ⟨pq.1 + pq.2, pq.1⟩)
  · intro pq hpq
    simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_primesBelow] at hpq
    obtain ⟨⟨h1, hp⟩, ⟨h2, hq⟩⟩ := hpq
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Icc, mem_filter, mem_range]
    refine ⟨⟨by have := hp.two_le; omega, by omega⟩, by have := hq.two_le; omega, hp, ?_⟩
    simpa using hq
  · intro a _ b _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : a.1 = b.1 := by simpa using h2
    ext
    · exact h2'
    · omega

lemma mem_G_of_r_pos {n : ℕ} (h : 0 < r n) : n ∈ G := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  simp only [mem_filter, mem_range] at hp
  exact ⟨p, n - p, hp.2.1, hp.2.2, by omega⟩

/-- Cauchy-Schwarz on the support of `r`. -/
lemma cauchy_schwarz_r (N : ℕ) :
    ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) ^ 2 ≤
      (#{n ∈ Icc 1 N | n ∈ G} : ℝ) * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := by
  set s := (Icc 1 N).filter (fun n => 0 < r n)
  have hs : ∑ n ∈ Icc 1 N, (r n : ℝ) = ∑ n ∈ s, (r n : ℝ) := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro n _
    split_ifs with h
    · rfl
    · simp [Nat.eq_zero_of_not_pos h]
  have hs2 : ∑ n ∈ s, ((r n : ℝ)) ^ 2 ≤ ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have hsub : #s ≤ #{n ∈ Icc 1 N | n ∈ G} := by
    apply Finset.card_le_card
    intro n hn; simp only [s, mem_filter] at hn ⊢; exact ⟨hn.1, mem_G_of_r_pos hn.2⟩
  have hsubR : (#s : ℝ) ≤ #{n ∈ Icc 1 N | n ∈ G} := by exact_mod_cast hsub
  push_cast
  rw [hs]
  calc (∑ n ∈ s, (r n : ℝ)) ^ 2 ≤ #s * ∑ n ∈ s, ((r n : ℝ)) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (#{n ∈ Icc 1 N | n ∈ G} : ℝ) * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := by
      gcongr

/-- **S3 from S1u and S2.** -/
theorem S3_of_S1u_S2 (h1 : S1u) (h2 : S2) : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  obtain ⟨C₀, hC⟩ := h1
  obtain ⟨D₀, hD⟩ := h2
  obtain ⟨c, hc, m₀, hm⟩ := pi_lower
  set C := max C₀ 1
  set D := max D₀ 1
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c ^ 4 / (81 * C ^ 2 * D), by positivity, 2 * m₀ + 6, fun N hN => ?_⟩
  set m := N / 2
  have hm2 : 2 * m ≤ N := Nat.mul_div_le N 2
  have hmge : m₀ ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hNR : (6 : ℝ) ≤ N := by exact_mod_cast (show 6 ≤ N by omega)
  have hmR : (N : ℝ) ≤ 3 * m := by
    have : N ≤ 3 * m := by omega
    exact_mod_cast this
  have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  set L := Real.log N
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogm_le : Real.log m ≤ L := Real.log_le_log (by linarith) (by
    have : m ≤ N := by omega
    exact_mod_cast this)
  -- first moment
  have hpi := hm m hmge
  have hR1 : ((Nat.primeCounting m : ℝ)) ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
    exact_mod_cast sum_r_ge m N hm2
  have hpiL : c * N / (3 * L) ≤ (Nat.primeCounting m : ℝ) := by
    refine le_trans ?_ hpi
    rw [div_le_div_iff₀ (by positivity) hlogm_pos]
    have : c * N * Real.log m ≤ c * (3 * m) * L := by
      have := mul_le_mul hmR hlogm_le hlogm_pos.le (by positivity)
      nlinarith
    linarith
  have hA : (c * N / (3 * L)) ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) :=
    le_trans (pow_le_pow_left₀ (by positivity) hpiL 2) hR1
  -- second moment
  have hR2 : ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * (D * N) := by
    have hpt : ∀ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := by
      intro n hn
      have h := hC N (by omega) n hn
      have h' : (r n : ℝ) ≤ C * N / L ^ 2 * singProd n := by
        refine h.trans ?_
        gcongr
        · exact singProd_nonneg n
        · exact le_max_left _ _
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h' 2
    calc ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2
        ≤ ∑ n ∈ Icc 1 N, (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := Finset.sum_le_sum hpt
      _ = (C * N / L ^ 2) ^ 2 * ∑ n ∈ Icc 1 N, singProd n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * N / L ^ 2) ^ 2 * (D * N) := by
          gcongr
          exact (hD N (by omega)).trans (by gcongr; exact le_max_left _ _)
  have hCS := cauchy_schwarz_r N
  set K : ℝ := ((#{n ∈ Icc 1 N | n ∈ G} : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := by positivity
  -- combine: (cN/3L)^4 ≤ K * (C N / L^2)^2 * D N
  have hcomb : ((c * N / (3 * L)) ^ 2) ^ 2 ≤ K * ((C * N / L ^ 2) ^ 2 * (D * N)) := by
    calc ((c * N / (3 * L)) ^ 2) ^ 2 ≤ (((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hA 2
      _ ≤ K * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := hCS
      _ ≤ K * ((C * N / L ^ 2) ^ 2 * (D * N)) := by gcongr
  have hNpos : (0 : ℝ) < N := by linarith
  have e1 : ((c * N / (3 * L)) ^ 2) ^ 2 = c ^ 4 * N ^ 4 / (81 * L ^ 4) := by
    field_simp; ring
  have e2 : K * ((C * N / L ^ 2) ^ 2 * (D * N)) = K * (C ^ 2 * D * N ^ 3) / L ^ 4 := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at hcomb
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hL4 : 0 < L ^ 4 := by positivity
  have hN3 : 0 < (N : ℝ) ^ 3 := by positivity
  -- hcomb : c^4 N^4 L^4 ≤ K C^2 D N^3 * 81 L^4
  have : c ^ 4 * N ^ 4 ≤ K * (C ^ 2 * D * N ^ 3) * 81 := by
    have := hcomb
    nlinarith [hL4]
  nlinarith [hN3, hNpos]

end LeanLab.SchnirelmannGoldbach
