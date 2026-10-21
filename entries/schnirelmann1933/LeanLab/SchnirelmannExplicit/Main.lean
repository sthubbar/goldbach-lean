module

public import LeanLab.SchnirelmannExplicit.Basis
public import LeanLab.SchnirelmannExplicit.Constants
public import LeanLab.SchnirelmannGoldbach.FromDensity

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Schnirelmann's theorem with an explicit constant: every integer `n ≥ 2` is a sum of at most
`H₀ = 4 * K₀ + 2 = 245882948879790567862862086` primes (about 2.46 * 10^26). Explicit S3 and
S4 links, then the explicit basis theorem from Basis.lean.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit

open LeanLab.SchnirelmannGoldbach

/-- **S3, explicit.** From explicit S1u, S2 and Chebyshev constants, the Goldbach sums up to `N`
number at least `c^4 / (81 C^2 D) · N` for `N ≥ 2 m₀ + 6` (with `C, D` replaced by
`max C 1, max D 1`). Same proof as `S3_of_S1u_S2`. -/
theorem S3_explicit_of (C₀ D₀ c : ℝ) (hc : 0 < c) (m₀ : ℕ)
    (hC : ∀ N : ℕ, 3 ≤ N → ∀ n ∈ Icc 1 N,
      (r n : ℝ) ≤ C₀ * N / (Real.log N) ^ 2 * singProd n)
    (hD : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ D₀ * N)
    (hm : ∀ m : ℕ, m₀ ≤ m → c * m / Real.log m ≤ (Nat.primeCounting m : ℝ)) :
    ∀ N ≥ 2 * m₀ + 6, c ^ 4 / (81 * (max C₀ 1) ^ 2 * (max D₀ 1)) * N ≤
      #{n ∈ Icc 1 N | n ∈ G} := by
  set C := max C₀ 1
  set D := max D₀ 1
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  intro N hN
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
  have : c ^ 4 * N ^ 4 ≤ K * (C ^ 2 * D * N ^ 3) * 81 := by
    have := hcomb
    nlinarith [hL4]
  nlinarith [hN3, hNpos]

/-- **S4, explicit.** If Goldbach sums up to `N` number at least `c N` for `N ≥ N₀`, then
`σ({0, 1} ∪ G) ≥ min c (1 / (N₀ + 1))`. Same proof as `S4_of_S3`. -/
theorem S4_explicit (c : ℝ) (N₀ : ℕ)
    (hN : ∀ N ≥ N₀, c * N ≤ #{n ∈ Finset.Icc 1 N | n ∈ G}) :
    min c (1 / ((N₀ : ℝ) + 1)) ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  set δ : ℝ := min c (1 / ((N₀ : ℝ) + 1)) with hδ
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  rcases Nat.lt_or_ge n N₀ with hlt | hge
  · have h1 : (1 : ℝ) ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
      have : 1 ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
        apply Finset.card_pos.mpr
        exact ⟨1, by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hn⟩,
          Or.inl (Or.inr rfl)⟩⟩
      exact_mod_cast this
    have hnN : (n : ℝ) ≤ N₀ := by exact_mod_cast hlt.le
    calc δ * n ≤ (1 / ((N₀ : ℝ) + 1)) * n := by gcongr; exact min_le_right _ _
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
      _ ≤ _ := h1
  · have h := hN n hge
    have hsub : #{a ∈ Finset.Icc 1 n | a ∈ G} ≤
        #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
      apply Finset.card_le_card
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at ha ⊢
      exact ⟨⟨by omega, ha.1.2⟩, Or.inr ha.2⟩
    have hsubR : (#{a ∈ Finset.Icc 1 n | a ∈ G} : ℝ) ≤
        #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by exact_mod_cast hsub
    calc δ * n ≤ c * n := by gcongr; exact min_le_left _ _
      _ ≤ _ := h.trans hsubR

/-- **S3 with the concrete constants.** For `N ≥ 206`, at least
`(log 2 / 2)^4 / (81 · C1^2 · 9) · N` integers in `[1, N]` are Goldbach sums. -/
theorem S3_concrete : ∀ N ≥ 206,
    (Real.log 2 / 2) ^ 4 / (81 * C1 ^ 2 * 9) * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  have h := S3_explicit_of C1 9 (Real.log 2 / 2) (by positivity) 100
    S1u_explicit S2_explicit pi_lower_explicit
  have hC1 : max C1 1 = C1 := max_eq_left (by norm_num [C1])
  have h9 : max (9 : ℝ) 1 = 9 := by norm_num
  rw [hC1, h9] at h
  exact h

/-- A rational lower bound for the S3 density constant, using `log 2 > 0.6931471803`. -/
noncomputable def α₀ : ℝ := (6931471803 / 20000000000 : ℝ) ^ 4 / (81 * C1 ^ 2 * 9)

/-- `K₀ = ⌈1 / α₀⌉`. -/
def K₀ : ℕ := 61470737219947641965715521

/-- The explicit Schnirelmann constant. -/
def H₀ : ℕ := 4 * K₀ + 2

lemma H₀_eq : H₀ = 245882948879790567862862086 := by norm_num [H₀, K₀]

lemma α₀_le_density : α₀ ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  have h4 := S4_explicit _ 206 S3_concrete
  refine le_trans ?_ h4
  apply le_min
  · unfold α₀
    have hl2 := Real.log_two_gt_d9
    have hpos : (0 : ℝ) < 81 * C1 ^ 2 * 9 := by norm_num [C1]
    apply div_le_div_of_nonneg_right _ hpos.le
    apply pow_le_pow_left₀ (by norm_num)
    norm_num at hl2 ⊢
    linarith
  · norm_num [α₀, C1]

lemma one_le_α₀_mul_K₀ : 1 ≤ α₀ * (K₀ : ℝ) := by
  norm_num [α₀, C1, K₀]

/-- **Schnirelmann's theorem, explicit.** Every integer `n ≥ 2` is a sum of at most
`H₀ = 245882948879790567862862086` primes. -/
theorem schnirelmann_bounded_primes_explicit :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₀, SumOfPrimes k n := by
  have hh : (2 * K₀) • ({0, 1} ∪ G : Set ℕ) = Set.univ := by
    have := nsmul_eq_univ_of_le_density ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₀
      (by convert α₀_le_density) K₀ one_le_α₀_mul_K₀
    exact this
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₀], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₀], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ (2 * K₀) • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ (2 * K₀) (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₀; omega, hs⟩

/-- Corollary with a round constant: at most `3 · 10^26` primes suffice. -/
theorem schnirelmann_bounded_primes_explicit_round :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ 3 * 10 ^ 26, SumOfPrimes k n := by
  intro n hn
  obtain ⟨k, hk, hs⟩ := schnirelmann_bounded_primes_explicit n hn
  exact ⟨k, hk.trans (by rw [H₀_eq]; norm_num), hs⟩

end LeanLab.SchnirelmannExplicit
