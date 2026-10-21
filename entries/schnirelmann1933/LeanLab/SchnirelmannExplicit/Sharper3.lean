module

public import LeanLab.SchnirelmannExplicit.S2Sharp
public import LeanLab.SchnirelmannExplicit.DysonBasis

/-!
Explicit Schnirelmann constant, third sharpening, unit U-0310, I-0063.
Every integer `n ≥ 2` is a sum of at most `H₃ = 42075180` primes, about `4.2 · 10^7`,
down from `H₂ = 12168431812` in DysonBasis.lean, a factor of about 289.
Three changes, each elementary:
* S2 with constant `2.52` in place of `9`, S2Sharp.lean.
* S3 with `N ≤ (2 + 10^-7) m` for `m = N/2` in place of `N ≤ 3m`, so `λ^4 ≈ 16` replaces `81`,
  and Chebyshev's constant `0.6931` for `m ≥ 10^7`, from Mathlib's `Chebyshev.pi_ge`, in place
  of `log 2 / 2`.
* S4 with the floor from the Goldbach sums `p + 2`, `π(10^5) ≥ 2800`, in place of `1/(N₁ + 1)`,
  which would otherwise have capped the density at about `1.7 · 10^-10`.
The sieve input S1u, constant 347 for `N ≥ 5.92 · 10^9`, is unchanged from Sharper.lean, and
the basis step is Dyson's, from DysonBasis.lean. No cited input, unconditional.
KNOWN mathematics; Ramaré 1995 gets 7 primes by much stronger analytic input. Goldbach itself
is open.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1302Z-30907. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit.Sharper3

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.SchnirelmannExplicit.DysonBasis

/-- **S3 with a general ratio.** As `S3_explicit_from`, but with `N ≤ (2 + 1/m₀) m` for
`m = N / 2`, so the factor `81 = 3^4` becomes `(2 + 1/m₀)^4`. -/
theorem S3_lam (C D c : ℝ) (hCpos : 0 < C) (hDpos : 0 < D) (hc : 0 < c) (m₀ N₁ : ℕ)
    (hm₀ : 3 ≤ m₀)
    (hC : ∀ N : ℕ, N₁ ≤ N → ∀ n ∈ Icc 1 N,
      (r n : ℝ) ≤ C * N / (Real.log N) ^ 2 * singProd n)
    (hD : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ D * N)
    (hm : ∀ m : ℕ, m₀ ≤ m → c * m / Real.log m ≤ (Nat.primeCounting m : ℝ)) :
    ∀ N ≥ 2 * m₀, N₁ ≤ N → c ^ 4 / ((2 + 1 / (m₀ : ℝ)) ^ 4 * C ^ 2 * D) * N ≤
      #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN hN₁
  set lam : ℝ := 2 + 1 / (m₀ : ℝ) with hlam
  have hm₀R : (3 : ℝ) ≤ m₀ := by exact_mod_cast hm₀
  have hlampos : 0 < lam := by positivity
  set m := N / 2
  have hm2 : 2 * m ≤ N := Nat.mul_div_le N 2
  have hmge : m₀ ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hNR : (6 : ℝ) ≤ N := by exact_mod_cast (show 6 ≤ N by omega)
  have hmR : (N : ℝ) ≤ lam * m := by
    have h1 : N ≤ 2 * m + 1 := by omega
    have h1R : (N : ℝ) ≤ 2 * m + 1 := by exact_mod_cast h1
    have hmm : (m₀ : ℝ) ≤ m := by exact_mod_cast hmge
    have h2 : (1 : ℝ) ≤ m / m₀ := by rw [le_div_iff₀ (by linarith)]; linarith
    calc (N : ℝ) ≤ 2 * m + 1 := h1R
      _ ≤ 2 * m + m / m₀ := by linarith
      _ = lam * m := by rw [hlam]; ring
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
  have hpiL : c * N / (lam * L) ≤ (Nat.primeCounting m : ℝ) := by
    refine le_trans ?_ hpi
    rw [div_le_div_iff₀ (by positivity) hlogm_pos]
    have : c * N * Real.log m ≤ c * (lam * m) * L := by
      have := mul_le_mul hmR hlogm_le hlogm_pos.le (by positivity)
      nlinarith
    linarith
  have hA : (c * N / (lam * L)) ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) :=
    le_trans (pow_le_pow_left₀ (by positivity) hpiL 2) hR1
  have hR2 : ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * (D * N) := by
    have hpt : ∀ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := by
      intro n hn
      have h' : (r n : ℝ) ≤ C * N / L ^ 2 * singProd n := hC N hN₁ n hn
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h' 2
    calc ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2
        ≤ ∑ n ∈ Icc 1 N, (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := Finset.sum_le_sum hpt
      _ = (C * N / L ^ 2) ^ 2 * ∑ n ∈ Icc 1 N, singProd n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * N / L ^ 2) ^ 2 * (D * N) := by
          gcongr
          exact hD N (by omega)
  have hCS := cauchy_schwarz_r N
  set K : ℝ := ((#{n ∈ Icc 1 N | n ∈ G} : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hcomb : ((c * N / (lam * L)) ^ 2) ^ 2 ≤ K * ((C * N / L ^ 2) ^ 2 * (D * N)) := by
    calc ((c * N / (lam * L)) ^ 2) ^ 2 ≤ (((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hA 2
      _ ≤ K * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := hCS
      _ ≤ K * ((C * N / L ^ 2) ^ 2 * (D * N)) := by gcongr
  have hNpos : (0 : ℝ) < N := by linarith
  have e1 : ((c * N / (lam * L)) ^ 2) ^ 2 = c ^ 4 * N ^ 4 / (lam ^ 4 * L ^ 4) := by
    field_simp
  have e2 : K * ((C * N / L ^ 2) ^ 2 * (D * N)) = K * (C ^ 2 * D * N ^ 3) / L ^ 4 := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at hcomb
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hL4 : 0 < L ^ 4 := by positivity
  have hN3 : 0 < (N : ℝ) ^ 3 := by positivity
  have : c ^ 4 * N ^ 4 ≤ K * (C ^ 2 * D * N ^ 3) * lam ^ 4 := by
    have h' : c ^ 4 * N ^ 4 * L ^ 4 ≤ K * (C ^ 2 * D * N ^ 3) * lam ^ 4 * L ^ 4 := by
      linarith
    exact le_of_mul_le_mul_right h' hL4
  nlinarith [hN3, hNpos]

lemma exp14_ge : (1000000 : ℝ) ≤ Real.exp 14 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 14 = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (1000000 : ℝ) ≤ 2.7182818283 ^ 14 := by norm_num
    _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) h.le 14

/-- **Chebyshev, sharp constant for large `m`.** `π m ≥ 0.6931 m / log m` for `m ≥ 10^7`,
from Mathlib's `Chebyshev.pi_ge`. -/
theorem pi_lower_sharp : ∀ m : ℕ, 10 ^ 7 ≤ m →
    (6931 / 10000 : ℝ) * m / Real.log m ≤ (Nat.primeCounting m : ℝ) := by
  intro m hm
  have hl2 := Real.log_two_gt_d9
  have hm' : (10 ^ 7 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  refine le_trans ?_ (Chebyshev.pi_ge m)
  apply div_le_div_of_nonneg_right _ hlogm.le
  have h1 : Real.log ((m + 1) / 1000000) ≤ (m + 1) / 1000000 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h6 : Real.log (1000000 : ℝ) ≤ 14 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact exp14_ge
  nlinarith

lemma exp12_ge : (100000 : ℝ) ≤ Real.exp 12 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (100000 : ℝ) ≤ 2.7182818283 ^ 12 := by norm_num
    _ ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h.le 12

/-- `π(10^5) ≥ 2800`, from the Chebyshev bound with constant `log 2 / 2`. -/
lemma pi_1e5 : (2800 : ℝ) ≤ Nat.primeCounting 100000 := by
  have h := pi_lower_explicit 100000 (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have hlog : Real.log (100000 : ℝ) ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact exp12_ge
  have hlogpos : 0 < Real.log (100000 : ℝ) := Real.log_pos (by norm_num)
  refine le_trans ?_ h
  push_cast
  rw [le_div_iff₀ hlogpos]
  nlinarith

/-- `π B` Goldbach sums `p + 2` lie in `(0, n]` once `B + 2 ≤ n`. -/
lemma card_ge_pi (B n : ℕ) (hBn : B + 2 ≤ n) :
    Nat.primeCounting B ≤ #{a ∈ Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
  have hcard : Nat.primeCounting B = #(Nat.primesBelow (B + 1)) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [hcard]
  apply Finset.card_le_card_of_injOn (fun p => p + 2)
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_coe, Nat.mem_primesBelow] at hp ⊢
    simp only [mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, Or.inr ⟨p, 2, hp.2, Nat.prime_two, rfl⟩⟩
  · intro p _ q _ h
    simp only at h
    omega

/-- **S4 with a prime floor.** If `α N ≤ #(G ∩ [1, N])` for `N ≥ N₁`, `α (B + 2) ≤ 1` and
`α N₁ ≤ π B`, then `σ({0, 1} ∪ G) ≥ α`. -/
theorem S4_floor (α : ℝ) (hα : 0 ≤ α) (N₁ B : ℕ)
    (hN : ∀ N ≥ N₁, α * N ≤ #{n ∈ Finset.Icc 1 N | n ∈ G})
    (hB : α * (B + 2) ≤ 1) (hmid : α * N₁ ≤ Nat.primeCounting B) :
    α ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  rcases Nat.lt_or_ge n N₁ with hlt | hge
  · rcases Nat.lt_or_ge (B + 2) n with hBn | hBn
    · have h1 := card_ge_pi B n hBn.le
      have h1R : (Nat.primeCounting B : ℝ) ≤
          #{a ∈ Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by exact_mod_cast h1
      have hnN : (n : ℝ) ≤ N₁ := by exact_mod_cast hlt.le
      calc α * n ≤ α * N₁ := by gcongr
        _ ≤ _ := hmid.trans h1R
    · have h1 : (1 : ℝ) ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
        have : 1 ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
          apply Finset.card_pos.mpr
          exact ⟨1, by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hn⟩,
            Or.inl (Or.inr rfl)⟩⟩
        exact_mod_cast this
      have hnB : (n : ℝ) ≤ B + 2 := by exact_mod_cast hBn
      calc α * n ≤ α * (B + 2) := by gcongr
        _ ≤ 1 := hB
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
    exact h.trans hsubR

/-- The new S3 density constant, `c^4 / (λ^4 C^2 D)` with `c = 0.6931`, `λ = 2 + 10^-7`,
`C = 347`, `D = 2.52`. -/
noncomputable def α₃ : ℝ :=
  (6931 / 10000 : ℝ) ^ 4 / ((2 + 1 / ((10 ^ 7 : ℕ) : ℝ)) ^ 4 * 347 ^ 2 * 2.52)

/-- **S3, third sharpening.** For `N ≥ N₁ = 5920000000`, at least `α₃ N` integers in `[1, N]`
are Goldbach sums, `α₃ ≈ 4.75 · 10^-8`. -/
theorem S3_sharp3 : ∀ N ≥ N₁, α₃ * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  exact S3_lam 347 2.52 (6931 / 10000) (by norm_num) (by norm_num) (by norm_num) (10 ^ 7) N₁
    (by norm_num) S1u_sharp S2_sharp pi_lower_sharp N (by unfold N₁ at hN; omega) hN

lemma α₃_pos : 0 < α₃ := by unfold α₃; positivity

lemma α₃_le_density : α₃ ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  apply S4_floor α₃ α₃_pos.le N₁ 100000 S3_sharp3
  · norm_num [α₃]
  · refine le_trans ?_ pi_1e5
    norm_num [α₃, N₁]

/-- `K₃ = ⌈1 / α₃⌉`. -/
def K₃ : ℕ := 21037589

lemma one_le_α₃_mul_K₃ : 1 ≤ α₃ * (K₃ : ℝ) := by
  norm_num [α₃, K₃]

/-- The new explicit Schnirelmann constant. -/
def H₃ : ℕ := 2 * K₃ + 2

lemma H₃_eq : H₃ = 42075180 := by norm_num [H₃, K₃]

/-- **Schnirelmann's theorem, third explicit form.** Every integer `n ≥ 2` is a sum of at most
`H₃ = 42075180` primes. Unconditional, with no placeholder proofs. -/
theorem schnirelmann_bounded_primes_H₃ :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₃, SumOfPrimes k n := by
  have hh : K₃ • ({0, 1} ∪ G : Set ℕ) = Set.univ :=
    nsmul_eq_univ_dyson ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₃
      (by convert α₃_le_density) K₃ one_le_α₃_mul_K₃
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₃], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₃], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ K₃ • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ K₃ (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₃; omega, hs⟩

/-- The new constant against the Dyson one: `H₃ · 289 < H₂`. -/
lemma H₃_lt_H₂ : H₃ * 289 < H₂ := by norm_num [H₃, K₃, H₂, K₁]

end LeanLab.SchnirelmannExplicit.Sharper3
