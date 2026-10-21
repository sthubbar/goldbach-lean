module

public import LeanLab.SchnirelmannExplicit.Sharper5
public import LeanLab.ChebyshevExplicit.Psi30

/-!
Explicit Schnirelmann constant, sixth sharpening, unit U-5658, I-0063.
Every integer `n ≥ 2` is a sum of at most `H₆ = 30772` primes, down from `H₅ = 97246` in
Sharper5.lean, a factor of about 3.16.
The change is Chebyshev's constant in the first moment of S3 and in the floor: `c = 0.92` from
`ChebyshevExplicit.pi_ge_chebyshev30`, Chebyshev 1852, in place of Mathlib's `0.69`, so the density
`β² c⁴ / (C² D)` grows by `(0.92/0.69)⁴`. The first moment now starts at `m₀ = 10^5`; below
`10^5 + 3` the floor of Sharper5 with `0.69` is kept, and on `[10^5 + 3, N₂)` the floor
`π(N - 2) ≥ 0.92 (N - 2)/log(N - 2)` beats `α₆ N`, since `α₆ · 13863 < 0.91`.
S1u with constant 33 from `N₂ = 3^10000`, S2 with `2.52` and Dyson's basis step are as in
Sharper5.lean. No cited input, unconditional.
KNOWN mathematics and far weaker than the literature, Klimov 55, Vaughan 27, Riesel-Vaughan 19,
Ramaré 7. Goldbach itself is open.
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1515Z-cloud27. Checked only by the Lean
kernel.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit.Sharper6

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.SchnirelmannExplicit.DysonBasis LeanLab.SchnirelmannExplicit.Sharper3
open LeanLab.SchnirelmannExplicit.Sharper4 LeanLab.SchnirelmannExplicit.Sharper5

/-- Chebyshev, `π m ≥ 0.92 m / log m` for `m ≥ 10^5`, from `pi_ge_chebyshev30`. -/
theorem pi_lower_092 : ∀ m : ℕ, 10 ^ 5 ≤ m →
    (92 / 100 : ℝ) * m / Real.log m ≤ (Nat.primeCounting m : ℝ) := by
  intro m hm
  have h := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 m (by omega)
  have hmR : (10 ^ 5 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  -- `5 log m ≤ 0.0012 m`
  have hl : Real.log m ≤ m / 10000 + 9 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (m : ℝ) / 10000) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    have : Real.log 10000 ≤ 14 * Real.log 2 := by
      have h := Real.log_le_log (x := 10000) (y := (2 : ℝ) ^ 14) (by norm_num) (by norm_num)
      rw [Real.log_pow] at h; push_cast at h; exact h
    linarith [Real.log_two_lt_d9]
  refine le_trans ?_ h
  apply div_le_div_of_nonneg_right _ hlog.le
  nlinarith

/-- `log N ≤ 21 + N / 10^10`. -/
lemma log_le_lin10 (N : ℝ) (hN : 0 < N) : Real.log N ≤ 23 + N / 10000000000 := by
  have h1 := Real.log_le_sub_one_of_pos (x := N / 10000000000) (by positivity)
  rw [Real.log_div hN.ne' (by norm_num)] at h1
  have : Real.log 10000000000 ≤ 34 * Real.log 2 := by
    have h := Real.log_le_log (x := 10000000000) (y := (2 : ℝ) ^ 34) (by norm_num) (by norm_num)
    rw [Real.log_pow] at h; push_cast at h; exact h
  linarith [Real.log_two_lt_d9]

lemma N₂_ge10 : 10 ^ 10 ≤ N₂ := by
  rw [N₂_def]
  calc 10 ^ 10 ≤ 3 ^ 21 := by norm_num
    _ ≤ 3 ^ 10000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **S3 with the all-pairs first moment, general sieve constant.** -/
theorem S3_gen6 (C : ℝ) (hC0 : 0 < C) (N₁ : ℕ) (hN₁ : 10 ^ 10 ≤ N₁)
    (hC : ∀ N : ℕ, N₁ ≤ N → ∀ n ∈ Icc 1 N,
      (r n : ℝ) ≤ C * N / (Real.log N) ^ 2 * singProd n) :
    ∀ N ≥ N₁, (499 / 1000 : ℝ) ^ 2 * (92 / 100) ^ 4 / (C ^ 2 * 2.52) * N ≤
      #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  have hNR : (10 ^ 10 : ℝ) ≤ N := by exact_mod_cast le_trans hN₁ hN
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hLlin : L ≤ 23 + N / 10000000000 := log_le_lin10 N hNpos
  set c : ℝ := 92 / 100
  set β : ℝ := 499 / 1000
  have hfm := first_moment c (by norm_num) (10 ^ 5) N (by norm_num) (by omega) pi_lower_092
  push_cast at hfm
  have hfm' : c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - 100000 * N) - 100000 * N) ≤
      ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by push_cast; exact hfm
  have hS1 : β * c ^ 2 * N ^ 2 / L ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
    refine le_trans ?_ hfm'
    rw [div_le_iff₀ (by positivity)]
    have e : c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - 100000 * N) - 100000 * N) * L ^ 2 =
        c ^ 2 * ((N : ℝ) * (N - 1) / 2 - 100000 * N) - c * 100000 * N * L := by
      field_simp
    rw [e]
    have hkey : c * 100000 * L ≤ c ^ 2 * ((1 / 2 - β) * N - 1 / 2 - 100000) := by
      simp only [c, β]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hkey hNpos.le]
  have hR2 : ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * (2.52 * N) := by
    have hpt : ∀ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 ≤ (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := by
      intro n hn
      have h' : (r n : ℝ) ≤ C * N / L ^ 2 * singProd n := hC N hN n hn
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h' 2
    calc ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2
        ≤ ∑ n ∈ Icc 1 N, (C * N / L ^ 2) ^ 2 * singProd n ^ 2 := Finset.sum_le_sum hpt
      _ = (C * N / L ^ 2) ^ 2 * ∑ n ∈ Icc 1 N, singProd n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * N / L ^ 2) ^ 2 * (2.52 * N) := by
          gcongr
          exact S2_sharp N (by omega)
  have hCS := cauchy_schwarz_r N
  set K : ℝ := ((#{n ∈ Icc 1 N | n ∈ G} : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hcomb : (β * c ^ 2 * N ^ 2 / L ^ 2) ^ 2 ≤ K * ((C * N / L ^ 2) ^ 2 * (2.52 * N)) := by
    calc (β * c ^ 2 * N ^ 2 / L ^ 2) ^ 2 ≤ (((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hS1 2
      _ ≤ K * ∑ n ∈ Icc 1 N, ((r n : ℝ)) ^ 2 := hCS
      _ ≤ K * ((C * N / L ^ 2) ^ 2 * (2.52 * N)) := by gcongr
  have e1 : (β * c ^ 2 * N ^ 2 / L ^ 2) ^ 2 = β ^ 2 * c ^ 4 * N ^ 4 / L ^ 4 := by
    field_simp
  have e2 : K * ((C * N / L ^ 2) ^ 2 * (2.52 * N)) = K * (C ^ 2 * 2.52 * N ^ 3) / L ^ 4 := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at hcomb
  have hL4 : 0 < L ^ 4 := by positivity
  have hN3 : 0 < (N : ℝ) ^ 3 := by positivity
  have h' : β ^ 2 * c ^ 4 * N ^ 4 ≤ K * (C ^ 2 * 2.52 * N ^ 3) :=
    le_of_mul_le_mul_right hcomb hL4
  have h'' : β ^ 2 * c ^ 4 * N * N ^ 3 ≤ (K * (C ^ 2 * 2.52)) * N ^ 3 := by
    nlinarith
  have h3 : β ^ 2 * c ^ 4 * N ≤ K * (C ^ 2 * 2.52) := le_of_mul_le_mul_right h'' hN3
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  simp only [c, β] at h3
  linarith


/-- The primes `p ≤ B` give the Goldbach numbers `p + 2 ≤ n`. -/
lemma card_ge_pi_G (B n : ℕ) (hBn : B + 2 ≤ n) :
    Nat.primeCounting B ≤ #{a ∈ Icc 1 n | a ∈ G} := by
  have hcard : Nat.primeCounting B = #(Nat.primesBelow (B + 1)) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [hcard]
  apply Finset.card_le_card_of_injOn (fun p => p + 2)
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_coe, Nat.mem_primesBelow] at hp ⊢
    simp only [mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨p, 2, hp.2, Nat.prime_two, rfl⟩⟩
  · intro p _ q _ h
    simp only at h
    omega

/-- The new density constant, `β^2 c^4 / (C^2 D)` with `c = 0.92`, `C = 33`. -/
noncomputable def α₆ : ℝ := (499 / 1000 : ℝ) ^ 2 * (92 / 100) ^ 4 / (33 ^ 2 * 2.52)

lemma α₆_pos : 0 < α₆ := by unfold α₆; positivity

/-- `α₆ N ≤ #(G ∩ [1, N])` for every `N ≥ 10^5 + 3`. -/
theorem density_mid : ∀ N ≥ 10 ^ 5 + 3, α₆ * N ≤ #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  rcases Nat.lt_or_ge N N₂ with hlt | hge
  · set s := N - 2 with hs
    have h1 : (Nat.primeCounting s : ℝ) ≤ #{n ∈ Icc 1 N | n ∈ G} := by
      exact_mod_cast card_ge_pi_G s N (by omega)
    have hpi := pi_lower_092 s (by omega)
    have hsR : (10 ^ 5 + 1 : ℝ) ≤ s := by
      have : 10 ^ 5 + 1 ≤ s := by omega
      exact_mod_cast this
    have hsn : (s : ℝ) = N - 2 := by
      rw [hs]; push_cast [show 2 ≤ N by omega]; ring
    have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
    have hlogsN : Real.log s ≤ 13863 := log_le_of_lt s (by omega) (by omega)
    have h2 : (92 / 100 : ℝ) * s / 13863 ≤ (92 / 100 : ℝ) * s / Real.log s :=
      div_le_div_of_nonneg_left (by positivity) hlogs hlogsN
    have hα : α₆ * 13863 ≤ 0.91 := by norm_num [α₆]
    have hNR : (10 ^ 5 + 3 : ℝ) ≤ N := by exact_mod_cast hN
    have h3 : α₆ * N ≤ (92 / 100 : ℝ) * s / 13863 := by
      rw [le_div_iff₀ (by norm_num), hsn]
      have := mul_le_mul_of_nonneg_right hα (by linarith : (0 : ℝ) ≤ N)
      nlinarith [α₆_pos]
    linarith
  · exact S3_gen6 33 (by norm_num) N₂ N₂_ge10 S1u_huge N hge

lemma α₆_le_density : α₆ ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  apply S4_floor2 α₆ α₆_pos.le (10 ^ 5 + 3) 12 density_mid
  · intro n hn h1
    have hpos : (0 : ℝ) < n := by exact_mod_cast h1
    have hle : (n : ℝ) ≤ 10 ^ 5 + 3 := by exact_mod_cast hn.le
    calc Real.log n ≤ Real.log (10 ^ 5 + 3) := Real.log_le_log hpos hle
      _ ≤ 12 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (12 : ℝ)
        have h12 : (2.7182818283 : ℝ) ^ 12 ≤ Real.exp 12 := by
          have e := Real.exp_nat_mul 1 12
          rw [mul_one] at e
          rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, e]
          exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12
        linarith [show (10 ^ 5 + 3 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 by norm_num]
  · norm_num [α₆]
  · norm_num [α₆]

/-- `K₆ = ⌈1 / α₆⌉`. -/
def K₆ : ℕ := 15385

lemma one_le_α₆_mul_K₆ : 1 ≤ α₆ * (K₆ : ℝ) := by
  norm_num [α₆, K₆]

/-- The new explicit Schnirelmann constant. -/
def H₆ : ℕ := 2 * K₆ + 2

lemma H₆_eq : H₆ = 30772 := by norm_num [H₆, K₆]

/-- **Schnirelmann's theorem, sixth explicit form.** Every integer `n ≥ 2` is a sum of at most
`H₆ = 30772` primes. Unconditional, no cited input. -/
theorem schnirelmann_bounded_primes_H₆ :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₆, SumOfPrimes k n := by
  have hh : K₆ • ({0, 1} ∪ G : Set ℕ) = Set.univ :=
    nsmul_eq_univ_dyson ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₆
      (by convert α₆_le_density) K₆ one_le_α₆_mul_K₆
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₆], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₆], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ K₆ • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ K₆ (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₆; omega, hs⟩

/-- Against Sharper5: `3 H₆ < H₅`. -/
lemma H₆_lt_H₅ : 3 * H₆ < H₅ := by norm_num [H₆, K₆, H₅, K₅]

end LeanLab.SchnirelmannExplicit.Sharper6

