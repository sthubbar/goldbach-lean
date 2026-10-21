module

public import LeanLab.SchnirelmannExplicit.Sharper4

/-!
Explicit Schnirelmann constant, fifth sharpening, unit U-0312, I-0063.
Every integer `n ≥ 2` is a sum of at most `H₅ = 97246` primes, down from `H₄ = 10752072` in
Sharper4.lean, a factor of about 110.
The change is in the sieve input. S1u is claimed only for `N ≥ N₂ = 3^10000`, where the Selberg
level `z = N / log^9 N` makes the remainder `z (1 + log z)^6 + 2(z + 1)` negligible and
`log z ≥ 0.9856 log N`, so the constant drops from 347 to 33, against 32 in the limit. Every
`n < N₂` is then handled by the elementary floor `#(G ∩ [1, n]) ≥ π(n - 2)`, the sums `p + 2`, with
Chebyshev's `π s ≥ 0.69 s / log s`; this beats `α n` because `log n ≤ 10000 log 3` there and
`α ≈ 2.06 · 10^-5` is still small.
S2 with `2.52`, the all-pairs first moment and Dyson's basis step are as in Sharper3 and
Sharper4. No cited input, unconditional.
KNOWN mathematics and far weaker than the literature, Klimov 55, Vaughan 27, Riesel-Vaughan 19,
Ramaré 7. Goldbach itself is open.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1302Z-30907. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit.Sharper5

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.SchnirelmannExplicit.DysonBasis LeanLab.SchnirelmannExplicit.Sharper3
open LeanLab.SchnirelmannExplicit.Sharper4

/-- The new threshold for the sieve bound. -/
irreducible_def N₂ : ℕ := 3 ^ 10000

lemma N₂_ge : 10 ^ 9 ≤ N₂ := by
  rw [N₂_def]
  calc 10 ^ 9 ≤ 3 ^ 19 := by norm_num
    _ ≤ 3 ^ 10000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

lemma one_lt_log3 : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma log3_lt : Real.log 3 < 1.3863 := by
  have h4 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

lemma N₂_cast : (N₂ : ℝ) = (3 : ℝ) ^ 10000 := by
  rw [N₂_def, Nat.cast_pow]; norm_num

lemma N₂_pos : (0 : ℝ) < N₂ := by rw [N₂_cast]; positivity

lemma log_N₂ : Real.log (N₂ : ℝ) = 10000 * Real.log 3 := by
  rw [N₂_cast, Real.log_pow]; norm_num

lemma log_ge_of_ge (N : ℕ) (hN : N₂ ≤ N) : 10000 ≤ Real.log N := by
  have hpos : (0 : ℝ) < N₂ := N₂_pos
  have hle : (N₂ : ℝ) ≤ N := by exact_mod_cast hN
  have := Real.log_le_log hpos hle
  rw [log_N₂] at this
  nlinarith [one_lt_log3]

lemma log_le_of_lt (n : ℕ) (hn : n < N₂) (h1 : 1 ≤ n) : Real.log n ≤ 13863 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hle : (n : ℝ) ≤ N₂ := by exact_mod_cast hn.le
  have := Real.log_le_log hpos hle
  rw [log_N₂] at this
  nlinarith [log3_lt]

/-- `log u ≤ u/1000 + 6`. -/
lemma log_le_u (u : ℝ) (hu : 0 < u) : Real.log u ≤ u / 1000 + 6 := by
  have h1 : Real.log (u / 1000) ≤ u / 1000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hu.ne' (by norm_num)] at h1
  have h3 : Real.log (1000 : ℝ) ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact exp7_ge
  linarith

lemma pow6_le (u : ℝ) (hu : 10000 ≤ u) : (1 + u) ^ 6 + 4 ≤ 2 * u ^ 6 := by
  have h1 : 1 + u ≤ 1.0001 * u := by linarith
  have h2 : (1 + u) ^ 6 ≤ (1.0001 * u) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
  have h3 : (1.0001 * u) ^ 6 = 1.0001 ^ 6 * u ^ 6 := by ring
  have hu6 : (10000 : ℝ) ^ 6 ≤ u ^ 6 := pow_le_pow_left₀ (by norm_num) hu 6
  have h4 : (1.0001 : ℝ) ^ 6 ≤ 1.001 := by norm_num
  nlinarith

set_option maxHeartbeats 1000000 in
open LeanLab.SchnirelmannGoldbach.S1 in
/-- **S1u, for huge `N`.** For `N ≥ N₂ = 3^10000` and `1 ≤ n ≤ N`,
`r n ≤ 33 N / log² N · singProd n`. Sieve level `z = N / log^9 N`. -/
theorem S1u_huge : ∀ N : ℕ, N₂ ≤ N → ∀ n ∈ Icc 1 N,
    (r n : ℝ) ≤ 33 * N / (Real.log N) ^ 2 * singProd n := by
  intro N hN n hn
  simp only [mem_Icc] at hn
  have hu := log_ge_of_ge N hN
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (le_trans (by norm_num) N₂_ge) hN
    exact_mod_cast this
  clear hN
  have hNpos : (0 : ℝ) < N := by linarith
  set u := Real.log N with hu_def
  have hupos : 0 < u := by linarith
  have hsp := one_le_singProd n
  have hexpu : Real.exp u = N := Real.exp_log hNpos
  have hNl : (N : ℝ) / u ^ 2 ≥ 1 / 4 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [log_sq_le N hN1]
  by_cases hev : Even n ∧ 4 ≤ n
  · obtain ⟨hev, hn4⟩ := hev
    have hlu := log_le_u u hupos
    set w := u - 9 * Real.log u with hw
    have hw_ge : 0.9856 * u ≤ w := by
      have hw' : w = u - 9 * Real.log u := hw
      linarith
    have hwpos : 0 < w := by linarith
    set z := Real.exp w with hz
    have hz1 : 1 < z := by rw [hz]; exact Real.one_lt_exp_iff.mpr hwpos
    have hrz := r_le_of_even hev (by omega) hz1
    have hlogz : Real.log z = w := Real.log_exp _
    rw [hlogz] at hrz
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    -- z = N / u^9
    have hz_eq : z * u ^ 9 = N := by
      rw [hz, hw, Real.exp_sub, ← hexpu]
      have : Real.exp (9 * Real.log u) = u ^ 9 := by
        rw [show (9 : ℝ) * Real.log u = ((9 : ℕ) : ℝ) * Real.log u by norm_num,
          Real.exp_nat_mul, Real.exp_log hupos]
      rw [this]
      field_simp
    have hzpos : 0 < z := by positivity
    -- main term
    have hmain : 32 * n * singProd n / w ^ 2 ≤ 32.95 * (N / u ^ 2 * singProd n) := by
      have hw2 : (0.9856 * u) ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by positivity) hw_ge 2
      have hs0 : 0 ≤ singProd n := by linarith
      have hnum : 32 * n * singProd n ≤ 32 * N * singProd n := by
        have := mul_le_mul_of_nonneg_right hnN hs0
        nlinarith
      have step1 : 32 * n * singProd n / w ^ 2 ≤ 32 * N * singProd n / (0.9856 * u) ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hw2
      have e : 32 * N * singProd n / (0.9856 * u) ^ 2 =
          (32 / 0.9856 ^ 2) * (N / u ^ 2 * singProd n) := by
        field_simp
      have hc : (32 / 0.9856 ^ 2 : ℝ) ≤ 32.95 := by norm_num
      have hpos : 0 ≤ N / u ^ 2 * singProd n := by positivity
      rw [e] at step1
      exact step1.trans (mul_le_mul_of_nonneg_right hc hpos)
    -- error term
    have herr : z * (1 + w) ^ 6 + 2 * (z + 1) ≤ 0.05 * (N / u ^ 2 * singProd n) := by
      have hwu : w ≤ u := by
        have : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
        linarith
      have h1 : (1 + w) ^ 6 ≤ (1 + u) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      have h2 := pow6_le u hu
      have h3 : z * (1 + w) ^ 6 + 2 * (z + 1) ≤ z * ((1 + u) ^ 6 + 4) := by nlinarith
      have h4 : z * ((1 + u) ^ 6 + 4) ≤ z * (2 * u ^ 6) := mul_le_mul_of_nonneg_left h2 hzpos.le
      have h5 : z * (2 * u ^ 6) * u ^ 3 = 2 * N := by rw [← hz_eq]; ring
      have hu3 : (10000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
      have h6 : z * (2 * u ^ 6) ≤ 0.05 * (N / u ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        have hX : 0 ≤ z * (2 * u ^ 6) * u ^ 2 := by positivity
        have hXu : z * (2 * u ^ 6) * u ^ 2 * u = 2 * N := by rw [← h5]; ring
        have := mul_le_mul_of_nonneg_left hu hX
        linarith
      have h7 : 0.05 * (N / u ^ 2) ≤ 0.05 * (N / u ^ 2 * singProd n) := by
        have h0 : 0 ≤ N / u ^ 2 := by positivity
        have := le_mul_of_one_le_right h0 hsp
        linarith
      linarith
    calc (r n : ℝ) ≤ 32.95 * (N / u ^ 2 * singProd n) + 0.05 * (N / u ^ 2 * singProd n) := by
          linarith
      _ = 33 * N / u ^ 2 * singProd n := by ring
  · have h3 : (r n : ℝ) ≤ 3 := by exact_mod_cast r_le_three_of_not hev
    have : (3 : ℝ) ≤ 33 * (N / u ^ 2 * singProd n) := by nlinarith
    calc (r n : ℝ) ≤ 33 * (N / u ^ 2 * singProd n) := by linarith
      _ = 33 * N / u ^ 2 * singProd n := by ring

/-- **S3 with the all-pairs first moment, general sieve constant.** -/
theorem S3_gen (C : ℝ) (hC0 : 0 < C) (N₁ : ℕ) (hN₁ : 10 ^ 9 ≤ N₁)
    (hC : ∀ N : ℕ, N₁ ≤ N → ∀ n ∈ Icc 1 N,
      (r n : ℝ) ≤ C * N / (Real.log N) ^ 2 * singProd n) :
    ∀ N ≥ N₁, (499 / 1000 : ℝ) ^ 2 * (69 / 100) ^ 4 / (C ^ 2 * 2.52) * N ≤
      #{n ∈ Icc 1 N | n ∈ G} := by
  intro N hN
  have hNR : (10 ^ 9 : ℝ) ≤ N := by exact_mod_cast le_trans hN₁ hN
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hLlin : L ≤ 18 + N / 100000000 := log_le_lin N hNpos
  set c : ℝ := 69 / 100
  set β : ℝ := 499 / 1000
  have hfm := first_moment c (by norm_num) (10 ^ 4) N (by norm_num) (by omega) pi_lower_069
  push_cast at hfm
  have hfm' : c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - 10000 * N) - 10000 * N) ≤
      ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by push_cast; exact hfm
  have hS1 : β * c ^ 2 * N ^ 2 / L ^ 2 ≤ ((∑ n ∈ Icc 1 N, r n : ℕ) : ℝ) := by
    refine le_trans ?_ hfm'
    rw [div_le_iff₀ (by positivity)]
    have e : c / L * (c / L * ((N : ℝ) * (N - 1) / 2 - 10000 * N) - 10000 * N) * L ^ 2 =
        c ^ 2 * ((N : ℝ) * (N - 1) / 2 - 10000 * N) - c * 10000 * N * L := by
      field_simp
    rw [e]
    have hkey : c * 10000 * L ≤ c ^ 2 * ((1 / 2 - β) * N - 1 / 2 - 10000) := by
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

/-- **S4 with the floor `π(n - 2)`.** If `α N ≤ #(G ∩ [1, N])` for `N ≥ N₁`, `log n ≤ Λ` for
`n < N₁`, `α (10^4 + 2) ≤ 1` and `α Λ ≤ 0.6898`, then `σ({0, 1} ∪ G) ≥ α`. -/
theorem S4_floor2 (α : ℝ) (hα : 0 ≤ α) (N₁ : ℕ) (Λ : ℝ)
    (hN : ∀ N ≥ N₁, α * N ≤ #{n ∈ Finset.Icc 1 N | n ∈ G})
    (hΛ : ∀ n : ℕ, n < N₁ → 1 ≤ n → Real.log n ≤ Λ)
    (hB : α * (10 ^ 4 + 2) ≤ 1) (hmid : α * Λ ≤ 0.6898) :
    α ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  rcases Nat.lt_or_ge n N₁ with hlt | hge
  · rcases Nat.lt_or_ge (10 ^ 4 + 2) n with hBn | hBn
    · set s := n - 2 with hs
      have h1 := card_ge_pi s n (by omega)
      have h1R : (Nat.primeCounting s : ℝ) ≤
          #{a ∈ Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by exact_mod_cast h1
      have hpi := pi_lower_069 s (by omega)
      have hsR : (10 ^ 4 + 1 : ℝ) ≤ s := by
        have : 10 ^ 4 + 1 ≤ s := by omega
        exact_mod_cast this
      have hsn : (s : ℝ) = n - 2 := by
        rw [hs]; push_cast [show 2 ≤ n by omega]; ring
      have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
      have hlogsn : Real.log s ≤ Real.log n :=
        Real.log_le_log (by linarith) (by rw [hsn]; linarith)
      have hlogΛ : Real.log s ≤ Λ := hlogsn.trans (hΛ n hlt (by omega))
      have hΛpos : 0 < Λ := lt_of_lt_of_le hlogs hlogΛ
      have h2 : 0.69 * s / Λ ≤ 0.69 * s / Real.log s := by
        apply div_le_div_of_nonneg_left (by positivity) hlogs hlogΛ
      have h3 : α * n ≤ 0.69 * s / Λ := by
        rw [le_div_iff₀ hΛpos]
        have hnR' : (10 ^ 4 + 3 : ℝ) ≤ n := by
          have : 10 ^ 4 + 3 ≤ n := by omega
          exact_mod_cast this
        have : α * Λ * n ≤ 0.6898 * n := mul_le_mul_of_nonneg_right hmid hnR.le
        rw [hsn]
        nlinarith
      have h4 : (69 / 100 : ℝ) * s / Real.log s = 0.69 * s / Real.log s := by norm_num
      linarith [h4 ▸ hpi]
    · have h1 : (1 : ℝ) ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
        have : 1 ≤ #{a ∈ Finset.Ioc 0 n | a ∈ ({0, 1} ∪ G : Set ℕ)} := by
          apply Finset.card_pos.mpr
          exact ⟨1, by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hn⟩,
            Or.inl (Or.inr rfl)⟩⟩
        exact_mod_cast this
      have hnB : (n : ℝ) ≤ 10 ^ 4 + 2 := by exact_mod_cast hBn
      calc α * n ≤ α * (10 ^ 4 + 2) := by gcongr
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

/-- The new density constant, `β^2 c^4 / (C^2 D)` with `C = 33`. -/
noncomputable def α₅ : ℝ := (499 / 1000 : ℝ) ^ 2 * (69 / 100) ^ 4 / (33 ^ 2 * 2.52)

lemma α₅_pos : 0 < α₅ := by unfold α₅; positivity

lemma α₅_le_density : α₅ ≤ schnirelmannDensity ({0, 1} ∪ G : Set ℕ) := by
  apply S4_floor2 α₅ α₅_pos.le N₂ 13863
    (S3_gen 33 (by norm_num) N₂ N₂_ge S1u_huge) (fun n hn h1 => log_le_of_lt n hn h1)
  · norm_num [α₅]
  · norm_num [α₅]

/-- `K₅ = ⌈1 / α₅⌉`. -/
def K₅ : ℕ := 48622

lemma one_le_α₅_mul_K₅ : 1 ≤ α₅ * (K₅ : ℝ) := by
  norm_num [α₅, K₅]

/-- The new explicit Schnirelmann constant. -/
def H₅ : ℕ := 2 * K₅ + 2

lemma H₅_eq : H₅ = 97246 := by norm_num [H₅, K₅]

/-- **Schnirelmann's theorem, fifth explicit form.** Every integer `n ≥ 2` is a sum of at most
`H₅ = 97246` primes. Unconditional. -/
theorem schnirelmann_bounded_primes_H₅ :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₅, SumOfPrimes k n := by
  have hh : K₅ • ({0, 1} ∪ G : Set ℕ) = Set.univ :=
    nsmul_eq_univ_dyson ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₅
      (by convert α₅_le_density) K₅ one_le_α₅_mul_K₅
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₅], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₅], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ K₅ • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ K₅ (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₅; omega, hs⟩

/-- Against Sharper4: `110 H₅ < H₄`. -/
lemma H₅_lt_H₄ : 110 * H₅ < H₄ := by norm_num [H₅, K₅, H₄, K₄]

end LeanLab.SchnirelmannExplicit.Sharper5
