module

public import LeanLab.DensityGoldbach.U1488Window

/-!
Unit U-1488, run 20261022T1603Z-23862. P0047 Alsetri and Shao 2024, Theorem 1.2.

Before: `alsetriShao_1_2_U1484 : GreenThm21Circle3 → AlsetriShao12`.

Alsetri-Shao Proposition 3.1 asks only for `‖f̂‖_p ≤ M` at ONE exponent `2 < p < 4` for
`0 ≤ f ≤ ν_b`. A weak type, or large spectrum, bound at any exponent `q < 4` gives this at
`p = (q + 4)/2` by an elementary dyadic summation, and the strong `L³` bound `Green66` gives the
weak type bound at `q = 3` by Chebyshev. So the cited input is shrunk to

* `GreenLargeSpec`: for some `0 < q < 4` and `K`, uniformly in large `z`, reduced `b` and large
  prime `N`, every `0 ≤ f ≤ ν_b` and every `δ > 0` have `#{r : |f̂(r)| ≥ δ} ≤ K δ^{-q}`.

Results:
* `largeSpec_of_green66 : Green66 → GreenLargeSpec`, and so `GreenThm21Circle3 → GreenLargeSpec`:
  the new input is implied by the old one.
* `green66p_of_largeSpec : GreenLargeSpec → ∃ p, 2 < p ∧ p < 4 ∧ Green66p p`, elementary.
* `alsetriShao_1_2_U1488 : GreenLargeSpec → AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1488
open LeanLab.DensityGoldbach.U1446

/-- **Large spectrum bound for the majorant class**, the remaining cited input: some exponent
`0 < q < 4` and constant `K` with `#{r ∈ Z_N : δ ≤ |f̂(r)|} ≤ K δ^{-q}` for all `δ > 0` and all
`0 ≤ f ≤ ν_b`, `W = z#` with `z` large, `b` reduced, `N` a large prime. -/
def GreenLargeSpec : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 4 ∧ ∃ K : ℝ, 0 < K ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z → ∀ b : ℕ,
    b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
      N.Prime → N₀ ≤ N → ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) →
        ∀ δ : ℝ, 0 < δ → ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ K * δ ^ (-q)

/-! ### Chebyshev: the strong `L³` bound gives the weak type bound -/

theorem largeSpec_of_green66 (H : Green66) : GreenLargeSpec := by
  obtain ⟨C, hC, z₁, hG⟩ := H
  refine ⟨3, by norm_num, by norm_num, C ^ (3 : ℝ), by positivity, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hG z hz b hb hcop
  refine ⟨N₀, fun N _ hNp hN f hf δ hδ => ?_⟩
  have hl := hN₀ N hNp hN f hf
  set s := ∑ r : ZMod N, ‖hatE N f r‖ ^ (3 : ℝ) with hs
  have hs0 : 0 ≤ s := sum_nonneg fun r _ => by positivity
  have hsC : s ≤ C ^ (3 : ℝ) := by
    have h1 : (s ^ (1 / (3 : ℝ))) ^ (3 : ℝ) ≤ C ^ (3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hl (by norm_num)
    rwa [← Real.rpow_mul hs0, show 1 / (3 : ℝ) * 3 = 1 by norm_num, Real.rpow_one] at h1
  set S := univ.filter (fun r : ZMod N => δ ≤ ‖hatE N f r‖)
  have hS : (S.card : ℝ) * δ ^ (3 : ℝ) ≤ s := by
    calc (S.card : ℝ) * δ ^ (3 : ℝ) = ∑ r ∈ S, δ ^ (3 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ S, ‖hatE N f r‖ ^ (3 : ℝ) := sum_le_sum fun r hr =>
          Real.rpow_le_rpow hδ.le (mem_filter.1 hr).2 (by norm_num)
      _ ≤ s := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => by positivity
  have hd : 0 < δ ^ (3 : ℝ) := by positivity
  rw [Real.rpow_neg hδ.le, ← div_eq_mul_inv, le_div_iff₀ hd]
  linarith

/-! ### Dyadic summation: a weak type bound below `p` gives the strong bound at `p` -/

lemma sup_of_spec {ι : Type*} [Fintype ι] (a : ι → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 0 < K)
    (hS : ∀ δ : ℝ, 0 < δ → ((univ.filter (fun i => δ ≤ a i)).card : ℝ) ≤ K * δ ^ (-q))
    (i : ι) : a i ≤ K ^ (1 / q) := by
  by_contra h
  push Not at h
  have hM : 0 < K ^ (1 / q) := by positivity
  have h1 := hS (a i) (hM.trans h)
  have hcard : (1 : ℝ) ≤ (univ.filter (fun j => a i ≤ a j)).card := by
    have : (univ.filter (fun j => a i ≤ a j)).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, le_rfl⟩⟩
    exact_mod_cast this.card_pos
  have h2 : (a i) ^ (-q) < (K ^ (1 / q)) ^ (-q) := Real.rpow_lt_rpow_of_neg hM h (by linarith)
  have h3 : (K ^ (1 / q)) ^ (-q) = K⁻¹ := by
    rw [← Real.rpow_mul hK.le, show 1 / q * -q = -1 by field_simp, Real.rpow_neg_one]
  have h4 : K * (a i) ^ (-q) < 1 := by
    calc K * (a i) ^ (-q) < K * K⁻¹ := by rw [← h3]; exact mul_lt_mul_of_pos_left h2 hK
      _ = 1 := mul_inv_cancel₀ hK.ne'
  linarith

lemma dyadic_alg (M K p q : ℝ) (hM : 0 < M) (j : ℕ) :
    (M * (1 / 2) ^ j) ^ p * (K * (M * (1 / 2) ^ (j + 1)) ^ (-q)) =
      K * 2 ^ q * M ^ (p - q) * ((1 / 2 : ℝ) ^ (p - q)) ^ j := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hu : (0 : ℝ) < (1 / 2) ^ j := by positivity
  have e0 : M * (1 / 2 : ℝ) ^ (j + 1) = M * (1 / 2) ^ j * (1 / 2) := by rw [pow_succ]; ring
  have e3 : ((1 : ℝ) / 2) ^ (-q) = 2 ^ q := by
    rw [Real.rpow_neg hh.le, Real.div_rpow zero_le_one zero_le_two, Real.one_rpow]; field_simp
  have e4 : (M * (1 / 2 : ℝ) ^ j * (1 / 2)) ^ (-q) = M ^ (-q) * ((1 / 2 : ℝ) ^ j) ^ (-q) * 2 ^ q := by
    rw [Real.mul_rpow (by positivity) hh.le, Real.mul_rpow hM.le hu.le, e3]
  have e5 : (M * (1 / 2 : ℝ) ^ j) ^ p = M ^ p * ((1 / 2 : ℝ) ^ j) ^ p :=
    Real.mul_rpow hM.le hu.le
  have e1 : M ^ (p - q) = M ^ p * M ^ (-q) := by rw [sub_eq_add_neg, Real.rpow_add hM]
  have e2 : ((1 / 2 : ℝ) ^ (p - q)) ^ j = ((1 / 2 : ℝ) ^ j) ^ p * ((1 / 2 : ℝ) ^ j) ^ (-q) := by
    rw [Real.rpow_pow_comm hh.le, sub_eq_add_neg, Real.rpow_add hu]
  rw [e0, e4, e5, e1, e2]
  ring

theorem dyadic_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (q p K : ℝ)
    (hq : 0 < q) (hqp : q < p) (hK : 0 < K)
    (hS : ∀ δ : ℝ, 0 < δ → ((univ.filter (fun i => δ ≤ a i)).card : ℝ) ≤ K * δ ^ (-q)) :
    ∑ i, a i ^ p ≤ 1 + K * 2 ^ q * (K ^ (1 / q)) ^ (p - q) / (1 - (1 / 2 : ℝ) ^ (p - q)) := by
  set M := K ^ (1 / q) with hMdef
  have hM : 0 < M := by positivity
  have hp : 0 < p := by linarith
  have hMa : ∀ i, a i ≤ M := sup_of_spec a q K hq hK hS
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  set ρ : ℝ := (1 / 2) ^ (p - q) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one hh.le (by norm_num) (by linarith)
  -- choose `J` with `|ι| (M 2^{-J})^p ≤ 1`
  set n := Fintype.card ι
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / ((n + 1) * M ^ p) by positivity)
    (show (1 / 2 : ℝ) ^ p < 1 from Real.rpow_lt_one hh.le (by norm_num) hp)
  have htail : (n : ℝ) * (M * (1 / 2) ^ J) ^ p ≤ 1 := by
    rw [Real.mul_rpow hM.le (by positivity), ← Real.rpow_pow_comm hh.le]
    have hMp : 0 < M ^ p := by positivity
    rw [lt_div_iff₀ (by positivity)] at hJ
    have : (n : ℝ) * (M ^ p * ((1 / 2) ^ p) ^ J) ≤ ((1 / 2) ^ p) ^ J * ((n + 1) * M ^ p) := by
      have : 0 ≤ ((1 / 2 : ℝ) ^ p) ^ J * M ^ p := by positivity
      nlinarith
    linarith
  set g : ℕ → ι → ℝ := fun j i => if M * (1 / 2) ^ (j + 1) < a i then (M * (1 / 2) ^ j) ^ p else 0
  have hg0 : ∀ j i, 0 ≤ g j i := fun j i => by
    simp only [g]; split_ifs
    · positivity
    · exact le_rfl
  -- pointwise
  have hpt : ∀ i, a i ^ p ≤ (M * (1 / 2) ^ J) ^ p + ∑ j ∈ range J, g j i := by
    intro i
    by_cases hsmall : a i ≤ M * (1 / 2) ^ J
    · have := Real.rpow_le_rpow (ha i) hsmall hp.le
      have : 0 ≤ ∑ j ∈ range J, g j i := sum_nonneg fun j _ => hg0 j i
      linarith
    · push Not at hsmall
      have hex : ∃ j, M * (1 / 2) ^ (j + 1) < a i := by
        rcases Nat.eq_zero_or_pos J with h0 | h0
        · subst h0; simp at hsmall; linarith [hMa i]
        · exact ⟨J - 1, by rwa [Nat.sub_add_cancel h0]⟩
      set j₀ := Nat.find hex
      have hj₀ : M * (1 / 2) ^ (j₀ + 1) < a i := Nat.find_spec hex
      have hj₀J : j₀ < J := by
        rcases Nat.eq_zero_or_pos J with h0 | h0
        · subst h0; simp at hsmall; linarith [hMa i]
        · have : j₀ ≤ J - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel h0])
          omega
      have hup : a i ≤ M * (1 / 2) ^ j₀ := by
        rcases Nat.eq_zero_or_pos j₀ with h0 | h0
        · rw [h0, pow_zero, mul_one]; exact hMa i
        · have hmin := Nat.find_min hex (show j₀ - 1 < j₀ by omega)
          push Not at hmin
          rwa [Nat.sub_add_cancel h0] at hmin
      have h1 : a i ^ p ≤ g j₀ i := by
        simp only [g]; rw [if_pos hj₀]; exact Real.rpow_le_rpow (ha i) hup hp.le
      have h2 : g j₀ i ≤ ∑ j ∈ range J, g j i :=
        single_le_sum (fun j _ => hg0 j i) (mem_range.2 hj₀J)
      have : 0 ≤ (M * (1 / 2) ^ J) ^ p := by positivity
      linarith
  -- sum over `i`
  have hsum : ∑ i, a i ^ p ≤ n * (M * (1 / 2) ^ J) ^ p + ∑ j ∈ range J, ∑ i, g j i := by
    calc ∑ i, a i ^ p ≤ ∑ i, ((M * (1 / 2) ^ J) ^ p + ∑ j ∈ range J, g j i) := sum_le_sum
          fun i _ => hpt i
      _ = n * (M * (1 / 2) ^ J) ^ p + ∑ j ∈ range J, ∑ i, g j i := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_comm]
  have hlev : ∀ j, ∑ i, g j i ≤ K * 2 ^ q * M ^ (p - q) * ρ ^ j := by
    intro j
    have hδ : 0 < M * (1 / 2) ^ (j + 1) := by positivity
    have hc := hS _ hδ
    have hsub : univ.filter (fun i => M * (1 / 2) ^ (j + 1) < a i) ⊆
        univ.filter (fun i => M * (1 / 2) ^ (j + 1) ≤ a i) := fun i hi => by
      simp only [mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.le⟩
    have hc' : ((univ.filter (fun i => M * (1 / 2) ^ (j + 1) < a i)).card : ℝ) ≤
        K * (M * (1 / 2) ^ (j + 1)) ^ (-q) := le_trans (by exact_mod_cast card_le_card hsub) hc
    have he : ∑ i, g j i = (M * (1 / 2) ^ j) ^ p *
        ((univ.filter (fun i => M * (1 / 2) ^ (j + 1) < a i)).card : ℝ) := by
      simp only [g]
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rw [he, ← dyadic_alg M K p q hM j]
    exact mul_le_mul_of_nonneg_left hc' (by positivity)
  have hgeom : ∑ j ∈ range J, ρ ^ j ≤ 1 / (1 - ρ) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hρ0 hρ1
    simpa using this
  have hK' : 0 ≤ K * 2 ^ q * M ^ (p - q) := by positivity
  calc ∑ i, a i ^ p ≤ n * (M * (1 / 2) ^ J) ^ p + ∑ j ∈ range J, ∑ i, g j i := hsum
    _ ≤ 1 + ∑ j ∈ range J, K * 2 ^ q * M ^ (p - q) * ρ ^ j := by
        have := sum_le_sum fun j (_ : j ∈ range J) => hlev j
        linarith
    _ = 1 + K * 2 ^ q * M ^ (p - q) * ∑ j ∈ range J, ρ ^ j := by rw [mul_sum]
    _ ≤ 1 + K * 2 ^ q * M ^ (p - q) * (1 / (1 - ρ)) := by
        have := mul_le_mul_of_nonneg_left hgeom hK'
        linarith
    _ = 1 + K * 2 ^ q * M ^ (p - q) / (1 - ρ) := by ring

theorem green66p_of_largeSpec (H : GreenLargeSpec) : ∃ p : ℝ, 2 < p ∧ p < 4 ∧ Green66p p := by
  obtain ⟨q, hq, hq4, K, hK, z₁, hG⟩ := H
  set p := (q + 4) / 2 with hp
  have hqp : q < p := by simp only [p]; linarith
  have hp0 : 0 < p := by linarith
  set B := 1 + K * 2 ^ q * (K ^ (1 / q)) ^ (p - q) / (1 - (1 / 2 : ℝ) ^ (p - q))
  have hρ1 : (1 / 2 : ℝ) ^ (p - q) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hB : 0 < B := by
    have : 0 < 1 - (1 / 2 : ℝ) ^ (p - q) := by linarith
    positivity
  refine ⟨p, by simp only [p]; linarith, by simp only [p]; linarith, B ^ (1 / p),
    by positivity, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hG z hz b hb hcop
  refine ⟨N₀, fun N _ hNp hN f hf => ?_⟩
  have hs := dyadic_sum (fun r => ‖hatE N f r‖) (fun r => norm_nonneg _) q p K hq hqp hK
    (hN₀ N hNp hN f hf)
  unfold lpHat
  exact Real.rpow_le_rpow (sum_nonneg fun r _ => by positivity) hs (by positivity)

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenLargeSpec` only. -/
theorem alsetriShao_1_2_U1488 (H : GreenLargeSpec) : AlsetriShao12 := by
  obtain ⟨p, hp2, hp4, h⟩ := green66p_of_largeSpec H
  exact alsetriShao_1_2_of_p p hp2 hp4 h

/-- The new input is implied by the old one: `GreenThm21Circle3 → GreenLargeSpec`. -/
theorem largeSpec_of_circle3 (H : LeanLab.DensityGoldbach.U1472.GreenThm21Circle3) :
    GreenLargeSpec :=
  largeSpec_of_green66 (LeanLab.DensityGoldbach.U1472.green66_of_circle H)

/-! ### Faithfulness tests -/

/-- Not trivially true: at `f = ν_b` the zero coefficient is `E ν_b`, so the spectrum at level
`δ = E ν_b` is nonempty whenever `E ν_b > 0`; the bound has real content at every level. -/
theorem nontrivial_Spec (N W b : ℕ) [NeZero N] (h : 0 < avg N (nuW W b N)) :
    1 ≤ (univ.filter (fun r => avg N (nuW W b N) ≤ ‖hatE N (nuW W b N) r‖)).card := by
  refine Finset.card_pos.2 ⟨0, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
  rw [hatE_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h]

/-- Vacuity: `f = 0` meets the hypotheses and has empty spectrum at every `δ > 0`. -/
theorem vacuity_Spec (N W b : ℕ) [NeZero N] (δ : ℝ) (hδ : 0 < δ) :
    (univ.filter (fun r => δ ≤ ‖hatE N (fun _ => (0 : ℝ)) r‖)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r _
  simp [hatE]
  exact hδ

end LeanLab.DensityGoldbach.U1488
