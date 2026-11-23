module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
The reduction of the explicit formula on P0045 pages 5 and 6.
The odd radical argument is kept separate from the analytic family selection.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-! Helpers for `explicit_formula_reduction481`. These are the proved steps of
`SPLIT_explicit_formula_reduction481`, repeated here as private lemmas because that file imports
this one. They do not use `indexed_zero_count481` or `gamma_pair_bound481`: the counting bound and
the Gamma pair bound enter only through the hypotheses of the target. -/

section explicit_formula_reduction_helpers

/-! ### A threshold helper for the assembly

`log X` eventually dominates any fixed height, so every zero of the box eventually sits in the
closed strip `1/2 ≤ re ≤ 1`; this is the only place where the height enters the strip. -/

private theorem lpz_efr_log_threshold481 (H : ℝ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 2 * H ≤ Real.log X := by
  have h : Filter.Tendsto (fun X : ℕ => Real.log X) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (h.eventually (Filter.eventually_ge_atTop (2 * H)))

/-! ### The steps of the reduction -/

/-- Page 5, the density estimate following display 8: the size of the zero family.
The family of Lemma 4.1 lists its zeros with multiplicity, so the number `K` of non-pole
members is at most the total analytic multiplicity of the listed zeros, and the density input
bounds that total in terms of the height alone. This is the counting step only: it asserts
nothing about the major arcs or about the singular series. -/
private theorem lpz_efr_zero_family_card_bound481 (hdensity : JutilaStatement481)
    (hcount : ∀ {K : ℕ} (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
      (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ P : ℝ, AdmissibleP131 X P →
      ∀ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
        (z 0).1 = 1 → (z 0).2.2 = 1 → (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) →
        (∀ w, (univ.filter (fun i => i ≠ 0 ∧ z i = w)).card ≤
          analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
        (K : ℝ) ≤ C₀ * Real.exp (4 * H) := by
  obtain ⟨C₀, hC₀, hdens⟩ := hdensity
  refine ⟨C₀, hC₀, fun H T hH hT => ?_⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → T ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by
    refine ⟨⌈(T + 1) ^ ((5 : ℝ) / 2)⌉₊ + 1, fun X hX => ?_⟩
    have hpos : (0 : ℝ) < T + 1 := by linarith
    have hM : (0 : ℝ) ≤ (T + 1) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hpos.le _
    have hXM : (T + 1) ^ ((5 : ℝ) / 2) ≤ (X : ℝ) := by
      have h1 : ⌈(T + 1) ^ ((5 : ℝ) / 2)⌉₊ ≤ X := by omega
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have h1 : ((T + 1) ^ ((5 : ℝ) / 2)) ^ ((2 : ℝ) / 5) ≤ (X : ℝ) ^ ((2 : ℝ) / 5) :=
      Real.rpow_le_rpow hM hXM (by norm_num)
    have h2 : ((T + 1) ^ ((5 : ℝ) / 2)) ^ ((2 : ℝ) / 5) = T + 1 := by
      rw [← Real.rpow_mul hpos.le]
      norm_num
    rw [h2] at h1
    linarith
  obtain ⟨X₂, hX₂⟩ := hdens H T hH hT
  refine ⟨max (max X₁ 2) X₂, fun X hX P hP => ?_⟩
  have hX1 : X₁ ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hX3 : X₂ ≤ X := by omega
  obtain ⟨hPlow, hPhigh⟩ := hP
  have hTP : T ≤ P := le_trans (hX₁ X hX1) hPlow
  have hPX : P ≤ Real.sqrt X := by
    refine le_trans hPhigh ?_
    have h1 : (X : ℝ) ^ ((41 : ℝ) / 100) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_le_rpow_left_iff (by exact_mod_cast (by omega : 1 < X))]
      norm_num
    rwa [Real.sqrt_eq_rpow]
  intro K z hz01 hz0s hbox hmult
  set F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :=
    (univ.erase (0 : Fin (K + 1))).image z with hF
  have hFbox : ∀ w ∈ F, w ∈ zeroBox481 X H T P := by
    intro w hw
    rw [hF] at hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact hbox i (Finset.mem_erase.mp hi).1
  have hdensF := hX₂ X hX3 P hTP hPX F hFbox
  have hcard_le : ∀ w, (univ.filter (fun i : Fin K => z i.succ = w)).card
      ≤ (univ.filter (fun i : Fin (K + 1) => i ≠ 0 ∧ z i = w)).card := by
    intro w
    calc (univ.filter (fun i : Fin K => z i.succ = w)).card
        = ((univ.filter (fun i : Fin K => z i.succ = w)).image
            (Fin.succ : Fin K → Fin (K + 1))).card :=
          (Finset.card_image_of_injective _ (Fin.succ_injective K)).symm
      _ ≤ (univ.filter (fun i : Fin (K + 1) => i ≠ 0 ∧ z i = w)).card := by
          refine Finset.card_le_card ?_
          intro b hb
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
          rw [Finset.mem_filter] at hi ⊢
          exact ⟨Finset.mem_univ _, Fin.succ_ne_zero i, hi.2⟩
  have hsub : (univ : Finset (Fin K)).image (fun i => z i.succ) ⊆ F := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    rw [hF]
    exact Finset.mem_image.mpr
      ⟨Fin.succ i, Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩, rfl⟩
  have hsum_le : ∑ w ∈ (univ : Finset (Fin K)).image (fun i => z i.succ),
        (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ)
      ≤ ∑ w ∈ F, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.cast_nonneg _)
  have hK := hcount (fun i : Fin K => z i.succ) (fun w => (hcard_le w).trans (hmult w))
  linarith

/-- `1 - 1/(m-1)^2` lies in `[0,1]` for `m ≥ 3`. -/
private lemma lpz_efr_factor_bounds481 {m : ℕ} (hm : 3 ≤ m) :
    0 ≤ 1 - 1 / ((m : ℝ) - 1) ^ 2 ∧ 1 - 1 / ((m : ℝ) - 1) ^ 2 ≤ 1 := by
  have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (2 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have h4 : (4 : ℝ) ≤ ((m : ℝ) - 1) ^ 2 := by nlinarith
  constructor
  · rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  · have h : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
    linarith

/-- The Euler product of `1 - 1/(m-1)^2` telescopes. -/
private lemma lpz_efr_telescope_prod481 (M : ℕ) (hM : 2 ≤ M) :
    ∏ m ∈ Icc 3 M, (1 - 1 / ((m : ℝ) - 1) ^ 2) = (M : ℝ) / (2 * ((M : ℝ) - 1)) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    have hM0' : (M : ℝ) - 1 ≠ 0 := by linarith
    push_cast
    rw [add_sub_cancel_right]
    field_simp
    ring

/-- The singular series factor dominates `1 - 1/(p-1)^2` at every prime. -/
private lemma lpz_efr_singF_ge_factor481 (n : ℕ) (p : {p : ℕ // p.Prime}) :
    1 - 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ singF n p := by
  obtain ⟨m, hm⟩ := p
  unfold singF
  split_ifs with h
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.two_le
    have hpos : 0 < (m : ℝ) - 1 := by linarith
    have hge : (1 : ℝ) ≤ (m : ℝ) / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ hpos]
      linarith
    have hnn : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_refl _

/-- At the prime two an even `n` gives the factor `2`. -/
private lemma lpz_efr_singF_two481 {n : ℕ} (h2 : 2 ∣ n) :
    singF n ⟨2, Nat.prime_two⟩ = 2 := by
  have h2' : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}).1 = 2 := rfl
  unfold singF
  rw [if_pos h2]
  norm_num

/-- Every finite subproduct of the singular series factors of an even `n` is at least `1/2`. -/
private lemma lpz_efr_prod_singF_ge_half481 {n : ℕ} (h2n : 2 ∣ n)
    (s : Finset {p : ℕ // p.Prime}) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ s, singF n p := by
  classical
  set T := s.erase ⟨2, Nat.prime_two⟩ with hT
  set M : ℕ := max 3 (∑ p ∈ s, p.1) with hM
  have hM3 : 3 ≤ M := le_max_left _ _
  have hstep1 : (1 / 2 : ℝ) ≤ ∏ m ∈ Icc 3 M, (1 - 1 / ((m : ℝ) - 1) ^ 2) := by
    rw [lpz_efr_telescope_prod481 M (by omega)]
    have hM3' : (2 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
      linarith
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hTsub : T.image (fun p : {p : ℕ // p.Prime} => (p.1 : ℕ)) ⊆ Icc 3 M := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    rw [hT, Finset.mem_erase] at hp
    obtain ⟨hp2, hps⟩ := hp
    have hp2' : p.1 ≠ 2 := fun h => hp2 (Subtype.ext h)
    have hpge : 3 ≤ p.1 := by
      have h2le : 2 ≤ p.1 := p.2.two_le
      omega
    have hle : p.1 ≤ ∑ q ∈ s, q.1 :=
      Finset.single_le_sum (f := fun q => q.1) (fun _ _ => Nat.zero_le _) hps
    exact Finset.mem_Icc.mpr ⟨hpge, le_trans hle (le_max_right _ _)⟩
  have hstep2 : ∏ m ∈ Icc 3 M, (1 - 1 / ((m : ℝ) - 1) ^ 2)
      ≤ ∏ m ∈ T.image (fun p : {p : ℕ // p.Prime} => (p.1 : ℕ)), (1 - 1 / ((m : ℝ) - 1) ^ 2) :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hTsub
      (fun m hm => (lpz_efr_factor_bounds481 (Finset.mem_Icc.mp hm).1).1)
      (fun m hm _ => (lpz_efr_factor_bounds481 (Finset.mem_Icc.mp hm).1).2)
  have hstep3 : ∏ m ∈ T.image (fun p : {p : ℕ // p.Prime} => (p.1 : ℕ)), (1 - 1 / ((m : ℝ) - 1) ^ 2)
      = ∏ p ∈ T, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    rw [Finset.prod_image]
    intro p _ q _ hpq
    exact Subtype.ext hpq
  have hstep4 : ∏ p ∈ T, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)
      ≤ ∏ p ∈ T, singF n p :=
    Finset.prod_le_prod₀
      (fun p hp => (lpz_efr_factor_bounds481 (Finset.mem_Icc.mp
        (hTsub (Finset.mem_image_of_mem (fun p : {p : ℕ // p.Prime} => (p.1 : ℕ)) hp))).1).1)
      (fun p _ => lpz_efr_singF_ge_factor481 n p)
  have hstep5 : ∏ p ∈ T, singF n p ≤ ∏ p ∈ s, singF n p := by
    by_cases hmem : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ s
    · have hins : s = insert ⟨2, Nat.prime_two⟩ T := by
        rw [hT, Finset.insert_erase hmem]
      rw [hins, Finset.prod_insert (Finset.notMem_erase _ _), lpz_efr_singF_two481 h2n]
      have h0 : 0 ≤ ∏ p ∈ T, singF n p := Finset.prod_nonneg (fun p _ => singF_nonneg131 n p)
      linarith
    · have : s = T := by rw [hT, Finset.erase_eq_of_notMem hmem]
      rw [this]
  calc (1 / 2 : ℝ) ≤ ∏ m ∈ Icc 3 M, (1 - 1 / ((m : ℝ) - 1) ^ 2) := hstep1
    _ ≤ ∏ m ∈ T.image (fun p : {p : ℕ // p.Prime} => (p.1 : ℕ)), (1 - 1 / ((m : ℝ) - 1) ^ 2) := hstep2
    _ = ∏ p ∈ T, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := hstep3
    _ ≤ ∏ p ∈ T, singF n p := hstep4
    _ ≤ ∏ p ∈ s, singF n p := hstep5

/-- Page 2, display 2: for even `n` the singular series is `2 c_0` times a product of
factors `(p - 1) / (p - 2)` over odd primes `p` dividing `n`, each at least one, so it is at least
the twin prime constant `2 c_0`, which is positive. Every member of the even window is even, so
this gives a uniform positive lower bound there. The page 6 paragraph before Corollary 4.2 states
no lower bound for the singular series; the earlier citation of that paragraph was wrong and is
corrected by architect U-1649. Only positivity, not any asymptotic, is used by the reduction. -/
private theorem lpz_efr_singular_series_lower481 :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (X n : ℕ), n ∈ evenJ131 X → s₀ ≤ Sing n := by
  refine ⟨1 / 2, by norm_num, fun X n hn => ?_⟩
  have hev : Even n := (Finset.mem_filter.mp hn).2.1
  have h2n : 2 ∣ n := even_iff_two_dvd.mp hev
  have hS : Sing n = ∏' p : {p : ℕ // p.Prime}, singF n p := rfl
  rw [hS]
  by_cases hm : Multipliable (fun p : {p : ℕ // p.Prime} => singF n p)
  · exact ge_of_tendsto' hm.hasProd (fun s => lpz_efr_prod_singF_ge_half481 h2n s)
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

/-- Page 6, the choice of the parameters: the height and the frequency cut-off can be
taken large enough that the uniform remainder of Lemma 4.1 is below `η s₀ / 2`, and then the
small parameter can be taken small enough that the off-diagonal contribution is below
`η s₀ / 2` as well. This is a real-variable existence statement with no number theory in it:
`exp (-c H)` and `T ^ (-1/2)` are made small, and then the factor
`(C₀ exp (4 H) + 2) ^ 2 π` is compensated by `ε`. -/
private theorem lpz_efr_absorption_constants481 (c B ε₀ s₀ C₀ η H₀ T₀ : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B) (hε₀ : 0 < ε₀) (hs₀ : 0 < s₀) (hC₀ : 0 ≤ C₀)
    (hη : 0 < η) :
    ∃ H T ε : ℝ, H₀ ≤ H ∧ 1 ≤ H ∧ T₀ ≤ T ∧ 1 ≤ T ∧ 0 < ε ∧ ε < ε₀ ∧
      2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T) ≤ η * s₀ / 2 ∧
      (C₀ * Real.exp (4 * H) + 2) ^ 2 * Real.pi * ε ≤ η * s₀ / 2 := by
  have hquarter : 0 < η * s₀ / 4 := by
    have h := mul_pos hη hs₀
    linarith
  have hhalf : 0 < η * s₀ / 2 := by
    have h := mul_pos hη hs₀
    linarith
  have hexpH : Filter.Tendsto (fun H : ℝ => Real.exp (-c * H)) Filter.atTop (nhds 0) := by
    have hcH : Filter.Tendsto (fun H : ℝ => c * H) Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos (f := fun H : ℝ => H) hc).mpr Filter.tendsto_id
    have h1 : Filter.Tendsto (fun H : ℝ => -(c * H)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atBot_iff.mpr hcH
    have h2 : Filter.Tendsto (fun H : ℝ => Real.exp (-(c * H))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa [neg_mul] using h2
  have hmulH : Filter.Tendsto (fun H : ℝ => 2 * B * Real.exp (-c * H)) Filter.atTop (nhds 0) := by
    have h := hexpH.const_mul (2 * B)
    simpa using h
  have hevH : ∀ᶠ H : ℝ in Filter.atTop, 2 * B * Real.exp (-c * H) ≤ η * s₀ / 4 :=
    hmulH.eventually (eventually_le_nhds hquarter)
  obtain ⟨H₁, hH₁⟩ := Filter.eventually_atTop.mp hevH
  have hinvT : Filter.Tendsto (fun T : ℝ => (Real.sqrt T)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hmulT : Filter.Tendsto (fun T : ℝ => 2 * B * (1 / Real.sqrt T)) Filter.atTop (nhds 0) := by
    have h := hinvT.const_mul (2 * B)
    simpa [one_div] using h
  have hevT : ∀ᶠ T : ℝ in Filter.atTop, 2 * B * (1 / Real.sqrt T) ≤ η * s₀ / 4 :=
    hmulT.eventually (eventually_le_nhds hquarter)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp hevT
  set H : ℝ := max (max H₀ 1) H₁ with hHH
  set T : ℝ := max (max T₀ 1) T₁ with hTT
  have hH₀ : H₀ ≤ H := by rw [hHH]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hH1 : 1 ≤ H := by rw [hHH]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hH₁le : H₁ ≤ H := by rw [hHH]; exact le_max_right _ _
  have hT₀ : T₀ ≤ T := by rw [hTT]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hT1 : 1 ≤ T := by rw [hTT]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hT₁le : T₁ ≤ T := by rw [hTT]; exact le_max_right _ _
  have hAbs : 2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T) ≤ η * s₀ / 2 := by
    have h1 : 2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)
        = 2 * B * Real.exp (-c * H) + 2 * B * (1 / Real.sqrt T) := by ring
    have h2 := hH₁ H hH₁le
    have h3 := hT₁ T hT₁le
    rw [h1]
    linarith
  set D : ℝ := (C₀ * Real.exp (4 * H) + 2) ^ 2 * Real.pi with hDD
  have hD0 : 0 ≤ D := by
    rw [hDD]
    exact mul_nonneg (sq_nonneg _) Real.pi_pos.le
  have hD1 : 0 < D + 1 := by linarith
  have hεpos : 0 < min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1))) := by
    refine lt_min ?_ ?_
    · linarith
    · exact div_pos hhalf (by linarith)
  have hεlt : min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1))) < ε₀ := by
    have h1 : min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1))) ≤ ε₀ / 2 := min_le_left _ _
    linarith
  have hεbound : D * min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1))) ≤ η * s₀ / 2 := by
    have hle : min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1)))
        ≤ (η * s₀ / 2) / (2 * (D + 1)) := min_le_right _ _
    have hstep : D * ((η * s₀ / 2) / (2 * (D + 1))) ≤ η * s₀ / 2 := by
      have hkey : D * ((η * s₀ / 2) / (2 * (D + 1)))
          = (D / (D + 1)) * (η * s₀ / 2 / 2) := by
        field_simp
      rw [hkey]
      have h1 : D / (D + 1) ≤ 1 := by
        rw [div_le_one hD1]
        linarith
      have h2 : 0 ≤ η * s₀ / 2 / 2 := by linarith
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      have h4 : 1 * (η * s₀ / 2 / 2) = η * s₀ / 2 / 2 := one_mul _
      rw [h4] at h3
      linarith
    calc D * min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1)))
        ≤ D * ((η * s₀ / 2) / (2 * (D + 1))) := mul_le_mul_of_nonneg_left hle hD0
      _ ≤ η * s₀ / 2 := hstep
  exact ⟨H, T, min (ε₀ / 2) (η * s₀ / 2 / (2 * (D + 1))),
    hH₀, hH1, hT₀, hT1, hεpos, hεlt, hAbs, hεbound⟩

/-- The algebraic core of the near diagonal estimate: the pole pair is worth exactly
`n * Sing n`; every other summand is at most `ε` in modulus and there are at most
`(K + 1) ^ 2 - 1` of them. -/
private theorem lpz_efr_main_term_core481 (K : ℕ) (f : Fin (K + 1) → Fin (K + 1) → ℂ) (n : ℕ) (ε s : ℝ)
    (hf00 : f 0 0 = (s : ℂ) * (n : ℂ))
    (hpair : ∀ i j : Fin (K + 1), (i ≠ 0 ∨ j ≠ 0) → ‖f i j‖ ≤ ε * (Real.pi * n))
    (hε : 0 ≤ ε) :
    |(∑ i, ∑ j, f i j).re - n * s| ≤ ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := by
  have hrow : ∀ i : Fin (K + 1), i ≠ 0 →
      ‖∑ j, f i j‖ ≤ ((K : ℝ) + 1) * (ε * (Real.pi * n)) := by
    intro i hi
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin (K + 1), ‖f i j‖
        ≤ ∑ _j : Fin (K + 1), ε * (Real.pi * n) :=
          Finset.sum_le_sum (fun j _ => hpair i j (Or.inl hi))
      _ = ((K : ℝ) + 1) * (ε * (Real.pi * n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hcard : (univ.erase (0 : Fin (K + 1))).card = K := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hrow0 : ‖∑ j ∈ univ.erase (0 : Fin (K + 1)), f 0 j‖ ≤
      ((K : ℝ)) * (ε * (Real.pi * n)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ univ.erase (0 : Fin (K + 1)), ‖f 0 j‖
        ≤ ∑ _j ∈ univ.erase (0 : Fin (K + 1)), ε * (Real.pi * n) :=
          Finset.sum_le_sum (fun j hj => hpair 0 j (Or.inr (Finset.mem_erase.mp hj).1))
      _ = ((K : ℝ)) * (ε * (Real.pi * n)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hrows : ‖∑ i ∈ univ.erase (0 : Fin (K + 1)), ∑ j, f i j‖ ≤
      ((K : ℝ)) * (((K : ℝ) + 1) * (ε * (Real.pi * n))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ univ.erase (0 : Fin (K + 1)), ‖∑ j, f i j‖
        ≤ ∑ _i ∈ univ.erase (0 : Fin (K + 1)), ((K : ℝ) + 1) * (ε * (Real.pi * n)) :=
          Finset.sum_le_sum (fun i hi => hrow i (Finset.mem_erase.mp hi).1)
      _ = ((K : ℝ)) * (((K : ℝ) + 1) * (ε * (Real.pi * n))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hdec : (∑ i, ∑ j, f i j) - (s : ℂ) * (n : ℂ)
      = (∑ j ∈ univ.erase (0 : Fin (K + 1)), f 0 j) +
        (∑ i ∈ univ.erase (0 : Fin (K + 1)), ∑ j, f i j) := by
    have h1 : (∑ i : Fin (K + 1), ∑ j, f i j)
        = (∑ j, f 0 j) + ∑ i ∈ univ.erase (0 : Fin (K + 1)), ∑ j, f i j := by
      rw [← Finset.add_sum_erase (univ : Finset (Fin (K + 1)))
        (fun i => ∑ j, f i j) (Finset.mem_univ 0)]
    have h2 : (∑ j : Fin (K + 1), f 0 j)
        = f 0 0 + ∑ j ∈ univ.erase (0 : Fin (K + 1)), f 0 j := by
      rw [← Finset.add_sum_erase (univ : Finset (Fin (K + 1)))
        (fun j => f 0 j) (Finset.mem_univ 0)]
    rw [h1, h2, hf00]
    ring
  have hbound : ‖(∑ i, ∑ j, f i j) - (s : ℂ) * (n : ℂ)‖ ≤
      ((K : ℝ)) * (ε * (Real.pi * n)) +
        ((K : ℝ)) * (((K : ℝ) + 1) * (ε * (Real.pi * n))) := by
    rw [hdec]
    exact (norm_add_le _ _).trans (add_le_add hrow0 hrows)
  have hre : (∑ i, ∑ j, f i j).re - (n : ℝ) * s
      = ((∑ i, ∑ j, f i j) - (s : ℂ) * (n : ℂ)).re := by
    rw [Complex.sub_re]
    have hC : ((s : ℂ) * (n : ℂ)).re = (n : ℝ) * s := by
      rw [Complex.mul_re]
      simp
      ring
    rw [hC]
  rw [hre]
  refine ((Complex.abs_re_le_norm _).trans hbound).trans ?_
  have hpos : 0 ≤ ε * (Real.pi * n) :=
    mul_nonneg hε (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n))
  have hEq : ((K : ℝ)) * (ε * (Real.pi * n)) +
      ((K : ℝ)) * (((K : ℝ) + 1) * (ε * (Real.pi * n)))
      = ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n - ε * (Real.pi * n) := by ring
  rw [hEq]
  linarith

/-- Page 5, Lemma 4.1: the finite zero sum for one integer `n`. The pole pair carries
the full main term `n * Sing n`, and every pair with at least one zero factor contributes at
most the small parameter. This is a single sum estimate: it has no exceptional set, no
counting and no uniformity in `X`. -/
private theorem lpz_efr_explicit_formula_main_term481 {K : ℕ}
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) (n : ℕ) (ε : ℝ)
    (hz0 : (z 0).2.2 = 1) (hSg00 : Sg 0 0 n = (Sing n : ℂ))
    (hγ : ∀ i j, ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n)
    (hε : 0 ≤ ε) (hSgε : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → ‖Sg i j n‖ ≤ ε) :
    |(∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n).re - n * Sing n| ≤
      ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := by
  have hgamma11 : gammaPair481 1 1 n = (n : ℂ) := by
    have hG2 : Complex.Gamma ((1 : ℂ) + 1) = 1 := by
      rw [Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, one_mul]
    have h3 : (1 : ℂ) + 1 - 1 = 1 := by norm_num
    unfold gammaPair481
    rw [hG2, h3, Complex.Gamma_one, Complex.cpow_one]
    norm_num
  have hsign : ∀ i : Fin (K + 1), ‖zeroSign481 i‖ = 1 := by
    intro i
    unfold zeroSign481
    split_ifs <;> simp
  refine lpz_efr_main_term_core481 K (fun i j => Sg i j n * zeroSign481 i * zeroSign481 j *
    gammaPair481 (z i).2.2 (z j).2.2 n) n ε (Sing n) ?_ ?_ hε
  · have h0s : zeroSign481 (0 : Fin (K + 1)) = 1 := by simp [zeroSign481]
    rw [hz0, hSg00, hgamma11, h0s]
    ring
  · intro i j hij
    have h1 : ‖Sg i j n‖ ≤ ε := hSgε i j hij
    have h2 : ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n := hγ i j
    rw [norm_mul, norm_mul, norm_mul, hsign i, hsign j, mul_one, mul_one]
    exact mul_le_mul h1 h2 (norm_nonneg _) hε

/-- Page 5, Lemma 4.1: the crude size of the same finite zero sum for one integer `n`,
with every pair counted at its uniform bound `Sing n` rather than at the small parameter.
This is the estimate that survives when the small-parameter clause is unavailable, so it
carries no exceptional set either. -/
private theorem lpz_efr_explicit_formula_total_size481 {K : ℕ}
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) (n : ℕ)
    (hγ : ∀ i j, ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n)
    (hSgb : ∀ i j, ‖Sg i j n‖ ≤ Sing n) (hS0 : 0 ≤ Sing n) :
    |(∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
      n * Sing n + ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by
  have hz : ∀ i : Fin (K + 1), ‖zeroSign481 i‖ = 1 := by
    intro i
    unfold zeroSign481
    split_ifs <;> simp
  have hterm : ∀ i j : Fin (K + 1),
      ‖Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Sing n * Real.pi * n := by
    intro i j
    rw [norm_mul, norm_mul, norm_mul, hz i, hz j, mul_one, mul_one]
    have h1 : ‖Sg i j n‖ ≤ Sing n := hSgb i j
    have h2 : ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n := hγ i j
    have hpi : 0 ≤ Real.pi * n := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    calc ‖Sg i j n‖ * ‖gammaPair481 (z i).2.2 (z j).2.2 n‖
        ≤ Sing n * (Real.pi * n) := mul_le_mul h1 h2 (norm_nonneg _) hS0
      _ = Sing n * Real.pi * n := by ring
  have hinner : ∀ i : Fin (K + 1),
      ‖∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ ((K : ℝ) + 1) * (Sing n * Real.pi * n) := by
    intro i
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin (K + 1), ‖Sg i j n * zeroSign481 i * zeroSign481 j *
          gammaPair481 (z i).2.2 (z j).2.2 n‖
        ≤ ∑ _j : Fin (K + 1), Sing n * Real.pi * n :=
          Finset.sum_le_sum (fun j _ => hterm i j)
      _ = ((K : ℝ) + 1) * (Sing n * Real.pi * n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hT : ‖∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤
      ((K : ℝ) + 1) * (((K : ℝ) + 1) * (Sing n * Real.pi * n)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin (K + 1), ‖∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
          gammaPair481 (z i).2.2 (z j).2.2 n‖
        ≤ ∑ _i : Fin (K + 1), ((K : ℝ) + 1) * (Sing n * Real.pi * n) :=
          Finset.sum_le_sum (fun i _ => hinner i)
      _ = ((K : ℝ) + 1) * (((K : ℝ) + 1) * (Sing n * Real.pi * n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hre : |(∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
        gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
      ((K : ℝ) + 1) * (((K : ℝ) + 1) * (Sing n * Real.pi * n)) :=
    (Complex.abs_re_le_norm _).trans hT
  have hnn : 0 ≤ (n : ℝ) * Sing n := mul_nonneg (Nat.cast_nonneg n) hS0
  refine hre.trans ?_
  have hEq : ((K : ℝ) + 1) * (((K : ℝ) + 1) * (Sing n * Real.pi * n))
      = ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by ring
  rw [hEq]
  linarith

end explicit_formula_reduction_helpers

/-- LEAF. P0045 page 5, multiplicity sentence before Lemma 4.1.
Group an indexed zero family by its actual character and zero value.
The occurrence bound controls its length by the sum of analytic multiplicities. -/
theorem indexed_zero_count481 {K : ℕ}
    (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (hmult : ∀ w, (univ.filter (fun i => z i = w)).card ≤
      analyticOrderNatAt (Lfun481 w.2.1) w.2.2) :
    (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ) := by
  exact_mod_cast (show K ≤ ∑ w ∈ univ.image z, analyticOrderNatAt (Lfun481 w.2.1) w.2.2 from by
    simpa only [← card_eq_sum_card_image z univ, card_univ, Fintype.card_fin] using
      (sum_le_sum fun w (_ : w ∈ univ.image z) => hmult w))

/-! Helpers for `gamma_pair_bound481`. These are the proved steps of
`SPLIT_gamma_pair_bound481`, repeated here as private lemmas because that file imports this one.
Mathlib inputs: `Complex.betaIntegral_eq_Gamma_mul_div`, `Complex.betaIntegral_convergent`,
`Real.Gamma_one_half_eq`. -/

section gamma_pair_helpers

open MeasureTheory

private lemma lpz_norm_cpow_factor (u : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (u - 1)‖ = x ^ (u.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

private lemma lpz_integrand_norm (u v : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ =
      x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  have h2 : ‖(1 - (x : ℂ)) ^ (v - 1)‖ = (1 - x) ^ (v.re - 1) := by
    have hc : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact lpz_norm_cpow_factor v (by linarith)
  rw [norm_mul, lpz_norm_cpow_factor u hx0, h2]

private lemma lpz_ae_ne_one : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 1 := by
  have h : (volume : Measure ℝ) ({1} : Set ℝ) = 0 := by simp
  exact MeasureTheory.ae_iff.mpr (by simp)

/-- The norm of the Beta integral is at most the integral of the modulus, and the modulus of the
integrand is exactly the real Beta integrand of the real parts. -/
private lemma lpz_beta_norm_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  rw [Complex.betaIntegral]
  refine (intervalIntegral.norm_integral_le_integral_norm
    (f := fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1))
    (a := 0) (b := 1) zero_le_one).trans_eq ?_
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [lpz_ae_ne_one] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact lpz_integrand_norm u v hx.1 (lt_of_le_of_ne hx.2 hx1)

/-- For real parameters of positive real part the Beta integral is a nonnegative real number, and
its modulus is the real Beta integral. -/
private lemma lpz_beta_norm_eq (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) :
    ‖Complex.betaIntegral (a : ℂ) (b : ℂ)‖ =
      ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  have hcongr : (∫ x in (0 : ℝ)..1, (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1))
      = ∫ x in (0 : ℝ)..1, ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [lpz_ae_ne_one] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : 0 < x := hx.1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have e1 : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
      have he : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [he, ← Complex.ofReal_cpow hx0.le]
    have e2 : (1 - (x : ℂ)) ^ ((b : ℂ) - 1) = (((1 - x) ^ (b - 1) : ℝ) : ℂ) := by
      have hc : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
      have he : (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, he, ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - x)]
    rw [e1, e2, ← Complex.ofReal_mul]
  rw [Complex.betaIntegral, hcongr, intervalIntegral.integral_ofReal]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  refine intervalIntegral.integral_nonneg zero_le_one ?_
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (by linarith [hx.2]) _)

/-- The real Beta integrand of positive parameters is interval integrable on `[0,1]`. -/
private lemma lpz_intervalIntegrable_beta (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 := by
  have hc : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) volume 0 1 :=
    Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
      (by simpa using ha) (by simpa using hb)
  have hnorm : IntervalIntegrable
      (fun x : ℝ => ‖(x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)‖) volume 0 1 :=
    intervalIntegrable_iff.mpr hc.def'.norm
  refine hnorm.congr_ae ?_
  filter_upwards [lpz_ae_ne_one.filter_mono ae_restrict_le,
    self_mem_ae_restrict measurableSet_uIoc] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact lpz_integrand_norm _ _ hx.1 (lt_of_le_of_ne hx.2 hx1)

/-- The symmetric Beta integral at one half is `π`. -/
private lemma lpz_beta_half : Complex.betaIntegral ((1 / 2 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ) =
    (Real.pi : ℂ) := by
  have hg : Complex.Gamma ((1 / 2 : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Complex.Gamma_ofReal, Real.Gamma_one_half_eq]
  have hsum : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num), hsum, hg,
    Complex.Gamma_one, div_one, ← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]


/-- First step: identify the modulus of the Gamma quotient with the modulus of the Beta
integral. In the strip of the target both real parts are positive, so the Beta integral exists and
the Gamma factors multiply to `Γ (s + t)` times it; dividing by the nonvanishing `Γ (s + t)` gives
the identity of norms. This is the reduction step, an identity and not an estimate. -/
private theorem lpz_gamma_ratio_norm_eq_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ =
      ‖Complex.betaIntegral s t‖ := by
  rw [← Complex.betaIntegral_eq_Gamma_mul_div s t (by linarith) (by linarith)]

/-- Second step: the Beta integral of the complex pair is dominated by the Beta integral of
its real parts. The integrand of the real-part Beta integral is the pointwise modulus of the
integrand of the complex one, so the norm of the integral is at most the integral of the modulus,
which is the real-part Beta integral. -/
private theorem lpz_beta_norm_le_re_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.betaIntegral s t‖ ≤ ‖Complex.betaIntegral (s.re : ℂ) (t.re : ℂ)‖ := by
  have h1 := lpz_beta_norm_le s t
  have h2 := lpz_beta_norm_eq s.re t.re (by linarith) (by linarith)
  rw [h2]
  exact h1

/-- Third step: the real-parameter Beta integral is at most `π` once both parameters are at
least one half. On `(0, 1)` the integrand decreases in each parameter, so the integral is largest at
the pair `(1/2, 1/2)`, where it equals the square of `Γ (1/2)` divided by `Γ 1`, that is `π`. -/
private theorem lpz_beta_real_half_le_pi481 {a b : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    ‖Complex.betaIntegral (a : ℂ) (b : ℂ)‖ ≤ Real.pi := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [lpz_beta_norm_eq a b ha0 hb0]
  have hstep : (∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1))
      ≤ ∫ x in (0 : ℝ)..1, x ^ ((1 / 2 : ℝ) - 1) * (1 - x) ^ ((1 / 2 : ℝ) - 1) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo
      (f := fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
      (g := fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) * (1 - x) ^ ((1 / 2 : ℝ) - 1))
      (a := 0) (b := 1) zero_le_one (lpz_intervalIntegrable_beta a b ha0 hb0)
      (lpz_intervalIntegrable_beta _ _ (by norm_num) (by norm_num)) ?_
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have h1 : x ^ (a - 1) ≤ x ^ ((1 / 2 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith)
    have h2 : (1 - x) ^ (b - 1) ≤ (1 - x) ^ ((1 / 2 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hx0.le _)
  refine hstep.trans ?_
  rw [← lpz_beta_norm_eq (1 / 2) (1 / 2) (by norm_num) (by norm_num), lpz_beta_half]
  rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- Fourth step: the norm of the power factor is the real power at the real part of the
exponent. The base is the positive integer `n`, so the norm of `n ^ w` is `n ^ w.re`. -/
private theorem lpz_cpow_norm_eq481 {s t : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (s + t - 1)‖ = (n : ℝ) ^ ((s + t).re - 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : (s + t - (1 : ℂ)).re = (s + t).re - 1 := by simp
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre]

/-- Fifth step: a real power of a base at least one is at most the base itself when the
exponent is at most one. Here `σ = (s + t).re` is at most two, so the exponent `σ - 1` is at most
one, and the base `n` is at least one. -/
private theorem lpz_rpow_sub_one_le_self481 {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : σ ≤ 2) :
    (n : ℝ) ^ (σ - 1) ≤ (n : ℝ) := by
  refine Real.rpow_le_self_of_one_le ?_ ?_
  · exact_mod_cast hn
  · linarith

end gamma_pair_helpers

/-- LEAF. PROVED. P0045 page 5, Gamma pair in Lemma 4.1.
The beta integral bounds the Gamma quotient by pi in this strip.
The power of positive n is then bounded by n. This is a derived summand estimate. -/
theorem gamma_pair_bound481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re)
    (hs1 : s.re ≤ 1) (ht1 : t.re ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖gammaPair481 s t n‖ ≤ Real.pi * n := by
  have hA : ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ ≤ Real.pi := by
    rw [lpz_gamma_ratio_norm_eq_beta481 hs0 ht0]
    exact (lpz_beta_norm_le_re_beta481 hs0 ht0).trans (lpz_beta_real_half_le_pi481 hs0 ht0)
  have hB : ‖(n : ℂ) ^ (s + t - 1)‖ ≤ (n : ℝ) := by
    rw [lpz_cpow_norm_eq481 (s := s) (t := t) hn]
    refine lpz_rpow_sub_one_le_self481 hn ?_
    have hst : (s + t).re = s.re + t.re := Complex.add_re s t
    linarith
  rw [gammaPair481, norm_mul]
  exact mul_le_mul hA hB (norm_nonneg _) Real.pi_pos.le

/-- LEAF. PROVED. P0045 page 6, paragraph before Corollary 4.2 and display 9.
Choose H and T large, then epsilon small. Separate the pole pair in Lemma 4.1,
bound the other Gamma pairs and absorb the remainder using n in J and Sing n bounded below.
Jutila controls the indexed family with multiplicity. This leaf does not assert display 10. -/
theorem explicit_formula_reduction481
    (hexp : Lemma41Statement481) (hdensity : JutilaStatement481)
    (hcount : ∀ {K : ℕ} (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
      (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ))
    (hgamma : ∀ {s t : ℂ}, (1 / 2 : ℝ) ≤ s.re → (1 / 2 : ℝ) ≤ t.re →
      s.re ≤ 1 → t.re ≤ 1 → ∀ {n : ℕ}, 1 ≤ n →
        ‖gammaPair481 s t n‖ ≤ Real.pi * n)
    (η : ℝ) (hη : 0 < η) :
    ∃ (K₁ Cstar : ℕ) (A H T : ℝ), 0 < Cstar ∧ 0 ≤ A ∧ 1 ≤ H ∧ 1 ≤ T ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ E.card ≤ K₁ ∧
          (∀ r ∈ E, ∃ z ∈ zeroBox481 X H T P, z.1 = r) ∧
          (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
            |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
          (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  classical
  obtain ⟨C₀, hC₀, hdens⟩ := lpz_efr_zero_family_card_bound481 hdensity hcount
  obtain ⟨s₀, hs₀, hs₀le⟩ := lpz_efr_singular_series_lower481
  obtain ⟨c, ε₀, B, H₀, T₀, hc, hε₀, hB, Cε, hCε, hmain⟩ := hexp
  obtain ⟨H, T, ε, hH₀, hH1, hT₀, hT1, hε, hεε₀, hAbs, hSmall⟩ :=
    lpz_efr_absorption_constants481 c B ε₀ s₀ C₀ η H₀ T₀ hc hB hε₀ hs₀ hC₀ hη
  set K₁ : ℕ := ⌈C₀ * Real.exp (4 * H)⌉₊ + 1 with hK₁
  set Cstar : ℕ := Cε ε with hCs
  set A : ℝ := 1 + ((K₁ : ℝ) + 1) ^ 2 * Real.pi + η / 2 with hA
  have hCstar : 0 < Cstar := hCε ε
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨X₁, hX₁⟩ := hmain H T hH₀ hT₀
  obtain ⟨X₂, hX₂⟩ := hdens H T hH1 hT1
  obtain ⟨X₃, hX₃⟩ := lpz_efr_log_threshold481 H
  refine ⟨K₁, Cstar, A, H, T, hCstar, hA0, hH1, hT1, max X₁ (max X₂ X₃), ?_⟩
  intro X hX
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  obtain ⟨P, hP, K, z, Sg, hz01, hz0s, hbox, hmult, hSg00, hSgb, hSgε, hrem⟩ :=
    hX₁ X hx1
  have hnR : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have hlog : 2 * H ≤ Real.log X := hX₃ X hx3
  have hlogpos : 0 < Real.log X := by linarith
  have hdivH : H / Real.log X ≤ 1 / 2 := by
    rw [div_le_iff₀ hlogpos]
    linarith
  have hstrip : ∀ i : Fin (K + 1), (1 / 2 : ℝ) ≤ (z i).2.2.re ∧ (z i).2.2.re ≤ 1 := by
    intro i
    by_cases hi : i = 0
    · have hz : (z i).2.2 = 1 := by rw [hi]; exact hz0s
      rw [hz]
      norm_num
    · have hmem := hbox i hi
      simp only [zeroBox481, Set.mem_setOf_eq] at hmem
      obtain ⟨-, -, -, -, hre, hre1, -⟩ := hmem
      exact ⟨by linarith, le_of_lt hre1⟩
  have hγf : ∀ (n : ℕ), 1 ≤ n → ∀ i j,
      ‖gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤ Real.pi * n :=
    fun n hn i j => hgamma (hstrip i).1 (hstrip j).1 (hstrip i).2 (hstrip j).2 hn
  have hK : (K : ℝ) ≤ C₀ * Real.exp (4 * H) := hX₂ X hx2 P hP K z hz01 hz0s hbox hmult
  have hKle : K ≤ K₁ := by
    have h1 : (K : ℝ) ≤ (⌈C₀ * Real.exp (4 * H)⌉₊ : ℝ) := le_trans hK (Nat.le_ceil _)
    have h2 : K ≤ ⌈C₀ * Real.exp (4 * H)⌉₊ := by exact_mod_cast h1
    rw [hK₁]
    omega
  refine ⟨P, (univ.erase (0 : Fin (K + 1))).image (fun i => (z i).1), hP, ?_, ?_, ?_, ?_⟩
  · have hcard : ((univ.erase (0 : Fin (K + 1))).image (fun i => (z i).1)).card ≤ K := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨z i, hbox i (Finset.mem_erase.mp hi).1, rfl⟩
  · intro n hn hnonexc
    have hn1 : 1 ≤ n := (evenJ_nat131 hn).1
    have hX2n : (X : ℝ) ≤ 2 * n := by
      have h : (2 : ℝ) * X ≤ 3 * n := by
        have hnat : 2 * X ≤ 3 * n := (evenJ_nat131 hn).2.2.2
        exact_mod_cast hnat
      linarith
    have hQ0 : 0 ≤ Real.exp (-c * H) + 1 / Real.sqrt T := by
      have h1 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
      have h2 : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
      positivity
    have hSgε' : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → ‖Sg i j n‖ ≤ ε := by
      intro i j hij
      refine hSgε ε hε hεε₀ i j n hn ?_
      rcases hij with hi | hj
      · exact Or.inl (hnonexc (z i).1 (Finset.mem_image.mpr
          ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩))
      · exact Or.inr (hnonexc (z j).1 (Finset.mem_image.mpr
          ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, rfl⟩))
    set Tsum : ℝ := (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
      gammaPair481 (z i).2.2 (z j).2.2 n).re with hTsum
    have hrem' : |binaryMajor131 X n P - Tsum| ≤
        (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by
      have hremn := hrem n hn
      rw [← hTsum] at hremn
      refine hremn.trans ?_
      calc B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)
          = X * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) := by ring
        _ ≤ (2 * n) * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) :=
            mul_le_mul_of_nonneg_right hX2n (mul_nonneg hB hQ0)
        _ = (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by ring
    have h4 : |Tsum - n * Sing n| ≤ ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := by
      have h := lpz_efr_explicit_formula_main_term481 z Sg n ε hz0s (hSg00 n hn) (hγf n hn1) hε.le hSgε'
      rw [← hTsum] at h
      exact h
    have hOffN : ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n ≤ (η * s₀ / 2) * n := by
      have hsq : ((K : ℝ) + 1) ^ 2 ≤ (C₀ * Real.exp (4 * H) + 2) ^ 2 := by
        nlinarith [hK]
      calc ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n
          = ((K : ℝ) + 1) ^ 2 * (ε * Real.pi * n) := by ring
        _ ≤ (C₀ * Real.exp (4 * H) + 2) ^ 2 * (ε * Real.pi * n) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = ((C₀ * Real.exp (4 * H) + 2) ^ 2 * Real.pi * ε) * n := by ring
        _ ≤ (η * s₀ / 2) * n := mul_le_mul_of_nonneg_right hSmall (hnR n)
    calc |binaryMajor131 X n P - n * Sing n|
        ≤ |binaryMajor131 X n P - Tsum| + |Tsum - n * Sing n| := abs_sub_le _ _ _
      _ ≤ (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n +
          ((K : ℝ) + 1) ^ 2 * ε * Real.pi * n := add_le_add hrem' h4
      _ ≤ (η * s₀ / 2) * n + (η * s₀ / 2) * n :=
          add_le_add (mul_le_mul_of_nonneg_right hAbs (hnR n)) hOffN
      _ ≤ η * n * Sing n := by
          have hs : s₀ ≤ Sing n := hs₀le X n hn
          have h1 : (η * s₀ / 2) * n + (η * s₀ / 2) * n = (η * n) * s₀ := by ring
          rw [h1]
          calc (η * n) * s₀ ≤ (η * n) * Sing n :=
                mul_le_mul_of_nonneg_left hs (by positivity)
            _ = η * n * Sing n := by ring
  · intro n hn
    have hn1 : 1 ≤ n := (evenJ_nat131 hn).1
    have hX2n : (X : ℝ) ≤ 2 * n := by
      have h : (2 : ℝ) * X ≤ 3 * n := by
        have hnat : 2 * X ≤ 3 * n := (evenJ_nat131 hn).2.2.2
        exact_mod_cast hnat
      linarith
    have hQ0 : 0 ≤ Real.exp (-c * H) + 1 / Real.sqrt T := by
      have h1 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
      have h2 : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
      positivity
    set Tsum : ℝ := (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
      gammaPair481 (z i).2.2 (z j).2.2 n).re with hTsum
    have hrem' : |binaryMajor131 X n P - Tsum| ≤
        (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by
      have hremn := hrem n hn
      rw [← hTsum] at hremn
      refine hremn.trans ?_
      calc B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)
          = X * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) := by ring
        _ ≤ (2 * n) * (B * (Real.exp (-c * H) + 1 / Real.sqrt T)) :=
            mul_le_mul_of_nonneg_right hX2n (mul_nonneg hB hQ0)
        _ = (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n := by ring
    have h5 : |Tsum| ≤ n * Sing n + ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by
      have h := lpz_efr_explicit_formula_total_size481 z Sg n (hγf n hn1) (fun i j => hSgb i j n hn)
        (Sing_nonneg131 n)
      rw [← hTsum] at h
      exact h
    have hDnS : (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n ≤
        (η / 2) * (n * Sing n) := by
      have hnS : s₀ * (n : ℝ) ≤ Sing n * n :=
        mul_le_mul_of_nonneg_right (hs₀le X n hn) (hnR n)
      calc (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n
          ≤ (η * s₀ / 2) * n := mul_le_mul_of_nonneg_right hAbs (hnR n)
        _ = (η / 2) * (s₀ * n) := by ring
        _ ≤ (η / 2) * (Sing n * n) := mul_le_mul_of_nonneg_left hnS (by positivity)
        _ = (η / 2) * (n * Sing n) := by ring
    have hKle' : ((K : ℝ) + 1) ^ 2 ≤ ((K₁ : ℝ) + 1) ^ 2 := by
      have h : (K : ℝ) ≤ (K₁ : ℝ) := by exact_mod_cast hKle
      nlinarith
    have hoffS : ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n ≤
        ((K₁ : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by
      have h0 : 0 ≤ Real.pi * n * Sing n :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)) (Sing_nonneg131 n)
      calc ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n
          = ((K : ℝ) + 1) ^ 2 * (Real.pi * n * Sing n) := by ring
        _ ≤ ((K₁ : ℝ) + 1) ^ 2 * (Real.pi * n * Sing n) :=
            mul_le_mul_of_nonneg_right hKle' h0
        _ = ((K₁ : ℝ) + 1) ^ 2 * Real.pi * n * Sing n := by ring
    have hb : |binaryMajor131 X n P| ≤ |binaryMajor131 X n P - Tsum| + |Tsum| := by
      simpa using abs_add_le (binaryMajor131 X n P - Tsum) Tsum
    calc |binaryMajor131 X n P|
        ≤ |binaryMajor131 X n P - Tsum| + |Tsum| := hb
      _ ≤ (2 * B * (Real.exp (-c * H) + 1 / Real.sqrt T)) * n +
          (n * Sing n + ((K : ℝ) + 1) ^ 2 * Real.pi * n * Sing n) := add_le_add hrem' h5
      _ ≤ (η / 2) * (n * Sing n) +
          (n * Sing n + ((K₁ : ℝ) + 1) ^ 2 * Real.pi * n * Sing n) :=
          add_le_add hDnS (add_le_add le_rfl hoffS)
      _ = A * n * Sing n := by rw [hA]; ring

/-- P0045 page 6, display 10: combine the real and nonreal character cases.
The conclusion remains conditional on the explicit classification and zero region inputs. -/
theorem exceptional_radical481 (hclass : RealPrimitiveStatement481)
    (hzero : RealZeroStatement481) (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨cr, hcr, Xr, hr⟩ := real_exceptional_conductor481 hzero H T hH hT
  obtain ⟨cn, hcn, Xn, hn⟩ := nonreal_exceptional_radical481 hiw H T hH hT
  refine ⟨min (cr / 8) cn, lt_min (by positivity) hcn, max Xr Xn, ?_⟩
  intro X hX P hP z hz
  by_cases hreal : ∀ a, (z.2.1 a).im = 0
  · have hbound := real_radical_transfer481 (hclass _ hz.1 _ hz.2.2.1 hreal)
      (hr X ((le_max_left _ _).trans hX) P hP z hz hreal)
    have hm := mul_le_mul_of_nonneg_right (min_le_left (cr / 8) cn) (sq_nonneg (Lg X))
    nlinarith
  · exact (mul_le_mul_of_nonneg_right (min_le_right (cr / 8) cn)
      (sq_nonneg (Lg X))).trans
        (hn X ((le_max_right _ _).trans hX) P hP z hz (by simpa using hreal))

end
end LeanLab.LPZ2007
