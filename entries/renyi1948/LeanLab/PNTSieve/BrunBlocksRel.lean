module

public import LeanLab.PNTSieve.BrunBlocksSupport

/-!
# Brun's block sieve with relative errors

Unit U-5508, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics, the shape
`S ≥ X V (1 - ε)` of the fundamental lemma.

`blocks_main_dev` bounds the main terms with absolute errors; since `V = ∏_Ω (1 - x_p)` decays like
`1/log z`, the fundamental lemma needs them relative to `V`. With the block ratio
`ρ_B = max(E_B^{re}, E_B^{ro})/V_B`:

* `blocks_rel_dev`: `|M_U - V| ≤ dU V` and `|M_L - V| ≤ dL V`, with
  `dU(b::Bs) = ρ_b (1 + dU) + dU`, `dL(b::Bs) = dL + ρ_b (1 + dU) + ρ_b (dL + dU)`;
* `d_le_of_sum`: if `Σ_b ρ_b ≤ 1/10` then `dU ≤ 2 Σ ρ_b` and `dL ≤ 5 Σ ρ_b`;
* `blocks_main_rel`: `S(A, Ω) ≥ X V (1 - 5 Σ ρ_b) - 3^{#blocks} Σ_{cL S ≠ 0} |R_S|`.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- The block ratio `ρ_B = max(E_B^{re}, E_B^{ro})/V_B`. -/
noncomputable def rho (x : ℕ → ℝ) (b : Block) : ℝ :=
  max (truncErr b.1 x b.2.1) (truncErr b.1 x b.2.2) / ∏ p ∈ b.1, (1 - x p)

noncomputable def dU (x : ℕ → ℝ) : List Block → ℝ
  | [] => 0
  | b :: Bs => rho x b * (1 + dU x Bs) + dU x Bs

noncomputable def dL (x : ℕ → ℝ) : List Block → ℝ
  | [] => 0
  | b :: Bs => dL x Bs + rho x b * (1 + dU x Bs) + rho x b * (dL x Bs + dU x Bs)

/-- The sum of the block ratios. -/
noncomputable def rhoSum (x : ℕ → ℝ) : List Block → ℝ
  | [] => 0
  | b :: Bs => rho x b + rhoSum x Bs

lemma truncErr_nonneg (P : Finset ℕ) (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (r : ℕ) :
    0 ≤ truncErr P x r := by
  unfold truncErr
  have : 0 ≤ ∑ p ∈ P, x p := sum_nonneg (fun p _ => hx0 p)
  positivity

lemma rho_nonneg (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (b : Block) :
    0 ≤ rho x b := by
  unfold rho
  apply div_nonneg (le_max_of_le_left (truncErr_nonneg _ x hx0 _))
  exact prod_nonneg (fun p _ => by linarith [hx1 p])

lemma rhoSum_nonneg (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) :
    ∀ Bs : List Block, 0 ≤ rhoSum x Bs
  | [] => le_rfl
  | b :: Bs => add_nonneg (rho_nonneg x hx0 hx1 b) (rhoSum_nonneg x hx0 hx1 Bs)

/-- **Relative main-term errors.** Needs `x_p < 1`, so every `V_B > 0`. -/
theorem blocks_rel_dev (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1) :
    ∀ Bs : List Block, Good Bs →
      |wMain (univB Bs) (cU Bs) x - ∏ p ∈ univB Bs, (1 - x p)| ≤
          dU x Bs * ∏ p ∈ univB Bs, (1 - x p) ∧
      |wMain (univB Bs) (cL Bs) x - ∏ p ∈ univB Bs, (1 - x p)| ≤
          dL x Bs * ∏ p ∈ univB Bs, (1 - x p)
  | [], _ => by simp [univB, cU, cL, dU, dL, wMain_unit]
  | b :: Bs, hG => by
    have hx1' : ∀ p, x p ≤ 1 := fun p => (hx1 p).le
    obtain ⟨hP, hD, hre, hro, hG'⟩ := hG
    obtain ⟨ihU, ihL⟩ := blocks_rel_dev x hx0 hx1 Bs hG'
    simp only [univB, cL, cU, dU, dL]
    rw [wMain_sub, wMain_add, wMain_tens hD, wMain_tens hD, wMain_tens hD,
      wMain_tc, wMain_tc, prod_union hD]
    set V := ∏ p ∈ b.1, (1 - x p)
    set V' := ∏ p ∈ univB Bs, (1 - x p)
    set MU := wMain (univB Bs) (cU Bs) x
    set ML := wMain (univB Bs) (cL Bs) x
    set ρ := rho x b with hρ
    have hV : 0 < V := prod_pos (fun p _ => by linarith [hx1 p])
    have hV' : 0 < V' := prod_pos (fun p _ => by linarith [hx1 p])
    have hρ0 : 0 ≤ ρ := rho_nonneg x hx0 hx1' b
    have he : |msum b.1 x b.2.1 - V| ≤ ρ * V := by
      refine (main_dev b.1 x hx0 hx1' _).trans ?_
      rw [hρ, rho, div_mul_cancel₀ _ hV.ne']
      exact le_max_left _ _
    have ho : |msum b.1 x b.2.2 - V| ≤ ρ * V := by
      refine (main_dev b.1 x hx0 hx1' _).trans ?_
      rw [hρ, rho, div_mul_cancel₀ _ hV.ne']
      exact le_max_right _ _
    have hdU0 : 0 ≤ dU x Bs := by
      by_contra h
      push Not at h
      have : dU x Bs * V' < 0 := mul_neg_of_neg_of_pos h hV'
      linarith [abs_nonneg (MU - V')]
    have hdL0 : 0 ≤ dL x Bs := by
      by_contra h
      push Not at h
      have : dL x Bs * V' < 0 := mul_neg_of_neg_of_pos h hV'
      linarith [abs_nonneg (ML - V')]
    have hMU : |MU| ≤ (1 + dU x Bs) * V' := by
      have := abs_add_le (MU - V') V'
      rw [sub_add_cancel, abs_of_pos hV'] at this
      nlinarith
    constructor
    · have hid : msum b.1 x b.2.1 * MU - V * V' = (msum b.1 x b.2.1 - V) * MU + V * (MU - V') := by
        ring
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hV]
      have h1 := mul_le_mul he hMU (abs_nonneg _) (mul_nonneg hρ0 hV.le)
      have h2 := mul_le_mul_of_nonneg_left ihU hV.le
      have e : (ρ * (1 + dU x Bs) + dU x Bs) * (V * V') =
          ρ * V * ((1 + dU x Bs) * V') + V * (dU x Bs * V') := by ring
      rw [e]
      linarith
    · have hid : msum b.1 x b.2.1 * ML + msum b.1 x b.2.2 * MU - msum b.1 x b.2.1 * MU - V * V' =
          V * (ML - V') + (msum b.1 x b.2.2 - V) * MU + (msum b.1 x b.2.1 - V) * (ML - MU) := by
        ring
      rw [hid]
      have hLU : |ML - MU| ≤ (dL x Bs + dU x Bs) * V' := by
        have := abs_sub_le ML V' MU
        rw [abs_sub_comm V' MU] at this
        linarith
      rw [show (dL x Bs + ρ * (1 + dU x Bs) + ρ * (dL x Bs + dU x Bs)) * (V * V') =
          V * (dL x Bs * V') + (ρ * V) * ((1 + dU x Bs) * V') +
            (ρ * V) * ((dL x Bs + dU x Bs) * V') by ring]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [abs_mul, abs_of_pos hV]
        exact mul_le_mul_of_nonneg_left ihL hV.le
      · rw [abs_mul]; exact mul_le_mul ho hMU (abs_nonneg _) (mul_nonneg hρ0 hV.le)
      · rw [abs_mul]; exact mul_le_mul he hLU (abs_nonneg _) (mul_nonneg hρ0 hV.le)

/-- **Accumulation**: if `Σ ρ_b ≤ 1/10` then `0 ≤ dU ≤ 2 Σ ρ_b` and `0 ≤ dL ≤ 5 Σ ρ_b`. -/
theorem d_le_of_sum (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) :
    ∀ Bs : List Block, rhoSum x Bs ≤ 1 / 10 →
      0 ≤ dU x Bs ∧ dU x Bs ≤ 2 * rhoSum x Bs ∧ 0 ≤ dL x Bs ∧ dL x Bs ≤ 5 * rhoSum x Bs
  | [], _ => by simp [dU, dL, rhoSum]
  | b :: Bs, h => by
    have hρ := rho_nonneg x hx0 hx1 b
    have hS := rhoSum_nonneg x hx0 hx1 Bs
    simp only [rhoSum] at h
    obtain ⟨hU0, hU, hL0, hL⟩ := d_le_of_sum x hx0 hx1 Bs (by linarith)
    simp only [dU, dL, rhoSum]
    have hU2 : dU x Bs ≤ 1 / 5 := by linarith
    have hL2 : dL x Bs ≤ 1 / 2 := by linarith
    refine ⟨by positivity, ?_, by positivity, ?_⟩
    · nlinarith
    · nlinarith

/-- **Brun's block sieve with relative error**: `S(A, Ω) ≥ X V (1 - 5 Σ ρ_b) - 3^n Σ |R_S|`. -/
theorem blocks_main_rel (A : Finset ℕ) (Bs : List Block) (hG : Good Bs) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1) (X : ℝ) (hX : 0 ≤ X)
    (hρ : rhoSum x Bs ≤ 1 / 10) :
    X * (∏ p ∈ univB Bs, (1 - x p)) * (1 - 5 * rhoSum x Bs) -
      3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), |rem A x X S| ≤
      (sifted A (univB Bs) : ℝ) := by
  have hx1' : ∀ p, x p ≤ 1 := fun p => (hx1 p).le
  have h1 := blocks_sum A Bs hG
  rw [sum_wEval A (univB Bs) (cL Bs) x X] at h1
  have h2 := (blocks_rel_dev x hx0 hx1 Bs hG).2
  rw [abs_le] at h2
  have hd := (d_le_of_sum x hx0 hx1' Bs hρ).2.2.2
  have hV : 0 ≤ ∏ p ∈ univB Bs, (1 - x p) := prod_nonneg (fun p _ => by linarith [hx1 p])
  have h3 : -(3 ^ Bs.length *
      ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), |rem A x X S|) ≤
      ∑ S ∈ (univB Bs).powerset, cL Bs S * rem A x X S := by
    have hle : ∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤
        3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0),
          |rem A x X S| := by
      rw [mul_sum, sum_filter]
      refine sum_le_sum (fun S _ => ?_)
      split_ifs with hS
      · exact mul_le_mul_of_nonneg_right (coeff_bounds Bs S).2 (abs_nonneg _)
      · push Not at hS; rw [hS]; simp
    have : -∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤
        ∑ S ∈ (univB Bs).powerset, cL Bs S * rem A x X S := by
      rw [← sum_neg_distrib]
      refine sum_le_sum (fun S _ => ?_)
      rw [← abs_mul]
      exact neg_abs_le _
    linarith
  have h4 : (∏ p ∈ univB Bs, (1 - x p)) * (1 - 5 * rhoSum x Bs) ≤ wMain (univB Bs) (cL Bs) x := by
    have := mul_le_mul_of_nonneg_left hd hV
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 hX
  nlinarith

end LeanLab.PNTSieve.Bonferroni

