module

public import LeanLab.Pintz2018.Statements

/-!
Theorem K, display 4.41 on page 18, decomposed along displays 8.12 to 8.16 on page 35.
Maximality is taken over the box and budget, including unsorted competitors.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Decomp117b

/-- LEAF. Page 35, displays 8.12 to 8.14. Moving mass from the smaller coordinate
to the larger decreases a concave cost and increases a strictly convex objective. -/
theorem leaf_pair_exchange (H G : ℝ → ℝ)
    (hH : ConcaveOn ℝ (Set.Ici 1) H) (hG : StrictConvexOn ℝ (Set.Ici 1) G)
    (y z eta : ℝ) (hyz : z ≤ y) (heta : 0 < eta) (hz : 1 ≤ z - eta) :
    H (y + eta) + H (z - eta) ≤ H y + H z ∧
      G y + G z < G (y + eta) + G (z - eta) := by
  have hden : 0 < y - z + 2 * eta := by linarith
  have hden' : y - z + 2 * eta ≠ 0 := hden.ne'
  let a := eta / (y - z + 2 * eta)
  let b := (y - z + eta) / (y - z + 2 * eta)
  have ha : 0 < a := div_pos heta hden
  have hb : 0 < b := div_pos (by linarith) hden
  have hab : a + b = 1 := by
    dsimp [a, b]; rw [← add_div, div_eq_one_iff_eq hden']; ring
  have hyid : b * (y + eta) + a * (z - eta) = y := by
    dsimp [a, b]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hden']
    ring
  have hzid : a * (y + eta) + b * (z - eta) = z := by
    dsimp [a, b]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hden']
    ring
  have hhi : y + eta ∈ Set.Ici (1 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have hlo : z - eta ∈ Set.Ici (1 : ℝ) := hz
  have hne : y + eta ≠ z - eta := by linarith
  have hh1 := hH.2 hhi hlo hb.le ha.le (by linarith : b + a = 1)
  have hh2 := hH.2 hhi hlo ha.le hb.le hab
  have hg1 := hG.2 hhi hlo hne hb ha (by linarith : b + a = 1)
  have hg2 := hG.2 hhi hlo hne ha hb hab
  simp only [smul_eq_mul, hyid, hzid] at hh1 hh2 hg1 hg2
  constructor
  · linear_combination hh1 + hh2 - (H (y + eta) + H (z - eta)) * hab
  · linear_combination hg1 + hg2 + (G (y + eta) + G (z - eta)) * hab

/-- LEAF. Page 35, the substitution after display 8.16.
The sum changes by the sum of the two coordinate changes. -/
theorem leaf_two_update_sum (s : Finset ℕ) (y : ℕ → ℝ) (f : ℝ → ℝ)
    (k r : ℕ) (hk : k ∈ s) (hr : r ∈ s) (hkr : k ≠ r) (u v : ℝ) :
    (∑ j ∈ s, f (Function.update (Function.update y k u) r v j)) =
      (∑ j ∈ s, f (y j)) + (f u - f (y k)) + (f v - f (y r)) := by
  have hu : ∀ (z : ℕ → ℝ) (i : ℕ), i ∈ s → ∀ t : ℝ,
      (∑ j ∈ s, f (Function.update z i t j)) =
        (∑ j ∈ s, f (z j)) + f t - f (z i) := by
    intro z i hi t
    simp_rw [Function.apply_update (fun _ => f)]
    rw [Finset.sum_update_of_mem hi]
    have hzero := Finset.sum_update_of_mem hi (fun j => f (z j)) (f (z i))
    simp only [Function.update_eq_self] at hzero
    linarith
  rw [hu (Function.update y k u) r hr v, hu y k hk u,
    Function.update_of_ne (Ne.symm hkr)]
  ring

/-- LEAF. Page 35, the small positive eta after display 8.16.
A gap below the upper bound and a lower coordinate above one permit a transfer. -/
theorem leaf_transfer_box (s : Finset ℕ) (y Y : ℕ → ℝ) (k r : ℕ) (hkr : k ≠ r)
    (hbox : ∀ j ∈ s, 1 ≤ y j ∧ y j ≤ Y j) (hgap : y k < Y k) (hactive : 1 < y r) :
    ∃ eta : ℝ, 0 < eta ∧ 1 ≤ y r - eta ∧
      ∀ j ∈ s, 1 ≤ Function.update (Function.update y k (y k + eta)) r (y r - eta) j ∧
        Function.update (Function.update y k (y k + eta)) r (y r - eta) j ≤ Y j := by
  let eta := min (Y k - y k) (y r - 1) / 2
  have heta : 0 < eta := div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hcap : eta ≤ Y k - y k := by
    have := min_le_left (Y k - y k) (y r - 1)
    dsimp [eta] at *
    linarith
  have hfloor : eta ≤ y r - 1 := by
    have := min_le_right (Y k - y k) (y r - 1)
    dsimp [eta] at *
    linarith
  refine ⟨eta, heta, by linarith, ?_⟩
  intro j hj
  by_cases hjr : j = r
  · subst j
    simp only [Function.update_self]
    exact ⟨by linarith, by linarith [(hbox r hj).2]⟩
  · rw [Function.update_of_ne hjr]
    by_cases hjk : j = k
    · subst j
      simp only [Function.update_self]
      exact ⟨by linarith [(hbox k hj).1], by linarith⟩
    · rw [Function.update_of_ne hjk]
      exact hbox j hj

/-- LEAF. Page 35, displays 8.15 and 8.16. A box and budget maximizer
saturates every coordinate at least as large as a later coordinate above one. -/
theorem leaf_greedy_saturation (s : Finset ℕ) (y Y : ℕ → ℝ) (H G : ℝ → ℝ) (budget : ℝ)
    (hH : ConcaveOn ℝ (Set.Ici 1) H) (hG : StrictConvexOn ℝ (Set.Ici 1) G)
    (hbox : ∀ j ∈ s, 1 ≤ y j ∧ y j ≤ Y j)
    (hbudget : (∑ j ∈ s, H (y j)) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ, (∀ j ∈ s, 1 ≤ z j ∧ z j ≤ Y j) →
      (∑ j ∈ s, H (z j)) ≤ budget → (∑ j ∈ s, G (z j)) ≤ ∑ j ∈ s, G (y j))
    (k r : ℕ) (hk : k ∈ s) (hr : r ∈ s) (hkr : k ≠ r)
    (hykr : y r ≤ y k) (hactive : 1 < y r) : y k = Y k := by
  by_contra hne
  have hgap : y k < Y k := lt_of_le_of_ne (hbox k hk).2 hne
  obtain ⟨eta, heta, hfloor, hnewbox⟩ :=
    leaf_transfer_box s y Y k r hkr hbox hgap hactive
  let z := Function.update (Function.update y k (y k + eta)) r (y r - eta)
  have hexchange := leaf_pair_exchange H G hH hG (y k) (y r) eta hykr heta hfloor
  have hHsum := leaf_two_update_sum s y H k r hk hr hkr (y k + eta) (y r - eta)
  have hGsum := leaf_two_update_sum s y G k r hk hr hkr (y k + eta) (y r - eta)
  have hnewbudget : (∑ j ∈ s, H (z j)) ≤ budget := by
    change (∑ j ∈ s, H (Function.update (Function.update y k (y k + eta)) r (y r - eta) j)) ≤ budget
    rw [hHsum]
    linarith [hexchange.1]
  have hmax' := hmax z hnewbox hnewbudget
  change (∑ j ∈ s, G (Function.update (Function.update y k (y k + eta)) r (y r - eta) j)) ≤ _ at hmax'
  rw [hGsum] at hmax'
  linarith [hexchange.2]

/-- LEAF. Page 35, display 8.15, with the transformation 8.10 on page 34.
Equal exponential coordinates give equal original coordinates. -/
theorem leaf_exp_coordinates (T d e : ℝ) (hT : 0 < T)
    (h : Real.exp (d * T) = Real.exp (e * T)) : d = e := by
  exact mul_right_cancel₀ hT.ne' (Real.exp_injective h)

/-- The exact existing cited Prop for the saturation part of Theorem K.
CONDITIONAL ON cost concavity, objective strict convexity and maximality.
Maximality uses the box and budget domain without the order constraint. -/
theorem theoremK_optimalChoice_of_leaves (J r : ℕ) (d e : ℕ → ℝ) (T budget : ℝ)
    (H G : ℝ → ℝ) (hT : 0 < T) (hrJ : r ≤ J)
    (hH : ConcaveOn ℝ (Set.Ici 1) H) (hG : StrictConvexOn ℝ (Set.Ici 1) G)
    (hbox : ∀ j ∈ Finset.Icc 1 J,
      1 ≤ Real.exp (d j * T) ∧ Real.exp (d j * T) ≤ Real.exp (e j * T))
    (hbudget : (∑ j ∈ Finset.Icc 1 J, H (Real.exp (d j * T))) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ,
      (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Real.exp (e j * T)) →
      (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, G (z j)) ≤ ∑ j ∈ Finset.Icc 1 J, G (Real.exp (d j * T)))
    (hmono : AntitoneOn d (Set.Icc 1 J)) (hactive : 0 < d r) :
    TheoremK_OptimalChoice r d e := by
  intro j hj hjr
  apply leaf_exp_coordinates T (d j) (e j) hT
  apply leaf_greedy_saturation (Finset.Icc 1 J)
    (fun j => Real.exp (d j * T)) (fun j => Real.exp (e j * T)) H G budget
    hH hG hbox hbudget hmax j r
    (Finset.mem_Icc.mpr ⟨hj, (Nat.le_of_lt hjr).trans hrJ⟩)
    (Finset.mem_Icc.mpr ⟨by omega, hrJ⟩) (Nat.ne_of_lt hjr)
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (hmono ⟨hj, (Nat.le_of_lt hjr).trans hrJ⟩ ⟨by omega, hrJ⟩ (Nat.le_of_lt hjr)) hT.le
  · simpa using Real.one_lt_exp_iff.mpr (mul_pos hactive hT)

end LeanLab.Pintz2018.Decomp117b
