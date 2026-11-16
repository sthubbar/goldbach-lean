module

public import LeanLab.Pintz2018.Decomp117b

/-!
The ordered exchange in Pintz 2018, page 35, displays 8.15 and 8.16.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Ordered117

/-- The first unsaturated coordinate and the last active coordinate permit an ordered transfer.
Source: page 35, the argument after display 8.16. -/
theorem transfer_antitone (J k r : ℕ) (y Y : ℕ → ℝ) (eta : ℝ)
    (hmono : AntitoneOn y (Set.Icc 1 J)) (hkr : k < r) (heta : 0 ≤ eta)
    (hcap : y k + eta ≤ Y k) (hfloor : 1 ≤ y r - eta)
    (hprior : ∀ i ∈ Set.Icc 1 J, i < k → Y k ≤ y i)
    (htail : ∀ j ∈ Set.Icc 1 J, r < j → y j = 1) :
    AntitoneOn (Function.update (Function.update y k (y k + eta)) r (y r - eta))
      (Set.Icc 1 J) := by
  intro i hi j hj hij
  have hm := hmono hi hj hij
  by_cases hir : i = r
  · subst i
    by_cases hjr : j = r
    · subst j
      exact le_rfl
    · have hrj : r < j := lt_of_le_of_ne hij (Ne.symm hjr)
      have hjk : j ≠ k := by omega
      rw [Function.update_of_ne hjr, Function.update_of_ne hjk, Function.update_self]
      rw [htail j hj hrj]
      exact hfloor
  · by_cases hik : i = k
    · subst i
      rw [Function.update_of_ne (Nat.ne_of_lt hkr), Function.update_self]
      by_cases hjr : j = r
      · subst j
        rw [Function.update_self]
        linarith
      · rw [Function.update_of_ne hjr]
        by_cases hjk : j = k
        · subst j
          simp only [Function.update_self, le_refl]
        · rw [Function.update_of_ne hjk]
          linarith
    · rw [Function.update_of_ne hir, Function.update_of_ne hik]
      by_cases hjr : j = r
      · subst j
        rw [Function.update_self]
        linarith
      · rw [Function.update_of_ne hjr]
        by_cases hjk : j = k
        · subst j
          rw [Function.update_self]
          exact hcap.trans (hprior i hi (lt_of_le_of_ne hij hik))
        · rw [Function.update_of_ne hjk]
          exact hm

/-- Saturation in the paper's ordered feasible domain.
Source: page 35, displays 8.15 and 8.16. -/
theorem saturation_ordered (J r : ℕ) (y Y : ℕ → ℝ) (H G : ℝ → ℝ) (budget : ℝ)
    (hr : r ∈ Finset.Icc 1 J)
    (hH : ConcaveOn ℝ (Set.Ici 1) H) (hG : StrictConvexOn ℝ (Set.Ici 1) G)
    (hmono : AntitoneOn y (Set.Icc 1 J)) (hY : AntitoneOn Y (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 1 ≤ y j ∧ y j ≤ Y j)
    (hactive : 1 < y r) (htail : ∀ j ∈ Set.Icc 1 J, r < j → y j = 1)
    (hbudget : (∑ j ∈ Finset.Icc 1 J, H (y j)) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Y j) →
      AntitoneOn z (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, G (z j)) ≤ ∑ j ∈ Finset.Icc 1 J, G (y j)) :
    TheoremK_OptimalChoice r y Y := by
  classical
  intro j hj hjr
  have hrJ := (Finset.mem_Icc.mp hr).2
  by_contra hne
  have hex : ∃ k : ℕ, 1 ≤ k ∧ k < r ∧ y k < Y k :=
    ⟨j, hj, hjr, lt_of_le_of_ne
      (hbox j (Finset.mem_Icc.mpr ⟨hj, by omega⟩)).2 hne⟩
  let k := Nat.find hex
  have hk : 1 ≤ k ∧ k < r ∧ y k < Y k := Nat.find_spec hex
  have hkfin : k ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨hk.1, by omega⟩
  have hkneq : k ≠ r := Nat.ne_of_lt hk.2.1
  have hprior : ∀ i ∈ Set.Icc 1 J, i < k → Y k ≤ y i := by
    intro i hi hik
    have hsat : y i = Y i := by
      have hle := (hbox i (Finset.mem_Icc.mpr hi)).2
      by_contra hni
      exact Nat.find_min hex hik ⟨hi.1, by omega, lt_of_le_of_ne hle hni⟩
    rw [hsat]
    exact hY hi (Finset.mem_Icc.mp hkfin) hik.le
  obtain ⟨eta, heta, hfloor, hnewbox⟩ :=
    Decomp117b.leaf_transfer_box (Finset.Icc 1 J) y Y k r hkneq hbox hk.2.2 hactive
  have hcap : y k + eta ≤ Y k := by
    simpa only [Function.update_of_ne hkneq, Function.update_self] using (hnewbox k hkfin).2
  let z := Function.update (Function.update y k (y k + eta)) r (y r - eta)
  have hnewmono : AntitoneOn z (Set.Icc 1 J) :=
    transfer_antitone J k r y Y eta hmono hk.2.1 heta.le hcap hfloor hprior htail
  have hx := Decomp117b.leaf_pair_exchange H G hH hG (y k) (y r) eta
    (hmono (Finset.mem_Icc.mp hkfin) (Finset.mem_Icc.mp hr) hk.2.1.le) heta hfloor
  have hHsum := Decomp117b.leaf_two_update_sum (Finset.Icc 1 J) y H k r hkfin hr hkneq
    (y k + eta) (y r - eta)
  have hGsum := Decomp117b.leaf_two_update_sum (Finset.Icc 1 J) y G k r hkfin hr hkneq
    (y k + eta) (y r - eta)
  have hnewbudget : (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget := by
    change (∑ j ∈ Finset.Icc 1 J, H (Function.update (Function.update y k (y k + eta)) r (y r - eta) j)) ≤ budget
    rw [hHsum]
    linarith [hx.1]
  have hm := hmax z hnewbox hnewmono hnewbudget
  change (∑ j ∈ Finset.Icc 1 J, G (Function.update (Function.update y k (y k + eta)) r (y r - eta) j)) ≤ _ at hm
  rw [hGsum] at hm
  linarith [hx.2]

end LeanLab.Pintz2018.Ordered117
