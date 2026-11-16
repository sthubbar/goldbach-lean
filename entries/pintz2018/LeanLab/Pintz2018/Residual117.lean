module

public import LeanLab.Pintz2018.Greedy117

/-!
Budget and residual coordinate bookkeeping for Theorem K, page 18, display 4.42.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Residual117
open scoped Topology

/-- A continuous cost allows a positive coordinate increase when both the cap and budget have room.
Source: the maximization argument on page 35, after display 8.16. -/
theorem small_increase (H : ℝ → ℝ) (y cap slack : ℝ)
    (hH : ContinuousAt H y) (hcap : y < cap) (hslack : 0 < slack) :
    ∃ eta : ℝ, 0 < eta ∧ y + eta ≤ cap ∧ H (y + eta) - H y < slack := by
  have hc : ContinuousAt (fun t : ℝ => H (y + t) - H y) 0 := by
    apply ContinuousAt.sub _ continuousAt_const
    have hh : ContinuousAt H ((fun t : ℝ => y + t) 0) := by simpa using hH
    exact hh.comp (continuousAt_const.add continuousAt_id)
  have hevent : ∀ᶠ t : ℝ in nhds 0, H (y + t) - H y < slack :=
    hc.eventually_lt continuousAt_const (by simpa using hslack)
  obtain ⟨delta, hdelta, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let eta := min (cap - y) delta / 2
  have heta : 0 < eta := div_pos (lt_min (by linarith) hdelta) (by norm_num)
  have hgap : eta ≤ cap - y := by
    have := min_le_left (cap - y) delta
    dsimp [eta] at *
    linarith
  have hd : eta < delta := by
    have := min_le_right (cap - y) delta
    dsimp [eta] at *
    linarith
  refine ⟨eta, heta, by linarith, hnear ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos heta] using hd

/-- Increasing the first unsaturated coordinate up to its cap preserves decreasing order.
Source: page 35, the first deficit choice 8.16. -/
theorem increase_antitone (J k : ℕ) (y : ℕ → ℝ) (u : ℝ)
    (hmono : AntitoneOn y (Set.Icc 1 J)) (hu : y k ≤ u)
    (hprior : ∀ i ∈ Set.Icc 1 J, i < k → u ≤ y i) :
    AntitoneOn (Function.update y k u) (Set.Icc 1 J) := by
  intro i hi j hj hij
  have hm := hmono hi hj hij
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · subst j
      exact le_rfl
    · rw [Function.update_of_ne hjk, Function.update_self]
      exact hm.trans hu
  · rw [Function.update_of_ne hik]
    by_cases hjk : j = k
    · subst j
      rw [Function.update_self]
      exact hprior i hi (lt_of_le_of_ne hij hik)
    · rw [Function.update_of_ne hjk]
      exact hm

/-- A maximizing configuration with an unsaturated cap exhausts the cost budget.
Source: page 18, display 4.42, and page 35, after 8.16. -/
theorem budget_tight (J : ℕ) (y Y : ℕ → ℝ) (H G : ℝ → ℝ) (budget : ℝ)
    (hH : ∀ x : ℝ, 1 ≤ x → ContinuousAt H x)
    (hG : StrictMonoOn G (Set.Ici 1))
    (hmono : AntitoneOn y (Set.Icc 1 J)) (hY : AntitoneOn Y (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 1 ≤ y j ∧ y j ≤ Y j)
    (hdeficit : ∃ k ∈ Finset.Icc 1 J, y k < Y k)
    (hbudget : (∑ j ∈ Finset.Icc 1 J, H (y j)) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Y j) →
      AntitoneOn z (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, G (z j)) ≤ ∑ j ∈ Finset.Icc 1 J, G (y j)) :
    (∑ j ∈ Finset.Icc 1 J, H (y j)) = budget := by
  classical
  by_contra hne
  have hslack : 0 < budget - ∑ j ∈ Finset.Icc 1 J, H (y j) := by
    exact sub_pos.mpr (lt_of_le_of_ne hbudget hne)
  have hex : ∃ k : ℕ, 1 ≤ k ∧ k ≤ J ∧ y k < Y k := by
    obtain ⟨k, hk, hkgap⟩ := hdeficit
    exact ⟨k, (Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2, hkgap⟩
  let k := Nat.find hex
  have hk : 1 ≤ k ∧ k ≤ J ∧ y k < Y k := Nat.find_spec hex
  have hkfin : k ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨hk.1, hk.2.1⟩
  have hprior : ∀ i ∈ Set.Icc 1 J, i < k → Y k ≤ y i := by
    intro i hi hik
    have hsat : y i = Y i := by
      by_contra hni
      exact Nat.find_min hex hik ⟨hi.1, hi.2,
        lt_of_le_of_ne (hbox i (Finset.mem_Icc.mpr hi)).2 hni⟩
    rw [hsat]
    exact hY hi ⟨hk.1, hk.2.1⟩ hik.le
  obtain ⟨eta, heta, hcap, hcost⟩ := small_increase H (y k) (Y k)
    (budget - ∑ j ∈ Finset.Icc 1 J, H (y j))
    (hH (y k) (hbox k hkfin).1) hk.2.2 hslack
  let z := Function.update y k (y k + eta)
  have hnewbox : ∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Y j := by
    intro j hj
    by_cases hjk : j = k
    · subst j
      simp only [z, Function.update_self]
      exact ⟨by linarith [(hbox k hkfin).1], hcap⟩
    · simpa only [z, Function.update_of_ne hjk] using hbox j hj
  have hnewmono : AntitoneOn z (Set.Icc 1 J) :=
    increase_antitone J k y (y k + eta) hmono (by linarith)
      (fun i hi hik => hcap.trans (hprior i hi hik))
  have hu : ∀ f : ℝ → ℝ, (∑ j ∈ Finset.Icc 1 J, f (z j)) =
      (∑ j ∈ Finset.Icc 1 J, f (y j)) + f (y k + eta) - f (y k) := by
    intro f
    dsimp [z]
    simp_rw [Function.apply_update (fun _ => f)]
    rw [Finset.sum_update_of_mem hkfin]
    have hzero := Finset.sum_update_of_mem hkfin (fun j => f (y j)) (f (y k))
    simp only [Function.update_eq_self] at hzero
    linarith
  have hnewbudget : (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget := by
    rw [hu H]
    linarith
  have hgain : G (y k) < G (y k + eta) :=
    hG (hbox k hkfin).1 (by have := (hbox k hkfin).1; change 1 ≤ y k + eta; linarith)
      (by linarith)
  have hm := hmax z hnewbox hnewmono hnewbudget
  rw [hu G] at hm
  linarith

/-- A saturated prefix and a zero cost tail leave exactly the residual cost coordinate.
Source: page 18, display 4.42. -/
theorem residual_cost (J r : ℕ) (y Y : ℕ → ℝ) (H : ℝ → ℝ) (budget : ℝ)
    (hr : r ∈ Finset.Icc 1 J) (hzero : H 1 = 0)
    (hsat : TheoremK_OptimalChoice r y Y)
    (htail : ∀ j ∈ Set.Icc 1 J, r < j → y j = 1)
    (htight : (∑ j ∈ Finset.Icc 1 J, H (y j)) = budget) :
    H (y r) = budget - ∑ j ∈ Finset.Icc 1 (r - 1), H (Y j) := by
  have hfilter : (Finset.Icc 1 J).filter (fun j => j < r) = Finset.Icc 1 (r - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have := Finset.mem_Icc.mp hr
    omega
  have hsum : (∑ j ∈ Finset.Icc 1 J, H (y j)) =
      (∑ j ∈ Finset.Icc 1 (r - 1), H (Y j)) + H (y r) := by
    calc
      (∑ j ∈ Finset.Icc 1 J, H (y j)) =
          (∑ j ∈ Finset.Icc 1 J, if j < r then H (Y j) else 0) +
          ∑ j ∈ Finset.Icc 1 J, if j = r then H (y r) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjr : j < r
        · simp [hjr, Nat.ne_of_lt hjr, hsat j (Finset.mem_Icc.mp hj).1 hjr]
        · by_cases hje : j = r
          · subst j
            simp
          · have hrj : r < j := by omega
            simp [hjr, hje, htail j (Finset.mem_Icc.mp hj) hrj, hzero]
      _ = _ := by
        rw [← Finset.sum_filter, hfilter]
        simp [hr]
  linarith

/-- The residual cost equation determines its coordinate uniquely when the cost is strictly increasing.
Source: page 18, Remark 2 after display 4.42. -/
theorem residual_unique (H : ℝ → ℝ) (value y u : ℝ)
    (hH : StrictMonoOn H (Set.Ici 1)) (hy : 1 ≤ y) (hu : 1 ≤ u)
    (hvalue : H y = value) (huvalue : H u = value) : y = u := by
  exact hH.injOn hy hu (hvalue.trans huvalue.symm)

/-- Saturation, budget tightness and the residual equation assembled for an ordered maximizer.
Source: page 18, displays 4.41 and 4.42, with the proof on page 35. -/
theorem saturation_and_residual (J r : ℕ) (y Y : ℕ → ℝ) (H G : ℝ → ℝ) (budget : ℝ)
    (hr : r ∈ Finset.Icc 1 J) (hzero : H 1 = 0)
    (hH : ConcaveOn ℝ (Set.Ici 1) H) (hHcont : ∀ x : ℝ, 1 ≤ x → ContinuousAt H x)
    (hG : StrictConvexOn ℝ (Set.Ici 1) G) (hGmono : StrictMonoOn G (Set.Ici 1))
    (hmono : AntitoneOn y (Set.Icc 1 J)) (hY : AntitoneOn Y (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 1 ≤ y j ∧ y j ≤ Y j)
    (hactive : 1 < y r) (htail : ∀ j ∈ Set.Icc 1 J, r < j → y j = 1)
    (hdeficit : ∃ k ∈ Finset.Icc 1 J, y k < Y k)
    (hbudget : (∑ j ∈ Finset.Icc 1 J, H (y j)) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Y j) →
      AntitoneOn z (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, G (z j)) ≤ ∑ j ∈ Finset.Icc 1 J, G (y j)) :
    TheoremK_OptimalChoice r y Y ∧
      (∑ j ∈ Finset.Icc 1 J, H (y j)) = budget ∧
      H (y r) = budget - ∑ j ∈ Finset.Icc 1 (r - 1), H (Y j) := by
  have hs := Ordered117.saturation_ordered J r y Y H G budget hr hH hG hmono hY
    hbox hactive htail hbudget hmax
  have ht := budget_tight J y Y H G budget hHcont hGmono hmono hY hbox hdeficit hbudget hmax
  exact ⟨hs, ht, residual_cost J r y Y H budget hr hzero hs htail ht⟩

end LeanLab.Pintz2018.Residual117
