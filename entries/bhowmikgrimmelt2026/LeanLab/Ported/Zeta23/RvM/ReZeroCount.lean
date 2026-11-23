module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.DiscreteSubset

/-!
Ported from https://github.com/anthropics/formal-math
Commit e1a4e6508154ea59f030480661590a9fe3018011
Source path zeta23/Zeta23/RvM/ReZeroCount.lean
Author: Anthropic, PBC.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under the Apache License, Version 2.0.
SPDX-License-Identifier: Apache-2.0
The full license is in the LICENSE file at the root of this repository.
This narrow port retains only finite_zeros_closedBall.
The namespace and imports were adapted to Lean 4.35.0 and its Mathlib.
AI wrote the integration code. Goldbach is open.
-/

@[expose] public section

open Complex Set Metric

namespace LeanLab.Ported.Zeta23.RvM

/-- zeros of a function analytic on (a neighbourhood of each point of) an open ball are finite in
any closed sub-ball, given one nonvanishing point. -/
lemma finite_zeros_closedBall {f : ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hA : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball 0 R)
    (hfz₀ : f z₀ ≠ 0) : {z : ℂ | ‖z‖ ≤ r ∧ f z = 0}.Finite := by
  have hU : IsPreconnected (Metric.ball (0:ℂ) R) := (convex_ball 0 R).isPreconnected
  rcases hA.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h0 | hcod
  · exact absurd (h0 hz₀) hfz₀
  rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
  have hsub : Metric.closedBall (0:ℂ) r ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball hrR
  -- choose, for every z in the closed ball, a neighbourhood with finitely many zeros
  have hloc : ∀ z ∈ Metric.closedBall (0:ℂ) r, ∃ t ∈ nhds z,
      (t ∩ {x : ℂ | x ∈ Metric.ball (0:ℂ) R ∧ f x = 0}).Finite := by
    intro z hz
    obtain ⟨t, ht, hfin⟩ := hcod z (hsub hz)
    refine ⟨t, ht, hfin.subset ?_⟩
    rintro x ⟨hxt, hxU, hx0⟩
    exact ⟨hxt, hxU, by simpa using hx0⟩
  choose t ht hfin using hloc
  obtain ⟨I, hcover⟩ := (isCompact_closedBall (0:ℂ) r).elim_nhds_subcover' t ht
  refine ((I.finite_toSet.biUnion fun z _ => hfin z z.2).subset ?_)
  rintro x ⟨hxr, hx0⟩
  have hxball : x ∈ Metric.closedBall (0:ℂ) r := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨z, hzI, hxz⟩ := Set.mem_iUnion₂.mp (hcover hxball)
  exact Set.mem_iUnion₂.mpr ⟨z, hzI, hxz, hsub hxball, hx0⟩

end LeanLab.Ported.Zeta23.RvM
