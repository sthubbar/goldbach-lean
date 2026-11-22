module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.KadiriLumley2014.RowDefinition92
public import LeanLab.KadiriLumley2014.Decomp92
public import LeanLab.KadiriLumley2014.Corollary
public import LeanLab.KadiriLumley2014.CostaSplit
public import LeanLab.KadiriLumley2014.BrunTitchmarshMV

/-!
Kadiri and Lumley 2014, one row of Table 2 of Theorem 1.1 from explicit inputs.
Every external input is an explicit hypothesis: the Costa Pereira bound of Lemma 2.1, the
Montgomery and Vaughan inequality, and display 2.64 of the paper at the row's least admissible
normalized `X`. The proof follows section 2 of the paper through the lemmas of Decomp92.
AI wrote this Lean code. Binary Goldbach is open; this file says nothing new about it.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.PalomarEntry
open Real Set MeasureTheory
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- One row of Table 2 of Theorem 1.1, from the Costa Pereira bound `CostaEstimate`, the
Montgomery and Vaughan Brun Titchmarsh inequality, and display 2.64 of the paper at this row's
least admissible normalized `X`, each an explicit hypothesis. -/
theorem row_of_inputs (hC : CostaEstimate)
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    {r : PrintedRow} (hr : r ∈ tableTwo)
    (hE : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    KLRow r.threshold r.gapDenom := by
  intro x hx
  obtain ⟨a, ha, hD⟩ := tableTwo_rounding_consistent hr
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : 1 / (10 : ℝ) ^ 12 ≤ r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    norm_num at h ⊢
    exact h
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hu0 : (0 : ℝ) < r.uQ := by linarith
  have hrpar := (tableTwo_rounding_arithmetic r hr).1
  have haQ : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hrpar.2.2.2.1
  have hbQ : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
    have hb := (Rat.cast_le (K := ℝ)).mpr hrpar.2.2.2.2.1
    push_cast at hb
    norm_num at hb ⊢
    exact hb
  have ha0 : 0 ≤ a := haQ.trans ha.1
  have ha2 : a ≤ 1 / 2 := ha.2.trans hbQ
  have hxbase : (4 * 10 ^ 18 : ℝ) < x :=
    lt_of_le_of_lt (by
      have h := tableTwo_threshold_ge_base hr
      norm_num [evenBase] at h ⊢
      exact h) hx
  let X : ℝ := x / (Real.exp r.uQ * (1 + (r.deltaQ : ℝ) * (1 - a)))
  obtain ⟨hX0, hX38, hgap, htop⟩ := normalized_domain hδ.le hδ1 hu hu1 ha0 ha2 hxbase
  change 0 < X at hX0
  change Real.exp 38 ≤ X at hX38
  change 1 < X * (Real.exp r.uQ - 1) at hgap
  change Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a))) = x at htop
  have htail : tailThetaIntegral r.m r.deltaQ r.uQ X a ≤
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a :=
    tail_bound_of_pointwise r.m hδ.le ((Real.exp_pos 38).le.trans hX38) ha0 ha2
      (fun t ht => BrunTitchmarshMV.brun_titchmarsh_pointwise_of_MV hMV hδ.le hδ1 hu0 hu1
        hX38 hgap ht)
  -- the zero sum budget at X, from display 2.64 at the row endpoint
  have hxX : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a))) := by
    rwa [htop]
  obtain ⟨hY38, hYX, hgapY⟩ := rowEndpointX_domain hr ha hX38 hxX
  have hm : 0 < r.m := by have := (tableTwo_parameters r hr).1; omega
  have hb := zero_budget_of_endpoint hm hδ hu0 ha0 ha.2 hbQ hY38 hYX hgapY hE
  -- the psi margin at X
  have hl := (smoothed_explicit_lower (tableTwo_parameters r hr).1 hδ hδ1 hu0 hu1 hX38).2
  have hmargin : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) < psiAverage r.m r.deltaQ r.uQ X := by
    linarith
  have hpos := central_positive_of_psi_margin hC r.m hδ.le hδ1 hu0.le hu1
    hX38 ha0 ha2 htail hmargin
  obtain ⟨p, hp, hlo, hhi⟩ := prime_of_smoothing hδ hu0.le hX0 ha0 ha2 hpos
  have hB : 1 + (r.deltaQ : ℝ) * (1 - a) ≠ 0 := by
    have : 0 ≤ (r.deltaQ : ℝ) * (1 - a) := mul_nonneg hδ.le (by linarith)
    positivity
  have hlow := lower_endpoint_identity (X := X) hB hD
  rw [htop] at hlow hhi
  exact ⟨p, hp, by rwa [hlow], hhi⟩

end LeanLab.KadiriLumley2014.PalomarEntry
