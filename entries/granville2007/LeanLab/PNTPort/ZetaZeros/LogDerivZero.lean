module

public import Mathlib

/-!
# The residue of `f'/f` at a zero of order `m` is `m`

Lab proof, unit U-5276, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics, no
cited input. `tendsto_mul_logDeriv`: if `f` is analytic at `ρ` with `analyticOrderAt f ρ = m`,
then `(s - ρ) f'(s)/f(s) → m` as `s → ρ`, `s ≠ ρ`. With `f = ζ` this is the residue `m(ρ)` of
`ζ'/ζ` at a zero, the input the ported rectangle residue theorem
`RectangleIntegral'_eq_sumResiduesIn` needs for an explicit formula with all zeros.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Filter Topology

theorem tendsto_mul_logDeriv {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ} (hf : AnalyticAt ℂ f ρ)
    (hord : analyticOrderAt f ρ = m) :
    Tendsto (fun s => (s - ρ) * (deriv f s / f s)) (𝓝[≠] ρ) (𝓝 (m : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast).mp hord
  simp only [smul_eq_mul] at hfg
  -- near `ρ`, `f = (s - ρ)^m g` and `f' = m (s - ρ)^(m-1) g + (s - ρ)^m g'`
  have hfg' : ∀ᶠ s in 𝓝 ρ, ∀ᶠ u in 𝓝 s, f u = (u - ρ) ^ m * g u := hfg.eventually_nhds
  have hgev : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have hg0ev : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have key : ∀ᶠ s in 𝓝[≠] ρ, (s - ρ) * (deriv f s / f s) = m + (s - ρ) * (deriv g s / g s) := by
    filter_upwards [nhdsWithin_le_nhds hfg', nhdsWithin_le_nhds hgev, nhdsWithin_le_nhds hg0ev,
      self_mem_nhdsWithin] with s hs hgs hg0s hsρ
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    have hd : HasDerivAt (fun u => (u - ρ) ^ m * g u)
        ((m : ℂ) * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      (((hasDerivAt_id s).sub_const ρ).pow m).mul hgs.differentiableAt.hasDerivAt
    have hderiv : deriv f s = (m : ℂ) * (s - ρ) ^ (m - 1) * g s + (s - ρ) ^ m * deriv g s := by
      rw [(hd.congr_of_eventuallyEq hs).deriv]; ring
    have hfs : f s = (s - ρ) ^ m * g s := hs.self_of_nhds
    rw [hderiv, hfs]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp
    · have hpow : (s - ρ) ^ m = (s - ρ) ^ (m - 1) * (s - ρ) := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow]
      field_simp
  refine Tendsto.congr' (EventuallyEq.symm key) ?_
  have hcont : ContinuousAt (fun s => (s - ρ) * (deriv g s / g s)) ρ := by
    apply ContinuousAt.mul (by fun_prop)
    exact (hg.deriv.continuousAt).div hg.continuousAt hg0
  have h0 : (fun s => (s - ρ) * (deriv g s / g s)) ρ = 0 := by simp
  have ht : Tendsto (fun s => (s - ρ) * (deriv g s / g s)) (𝓝[≠] ρ) (𝓝 0) := by
    have := hcont.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (tendsto_const_nhds (x := (m : ℂ)) (f := 𝓝[≠] ρ)).add ht
  rw [add_zero] at h2
  exact h2

end LeanLab.PNTPort.ZetaZeros

