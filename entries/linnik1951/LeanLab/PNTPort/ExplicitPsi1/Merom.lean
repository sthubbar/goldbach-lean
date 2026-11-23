module

public import Mathlib

/-!
# ζ is meromorphic, with a simple pole at 1, and the residues of ζ'/ζ

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input.

* `meromorphicAt_zeta`: ζ is meromorphic at every point, from
  `ζ s = (Λ₀(s) - 1/s - 1/(1 - s)) / Γℝ(s)` for `s ≠ 0`.
* `order_zeta_one`: the meromorphic order of ζ at 1 is `-1`.
* `order_zeta_ne_top`: ζ is not locally zero anywhere.
* `tendsto_mul_logDeriv_mero`: if `f` has meromorphic order `n` at `p`, then
  `(s - p) f'(s)/f(s) → n`; it generalizes `ZetaZeros.tendsto_mul_logDeriv` from zeros to poles.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology

local notation "ζ" => riemannZeta

/-- `ζ s = (Λ₀ s - 1/s - 1/(1 - s)) · Γℝ(s)⁻¹` for `s ≠ 0`. -/
lemma zeta_eq_completed {s : ℂ} (hs : s ≠ 0) :
    ζ s = (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) * (Gammaℝ s)⁻¹ := by
  rw [riemannZeta_def_of_ne_zero hs, completedRiemannZeta_eq, div_eq_mul_inv]

lemma eventually_ne_zero_nhdsNE (p : ℂ) : ∀ᶠ s in 𝓝[≠] p, s ≠ 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (eventually_ne_nhds hp)

theorem meromorphicAt_zeta (p : ℂ) : MeromorphicAt ζ p := by
  have h0 : MeromorphicAt completedRiemannZeta₀ p :=
    (differentiable_completedZeta₀.analyticAt p).meromorphicAt
  have hG : MeromorphicAt (fun s => (Gammaℝ s)⁻¹) p :=
    (differentiable_Gammaℝ_inv.analyticAt p).meromorphicAt
  have hid : MeromorphicAt (fun s : ℂ => s) p := analyticAt_id.meromorphicAt
  have hA : MeromorphicAt
      (fun s => (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) * (Gammaℝ s)⁻¹) p := by
    apply MeromorphicAt.mul _ hG
    apply MeromorphicAt.sub (MeromorphicAt.sub h0 ((MeromorphicAt.const 1 p).div hid))
    exact (MeromorphicAt.const 1 p).div ((MeromorphicAt.const 1 p).sub hid)
  refine hA.congr ?_
  filter_upwards [eventually_ne_zero_nhdsNE p] with s hs
  exact (zeta_eq_completed hs).symm

theorem order_zeta_one : meromorphicOrderAt ζ 1 = -1 := by
  show meromorphicOrderAt ζ 1 = ((-1 : ℤ) : WithTop ℤ)
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_zeta 1)]
  refine ⟨fun s => (s - 1) * (completedRiemannZeta₀ s - 1 / s) * (Gammaℝ s)⁻¹ + (Gammaℝ s)⁻¹,
    ?_, ?_, ?_⟩
  · have hG : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) 1 := differentiable_Gammaℝ_inv.analyticAt 1
    have h0 : AnalyticAt ℂ completedRiemannZeta₀ 1 := differentiable_completedZeta₀.analyticAt 1
    have hinv : AnalyticAt ℂ (fun s : ℂ => 1 / s) 1 :=
      analyticAt_const.div analyticAt_id one_ne_zero
    exact ((((analyticAt_id.sub analyticAt_const).mul (h0.sub hinv))).mul hG).add hG
  · simp [Gammaℝ_one]
  · filter_upwards [self_mem_nhdsWithin, eventually_ne_zero_nhdsNE 1] with s hs1 hs0
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hs1'' : 1 - s ≠ 0 := by intro h; apply hs1'; linear_combination -h
    rw [zeta_eq_completed hs0, zpow_neg_one, smul_eq_mul]
    field_simp
    ring

lemma analyticAt_zeta {p : ℂ} (hp : p ≠ 1) : AnalyticAt ℂ ζ p :=
  analyticOn_riemannZeta p hp

lemma analyticOrderAt_zeta_ne_top {p : ℂ} (hp : p ≠ 1) : analyticOrderAt ζ p ≠ ⊤ := by
  have hU : AnalyticOnNhd ℂ ζ ({1}ᶜ : Set ℂ) := fun z hz => analyticAt_zeta hz
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have h2 : analyticOrderAt ζ 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    simp
  exact hU.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := p)
    (by simp) (by simpa using hp) h2

/-- Away from 1 the meromorphic order of ζ is its analytic order, a natural number. -/
theorem order_zeta_of_ne_one {p : ℂ} (hp : p ≠ 1) :
    meromorphicOrderAt ζ p = (analyticOrderNatAt ζ p : ℤ) := by
  rw [(analyticAt_zeta hp).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_zeta_ne_top hp)
  rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
  simp

theorem order_zeta_ne_top (p : ℂ) : meromorphicOrderAt ζ p ≠ ⊤ := by
  rcases eq_or_ne p 1 with rfl | hp
  · rw [order_zeta_one]; simp
  · rw [order_zeta_of_ne_one hp]; simp

/-- If `f` has meromorphic order `n` at `p`, then `(s - p) f'(s)/f(s) → n` as `s → p`. -/
theorem tendsto_mul_logDeriv_mero {f : ℂ → ℂ} {p : ℂ} {n : ℤ} (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = n) :
    Tendsto (fun s => (s - p) * (deriv f s / f s)) (𝓝[≠] p) (𝓝 (n : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  simp only [smul_eq_mul] at hfg
  have hfg' : ∀ᶠ s in 𝓝[≠] p, ∀ᶠ u in 𝓝 s, f u = (u - p) ^ n * g u := by
    have := eventually_eventually_nhdsWithin.mpr hfg
    filter_upwards [this, self_mem_nhdsWithin] with s hs hsp
    rwa [nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds hsp)] at hs
  have hgev : ∀ᶠ s in 𝓝 p, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have hg0ev : ∀ᶠ s in 𝓝 p, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have key : ∀ᶠ s in 𝓝[≠] p, (s - p) * (deriv f s / f s) = n + (s - p) * (deriv g s / g s) := by
    filter_upwards [hfg', nhdsWithin_le_nhds hgev, nhdsWithin_le_nhds hg0ev,
      self_mem_nhdsWithin] with s hs hgs hg0s hsp
    have hw : s - p ≠ 0 := sub_ne_zero.mpr hsp
    have hz : HasDerivAt (fun u : ℂ => (u - p) ^ n) ((n : ℂ) * (s - p) ^ (n - 1) * 1) s :=
      by
        have h1 : HasDerivAt (fun u : ℂ => u - p) 1 s := (hasDerivAt_id' s).sub_const p
        exact (hasDerivAt_zpow n (s - p) (Or.inl hw)).comp s h1
    have hd : HasDerivAt (fun u => (u - p) ^ n * g u)
        ((n : ℂ) * (s - p) ^ (n - 1) * 1 * g s + (s - p) ^ n * deriv g s) s :=
      hz.mul hgs.differentiableAt.hasDerivAt
    have hderiv : deriv f s = (n : ℂ) * (s - p) ^ (n - 1) * g s + (s - p) ^ n * deriv g s := by
      rw [(hd.congr_of_eventuallyEq hs).deriv]; ring
    have hfs : f s = (s - p) ^ n * g s := hs.self_of_nhds
    have hpow : (s - p) ^ n = (s - p) ^ (n - 1) * (s - p) := by
      rw [zpow_sub_one₀ hw]; field_simp
    have hne : (s - p) ^ (n - 1) ≠ 0 := zpow_ne_zero _ hw
    rw [hderiv, hfs, hpow]
    field_simp
  refine Tendsto.congr' (EventuallyEq.symm key) ?_
  have hcont : ContinuousAt (fun s => (s - p) * (deriv g s / g s)) p := by
    apply ContinuousAt.mul (by fun_prop)
    exact (hg.deriv.continuousAt).div hg.continuousAt hg0
  have ht : Tendsto (fun s => (s - p) * (deriv g s / g s)) (𝓝[≠] p) (𝓝 0) := by
    have := hcont.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (tendsto_const_nhds (x := (n : ℂ)) (f := 𝓝[≠] p)).add ht
  rw [add_zero] at h2
  exact h2

/-- The residue of `ζ'/ζ` at 1 is `-1`. -/
theorem tendsto_logDeriv_zeta_one :
    Tendsto (fun s => (s - 1) * (deriv ζ s / ζ s)) (𝓝[≠] 1) (𝓝 (-1 : ℂ)) := by
  have := tendsto_mul_logDeriv_mero (meromorphicAt_zeta 1) order_zeta_one
  simpa using this

/-- The residue of `ζ'/ζ` at a point `ρ ≠ 1` is the order of ζ there. -/
theorem tendsto_logDeriv_zeta_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    Tendsto (fun s => (s - ρ) * (deriv ζ s / ζ s)) (𝓝[≠] ρ)
      (𝓝 (analyticOrderNatAt ζ ρ : ℂ)) := by
  have := tendsto_mul_logDeriv_mero (meromorphicAt_zeta ρ) (order_zeta_of_ne_one hρ)
  simpa using this

/-- `ζ'/ζ` has at most simple poles. -/
theorem order_logDeriv_zeta_ge (p : ℂ) : -1 ≤ meromorphicOrderAt (logDeriv ζ) p := by
  by_cases h : meromorphicOrderAt ζ p = 0
  · refine le_trans ?_ (meromorphicOrderAt_logDeriv_nonneg (meromorphicAt_zeta p) h)
    exact WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)
  · rw [meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_zeta p) h (order_zeta_ne_top p)]

end LeanLab.PNTPort.ExplicitPsi1

