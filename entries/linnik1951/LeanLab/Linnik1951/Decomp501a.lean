module

public import LeanLab.Linnik1951.Repair493ContourData
public import LeanLab.Linnik1951.Repair493PositiveKernel
public import LeanLab.Linnik1951.Decomp452g

/-!
P0093 pages 157 and 158. Signed finite alpha frequency estimates.
The sealed finite square split declarations move here from SPLIT_outer_finite_square487.
The new helpers retain the diagonal scale and preserve frequency cancellation.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

set_option maxHeartbeats 1600000

/-- The Mellin kernel is continuous in the pair (alpha, t). -/
private theorem continuous_mellinKernel487 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hline : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    dsimp [mellinLine1622]; fun_prop
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hline.continuousAt
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hh
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlog0 : (0 : ℝ) ≤ 1 / Real.log (N : ℝ) :=
      div_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)))
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    refine Or.inl ?_
    have hre : (Z p.1).re = 1 / (N : ℝ) := by
      simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hre]
    exact div_pos one_pos hNpos
  exact ((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)

/-- The alpha integral of the kernel product is continuous in the frequency pair. -/
private theorem continuous_alphaKernel_integral487 (N : ℕ) (hN : 1 ≤ N) (a b : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ α in a..b,
      mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)) := by
  let f : (ℝ × ℝ) → ℝ → ℂ := fun p α =>
    mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)
  have h := continuous_mellinKernel487 N hN
  have hu : Continuous (Function.uncurry f) := by
    change Continuous (fun q : (ℝ × ℝ) × ℝ =>
      mellinKernel442 N q.2 q.1.1 * (starRingEnd ℂ) (mellinKernel442 N q.2 q.1.2))
    exact (h.comp (continuous_snd.prodMk continuous_fst.fst)).mul
      (h.comp (continuous_snd.prodMk continuous_fst.snd)).star
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := f) (μ := volume) hu a b
  exact hc

/-- An iterated interval integral over a square is the set integral over the product box. -/
private theorem iterated_eq_box487 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → ℝ → E) (a b : ℝ)
    (hF : IntegrableOn (Function.uncurry F) (Set.uIoc a b ×ˢ Set.uIoc a b)) :
    (∫ t in a..b, ∫ u in a..b, F t u) =
      ∫ z in (Set.uIoc a b ×ˢ Set.uIoc a b), F z.1 z.2 := by
  rcases le_total a b with h | h
  · rw [Set.uIoc_of_le h] at hF
    calc (∫ t in a..b, ∫ u in a..b, F t u)
        = ∫ t in Set.Ioc a b, ∫ u in Set.Ioc a b, F t u := by
          simp_rw [intervalIntegral.integral_of_le h]
      _ = ∫ z in (Set.uIoc a b ×ˢ Set.uIoc a b), F z.1 z.2 := by
          rw [Set.uIoc_of_le h]
          exact (setIntegral_prod (fun z : ℝ × ℝ => F z.1 z.2) hF).symm
  · rw [Set.uIoc_of_ge h] at hF
    calc (∫ t in a..b, ∫ u in a..b, F t u)
        = ∫ t in a..b, (-∫ u in Set.Ioc b a, F t u) := by
          apply intervalIntegral.integral_congr
          intro t _
          exact intervalIntegral.integral_of_ge h
      _ = -∫ t in a..b, (∫ u in Set.Ioc b a, F t u) :=
          intervalIntegral.integral_neg
      _ = -(-∫ t in Set.Ioc b a, (∫ u in Set.Ioc b a, F t u)) := by
          rw [intervalIntegral.integral_of_ge h]
      _ = ∫ t in Set.Ioc b a, ∫ u in Set.Ioc b a, F t u := by rw [neg_neg]
      _ = ∫ z in (Set.uIoc a b ×ˢ Set.uIoc a b), F z.1 z.2 := by
          rw [Set.uIoc_of_ge h]
          exact (setIntegral_prod (fun z : ℝ × ℝ => F z.1 z.2) hF).symm

/-- Split a double interval integral over a square at the sign of the sum of the variables. -/
private theorem region_split_aux487 (T : ℝ) (G : ℝ → ℝ → ℝ)
    (hG : Continuous (Function.uncurry G)) :
    (∫ t in -T..T, ∫ u in -T..T, G t u) =
      (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then G t u else 0) +
      (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then 0 else G t u) := by
  set S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 + p.2} with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  have hBmeas : MeasurableSet (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) :=
    measurableSet_uIoc.prod measurableSet_uIoc
  have hGmeas : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := hG.measurable
  have hGint : IntegrableOn (Function.uncurry G) (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) :=
    (hG.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hGint' : Integrable (Function.uncurry G)
      (volume.restrict (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T)) := hGint
  have hind1 : IntegrableOn (S.indicator (Function.uncurry G))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    refine Integrable.mono' hGint'.norm (hGmeas.indicator hSmeas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => norm_indicator_le_norm_self _ p)
  have hind2 : IntegrableOn (Sᶜ.indicator (Function.uncurry G))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    refine Integrable.mono' hGint'.norm (hGmeas.indicator hSmeas.compl).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => norm_indicator_le_norm_self _ p)
  have hfun1 : (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then G p.1 p.2 else 0) =
      S.indicator (Function.uncurry G) := by
    funext p
    by_cases h : 0 ≤ p.1 + p.2
    · rw [if_pos h, Set.indicator_of_mem (f := Function.uncurry G)
        (show p ∈ S from by simpa [hS] using h)]
      rfl
    · rw [if_neg h, Set.indicator_of_notMem (f := Function.uncurry G)
        (show p ∉ S from by simpa [hS] using h)]
  have hfun2 : (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then 0 else G p.1 p.2) =
      Sᶜ.indicator (Function.uncurry G) := by
    funext p
    by_cases h : 0 ≤ p.1 + p.2
    · rw [if_pos h, Set.indicator_of_notMem (f := Function.uncurry G)
        (show p ∉ Sᶜ from fun hp => hp (show p ∈ S from by simpa [hS] using h))]
    · rw [if_neg h, Set.indicator_of_mem (f := Function.uncurry G)
        (show p ∈ Sᶜ from by simpa [hS] using h)]
      rfl
  have hp1 : IntegrableOn (Function.uncurry (fun t u => if 0 ≤ t + u then G t u else 0))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    have he : Function.uncurry (fun t u => if 0 ≤ t + u then G t u else 0)
        = (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then G p.1 p.2 else 0) := rfl
    rw [he, hfun1]
    exact hind1
  have hp2 : IntegrableOn (Function.uncurry (fun t u => if 0 ≤ t + u then 0 else G t u))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    have he : Function.uncurry (fun t u => if 0 ≤ t + u then 0 else G t u)
        = (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then 0 else G p.1 p.2) := rfl
    rw [he, hfun2]
    exact hind2
  have hpiece1 : (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then G t u else 0) =
      ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T),
        S.indicator (Function.uncurry G) z := by
    rw [iterated_eq_box487 (fun t u => if 0 ≤ t + u then G t u else 0) (-T) T hp1, hfun1]
  have hpiece2 : (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then 0 else G t u) =
      ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T),
        Sᶜ.indicator (Function.uncurry G) z := by
    rw [iterated_eq_box487 (fun t u => if 0 ≤ t + u then 0 else G t u) (-T) T hp2, hfun2]
  have hBsplit : (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), Function.uncurry G z) =
      (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), S.indicator (Function.uncurry G) z) +
      (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T),
        Sᶜ.indicator (Function.uncurry G) z) := by
    have hdisj : Disjoint ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ S)
        ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ Sᶜ) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have hun : ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ S) ∪
        ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ Sᶜ) =
        Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    have key := setIntegral_union (μ := volume) hdisj (hBmeas.inter hSmeas.compl)
      (hGint.mono_set Set.inter_subset_left) (hGint.mono_set Set.inter_subset_left)
    rw [hun] at key
    rw [key, setIntegral_indicator (s := Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T)
        (f := Function.uncurry G) hSmeas,
      setIntegral_indicator (s := Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T)
        (f := Function.uncurry G) hSmeas.compl]
  have hboxG : (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), Function.uncurry G z) =
      (∫ t in -T..T, ∫ u in -T..T, G t u) :=
    (iterated_eq_box487 G (-T) T hGint).symm
  rw [← hboxG, hBsplit, ← hpiece1, ← hpiece2]

/-- Sharp modulus of one power factor of the Mellin kernel. -/
private theorem norm_cpow_mellin487 (N : ℕ) (hN : 3 ≤ N) {z : ℂ} (hz : z ≠ 0)
    (t : ℝ) :
    ‖z ^ (-(mellinLine1622 N t))‖ =
      ‖z‖ ^ (-(1 / 2 + 1 / Real.log (N : ℝ))) * Real.exp (t * z.arg) := by
  have hlog : Complex.log z = (Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im]
  have hre : (Complex.log z * (-(mellinLine1622 N t))).re =
      -((1 / 2 + 1 / Real.log (N : ℝ)) * Real.log ‖z‖) + t * z.arg := by
    rw [hlog]
    simp only [mellinLine1622, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      sub_zero, zero_add]
    ring
  have hpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  calc ‖z ^ (-(mellinLine1622 N t))‖
      = Real.exp ((Complex.log z * (-(mellinLine1622 N t))).re) := by
        rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
    _ = Real.exp (-((1 / 2 + 1 / Real.log (N : ℝ)) * Real.log ‖z‖)) *
          Real.exp (t * z.arg) := by
        rw [hre, Real.exp_add]
    _ = ‖z‖ ^ (-(1 / 2 + 1 / Real.log (N : ℝ))) * Real.exp (t * z.arg) := by
        rw [Real.rpow_def_of_pos hpos]
        congr 1
        ring

/-- The pair of conjugate power factors at two frequencies, with the sum exponent. -/
private theorem norm_cpow_pair487 (N : ℕ) (hN : 3 ≤ N) {z : ℂ} (hz : z ≠ 0)
    (hzre : z.re = 1 / (N : ℝ)) (t u : ℝ) :
    ‖z ^ (-(mellinLine1622 N t)) * (starRingEnd ℂ) (z ^ (-(mellinLine1622 N u)))‖ ≤
      Real.exp 2 * (N : ℝ) * Real.exp ((t + u) * z.arg) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  set σ : ℝ := 1 / 2 + 1 / Real.log (N : ℝ) with hσ
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hnt : ‖z‖ ^ (-σ) ≤ (N : ℝ) ^ σ := by
    have hznorm : (1 / (N : ℝ)) ≤ ‖z‖ := by
      have h1 := Complex.abs_re_le_norm z
      rw [hzre] at h1
      rwa [abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))] at h1
    have hstep := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 / (N : ℝ)) hznorm
      (show -σ ≤ 0 from by linarith)
    have hbase : ((1 : ℝ) / (N : ℝ)) ^ (-σ) = (N : ℝ) ^ σ := by
      rw [one_div, Real.inv_rpow hNpos.le, ← Real.rpow_neg]
      · ring_nf
      · exact hNpos.le
    rwa [hbase] at hstep
  have hNpow : (N : ℝ) ^ σ = Real.exp 1 * Real.sqrt N := by
    have hadd : (N : ℝ) ^ σ =
        (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / Real.log (N : ℝ)) := by
      rw [hσ, Real.rpow_add hNpos]
    rw [hadd, ← Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos,
      show Real.log (N : ℝ) * (1 / Real.log (N : ℝ)) = 1 from by field_simp]
    ring
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have e1 := norm_cpow_mellin487 N hN hz t
  have e2 := norm_cpow_mellin487 N hN hz u
  rw [norm_mul, Complex.norm_conj, e1, e2]
  change ‖z‖ ^ (-σ) * Real.exp (t * z.arg) *
      (‖z‖ ^ (-σ) * Real.exp (u * z.arg)) ≤
    Real.exp 2 * (N : ℝ) * Real.exp ((t + u) * z.arg)
  have hprod : (‖z‖ ^ (-σ) * Real.exp (t * z.arg)) *
      (‖z‖ ^ (-σ) * Real.exp (u * z.arg)) =
      (‖z‖ ^ (-σ) * ‖z‖ ^ (-σ)) * (Real.exp (t * z.arg) * Real.exp (u * z.arg)) := by
    ring
  rw [hprod]
  have hmono : ‖z‖ ^ (-σ) * ‖z‖ ^ (-σ) ≤ (N : ℝ) ^ σ * (N : ℝ) ^ σ :=
    mul_le_mul hnt hnt (Real.rpow_nonneg (norm_nonneg z) _) (Real.rpow_nonneg hNpos.le _)
  have hexpadd : Real.exp (t * z.arg) * Real.exp (u * z.arg) =
      Real.exp ((t + u) * z.arg) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexpadd]
  refine le_trans (mul_le_mul hmono le_rfl (Real.exp_pos _).le (by positivity)) ?_
  rw [hexp2, hNpow]
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
    rw [← sq, Real.sq_sqrt hNpos.le]
  have hstep : Real.exp 1 * Real.sqrt (N : ℝ) * (Real.exp 1 * Real.sqrt (N : ℝ)) *
        Real.exp ((t + u) * z.arg) =
      Real.exp 1 * Real.exp 1 * (N : ℝ) * Real.exp ((t + u) * z.arg) := by
    rw [show Real.exp 1 * Real.sqrt (N : ℝ) * (Real.exp 1 * Real.sqrt (N : ℝ))
        = Real.exp 1 * Real.exp 1 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) from by ring, hsq]
  exact le_of_eq hstep

-- END LEAF 5 HELPERS

/-! ### Leaf 5: a lower bound for the sum kernel (a strip of width 1 along the anti-diagonal) -/

/-- On the frequency square of radius `T` the exponentially decreasing sum kernel is at least
a constant times `T`: the strip `0 ≤ t ≤ T - 1`, `-t ≤ u ≤ -t + 1` has measure `T - 1` and
there `|t + u| ≤ 1`, so the integrand is bounded below by `exp (-(π/4))`. -/
private theorem sumKernel_lower487 (T : ℝ) (hT : 2 ≤ T) :
    Real.exp (-(Real.pi / 4)) * (T / 2) ≤ sumKernel376 T := by
  set F : ℝ → ℝ → ℝ := fun t u => Real.exp (-(Real.pi / 4) * |t + u|) with hF
  have hc : (0 : ℝ) < Real.exp (-(Real.pi / 4)) := Real.exp_pos _
  have hFcurry : Function.uncurry F =
      fun p : ℝ × ℝ => Real.exp (-(Real.pi / 4) * |p.1 + p.2|) := by
    funext p
    rfl
  have hFcont : Continuous (Function.uncurry F) := by
    rw [hFcurry]
    fun_prop
  have hFt (t : ℝ) : Continuous fun u : ℝ => F t u := by
    have h : (fun u : ℝ => F t u) = fun u => Real.exp (-(Real.pi / 4) * |t + u|) := by
      funext u
      simp only [hF]
    rw [h]
    fun_prop
  -- the inner integral from `-T` to `T` dominates the constant on the strip
  have hinner : ∀ t ∈ Set.Icc (0 : ℝ) (T - 1),
      Real.exp (-(Real.pi / 4)) ≤ ∫ u in -T..T, F t u := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htT : t ≤ T - 1 := ht.2
    have hconst : (∫ u in (-t)..(-t + 1), Real.exp (-(Real.pi / 4))) =
        Real.exp (-(Real.pi / 4)) := by
      simp
    have hstep2 : (∫ u in (-t)..(-t + 1), Real.exp (-(Real.pi / 4))) ≤
        ∫ u in (-t)..(-t + 1), F t u := by
      apply intervalIntegral.integral_mono_on (by linarith : (-t : ℝ) ≤ -t + 1)
      · exact intervalIntegrable_const
      · exact (hFt t).intervalIntegrable _ _
      · intro u hu
        have hu1 : -t ≤ u := hu.1
        have hu2 : u ≤ -t + 1 := hu.2
        have habs : |t + u| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        refine Real.exp_le_exp.mpr ?_
        nlinarith [Real.pi_pos, abs_nonneg (t + u), habs]
    have hstep3 : (∫ u in (-t)..(-t + 1), F t u) ≤ ∫ u in -T..T, F t u := by
      apply intervalIntegral.integral_mono_interval (c := -T) (d := T)
      · linarith
      · linarith
      · linarith
      · exact Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
      · exact (hFt t).intervalIntegrable _ _
    rw [hconst] at hstep2
    exact hstep2.trans hstep3
  -- restrict the outer integral to the same range of `t`
  have houter : (∫ t in (0 : ℝ)..(T - 1), Real.exp (-(Real.pi / 4))) ≤
      ∫ t in (0 : ℝ)..(T - 1), ∫ u in -T..T, F t u := by
    apply intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ T - 1)
    · exact intervalIntegrable_const
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := F) (μ := volume) hFcont (-T) T).intervalIntegrable _ _
    · intro t ht
      exact hinner t ⟨ht.1, ht.2⟩
  have houter2 : (∫ t in (0 : ℝ)..(T - 1), ∫ u in -T..T, F t u) ≤
      ∫ t in -T..T, ∫ u in -T..T, F t u := by
    apply intervalIntegral.integral_mono_interval (c := -T) (d := T)
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall (fun t =>
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => (Real.exp_pos _).le))
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := F) (μ := volume) hFcont (-T) T).intervalIntegrable _ _
  have hval : (∫ t in (0 : ℝ)..(T - 1), Real.exp (-(Real.pi / 4))) =
      Real.exp (-(Real.pi / 4)) * (T - 1) := by
    simp [mul_comm]
  have hhalf : T / 2 ≤ T - 1 := by linarith
  calc Real.exp (-(Real.pi / 4)) * (T / 2)
      ≤ Real.exp (-(Real.pi / 4)) * (T - 1) := mul_le_mul_of_nonneg_left hhalf hc.le
    _ = ∫ t in (0 : ℝ)..(T - 1), Real.exp (-(Real.pi / 4)) := hval.symm
    _ ≤ ∫ t in (0 : ℝ)..(T - 1), ∫ u in -T..T, F t u := houter
    _ ≤ ∫ t in -T..T, ∫ u in -T..T, F t u := houter2
    _ = sumKernel376 T := by rw [hF]; simp only [sumKernel376]

-- END LEAF 5 LOWER

/-! ### Leaf 5: the exponential frequency weight is uniformly bounded on the square -/

/-- The linear weight is absorbed by the exponential decay: `3 + |s| ≤ 4 exp ((π/4)|s|)`. -/
private theorem exp_weight_le487 (s : ℝ) :
    (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|) ≤ 4 * Real.exp (-(Real.pi / 4) * |s|) := by
  have hc : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |s|) := Real.exp_pos _
  have hs : (0 : ℝ) ≤ |s| := abs_nonneg s
  have hlin : 3 + |s| ≤ 4 * Real.exp ((Real.pi / 4) * |s|) := by
    have h1 : (Real.pi / 4) * |s| + 1 ≤ Real.exp ((Real.pi / 4) * |s|) := Real.add_one_le_exp _
    nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hlin hc.le
  refine hmul.trans_eq ?_
  rw [mul_assoc, ← Real.exp_add,
    show (Real.pi / 4) * |s| + -(Real.pi / 2) * |s| = -(Real.pi / 4) * |s| from by ring]

/-- Pointwise in `alpha`: on the negative region `t + u ≤ 0` the kernel pair is bounded by
`exp 2 · N` times the two Gamma weights. The angular factor is `≤ 1` because `arg z ≥ 0`. -/
private theorem kernel_pair_pointwise487 (N : ℕ) (hN : 3 ≤ N) {α : ℝ} (hα : 0 ≤ α)
    (t u : ℝ) (htu : t + u ≤ 0) :
    ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤
      (Real.exp 2 * (N : ℝ)) *
        ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
         (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) := by
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hzre : z.re = 1 / (N : ℝ) := by simp [hz]
  have hzim : z.im = 2 * Real.pi * α := by simp [hz]
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hzpos
    simp at hzpos
  have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by rw [hzim]; positivity)
  have hpow := norm_cpow_pair487 N hN hzne hzre t u
  have hexp : Real.exp ((t + u) * z.arg) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [harg, htu]
  have hker : ∀ s : ℝ, mellinKernel442 N α s =
      z ^ (-(mellinLine1622 N s)) * Complex.Gamma (mellinLine1622 N s) := by
    intro s
    rfl
  have hgamma_t := gamma_mellin_line442 N hN t
  have hgamma_u := gamma_mellin_line442 N hN u
  have h1 : ‖z ^ (-(mellinLine1622 N t)) *
      (starRingEnd ℂ) (z ^ (-(mellinLine1622 N u)))‖ ≤ Real.exp 2 * (N : ℝ) := by
    refine hpow.trans ?_
    calc Real.exp 2 * (N : ℝ) * Real.exp ((t + u) * z.arg)
        ≤ Real.exp 2 * (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 2 * (N : ℝ) := by ring
  have hAB : ‖Complex.Gamma (mellinLine1622 N t)‖ *
      ‖Complex.Gamma (mellinLine1622 N u)‖ ≤
      (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
        (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))) :=
    mul_le_mul hgamma_t hgamma_u (norm_nonneg _) (by positivity)
  calc ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
      = ‖z ^ (-(mellinLine1622 N t)) *
            (starRingEnd ℂ) (z ^ (-(mellinLine1622 N u)))‖ *
          (‖Complex.Gamma (mellinLine1622 N t)‖ *
            ‖Complex.Gamma (mellinLine1622 N u)‖) := by
        rw [hker t, hker u, map_mul]
        simp only [norm_mul, Complex.norm_conj]
        ring
    _ ≤ (Real.exp 2 * (N : ℝ)) *
          ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
           (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) :=
        mul_le_mul h1 hAB (by positivity) (by positivity)

/-- The `alpha` integral of the kernel pair on the outer range, on the negative region. -/
private theorem kernel_pair_integral487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hRN : 4 * R ≤ (N : ℝ)) (t u : ℝ) (htu : t + u ≤ 0) :
    ‖∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤
      (1 / R) * ((Real.exp 2 * (N : ℝ)) *
        ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
         (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hN1 : 1 ≤ N := by omega
  set C : ℝ := (Real.exp 2 * (N : ℝ)) *
      ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
       (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) with hC
  have hCnonneg : (0 : ℝ) ≤ C := by rw [hC]; positivity
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNpos hRpos]
    linarith
  have hker := continuous_mellinKernel487 N hN1
  have hcont : Continuous fun α : ℝ =>
      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u) := by
    have h1 : Continuous fun α : ℝ => mellinKernel442 N α t :=
      hker.comp (continuous_id.prodMk continuous_const)
    have h2 : Continuous fun α : ℝ => mellinKernel442 N α u :=
      hker.comp (continuous_id.prodMk continuous_const)
    exact h1.mul h2.star
  have hpt : ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
      ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤ C := by
    intro α hα
    have hα0 : 0 ≤ α := by
      have : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
      linarith [hα.1]
    exact kernel_pair_pointwise487 N hN hα0 t u htu
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun α : ℝ => mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)) hab
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R),
        ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
      ∫ α in (4 / (N : ℝ))..(1 / R), C := by
    apply intervalIntegral.integral_mono_on hab
    · exact hcont.norm.intervalIntegrable _ _
    · exact intervalIntegrable_const (c := C)
    · intro α hα
      exact hpt α hα
  have hval : (∫ α in (4 / (N : ℝ))..(1 / R), C) = C * (1 / R - 4 / (N : ℝ)) := by
    simp [mul_comm]
  have hdiff : 1 / R - 4 / (N : ℝ) ≤ 1 / R := by
    have : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
    linarith
  calc ‖∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
      ≤ (∫ α in (4 / (N : ℝ))..(1 / R),
        ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) := hnorm
    _ ≤ ∫ α in (4 / (N : ℝ))..(1 / R), C := hmono
    _ = C * (1 / R - 4 / (N : ℝ)) := hval
    _ ≤ C * (1 / R) := mul_le_mul_of_nonneg_left hdiff hCnonneg
    _ = (1 / R) * C := by ring

-- END LEAF 5 PAIR

/-- The line bound with the logarithm of the frequency replaced by a polynomial weight:
`‖M t‖ ≤ B0 (8 log³N + 8 (3 + |t|)³)` for `N ≥ 2`. This is what lets the exponential decay of the
Gamma factor absorb the coefficient weight on the negative region. -/
private theorem mellin_weight_le487 (N : ℕ) (hN : 2 ≤ N) (B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) (t : ℝ) :
    ‖M t‖ ≤ B0 * (8 * Real.log N ^ 3 + 8 * (3 + |t|) ^ 3) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsplit := log_cube_split442 N t hN
  -- the logarithm of the frequency is dominated by the linear weight
  have h3 : Real.log (|t| + 2) ≤ 3 + |t| := by
    have hpos : (0 : ℝ) < |t| + 2 := by positivity
    have hle : Real.log (|t| + 2) ≤ |t| + 2 - 1 := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hcube : Real.log (|t| + 2) ^ 3 ≤ (3 + |t|) ^ 3 := by
    have h3' : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
    exact pow_le_pow_left₀ hlog0 h3 3
  have hbound : Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.log N ^ 3 + 8 * (3 + |t|) ^ 3 := by
    refine hsplit.trans ?_
    have : 8 * Real.log (|t| + 2) ^ 3 ≤ 8 * (3 + |t|) ^ 3 := by linarith
    linarith
  exact (hM.2 t).trans (mul_le_mul_of_nonneg_left hbound hB0)

-- END LEAF 5 COEFF

/-- A polynomial weight of degree four is dominated by half of the exponential decay. -/
private theorem poly_le_exp487 (s : ℝ) :
    (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|) ≤
      4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|) := by
  have hs : (0 : ℝ) ≤ |s| := abs_nonneg s
  -- (1 + |s|) ^ 4 ≤ 384 e · exp (|s| / 2)
  have h1 : (1 + |s|) ^ 4 ≤ 384 * (Real.exp 1 * Real.exp (|s| / 2)) := by
    set u : ℝ := |s| / 2 + 1 with hu
    have hu1 : (1 : ℝ) ≤ u := by rw [hu]; linarith
    have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu1
    have hpow : u ^ 4 / ((Nat.factorial 4 : ℕ) : ℝ) ≤ Real.exp u :=
      Real.pow_div_factorial_le_exp (x := u) hu0 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
    rw [hfac] at hpow
    have h4 : u ^ 4 ≤ 24 * Real.exp u := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 24)] at hpow
      linarith
    have hlin : 1 + |s| ≤ 2 * u := by rw [hu]; linarith
    have h4' : (0 : ℝ) ≤ 1 + |s| := by linarith
    have hpow4 : (1 + |s|) ^ 4 ≤ (2 * u) ^ 4 := pow_le_pow_left₀ h4' hlin 4
    have hexp : Real.exp u = Real.exp 1 * Real.exp (|s| / 2) := by
      rw [hu, show |s| / 2 + 1 = 1 + |s| / 2 from by ring, Real.exp_add]
    rw [hexp] at h4
    calc (1 + |s|) ^ 4 ≤ (2 * u) ^ 4 := hpow4
      _ = 16 * u ^ 4 := by ring
      _ ≤ 384 * (Real.exp 1 * Real.exp (|s| / 2)) := by nlinarith [h4]
  -- (3 + |s|) ^ 4 ≤ 256 (1 + |s|) ^ 4
  have h2 : (3 + |s|) ^ 4 ≤ 256 * (1 + |s|) ^ 4 := by
    have hle : 3 + |s| ≤ 4 * (1 + |s|) := by linarith
    have hpos : (0 : ℝ) ≤ 3 + |s| := by linarith
    calc (3 + |s|) ^ 4 ≤ (4 * (1 + |s|)) ^ 4 := pow_le_pow_left₀ hpos hle 4
      _ = 256 * (1 + |s|) ^ 4 := by ring
  -- combine: (3 + |s|) ^ 4 ≤ 1048576 exp (1 + |s| / 2)
  have key : (3 + |s|) ^ 4 ≤ 1048576 * Real.exp (1 + |s| / 2) := by
    have hexp1 : Real.exp 1 * Real.exp (|s| / 2) = Real.exp (1 + |s| / 2) := by
      rw [Real.exp_add]
    rw [hexp1] at h1
    refine h2.trans ?_
    calc 256 * (1 + |s|) ^ 4 ≤ 256 * (384 * Real.exp (1 + |s| / 2)) := by linarith [h1]
      _ ≤ 1048576 * Real.exp (1 + |s| / 2) := by
          have hpos : (0 : ℝ) < Real.exp (1 + |s| / 2) := Real.exp_pos _
          nlinarith [hpos]
  -- multiply by the decay and fold into one exponential
  have hc : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |s|) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right key hc.le
  have he1 : Real.exp 1 ≤ 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have hpos : (0 : ℝ) < Real.exp (-((Real.pi - 1) / 2) * |s|) := Real.exp_pos _
  refine hmul.trans ?_
  calc 1048576 * Real.exp (1 + |s| / 2) * Real.exp (-(Real.pi / 2) * |s|)
      = 1048576 * (Real.exp 1 * Real.exp (-((Real.pi - 1) / 2) * |s|)) := by
        rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ 4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|) := by
        have hh := mul_le_mul_of_nonneg_right he1 hpos.le
        nlinarith [hpos]

-- END LEAF 5 POLY

/-- The degree four polynomial-exponential weight has an absolutely bounded integral on any
symmetric interval. This is the constant that absorbs the coefficient weight in leaf 5. -/
private theorem poly_exp_moment487 (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in -T..T, (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)) ≤ 8388608 := by
  have hc : (0 : ℝ) < (Real.pi - 1) / 2 := by linarith [Real.pi_gt_three]
  have hcont : Continuous fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|) := by fun_prop
  have hTT : (-T : ℝ) ≤ T := by linarith
  -- the one sided integral of the decay
  have hhalf : (∫ s in (0 : ℝ)..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) ≤
      2 / (Real.pi - 1) := by
    rw [intervalIntegral.integral_of_le hT]
    have hcongr : (∫ s in Set.Ioc (0 : ℝ) T,
        Real.exp (-((Real.pi - 1) / 2) * |s|)) =
        ∫ s in Set.Ioc (0 : ℝ) T, Real.exp (-((Real.pi - 1) / 2) * s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [abs_of_pos hs.1]
    rw [hcongr]
    refine le_trans (setIntegral_mono_set (μ := volume)
      (integrableOn_exp_mul_Ioi (a := -((Real.pi - 1) / 2)) (by linarith) (0 : ℝ))
      (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx))) ?_
    rw [integral_exp_mul_Ioi (a := -((Real.pi - 1) / 2)) (by linarith) (0 : ℝ), mul_zero,
      Real.exp_zero]
    have hval : -(1 : ℝ) / (-((Real.pi - 1) / 2)) = 2 / (Real.pi - 1) := by
      rw [div_eq_div_iff (by linarith : (-((Real.pi - 1) / 2)) ≠ 0)
        (by linarith : (Real.pi - 1) ≠ 0)]
      ring
    rw [hval]
  have heven : (∫ s in -T..0, Real.exp (-((Real.pi - 1) / 2) * |s|)) =
      ∫ s in (0 : ℝ)..T, Real.exp (-((Real.pi - 1) / 2) * |s|) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|)) (a := (0 : ℝ)) (b := T)
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [abs_neg]
  have htotal : (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) ≤
      4 / (Real.pi - 1) := by
    have h1 : IntervalIntegrable (fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|))
        volume (-T) 0 := hcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|))
        volume 0 T := hcont.intervalIntegrable _ _
    have hsplit : (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) =
        (∫ s in -T..0, Real.exp (-((Real.pi - 1) / 2) * |s|)) +
          (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    calc (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|))
        = (∫ s in -T..0, Real.exp (-((Real.pi - 1) / 2) * |s|)) +
            (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := hsplit
      _ = (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) +
            (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := by rw [heven]
      _ ≤ 2 / (Real.pi - 1) + 2 / (Real.pi - 1) := add_le_add hhalf hhalf
      _ = 4 / (Real.pi - 1) := by ring
  have hstep : (∫ s in -T..T, (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)) ≤
      ∫ s in -T..T, 4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|) := by
    apply intervalIntegral.integral_mono_on hTT
    · exact (by fun_prop : Continuous fun s : ℝ =>
        (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s : ℝ =>
        4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|)).intervalIntegrable _ _
    · intro s _
      exact poly_le_exp487 s
  have hval : (∫ s in -T..T, 4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|)) =
      4194304 * (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hval] at hstep
  have hpi : (0 : ℝ) < (Real.pi - 1) := by linarith [Real.pi_gt_three]
  have hnn : (0 : ℝ) ≤ ∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|) :=
    intervalIntegral.integral_nonneg hTT (fun s _ => (Real.exp_pos _).le)
  calc (∫ s in -T..T, (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|))
      ≤ 4194304 * (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := hstep
    _ ≤ 4194304 * (4 / (Real.pi - 1)) := by
        have : (0 : ℝ) ≤ 4 / (Real.pi - 1) := by positivity
        nlinarith [htotal, hnn, hpi]
    _ ≤ 8388608 := by
        rw [show (8388608 : ℝ) = 4194304 * 2 from by norm_num]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [div_le_iff₀ hpi]
        nlinarith [Real.pi_gt_three]

-- END LEAF 5 MOMENT

/-- The linear-exponential weight integrates to at most sixteen. -/
private theorem linear_exp_moment487 (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in -T..T, (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)) ≤ 16 := by
  have hcont : Continuous fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|) := by fun_prop
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hhalf : (∫ s in (0 : ℝ)..T, Real.exp (-(Real.pi / 4) * |s|)) ≤ 4 / Real.pi := by
    rw [intervalIntegral.integral_of_le hT]
    have hcongr : (∫ s in Set.Ioc (0 : ℝ) T, Real.exp (-(Real.pi / 4) * |s|)) =
        ∫ s in Set.Ioc (0 : ℝ) T, Real.exp (-(Real.pi / 4) * s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [abs_of_pos hs.1]
    rw [hcongr]
    refine le_trans (setIntegral_mono_set (μ := volume)
      (integrableOn_exp_mul_Ioi (a := -(Real.pi / 4)) (by linarith [Real.pi_pos]) (0 : ℝ))
      (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx))) ?_
    rw [integral_exp_mul_Ioi (a := -(Real.pi / 4)) (by linarith [Real.pi_pos]) (0 : ℝ), mul_zero,
      Real.exp_zero]
    have hval : -(1 : ℝ) / (-(Real.pi / 4)) = 4 / Real.pi := by
      rw [div_eq_div_iff (by linarith [Real.pi_pos] : (-(Real.pi / 4)) ≠ 0)
        (ne_of_gt Real.pi_pos)]
      ring
    rw [hval]
  have heven : (∫ s in -T..0, Real.exp (-(Real.pi / 4) * |s|)) =
      ∫ s in (0 : ℝ)..T, Real.exp (-(Real.pi / 4) * |s|) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|)) (a := (0 : ℝ)) (b := T)
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [abs_neg]
  have htotal : (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) ≤ 8 / Real.pi := by
    have h1 : IntervalIntegrable (fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|)) volume (-T) 0 :=
      hcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|)) volume 0 T :=
      hcont.intervalIntegrable _ _
    have hsplit : (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) =
        (∫ s in -T..0, Real.exp (-(Real.pi / 4) * |s|)) +
          (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    calc (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|))
        = (∫ s in -T..0, Real.exp (-(Real.pi / 4) * |s|)) +
            (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) := hsplit
      _ = (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) +
            (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) := by rw [heven]
      _ ≤ 4 / Real.pi + 4 / Real.pi := add_le_add hhalf hhalf
      _ = 8 / Real.pi := by ring
  have hstep : (∫ s in -T..T, (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)) ≤
      ∫ s in -T..T, 4 * Real.exp (-(Real.pi / 4) * |s|) := by
    apply intervalIntegral.integral_mono_on hTT
    · exact (by fun_prop : Continuous fun s : ℝ =>
        (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s : ℝ =>
        4 * Real.exp (-(Real.pi / 4) * |s|)).intervalIntegrable _ _
    · intro s _
      exact exp_weight_le487 s
  have hval : (∫ s in -T..T, 4 * Real.exp (-(Real.pi / 4) * |s|)) =
      4 * (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hval] at hstep
  have hnn : (0 : ℝ) ≤ ∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|) :=
    intervalIntegral.integral_nonneg hTT (fun s _ => (Real.exp_pos _).le)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  calc (∫ s in -T..T, (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|))
      ≤ 4 * (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) := hstep
    _ ≤ 4 * (8 / Real.pi) := by
        have : (0 : ℝ) ≤ 8 / Real.pi := by positivity
        nlinarith [htotal, hnn, hpi]
    _ ≤ 16 := by
        have he : 4 * (8 / Real.pi) = 32 / Real.pi := by ring
        rw [he, div_le_iff₀ hpi]
        nlinarith [Real.pi_gt_three]

-- END LEAF 5 LINEARMOMENT

/-- The coefficient times the Gamma weight integrates to an explicit constant, uniformly in the
frequency radius. This is the single-variable factor of the negative-region square. -/
private theorem coeff_weight_moment487 (N : ℕ) (hN : 16384 ≤ N) (B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in -T..T, ‖M s‖ * (Real.sqrt (2 * Real.pi) * (3 + |s|) *
        Real.exp (-(Real.pi * |s| / 2))))
      ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608) := by
  set W : ℝ → ℝ := fun s => Real.sqrt (2 * Real.pi) * (3 + |s|) *
    Real.exp (-(Real.pi * |s| / 2)) with hW
  set L : ℝ → ℝ := fun s => (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|) with hL
  set P : ℝ → ℝ := fun s => (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|) with hP
  have hconv : ∀ s : ℝ, Real.exp (-(Real.pi * |s| / 2)) = Real.exp (-(Real.pi / 2) * |s|) := by
    intro s
    congr 1
    ring
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hWcont : Continuous W := by rw [hW]; fun_prop
  have hLcont : Continuous L := by rw [hL]; fun_prop
  have hPcont : Continuous P := by rw [hP]; fun_prop
  -- the pointwise comparison
  have hpt : ∀ s : ℝ, ‖M s‖ * W s ≤
      8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) := by
    intro s
    have h1 := mellin_weight_le487 N (by omega) B0 hB0 M hM s
    have hWnn : (0 : ℝ) ≤ W s := by rw [hW]; positivity
    have hstep : ‖M s‖ * W s ≤
        B0 * (8 * Real.log N ^ 3 + 8 * (3 + |s|) ^ 3) * W s :=
      mul_le_mul_of_nonneg_right h1 hWnn
    have he' : B0 * (8 * Real.log N ^ 3 + 8 * (3 + |s|) ^ 3) *
          (Real.sqrt (2 * Real.pi) * (3 + |s|) * Real.exp (-(Real.pi * |s| / 2))) =
        8 * B0 * Real.sqrt (2 * Real.pi) *
          (Real.log N ^ 3 * ((3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)) +
            (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)) := by
      rw [hconv s]
      ring
    have he : B0 * (8 * Real.log N ^ 3 + 8 * (3 + |s|) ^ 3) * W s =
        8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) := by
      simpa only [hW, hL, hP] using he'
    linarith [hstep, he ▸ hstep]
  -- the majorant is continuous
  have hmajcont : Continuous fun s : ℝ =>
      8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) :=
    continuous_const.mul ((continuous_const.mul hLcont).add hPcont)
  have hmono : (∫ s in -T..T, ‖M s‖ * W s) ≤
      ∫ s in -T..T, 8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) := by
    apply intervalIntegral.integral_mono_on hTT
    · exact (hM.1.norm.mul hWcont).intervalIntegrable _ _
    · exact hmajcont.intervalIntegrable _ _
    · intro s _
      exact hpt s
  -- evaluate the majorant integral
  have hsplit : (∫ s in -T..T, 8 * B0 * Real.sqrt (2 * Real.pi) *
        (Real.log N ^ 3 * L s + P s)) =
      8 * B0 * Real.sqrt (2 * Real.pi) *
        (Real.log N ^ 3 * (∫ s in -T..T, L s) + (∫ s in -T..T, P s)) := by
    have hIL : IntervalIntegrable (fun s : ℝ => Real.log N ^ 3 * L s) volume (-T) T :=
      (continuous_const.mul hLcont).intervalIntegrable _ _
    have hIP : IntervalIntegrable P volume (-T) T := hPcont.intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_add hIL hIP, intervalIntegral.integral_const_mul]
  have hLb : (∫ s in -T..T, L s) ≤ 16 := by
    rw [hL]
    exact linear_exp_moment487 T hT
  have hPb : (∫ s in -T..T, P s) ≤ 8388608 := by
    rw [hP]
    exact poly_exp_moment487 T hT
  have hLnn : (0 : ℝ) ≤ ∫ s in -T..T, L s :=
    intervalIntegral.integral_nonneg hTT (fun s _ => by rw [hL]; positivity)
  have hlog3 : (0 : ℝ) ≤ Real.log N ^ 3 := by positivity
  have hB : (0 : ℝ) ≤ 8 * B0 * Real.sqrt (2 * Real.pi) := by positivity
  rw [hsplit] at hmono
  refine hmono.trans ?_
  have hinner : Real.log N ^ 3 * (∫ s in -T..T, L s) + (∫ s in -T..T, P s) ≤
      16 * Real.log N ^ 3 + 8388608 := by
    nlinarith [hLb, hPb, hLnn, hlog3]
  calc 8 * B0 * Real.sqrt (2 * Real.pi) *
        (Real.log N ^ 3 * (∫ s in -T..T, L s) + (∫ s in -T..T, P s))
      ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608) :=
        mul_le_mul_of_nonneg_left hinner hB

-- END LEAF 5 COEFFMOMENT

private theorem sum_region_core487 (N : ℕ) (hN : 16384 ≤ N) (R : ℝ) (hR1 : 1 ≤ R)
    (hRN : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (B0 : ℝ) (hB0 : 0 < B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) :
    (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          if 0 ≤ t + u then 0
          else ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)
      ≤ (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hTT : -T ≤ T := by linarith
  -- the logarithms are at least one
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    refine Real.le_log_iff_exp_le ?_ |>.mpr ?_
    · exact hNpos
    · exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
  -- `4 R ≤ N`
  have h4R : 4 * R ≤ (N : ℝ) := by
    have h1 : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
    have h2 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) / 4 := by
      rw [← Real.sqrt_eq_rpow]
      have hs : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hNpos.le
      have hs0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      have h16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 16 ≤ N by omega)
      have h4 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith [hs, hs0, h16]
      nlinarith [hs, hs0, h4]
    linarith
  -- the single-variable weight and the coefficient-weighted version
  set G : ℝ → ℝ := fun s => ‖M s‖ * (Real.sqrt (2 * Real.pi) * (3 + |s|) *
    Real.exp (-(Real.pi * |s| / 2))) with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact hM.1.norm.mul (by fun_prop)
  have hGnn : ∀ s : ℝ, 0 ≤ G s := by
    intro s
    rw [hG]
    positivity
  -- the joint integrand and its majorant
  set C : ℝ := (1 / R) * (Real.exp 2 * (N : ℝ)) with hC
  have hCnn : (0 : ℝ) ≤ C := by rw [hC]; positivity
  have hJcont : Continuous fun z : ℝ × ℝ =>
      ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖ := by
    have hI : Continuous fun z : ℝ × ℝ => ∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2) :=
      continuous_alphaKernel_integral487 N (by omega) _ _
    exact ((hM.1.comp continuous_fst).norm.mul (hM.1.comp continuous_snd).norm).mul hI.norm
  have hMAJcont : Continuous fun z : ℝ × ℝ => C * (G z.1 * G z.2) :=
    continuous_const.mul ((hGcont.comp continuous_fst).mul (hGcont.comp continuous_snd))
  -- pointwise domination on the whole plane
  have hmaj : ∀ t u : ℝ,
      (if 0 ≤ t + u then (0 : ℝ)
        else ‖M t‖ * ‖M u‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)
      ≤ C * (G t * G u) := by
    intro t u
    by_cases h : 0 ≤ t + u
    · rw [if_pos h]
      have h1 : (0 : ℝ) ≤ G t := hGnn t
      have h2 : (0 : ℝ) ≤ G u := hGnn u
      have := mul_nonneg h1 h2
      have := mul_nonneg hCnn this
      linarith
    · rw [if_neg h]
      have hker := kernel_pair_integral487 N (by omega) R hR1 h4R t u
        (le_of_lt (lt_of_not_ge h))
      have hstep : ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
          ≤ ‖M t‖ * ‖M u‖ * (C *
            ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
             (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))))) := by
        rw [hC]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
            ≤ 1 / R * (Real.exp 2 * (N : ℝ) *
                ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
                 (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))))) := hker
          _ = 1 / R * (Real.exp 2 * (N : ℝ)) *
                ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
                 (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) := by ring
      refine hstep.trans (le_of_eq ?_)
      rw [hC, hG]
      ring
  -- the majorant is integrable on the box
  have hMAJint : IntegrableOn (fun z : ℝ × ℝ => C * (G z.1 * G z.2))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) :=
    (hMAJcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hnnF : ∀ z : ℝ × ℝ, (0 : ℝ) ≤
      (if 0 ≤ z.1 + z.2 then (0 : ℝ)
        else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖) := by
    intro z
    by_cases h : 0 ≤ z.1 + z.2
    · rw [if_pos h]
    · rw [if_neg h]
      positivity
  -- the joint integrand is integrable on the box by domination
  have hFint : IntegrableOn (fun z : ℝ × ℝ => if 0 ≤ z.1 + z.2 then (0 : ℝ)
      else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖)
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    have hmeas : Measurable fun z : ℝ × ℝ => if 0 ≤ z.1 + z.2 then (0 : ℝ)
        else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖ :=
      Measurable.ite (measurableSet_le measurable_const (measurable_fst.add measurable_snd))
        measurable_const hJcont.measurable
    refine Integrable.mono' hMAJint hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnnF z)]
    exact hmaj z.1 z.2
  -- the box comparison
  have hbox : (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), (if 0 ≤ z.1 + z.2 then (0 : ℝ)
        else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖))
      ≤ ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), C * (G z.1 * G z.2) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_))
      hMAJint (Filter.Eventually.of_forall (fun z => hmaj z.1 z.2))
    exact hnnF z
  -- factorize the majorant integral
  have hmajint : (∫ t in -T..T, ∫ u in -T..T, C * (G t * G u)) =
      C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := by
    have hinner : ∀ t : ℝ, (∫ u in -T..T, C * (G t * G u)) =
        C * G t * (∫ u in -T..T, G u) := by
      intro t
      have hfac : (fun u : ℝ => C * (G t * G u)) = fun u : ℝ => (C * G t) * G u := by
        funext u
        ring
      rw [hfac, intervalIntegral.integral_const_mul]
    have houter : (∫ t in -T..T, C * G t * (∫ u in -T..T, G u)) =
        C * (∫ u in -T..T, G u) * (∫ t in -T..T, G t) := by
      have hfac : (fun t : ℝ => C * G t * (∫ u in -T..T, G u)) =
          fun t : ℝ => (C * (∫ u in -T..T, G u)) * G t := by
        funext t
        ring
      rw [hfac, intervalIntegral.integral_const_mul]
    calc (∫ t in -T..T, ∫ u in -T..T, C * (G t * G u))
        = ∫ t in -T..T, C * G t * (∫ u in -T..T, G u) := by simp only [hinner]
      _ = C * (∫ u in -T..T, G u) * (∫ t in -T..T, G t) := houter
      _ = C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := by ring
  have hmono : (∫ t in -T..T, ∫ u in -T..T, (if 0 ≤ t + u then (0 : ℝ)
        else ‖M t‖ * ‖M u‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖))
      ≤ C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := by
    calc (∫ t in -T..T, ∫ u in -T..T, (if 0 ≤ t + u then (0 : ℝ)
          else ‖M t‖ * ‖M u‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖))
        = ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), (if 0 ≤ z.1 + z.2 then (0 : ℝ)
            else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖) :=
          iterated_eq_box487 _ (-T) T hFint
      _ ≤ ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), C * (G z.1 * G z.2) := hbox
      _ = ∫ t in -T..T, ∫ u in -T..T, C * (G t * G u) :=
          (iterated_eq_box487 (fun t u => C * (G t * G u)) (-T) T hMAJint).symm
      _ = C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := hmajint
  -- bound the one dimensional integral
  have hGb : (∫ s in -T..T, G s) ≤
      8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608) := by
    rw [hG]
    exact coeff_weight_moment487 N hN B0 hB0.le M hM T hT0
  have hlog3 : (1 : ℝ) ≤ Real.log N ^ 3 := by
    have h0 := Real.log_nonneg hNr1
    nlinarith [hlog1, h0, sq_nonneg (Real.log N)]
  have hGb2 : (∫ s in -T..T, G s) ≤
      8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 := by
    refine hGb.trans ?_
    have h1 : 16 * Real.log N ^ 3 + 8388608 ≤ 8388624 * Real.log N ^ 3 := by
      nlinarith [hlog3]
    have h2 : (0 : ℝ) ≤ 8 * B0 * Real.sqrt (2 * Real.pi) := by positivity
    calc 8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608)
        ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * (8388624 * Real.log N ^ 3) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 := by ring
  -- numerical closing
  have hA : (0 : ℝ) ≤ (1 / R) * (Real.exp 2 * (N : ℝ)) := by positivity
  have hG2 : (∫ s in -T..T, G s) * (∫ s in -T..T, G s) ≤
      (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
        (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) := by
    have hnn : (0 : ℝ) ≤ ∫ s in -T..T, G s :=
      intervalIntegral.integral_nonneg hTT (fun s _ => hGnn s)
    exact mul_le_mul hGb2 hGb2 hnn (by positivity)
  refine hmono.trans ?_
  have hlog6 : (0 : ℝ) ≤ Real.log N ^ 6 := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ 3 := by
    have h1 : (2 * Real.pi : ℝ) ≤ 9 := by nlinarith [Real.pi_lt_four]
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt h1
      _ = 3 := by norm_num
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have he : (Real.exp 2 : ℝ) ≤ 9 := by
    rw [hexp2]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith [Real.exp_pos 1]
  have hnnG : (0 : ℝ) ≤ ∫ s in -T..T, G s :=
    intervalIntegral.integral_nonneg hTT (fun s _ => hGnn s)
  -- insert the one dimensional bound
  have hstep1 : C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) ≤
      C * ((8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
        (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCnn
    exact mul_le_mul hGb2 hGb2 hnnG (by positivity)
  refine hstep1.trans ?_
  rw [hC]
  have hK : (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
        (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) * (Real.exp 2) ≤
      B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by
    have hloggroup : Real.log N ^ 6 = Real.log N ^ 3 * Real.log N ^ 3 := by ring
    rw [hloggroup]
    have hS : 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 ≤
        8 * B0 * 3 * 8388624 * Real.log N ^ 3 := by
      calc 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3
          = (8 * B0 * 8388624 * Real.log N ^ 3) * Real.sqrt (2 * Real.pi) := by ring
        _ ≤ (8 * B0 * 8388624 * Real.log N ^ 3) * 3 :=
            mul_le_mul_of_nonneg_left hsqrt
              (by positivity : (0 : ℝ) ≤ 8 * B0 * 8388624 * Real.log N ^ 3)
        _ = 8 * B0 * 3 * 8388624 * Real.log N ^ 3 := by ring
    have hSnn : (0 : ℝ) ≤ 8 * B0 * 3 * 8388624 * Real.log N ^ 3 := by positivity
    have hS'nn : (0 : ℝ) ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 :=
      by positivity
    have hsq : (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) ≤
        (8 * B0 * 3 * 8388624 * Real.log N ^ 3) *
          (8 * B0 * 3 * 8388624 * Real.log N ^ 3) :=
      mul_le_mul hS hS hS'nn hSnn
    have hsq2 : (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) * (Real.exp 2) ≤
        (8 * B0 * 3 * 8388624 * Real.log N ^ 3) *
          (8 * B0 * 3 * 8388624 * Real.log N ^ 3) * (Real.exp 2) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos 2).le
    refine hsq2.trans ?_
    have hrw : (8 * B0 * 3 * 8388624 * Real.log N ^ 3) *
          (8 * B0 * 3 * 8388624 * Real.log N ^ 3) * (Real.exp 2) =
        B0 ^ 2 * (Real.log N ^ 3 * Real.log N ^ 3) *
          ((8 * 3 * 8388624) * (8 * 3 * 8388624) * (Real.exp 2)) := by ring
    rw [hrw]
    have hnn : (0 : ℝ) ≤ B0 ^ 2 * (Real.log N ^ 3 * Real.log N ^ 3) := by positivity
    have hnum : (8 * 3 * 8388624 : ℝ) * (8 * 3 * 8388624) * (Real.exp 2) ≤
        36893488147419103232 := by
      nlinarith [he, Real.exp_pos 2, sq_nonneg (8 * 3 * 8388624 : ℝ)]
    exact mul_le_mul_of_nonneg_left hnum hnn
  calc (1 / R) * (Real.exp 2 * (N : ℝ)) *
        ((8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3))
      = (N : ℝ) / R * ((8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) * (Real.exp 2)) := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ (N : ℝ) / R * (B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232) := by
        refine mul_le_mul_of_nonneg_left hK (by positivity)
    _ = (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by
        have hsplit : (N : ℝ) / R * (B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232) =
            (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by ring
        rw [hsplit]

-- END LEAF 5 CORE

/-- `4 R ≤ N` from the radius restriction, for the range used by leaf 5. -/
private theorem four_mul_le487 (N : ℕ) (hN : 16384 ≤ N) (R : ℝ)
    (hR : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) : 4 * R ≤ (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h1 : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
  have h2 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) / 4 := by
    rw [← Real.sqrt_eq_rpow]
    have hs : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have hs0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have h16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 16 ≤ N by omega)
    have h4 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith [hs, hs0, h16]
    nlinarith [hs, hs0, h4]
  linarith

/-- The decay factor at the anti-diagonal scale is at least a sixteenth. -/
private theorem exp_quarter_le487 : (1 / 16 : ℝ) ≤ Real.exp (-(Real.pi / 4)) := by
  have hpos : (0 : ℝ) < Real.exp (Real.pi / 4) := Real.exp_pos _
  have h2 : Real.exp (Real.pi / 4) ≤ 16 := by
    have hpi : Real.pi / 4 ≤ 2 := by nlinarith [Real.pi_lt_four]
    have hle : Real.exp (Real.pi / 4) ≤ Real.exp 2 := Real.exp_le_exp.mpr hpi
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h9 : Real.exp 2 ≤ 9 := by
      rw [he2]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    linarith
  have hinv : Real.exp (-(Real.pi / 4)) = (Real.exp (Real.pi / 4))⁻¹ := by
    rw [← Real.exp_neg]
  rw [hinv]
  simpa only [one_div] using one_div_le_one_div_of_le hpos h2


/-- LEAF. First conjunct of the target: the square of the finite signed contour is continuous in
alpha, so it is interval integrable over the outer range. No estimate is involved. -/
theorem outer_finite_square_integrable487 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, ∀ M : ℝ → ℂ, Continuous M →
      IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2) volume
        (4 / (N : ℝ)) (1 / R) := by
  refine ⟨2, ?_⟩
  intro N hN R M hM
  exact ((continuous_truncatedMellin487 N (by omega) R M hM).norm.pow 2).intervalIntegrable _ _

/-- LEAF. Square and Fubini step. The squared finite contour is bounded by two over pi squared
times the double frequency integral of the coefficient moduli times the modulus of the alpha
integral of the kernel product. Only the signed square identity, the exchange of the alpha
integral with the two frequency integrals and the triangle inequality are used here. -/
theorem outer_finite_modulus_reduction487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (M : ℝ → ℂ)
    (hM : Continuous M) :
    (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
      (1 / (2 * Real.pi)) ^ 2 *
        ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ := by
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  let a : ℝ := 4 / (N : ℝ)
  let b : ℝ := 1 / R
  let H : ℝ → ℝ → ℝ := fun t u => ‖M t‖ * ‖M u‖ *
    ‖∫ α in a..b, mellinKernel442 N α t * star (mellinKernel442 N α u)‖
  have hH0 (t u : ℝ) : 0 ≤ H t u := by dsimp [H]; positivity
  have hpos : 0 ≤ ∫ t in -T..T, ∫ u in -T..T, H t u := by
    rcases le_total (-T) T with hT | hT
    · exact intervalIntegral.integral_nonneg_of_forall hT (fun t =>
        intervalIntegral.integral_nonneg_of_forall hT (hH0 t))
    · have hrev : (∫ t in -T..T, ∫ u in -T..T, H t u) =
          ∫ t in T..-T, ∫ u in T..-T, H t u := by
        calc
          _ = -(∫ t in T..-T, ∫ u in -T..T, H t u) := by
            rw [intervalIntegral.integral_symm]
          _ = -(∫ t in T..-T, -(∫ u in T..-T, H t u)) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro t ht
            change (∫ u in -T..T, H t u) = -(∫ u in T..-T, H t u)
            exact intervalIntegral.integral_symm T (-T)
          _ = _ := by rw [intervalIntegral.integral_neg, neg_neg]
      rw [hrev]
      exact intervalIntegral.integral_nonneg_of_forall hT (fun t =>
        intervalIntegral.integral_nonneg_of_forall hT (hH0 t))
  change (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) ≤
    (1 / (2 * Real.pi)) ^ 2 * ∫ t in -T..T, ∫ u in -T..T, H t u
  by_cases hab : a ≤ b
  · have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have ha : 0 < a := by dsimp [a]; positivity
    have hRp : 0 < R := (one_div_pos).mp (ha.trans_le hab)
    have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hT0 : 0 ≤ T := by dsimp [T]; positivity
    have horder : -T ≤ T := by linarith
    let G : ℝ → ℝ → ℂ := fun t u => (M t * star (M u)) *
      ∫ α in a..b, mellinKernel442 N α t * star (mellinKernel442 N α u)
    have hK : Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
      simpa only [mul_one] using
        continuous_mellin_integrand487 N hN (fun _ => 1) continuous_const
    have hP : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.1)) :=
      continuous_snd.prodMk continuous_fst.fst
    have hQ : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) :=
      continuous_snd.prodMk continuous_fst.snd
    have hF : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        mellinKernel442 N p.2 p.1.1 * star (mellinKernel442 N p.2 p.1.2)) := by
      simpa only [Function.comp_def, Pi.mul_def] using (hK.comp hP).mul (hK.comp hQ).star
    have hI : Continuous (fun p : ℝ × ℝ =>
        ∫ α in a..b, mellinKernel442 N α p.1 * star (mellinKernel442 N α p.2)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF a b
    have hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2) := by
      simpa only [G, Function.comp_def, Pi.mul_def] using
        ((hM.comp continuous_fst).mul (hM.comp continuous_snd).star).mul hI
    have hH : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
      simpa only [H, Function.comp_def, Pi.mul_def] using
        ((hM.comp continuous_fst).norm.mul (hM.comp continuous_snd).norm).mul hI.norm
    have hGi : Continuous (fun t : ℝ => ∫ u in -T..T, G t u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG (-T) T
    have hHi : Continuous (fun t : ℝ => ∫ u in -T..T, H t u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hH (-T) T
    have hfactor (t u : ℝ) :
        (∫ α in a..b, (mellinKernel442 N α t * M t) *
          (starRingEnd ℂ) (mellinKernel442 N α u * M u)) = G t u := by
      dsimp [G]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro α hα
      simp only [map_mul]
      ring
    have hf := truncated_signed_fubini487 N hN R M hM a b
    dsimp only at hf
    simp_rw [hfactor] at hf
    rw [hf]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    calc
      _ ≤ ‖∫ t in -T..T, ∫ u in -T..T, G t u‖ := Complex.re_le_norm _
      _ ≤ ∫ t in -T..T, ‖∫ u in -T..T, G t u‖ :=
        intervalIntegral.norm_integral_le_integral_norm horder
      _ ≤ ∫ t in -T..T, ∫ u in -T..T, H t u := by
        apply intervalIntegral.integral_mono_on horder
          (hGi.norm.intervalIntegrable _ _) (hHi.intervalIntegrable _ _)
        intro t ht
        calc
          _ ≤ ∫ u in -T..T, ‖G t u‖ :=
            intervalIntegral.norm_integral_le_integral_norm horder
          _ = _ := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp only [G, H, norm_mul, norm_star]
  · have hba : b ≤ a := le_of_not_ge hab
    have hleft : (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall hba
        (fun α => sq_nonneg ‖truncatedMellin487 N R M α‖))
    exact hleft.trans (mul_nonneg (sq_nonneg _) hpos)

/-- LEAF. Region split of the frequency square. The double modulus integral over the square of
radius N over R times log cubed N is the sum of its part with t + u nonnegative and its part with
t + u negative. The two parts are the positive frequency difference case and the negative
frequency sum case of the outer contour. -/
theorem outer_finite_region_split487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (hM : Continuous M) :
    (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
      (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            if 0 ≤ t + u then
              ‖M t‖ * ‖M u‖ *
                ‖∫ α in (4 / (N : ℝ))..(1 / R),
                  mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
            else 0) +
        (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            if 0 ≤ t + u then 0
            else
              ‖M t‖ * ‖M u‖ *
                ‖∫ α in (4 / (N : ℝ))..(1 / R),
                  mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) := by
  by_cases hzero : N = 0
  · subst N
    simp
  have hN : 1 ≤ N := by omega
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  let H : ℝ × ℝ → ℝ := fun p => ‖M p.1‖ * ‖M p.2‖ *
    ‖∫ α in (4 / (N : ℝ))..(1 / R),
      mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)‖
  have hK : Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
    simpa only [mul_one] using
      continuous_mellin_integrand_positive493 N hN (fun _ => 1) continuous_const
  have hP : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.1)) :=
    continuous_snd.prodMk continuous_fst.fst
  have hQ : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) :=
    continuous_snd.prodMk continuous_fst.snd
  have hF : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      mellinKernel442 N p.2 p.1.1 * (starRingEnd ℂ) (mellinKernel442 N p.2 p.1.2)) := by
    simpa only [Function.comp_def, Pi.mul_def, starRingEnd_apply] using (hK.comp hP).mul (hK.comp hQ).star
  have hI : Continuous (fun p : ℝ × ℝ =>
      ∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _
  have hH : Continuous H := by
    simpa only [H, Function.comp_def, Pi.mul_def] using
      ((hM.comp continuous_fst).norm.mul (hM.comp continuous_snd).norm).mul hI.norm
  let μ : Measure ℝ := volume.restrict (Set.uIoc (-T) T)
  have hprod : Integrable H (μ.prod μ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact (hH.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hinner (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) (t : ℝ) :
      IntervalIntegrable (fun u => S.indicator H (t, u)) volume (-T) T := by
    apply intervalIntegrable_iff.mpr
    have hc : Continuous (fun u : ℝ => H (t, u)) :=
      hH.comp (continuous_const.prodMk continuous_id)
    have hi : IntervalIntegrable (fun u : ℝ => H (t,u)) volume (-T) T :=
      hc.intervalIntegrable (-T) T
    have hs : MeasurableSet ((fun u : ℝ => (t, u)) ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    change IntegrableOn (((fun u : ℝ => (t,u)) ⁻¹' S).indicator
      (fun u => H (t,u))) (Set.uIoc (-T) T) volume
    exact hi.def'.indicator hs
  have houter (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
      IntervalIntegrable (fun t => ∫ u in -T..T, S.indicator H (t, u))
        volume (-T) T := by
    apply intervalIntegrable_iff.mpr
    have hi := (hprod.indicator hS).integral_prod_left
    have hs := hi.const_mul (if -T ≤ T then (1 : ℝ) else -1)
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, μ, IntegrableOn] using hs
  let S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 + p.2}
  have hS : MeasurableSet S := measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  change (∫ t in -T..T, ∫ u in -T..T, H (t,u)) ≤
    (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then H (t,u) else 0) +
    (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then 0 else H (t,u))
  have hsplit (t : ℝ) : (∫ u in -T..T, H (t,u)) =
      (∫ u in -T..T, S.indicator H (t,u)) +
      (∫ u in -T..T, Sᶜ.indicator H (t,u)) := by
    rw [← intervalIntegral.integral_add (hinner S hS t) (hinner Sᶜ hS.compl t)]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [Set.indicator_apply, S, Set.mem_ofPred_eq, Set.mem_compl_iff]
    split_ifs <;> simp
  calc
    _ = ∫ t in -T..T, ((∫ u in -T..T, S.indicator H (t,u)) +
        (∫ u in -T..T, Sᶜ.indicator H (t,u))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hsplit t
    _ = (∫ t in -T..T, ∫ u in -T..T, S.indicator H (t,u)) +
        (∫ t in -T..T, ∫ u in -T..T, Sᶜ.indicator H (t,u)) :=
      intervalIntegral.integral_add (houter S hS) (houter Sᶜ hS.compl)
    _ ≤ _ := by
      simp only [Set.indicator_apply, S, Set.mem_ofPred_eq, Set.mem_compl_iff,
        ite_not]
      exact le_rfl

/-- P0093 page 157 before equation 4.4. A Gaussian weight and the three lines
theorem give the sharp polynomial exponent for Gamma on a bounded frequency
window. The exponential factor uses the absolute imaginary part. -/
theorem gamma_window501 (A : ℝ) (hA : 1 ≤ A) (s : ℂ)
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) (ht : |s.im| ≤ A) :
    ‖Complex.Gamma s‖ * Real.exp (Real.pi * |s.im| / 2) ≤
      18 * Real.sqrt (2 * Real.pi) * A ^ (s.re - 1 / 2) := by
  have hAp : 0 < A := by linarith
  have hA0 : A ≠ 0 := ne_of_gt hAp
  have hA2 : 0 < A ^ 2 := by positivity
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  let C := Real.sqrt (2 * Real.pi)
  have hC : 0 < C := by dsimp [C]; positivity
  let E : ℂ → ℂ := fun z => -(Real.pi * Complex.I * z / 2) +
    ((z - 1 / 2) / (A : ℂ)) ^ 2 - (z - 1 / 2) * (Real.log A : ℂ)
  let F : ℂ → ℂ := fun z => Complex.Gamma z * Complex.exp (E z)
  have hE (z : ℂ) : (E z).re = Real.pi * z.im / 2 +
      ((z.re - 1 / 2) ^ 2 - z.im ^ 2) / A ^ 2 - (z.re - 1 / 2) * Real.log A := by
    simp [E, pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
    <;> field_simp [hA0]
  have hFnorm (z : ℂ) : ‖F z‖ = ‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2 +
      ((z.re - 1 / 2) ^ 2 - z.im ^ 2) / A ^ 2 - (z.re - 1 / 2) * Real.log A) := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_exp, hE]
  have hhalf (z : ℂ) (hz : z.re = 1 / 2) : ‖F z‖ ≤ 6 * C := by
    have he : z = (1 / 2 : ℂ) + z.im * Complex.I := by apply Complex.ext <;> simp [hz]
    have hg := LeanLab.PNTPort.ZetaZeros.norm_Gamma_half_mul_exp_le z.im
    rw [← he] at hg
    rw [hFnorm, hz]
    have hx : Real.pi * z.im / 2 + ((1 / 2 - 1 / 2) ^ 2 - z.im ^ 2) / A ^ 2 -
        (1 / 2 - 1 / 2) * Real.log A ≤ Real.pi * z.im / 2 := by
      norm_num
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg z.im)) hA2.le
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (norm_nonneg _)).trans
      (hg.trans (by dsimp [C]; nlinarith [hC]))
  have hthree (z : ℂ) (hz : z.re = 3 / 2) : ‖F z‖ ≤ 6 * C := by
    let y := z.im
    have he : z = ((1 / 2 : ℂ) + y * Complex.I) + 1 := by
      apply Complex.ext <;> simp [hz, y] <;> norm_num
    have hne : (1 / 2 : ℂ) + y * Complex.I ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; norm_num at this
    have hg := LeanLab.PNTPort.ZetaZeros.norm_Gamma_half_mul_exp_le y
    have hn : ‖(1 / 2 : ℂ) + y * Complex.I‖ ≤ 1 + |y| := by
      have hh := norm_add_le (1 / 2 : ℂ) ((y : ℂ) * Complex.I)
      simpa using hh.trans (by norm_num)
    have hy : 1 + |y| ≤ 2 * A * Real.exp (y ^ 2 / A ^ 2) := by
      have hx := Real.add_one_le_exp (y ^ 2 / A ^ 2)
      have he : |y| / A ≤ 1 + y ^ 2 / A ^ 2 := by
        apply (div_le_iff₀ hAp).mpr
        have hh : A * (1 + y ^ 2 / A ^ 2) = A + y ^ 2 / A := by field_simp
        rw [mul_comm _ A, hh]
        have hp : (|y| - A) * A ≤ y ^ 2 := by
          nlinarith [sq_nonneg (|y| - A / 2), sq_abs y]
        have hh := (le_div_iff₀ hAp).mpr hp
        linarith
      have hy' := mul_le_mul_of_nonneg_left (he.trans (by simpa only [add_comm] using hx)) hAp.le
      have hid : A * (|y| / A) = |y| := by field_simp
      rw [hid] at hy'
      have h1 : 1 ≤ Real.exp (y ^ 2 / A ^ 2) := Real.one_le_exp (by positivity)
      nlinarith
    have hex : Real.exp (y ^ 2 / A ^ 2) *
        Real.exp ((1 - y ^ 2) / A ^ 2 - Real.log A) = Real.exp (1 / A ^ 2) / A := by
      rw [← Real.exp_add]
      rw [show y ^ 2 / A ^ 2 + ((1 - y ^ 2) / A ^ 2 - Real.log A) =
        1 / A ^ 2 - Real.log A by ring]
      rw [Real.exp_sub, Real.exp_log hAp]
    have hsmall : Real.exp (1 / A ^ 2) ≤ 3 := by
      apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
      exact (div_le_one hA2).mpr (by nlinarith)
    rw [hFnorm, hz]
    norm_num only [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, one_pow, one_mul]
    rw [Real.exp_sub]
    -- regroup the oscillatory damping and the Gaussian weight
    have hid : ‖Complex.Gamma z‖ *
        (Real.exp (Real.pi * z.im / 2 + (1 - z.im ^ 2) / A ^ 2) / Real.exp (Real.log A)) =
        (‖Complex.Gamma ((1 / 2 : ℂ) + y * Complex.I)‖ * Real.exp (Real.pi * y / 2)) *
          ‖(1 / 2 : ℂ) + y * Complex.I‖ *
          Real.exp ((1 - y ^ 2) / A ^ 2 - Real.log A) := by
      have hgz : Complex.Gamma z = ((1 / 2 : ℂ) + y * Complex.I) *
          Complex.Gamma ((1 / 2 : ℂ) + y * Complex.I) := by
        rw [he, Complex.Gamma_add_one _ hne]
      rw [hgz, norm_mul, Real.exp_add, Real.exp_sub]
      dsimp [y]
      ring
    rw [hid]
    calc
      _ ≤ C * ((2 * A * Real.exp (y ^ 2 / A ^ 2)) *
          Real.exp ((1 - y ^ 2) / A ^ 2 - Real.log A)) := by
        have hpoly := hn.trans hy
        have hp := mul_le_mul hg hpoly (norm_nonneg _) hC.le
        nlinarith [mul_le_mul_of_nonneg_right hp
          (Real.exp_pos ((1 - y ^ 2) / A ^ 2 - Real.log A)).le]
      _ = 2 * C * Real.exp (1 / A ^ 2) := by rw [mul_assoc (2 * A), hex]; field_simp
      _ ≤ 6 * C := by nlinarith
  have hbound : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (3 / 2)) := by
    let K := Real.Gamma (1 / 2) + Real.Gamma (3 / 2)
    refine ⟨K * Real.exp (Real.pi ^ 2 * A ^ 2 / 16 + 1), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzr : 1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2 := hz
    have hG := LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le hzr.1 hzr.2
    have hK : 0 ≤ K := (norm_nonneg _).trans hG
    have hEbound : Real.pi * z.im / 2 + ((z.re - 1 / 2) ^ 2 - z.im ^ 2) / A ^ 2 -
        (z.re - 1 / 2) * Real.log A ≤ Real.pi ^ 2 * A ^ 2 / 16 + 1 := by
      have hx : (z.re - 1 / 2) ^ 2 ≤ 1 := by nlinarith [hzr.1, hzr.2]
      have hn := mul_nonneg (show 0 ≤ z.re - 1 / 2 by linarith) hlogA
      have hquad : Real.pi * z.im / 2 - z.im ^ 2 / A ^ 2 ≤ Real.pi ^ 2 * A ^ 2 / 16 := by
        have hp : (Real.pi * z.im / 2 - Real.pi ^ 2 * A ^ 2 / 16) * A ^ 2 ≤ z.im ^ 2 := by
          nlinarith [sq_nonneg (z.im - Real.pi * A ^ 2 / 4)]
        have hh := (le_div_iff₀ hA2).mpr hp
        linarith
      have hdiv : (z.re - 1 / 2) ^ 2 / A ^ 2 ≤ 1 :=
        (div_le_one hA2).mpr (by nlinarith)
      rw [sub_div]
      nlinarith
    rw [Function.comp_apply, hFnorm]
    exact mul_le_mul hG (Real.exp_le_exp.mpr hEbound) (Real.exp_pos _).le hK
  have hdiff : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip (1 / 2) (3 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hcl : closure (Complex.HadamardThreeLines.verticalStrip (1 / 2) (3 / 2)) ⊆
        {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2} := by
      apply closure_minimal
      · intro w hw; exact ⟨hw.1.le, hw.2.le⟩
      · exact (isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)
    have hz0 : 0 < z.re := by have hh := hcl hz; linarith [hh.1]
    have hne : ∀ m : ℕ, z ≠ -m := by
      intro m hm; have hh := congrArg Complex.re hm; simp at hh
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hd : DifferentiableAt ℂ F z := by
      apply (Complex.differentiableAt_Gamma z hne).mul
      apply Complex.differentiableAt_exp.comp
      dsimp [E]
      fun_prop
    exact hd.differentiableWithinAt
  have hcore (z : ℂ) (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 3 / 2) (hy : |z.im| ≤ A) :
      ‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2) ≤
        18 * C * A ^ (z.re - 1 / 2) := by
    have hh := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' (by norm_num : (1 / 2 : ℝ) < 3 / 2)
      (show z ∈ Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (3 / 2) from ⟨hz, hz'⟩) hdiff hbound
      (fun w hw => hhalf w hw) (fun w hw => hthree w hw)
    have hr : (3 / 2 : ℝ) - 1 / 2 = 1 := by norm_num
    rw [hr, div_one, ← Real.rpow_add (by positivity : 0 < 6 * C)] at hh
    have he : 1 - (z.re - 1 / 2) + (z.re - 1 / 2) = 1 := by ring
    rw [he, Real.rpow_one] at hh
    have hid : ‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2) = ‖F z‖ *
        Real.exp ((z.im ^ 2 - (z.re - 1 / 2) ^ 2) / A ^ 2 + (z.re - 1 / 2) * Real.log A) := by
      rw [hFnorm, mul_assoc, ← Real.exp_add]
      congr 1
      ring
    have hfac : Real.exp ((z.im ^ 2 - (z.re - 1 / 2) ^ 2) / A ^ 2 +
        (z.re - 1 / 2) * Real.log A) ≤ 3 * A ^ (z.re - 1 / 2) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hAp]
      have hsq : z.im ^ 2 ≤ A ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.im) hy 2
      have hexp : Real.exp ((z.im ^ 2 - (z.re - 1 / 2) ^ 2) / A ^ 2) ≤ 3 := by
        apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
        exact (div_le_one hA2).mpr (by nlinarith [sq_nonneg (z.re - 1 / 2)])
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hexp
        (Real.exp_pos ((z.re - 1 / 2) * Real.log A)).le
    rw [hid]
    have hp := mul_le_mul hh hfac (Real.exp_pos _).le (by positivity : 0 ≤ 6 * C)
    nlinarith
  by_cases hi : 0 ≤ s.im
  · simpa only [abs_of_nonneg hi] using hcore s hs hs' ht
  · have hh := hcore (star s) (by simpa using hs) (by simpa using hs') (by simpa using ht)
    simpa only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.Gamma_conj,
      Complex.norm_conj, abs_of_neg (lt_of_not_ge hi)] using hh

/-- P0093 page 158 equation 4.6. The radial primitive retains its diagonal
scale L rather than replacing the real denominator by an absolute constant. -/
theorem radial_mellin_scaled501 (a b L d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hL : 0 < L) :
    ‖∫ u : ℝ in a..b,
      (u : ℂ) ^ (-((1 + 1 / L : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      4 * a ^ (-(1 / L)) * L / (1 + L * |d|) := by
  have hε : 0 < 1 / L := by positivity
  have hs := radial_mellin_integral_bound452 a b (1 / L) d ha (ha.trans_le hab) hε
  have hpow : b ^ (-(1 / L)) ≤ a ^ (-(1 / L)) :=
    Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  have hsq : 0 ≤ (1 / L) ^ 2 + d ^ 2 := by positivity
  have hden : 0 < Real.sqrt ((1 / L) ^ 2 + d ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg d])
  have he : 1 / L ≤ Real.sqrt ((1 / L) ^ 2 + d ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg d]
  have hd : |d| ≤ Real.sqrt ((1 / L) ^ 2 + d ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs d, sq_nonneg (1 / L)]
  have hscale : 1 + L * |d| ≤ 2 * L * Real.sqrt ((1 / L) ^ 2 + d ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left (show 1 / L + |d| ≤
      2 * Real.sqrt ((1 / L) ^ 2 + d ^ 2) by linarith) hL.le
    have hid : L * (1 / L + |d|) = 1 + L * |d| := by field_simp
    rw [hid] at hh
    nlinarith
  calc
    _ ≤ (a ^ (-(1 / L)) + b ^ (-(1 / L))) /
        Real.sqrt ((1 / L) ^ 2 + d ^ 2) := hs
    _ ≤ (2 * a ^ (-(1 / L))) / Real.sqrt ((1 / L) ^ 2 + d ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    _ ≤ _ := by
      rw [div_le_div_iff₀ hden (by positivity : 0 < 1 + L * |d|)]
      have hh := mul_le_mul_of_nonneg_left hscale
        (show 0 ≤ 2 * a ^ (-(1 / L)) by positivity)
      nlinarith

/-- P0093 page 158 equation 4.6. The antitone radial Jacobian preserves
the scaled diagonal estimate with an absolute factor eight. -/
theorem radial_jacobian_scaled501 (N a b L d : ℝ) (hN : 0 < N)
    (ha : 2 / N ≤ a) (hab : a ≤ b) (hL : 0 < L) :
    ‖∫ u : ℝ in a..b, radialJacobian452 N u •
      (u : ℂ) ^ (-((1 + 1 / L : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      8 * a ^ (-(1 / L)) * L / (1 + L * |d|) := by
  have hap : 0 < a := (div_pos (by norm_num) hN).trans_le ha
  have hbp : 0 < b := hap.trans_le hab
  have hNa : 2 ≤ N * a := by have hh := (div_le_iff₀ hN).mp ha; nlinarith
  have hNb : 2 ≤ N * b := by nlinarith
  have hja := radial_jacobian_bounds452 N a hN hap hNa
  have hjb := radial_jacobian_bounds452 N b hN hbp hNb
  have hanti : AntitoneOn (radialJacobian452 N) (Set.Icc a b) := by
    intro u hu v hv huv
    exact radial_jacobian_antitone452 N hN (ha.trans hu.1) (ha.trans hv.1) huv
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro hz
    linarith [hz.1]
  have hg : IntervalIntegrable
      (fun u : ℝ => (u : ℂ) ^ (-((1 + 1 / L : ℝ) : ℂ) - (d : ℂ) * Complex.I))
      volume a b := intervalIntegral.intervalIntegrable_cpow (Or.inr hzero)
  obtain ⟨ξ, hξ, hmean⟩ :=
    exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn hab hjb.1.le hanti hg
  have hinner := radial_mellin_scaled501 a ξ L d hap hξ.1 hL
  have hprod := mul_le_mul hja.2 hinner (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 2 * (4 * a ^ (-(1 / L)) * L / (1 + L * |d|)) := hmean.trans hprod
    _ = _ := by ring

/-- P0093 page 158 after equation 4.6. An elementary lower bound for the
integrated reciprocal difference kernel retains its logarithmic growth. -/
theorem difference_kernel_lower_log501 (T : ℝ) (hT : 0 ≤ T) :
    2 * T * Real.log (T + 1) ≤ differenceKernel376 T := by
  let f : ℝ → ℝ := fun x => 1 / (1 + |x|)
  have hf : Continuous f := continuous_const.div (continuous_const.add continuous_abs)
    (fun x => ne_of_gt (by positivity))
  have hn : ∀ x, 0 ≤ f x := fun x => by dsimp [f]; positivity
  have hp : (∫ x in (0 : ℝ)..T, f x) = Real.log (T + 1) := by
    have hfull := reciprocal_abs_integral376 T hT
    have heven := symmetric_integral376 f hf (fun x => by dsimp [f]; rw [abs_neg]) T
    change (∫ x in -T..T, f x) = _ at hfull
    linarith
  have hm : (∫ x in -T..0, f x) = Real.log (T + 1) := by
    calc
      _ = ∫ x in (0 : ℝ)..T, f (-x) := by
        simpa using (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := T)).symm
      _ = ∫ x in (0 : ℝ)..T, f x := by simp only [f, abs_neg]
      _ = _ := hp
  have hinner (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      Real.log (T + 1) ≤ ∫ u in -T..T, f (t + u) := by
    rw [intervalIntegral.integral_comp_add_left]
    by_cases ht0 : 0 ≤ t
    · rw [← hp]
      exact intervalIntegral.integral_mono_interval (by linarith [ht.2]) hT
        (by linarith) (ae_of_all _ hn) (hf.intervalIntegrable _ _)
    · rw [← hm]
      exact intervalIntegral.integral_mono_interval (by linarith)
        (by linarith) (by linarith [ht.1]) (ae_of_all _ hn) (hf.intervalIntegrable _ _)
  have hcont : Continuous (fun t : ℝ => ∫ u in -T..T, f (t + u)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) (-T) T
  have hmono := intervalIntegral.integral_mono_on (show -T ≤ T by linarith)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.log (T + 1)) volume (-T) T)
    (hcont.intervalIntegrable _ _) hinner
  have hchange : differenceKernel376 T = ∫ t in -T..T, ∫ u in -T..T, f (t + u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hh := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => 1 / (1 + |t + u|)) (a := -T) (b := T)
    simpa only [neg_neg, sub_eq_add_neg] using hh
  rw [hchange]
  simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add,
    ← two_mul, mul_assoc] using hmono

/-- P0093 page 158 equation 4.6. Resolving the diagonal at scale one over L
does not increase the integrated difference kernel by more than a factor eight
when one is at most L and L is at most the frequency radius. -/
theorem scaled_difference_kernel501 (L T : ℝ) (hL : 1 ≤ L) (hLT : L ≤ T) :
    (∫ t in -T..T, ∫ u in -T..T, L / (1 + L * |t - u|)) ≤
      8 * differenceKernel376 T := by
  have hLp : 0 < L := by linarith
  have hT : 0 ≤ T := by linarith
  let f : ℝ → ℝ := fun x => L / (1 + L * |x|)
  have hf : Continuous f := continuous_const.div
    (continuous_const.add (continuous_const.mul continuous_abs))
    (fun x => ne_of_gt (by positivity))
  have hchange : (∫ t in -T..T, ∫ u in -T..T, L / (1 + L * |t - u|)) =
      ∫ t in -T..T, ∫ u in -T..T, f (t + u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hh := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => L / (1 + L * |t + u|)) (a := -T) (b := T)
    simpa only [neg_neg, sub_eq_add_neg] using hh
  have hscale : (∫ v in -(2 * T)..(2 * T), f v) =
      2 * Real.log (2 * T * L + 1) := by
    calc
      _ = L * (∫ v in -(2 * T)..(2 * T), 1 / (1 + |v * L|)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v hv
        simp only [f, abs_mul, abs_of_pos hLp]
        ring
      _ = ∫ v in -(2 * T * L)..(2 * T * L), 1 / (1 + |v|) := by
        simpa only [smul_eq_mul, neg_mul] using
          (intervalIntegral.smul_integral_comp_mul_right
            (fun v : ℝ => 1 / (1 + |v|)) L (a := -(2 * T)) (b := 2 * T))
      _ = _ := reciprocal_abs_integral376 (2 * T * L) (by positivity)
  have hlog : Real.log (2 * T * L + 1) ≤ 4 * Real.log (T + 1) := by
    calc
      _ ≤ Real.log ((2 * T + 1) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg T])
      _ = 2 * Real.log (2 * T + 1) := Real.log_pow _ _
      _ ≤ 2 * Real.log ((T + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg T])
      _ = 4 * Real.log (T + 1) := by rw [Real.log_pow]; ring
  have hlower := difference_kernel_lower_log501 T hT
  calc
    _ = ∫ t in -T..T, ∫ u in -T..T, f (t + u) := hchange
    _ ≤ 2 * T * (∫ v in -(2 * T)..(2 * T), f v) :=
      kernel_box_bound376 f hf (fun x => by dsimp [f]; positivity) T hT
    _ = 4 * T * Real.log (2 * T * L + 1) := by rw [hscale]; ring
    _ ≤ 16 * T * Real.log (T + 1) := by nlinarith
    _ ≤ 8 * differenceKernel376 T := by linarith

/-- P0093 page 158 after equation 4.6. On the truncated frequency window,
the line coefficient bound is at most 216 B0 times log cubed N. -/
theorem coefficient_window501 (N : ℕ) (hN : 3 ≤ N) (R B0 : ℝ)
    (hR1 : 1 ≤ R) (hR : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) (t : ℝ)
    (ht : t ∈ Set.Icc (-((N : ℝ) / R * Real.log N ^ 3))
      ((N : ℝ) / R * Real.log N ^ 3)) :
    ‖M t‖ ≤ 216 * B0 * Real.log N ^ 3 := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hRp : 0 < R := by linarith
  have hlog1 : 1 ≤ Real.log N :=
    Real.le_log_iff_exp_le hNp |>.mpr (Real.exp_one_lt_three.le.trans hNr)
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hRN : R ≤ (N : ℝ) := by
    calc
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  let V := (N : ℝ) / R
  let T := V * Real.log N ^ 3
  have hV1 : 1 ≤ V := (le_div_iff₀ hRp).mpr (by simpa only [one_mul] using hRN)
  have hVN : V ≤ N := (div_le_iff₀ hRp).mpr (by nlinarith)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hV1 (one_le_pow₀ hlog1)
  have htT : |t| ≤ T := abs_le.mpr ht
  have hlog : Real.log (|t| + 2) ≤ 5 * Real.log N := by
    exact (Real.log_le_log (by positivity : 0 < |t| + 2)
      (by linarith : |t| + 2 ≤ 2 * T + 1)).trans
      (frequency_window_log376 N V hNr (by linarith) hVN)
  have hbound : Real.log ((N : ℝ) * (|t| + 2)) ≤ 6 * Real.log N := by
    rw [Real.log_mul (ne_of_gt hNp) (ne_of_gt (by positivity : 0 < |t| + 2))]
    linarith
  have hnonneg : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg t])
  calc
    ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := hM.2 t
    _ ≤ B0 * (6 * Real.log N) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hbound 3) hB0
    _ = 216 * B0 * Real.log N ^ 3 := by ring

/-- P0093 page 157 before equation 4.4. On the finite contour window, the
Gamma polynomial factor is bounded by an absolute constant. -/
theorem gamma_line_window501 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (t : ℝ) (ht : t ∈ Set.Icc (-((N : ℝ) / R * Real.log N ^ 3))
      ((N : ℝ) / R * Real.log N ^ 3)) :
    ‖Complex.Gamma (mellinLine1622 N t)‖ * Real.exp (Real.pi * |t| / 2) ≤
      18 * Real.sqrt (2 * Real.pi) * Real.exp 4 := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hLp : 1 ≤ Real.log N :=
    Real.le_log_iff_exp_le hNp |>.mpr (Real.exp_one_lt_three.le.trans hNr)
  have hLpos : 0 < Real.log N := by linarith
  have hRp : 0 < R := by linarith
  have hVN : (N : ℝ) / R ≤ N := (div_le_iff₀ hRp).mpr (by nlinarith)
  have hlogN : Real.log N ≤ N := by
    linarith [Real.log_le_sub_one_of_pos hNp]
  have hT : (N : ℝ) / R * Real.log N ^ 3 ≤ (N : ℝ) ^ 4 := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ 3 :=
        mul_le_mul hVN (pow_le_pow_left₀ hLpos.le hlogN 3) (by positivity) hNp.le
      _ = _ := by ring
  have htN : |t| ≤ (N : ℝ) ^ 4 := (abs_le.mpr ht).trans hT
  have hinv : 1 / Real.log N ≤ 1 := (div_le_one hLpos).mpr hLp
  have hlineRe : (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hlineIm : (mellinLine1622 N t).im = t := by
    simp only [mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, zero_add]
  have hg := gamma_window501 ((N : ℝ) ^ 4) (one_le_pow₀ (by linarith))
    (mellinLine1622 N t) (by rw [hlineRe]; exact le_add_of_nonneg_right (by positivity))
    (by rw [hlineRe]; linarith) (by simpa only [hlineIm] using htN)
  have hpow : ((N : ℝ) ^ 4) ^ ((mellinLine1622 N t).re - 1 / 2) = Real.exp 4 := by
    rw [hlineRe, show (1 / 2 + 1 / Real.log (N : ℝ)) - 1 / 2 =
      1 / Real.log (N : ℝ) by ring, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    field_simp [ne_of_gt hLpos]
    <;> norm_num
  simpa only [hlineIm, hpow] using hg

/-- P0093 page 157 equation 4.4. Polar factorization keeps the signed radial
frequency difference and the real angular frequency sum separate. -/
theorem cpow_pair_polar501 (z : ℂ) (hz : z ≠ 0) (σ t u : ℝ) :
    z ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      (starRingEnd ℂ) (z ^ (-((σ : ℂ) + (u : ℂ) * Complex.I))) =
    (‖z‖ : ℂ) ^ (-((2 * σ : ℝ) : ℂ) - ((t - u : ℝ) : ℂ) * Complex.I) *
      ((Real.exp ((t + u) * z.arg) : ℝ) : ℂ) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [Complex.cpow_def_of_ne_zero hz, Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hn))]
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.log_re, Complex.log_im, Complex.log_ofReal_re,
      Complex.arg_ofReal_of_nonneg hn.le, Complex.mul_re, Complex.mul_im]
    <;> ring

/-- P0093 page 157 second mean value step after equation 4.4. For a
nonnegative frequency sum, the normalized angular weight is nondecreasing
and at most one on the vertical line with positive real part. -/
theorem phase_weight501 (c k S : ℝ) (hc : 0 < c) (hk : 0 < k) (hS : 0 ≤ S) :
    Monotone (fun α : ℝ => Real.exp (-S * (Real.pi / 2 -
      (((c : ℂ) + ((k * α : ℝ) : ℂ) * Complex.I)).arg))) ∧
    ∀ α : ℝ, Real.exp (-S * (Real.pi / 2 -
      (((c : ℂ) + ((k * α : ℝ) : ℂ) * Complex.I)).arg)) ≤ 1 := by
  let Z : ℝ → ℂ := fun α => (c : ℂ) + ((k * α : ℝ) : ℂ) * Complex.I
  have hre (α : ℝ) : (Z α).re = c := by simp [Z]
  have him (α : ℝ) : (Z α).im = k * α := by simp [Z]
  have harg (α : ℝ) : (Z α).arg = Real.arctan (k * α / c) := by
    have hrange : |(Z α).arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hc))
    have hh := Real.arctan_tan (abs_lt.mp hrange).1 (abs_lt.mp hrange).2
    rw [Complex.tan_arg, hre, him] at hh
    exact hh.symm
  have hm : Monotone (fun α : ℝ => (Z α).arg) := by
    intro x y hxy
    change (Z x).arg ≤ (Z y).arg
    rw [harg, harg]
    apply Real.arctan_strictMono.monotone
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hk.le) hc.le
  change Monotone (fun α : ℝ => Real.exp (-S * (Real.pi / 2 - (Z α).arg))) ∧
    ∀ α : ℝ, Real.exp (-S * (Real.pi / 2 - (Z α).arg)) ≤ 1
  constructor
  · intro x y hxy
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hm hxy) hS
    nlinarith
  · intro α
    apply Real.exp_le_one_iff.mpr
    have hh : (Z α).arg ≤ Real.pi / 2 :=
      Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hc.le))
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hS) (sub_nonneg.mpr hh)

/-- P0093 pages 157 and 158 equations 4.4 through 4.6. A nonnegative
nondecreasing weight bounded by one preserves the scaled radial estimate
after the alpha change of variables. -/
theorem radial_weighted_alpha501 (N k a b L d : ℝ) (hN : 0 < N) (hk : 0 < k)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 < L) (hNa : 2 ≤ N * k * a)
    (w : ℝ → ℝ) (hwa : 0 ≤ w a) (hwb : w b ≤ 1)
    (hw : MonotoneOn w (Set.Icc a b)) :
    ‖∫ α in a..b, w α •
      ((Real.sqrt ((1 / N) ^ 2 + (k * α) ^ 2) : ℝ) : ℂ) ^
        (-((1 + 1 / L : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      (8 / k) * Real.sqrt ((1 / N) ^ 2 + (k * a) ^ 2) ^ (-(1 / L)) *
        L / (1 + L * |d|) := by
  let ρ : ℝ → ℝ := fun x => Real.sqrt ((1 / N) ^ 2 + x ^ 2)
  let p : ℂ := -((1 + 1 / L : ℝ) : ℂ) - (d : ℂ) * Complex.I
  let g : ℝ → ℂ := fun α => (ρ (k * α) : ℂ) ^ p
  have hrpos (x : ℝ) : 0 < ρ x := by dsimp [ρ]; positivity
  have hbase : Continuous (fun α : ℝ => (ρ (k * α) : ℂ)) := by dsimp [ρ]; fun_prop
  have hg : Continuous g := hbase.cpow continuous_const (fun α => Or.inl (hrpos _))
  obtain ⟨ξ, hξ, hmean⟩ :=
    exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
      hab hwa hw (hg.intervalIntegrable a b)
  have hξp : 0 < ξ := ha.trans_le hξ.1
  have hbp : 0 < b := ha.trans_le hab
  have hka : k * a ≤ ρ (k * a) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (1 / N)]
  have hρmono : MonotoneOn ρ (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.sqrt_le_sqrt
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    nlinarith
  have hρaξ : ρ (k * a) ≤ ρ (k * ξ) :=
    hρmono (show 0 ≤ k * a by positivity) (show 0 ≤ k * ξ by positivity) (mul_le_mul_of_nonneg_left hξ.1 hk.le)
  have hρξb : ρ (k * ξ) ≤ ρ (k * b) :=
    hρmono (show 0 ≤ k * ξ by positivity) (show 0 ≤ k * b by positivity) (mul_le_mul_of_nonneg_left hξ.2 hk.le)
  have hlow : 2 / N ≤ ρ (k * ξ) := by
    have hh : 2 / N ≤ k * a := (div_le_iff₀ hN).mpr (by nlinarith)
    exact hh.trans (hka.trans hρaξ)
  have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ p) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (fun x hx => Or.inl hx)
  have hchange := mellin_radial_substitution452 N (k * ξ) (k * b) hN (by positivity)
    (mul_le_mul_of_nonneg_left hξ.2 hk.le) (fun x : ℝ => (x : ℂ) ^ p) hc
  have hrad := radial_jacobian_scaled501 N (ρ (k * ξ)) (ρ (k * b)) L d
    hN hlow hρξb hL
  have hsub : (∫ α in ξ..b, g α) = (1 / k : ℝ) •
      (∫ x in k * ξ..(k * b), (ρ x : ℂ) ^ p) := by
    simpa only [g, one_div] using intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => (ρ x : ℂ) ^ p) (a := ξ) (b := b) (ne_of_gt hk)
  have hnorm : ‖∫ α in ξ..b, g α‖ ≤ (1 / k) *
      (8 * ρ (k * ξ) ^ (-(1 / L)) * L / (1 + L * |d|)) := by
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / k)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change ‖∫ x in k * ξ..(k * b),
      ((Real.sqrt ((1 / N) ^ 2 + x ^ 2) : ℝ) : ℂ) ^ p‖ ≤ _
    rw [hchange]
    exact hrad
  have hpow : ρ (k * ξ) ^ (-(1 / L)) ≤ ρ (k * a) ^ (-(1 / L)) :=
    Real.rpow_le_rpow_of_nonpos (hrpos _) hρaξ (neg_nonpos.mpr (by positivity))
  change ‖∫ α in a..b, w α • g α‖ ≤ _
  calc
    _ ≤ w b * ‖∫ α in ξ..b, g α‖ := hmean
    _ ≤ ‖∫ α in ξ..b, g α‖ := mul_le_of_le_one_left (norm_nonneg _) hwb
    _ ≤ (1 / k) * (8 * ρ (k * ξ) ^ (-(1 / L)) * L / (1 + L * |d|)) := hnorm
    _ ≤ (1 / k) * (8 * ρ (k * a) ^ (-(1 / L)) * L / (1 + L * |d|)) := by
      gcongr
    _ = _ := by dsimp [ρ]; ring

/-- LEAF. P0093 pages 157 and 158 equations 4.4 through 4.6. The pure signed
alpha kernel on the positive sum region has reciprocal difference decay with
the diagonal scale log N retained. No coefficient occurs in this estimate. -/
theorem outer_kernel_difference501 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ t ∈ Set.Icc (-((N : ℝ) / R * Real.log N ^ 3))
            ((N : ℝ) / R * Real.log N ^ 3),
        ∀ u ∈ Set.Icc (-((N : ℝ) / R * Real.log N ^ 3))
            ((N : ℝ) / R * Real.log N ^ 3), 0 ≤ t + u →
          ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤
          C * Real.log N / (1 + Real.log N * |t - u|) := by
  let G : ℝ := 18 * Real.sqrt (2 * Real.pi) * Real.exp 4
  refine ⟨8 * Real.exp 2 * G ^ 2, by dsimp [G]; positivity, 16383, ?_⟩
  intro N hN R hR1 hRN t ht u hu hsum
  have hN16 : 16384 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hLp : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let k : ℝ := 2 * Real.pi
  let a : ℝ := 4 / N
  let b : ℝ := 1 / R
  let L : ℝ := Real.log N / 2
  let σ : ℝ := 1 / 2 + 1 / Real.log N
  let S : ℝ := t + u
  let d : ℝ := t - u
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) + ((k * α : ℝ) : ℂ) * Complex.I
  let ρ : ℝ → ℝ := fun α => Real.sqrt ((1 / (N : ℝ)) ^ 2 + (k * α) ^ 2)
  let p : ℂ := -((1 + 1 / L : ℝ) : ℂ) - (d : ℂ) * Complex.I
  let w : ℝ → ℝ := fun α => Real.exp (-S * (Real.pi / 2 - (Z α).arg))
  let D : ℂ := (Complex.Gamma (mellinLine1622 N t) *
    (starRingEnd ℂ) (Complex.Gamma (mellinLine1622 N u))) * ((Real.exp (Real.pi * S / 2) : ℝ) : ℂ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk1 : 1 ≤ k := by dsimp [k]; nlinarith [Real.pi_gt_three]
  have ha : 0 < a := by dsimp [a]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    rw [div_le_div_iff₀ hNp hRp]
    simpa only [one_mul] using four_mul_le487 N hN16 R hRN
  have hNa : 2 ≤ (N : ℝ) * k * a := by
    have hh : (N : ℝ) * k * a = 8 * Real.pi := by
      dsimp [k, a]
      field_simp
      <;> ring
    rw [hh]
    nlinarith [Real.pi_gt_three]
  have hw := phase_weight501 (1 / (N : ℝ)) k S (by positivity) hk hsum
  have hrad := radial_weighted_alpha501 (N : ℝ) k a b L d hNp hk ha hab hL hNa w
    (by dsimp [w]; positivity) (hw.2 b) (hw.1.monotoneOn _)
  have hσ : 2 * σ = 1 + 1 / L := by dsimp [σ, L]; field_simp [ne_of_gt hLp] <;> ring
  have hz (α : ℝ) : Z α ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hh
    exact (ne_of_gt (by positivity : 0 < 1 / (N : ℝ))) hh
  have hρ (α : ℝ) : ‖Z α‖ = ρ α := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Z, ρ, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      mul_one, add_zero, zero_add, sub_zero]
    congr 1
    ring
  have hpair (α : ℝ) : mellinKernel442 N α t *
      (starRingEnd ℂ) (mellinKernel442 N α u) = D * (w α • (ρ α : ℂ) ^ p) := by
    have hpolar := cpow_pair_polar501 (Z α) (hz α) σ t u
    have hp : -((2 * σ : ℝ) : ℂ) - ((t - u : ℝ) : ℂ) * Complex.I = p := by
      dsimp [p, d]
      rw [hσ]
    have he : Real.exp (Real.pi * S / 2) * w α = Real.exp ((t + u) * (Z α).arg) := by
      dsimp [w, S]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Complex.Gamma (mellinLine1622 N t) *
          (starRingEnd ℂ) (Complex.Gamma (mellinLine1622 N u))) *
          (Z α ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
            (starRingEnd ℂ) (Z α ^ (-((σ : ℂ) + (u : ℂ) * Complex.I)))) := by
        dsimp [mellinKernel442, mellinLine1622, Z, σ, k]
        simp only [map_mul]
        ring
      _ = (Complex.Gamma (mellinLine1622 N t) *
          (starRingEnd ℂ) (Complex.Gamma (mellinLine1622 N u))) *
          ((ρ α : ℂ) ^ p * ((Real.exp ((t + u) * (Z α).arg) : ℝ) : ℂ)) := by
        rw [hpolar, hρ, hp]
      _ = D * (w α • (ρ α : ℂ) ^ p) := by
        rw [← he]
        dsimp [D]
        simp only [Complex.real_smul, Complex.ofReal_mul]
        ring
  have hD : ‖D‖ ≤ G ^ 2 := by
    have hgt := gamma_line_window501 N hN3 R hR1 t ht
    have hgu := gamma_line_window501 N hN3 R hR1 u hu
    have he : Real.exp (Real.pi * S / 2) ≤
        Real.exp (Real.pi * |t| / 2) * Real.exp (Real.pi * |u| / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [S]
      nlinarith [le_abs_self t, le_abs_self u, Real.pi_pos]
    dsimp only [D]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (‖Complex.Gamma (mellinLine1622 N t)‖ *
          ‖Complex.Gamma (mellinLine1622 N u)‖) *
          (Real.exp (Real.pi * |t| / 2) * Real.exp (Real.pi * |u| / 2)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.exp (Real.pi * |t| / 2)) *
          (‖Complex.Gamma (mellinLine1622 N u)‖ * Real.exp (Real.pi * |u| / 2)) := by ring
      _ ≤ G * G := mul_le_mul hgt hgu (by positivity) (by dsimp [G]; positivity)
      _ = G ^ 2 := by ring
  have hρlow : 1 / (N : ℝ) ≤ ρ a := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (k * a)]
  have hpow : ρ a ^ (-(1 / L)) ≤ Real.exp 2 := by
    calc
      _ ≤ (1 / (N : ℝ)) ^ (-(1 / L)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hρlow (neg_nonpos.mpr (by positivity))
      _ = (N : ℝ) ^ (1 / L) := by
        rw [one_div, Real.inv_rpow hNp.le, ← Real.rpow_neg]
        · congr 1; ring
        · exact hNp.le
      _ = Real.exp 2 := by
        rw [Real.rpow_def_of_pos hNp]
        congr 1
        dsimp [L]
        field_simp
  have hratio : L / (1 + L * |d|) ≤ Real.log N / (1 + Real.log N * |d|) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + L * |d|)
      (by positivity : 0 < 1 + Real.log N * |d|)]
    have hh : L ≤ Real.log N := by dsimp [L]; linarith
    nlinarith
  have hk8 : 8 / k ≤ 8 := (div_le_iff₀ hk).mpr (by linarith)
  have hrad' : ‖∫ α in a..b, w α • (ρ α : ℂ) ^ p‖ ≤
      8 * Real.exp 2 * Real.log N / (1 + Real.log N * |d|) := by
    calc
      _ ≤ (8 / k) * ρ a ^ (-(1 / L)) * L / (1 + L * |d|) := hrad
      _ = ((8 / k) * ρ a ^ (-(1 / L))) * (L / (1 + L * |d|)) := by ring
      _ ≤ (8 * Real.exp 2) * (Real.log N / (1 + Real.log N * |d|)) :=
        mul_le_mul (mul_le_mul hk8 hpow (by positivity) (by norm_num)) hratio
          (by positivity) (by positivity)
      _ = _ := by ring
  have hi : (∫ α in a..b, mellinKernel442 N α t *
      (starRingEnd ℂ) (mellinKernel442 N α u)) =
      D * (∫ α in a..b, w α • (ρ α : ℂ) ^ p) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun α _ => hpair α)
  change ‖∫ α in a..b, mellinKernel442 N α t *
      (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤ _
  rw [hi, norm_mul]
  calc
    _ ≤ G ^ 2 * (8 * Real.exp 2 * Real.log N / (1 + Real.log N * |d|)) :=
      mul_le_mul hD hrad' (norm_nonneg _) (by positivity)
    _ = (8 * Real.exp 2 * G ^ 2) * Real.log N /
        (1 + Real.log N * |t - u|) := by dsimp [d]; ring


/-- LEAF. P0093 page 158 equation 4.6 and the following displayed bound.
On the finite frequency square with nonnegative frequency sum, the coefficient
weighted alpha integral is bounded by log N to power seven divided by one plus
log N times the frequency difference. The alpha integral remains inside its norm. -/
theorem outer_difference_pointwise501 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          ∀ t ∈ Set.Icc (-((N : ℝ) / R * Real.log N ^ 3))
              ((N : ℝ) / R * Real.log N ^ 3),
          ∀ u ∈ Set.Icc (-((N : ℝ) / R * Real.log N ^ 3))
              ((N : ℝ) / R * Real.log N ^ 3), 0 ≤ t + u →
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤
              C * Real.log N ^ 7 / (1 + Real.log N * |t - u|) := by
  obtain ⟨C, hC, N0, hkernel⟩ := outer_kernel_difference501
  refine ⟨(216 * B0) ^ 2 * C, by positivity, max 3 N0, ?_⟩
  intro N hN R hR1 hR M hM t ht u hu hsum
  have hN3 : 3 ≤ N := by omega
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hMt := coefficient_window501 N hN3 R B0 hR1 hR hB0.le M hM t ht
  have hMu := coefficient_window501 N hN3 R B0 hR1 hR hB0.le M hM u hu
  have hcoeff := mul_le_mul hMt hMu (norm_nonneg _) (by positivity : 0 ≤ 216 * B0 * Real.log N ^ 3)
  have hk := hkernel N hN0 R hR1 hR t ht u hu hsum
  calc
    _ ≤ (216 * B0 * Real.log N ^ 3) * (216 * B0 * Real.log N ^ 3) *
        (C * Real.log N / (1 + Real.log N * |t - u|)) :=
      mul_le_mul hcoeff hk (norm_nonneg _) (by positivity)
    _ = ((216 * B0) ^ 2 * C) * Real.log N ^ 7 /
        (1 + Real.log N * |t - u|) := by ring


/-- LEAF. P0093 page 158 equations 4.5 and 4.6. Positive frequency difference
region with nonnegative frequency sum. The pointwise estimate retains the scale
log N divided by one plus log N times the frequency difference. Integrating that
scaled kernel costs an absolute constant times the original difference kernel. -/
theorem outer_finite_difference_region487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
              ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
                if 0 ≤ t + u then
                  ‖M t‖ * ‖M u‖ *
                    ‖∫ α in (4 / (N : ℝ))..(1 / R),
                      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
                else 0) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  obtain ⟨C, hC, N0, hpoint⟩ := outer_difference_pointwise501 B0 hB0
  refine ⟨8 * C, by positivity, max 3 N0, ?_⟩
  intro N hN R hR1 hR M hM
  have hN3 : 3 ≤ N := by omega
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNp : (0 : ℝ) < N := by linarith
  have hLp : 1 ≤ Real.log N :=
    Real.le_log_iff_exp_le hNp |>.mpr (Real.exp_one_lt_three.le.trans hNr)
  have hL0 : 0 ≤ Real.log N := by linarith
  have hRp : 0 < R := by linarith
  have hRN : R ≤ (N : ℝ) := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
         _ ≤ (N : ℝ) ^ (1 : ℝ) :=
           Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
         _ = N := Real.rpow_one _
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hLT : Real.log N ≤ T := by
    have hv : 1 ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa only [one_mul] using hRN)
    have hc : Real.log N ≤ Real.log N ^ 3 := by nlinarith [sq_nonneg (Real.log N - 1)]
    exact hc.trans (le_mul_of_one_le_left (by positivity) hv)

  let H : ℝ × ℝ → ℝ := fun z => ‖M z.1‖ * ‖M z.2‖ *
    ‖∫ α in (4 / (N : ℝ))..(1 / R),
      mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖
  let G : ℝ × ℝ → ℝ := fun z => C * Real.log N ^ 7 /
    (1 + Real.log N * |z.1 - z.2|)
  let S : Set (ℝ × ℝ) := {z | 0 ≤ z.1 + z.2}
  let Q := Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  have hQ : MeasurableSet Q := measurableSet_uIoc.prod measurableSet_uIoc
  have hH : Continuous H := by
    exact ((hM.1.comp continuous_fst).norm.mul (hM.1.comp continuous_snd).norm).mul
      (continuous_alphaKernel_integral487 N (by omega) _ _).norm
  have hG : Continuous G := by
    dsimp [G]
    exact continuous_const.div
      (continuous_const.add (continuous_const.mul (continuous_fst.sub continuous_snd).abs))
      (fun z => ne_of_gt (by positivity))
  have hHint : IntegrableOn H Q :=
    (hH.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hGint : IntegrableOn G Q :=
    (hG.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hFint : IntegrableOn (S.indicator H) Q := hHint.indicator hS
  have hmono : (∫ z in Q, S.indicator H z) ≤ ∫ z in Q, G z := by
    apply setIntegral_mono_on hFint hGint hQ
    intro z hz
    by_cases hs : z ∈ S
    · rw [Set.indicator_of_mem hs]
      have hzt : z.1 ∈ Set.Icc (-T) T := by
        simpa only [Set.uIcc_of_le (show -T ≤ T by linarith)] using
          (Set.uIoc_subset_uIcc hz.1)
      have hzu : z.2 ∈ Set.Icc (-T) T := by
        simpa only [Set.uIcc_of_le (show -T ≤ T by linarith)] using
          (Set.uIoc_subset_uIcc hz.2)
      exact hpoint N hN0 R hR1 hR M hM z.1 hzt z.2 hzu hs
    · rw [Set.indicator_of_notMem hs]
      dsimp [G]
      positivity
  have hleft := iterated_eq_box487 (fun t u => S.indicator H (t,u)) (-T) T hFint
  have hright := iterated_eq_box487 (fun t u => G (t,u)) (-T) T hGint
  change (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then H (t,u) else 0) ≤
    (8 * C) * Real.log N ^ 6 * differenceKernel376 T
  calc
    _ = ∫ z in Q, S.indicator H z := by simpa only [Set.indicator_apply, S, Set.mem_ofPred_eq] using hleft
    _ ≤ ∫ z in Q, G z := hmono
    _ = ∫ t in -T..T, ∫ u in -T..T, G (t,u) := hright.symm
    _ = C * Real.log N ^ 6 *
        (∫ t in -T..T, ∫ u in -T..T,
          Real.log N / (1 + Real.log N * |t - u|)) := by
      calc
        _ = ∫ t in -T..T, ∫ u in -T..T,
            (C * Real.log N ^ 6) *
              (Real.log N / (1 + Real.log N * |t - u|)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          apply intervalIntegral.integral_congr
          intro u hu
          dsimp [G]
          ring
        _ = _ := by simp only [intervalIntegral.integral_const_mul]
    _ ≤ C * Real.log N ^ 6 * (8 * differenceKernel376 T) :=
      mul_le_mul_of_nonneg_left (scaled_difference_kernel501 (Real.log N) T hLp hLT)
        (by positivity)
    _ = (8 * C) * Real.log N ^ 6 * differenceKernel376 T := by ring


/-- LEAF. Negative frequency sum region, t + u negative. There the Gamma asymptotics on the line
supply exponential decay in the sum of the frequencies, which dominates the polynomial weight of
the coefficient bound, so the region costs log N to the seventh times the exponential sum kernel at
the radius N over R times log cubed N. -/
theorem outer_finite_sum_region487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
              ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
                if 0 ≤ t + u then 0
                else
                  ‖M t‖ * ‖M u‖ *
                    ‖∫ α in (4 / (N : ℝ))..(1 / R),
                      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  refine ⟨4722366482869645213696 * B0 ^ 2, by positivity, 16383, ?_⟩
  intro N hN R hR1 hRN M hM
  have hN16 : 16384 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    refine Real.le_log_iff_exp_le hNpos |>.mpr ?_
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
  have hlog4 : (1 : ℝ) ≤ Real.log N ^ 4 := by
    have h0 : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
    have hsq : (1 : ℝ) ≤ Real.log N * Real.log N := by nlinarith [hlog1]
    have hgroup : Real.log N ^ 4 = (Real.log N * Real.log N) * (Real.log N * Real.log N) :=
      by ring
    rw [hgroup]
    nlinarith [hsq, mul_nonneg h0 h0]
  have h4R : 4 * R ≤ (N : ℝ) := four_mul_le487 N hN16 R hRN
  -- the radius is at least two, so the sum kernel obeys its lower bound
  have hT2 : 2 ≤ (N : ℝ) / R * Real.log N ^ 3 := by
    have hNR : (4 : ℝ) ≤ (N : ℝ) / R := by
      rw [le_div_iff₀ hRpos]
      linarith
    have hlog3 : (1 : ℝ) ≤ Real.log N ^ 3 := by
      have h0 : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
      nlinarith [hlog1, h0, sq_nonneg (Real.log N)]
    calc (2 : ℝ) ≤ 4 * 1 := by norm_num
      _ ≤ (N : ℝ) / R * Real.log N ^ 3 :=
          mul_le_mul hNR hlog3 (by norm_num) (by linarith)
  have hlow := sumKernel_lower487 ((N : ℝ) / R * Real.log N ^ 3) hT2
  have hcore := sum_region_core487 N hN16 R hR1 hRN B0 hB0 M hM
  have hquarter := exp_quarter_le487
  -- everything is nonnegative
  have hNn : (0 : ℝ) ≤ N := hNpos.le
  have hRn : (0 : ℝ) ≤ R := hRpos.le
  have hlogn : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
  have hprod : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 3 := by positivity
  -- the comparison of the two right hand sides
  refine hcore.trans ?_
  have hstep : (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 ≤
      4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7 *
        sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
    -- replace the sum kernel by its lower bound
    have hsumlb : Real.exp (-(Real.pi / 4)) * (((N : ℝ) / R * Real.log N ^ 3) / 2) ≤
        sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := hlow
    have hkey : (1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2) ≤
        sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) :=
      le_trans (by
        have h1 : (1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2) ≤
            Real.exp (-(Real.pi / 4)) * (((N : ℝ) / R * Real.log N ^ 3) / 2) :=
          mul_le_mul_of_nonneg_right hquarter (by positivity)
        exact h1) hsumlb
    -- multiply the lower bound by the positive factor
    have hfac : (0 : ℝ) ≤ 4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7 := by positivity
    have hmul : (4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7) *
          ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2)) ≤
        (4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7) *
          sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) :=
      mul_le_mul_of_nonneg_left hkey hfac
    refine le_trans ?_ hmul
    -- and the explicit arithmetic
    have hlog6nn : (0 : ℝ) ≤ Real.log N ^ 6 := by positivity
    have hB0nn : (0 : ℝ) ≤ B0 ^ 2 := by positivity
    have hbase : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 6 := by positivity
    have harith : (N : ℝ) / R * Real.log N ^ 6 * 36893488147419103232 ≤
        (4722366482869645213696 : ℝ) * Real.log N ^ 7 *
          ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2)) := by
      have hgroup : Real.log N ^ 7 = Real.log N ^ 6 * Real.log N := by ring
      rw [hgroup]
      nlinarith [hlog4, hlog6nn, hlogn, hprod, hNn, hRn,
        mul_nonneg hlogn hlog6nn, mul_nonneg hlog6nn hlog6nn,
        mul_nonneg (mul_nonneg hlogn hlog6nn) hlogn]
    have hB0sq : (0 : ℝ) ≤ B0 ^ 2 := hB0nn
    calc (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232
        = B0 ^ 2 * ((N : ℝ) / R * Real.log N ^ 6 * 36893488147419103232) := by ring
      _ ≤ B0 ^ 2 * ((4722366482869645213696 : ℝ) * Real.log N ^ 7 *
            ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2))) :=
          mul_le_mul_of_nonneg_left harith hB0sq
      _ = (4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7) *
            ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2)) := by ring
  exact hstep

/-- The finite signed outer square of the contour truncated at radius N over R times log cubed N.
This is proved from the integrability leaf, the square and Fubini reduction, the region split and
the two region estimates; the two region constants are added. -/
theorem outer_finite_square487_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2)
            volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  obtain ⟨Cd, hCd, Nd, hd⟩ := outer_finite_difference_region487 B0 hB0
  obtain ⟨Cs, hCs, Ns, hs⟩ := outer_finite_sum_region487 B0 hB0
  obtain ⟨Ni, hi⟩ := outer_finite_square_integrable487
  refine ⟨Cd + Cs, by positivity, max 8 (max Ni (max Nd Ns)), ?_⟩
  intro N hN R hR1 hR M hM
  have hN8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNd : Nd < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNs : Ns < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hl0 : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (pow_nonneg hl0 3)
  have hd0 : 0 ≤ differenceKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
  have hs0 : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun u => (Real.exp_pos _).le)
  have hk0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) ^ 2 := by positivity
  have hk1 : (1 / (2 * Real.pi)) ^ 2 ≤ 1 := by
    have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hle : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc (1 / (2 * Real.pi)) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = 1 := one_pow 2
  have hl6d : 0 ≤ Real.log N ^ 6 * differenceKernel376 T :=
    mul_nonneg (pow_nonneg hl0 6) hd0
  have hl7s : 0 ≤ Real.log N ^ 7 * sumKernel376 T :=
    mul_nonneg (pow_nonneg hl0 7) hs0
  have e1 : (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T) ≤
      Cd * Real.log N ^ 6 * differenceKernel376 T := by
    calc (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T)
        ≤ 1 * (Cd * Real.log N ^ 6 * differenceKernel376 T) :=
          mul_le_mul_of_nonneg_right hk1
            (mul_nonneg (mul_nonneg hCd.le (pow_nonneg hl0 6)) hd0)
      _ = Cd * Real.log N ^ 6 * differenceKernel376 T := one_mul _
  have e2 : (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T) ≤
      Cs * Real.log N ^ 7 * sumKernel376 T := by
    calc (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T)
        ≤ 1 * (Cs * Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_right hk1
            (mul_nonneg (mul_nonneg hCs.le (pow_nonneg hl0 7)) hs0)
      _ = Cs * Real.log N ^ 7 * sumKernel376 T := one_mul _
  have e3 : Cd * Real.log N ^ 6 * differenceKernel376 T ≤
      (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T := by
    calc Cd * Real.log N ^ 6 * differenceKernel376 T
        = Cd * (Real.log N ^ 6 * differenceKernel376 T) := by ring
      _ ≤ (Cd + Cs) * (Real.log N ^ 6 * differenceKernel376 T) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCs.le) hl6d
      _ = (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T := by ring
  have e4 : Cs * Real.log N ^ 7 * sumKernel376 T ≤
      (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := by
    calc Cs * Real.log N ^ 7 * sumKernel376 T
        = Cs * (Real.log N ^ 7 * sumKernel376 T) := by ring
      _ ≤ (Cd + Cs) * (Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCd.le) hl7s
      _ = (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := by ring
  refine ⟨hi N hNi R M hM.1, ?_⟩
  calc
    (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2)
        ≤ (1 / (2 * Real.pi)) ^ 2 *
          ∫ t in -T..T, ∫ u in -T..T,
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ :=
          outer_finite_modulus_reduction487 N (by omega) R M hM.1
    _ ≤ (1 / (2 * Real.pi)) ^ 2 *
          ((∫ t in -T..T, ∫ u in -T..T,
              if 0 ≤ t + u then
                ‖M t‖ * ‖M u‖ *
                  ‖∫ α in (4 / (N : ℝ))..(1 / R),
                    mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
              else 0) +
            (∫ t in -T..T, ∫ u in -T..T,
              if 0 ≤ t + u then 0
              else
                ‖M t‖ * ‖M u‖ *
                  ‖∫ α in (4 / (N : ℝ))..(1 / R),
                    mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)) :=
          mul_le_mul_of_nonneg_left (outer_finite_region_split487 N R M hM.1) hk0
    _ ≤ (1 / (2 * Real.pi)) ^ 2 *
          (Cd * Real.log N ^ 6 * differenceKernel376 T +
            Cs * Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hd N hNd R hR1 hR M hM) (hs N hNs R hR1 hR M hM)) hk0
    _ = (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T) +
          (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T) := by ring
    _ ≤ Cd * Real.log N ^ 6 * differenceKernel376 T +
          Cs * Real.log N ^ 7 * sumKernel376 T := add_le_add e1 e2
    _ ≤ (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T +
          (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := add_le_add e3 e4

end LeanLab.Linnik1951
