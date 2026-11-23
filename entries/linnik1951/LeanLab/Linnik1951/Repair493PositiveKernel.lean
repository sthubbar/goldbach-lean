module

public import LeanLab.Linnik1951.Repair493ContourData
public import LeanLab.Linnik1951.SPLIT_outer_kernel_integrable442

/-!
P0093 page 157 before equation 4.4. Positive parameter kernel regularity.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 157 finite contour. At every positive natural N a continuous
coefficient gives a jointly continuous signed Mellin integrand. The real part
of its base is positive and the line avoids every Gamma pole. -/
theorem continuous_mellin_integrand_positive493 (N : ℕ) (hN : 1 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2 * M p.2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
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
    have hinv : 0 ≤ 1 / Real.log N := by positivity
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  exact (((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)).mul (hM.comp continuous_snd)

/-- P0093 page 157 logarithmic line weight. For every positive natural N,
the log cubed weight is bounded by a positive constant times one plus absolute
t to power three. -/
theorem log_weight_cubic_positive493 (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ C * (1 + |t|) ^ 3 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  refine ⟨(Real.log N + 1) ^ 3, by positivity, ?_⟩
  intro t
  have ht : 0 ≤ |t| := abs_nonneg t
  have hp : 0 < |t| + 2 := by positivity
  have hlog : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [mul_nonneg (Nat.cast_nonneg N) ht])
  have hbound : Real.log ((N : ℝ) * (|t| + 2)) ≤ (Real.log N + 1) * (1 + |t|) := by
    rw [Real.log_mul hNp.ne' hp.ne']
    have hi := Real.log_le_sub_one_of_pos hp
    nlinarith [mul_nonneg hL ht]
  calc
    _ ≤ ((Real.log N + 1) * (1 + |t|)) ^ 3 := pow_le_pow_left₀ hlog hbound 3
    _ = _ := by ring

/-- P0093 page 157 before equation 4.4. The absolute Mellin kernel with its
log cubed line weight is integrable for every positive natural N and fixed phase.
A Gamma recurrence covers the small parameter strip. -/
theorem weighted_kernel_integrable_positive493 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hln : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  let σ : ℝ := 1 / 2 + 1 / Real.log N
  have hσlo : (1 / 2 : ℝ) ≤ σ := by
    have hi : 0 ≤ 1 / Real.log N := by positivity
    dsimp [σ]
    linarith
  have hσhi : σ ≤ (5 / 2 : ℝ) := by
    by_cases h1 : N = 1
    · subst N
      norm_num [σ]
    · have h2 : 2 ≤ N := by omega
      have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      have hlow : (1 / 2 : ℝ) ≤ Real.log N := hhalf.trans
        (Real.log_le_log (by norm_num) (by exact_mod_cast h2))
      have hinv : 1 / Real.log N ≤ 2 := (div_le_iff₀ hlog).mpr (by linarith)
      dsimp [σ]
      linarith
  have hre (t : ℝ) : (mellinLine1622 N t).re = σ := by
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, σ]
  have him (t : ℝ) : (mellinLine1622 N t).im = t := by
    simp only [mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hnorm (t c : ℝ) (hc : 0 ≤ σ + c) (hc3 : σ + c ≤ 3) :
      ‖mellinLine1622 N t + (c : ℂ)‖ ≤ 3 + |t| := by
    calc
      _ ≤ |(mellinLine1622 N t + (c : ℂ)).re| +
          |(mellinLine1622 N t + (c : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (σ + c) + |t| := by
        rw [Complex.add_re, hre, Complex.ofReal_re, Complex.add_im, him,
          Complex.ofReal_im, add_zero, abs_of_nonneg hc]
      _ ≤ _ := by linarith
  have hGamma (t : ℝ) : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (3 + |t|) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
    by_cases hs : σ ≤ 3 / 2
    · have hg := gamma_absolute_decay442 (mellinLine1622 N t)
        (by rw [hre]; exact hσlo) (by rw [hre]; exact hs)
      have hn : ‖mellinLine1622 N t + 1‖ ≤ 3 + |t| := by
        simpa only [Complex.ofReal_one] using hnorm t 1 (by linarith) (by linarith)
      calc
        _ ≤ Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t + 1‖ *
            Real.exp (-(Real.pi * |t| / 2)) := by simpa only [him] using hg
        _ ≤ Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by gcongr
        _ ≤ _ := by gcongr; nlinarith [abs_nonneg t]
    · have hslo : (1 / 2 : ℝ) ≤ (mellinLine1622 N t - 1).re := by
        simp only [Complex.sub_re, hre, Complex.one_re]
        linarith
      have hshi : (mellinLine1622 N t - 1).re ≤ (3 / 2 : ℝ) := by
        simp only [Complex.sub_re, hre, Complex.one_re]
        linarith
      have hsne : mellinLine1622 N t - 1 ≠ 0 := by
        intro he
        have hh := congrArg Complex.re he
        simp only [Complex.sub_re, hre, Complex.one_re, Complex.zero_re] at hh
        linarith
      have hn0 : ‖mellinLine1622 N t‖ ≤ 3 + |t| := by
        simpa using hnorm t 0 (by linarith) (by linarith)
      have hn1 : ‖mellinLine1622 N t - 1‖ ≤ 3 + |t| := by
        simpa only [Complex.ofReal_neg, Complex.ofReal_one, ← sub_eq_add_neg] using
          hnorm t (-1) (by linarith) (by linarith)
      have hg := gamma_absolute_decay442 (mellinLine1622 N t - 1) hslo hshi
      have hg' : ‖Complex.Gamma (mellinLine1622 N t - 1)‖ ≤
          Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
        calc
          _ ≤ Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t‖ *
              Real.exp (-(Real.pi * |t| / 2)) := by
            simpa only [sub_add_cancel, Complex.sub_im, him, Complex.one_im, sub_zero] using hg
          _ ≤ _ := by gcongr
      have hrec := Complex.Gamma_add_one (mellinLine1622 N t - 1) hsne
      rw [sub_add_cancel] at hrec
      calc
        _ = ‖mellinLine1622 N t - 1‖ * ‖Complex.Gamma (mellinLine1622 N t - 1)‖ := by
          rw [hrec, norm_mul]
        _ ≤ (3 + |t|) * (Real.sqrt (2 * Real.pi) * (3 + |t|) *
            Real.exp (-(Real.pi * |t| / 2))) := mul_le_mul hn1 hg' (norm_nonneg _) (by positivity)
        _ = _ := by ring
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hzre : z.re = 1 / (N : ℝ) := by simp [z]
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by intro he; simpa [he] using hzpos
  have harg : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzpos)
  let δ : ℝ := Real.pi / 2 - |z.arg|
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let A : ℝ := ‖z‖ ^ (-σ) * Real.sqrt (2 * Real.pi)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpower (t : ℝ) : ‖z ^ (-(mellinLine1622 N t))‖ ≤
      ‖z‖ ^ (-σ) * Real.exp (|t| * |z.arg|) := by
    rw [Complex.norm_cpow_of_ne_zero hz, Complex.neg_re, hre, Complex.neg_im, him,
      div_eq_mul_inv, ← Real.exp_neg]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg z) _)
    apply Real.exp_le_exp.mpr
    calc
      -(z.arg * -t) = z.arg * t := by ring
      _ ≤ |z.arg * t| := le_abs_self _
      _ = |t| * |z.arg| := by rw [abs_mul, mul_comm]
  have hK (t : ℝ) : ‖mellinKernel442 N α t‖ ≤
      A * (3 + |t|) ^ 2 * Real.exp (-(δ * |t|)) := by
    change ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (‖z‖ ^ (-σ) * Real.exp (|t| * |z.arg|)) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) :=
        mul_le_mul (hpower t) (hGamma t) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show -(δ * |t|) = |t| * |z.arg| + -(Real.pi * |t| / 2) by dsimp [δ]; ring,
          Real.exp_add]
        dsimp [A]
        ring
  obtain ⟨C, hC, hlog⟩ := log_weight_cubic_positive493 N hN
  have hk (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(δ * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := δ)
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 5) (Set.Ioi 0) := by
    apply (((((hk 5).add ((hk 4).const_mul 5)).add ((hk 3).const_mul 10)).add
      ((hk 2).const_mul 10)).add ((hk 1).const_mul 5)).add (hk 0) |>.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  have hc : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 5) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  have hn : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 5) (Set.Iic 0) := by
    have hn := (show IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 5)
      (Set.Ici (-0)) from by simpa using hc).comp_neg_Iic
    simpa only [abs_neg] using hn
  have hQ : Integrable (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 5) := by
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hn.union hp
  have hpair : Continuous (fun t : ℝ => (α, t)) := continuous_const.prodMk continuous_id
  have hKc : Continuous (fun t : ℝ => mellinKernel442 N α t) := by
    have hj : Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
      simpa only [mul_one] using
        continuous_mellin_integrand_positive493 N hN (fun _ => 1) continuous_const
    simpa only [Function.comp_def] using hj.comp hpair
  have hargcont : Continuous (fun t : ℝ => (N : ℝ) * (|t| + 2)) := by fun_prop
  have hlogcont : Continuous (fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2))) :=
    hargcont.log (fun t => by positivity)
  have hcont : Continuous (fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by fun_prop
  have hln0 (t : ℝ) : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    apply pow_nonneg
    apply Real.log_nonneg
    nlinarith [mul_nonneg hNp.le (abs_nonneg t)]
  apply (hQ.const_mul (9 * A * C)).mono' hcont.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hln0 t))]
  calc
    _ ≤ (A * (3 + |t|) ^ 2 * Real.exp (-(δ * |t|))) * (C * (1 + |t|) ^ 3) :=
      mul_le_mul (hK t) (hlog t) (hln0 t) (by positivity)
    _ ≤ (A * (3 * (1 + |t|)) ^ 2 * Real.exp (-(δ * |t|))) * (C * (1 + |t|) ^ 3) := by
      gcongr
      linarith [abs_nonneg t]
    _ = (9 * A * C) * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 5) := by ring

end LeanLab.Linnik1951
