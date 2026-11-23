module

public import LeanLab.Linnik1951.SPLIT_grh_mellin_transfer519
public import LeanLab.Linnik1951.Gamma442

/-!
P0093 Linnik 1951, page 156 equation 4.1 and page 159 before equation 5.1.
Proves the shift of the Mellin line from re s equal to 2 to re s equal to 1/2 plus 1/ln N
for the integrand z to the power minus s times Gamma s times G s, by Cauchy on rectangles.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Topology

/-- Textbook step behind P0093 page 156: Cauchy's theorem on the rectangle with corners
a minus T i and b plus T i, for a function differentiable at every point of the closed
vertical strip a at most re s at most b. The difference of the two vertical integrals
times i equals the difference of the two horizontal integrals. -/
theorem rect_identity_b1122x (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s) (T : ℝ) :
    Complex.I * ((∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      ∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * Complex.I)) =
    (∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * Complex.I)) -
      ∫ x : ℝ in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (⟨a, -T⟩ : ℂ) (⟨b, T⟩ : ℂ) ?_
  · dsimp only at H
    simp only [smul_eq_mul] at H
    linear_combination H
  · intro s hs
    rw [Complex.mem_reProdIm] at hs
    obtain ⟨h1, -⟩ := hs
    dsimp only at h1
    rw [Set.uIcc_of_le hab] at h1
    exact (hd s h1.1 h1.2).differentiableWithinAt

/-- Textbook step behind P0093 page 156: a vertical line of integration may be moved across
a strip where the integrand is holomorphic, integrable on both edges, and bounded by a
function of the height that tends to zero. The horizontal sides of the rectangles vanish
in the limit and the vertical sides tend to the two line integrals. -/
theorem strip_shift_b1122x (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (ha : Integrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)))
    (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hfg : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g |s.im|) :
    ∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I) := by
  have hre : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by intro x y; simp
  have him : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by intro x y; simp
  set Hh : ℝ → ℂ := fun y => ∫ x : ℝ in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I) with hHh
  have hH : ∀ y : ℝ, ‖Hh y‖ ≤ g |y| * |b - a| := by
    intro y
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have := hfg ((x : ℂ) + (y : ℂ) * Complex.I) (by rw [hre]; exact hx.1.le)
      (by rw [hre]; exact hx.2)
    rwa [him] at this
  have hlim0 : Tendsto (fun T : ℝ => Hh T - Hh (-T)) atTop (𝓝 0) := by
    have hg2 : Tendsto (fun T : ℝ => 2 * |b - a| * g T) atTop (𝓝 0) := by
      simpa using hg.const_mul (2 * |b - a|)
    apply squeeze_zero_norm' _ hg2
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have h1 := hH T
    have h2 := hH (-T)
    rw [abs_neg, abs_of_nonneg hT] at h2
    rw [abs_of_nonneg hT] at h1
    calc ‖Hh T - Hh (-T)‖ ≤ ‖Hh T‖ + ‖Hh (-T)‖ := norm_sub_le _ _
      _ ≤ g T * |b - a| + g T * |b - a| := add_le_add h1 h2
      _ = 2 * |b - a| * g T := by ring
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hlim1 := (hvb.sub hva).const_mul Complex.I
  have heq : (fun T : ℝ => Complex.I * ((∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      ∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * Complex.I))) =
      fun T : ℝ => Hh T - Hh (-T) := by
    funext T
    exact rect_identity_b1122x f a b hab hd T
  rw [heq] at hlim1
  have h0 := tendsto_nhds_unique hlim1 hlim0
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have := (mul_eq_zero.mp h0).resolve_left hI
  exact (sub_eq_zero.mp this).symm

/-- Textbook integrability step for P0093 page 157: every power of the absolute value
times a two sided exponential decay is integrable on the real line. -/
theorem abs_pow_exp_integrable_b1122x (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) := by
  have hk : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(δ * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := 1) (b := δ) (by linarith [Nat.cast_nonneg (α := ℝ) k])
        (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) (Set.Ioi 0) := by
    refine hk.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [abs_of_pos (show (0 : ℝ) < t from ht)]
  have hc : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  have hn : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) (Set.Iic 0) := by
    have hn := (show IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|)))
      (Set.Ici (-0)) from by simpa using hc).comp_neg_Iic
    simpa only [abs_neg] using hn
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hn.union hp

/-- Textbook integrability step for P0093 page 157: the weight one plus absolute t to the
fifth times exp of minus delta absolute t is integrable for delta positive. -/
theorem quintic_exp_integrable_b1122x (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ 5 * Real.exp (-(δ * |t|))) := by
  have h0 := abs_pow_exp_integrable_b1122x δ hδ 0
  have h5 := abs_pow_exp_integrable_b1122x δ hδ 5
  refine Integrable.mono' ((h0.add h5).const_mul 32) ?_ (ae_of_all _ fun t => ?_)
  · exact (by fun_prop : Continuous fun t : ℝ =>
      (1 + |t|) ^ 5 * Real.exp (-(δ * |t|))).aestronglyMeasurable
  · have hx : 0 ≤ |t| := abs_nonneg t
    have hpoly : (1 + |t|) ^ 5 ≤ 32 * (|t| ^ 0 + |t| ^ 5) := by
      rcases le_total |t| 1 with h | h
      · have h32 : (1 + |t|) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have h5 : 0 ≤ |t| ^ 5 := by positivity
        rw [pow_zero]
        linarith
      · have h32 : (1 + |t|) ^ 5 ≤ (2 * |t|) ^ 5 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 5
        rw [mul_pow] at h32
        rw [pow_zero]
        linarith
    have he : 0 < Real.exp (-(δ * |t|)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith

/-- Textbook limit for P0093 page 156: A times one plus u to the fifth times exp of minus
delta u tends to 0 as u tends to infinity, for delta positive. It kills the horizontal
sides of the rectangles. -/
theorem quintic_exp_tendsto_b1122x (A δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun u : ℝ => A * ((1 + u) ^ 5 * Real.exp (-(δ * u)))) atTop (𝓝 0) := by
  have hv : Tendsto (fun u : ℝ => δ * (1 + u)) atTop atTop :=
    (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop hδ
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp hv).const_mul
    (A * Real.exp δ / δ ^ 5)
  rw [mul_zero] at h
  refine h.congr (fun u => ?_)
  simp only [Function.comp]
  rw [show -(δ * (1 + u)) = -δ + -(δ * u) by ring, Real.exp_add, Real.exp_neg δ]
  have he : Real.exp δ ≠ 0 := (Real.exp_pos δ).ne'
  have hd : δ ^ 5 ≠ 0 := pow_ne_zero 5 hδ.ne'
  field_simp

/-- P0093 page 157 Gamma decay, extended by the functional equation Gamma of s equals
s minus 1 times Gamma of s minus 1 to the strip from 1/2 to 2: the norm of Gamma s is at
most square root of 2 pi times 9 times one plus absolute im s squared times exp of minus
pi absolute im s over 2. -/
theorem gamma_strip_two_b1122x (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * (9 * (1 + |s.im|) ^ 2) *
      Real.exp (-(Real.pi * |s.im| / 2)) := by
  have ht := abs_nonneg s.im
  rcases le_or_gt s.re (3 / 2) with h | h
  · have hg := gamma_absolute_decay442 s hlo h
    have hn : ‖s + 1‖ ≤ 9 * (1 + |s.im|) ^ 2 := by
      have hh := Complex.norm_le_abs_re_add_abs_im (s + 1)
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
        add_zero] at hh
      rw [abs_of_pos (by linarith : 0 < s.re + 1)] at hh
      nlinarith
    calc ‖Complex.Gamma s‖ ≤ _ := hg
      _ ≤ _ := by gcongr
  · have hs1 : s - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    have hrec : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
      have := Complex.Gamma_add_one (s - 1) hs1
      rwa [sub_add_cancel] at this
    have hre1 : (s - 1).re = s.re - 1 := by simp
    have him1 : (s - 1).im = s.im := by simp
    have hg := gamma_absolute_decay442 (s - 1) (by rw [hre1]; linarith)
      (by rw [hre1]; linarith)
    rw [sub_add_cancel, him1] at hg
    have hn1 : ‖s - 1‖ ≤ 3 * (1 + |s.im|) := by
      have hh := Complex.norm_le_abs_re_add_abs_im (s - 1)
      rw [hre1, him1, abs_of_pos (by linarith : 0 < s.re - 1)] at hh
      linarith
    have hn2 : ‖s‖ ≤ 3 * (1 + |s.im|) := by
      have hh := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos (by linarith : 0 < s.re)] at hh
      linarith
    have hg2 : ‖Complex.Gamma (s - 1)‖ ≤ Real.sqrt (2 * Real.pi) * (3 * (1 + |s.im|)) *
        Real.exp (-(Real.pi * |s.im| / 2)) := hg.trans (by gcongr)
    rw [hrec, norm_mul]
    calc ‖s - 1‖ * ‖Complex.Gamma (s - 1)‖
        ≤ (3 * (1 + |s.im|)) * (Real.sqrt (2 * Real.pi) * (3 * (1 + |s.im|)) *
            Real.exp (-(Real.pi * |s.im| / 2))) := by gcongr
      _ = _ := by ring

/-- P0093 page 156 size of the kernel z to the power minus s: for z nonzero and
0 at most re s at most 2, its norm is at most one plus norm z to the minus 2, times
exp of absolute arg z times absolute im s. -/
theorem cpow_neg_bound_b1122x (z : ℂ) (hz : z ≠ 0) (s : ℂ) (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖z ^ (-s)‖ ≤ (1 + ‖z‖ ^ (-2 : ℝ)) * Real.exp (|Complex.arg z| * |s.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hz]
  simp only [Complex.neg_re, Complex.neg_im]
  have hx : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp : ‖z‖ ^ (-s.re) ≤ 1 + ‖z‖ ^ (-2 : ℝ) := by
    rcases le_total 1 ‖z‖ with h | h
    · have := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith : -s.re ≤ 0)
      have := Real.rpow_nonneg hx.le (-2 : ℝ)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hx h (by linarith : (-2 : ℝ) ≤ -s.re)
      linarith
  have he : 1 / Real.exp (Complex.arg z * -s.im) ≤ Real.exp (|Complex.arg z| * |s.im|) := by
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [← abs_mul]
    have h1 := le_abs_self (Complex.arg z * s.im)
    have h2 : -(Complex.arg z * -s.im) = Complex.arg z * s.im := by ring
    linarith
  rw [div_eq_mul_one_div]
  exact mul_le_mul hp he (by positivity) (by positivity)

/-- P0093 page 159 bound for log L on the line, made polynomial: for N at least 2 the
logarithm of N times absolute t plus 2 lies between 0 and log N plus 1 times one plus
absolute t. -/
theorem log_poly_b1122x (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    0 ≤ Real.log ((N : ℝ) * (|t| + 2)) ∧
      Real.log ((N : ℝ) * (|t| + 2)) ≤ (Real.log N + 1) * (1 + |t|) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht := abs_nonneg t
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  refine ⟨Real.log_nonneg (by nlinarith), ?_⟩
  rw [Real.log_mul (by positivity) (by positivity)]
  have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < |t| + 2)
  nlinarith

/-- P0093 page 156 decay of the Mellin integrand z to the minus s times Gamma s times G s
on the closed strip from 1/2 plus 1/ln N to 2: a constant times one plus absolute im s to
the fifth times exp of minus pi over 2 minus absolute arg z, times absolute im s. -/
theorem integrand_bound_b1122x (N : ℕ) (hN : 2 ≤ N) (G : ℂ → ℂ) (B0 : ℝ)
    (hGb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3)
    (z : ℂ) (hz : z ≠ 0) (s : ℂ) (h1 : 1 / 2 + 1 / Real.log N ≤ s.re) (h2 : s.re ≤ 2) :
    ‖z ^ (-s) * Complex.Gamma s * G s‖ ≤
      ((1 + ‖z‖ ^ (-2 : ℝ)) * Real.sqrt (2 * Real.pi) * 9 * |B0| * (Real.log N + 1) ^ 3) *
        ((1 + |s.im|) ^ 5 * Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |s.im|))) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hc : 1 / 2 ≤ s.re := by
    have : 0 < 1 / Real.log N := by positivity
    linarith
  have hA := cpow_neg_bound_b1122x z hz s (by linarith) h2
  have hB := gamma_strip_two_b1122x s hc h2
  obtain ⟨hl0, hl1⟩ := log_poly_b1122x N hN s.im
  have hC : ‖G s‖ ≤ |B0| * (Real.log N + 1) ^ 3 * (1 + |s.im|) ^ 3 := by
    calc ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 := hGb s h1 h2
      _ ≤ |B0| * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |B0| * ((Real.log N + 1) * (1 + |s.im|)) ^ 3 := by gcongr
      _ = _ := by ring
  rw [norm_mul, norm_mul]
  calc ‖z ^ (-s)‖ * ‖Complex.Gamma s‖ * ‖G s‖
      ≤ ((1 + ‖z‖ ^ (-2 : ℝ)) * Real.exp (|Complex.arg z| * |s.im|)) *
        (Real.sqrt (2 * Real.pi) * (9 * (1 + |s.im|) ^ 2) *
          Real.exp (-(Real.pi * |s.im| / 2))) *
        (|B0| * (Real.log N + 1) ^ 3 * (1 + |s.im|) ^ 3) := by gcongr
    _ = _ := by
      have : Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |s.im|)) =
          Real.exp (|Complex.arg z| * |s.im|) * Real.exp (-(Real.pi * |s.im| / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      ring

/-- P0093 page 156 equation 4.1 and page 159 before equation 5.1: under the bound on G on
the strip, the Mellin integral on the line re s equal to 1/2 plus 1/ln N equals the one on
the line re s equal to 2, by Cauchy on rectangles and the decay of Gamma. -/
theorem mellin_line_shift_proof_b1122 (N : ℕ) (hN : 2 ≤ N) (G : ℂ → ℂ)
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re}) (B0 : ℝ)
    (hGb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3) (α : ℝ) :
    mellinU519 N (fun t : ℝ => G (mellinLine519 N t)) α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
            G ((2 : ℂ) + (t : ℂ) * Complex.I) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hc12 : 1 / 2 < 1 / 2 + 1 / Real.log N := by
    have : 0 < 1 / Real.log N := by positivity
    linarith
  have hc2 : 1 / 2 + 1 / Real.log N ≤ 2 := by
    have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
    have h23 : (2 : ℝ) / 3 ≤ Real.log N := by
      have := Real.log_two_gt_d9; linarith
    have : 1 / Real.log N ≤ 3 / 2 := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hzre : 0 < z.re := by
    have h := one_div_pos.mpr (show (0 : ℝ) < N by linarith)
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact h
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  have hδ : 0 < Real.pi / 2 - |Complex.arg z| := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
    linarith
  let F : ℂ → ℂ := fun s => z ^ (-s) * Complex.Gamma s * G s
  have hFd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ F s := by
    intro s hs
    have hnp : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hG' : DifferentiableAt ℂ G s :=
      hGd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
    exact ((differentiableAt_id.neg.const_cpow (Or.inl hz)).mul
      (Complex.differentiableAt_Gamma s hnp)).mul hG'
  let A : ℝ := (1 + ‖z‖ ^ (-2 : ℝ)) * Real.sqrt (2 * Real.pi) * 9 * |B0| *
    (Real.log N + 1) ^ 3
  let g : ℝ → ℝ := fun u => A * ((1 + u) ^ 5 * Real.exp (-((Real.pi / 2 - |Complex.arg z|) * u)))
  have hFb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 → ‖F s‖ ≤ g |s.im| :=
    fun s h1 h2 => integrand_bound_b1122x N hN G B0 hGb z hz s h1 h2
  have hgi : Integrable (fun t : ℝ => g |t|) :=
    (quintic_exp_integrable_b1122x _ hδ).const_mul A
  have hline : ∀ σ : ℝ, 1 / 2 + 1 / Real.log N ≤ σ → σ ≤ 2 →
      Integrable (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    intro σ h1 h2
    have hre : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by intro t; simp
    have him : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by intro t; simp
    refine hgi.mono' ?_ (ae_of_all _ fun t => ?_)
    · have hcont : Continuous (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (hFd _ (by rw [hre]; linarith)).continuousAt.comp (by fun_prop)
      exact hcont.aestronglyMeasurable
    · have := hFb ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact h1) (by rw [hre]; exact h2)
      rwa [him] at this
  have hg : Tendsto g atTop (𝓝 0) := quintic_exp_tendsto_b1122x A _ hδ
  have key := strip_shift_b1122x F (1 / 2 + 1 / Real.log N) 2 hc2
    (fun s h1 _ => hFd s (by linarith)) (hline _ le_rfl hc2) (hline 2 hc2 le_rfl) g hg hFb
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num] at key
  rw [mellinU519]
  exact congrArg (fun w => ((1 / (2 * Real.pi) : ℝ) : ℂ) * w) key

end LeanLab.Linnik1951.Task519
