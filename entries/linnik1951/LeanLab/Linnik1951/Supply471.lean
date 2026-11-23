module

public import LeanLab.Linnik1951.SPLIT1622_mellin
public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
P0093 page 159 Section 5. Zero free regions and logarithm bounds on the Mellin line.
The partial sum integral and disk logarithm are proved standard bridges.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Complex Metric Set MeasureTheory Finset Filter
open scoped Topology


/-- Page 159 Section 5. GRH excludes every nonprincipal zero right of one half. -/
theorem LFunction_ne_zero_right471 (hG : LeanLab.DERZ1997.GRH)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) : DirichletCharacter.LFunction χ s ≠ 0 := by
  unfold LeanLab.DERZ1997.GRH at hG
  by_cases h1 : s.re < 1
  · intro hz
    have := hG q χ s hz (by linarith) h1
    linarith
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (le_of_not_gt h1)

/-- Page 156 Lemma 2. The shifted Mellin line lies strictly right of one half. -/
theorem mellinLine_re_gt_half471 (N : ℕ) (hN : 1 < N) (t : ℝ) :
    1 / 2 < (mellinLine1622 N t).re := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl := Real.log_pos hn
  simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero]
  linarith [one_div_pos.mpr hl]

/-- Page 156 Lemma 2. The shifted Mellin line is continuous in height. -/
theorem continuous_mellinLine471 (N : ℕ) : Continuous (mellinLine1622 N) := by
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- Page 159 Section 5. Holomorphy gives continuity of L along the line. -/
theorem continuous_LFunction_line471 (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Continuous fun t : ℝ => DirichletCharacter.LFunction χ (mellinLine1622 N t) := by
  exact (DirichletCharacter.differentiable_LFunction hχ).continuous.comp
    (continuous_mellinLine471 N)

/-- Page 159 Section 5. The real logarithm of the modulus is continuous on a zero free line. -/
theorem continuous_log_norm_line471 (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hz : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0) :
    Continuous fun t : ℝ => Real.log ‖DirichletCharacter.LFunction χ (mellinLine1622 N t)‖ := by
  exact (continuous_LFunction_line471 N q χ hχ).norm.log
    (fun t => norm_ne_zero_iff.mpr (hz t))

/-- Page 159 Section 5. The principal logarithm is continuous if the line image avoids its cut. -/
theorem continuous_lnL_of_slitPlane471 (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hs : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ∈ Complex.slitPlane) :
    Continuous fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t)) := by
  exact (continuous_LFunction_line471 N q χ hχ).clog hs

/-- Page 159 Section 5. The principal logarithm costs at most pi beyond its real part. -/
theorem norm_log_le_log_norm_add_pi471 (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc
    ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |Real.log ‖z‖| + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      linarith [Complex.abs_arg_le_pi z]

/-- Page 159 Section 5. The absolutely convergent anchor series is within three quarters of one. -/
theorem norm_LFunction_sub_one471 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : s.re = 2) :
    ‖DirichletCharacter.LFunction χ s - 1‖ ≤ 3 / 4 := by
  let f : ℕ → ℂ := LSeries.term (fun n => χ n) s
  have hf : Summable f := χ.LSeriesSummable_of_one_lt_re (by linarith)
  have he : (∑' n, f (n + 2)) = DirichletCharacter.LFunction χ s - 1 := by
    have h := hf.sum_add_tsum_nat_add 2
    rw [χ.LFunction_eq_LSeries (by linarith)]
    change (∑' n, f (n + 2)) = (∑' n, f n) - 1
    have hsum : ∑ i ∈ Finset.range 2, f i = 1 := by
      simp [f, Finset.sum_range_succ, LSeries.term]
    rw [hsum] at h
    linear_combination h
  rw [← he]
  have ht : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ] using h

  calc
    ‖∑' n, f (n + 2)‖ ≤ ∑' n, ‖f (n + 2)‖ := norm_tsum_le_tsum_norm ((hf.comp_injective (add_left_injective 2)).norm)
    _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 := by
      apply Summable.tsum_le_tsum _ ((hf.comp_injective (add_left_injective 2)).norm) ht.summable
      intro n
      change ‖LSeries.term (fun n => χ n) s (n + 2)‖ ≤ _
      simp only [LSeries.norm_term_eq, hs]
      rw [ite_eq_right (by omega), Real.rpow_two]
      exact div_le_div_of_nonneg_right (χ.norm_le_one _) (sq_nonneg _)
    _ = Real.pi ^ 2 / 6 - 1 := ht.tsum_eq
    _ ≤ 3 / 4 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]

/-- Page 159 Section 5. The logarithm is uniformly bounded on the anchor line of real part two. -/
theorem norm_lnL_anchor471 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s.re = 2) : ‖Complex.log (DirichletCharacter.LFunction χ s)‖ ≤ 2 := by
  have hd := norm_LFunction_sub_one471 q χ s hs
  have hb := Complex.norm_log_one_add_le (show ‖DirichletCharacter.LFunction χ s - 1‖ < 1 by linarith)
  have hi : (1 - ‖DirichletCharacter.LFunction χ s - 1‖)⁻¹ ≤ 4 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hh : ‖DirichletCharacter.LFunction χ s - 1‖ ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (DirichletCharacter.LFunction χ s - 1)]
  have hmul := mul_le_mul hh hi (inv_nonneg.mpr (by linarith : 0 ≤ 1 - ‖DirichletCharacter.LFunction χ s - 1‖)) (by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ 2)
  rw [show (1 : ℂ) + (DirichletCharacter.LFunction χ s - 1) = DirichletCharacter.LFunction χ s by ring] at hb
  calc
    ‖Complex.log (DirichletCharacter.LFunction χ s)‖ ≤
        ‖DirichletCharacter.LFunction χ s - 1‖ ^ 2 * (1 - ‖DirichletCharacter.LFunction χ s - 1‖)⁻¹ / 2 + ‖DirichletCharacter.LFunction χ s - 1‖ := by simpa using hb
    _ ≤ 2 := by nlinarith

/-- Standard bridge for page 159. A nonvanishing holomorphic function on a disk has a normalized holomorphic logarithm. -/
theorem log_ball471 {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hz : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧
      g c = Complex.log (f c) ∧ ∀ z ∈ ball c r, Complex.exp (g z) = f z := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hd := (hf.deriv isOpen_ball).div hf hz
  obtain ⟨G, hGc, hG⟩ := hd.isExactOn_ball.with_val_at c 0
  let H : ℂ → ℂ := fun z => Complex.exp (-G z) * f z
  have hH (z : ℂ) (hzb : z ∈ ball c r) : HasDerivAt H 0 z := by
    have hfd : HasDerivAt f (deriv f z) z :=
      ((hf z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)).hasDerivAt
    convert ((hG z hzb).neg.cexp).mul hfd using 1
    dsimp
    field_simp [hz z hzb]
    ring
  have hHd : DifferentiableOn ℂ H (ball c r) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hconst (z : ℂ) (hzb : z ∈ ball c r) : H z = f c := by
    have heq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hHd (fun z hz => (hH z hz).deriv) hzb hc
    simpa [H, hGc] using heq
  refine ⟨fun z => G z + Complex.log (f c), ?_, by simp [hGc], ?_⟩
  · have hgD : DifferentiableOn ℂ G (ball c r) :=
      fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
    exact hgD.add_const _
  · intro z hzb
    rw [Complex.exp_add, Complex.exp_log (hz c hc)]
    have hh := hconst z hzb
    dsimp [H] at hh
    rw [← hh, ← mul_assoc, ← Complex.exp_add]
    simp

/-- Standard bridge for page 159. Borel Caratheodory turns a modulus upper bound into a principal logarithm norm bound. -/
theorem norm_lnL_disk471 {f : ℂ → ℂ} {R M A : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hupper : ∀ z ∈ ball 0 R, Real.log ‖f z‖ ≤ M)
    (hanchor : ‖Complex.log (f 0)‖ ≤ A) (z : ℂ) (hz : z ∈ ball 0 R) :
    ‖Complex.log (f z)‖ ≤
      2 * M * ‖z‖ / (R - ‖z‖) + A * (R + ‖z‖) / (R - ‖z‖) + Real.pi := by
  obtain ⟨g, hgd, hg0, hg⟩ := log_ball471 hR hf hn
  have hre (w : ℂ) (hw : w ∈ ball 0 R) : (g w).re = Real.log ‖f w‖ := by
    rw [← hg w hw, Complex.norm_exp, Real.log_exp]
  have hbound := Complex.borelCaratheodory hM hgd
    (fun w hw => by simpa [hre w hw] using hupper w hw) hR hz
  have hgap : 0 < R - ‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hz)
  have hrat : 0 ≤ (R + ‖z‖) / (R - ‖z‖) := by positivity
  calc
    ‖Complex.log (f z)‖ ≤ |Real.log ‖f z‖| + Real.pi := by
      calc
        _ ≤ |(Complex.log (f z)).re| + |(Complex.log (f z)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ _ := by simpa [Complex.log_re, Complex.log_im] using
          add_le_add_left (Complex.abs_arg_le_pi (f z)) |Real.log ‖f z‖|
    _ = |(g z).re| + Real.pi := by rw [hre z hz]
    _ ≤ ‖g z‖ + Real.pi := by linarith [Complex.abs_re_le_norm (g z)]
    _ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) + Real.pi :=
      by linarith [hbound]
    _ ≤ _ := by
      gcongr
      simpa [hg0] using hanchor

/-- Page 159 Section 5. A polynomial strip upper bound gives the cubic principal logarithm bound. -/
theorem lnL_pointwise_of_strip_upper471
    (hG : LeanLab.DERZ1997.GRH) (A : ℝ) (hA : 0 < A)
    (hstrip : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
        Real.log ‖DirichletCharacter.LFunction χ s‖ ≤ A * Real.log ((q : ℝ) * (|s.im| + 3)))
    (N : ℕ) (hN : 1 < N) (hlog : 2 ≤ Real.log N)
    (q : ℕ) [NeZero q] (hq : 1 ≤ q) (hqN : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ))
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
      (12 * A + 18 + Real.pi) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  let δ : ℝ := 1 / Real.log N
  let R : ℝ := 3 / 2 - δ / 2
  let c : ℂ := 2 + (t : ℂ) * Complex.I
  let f : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (c + w)
  let X : ℝ := (N : ℝ) * (|t| + 2)
  let L : ℝ := Real.log X
  let M : ℝ := 2 * A * L + 1
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlogpos : 0 < Real.log N := by linarith
  have hδ : 0 < δ := one_div_pos.mpr hlogpos
  have hδ2 : δ ≤ 1 / 2 := (div_le_iff₀ hlogpos).mpr (by linarith)
  have hR : 0 < R := by dsimp [R]; linarith
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hX : 3 ≤ X := by dsimp [X]; nlinarith [abs_nonneg t]
  have hNX : (N : ℝ) ≤ X := by dsimp [X]; nlinarith [abs_nonneg t]
  have hlogNL : Real.log N ≤ L := Real.log_le_log hNp hNX
  have hL : 2 ≤ L := le_trans hlog hlogNL
  have hM : 0 < M := by dsimp [M]; positivity
  have hqNr : (q : ℝ) ≤ N := hqN.trans (Real.rpow_le_self_of_one_le hNr.le (by norm_num))
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hfd : DifferentiableOn ℂ f (ball 0 R) :=
    ((DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)).differentiableOn
  have hre (w : ℂ) : (c + w).re = 2 + w.re := by simp [c]
  have him (w : ℂ) : (c + w).im = t + w.im := by simp [c]
  have hfnz (w : ℂ) (hw : w ∈ ball 0 R) : f w ≠ 0 := by
    apply LFunction_ne_zero_right471 hG q χ hχ
    have hn := mem_ball_zero_iff.mp hw
    have hr := (abs_le.mp (Complex.abs_re_le_norm w)).1
    rw [hre]
    dsimp [R] at hn
    linarith
  have hupper (w : ℂ) (hw : w ∈ ball 0 R) : Real.log ‖f w‖ ≤ M := by
    have hn := mem_ball_zero_iff.mp hw
    have hsmall : ‖w‖ < 3 / 2 := by dsimp [R] at hn; linarith
    have hlow : 1 / 2 ≤ (c + w).re := by
      rw [hre]; linarith [(abs_le.mp (Complex.abs_re_le_norm w)).1]
    have hhigh : (c + w).re ≤ 4 := by
      rw [hre]; linarith [Complex.re_le_norm w]
    have hb := hstrip q χ hχ (c + w) hlow hhigh
    have himbound : |(c + w).im| ≤ |t| + 2 := by
      rw [him]
      have ha := abs_add_le t w.im
      have hi := Complex.abs_im_le_norm w
      linarith
    have hbase : 0 < (q : ℝ) * (|(c + w).im| + 3) := by positivity
    have hbaseX : (q : ℝ) * (|(c + w).im| + 3) ≤ X ^ 2 := by
      have hh : (q : ℝ) * (|(c + w).im| + 3) ≤ (N : ℝ) * (|t| + 5) := by
        exact mul_le_mul hqNr (by linarith) (by positivity) hNp.le
      have hh2 : (N : ℝ) * (|t| + 5) ≤ 3 * X := by dsimp [X]; nlinarith [abs_nonneg t]
      nlinarith
    have hblog : Real.log ((q : ℝ) * (|(c + w).im| + 3)) ≤ 2 * L := by
      have hb' := Real.log_le_log hbase hbaseX
      simpa [Real.log_pow, L] using hb'
    change Real.log ‖DirichletCharacter.LFunction χ (c + w)‖ ≤ _
    calc
      _ ≤ A * Real.log ((q : ℝ) * (|(c + w).im| + 3)) := hb
      _ ≤ A * (2 * L) := mul_le_mul_of_nonneg_left hblog hA.le
      _ ≤ M := by dsimp [M]; linarith only []
  have hanchor : ‖Complex.log (f 0)‖ ≤ 2 := by
    change ‖Complex.log (DirichletCharacter.LFunction χ (c + 0))‖ ≤ 2
    exact norm_lnL_anchor471 q χ (c + 0) (by simp [c])
  let w : ℂ := ((δ - 3 / 2 : ℝ) : ℂ)
  have hwnorm : ‖w‖ = 3 / 2 - δ := by
    rw [show w = ((δ - 3 / 2 : ℝ) : ℂ) by rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hw : w ∈ ball 0 R := by rw [mem_ball_zero_iff, hwnorm]; dsimp [R]; linarith
  have hfw : f w = DirichletCharacter.LFunction χ (mellinLine1622 N t) := by
    change DirichletCharacter.LFunction χ (c + w) = _
    apply congrArg (DirichletCharacter.LFunction χ)
    dsimp [c, w, mellinLine1622, δ]
    push_cast
    ring
  have hb := norm_lnL_disk471 hR hM hfd hfnz hupper hanchor w hw
  rw [hfw, hwnorm] at hb
  have hden : R - (3 / 2 - δ) = δ / 2 := by dsimp [R]; ring
  rw [hden] at hb
  have hfirst : 2 * M * (3 / 2 - δ) / (δ / 2) ≤ 6 * M / δ := by
    apply (div_le_div_iff₀ (by positivity : 0 < δ / 2) hδ).mpr
    nlinarith only [mul_nonneg (sq_nonneg δ) hM.le]
  have hsecond : 2 * (R + (3 / 2 - δ)) / (δ / 2) ≤ 12 / δ := by
    apply (div_le_div_iff₀ (by positivity : 0 < δ / 2) hδ).mpr
    dsimp [R]
    nlinarith
  have hdiv : 6 * M / δ + 12 / δ = (12 * A * L + 18) * Real.log N := by
    dsimp [δ, M]
    field_simp
    ring
  have hsum : ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
      (12 * A * L + 18) * Real.log N + Real.pi := by
    rw [← hdiv]
    linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL3 : L ^ 2 ≤ L ^ 3 := by nlinarith [mul_nonneg (show 0 ≤ L - 1 by linarith) (sq_nonneg L)]
  have hcoef : 0 ≤ 12 * A + 18 + Real.pi := by positivity
  have hmult := mul_le_mul_of_nonneg_left hlogNL (show 0 ≤ 12 * A * L + 18 by positivity)
  have hpi := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 2 by nlinarith) Real.pi_pos.le
  have hcube := mul_le_mul_of_nonneg_left hL3 hcoef
  change _ ≤ (12 * A + 18 + Real.pi) * L ^ 3
  nlinarith

/-- Page 159 Section 5. The strip upper bound suffices uniformly for every height. -/
theorem lnL_growth_of_strip_upper471 (hG : LeanLab.DERZ1997.GRH)
    (hstrip : ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
        Real.log ‖DirichletCharacter.LFunction χ s‖ ≤ A * Real.log ((q : ℝ) * (|s.im| + 3))) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ,
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  obtain ⟨A, hA, hstrip⟩ := hstrip
  refine ⟨12 * A + 18 + Real.pi, by positivity, max 1 ⌈Real.exp 2⌉₊, ?_⟩
  intro N hN q hqi hq hqN χ hχ t
  have hn : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hexp : Real.exp 2 ≤ (N : ℝ) := by
    have hc : ⌈Real.exp 2⌉₊ ≤ N := le_trans (le_max_right _ _) hN.le
    exact (Nat.le_ceil _).trans (by exact_mod_cast hc)
  have hl : 2 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 2) hexp
    simpa using h
  exact lnL_pointwise_of_strip_upper471 hG A hA hstrip N hn hl q hq hqN χ hχ t

/-- Standard bridge for page 159. Every nonprincipal partial character sum has norm at most the modulus. -/
theorem character_partial_sum_bound471 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ (k : ZMod q)‖ ≤ (q : ℝ) := by
  classical
  let S : ℕ → ℂ := fun m => ∑ k ∈ range m, χ ((k + 1 : ℕ) : ZMod q)
  have hb (m : ℕ) : (∑ k ∈ range q, χ ((m + k + 1 : ℕ) : ZMod q)) = 0 := by
    have he := LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range
      (q := q) (fun a : ZMod q => χ (a + (m + 1 : ℕ)))
    have hs := Fintype.sum_equiv (Equiv.addRight ((m + 1 : ℕ) : ZMod q))
      (fun a : ZMod q => χ (a + ((m + 1 : ℕ) : ZMod q))) χ (fun a => rfl)
    rw [hs, MulChar.sum_eq_zero_of_ne_one hχ] at he
    simpa [add_assoc, add_left_comm, add_comm] using he.symm
  have hp : Function.Periodic S q := by
    intro m
    dsimp [S]
    rw [Finset.sum_range_add, hb, add_zero]
  have he (m : ℕ) : (∑ k ∈ Icc 1 m, χ (k : ZMod q)) = S m := by
    induction m with
    | zero => simp [S]
    | succ m hm =>
      rw [Finset.sum_Icc_succ_top (by omega), hm]
      simp [S, Finset.sum_range_succ]
  rw [he, ← hp.map_mod_nat]
  calc
    ‖S (n % q)‖ ≤ ∑ k ∈ range (n % q), ‖χ ((k + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (n % q), (1 : ℝ) := sum_le_sum (fun k hk => χ.norm_le_one _)
    _ ≤ (q : ℝ) := by simp; exact_mod_cast (Nat.mod_lt n (NeZero.pos q)).le

/-- Standard bridge for page 159. The Mellin integral of a bounded measurable function is holomorphic in the positive half plane. -/
theorem bounded_mellin_differentiable471 (P : ℝ → ℂ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hP : AEStronglyMeasurable P (volume.restrict (Set.Ioi 1)))
    (hbound : ∀ x : ℝ, 1 < x → ‖P x‖ ≤ Q) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x in Set.Ioi (1 : ℝ), P x * (x : ℂ) ^ (-(s + 1)))
      {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : 0 < s.re := hs
  let ε : ℝ := s.re / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let F : ℂ → ℝ → ℂ := fun z x => P x * (x : ℂ) ^ (-(z + 1))
  let D : ℂ → ℝ → ℂ := fun z x => -(Real.log x : ℂ) * F z x
  let B : ℝ → ℝ := fun x => (Q / ε) * x ^ (-ε - 1)
  have hc (z : ℂ) : AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi 1)) := by
    exact hP.mul ((ContinuousOn.aestronglyMeasurable (s := Set.Ioi (1 : ℝ))
      (fun x hx => (Complex.continuousAt_ofReal_cpow_const x (-(z + 1))
        (Or.inr (show x ≠ 0 by have : 1 < x := hx; linarith))).continuousWithinAt)
        measurableSet_Ioi))
  have hdmeas : AEStronglyMeasurable (D s) (volume.restrict (Set.Ioi 1)) := by
    exact ((Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable.neg).mul (hc s)
  have hn (z : ℂ) (x : ℝ) (hx : 1 < x) : ‖F z x‖ = ‖P x‖ * x ^ (-z.re - 1) := by
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    congr 1
    simp
    ring
  have hFi : Integrable (F s) (volume.restrict (Set.Ioi 1)) := by
    apply (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one).const_mul Q |>.mono' (hc s)
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun x hx => by
      have hx1 : 1 < x := hx
      rw [hn s x hx1]
      exact mul_le_mul_of_nonneg_right (hbound x hx1) (Real.rpow_nonneg (by linarith) _)
  have hBi : Integrable B (volume.restrict (Set.Ioi 1)) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : -ε - 1 < -1) zero_lt_one).const_mul _
  have hDn : ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioi 1), ∀ z ∈ ball s (s.re / 2), ‖D z x‖ ≤ B x := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun x hx z hz => by
      have hx1 : 1 < x := hx
      have hzdist : ‖z - s‖ < s.re / 2 := by simpa [dist_eq_norm] using hz
      have hzr : s.re / 2 ≤ z.re := by
        have hr := (abs_le.mp (Complex.abs_re_le_norm (z - s))).1
        simp only [sub_re] at hr
        linarith
      have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      have hlog := Real.log_le_rpow_div (by linarith : 0 ≤ x) hε
      have hpow := Real.rpow_le_rpow_of_exponent_le hx1.le (show -z.re - 1 ≤ -(s.re / 2) - 1 by linarith)
      have hQpow : ‖F z x‖ ≤ Q * x ^ (-(s.re / 2) - 1) := by
        rw [hn z x hx1]
        exact mul_le_mul (hbound x hx1) hpow (by positivity) hQ
      dsimp [D, B]
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
      calc
        Real.log x * ‖F z x‖ ≤ (x ^ ε / ε) * (Q * x ^ (-(s.re / 2) - 1)) :=
          mul_le_mul hlog hQpow (norm_nonneg _) (by positivity)
        _ = (Q / ε) * (x ^ ε * x ^ (-(s.re / 2) - 1)) := by ring
        _ = (Q / ε) * x ^ (ε + (-(s.re / 2) - 1)) := by
          rw [← Real.rpow_add (by linarith : 0 < x)]
        _ = (Q / ε) * x ^ (-ε - 1) := by
          congr 2
          dsimp [ε]
          ring

  have hder : ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioi 1), ∀ z ∈ ball s (s.re / 2),
      HasDerivAt (fun z => F z x) (D z x) z := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun x hx z hz => by
      have hx1 : 1 < x := hx
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
      simp only [F, D, Complex.cpow_def_of_ne_zero hx0]
      convert (((hasDerivAt_id z).add_const 1).neg.const_mul (Complex.log x)).cexp.const_mul (P x) using 1
      · funext y
        dsimp
      · dsimp
        rw [← Complex.ofReal_log (by linarith : 0 ≤ x)]
        ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds s (by positivity : 0 < s.re / 2))
    (Filter.Eventually.of_forall hc) hFi hdmeas hDn hBi hder).2.differentiableAt.differentiableWithinAt

/-- Standard bridge for page 159. Abel summation represents the continued nonprincipal L function on the positive half plane. -/
theorem LFunction_eq_partial_integral471 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ x in Set.Ioi (1 : ℝ),
      (∑ k ∈ Icc 1 ⌊x⌋₊, χ (k : ZMod q)) * (x : ℂ) ^ (-(s + 1)) := by
  let P : ℝ → ℂ := fun x => ∑ k ∈ Icc 1 ⌊x⌋₊, χ (k : ZMod q)
  let G : ℂ → ℂ := fun z => z * ∫ x in Set.Ioi (1 : ℝ), P x * (x : ℂ) ^ (-(z + 1))
  let U : Set ℂ := {z | 0 < z.re}
  have hP : AEStronglyMeasurable P (volume.restrict (Set.Ioi 1)) :=
    ((measurable_of_countable (fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))).comp Nat.measurable_floor).aestronglyMeasurable
  have hPd : DifferentiableOn ℂ G U := by
    exact differentiableOn_id.mul (bounded_mellin_differentiable471 P q (by positivity)
      hP (fun x hx => character_partial_sum_bound471 q χ hχ _))
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hLa := (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have hGa := hPd.analyticOnNhd hU
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q)) =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    apply Asymptotics.IsBigO.of_bound (q : ℝ)
    exact Filter.Eventually.of_forall fun n => by simpa using character_partial_sum_bound471 q χ hχ n
  have he : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] G := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    rw [χ.LFunction_eq_LSeries hz]
    exact LSeries_eq_mul_integral (fun n => χ n) (r := 0) le_rfl (by linarith)
      (χ.LSeriesSummable_of_one_lt_re hz) hO
  exact hLa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt 0).isPreconnected (by change 0 < (2 : ℂ).re; norm_num) he hs

/-- Standard bridge for page 159. Bounded partial sums give the integral bound q times norm s over real part s. -/
theorem norm_LFunction_of_partial_integral471 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 < s.re)
    (hpartial : ∀ n : ℕ, ‖∑ k ∈ Icc 1 n, χ (k : ZMod q)‖ ≤ (q : ℝ))
    (hid : DirichletCharacter.LFunction χ s = s * ∫ x in Set.Ioi (1 : ℝ),
      (∑ k ∈ Icc 1 ⌊x⌋₊, χ (k : ZMod q)) * (x : ℂ) ^ (-(s + 1))) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * (q : ℝ) / s.re := by
  have ha : -(s.re + 1) < -1 := by linarith
  have hint : IntegrableOn (fun x : ℝ => (q : ℝ) * x ^ (-(s.re + 1))) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul _
  have hb : ‖∫ x in Set.Ioi (1 : ℝ),
      (∑ k ∈ Icc 1 ⌊x⌋₊, χ (k : ZMod q)) * (x : ℂ) ^ (-(s + 1))‖ ≤
      ∫ x in Set.Ioi (1 : ℝ), (q : ℝ) * x ^ (-(s.re + 1)) := by
    apply norm_integral_le_of_norm_le hint
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun x hx => by
      have hx1 : 1 < x := hx
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x)]
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_right (hpartial _) (Real.rpow_nonneg (by linarith) _)
  have hi : (∫ x in Set.Ioi (1 : ℝ), (q : ℝ) * x ^ (-(s.re + 1))) = (q : ℝ) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha zero_lt_one]
    simp
    ring
  rw [hi] at hb
  rw [hid, norm_mul]
  have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg s)
  simpa [mul_div_assoc] using hh

/-- Standard bridge for page 159. The integral norm estimate gives twice the logarithm of q times absolute height plus three on the fixed strip. -/
theorem log_LFunction_upper_of_norm471 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs0 : 1 / 2 ≤ s.re) (hs4 : s.re ≤ 4)
    (hb : ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * (q : ℝ) / s.re) :
    Real.log ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * Real.log ((q : ℝ) * (|s.im| + 3)) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqn : (0 : ℝ) ≤ q := by positivity
  have hspos : 0 < s.re := by linarith
  have hsn : ‖s‖ ≤ 4 + |s.im| := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hn
    linarith
  have hdiv : ‖s‖ * (q : ℝ) / s.re ≤ 2 * (‖s‖ * (q : ℝ)) := by
    have hd := div_le_div_of_nonneg_left (show 0 ≤ ‖s‖ * (q : ℝ) by positivity)
      (by norm_num : (0 : ℝ) < 1 / 2) hs0
    norm_num at hd
    simpa [mul_comm] using hd
  have hpoly : 2 * (4 + |s.im|) ≤ (|s.im| + 3) ^ 2 := by nlinarith [abs_nonneg s.im]
  have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hpow : ‖DirichletCharacter.LFunction χ s‖ ≤ ((q : ℝ) * (|s.im| + 3)) ^ 2 := by
    calc
      _ ≤ 2 * (‖s‖ * (q : ℝ)) := hb.trans hdiv
      _ ≤ (q : ℝ) * (2 * (4 + |s.im|)) := by nlinarith [mul_le_mul_of_nonneg_right hsn hqn]
      _ ≤ (q : ℝ) * (|s.im| + 3) ^ 2 := mul_le_mul_of_nonneg_left hpoly hqn
      _ ≤ (q : ℝ) ^ 2 * (|s.im| + 3) ^ 2 := mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
      _ = _ := by ring
  have hbase : 1 ≤ (q : ℝ) * (|s.im| + 3) := by nlinarith [abs_nonneg s.im]
  by_cases hz : DirichletCharacter.LFunction χ s = 0
  · simp only [hz, norm_zero, Real.log_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg hbase)
  · have hl := Real.log_le_log (norm_pos_iff.mpr hz) hpow
    simpa [Real.log_pow] using hl

/-- Standard bridge for page 159. The fixed strip has a uniform one sided upper estimate without GRH. -/
theorem LFunction_strip_log_upper471 :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
        Real.log ‖DirichletCharacter.LFunction χ s‖ ≤ A * Real.log ((q : ℝ) * (|s.im| + 3)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro q hq χ hχ s hs0 hs4
  apply log_LFunction_upper_of_norm471 q χ s hs0 hs4
  exact norm_LFunction_of_partial_integral471 q χ s (by linarith)
    (character_partial_sum_bound471 q χ hχ)
    (LFunction_eq_partial_integral471 q χ hχ s (by linarith))

/-- Branch audit for page 159. Even the nonvanishing entire exponential has a discontinuous principal logarithm along an imaginary line. -/
theorem principal_log_exp_discontinuous471 : ¬ ContinuousAt (fun t : ℝ => Complex.log (Complex.exp ((t : ℂ) * Complex.I))) Real.pi := by
  intro h
  have heq : (fun t : ℝ => Complex.log (Complex.exp ((t : ℂ) * Complex.I))) =ᶠ[𝓝[>] Real.pi]
      (fun t : ℝ => ((t - 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
    have hl : ∀ᶠ t : ℝ in 𝓝[>] Real.pi, Real.pi < t := self_mem_nhdsWithin
    have hu : ∀ᶠ t : ℝ in 𝓝[>] Real.pi, t < 2 * Real.pi :=
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by linarith [Real.pi_pos]))
    filter_upwards [hl, hu] with t ht ht'
    have he : Complex.exp ((t : ℂ) * Complex.I) =
        Complex.exp (((t - 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨1, ?_⟩
      push_cast
      ring
    rw [he]
    apply Complex.log_exp <;> simp only [Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    · linarith
    · linarith
  have ht : Tendsto (fun t : ℝ => ((t - 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      (𝓝[>] Real.pi) (𝓝 (((-Real.pi : ℝ) : ℂ) * Complex.I)) := by
    have hc : Continuous (fun t : ℝ => ((t - 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by fun_prop
    convert hc.continuousAt.continuousWithinAt.tendsto (x := Real.pi) (s := Set.Ioi Real.pi) using 1 <;> congr 1 <;> push_cast <;> ring
  have hx := tendsto_nhds_unique h.continuousWithinAt.tendsto (ht.congr' heq.symm)
  have hlog : Complex.log (Complex.exp ((Real.pi : ℂ) * Complex.I)) = (Real.pi : ℂ) * Complex.I := by
    apply Complex.log_exp <;> simp <;> linarith [Real.pi_pos]
  rw [hlog] at hx
  have hi := congrArg Complex.im hx
  simp at hi
  linarith [Real.pi_pos]

/-- Standard bridge for page 159. A nonvanishing continuously differentiable real path has a normalized continuous logarithm. -/
theorem exists_continuous_log_path471 (f f' : ℝ → ℂ)
    (hfd : ∀ t : ℝ, HasDerivAt f (f' t) t) (hfc : Continuous f')
    (hz : ∀ t : ℝ, f t ≠ 0) :
    ∃ M : ℝ → ℂ, Continuous M ∧ M 0 = Complex.log (f 0) ∧
      ∀ t : ℝ, Complex.exp (M t) = f t := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hfd t).continuousAt)
  let r : ℝ → ℂ := fun t => f' t / f t
  have hr : Continuous r := hfc.div hf hz
  let M : ℝ → ℂ := fun t => Complex.log (f 0) + ∫ u in (0 : ℝ)..t, r u
  have hMd (t : ℝ) : HasDerivAt M (r t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
      hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt).const_add _
  let H : ℝ → ℂ := fun t => Complex.exp (-M t) * f t
  have hHd (t : ℝ) : HasDerivAt H 0 t := by
    convert ((hMd t).neg.cexp).mul (hfd t) using 1
    dsimp [r]
    field_simp [hz t]
    ring
  have hconst (t : ℝ) : H t = H 0 :=
    is_const_of_deriv_eq_zero (fun t => (hHd t).differentiableAt) (fun t => (hHd t).deriv) t 0
  have hM0 : M 0 = Complex.log (f 0) := by simp [M]
  refine ⟨M, (show Differentiable ℝ M from fun t => (hMd t).differentiableAt).continuous, hM0, ?_⟩
  intro t
  have hh := hconst t
  dsimp [H] at hh
  have h0 : Complex.exp (-M 0) * f 0 = 1 := by
    rw [hM0, Complex.exp_neg, Complex.exp_log (hz 0)]
    exact inv_mul_cancel₀ (hz 0)
  rw [h0] at hh
  have hm := congrArg (fun z : ℂ => Complex.exp (M t) * z) hh
  rw [← mul_assoc, ← Complex.exp_add] at hm
  simpa using hm.symm

/-- Page 159 Section 5. Nonvanishing supplies a continuous chosen logarithm on the Mellin line. -/
theorem exists_continuous_lnL_line471 (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hz : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0) :
    ∃ M : ℝ → ℂ, Continuous M ∧
      M 0 = Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N 0)) ∧
      ∀ t : ℝ, Complex.exp (M t) = DirichletCharacter.LFunction χ (mellinLine1622 N t) := by
  let f : ℝ → ℂ := fun t => DirichletCharacter.LFunction χ (mellinLine1622 N t)
  let f' : ℝ → ℂ := fun t => deriv (DirichletCharacter.LFunction χ) (mellinLine1622 N t) * Complex.I
  have hfc : Continuous f' :=
    ((DirichletCharacter.differentiable_LFunction hχ).deriv.continuous.comp
      (continuous_mellinLine471 N)).mul continuous_const
  have hfd (t : ℝ) : HasDerivAt f (f' t) t := by
    have hl : HasDerivAt (fun z : ℂ =>
        (((1 / 2 + 1 / Real.log N : ℝ)) : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
      convert ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add
        (((1 / 2 + 1 / Real.log N : ℝ)) : ℂ) using 1 <;> simp
    exact (χ.differentiableAt_LFunction (mellinLine1622 N t) (Or.inr hχ)).hasDerivAt.comp t hl.comp_ofReal
  exact exists_continuous_log_path471 f f' hfd hfc hz

/-- Standard bridge for page 159. The norm of the principal logarithm is continuous along every nonvanishing continuous path. -/
theorem continuous_norm_log471 {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (hf : Continuous f) (hz : ∀ x : X, f x ≠ 0) :
    Continuous fun x : X => ‖Complex.log (f x)‖ := by
  have hformula (z : ℂ) (hz : z ≠ 0) :
      ‖Complex.log z‖ = Real.sqrt ((Real.log ‖z‖) ^ 2 + (Real.arccos (z.re / ‖z‖)) ^ 2) := by
    have ha : |Complex.arg z| = Real.arccos (z.re / ‖z‖) := by
      have hc := Real.arccos_cos (abs_nonneg (Complex.arg z)) (Complex.abs_arg_le_pi z)
      rw [Real.cos_abs, Complex.cos_arg hz] at hc
      exact hc.symm
    rw [Complex.norm_def, Complex.normSq_apply, Complex.log_re, Complex.log_im, ← ha]
    congr 1
    nlinarith [sq_abs (Complex.arg z)]
  have hlog : Continuous fun x : X => Real.log ‖f x‖ :=
    hf.norm.log (fun x => norm_ne_zero_iff.mpr (hz x))
  have harg : Continuous fun x : X => Real.arccos ((f x).re / ‖f x‖) :=
    Real.continuous_arccos.comp ((Complex.continuous_re.comp hf).div hf.norm (fun x => norm_ne_zero_iff.mpr (hz x)))
  exact (((hlog.pow 2).add (harg.pow 2)).sqrt).congr (fun x => (hformula (f x) (hz x)).symm)

/-- Page 156 Lemma 2 and page 159 Section 5. The principal logarithm along a nonvanishing line is integrable on every compact height interval. -/
theorem intervalIntegrable_lnL_line471 (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hz : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0)
    (a b : ℝ) : IntervalIntegrable (fun t : ℝ =>
      Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))) volume a b := by
  have hf := continuous_LFunction_line471 N q χ hχ
  have hm : AEStronglyMeasurable (fun t : ℝ => Complex.log
      (DirichletCharacter.LFunction χ (mellinLine1622 N t))) (volume.restrict (Set.uIoc a b)) :=
    (Complex.measurable_log.comp hf.measurable).aestronglyMeasurable
  exact (IntervalIntegrable.intervalIntegrable_norm_iff hm).mp ((continuous_norm_log471 _ hf hz).intervalIntegrable a b)


/-- Derived explicit version of page 159 Section 5. Under GRH the coefficient forty two plus pi works for every natural N greater than eight. -/
theorem lnL_explicit_size471 (hG : LeanLab.DERZ1997.GRH)
    (N : ℕ) (hN : 8 < N) (q : ℕ) [NeZero q] (hq : 1 ≤ q)
    (hqN : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ))
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
      (42 + Real.pi) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  have hn : (9 : ℝ) ≤ N := by exact_mod_cast (by omega : 9 ≤ N)
  have he : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hl : 2 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 2) (le_trans he.le hn)
    simpa using hh
  have hstrip : ∀ (r : ℕ) [NeZero r] (ψ : DirichletCharacter ℂ r), ψ ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
        Real.log ‖DirichletCharacter.LFunction ψ s‖ ≤ 2 * Real.log ((r : ℝ) * (|s.im| + 3)) := by
    intro r hr ψ hψ s hs0 hs4
    apply log_LFunction_upper_of_norm471 r ψ s hs0 hs4
    exact norm_LFunction_of_partial_integral471 r ψ s (by linarith)
      (character_partial_sum_bound471 r ψ hψ)
      (LFunction_eq_partial_integral471 r ψ hψ s (by linarith))
  convert lnL_pointwise_of_strip_upper471 hG 2 (by norm_num) hstrip
    N (by omega) hl q hq hqN χ hχ t using 1 <;> norm_num

end LeanLab.Linnik1951
