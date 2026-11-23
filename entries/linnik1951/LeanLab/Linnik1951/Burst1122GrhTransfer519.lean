module

public import LeanLab.Linnik1951.SPLIT_grh_mellin_transfer519
public import LeanLab.Linnik1951.LnLCrossing1117
public import LeanLab.Linnik1951.Burst1122LogBound
public import LeanLab.Linnik1951.Burst1122CahenMellin
public import LeanLab.Linnik1951.Burst1122LineShift

/-!
P0093 Linnik 1951, page 159 before equation 5.1, with page 155 and page 156 equation 4.1.
A second route to grh_mellin_transfer519 of Decomp519a. The coefficient M on the
vertical line is G composed with mellinLine519 N, where G is a holomorphic logarithm
of the L-function on the open half plane re s greater than 1/2, normalised by the
prime power series on re s greater than 1. The principal branch Complex.log is not
used: by LnLCrossing1117 it jumps where the L-function crosses the negative real axis.
Proved here: GRH nonvanishing on the half plane, the existence of the holomorphic
logarithm with its normalisation, the separation of the exponent one terms, and the
assembly. The three former leaves, the GRH bound for log L, the Cahen Mellin formula on
the line re s equal to 2 and the shift of that line, are proved in Burst1122LogBound,
Burst1122CahenMellin and Burst1122LineShift, burst session S57.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset Topology

/-! ### Step 1. Nonvanishing on the half plane under GRH -/

/-- P0093 page 159 before equation 5.1. Under GRH, the L-function of a nonprincipal
character has no zero with real part greater than 1/2: in the strip below 1 by GRH,
and on re s at least 1 by the nonvanishing theorem of Mathlib. -/
theorem lfunction_ne_zero_half_b1122 (hG : LeanLab.DERZ1997.GRH) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 / 2 < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h0
  rcases lt_or_ge s.re 1 with h1 | h1
  · have := hG q χ s h0 (by linarith) h1
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1 h0

/-! ### Step 2. The holomorphic logarithm of L on the half plane -/

/-- Two logarithms of the same function near a point. If d is continuous at s0 and
exp of d is eventually the constant exp of d s0, then d is eventually the constant d s0,
because two logarithms differ by an integer multiple of 2 pi i. -/
theorem eventually_eq_of_exp_eventually_eq_b1122 (d : ℂ → ℂ) (s0 : ℂ)
    (hd : ContinuousAt d s0) (he : ∀ᶠ s in 𝓝 s0, Complex.exp (d s) = Complex.exp (d s0)) :
    ∀ᶠ s in 𝓝 s0, d s = d s0 := by
  have hsmall : ∀ᶠ s in 𝓝 s0, ‖d s - d s0‖ < 2 * Real.pi := by
    have h : ContinuousAt (fun s => ‖d s - d s0‖) s0 := (hd.sub continuousAt_const).norm
    have h0 : ‖d s0 - d s0‖ < 2 * Real.pi := by
      rw [sub_self, norm_zero]; positivity
    exact h.eventually (Iio_mem_nhds h0)
  filter_upwards [hsmall, he] with s hs he'
  have h1 : Complex.exp (d s - d s0) = 1 := by
    rw [Complex.exp_sub, he', div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hn0 : n = 0 := by
    by_contra hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
    have hnorm : ‖d s - d s0‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hnorm] at hs
    nlinarith [Real.pi_pos]
  rw [hn0] at hn
  simpa [sub_eq_zero] using hn

/-- The open half plane re s greater than 1/2 is simply connected, being convex. -/
theorem halfplane_isSimplyConnected_b1122 (c : ℝ) :
    IsSimplyConnected {s : ℂ | c < s.re} := by
  have hne : ({s : ℂ | c < s.re}).Nonempty := ⟨(c + 1 : ℝ), by simp⟩
  have := (convex_halfSpace_re_gt (r := c)).contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

/-- A continuous logarithm of a holomorphic nonvanishing function on an open set is
holomorphic there: near each point it is a constant plus the principal logarithm of a
quotient close to one. -/
theorem differentiableOn_of_continuous_log_b1122 {U : Set ℂ} (hU : IsOpen U)
    {f G : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ s ∈ U, f s ≠ 0)
    (hGc : ContinuousOn G U) (hGe : ∀ s ∈ U, Complex.exp (G s) = f s) :
    DifferentiableOn ℂ G U := by
  intro s0 hs0
  have hfa : DifferentiableAt ℂ f s0 := hf.differentiableAt (hU.mem_nhds hs0)
  have hf00 := hf0 s0 hs0
  set h : ℂ → ℂ := fun s => G s0 + Complex.log (f s / f s0) with hh
  have hslit : f s0 / f s0 ∈ Complex.slitPlane := by
    rw [div_self hf00]; exact Complex.one_mem_slitPlane
  have hhd : DifferentiableAt ℂ h s0 :=
    (differentiableAt_const _).add ((hfa.div_const _).clog hslit)
  have hd : ContinuousAt (fun s => G s - h s) s0 :=
    (hGc.continuousAt (hU.mem_nhds hs0)).sub hhd.continuousAt
  have hev : ∀ᶠ s in 𝓝 s0, Complex.exp (G s - h s) = Complex.exp (G s0 - h s0) := by
    have hnz : ∀ᶠ s in 𝓝 s0, f s ≠ 0 :=
      hfa.continuousAt.eventually_ne hf00
    filter_upwards [hU.mem_nhds hs0, hnz] with s hs hfs
    have hq : f s / f s0 ≠ 0 := div_ne_zero hfs hf00
    simp only [hh, Complex.exp_sub, Complex.exp_add, Complex.exp_log hq,
      Complex.exp_log (div_ne_zero hf00 hf00), hGe s hs, hGe s0 hs0]
    field_simp
  have hloc := eventually_eq_of_exp_eventually_eq_b1122 _ s0 hd hev
  have hzero : G s0 - h s0 = 0 := by
    simp [hh, div_self hf00]
  have hEq : G =ᶠ[𝓝 s0] h := by
    filter_upwards [hloc] with s hs
    rw [hzero] at hs
    exact sub_eq_zero.mp hs
  exact (hhd.congr_of_eventuallyEq hEq).differentiableWithinAt

/-- P0093 page 159 before equation 5.1 and page 155. A holomorphic nonvanishing
function on an open simply connected set has a holomorphic logarithm there. -/
theorem exists_holomorphic_log_b1122 {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ s ∈ U, f s ≠ 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ ∀ s ∈ U, Complex.exp (G s) = f s := by
  obtain ⟨G, hGc, hGe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hf.continuousOn
    (by rintro ⟨s, hs, h0⟩; exact hf0 s hs h0)
  exact ⟨G, differentiableOn_of_continuous_log_b1122 hUo hf hf0 hGc (fun s hs => hGe hs),
    fun s hs => hGe hs⟩

/-- P0093 page 155. The Euler logarithm series: the sum over primes p and exponents
k at least 1 of chi of p to the k times p to the minus k s over k. -/
theorem euler_log_term_b1122 {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' k : ℕ, (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) =
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
  apply HasSum.tsum_eq
  apply Complex.hasSum_taylorSeries_neg_log'
  have hp : 0 < (p : ℕ) := p.2.pos
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  have hχ : ‖χ (p : ℕ)‖ ≤ 1 := χ.norm_le_one _
  have hlt : ((p : ℕ) : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hχ (by positivity)
    _ < 1 := by rw [one_mul]; exact hlt

/-- The norm of the Euler factor variable is at most p to the minus sigma. -/
theorem euler_var_norm_b1122 {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (p : Nat.Primes) :
    ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
    _ = _ := one_mul _

/-- P0093 page 155. The Euler logarithm sum over primes is continuous on re s
greater than 1, by local uniform convergence. -/
theorem continuousOn_euler_log_b1122 {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun s : ℂ => ∑' p : Nat.Primes,
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))) {s : ℂ | 1 < s.re} := by
  intro s0 hs0
  simp only [Set.mem_ofPred_eq] at hs0
  set σ : ℝ := (1 + s0.re) / 2 with hσ
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  have hW : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs0W : s0 ∈ {s : ℂ | σ < s.re} := by simp only [Set.mem_ofPred_eq, hσ]; linarith
  have hsum : Summable (fun p : Nat.Primes => (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)) := by
    apply Summable.mul_left
    have h := (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
    exact h.comp_injective Nat.Primes.coe_nat_injective
  have hcont : ContinuousOn (fun s : ℂ => ∑' p : Nat.Primes,
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))) {s : ℂ | σ < s.re} := by
    have hvar : ∀ p : Nat.Primes, ∀ s : ℂ, σ < s.re →
        ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-σ) := by
      intro p s hs
      have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
      exact (euler_var_norm_b1122 χ s p).trans
        (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
    have hhalf : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) ≤ 1 / 2 := by
      intro p
      have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
      calc ((p : ℕ) : ℝ) ^ (-σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = ((p : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
    refine continuousOn_tsum (fun p => ?_) hsum (fun p s hs => ?_)
    · have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      intro s hs
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.neg
      apply ContinuousAt.clog
      · exact continuousAt_const.sub (continuousAt_const.mul
          (continuousAt_neg.const_cpow (Or.inl hp0)))
      · rw [sub_eq_add_neg]
        apply Complex.mem_slitPlane_of_norm_lt_one
        rw [norm_neg]
        exact ((hvar p s hs).trans (hhalf p)).trans_lt (by norm_num)
    · have hw := hvar p s hs
      have hw2 : ‖-(χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hw.trans (hhalf p)
      have hl := Complex.norm_log_one_add_half_le_self hw2
      rw [← sub_eq_add_neg, norm_neg] at hl
      rw [norm_neg]
      exact hl.trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  exact (hcont.continuousAt (hW.mem_nhds hs0W)).continuousWithinAt


/-- Two continuous logarithms of the same function on an open preconnected set differ
by a constant: a continuous function with exp equal to one there is constant. -/
theorem const_of_exp_eq_one_b1122 {V : Set ℂ} (hVo : IsOpen V) (hVp : IsPreconnected V)
    {d : ℂ → ℂ} (hdc : ContinuousOn d V) (he : ∀ s ∈ V, Complex.exp (d s) = 1)
    {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V) : d x = d y := by
  set n : ℂ → ℤ := fun s => round ((d s / (2 * Real.pi * Complex.I)).re) with hn
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hrep : ∀ s ∈ V, d s = (n s : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (he s hs)
    have hq : d s / (2 * Real.pi * Complex.I) = (m : ℂ) := by
      rw [hm, mul_div_assoc, div_self h2pi, mul_one]
    have : n s = m := by
      simp only [hn, hq, Complex.intCast_re, round_intCast]
    rw [this, hm]
  have hnc : ContinuousOn n V := by
    intro s0 hs0
    apply ContinuousAt.continuousWithinAt
    have hev : ∀ᶠ s in 𝓝 s0, Complex.exp (d s) = Complex.exp (d s0) := by
      filter_upwards [hVo.mem_nhds hs0] with s hs
      rw [he s hs, he s0 hs0]
    have hloc := eventually_eq_of_exp_eventually_eq_b1122 d s0
      (hdc.continuousAt (hVo.mem_nhds hs0)) hev
    have hne : n =ᶠ[𝓝 s0] fun _ => n s0 := by
      filter_upwards [hloc] with s hs
      simp only [hn, hs]
    exact continuousAt_const.congr hne.symm
  rw [hrep x hx, hrep y hy, hVp.constant hnc hx hy]

/-- P0093 page 159 before equation 5.1 and page 155. Under GRH, for a nonprincipal
character there is a holomorphic logarithm G of the L-function on the open half plane
re s greater than 1/2 which on re s greater than 1 equals the prime power series, the
sum over primes p and k at least 1 of chi of p to the k times p to the minus k s over k. -/
theorem holomorphic_log_L_b1122 (hG : LeanLab.DERZ1997.GRH) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
        (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) := by
  have hHo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨G0, hG0d, hG0e⟩ := exists_holomorphic_log_b1122 (halfplane_isSimplyConnected_b1122 _)
    hHo (f := DirichletCharacter.LFunction χ)
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    (fun s hs => lfunction_ne_zero_half_b1122 hG q χ hχ s hs)
  set E : ℂ → ℂ := fun s => ∑' p : Nat.Primes,
    -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) with hE
  have hVo : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVp : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt (r := 1)).isPreconnected
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs; simp only [Set.mem_ofPred_eq] at hs ⊢; linarith
  have hEexp : ∀ s : ℂ, 1 < s.re → Complex.exp (E s) = DirichletCharacter.LFunction χ s := by
    intro s hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
      ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs]
  have hdc : ContinuousOn (fun s => G0 s - E s) {s : ℂ | 1 < s.re} :=
    (hG0d.continuousOn.mono hsub).sub (continuousOn_euler_log_b1122 χ)
  have hde : ∀ s ∈ {s : ℂ | 1 < s.re}, Complex.exp (G0 s - E s) = 1 := by
    intro s hs
    rw [Complex.exp_sub, hG0e s (hsub hs), hEexp s hs,
      div_self (lfunction_ne_zero_half_b1122 hG q χ hχ s (hsub hs))]
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  refine ⟨fun s => G0 s - (G0 2 - E 2), hG0d.sub_const _, fun s hs => ?_⟩
  have hc := const_of_exp_eq_one_b1122 hVo hVp hdc hde hs h2
  have : G0 s - (G0 2 - E 2) = E s := by
    have hc' : G0 s - E s = G0 2 - E 2 := hc
    rw [← hc']; ring
  show G0 s - (G0 2 - E 2) = _
  rw [this, hE]
  exact tsum_congr fun p => (euler_log_term_b1122 χ s hs p).symm

/-! ### Step 3. The cited GRH bound for the logarithm of L -/

/-- P0093 page 159 before equation 5.1, the ERH bound for ln L. Formerly a HARD LEAF,
PROVED in burst session S57 by grh_strip_log_bound_proof_b1122 of Burst1122LogBound via
Borel Caratheodory, with no zero sum. Former citation wall: the classical bound for log L under the generalized Riemann
hypothesis, Titchmarsh, The Theory of the Riemann Zeta-Function, section 14.2 and
Montgomery and Vaughan, Multiplicative Number Theory I, chapter 13. Under GRH, for
N large, q at most N to the 1/7, a nonprincipal character chi and the holomorphic
logarithm G of its L-function normalised by the prime power series on re s greater
than 1, the norm of G at every s with 1/2 + 1/ln N at most re s at most 2 is at most
B0 times the cube of ln of N times the absolute imaginary part plus 2. The constant
B0 does not depend on N, q or chi. -/
theorem grh_strip_log_bound_b1122 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ G : ℂ → ℂ,
          DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} →
          (∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
            (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) →
          ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
            ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 :=
  grh_strip_log_bound_proof_b1122 hG

/-! ### Step 4. Mellin inversion on re s equal to 2 and the shift of the line -/

/-- P0093 page 156 display after equation 4.1 and page 159 before equation 5.1,
the Cahen Mellin formula on the line re s equal to 2. Formerly a MEDIUM LEAF, PROVED in
burst session S57 by cahen_mellin_line_two_proof_b1122 of Burst1122CahenMellin.
For z equal to 1/N + 2 pi i alpha, e to the minus n z is 1/(2 pi i) times the integral
of Gamma of s times n z to the minus s over re s equal to 2. Inserting the prime power
series of G, absolutely convergent on that line, and integrating term by term gives
the damped prime power series with weight 1/k. No zero hypothesis is used. -/
theorem cahen_mellin_line_two_b1122 (N : ℕ) (hN : 1 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (G : ℂ → ℂ)
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) (α : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
          G ((2 : ℂ) + (t : ℂ) * Complex.I)
      = ∑' p : Nat.Primes, ∑' k : ℕ,
          (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
            (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
              Complex.exp
                ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I)) :=
  cahen_mellin_line_two_proof_b1122 N hN q χ G hGs α

/-- P0093 page 156 display after equation 4.1 and page 159 before equation 5.1,
the shift of the Mellin line from re s equal to 2 to re s equal to 1/2 + 1/ln N. Formerly a
MEDIUM LEAF, PROVED in burst session S57 by mellin_line_shift_proof_b1122 of Burst1122LineShift.
Cauchy's theorem on the rectangle with vertical sides on the two lines: G is
holomorphic on re s greater than 1/2, Gamma decays like e to the minus pi |t| / 2 while
z to the minus s grows at most like e to the |t| |arg z| with |arg z| less than pi / 2,
and G grows at most like a power of ln |t| in the strip, so the horizontal sides tend
to zero. No zero hypothesis is used beyond the holomorphy of G. -/
theorem mellin_line_shift_b1122 (N : ℕ) (hN : 2 ≤ N) (G : ℂ → ℂ)
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re}) (B0 : ℝ)
    (hGb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3) (α : ℝ) :
    mellinU519 N (fun t : ℝ => G (mellinLine519 N t)) α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
            G ((2 : ℂ) + (t : ℂ) * Complex.I) :=
  mellin_line_shift_proof_b1122 N hN G hGd B0 hGb α


/-! ### Separation of the exponent one terms -/

/-- For a prime p and k at least 0, p + k is at most p to the k + 1. -/
theorem prime_add_le_pow_b1122 (p : Nat.Primes) (k : ℕ) :
    (p : ℕ) + k ≤ (p : ℕ) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hpos : 1 ≤ (p : ℕ) ^ (k + 1) := Nat.one_le_pow _ _ p.2.pos
    rw [pow_succ]
    nlinarith

/-- The damping at a prime power is at most the damping at p times a geometric factor. -/
theorem damp_pow_le_b1122 (N : ℕ) (hN : 1 ≤ N) (p : Nat.Primes) (k : ℕ) :
    Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) ≤
      Real.exp (-((p : ℕ) : ℝ) / N) * Real.exp (-1 / (N : ℝ)) ^ k := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := prime_add_le_pow_b1122 p k
  have hR : ((p : ℕ) : ℝ) + k ≤ ((p : ℕ) : ℝ) ^ (k + 1) := by exact_mod_cast h
  have hdiv : (((p : ℕ) : ℝ) + k) / N ≤ ((p : ℕ) : ℝ) ^ (k + 1) / N :=
    div_le_div_of_nonneg_right hR hNp.le
  have heq : -((p : ℕ) : ℝ) / N + (k : ℝ) * (-1 / (N : ℝ)) = -((((p : ℕ) : ℝ) + k) / N) := by
    ring
  rw [heq]
  linarith

/-- P0093 page 159 before equation 5.1. Separating the exponent one terms of the
damped prime power series with weight 1/k leaves the damped character prime series
plus the prime power double sum with exponents at least two. -/
theorem exponent_one_split_b1122 (N : ℕ) (hN : 1 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (α : ℝ) :
    ∑' p : Nat.Primes, ∑' k : ℕ,
        (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
            Complex.exp
              ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I))
      = characterPrime519 χ N α + ∑' p : Nat.Primes, ∑' k : ℕ,
          (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
            (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
              Complex.exp
                ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) := by
  set f : Nat.Primes → ℕ → ℂ := fun p k =>
    ((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
      (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I)
    with hf
  set r : ℝ := Real.exp (-1 / (N : ℝ)) with hr
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; exact div_neg_of_neg_of_pos (by norm_num) hNp
  have hgeo : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hnorm : ∀ p k, ‖f p k‖ ≤ Real.exp (-((p : ℕ) : ℝ) / N) * r ^ k := by
    intro p k
    refine le_trans ?_ (damp_pow_le_b1122 N hN p k)
    simp only [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : ‖((k : ℂ) + 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos k
    have h2 : ‖χ ((p : ℕ) ^ (k + 1))‖ ≤ 1 := χ.norm_le_one _
    calc ‖((k : ℂ) + 1)⁻¹‖ * ‖χ ((p : ℕ) ^ (k + 1))‖ *
          Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ)))
        ≤ 1 * 1 * Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumk : ∀ p, Summable (f p) := fun p =>
    Summable.of_norm_bounded (hgeo.mul_left _) (hnorm p)
  have hdamp : Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
    (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
  have ha : Summable (fun p => f p 0) :=
    Summable.of_norm_bounded hdamp (fun p => by simpa using hnorm p 0)
  have hb : Summable (fun p => ∑' k : ℕ, f p (k + 1)) := by
    refine Summable.of_norm_bounded (hdamp.mul_right (∑' k : ℕ, r ^ (k + 1))) (fun p => ?_)
    have hs1 : Summable (fun k : ℕ => ‖f p (k + 1)‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hnorm p (k + 1))
        ((summable_nat_add_iff 1).mpr hgeo |>.mul_left _)
    calc ‖∑' k : ℕ, f p (k + 1)‖ ≤ ∑' k : ℕ, ‖f p (k + 1)‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' k : ℕ, Real.exp (-((p : ℕ) : ℝ) / N) * r ^ (k + 1) :=
          hs1.tsum_le_tsum (fun k => hnorm p (k + 1))
            ((summable_nat_add_iff 1).mpr hgeo |>.mul_left _)
      _ = _ := tsum_mul_left
  have hinner : ∀ p, ∑' k : ℕ, f p k = f p 0 + ∑' k : ℕ, f p (k + 1) := fun p =>
    (hsumk p).tsum_eq_zero_add
  rw [tsum_congr hinner, ha.tsum_add hb]
  congr 1
  · unfold characterPrime519
    refine tsum_congr fun p => ?_
    simp only [hf, Nat.cast_zero, zero_add, inv_one, one_mul, pow_one, neg_div]
  · refine tsum_congr fun p => tsum_congr fun k => ?_
    simp only [hf]
    push_cast
    ring_nf

/-! ### Assembly -/

/-- P0093 page 159 before equation 5.1, with page 156 equation 4.1. The statement of
grh_mellin_transfer519, with M equal to G composed with mellinLine519 N for the
holomorphic logarithm G of the L-function. CONDITIONAL ON grh_strip_log_bound_b1122,
cahen_mellin_line_two_b1122 and mellin_line_shift_b1122. -/
theorem grh_mellin_transfer519_b1122 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖characterPrime519 χ N α - mellinU519 N M α‖ ≤ B * Real.sqrt N := by
  obtain ⟨B0, hB0, N1, h3⟩ := grh_strip_log_bound_b1122 hG
  obtain ⟨B, hB, N2, htail⟩ := prime_power_tail519
  refine ⟨B0, hB0, B, hB, max N1 (max N2 2), ?_⟩
  intro N hN q hq hqt χ hχ
  have : NeZero q := ⟨by omega⟩
  obtain ⟨G, hGd, hGs⟩ := holomorphic_log_L_b1122 hG q χ hχ
  have hN2 : 2 ≤ N := by omega
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2R
  have hlogpos : 0 < Real.log N := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2
  have hbound := h3 N (by omega) q hq hqt χ hχ G hGd hGs
  have hre : ∀ t : ℝ, (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : ∀ t : ℝ, (mellinLine519 N t).im = t := by
    intro t
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hle2 : 1 / 2 + 1 / Real.log N ≤ 2 := by
    have h23 : (2 : ℝ) / 3 ≤ Real.log N := by
      have := Real.log_two_gt_d9; linarith
    have : 1 / Real.log N ≤ 3 / 2 := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith
  refine ⟨fun t => G (mellinLine519 N t), ⟨?_, fun t => ?_⟩, fun α => ?_⟩
  · apply hGd.continuousOn.comp_continuous
    · unfold mellinLine519; fun_prop
    · intro t
      show 1 / 2 < (mellinLine519 N t).re
      rw [hre]; linarith [one_div_pos.mpr hlogpos]
  · have := hbound (mellinLine519 N t) (hre t).ge (by rw [hre]; exact hle2)
    rwa [him] at this
  · rw [mellin_line_shift_b1122 N hN2 G hGd B0 hbound α,
      cahen_mellin_line_two_b1122 N (by omega) q χ G hGs α,
      exponent_one_split_b1122 N (by omega) χ α, sub_add_cancel_left, norm_neg]
    exact htail N (by omega) q hq χ α

/-! ### The principal branch fails at a crossing -/

/-- Support for the QUESTION on line_bound_lnL519 of SPLIT_grh_mellin_transfer519.
If the L-function of a character takes a negative real value at the height t0 of the
line 1/2 + 1/ln N + i t and has negative imaginary part at heights arbitrarily close
to t0, then the conclusion of line_bound_lnL519 fails for that N, q and chi, for every
constant B0, because its continuity conjunct fails. CONDITIONAL ON the sign pattern of
the L-values, which is a hypothesis. It reuses not_continuous_lnL_line_of_crossing1117;
mellinLine519 and mellinLine1622 are the same expression. -/
theorem not_line_bound_lnL519_of_crossing_b1122 (N : ℕ) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t0 : ℝ)
    (hre : (DirichletCharacter.LFunction χ (mellinLine519 N t0)).re < 0)
    (him : (DirichletCharacter.LFunction χ (mellinLine519 N t0)).im = 0)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t - t0| < ε ∧
      (DirichletCharacter.LFunction χ (mellinLine519 N t)).im < 0) (B0 : ℝ) :
    ¬ (Continuous (fun t : ℝ =>
          Complex.log (DirichletCharacter.LFunction χ (mellinLine519 N t))) ∧
        ∀ t : ℝ, ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine519 N t))‖ ≤
          B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hl : mellinLine519 = LeanLab.Linnik1951.mellinLine1622 := rfl
  rintro ⟨hc, -⟩
  rw [hl] at hre him hnear hc
  exact LeanLab.Linnik1951.not_continuous_lnL_line_of_crossing1117 N q χ t0 hre him hnear hc

end LeanLab.Linnik1951.Task519
