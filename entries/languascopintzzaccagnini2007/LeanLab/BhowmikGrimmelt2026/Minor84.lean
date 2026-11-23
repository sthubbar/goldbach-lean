module

public import LeanLab.BhowmikGrimmelt2026.Decomp84
public import LeanLab.PNTPort.Gallagher.Basic

/-!
The minor arc proof following Proposition 4.1, pages 16 and 17.
The sealed target is Lemma42 9. The printed logarithm issue stays recorded in STATEMENTS.md.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- The major arcs `𝔐(R)` of (4.3), p. 14, at length `N`: `|α − a/q| ≤ R/(qN)`, `q ≤ R`,
`(a,q) = 1`. Integers `a` of any size are allowed, so the set is 1-periodic. -/
def MajorArc (N R : ℝ) (α : ℝ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ R ∧ ∃ a : ℤ, Int.gcd a q = 1 ∧ |α - a / q| ≤ R / (q * N)

/-- `r_𝔪(N) = ∫_{𝔪(R)} S(α)² e(−Nα) dα`, (4.4), with `S` of length `X` as in the proof of
Lemma 4.2, p. 16. -/
noncomputable def rMinor (X : ℕ) (R : ℝ) (N : ℕ) : ℂ :=
  ∫ α in Set.Ico (0 : ℝ) 1,
    Set.indicator {α | ¬ MajorArc X R α} (fun α => Ssum X α ^ 2 * ee (-(N * α))) α

/-- Lemma 4.2, p. 16, as printed, with the log power as a parameter `k`; printed `k = 5`.
The hypothesis `R < N^{1/2−ε}` is read as `R < X^{1/2−ε}`. -/
def Lemma42 (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ R : ℝ, 1 ≤ R → R < (X : ℝ) ^ (1 / 2 - ε) →
    ∑ N ∈ Finset.Icc 1 X, ‖rMinor X R N‖ ^ 2 ≤
      C * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) * X * Real.log X ^ k


/-- Page 14 display 4.3. The major arcs form a measurable set. -/
theorem measurableSet_majorArc84 (X R : ℝ) :
    MeasurableSet {α : ℝ | MajorArc X R α} := by
  unfold MajorArc
  measurability

/-- Pages 16 and 17, proof of Lemma 4.2. Off the major arcs, a reduced approximation
has denominator larger than R and at most X divided by R. -/
theorem minor_dirichlet84 {X R α : ℝ} (hX : 0 < X) (hR : 0 < R) (hRX : R ≤ X)
    (hminor : ¬ MajorArc X R α) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Int.gcd a q = 1 ∧ R < (q : ℝ) ∧
      (q : ℝ) ≤ X / R ∧ |α - a / q| < 1 / (q : ℝ) ^ 2 := by
  let Q : ℝ := X / R
  have hQ : 1 ≤ Q := (le_div_iff₀ hR).mpr (by simpa using hRX)
  have hQ0 : 0 < Q := by linarith
  obtain ⟨r, happ, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α (Nat.floor_pos.mpr hQ)
  have hq : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  have hq1 : 1 ≤ r.den := by have := r.pos; omega
  have hqQ : (r.den : ℝ) ≤ Q :=
    (by exact_mod_cast hden : (r.den : ℝ) ≤ ⌊Q⌋₊).trans (Nat.floor_le hQ0.le)
  have hQfloor : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hcop : Int.gcd r.num r.den = 1 := by
    simpa [Int.gcd_def] using r.reduced.gcd_eq_one
  have happ' : |α - (r.num : ℝ) / r.den| ≤
      1 / (((⌊Q⌋₊ : ℝ) + 1) * r.den) := by simpa [Rat.cast_def] using happ
  have happQ : |α - (r.num : ℝ) / r.den| ≤ 1 / (Q * r.den) := by
    apply happ'.trans
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right hQfloor.le hq.le)
  have hRq : R < (r.den : ℝ) := by
    by_contra h
    apply hminor
    refine ⟨r.den, hq1, le_of_not_gt h, r.num, hcop, ?_⟩
    calc
      _ ≤ 1 / (Q * r.den) := happQ
      _ = R / ((r.den : ℝ) * X) := by dsimp [Q]; field_simp
  refine ⟨r.num, r.den, hq1, hcop, hRq, hqQ, ?_⟩
  apply happ'.trans_lt
  exact one_div_lt_one_div_of_lt (by positivity)
    (by nlinarith only [mul_lt_mul_of_pos_right (hqQ.trans_lt hQfloor) hq])

/-- Page 16, proof of Lemma 4.2. The pointwise minor arc estimate from Proposition 4.1. -/
theorem minor_pointwise84 {X : ℕ} {R α : ℝ} (hX : 2 ≤ X) (hR : 1 ≤ R)
    (hRX : R ≤ X) (hminor : ¬ MajorArc X R α) :
    ‖Ssum X α‖ ≤ 48600 * ((X : ℝ) / Real.sqrt R +
      (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hR0 : 0 < R := by linarith
  obtain ⟨a, q, hq, hcop, hRq, hqR, happ⟩ := minor_dirichlet84 hX0 hR0 hRX hminor
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
  have hsR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
  have hfirst : (X : ℝ) / Real.sqrt q ≤ (X : ℝ) / Real.sqrt R :=
    div_le_div_of_nonneg_left hX0.le hsR (Real.sqrt_le_sqrt hRq.le)
  have hlast : Real.sqrt ((X : ℝ) * q) ≤ (X : ℝ) / Real.sqrt R := by
    have hprod : (X : ℝ) * q ≤ ((X : ℝ) / Real.sqrt R) ^ 2 := by
      have hqr : (q : ℝ) * R ≤ X := (le_div_iff₀ hR0).mp hqR
      rw [div_pow, hsR2, le_div_iff₀ hR0]
      nlinarith only [mul_le_mul_of_nonneg_left hqr hX0.le]
    exact (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq (by positivity))
  have hexplicit : ‖Ssum X α‖ ≤ 24300 * ((X : ℝ) / Real.sqrt q +
      (X : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt ((X : ℝ) * q)) * Real.log X ^ 4 := by
    rcases le_total q X with hqX | hXq
    · exact vaughan_small_denominator84 hX hq hcop happ hqX
    · exact vaughan_large_denominator84 hX hXq α
  calc
    _ ≤ 24300 * ((X : ℝ) / Real.sqrt q + (X : ℝ) ^ (4 / 5 : ℝ) +
        Real.sqrt ((X : ℝ) * q)) * Real.log X ^ 4 := hexplicit
    _ ≤ 24300 * (2 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ))) *
        Real.log X ^ 4 := by
      gcongr
      have hpow : 0 ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by positivity
      linarith
    _ = _ := by ring

/-- Page 16, last display. The von Mangoldt second moment is at most six X log X. -/
theorem mangoldt_energy84 (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, vonMangoldt n ^ 2 ≤ 6 * X * Real.log X := by
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hsum : (∑ n ∈ Finset.Icc 1 X, vonMangoldt n) ≤ Chebyshev.psi X := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc (by omega) le_rfl) (fun n _ _ => vonMangoldt_nonneg)
  have hpsi : Chebyshev.psi X ≤ 6 * X := by
    have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg X)
    have h4 := LeanLab.PNTPort.Vinogradov.log4_bounds.2
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, Real.log X * vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnX := (Finset.mem_Icc.mp hn).2
      have hterm : vonMangoldt n ≤ Real.log X :=
        vonMangoldt_le_log.trans (Real.log_le_log
          (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnX))
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right hterm (vonMangoldt_nonneg (n := n))
    _ = Real.log X * ∑ n ∈ Finset.Icc 1 X, vonMangoldt n := by rw [Finset.mul_sum]
    _ ≤ Real.log X * (6 * X) := mul_le_mul_of_nonneg_left (hsum.trans hpsi) hlog
    _ = _ := by ring

/-- Page 16, Parseval step. The minor arc integral is a unit interval Fourier coefficient. -/
theorem rMinor_eq_fourierCoeff84 (X : ℕ) (R : ℝ) (N : ℕ) :
    rMinor X R N = fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (Set.indicator {α : ℝ | ¬ MajorArc X R α} (fun α => Ssum X α ^ 2)) (N : ℤ) := by
  unfold rMinor
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ico
  intro α hα
  by_cases hm : α ∈ {α : ℝ | ¬ MajorArc X R α}
  · simp only [Set.indicator_of_mem hm, smul_eq_mul]
    rw [mul_comm (Ssum X α ^ 2)]
    congr 1
    rw [fourier_coe_apply]
    unfold ee
    congr 1
    push_cast
    ring
  · simp only [Set.indicator_of_notMem hm, smul_zero]

/-- Page 16, Parseval step. The minor arc coefficients satisfy Bessel's inequality. -/
theorem minor_bessel84 (X : ℕ) (R : ℝ) :
    ∑ N ∈ Finset.Icc 1 X, ‖rMinor X R N‖ ^ 2 ≤
      ∫ α in (0 : ℝ)..1,
        ‖Set.indicator {α : ℝ | ¬ MajorArc X R α} (fun α => Ssum X α ^ 2) α‖ ^ 2 := by
  let f : ℝ → ℂ := Set.indicator {α : ℝ | ¬ MajorArc X R α} (fun α => Ssum X α ^ 2)
  have hcont : Continuous (Ssum X) := by unfold Ssum ee; fun_prop
  have hS : MemLp (fun α => Ssum X α ^ 2) 2 (volume.restrict (Set.Ioc 0 1)) := by
    apply MemLp.of_bound (hcont.pow 2).aestronglyMeasurable ((X * Real.log X) ^ 2)
    apply Filter.Eventually.of_forall
    intro α
    change ‖Ssum X α ^ 2‖ ≤ (X * Real.log X) ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ssum_log_bound84 X α) 2
  have hf : MemLp f 2 (volume.restrict (Set.Ioc 0 1)) :=
    hS.indicator (measurableSet_majorArc84 X R).compl
  have hsum := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hf
  simp only [sub_zero, inv_one, one_smul] at hsum
  let s : Finset ℤ := (Finset.Icc 1 X).image (fun n : ℕ => (n : ℤ))
  have hle := Summable.sum_le_tsum s (fun n hn => sq_nonneg
    (‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖)) hsum.summable
  rw [hsum.tsum_eq] at hle
  have himage : (∑ n ∈ s, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 X,
        ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f (n : ℤ)‖ ^ 2 := by
    dsimp [s]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Int.ofNat.inj hab
  rw [himage] at hle
  simpa only [rMinor_eq_fourierCoeff84, f] using hle

/-- Page 16, last display. Parseval for the local prime sum on the unit interval. -/
theorem ssum_parseval84 (X : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 X, vonMangoldt n ^ 2 := by
  have heq (α : ℝ) : Ssum X α = ∑ n ∈ Finset.range (X + 1),
      (vonMangoldt n : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * α) := by
    rw [ssum_eq_library84, Nat.range_succ_eq_Icc_zero]
    unfold LeanLab.PNTPort.Vinogradov.S
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
    intro n hn hn'
    have hn0 : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
    simp [hn0]
  have hperiodic : Function.Periodic (fun α => ‖Ssum X α‖ ^ 2) 1 := by
    intro α
    have hs : Ssum X (α + 1) = Ssum X α := by
      rw [heq, heq]
      apply Finset.sum_congr rfl
      intro n hn
      have hp : (n : ℝ) * (α + 1) = (n : ℝ) * α + (n : ℤ) := by push_cast; ring
      rw [hp, LeanLab.PNTPort.LargeSieve.e_add, LeanLab.PNTPort.LargeSieve.e_int, mul_one]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hs
  calc
    _ = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖Ssum X α‖ ^ 2 := by
      have h := hperiodic.intervalIntegral_add_eq 0 (-(1 / 2 : ℝ))
      norm_num at h ⊢
      exact h
    _ = ∑ n ∈ Finset.range (X + 1), ‖(vonMangoldt n : ℂ)‖ ^ 2 := by
      simp_rw [heq]
      exact LeanLab.PNTPort.Gallagher.parseval (fun n => (vonMangoldt n : ℂ)) (X + 1)
    _ = ∑ n ∈ Finset.Icc 1 X, vonMangoldt n ^ 2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [Nat.range_succ_eq_Icc_zero]
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
      intro n hn hn'
      have hn0 : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
      simp [hn0]

/-- Pages 16 and 17, proof of Lemma 4.2. A pointwise minor arc bound times the full energy. -/
theorem minor_energy84 (X : ℕ) (R : ℝ) {B : ℝ}
    (hB : ∀ α : ℝ, ¬ MajorArc X R α → ‖Ssum X α‖ ≤ B) :
    ∑ N ∈ Finset.Icc 1 X, ‖rMinor X R N‖ ^ 2 ≤
      B ^ 2 * ∑ n ∈ Finset.Icc 1 X, vonMangoldt n ^ 2 := by
  let g : ℝ → ℂ := Set.indicator {α : ℝ | ¬ MajorArc X R α} (fun α => Ssum X α ^ 2)
  have hcont : Continuous (Ssum X) := by unfold Ssum ee; fun_prop
  have hmi : MeasurableSet {α : ℝ | ¬ MajorArc X R α} := (measurableSet_majorArc84 X R).compl
  have hgpt (α : ℝ) : ‖g α‖ ^ 2 =
      Set.indicator {α : ℝ | ¬ MajorArc X R α} (fun α => ‖Ssum X α‖ ^ 4) α := by
    by_cases hα : α ∈ {α : ℝ | ¬ MajorArc X R α}
    · simp only [g, Set.indicator_of_mem hα, norm_pow]
      ring
    · simp [g, Set.indicator_of_notMem hα]
  have h4 : IntervalIntegrable (fun α => ‖Ssum X α‖ ^ 4) volume 0 1 :=
    (hcont.norm.pow 4).intervalIntegrable _ _
  have hg2 : IntervalIntegrable (fun α => ‖g α‖ ^ 2) volume 0 1 := by
    simp_rw [hgpt]
    exact ⟨h4.1.indicator hmi, h4.2.indicator hmi⟩
  have hpt (α : ℝ) : ‖g α‖ ^ 2 ≤ B ^ 2 * ‖Ssum X α‖ ^ 2 := by
    rw [hgpt]
    by_cases hα : α ∈ {α : ℝ | ¬ MajorArc X R α}
    · rw [Set.indicator_of_mem hα]
      have hs := pow_le_pow_left₀ (norm_nonneg _) (hB α hα) 2
      nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖Ssum X α‖)]
    · rw [Set.indicator_of_notMem hα]
      positivity
  have hm : (∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2) ≤
      ∫ α in (0 : ℝ)..1, B ^ 2 * ‖Ssum X α‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hg2
      (((hcont.norm.pow 2).intervalIntegrable _ _).const_mul _) (fun α _ => hpt α)
  rw [intervalIntegral.integral_const_mul, ssum_parseval84] at hm
  exact (minor_bessel84 X R).trans hm

/-- Pages 16 and 17, proof of Lemma 4.2. The displayed proof gives logarithm power nine. -/
theorem minor_second_moment84 {X : ℕ} {R : ℝ} (hX : 2 ≤ X) (hR : 1 ≤ R) (hRX : R ≤ X) :
    ∑ N ∈ Finset.Icc 1 X, ‖rMinor X R N‖ ^ 2 ≤
      (12 * (48600 : ℝ) ^ 2) * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) *
        X * Real.log X ^ 9 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hR0 : 0 < R := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hA : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hR0.le]
  have hD : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    norm_num
  have hsq : ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 ≤
      2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA, ← hD]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  let B : ℝ := 48600 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4
  have hB : ∀ α : ℝ, ¬ MajorArc X R α → ‖Ssum X α‖ ≤ B :=
    fun α hminor => minor_pointwise84 hX hR hRX hminor
  calc
    _ ≤ B ^ 2 * ∑ n ∈ Finset.Icc 1 X, vonMangoldt n ^ 2 := minor_energy84 X R hB
    _ ≤ B ^ 2 * (6 * X * Real.log X) :=
      mul_le_mul_of_nonneg_left (mangoldt_energy84 X) (sq_nonneg B)
    _ = 6 * (48600 : ℝ) ^ 2 *
        ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 9 := by
      dsimp [B]
      ring
    _ ≤ 6 * (48600 : ℝ) ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 9 := by
      gcongr
    _ = _ := by ring

/-- The exact sealed Lemma42 9 proposition, now assembled from the completed proof steps. -/
theorem lemma42_proved84 : Lemma42 9 := by
  intro ε hε
  refine ⟨12 * (48600 : ℝ) ^ 2, fun X hX R hR hupper => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hp : (X : ℝ) ^ (1 / 2 - ε) ≤ X := by
    conv_rhs => rw [← Real.rpow_one (X : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  exact minor_second_moment84 hX hR (hupper.le.trans hp)

/-- Lemma 4.2 with its sealed statement and a completed proof. -/
theorem lemma42 : Lemma42 9 := lemma42_proved84

end LeanLab.BhowmikGrimmelt2026










