module

public import LeanLab.Linnik1951.SPLIT_grh_mellin_transfer519
public import LeanLab.Linnik1951.LnLCrossing1117
public import LeanLab.PNTPort.DirichletZF.Growth
public import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
P0093 Linnik 1951, page 159 before equation 5.1, with page 155 and page 156 equation 4.1.
Proves grh_strip_log_bound_proof_b1122: the holomorphic logarithm G of L of s and chi,
normalised by the prime power series, is at most B0 times the cube of ln of N times
the absolute imaginary part plus 2 on 1/2 + 1/ln N at most re s at most 2, by the
Titchmarsh 14.2 method: Borel Caratheodory with the upper bound for L, no zero sums.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open Filter Topology Metric

/-- P0093 page 155. The Euler logarithm series for one prime: the sum over k of
chi of p to the k + 1 times p to the minus k + 1 times s over k + 1 is minus the log of
one minus chi of p times p to the minus s, when re s exceeds 0. -/
theorem euler_log_term_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 0 < s.re) (p : Nat.Primes) :
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

/-- P0093 page 155 and page 159 before equation 5.1. A function G holomorphic on
re s greater than 1/2 that equals the prime power series on re s greater than 1 is a
logarithm of L there: exp of G is the Euler product on re s greater than 1, and the
identity theorem on the connected half plane extends the equality. -/
theorem exp_G_eq_LFunction_b1122x {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (G : ℂ → ℂ) (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (w : ℂ) (hw : 1 / 2 < w.re) :
    Complex.exp (G w) = DirichletCharacter.LFunction χ w := by
  have hHo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVo : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : ∀ s : ℂ, 1 < s.re → Complex.exp (G s) = DirichletCharacter.LFunction χ s := by
    intro s hs
    rw [hGs s hs, tsum_congr fun p => euler_log_term_b1122x χ s (by linarith) p,
      DirichletCharacter.LFunction_eq_LSeries χ hs,
      ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs]
  have hA : AnalyticOnNhd ℂ (fun s => Complex.exp (G s)) {s : ℂ | 1 / 2 < s.re} :=
    hGd.cexp.analyticOnNhd hHo
  have hB : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 / 2 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hHo
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  have hev : (fun s => Complex.exp (G s)) =ᶠ[𝓝 (2 : ℂ)] DirichletCharacter.LFunction χ := by
    filter_upwards [hVo.mem_nhds h2] with s hs
    exact h1 s hs
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt (r := 1 / 2)).isPreconnected (by norm_num) hev hw

/-- Titchmarsh 14.2 step one, with P0093 page 159. The real part of the logarithm G is
log of the norm of L, and the bound of L by q times the norm of w over re w gives
re G w at most log of 2 q times 4 plus the absolute imaginary part, for re w in
the range 1/2 to 4. -/
theorem re_G_le_b1122x {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (G : ℂ → ℂ) (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (w : ℂ) (hw : 1 / 2 < w.re) (hw4 : w.re ≤ 4) :
    (G w).re ≤ Real.log (2 * q * (4 + |w.im|)) := by
  have he := exp_G_eq_LFunction_b1122x χ hχ G hGd hGs w hw
  have hn : Real.exp (G w).re = ‖DirichletCharacter.LFunction χ w‖ := by
    rw [← he, Complex.norm_exp]
  have hL := LeanLab.PNTPort.DirichletZF.norm_LFunction_le hχ (s := w) (by linarith)
  have hwn : ‖w‖ ≤ 4 + |w.im| := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos (by linarith : 0 < w.re)] at this
    linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hdiv : (q : ℝ) * ‖w‖ / w.re ≤ 2 * q * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ (q : ℝ) * ‖w‖ := by positivity
    nlinarith
  have hfin : Real.exp (G w).re ≤ 2 * q * (4 + |w.im|) := by
    rw [hn]
    calc _ ≤ _ := hL
      _ ≤ 2 * q * ‖w‖ := hdiv
      _ ≤ 2 * q * (4 + |w.im|) := by gcongr
  calc (G w).re = Real.log (Real.exp (G w).re) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) hfin

/-- P0093 page 155. The constant majorant K, the sum over primes of 3/2 times p to
the minus 2, is summable. -/
theorem summable_K_b1122x :
    Summable (fun p : Nat.Primes => (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  apply Summable.mul_left
  have h := (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  exact h.comp_injective Nat.Primes.coe_nat_injective

/-- P0093 page 155, the center of the Borel Caratheodory disc. On re w equal to 2 the
prime power series G w has norm at most K, the sum over primes of 3/2 times p to the
minus 2, since each Euler logarithm is at most 3/2 times p to the minus 2. -/
theorem norm_G_center_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℂ → ℂ)
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (w : ℂ) (hw : w.re = 2) :
    ‖G w‖ ≤ ∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  rw [hGs w (by rw [hw]; norm_num),
    tsum_congr fun p => euler_log_term_b1122x χ w (by rw [hw]; norm_num) p]
  apply tsum_of_norm_bounded summable_K_b1122x.hasSum
  intro p
  have hv : ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-w)‖ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hw]
    calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ = _ := one_mul _
  have hhalf : ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 / 2 := by
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    calc ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = ((p : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
  have hw2 : ‖-(χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-w))‖ ≤ 1 / 2 := by
    rw [norm_neg]; exact hv.trans hhalf
  have hl := Complex.norm_log_one_add_half_le_self hw2
  rw [← sub_eq_add_neg, norm_neg] at hl
  rw [norm_neg]
  exact hl.trans (mul_le_mul_of_nonneg_left hv (by norm_num))

/-- Titchmarsh 14.2, Borel Caratheodory step, used for P0093 page 159 before 5.1.
With centre w0 equal to 2 + i Im s and radius 3/2 - 1/(2 l), where l at least 1 and
1/2 + 1/l at most re s at most 2, the norm of G s is at most K plus 8 l times
log of 2 q times the absolute imaginary part plus 6, plus K plus 1. -/
theorem G_strip_bound_b1122x {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (G : ℂ → ℂ) (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (l : ℝ) (hl : 1 ≤ l) (s : ℂ) (hs1 : 1 / 2 + 1 / l ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖G s‖ ≤ (∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) + 8 * l *
      (Real.log (2 * q * (|s.im| + 6)) +
        (∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) + 1) := by
  set K : ℝ := ∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun p => by positivity
  set t : ℝ := s.im with ht
  set w0 : ℂ := ⟨2, t⟩ with hw0
  have hw0re : w0.re = 2 := rfl
  have hw0im : w0.im = t := rfl
  have hc := norm_G_center_b1122x χ G hGs w0 hw0re
  set R : ℝ := 3 / 2 - 1 / (2 * l) with hR
  have hl0 : 0 < l := by linarith
  have hinv : 1 / l ≤ 1 := by rw [div_le_one hl0]; exact hl
  have hinv0 : 0 < 1 / l := by positivity
  have h2l : 1 / (2 * l) = (1 / l) / 2 := by field_simp
  have hRpos : 0 < R := by rw [hR, h2l]; linarith
  have hR32 : R ≤ 3 / 2 := by rw [hR, h2l]; linarith
  set M : ℝ := Real.log (2 * q * (|t| + 6)) + K + 1 with hM
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hlog0 : 0 ≤ Real.log (2 * q * (|t| + 6)) := by
    apply Real.log_nonneg
    have : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hMpos : 0 < M := by rw [hM]; linarith
  set f : ℂ → ℂ := fun u => G (w0 + u) - G w0 with hf
  have hball : ∀ u ∈ ball (0 : ℂ) R, 1 / 2 + 1 / (2 * l) < (w0 + u).re ∧
      (w0 + u).re ≤ 4 ∧ |(w0 + u).im| ≤ |t| + 2 := by
    intro u hu
    have hu' : ‖u‖ < R := mem_ball_zero_iff.mp hu
    have hre := Complex.abs_re_le_norm u
    have him := Complex.abs_im_le_norm u
    rw [abs_le] at hre
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.add_re, hw0re]; rw [hR] at hu'; linarith [hre.1]
    · simp only [Complex.add_re, hw0re]; linarith [hre.2]
    · simp only [Complex.add_im, hw0im]
      calc |t + u.im| ≤ |t| + |u.im| := abs_add_le _ _
        _ ≤ |t| + 2 := by linarith
  have hmaps : Set.MapsTo (fun u => w0 + u) (ball (0 : ℂ) R) {s : ℂ | 1 / 2 < s.re} := by
    intro u hu
    have := (hball u hu).1
    have : 0 < 1 / (2 * l) := by positivity
    simp only [Set.mem_ofPred_eq]; linarith
  have hfd : DifferentiableOn ℂ f (ball (0 : ℂ) R) :=
    (hGd.comp (differentiableOn_const _ |>.add differentiableOn_id) hmaps).sub_const _
  have hf1 : Set.MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ M} := by
    intro u hu
    obtain ⟨hre1, hre4, him⟩ := hball u hu
    have hpos : 1 / 2 < (w0 + u).re := by
      have : 0 < 1 / (2 * l) := by positivity
      linarith
    have hG1 := re_G_le_b1122x χ hχ G hGd hGs (w0 + u) hpos hre4
    have hmono : Real.log (2 * q * (4 + |(w0 + u).im|)) ≤ Real.log (2 * q * (|t| + 6)) := by
      apply Real.log_le_log
      · have : 0 ≤ |(w0 + u).im| := abs_nonneg _
        nlinarith
      · have : (0 : ℝ) ≤ 2 * q := by positivity
        nlinarith
    have hc' : -(G w0).re ≤ K := by
      have := Complex.abs_re_le_norm (G w0)
      rw [abs_le] at this
      linarith
    simp only [Set.mem_ofPred_eq, hf, Complex.sub_re]
    rw [hM]; linarith
  set z : ℂ := s - w0 with hz
  have hzeq : z = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hz, hw0re]
    · simp [hz, hw0im, ht]
  have hzn : ‖z‖ = 2 - s.re := by
    rw [hzeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  have hgap : 1 / (2 * l) ≤ R - ‖z‖ := by
    rw [hzn, hR, h2l]; linarith
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    have : 0 < 1 / (2 * l) := by positivity
    linarith
  have hf0 : f 0 = 0 := by simp [hf]
  have hBC := Complex.borelCaratheodory_zero hMpos hfd hf1 hRpos hzR hf0
  have hgap' : 1 / 2 ≤ l * (R - ‖z‖) := by
    have h := mul_le_mul_of_nonneg_left hgap hl0.le
    have : l * (1 / (2 * l)) = 1 / 2 := by field_simp
    linarith
  have hgpos : 0 < R - ‖z‖ := lt_of_lt_of_le (by positivity) hgap
  have hzle : ‖z‖ ≤ 2 := by rw [hzn]; linarith
  have hfz : ‖f z‖ ≤ 8 * l * M := by
    refine hBC.trans ?_
    rw [div_le_iff₀ hgpos]
    have h1 : 4 * M ≤ 8 * M * (l * (R - ‖z‖)) := by nlinarith
    have h2 : 2 * M * ‖z‖ ≤ 4 * M := by nlinarith [norm_nonneg z]
    nlinarith
  have hGs' : G s = f z + G w0 := by
    simp only [hf, hz]; ring_nf
  rw [hGs']
  calc ‖f z + G w0‖ ≤ ‖f z‖ + ‖G w0‖ := norm_add_le _ _
    _ ≤ 8 * l * M + K := add_le_add hfz hc
    _ = K + 8 * l * M := by ring

/-- P0093 page 159 before equation 5.1, the GRH bound for ln L used by Linnik, proved
here by the Titchmarsh 14.2 Borel Caratheodory method without GRH: for N above 2, q at
most N to the 1/7, chi nonprincipal and G the holomorphic logarithm of L fixed by the
prime power series on re s greater than 1, the norm of G on 1/2 + 1/ln N at most re s
at most 2 is at most B0 times the cube of ln of N times the absolute imaginary part
plus 2. The GRH hypothesis is not used. -/
theorem grh_strip_log_bound_proof_b1122 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ G : ℂ → ℂ,
          DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} →
          (∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
            (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) →
          ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
            ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 := by
  set K : ℝ := ∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun p => by positivity
  refine ⟨9 * K + 57, by positivity, 2, ?_⟩
  intro N hN q _ hq1 hqN χ hχ G hGd hGs s hs1 hs2
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hB := G_strip_bound_b1122x χ hχ G hGd hGs (Real.log N) hl1 s hs1 hs2
  rw [← hK] at hB
  set t : ℝ := s.im with ht
  set X : ℝ := Real.log ((N : ℝ) * (|t| + 2)) with hX
  have hta : 0 ≤ |t| := abs_nonneg t
  have hlX : Real.log N ≤ X := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hX1 : 1 ≤ X := hl1.trans hlX
  have hqN' : (q : ℝ) ≤ N := by
    calc (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := hqN
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hlog : Real.log (2 * q * (|t| + 6)) ≤ 5 + X := by
    have h6 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
      linarith
    have hle : 2 * q * (|t| + 6) ≤ 6 * ((N : ℝ) * (|t| + 2)) := by nlinarith
    calc Real.log (2 * q * (|t| + 6)) ≤ Real.log (6 * ((N : ℝ) * (|t| + 2))) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log 6 + X := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 5 + X := by linarith
  have hM : Real.log (2 * q * (|t| + 6)) + K + 1 ≤ (7 + K) * X := by nlinarith
  have hM0 : 0 ≤ Real.log (2 * q * (|t| + 6)) + K + 1 := by
    have : 0 ≤ Real.log (2 * q * (|t| + 6)) := Real.log_nonneg (by nlinarith)
    linarith
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have h1X3 : 1 ≤ X ^ 3 := by nlinarith
  have hstep : 8 * Real.log N * (Real.log (2 * q * (|t| + 6)) + K + 1) ≤
      8 * (7 + K) * X ^ 3 := by
    have ha : Real.log N * (Real.log (2 * q * (|t| + 6)) + K + 1) ≤ X * ((7 + K) * X) :=
      mul_le_mul hlX hM hM0 (by linarith)
    have : X * ((7 + K) * X) = (7 + K) * X ^ 2 := by ring
    nlinarith
  have hKX : K ≤ K * X ^ 3 := by nlinarith
  calc ‖G s‖ ≤ K + 8 * Real.log N * (Real.log (2 * q * (|t| + 6)) + K + 1) := hB
    _ ≤ (9 * K + 57) * X ^ 3 := by nlinarith

end LeanLab.Linnik1951.Task519
