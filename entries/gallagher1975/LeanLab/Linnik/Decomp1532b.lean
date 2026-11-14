module

public import Mathlib
public import LeanLab.Linnik.Decomp1532b2
public import LeanLab.RieselVaughan1983.MuPhiSum
public import LeanLab.RieselVaughan1983.GaussImprim
public import LeanLab.PNTSieve.MertensUpper
public import LeanLab.Linnik.U1394Fejer
public import LeanLab.Linnik.HilbertCosecant
public import LeanLab.HardyLittlewood1923.U1482ZeroCount
public import LeanLab.RieselVaughan1983.LargeSieveSchur
public import LeanLab.PNTPort.LargeSieve.Montgomery
public import LeanLab.Linnik.Decomp1532a
public import LeanLab.HeathBrown1985.DivisorEps
public import LeanLab.Linnik.U7204Display4
public import LeanLab.Zinoviev1997.TotientTail
public import LeanLab.PNTPort.DirichletZF.Siegel
public import LeanLab.Romanov.Decomp134
public import LeanLab.PNTPort.DirichletZF.Landau
public import LeanLab.PNTPort.StrongPNT.StrongPNT
public import LeanLab.Romanov.TotientWeights134
public import LeanLab.Linnik.Decomp1537a

/-!
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File b: the major arcs of Section 1, pp. 127-132, and Lemmas 6, 9, 10 of Section 2,
pp. 134-137.
* `majorArcs N P`: the union of the arcs `|α - a/q| ≤ 1/(qQ)`, `Q = N/P`, `1 ≤ q ≤ P`,
  `(a, q) = 1`, inside `[0, 1]`, display (2) p. 127. The arc of `a/q = 0/1` and `1/1` together
  are the arc `M(1, 1)` of the paper taken mod 1.
* `ramanujanSum q n = c_q(n)`, `singSeries n = Σ_q μ(q)²/φ(q)² c_q(n)`, p. 130 and p. 134.
* `Jn N n = Σ_{m₁ - m₂ = n} 1/(log m₁ log m₂)`, Theorem 3, p. 127.
* `zeroCount χ σ T`, the distinct zeros of `L(s, χ)` with `Re ρ ≥ σ`, `|Im ρ| ≤ T`.
* `excSet b T`, primitive characters of conductor at most `T` whose L-function has a zero with
  `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`, p. 127.
Leaves: disjointness and measure of the major arcs, Dirichlet's theorem, the Gauss sum, the
Ramanujan sum, the singular series, `J(n)`, the geometric sum behind `T(β)`, the multiplicative
large sieve, Gallagher's density estimate for zeros near 1, Page's theorem, Siegel's theorem,
Lemmas 6, 9 and 10.
Assembly: `minor_approx`, every point of `[0, 1]` off the major arcs has an approximation
`a/q` with `P < q ≤ N/P`, the starting point of Lemma 11, p. 137.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Proof additions by Codex task189 on 2026-10-30. AI wrote the Lean code.
Proof additions by Codex task195 on 2026-10-31 UTC. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp1532b

open LeanLab.PNTPort.DirichletZF

open Finset MeasureTheory ZMod ArithmeticFunction Filter Asymptotics
open LeanLab.PNTPort.DirichletZF (siegel_zero riemannZeta_real_neg L_lift lift_ne_one lift_sq)
open scoped Topology
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov (sum_moebius_divisors)
open LeanLab.PNTPort.LargeSieve (dist0 norm_e e_add norm_geom_le)
open LeanLab.Linnik.Decomp1532a (pairs dif ordTwo)
open LeanLab.Linnik.U1434Lemma21 (sv)
open LeanLab.Linnik.U1426ChainWire (Gs)
open LeanLab.Linnik.U1412Display53 (eC)

/-- The major arcs `𝔐`, display (2) p. 127, with `Q = N/P`, so `1/(qQ) = P/(qN)`. -/
def majorArcs (N : ℕ) (P : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℕ, a ≤ q ∧ Nat.Coprime a q ∧
    |α - a / q| ≤ P / (q * N)}

/-- The Ramanujan sum `c_q(n) = Σ_{a < q, (a, q) = 1} e(an/q)`. -/
noncomputable def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ range q with Nat.Coprime a q, eC ((a : ℝ) * n / q)

/-- The singular series `𝔖(n) = Σ_{q ≥ 1} μ(q)²/φ(q)² c_q(n)`, p. 130; for g = 2 this is the
`𝔖(n)` of p. 134, with `D/φ(D) = 2`. -/
noncomputable def singSeries (n : ℤ) : ℂ :=
  ∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n

/-- `J(n) = Σ_{1 < m₁, m₂ ≤ N, m₁ - m₂ = n} (log m₁ log m₂)⁻¹`, Theorem 3, p. 127. -/
noncomputable def Jn (N : ℕ) (n : ℤ) : ℝ :=
  ∑ m ∈ Ioc 1 N ×ˢ Ioc 1 N with (m.1 : ℤ) - m.2 = n, 1 / (Real.log m.1 * Real.log m.2)

/-- The distinct zeros `ρ` of `L(s, χ)` with `Re ρ ≥ σ` and `|Im ρ| ≤ T`. -/
noncomputable def zeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- Primitive characters of conductor `q + 1 ≤ T` whose L-function vanishes somewhere in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`, p. 127. -/
def excSet (b T : ℝ) : Set (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) :=
  {x | ((x.1 : ℝ) + 1 ≤ T) ∧ x.2.IsPrimitive ∧
    ∃ ρ : ℂ, x.2.LFunction ρ = 0 ∧ 1 - b / Real.log T ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- LEAF. Unit U-1532. The major arcs are disjoint when `2P² < N`, i.e. `2P < Q`: two arcs about
distinct fractions `a/q`, `a'/q'` with `q, q' ≤ P` do not meet, p. 127, after display (2). -/
theorem majorArcs_disjoint {N : ℕ} {P : ℝ} (hP : 0 < P) (hPN : 2 * P ^ 2 < N)
    {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : (q : ℝ) ≤ P) (hqP' : (q' : ℝ) ≤ P)
    (hne : (a : ℝ) / q ≠ a' / q') {α : ℝ}
    (h1 : |α - a / q| ≤ P / (q * N)) (h2 : |α - a' / q'| ≤ P / (q' * N)) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hPN
  have hcross : (a : ℤ) * q' - (a' : ℤ) * q ≠ 0 := by
    intro h
    apply hne
    apply (div_eq_div_iff hq0.ne' hq0'.ne').mpr
    exact_mod_cast (sub_eq_zero.mp h)
  have hint : (1 : ℝ) ≤ |(a : ℝ) * q' - (a' : ℝ) * q| := by
    have h := Int.one_le_abs hcross
    exact_mod_cast h
  have hdist : |(a : ℝ) / q - (a' : ℝ) / q'| ≤ P / (q * N) + P / (q' * N) := by
    calc
      _ = |(α - (a' : ℝ) / q') - (α - (a : ℝ) / q)| := by congr 1; ring
      _ ≤ |α - (a' : ℝ) / q'| + |α - (a : ℝ) / q| := abs_sub _ _
      _ ≤ _ := by linarith
  have heq : (a : ℝ) / q - (a' : ℝ) / q' =
      ((a : ℝ) * q' - (a' : ℝ) * q) / (q * q') := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hq0 hq0')] at hdist
  have hdist' := (div_le_iff₀ (mul_pos hq0 hq0')).mp hdist
  have heq' : (P / ((q : ℝ) * N) + P / ((q' : ℝ) * N)) * (q * q') =
      P * (q + q') / N := by field_simp <;> ring
  rw [heq'] at hdist'
  have hbound := (le_div_iff₀ hN).mp (hint.trans hdist')
  nlinarith

/-- LEAF. Unit U-1532. For `P ≥ 1`, `N ≥ 1` the major arcs have measure at most `4P²/N`,
since there are at most `2 + Σ_{2 ≤ q ≤ P} φ(q)` arcs and the arc at `a/q` has length
`2P/(qN)`, p. 127. -/
theorem volume_majorArcs_le {N : ℕ} {P : ℝ} (hP : 1 ≤ P) (hN : 1 ≤ N) :
    MeasureTheory.volume (majorArcs N P) ≤ ENNReal.ofReal (4 * P ^ 2 / N) := by
  classical
  have hP0 : 0 ≤ P := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let A : ℕ → ℕ → Set ℝ := fun q a =>
    Set.Icc ((a : ℝ) / q - P / (q * N)) ((a : ℝ) / q + P / (q * N))
  have hsub : majorArcs N P ⊆ ⋃ q ∈ Icc 1 ⌊P⌋₊, ⋃ a ∈ range (q + 1), A q a := by
    rintro α ⟨_, q, hq, hqP, a, haq, _, ha⟩
    refine Set.mem_iUnion₂.mpr ⟨q, mem_Icc.mpr ⟨hq, Nat.le_floor hqP⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨a, mem_range.mpr (by omega), ?_⟩
    change _ ≤ α ∧ α ≤ _
    rw [abs_le] at ha
    constructor <;> linarith [ha.1, ha.2]
  have hA : ∀ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ range (q + 1), volume (A q a) ≤
      ENNReal.ofReal (4 * P / N) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have heq : ∀ a, volume (A q a) = ENNReal.ofReal (2 * P / (q * N)) := by
      intro a
      change volume (Set.Icc _ _) = _
      rw [Real.volume_Icc]
      congr 1
      ring
    simp_rw [heq]
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos hq0 hN0) hN0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (mul_nonneg hP0 hN0.le)]
  calc
    volume (majorArcs N P) ≤ volume (⋃ q ∈ Icc 1 ⌊P⌋₊, ⋃ a ∈ range (q + 1), A q a) := measure_mono hsub
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, volume (⋃ a ∈ range (q + 1), A q a) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ range (q + 1), volume (A q a) :=
      sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ENNReal.ofReal (4 * P / N) := sum_le_sum hA
    _ ≤ ENNReal.ofReal (4 * P ^ 2 / N) := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hf := Nat.floor_le hP0
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hN0]
      nlinarith

/-- LEAF. Unit U-1532. Dirichlet's theorem in the form of p. 127, display (2): for
`α ∈ [0, 1]` and real `Q ≥ 1` there are `1 ≤ q ≤ Q` and `0 ≤ a ≤ q`, `(a, q) = 1`, with
`|α - a/q| ≤ 1/(qQ)`. -/
theorem exists_approx {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |α - a / q| ≤ 1 / (q * Q) := by
  have ha0 := hα.1
  have ha1 := hα.2
  have hQ0 : 0 < Q := by linarith
  have hn : 0 < ⌊Q⌋₊ := by have := Nat.le_floor (n := 1) (by simpa using hQ); omega
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hdenQ : (r.den : ℝ) ≤ Q :=
    (show (r.den : ℝ) ≤ ⌊Q⌋₊ by exact_mod_cast hden).trans (Nat.floor_le (by linarith))
  have hbd : |α - (r : ℝ)| ≤ 1 / (r.den * Q) := by
    refine hr.trans (one_div_le_one_div_of_le (mul_pos hd0 hQ0) ?_)
    nlinarith [Nat.lt_floor_add_one Q]
  by_cases hr0 : (r : ℝ) < 0
  · refine ⟨1, 0, by norm_num, by simpa using hQ, by norm_num, by norm_num, ?_⟩
    have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hsmall : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    simp only [Nat.cast_one, Nat.cast_zero, zero_div, sub_zero, one_mul]
    rw [abs_of_nonneg hα.1]
    rw [abs_of_nonneg (by linarith : 0 ≤ α - (r : ℝ))] at hbd
    linarith
  by_cases hr1 : 1 < (r : ℝ)
  · refine ⟨1, 1, by norm_num, by simpa using hQ, by norm_num, by norm_num, ?_⟩
    have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hsmall : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    simp only [Nat.cast_one, div_one, one_mul]
    rw [abs_of_nonpos (by linarith : α - 1 ≤ 0)]
    rw [abs_of_nonpos (by linarith : α - (r : ℝ) ≤ 0)] at hbd
    linarith
  have hnum0 : 0 ≤ r.num := Rat.num_nonneg.mpr (by exact_mod_cast (le_of_not_gt hr0))
  have hcast : (r.num.toNat : ℝ) / r.den = r := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum0, Rat.cast_def]
  refine ⟨r.den, r.num.toNat, r.den_pos, hdenQ, ?_, ?_, ?_⟩
  · have : (r.num.toNat : ℝ) / r.den ≤ 1 := by rw [hcast]; exact le_of_not_gt hr1
    have := (div_le_one hd0).mp this
    exact_mod_cast this
  · have he : r.num.toNat = r.num.natAbs := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg hnum0, Int.natCast_natAbs, abs_of_nonneg hnum0]
    rw [he]
    exact r.reduced
  · simpa [hcast] using hbd

/-- ASSEMBLY, CONDITIONAL ON the leaf `exists_approx`. A point of `[0, 1]` off the major arcs,
with `0 < P ≤ N`, has an approximation `a/q` in lowest terms with `P < q ≤ N/P` and
`|α - a/q| ≤ P/(qN)`; this is the start of the proof of Lemma 11, p. 137. -/
theorem minor_approx {N : ℕ} {P : ℝ} (hP : 0 < P) (hPN : P ≤ N) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hM : α ∉ majorArcs N P) :
    ∃ q a : ℕ, P < q ∧ (q : ℝ) ≤ N / P ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |α - a / q| ≤ P / (q * N) := by
  have hN : (0 : ℝ) < N := lt_of_lt_of_le hP hPN
  have hQ : 1 ≤ (N : ℝ) / P := by rw [le_div_iff₀ hP]; linarith
  obtain ⟨q, a, hq1, hqQ, haq, hcop, happ⟩ := exists_approx hα hQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have heq : 1 / (q * ((N : ℝ) / P)) = P / (q * N) := by
    field_simp
  rw [heq] at happ
  refine ⟨q, a, ?_, hqQ, haq, hcop, happ⟩
  by_contra hle
  push Not at hle
  exact hM ⟨hα, q, hq1, hle, a, haq, hcop, happ⟩

/-- LEAF. Unit U-1532. A primitive character `χ` modulo `q` has Gauss sum of absolute value
`√q`, display (6) p. 129 in the case `q = r`. -/
theorem gaussSum_norm_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖∑ a : ZMod q, χ a * eC ((a.val : ℝ) / q)‖ ^ 2 = q := by
  have he : (∑ a : ZMod q, χ a * eC ((a.val : ℝ) / q)) = gaussSum χ ZMod.stdAddChar := by
    unfold gaussSum
    apply sum_congr rfl
    intro a _
    congr 1
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    unfold eC
    congr 1
    push_cast
    ring
  rw [he]
  classical
  have hft : ZMod.dft χ = fun k => χ⁻¹ (-k) * gaussSum χ stdAddChar := by
    ext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hχinv : χ⁻¹.IsPrimitive := by simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hprod : gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = (q : ℂ) * χ (-1) := by
    have h := congr_fun (ZMod.dft_dft χ) (1 : ZMod q)
    rw [hft] at h
    rw [ZMod.dft_mul_const, ZMod.dft_comp_neg] at h
    dsimp only at h
    rw [hχinv.fourierTransform_eq_inv_mul_gaussSum] at h
    simpa [mul_comm] using h
  have hstar : star (gaussSum χ stdAddChar) = χ⁻¹ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [star_gaussSum_eq]
    simp only [gaussSum, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.neg (ZMod q))
    intro a
    simp only [Equiv.neg_apply, AddChar.inv_apply]
    rw [← mul_assoc, ← map_mul, neg_one_mul, neg_neg]
  have heq : gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = (q : ℂ) := by
    calc
      _ = (gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar) * χ⁻¹ (-1) := by rw [hstar]; ring
      _ = (q : ℂ) * (χ⁻¹ (-1) * χ (-1)) := by rw [hprod]; ring
      _ = q := by rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply isUnit_neg_one, mul_one]
  have hn := congrArg Complex.re heq
  have hn' : Complex.normSq (gaussSum χ stdAddChar) = (q : ℝ) := by
    simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.natCast_re] using hn
  rwa [Complex.normSq_eq_norm_sq] at hn'

/-- The divisor formula for the Ramanujan sum at an integer argument, p.130.
Adapted from the lab natural argument proof in PNTPort.Vinogradov.SingSeries. -/
theorem ramanujanSum_eq_divisor_sum {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q n = ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
      (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℤ) := by
  have heq : ramanujanSum q n =
      ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), LeanLab.PNTPort.LargeSieve.e (n * r / q) := by
    unfold ramanujanSum
    apply sum_congr rfl
    intro a ha
    rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
    congr 1
    ring
  rw [heq, Nat.gcd_comm q n.natAbs]

  rw [sum_filter]
  have step1 : ∀ r ∈ range q, (if Nat.Coprime r q then LeanLab.PNTPort.LargeSieve.e (n * r / q) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (μ d : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * r / q) := by
    intro r _
    rw [← sum_mul, sum_moebius_divisors]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl step1]
  rw [sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun r => d ∣ r))]
  · have step2 : ∀ d ∈ q.divisors, ∑ r ∈ (range q).filter (fun r => d ∣ r), (μ d : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * r / q)
        = (μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ n then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← mul_sum, ← LeanLab.PNTPort.LargeSieve.sum_e_mul_div n hqd]
      congr 1
      refine sum_nbij' (fun r => r / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [mem_filter, mem_range] at hr
        rw [mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [mem_range] at hs
        rw [mem_filter, mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro r hr
        rw [mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        rw [mem_filter] at hr
        obtain ⟨s, rfl⟩ := hr.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [sum_congr rfl step2]
    -- reindex d ↦ q / d onto the divisors of gcd(n, q)
    rw [← sum_filter_add_sum_filter_not q.divisors (fun d => ((q / d : ℕ) : ℤ) ∣ n)]
    rw [sum_eq_zero (s := q.divisors.filter (fun d => ¬ ((q / d : ℕ) : ℤ) ∣ n))
      (fun d hd => by rw [mem_filter] at hd; rw [if_neg hd.2, mul_zero]), add_zero]
    refine sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mem_divisors]
      refine ⟨Nat.dvd_gcd (Int.natCast_dvd.mp hd.2) (Nat.div_dvd_of_dvd hd.1.1), ?_⟩
      exact (Nat.gcd_pos_of_pos_right n.natAbs (by omega)).ne'
    · intro e he
      rw [Nat.mem_divisors] at he
      have heq : e ∣ q := (Nat.dvd_gcd_iff.1 he.1).2
      have hen : e ∣ n.natAbs := (Nat.dvd_gcd_iff.1 he.1).1
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos heq (by omega)
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd heq, by omega⟩, ?_⟩
      rw [Nat.div_div_self heq (by omega)]; exact Int.natCast_dvd.mpr hen
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro e he
      rw [Nat.mem_divisors] at he
      exact Nat.div_div_self (Nat.dvd_gcd_iff.1 he.1).2 (by omega)
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [if_pos hd.2, Nat.div_div_self hd.1.1 (by omega)]
      ring
  · intro r d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, by omega⟩


/-- LEAF. Unit U-1532. For squarefree `q`, `c_q(n) = μ(q/(q, n)) φ((q, n))`, the fact used on
p. 130 before display (11). -/
theorem ramanujanSum_squarefree {q : ℕ} (hq : Squarefree q) (n : ℤ) :
    ramanujanSum q n =
      ((ArithmeticFunction.moebius (q / Nat.gcd q n.natAbs) : ℤ) : ℂ) *
        ((Nat.gcd q n.natAbs).totient : ℂ) := by
  classical
  rw [ramanujanSum_eq_divisor_sum (Nat.pos_of_ne_zero hq.ne_zero) n]
  generalize hgdef : Nat.gcd q n.natAbs = g
  have hg : g ∣ q := hgdef ▸ Nat.gcd_dvd_left q n.natAbs
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hq.ne_zero hg
  have hcop : Nat.Coprime (q / g) g := Nat.coprime_of_squarefree_mul (by rwa [Nat.div_mul_cancel hg])
  have hsum : (∑ d ∈ g.divisors, (d : ℂ) * (moebius (g / d) : ℤ)) = (g.totient : ℂ) := by
    have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℂ) (f := fun n => (n.totient : ℂ))
      (g := fun n => (n : ℂ))).mp (by intro n hn; exact_mod_cast Nat.sum_totient n) g (Nat.pos_of_ne_zero hg0)
    rw [Nat.sum_divisorsAntidiagonal' (fun a b => (moebius a : ℂ) * (b : ℂ))] at h
    simpa only [mul_comm] using h
  calc
    _ = ∑ d ∈ g.divisors, (moebius (q / g) : ℂ) * ((d : ℂ) * (moebius (g / d) : ℂ)) := by
      apply sum_congr rfl
      intro d hd
      have hdg := Nat.dvd_of_mem_divisors hd
      have heq : q / d = (q / g) * (g / d) := by rw [← Nat.mul_div_assoc _ hdg, Nat.div_mul_cancel hg]
      rw [heq, isMultiplicative_moebius.map_mul_of_coprime (hcop.of_dvd_right (Nat.div_dvd_of_dvd hdg))]
      push_cast
      ring
    _ = _ := by rw [← mul_sum, hsum]

/-- The literal numerator n printed on p.130 fails at q = 2 and n = 1. -/
theorem printed_ramanujan_formula_two_one_ne : ramanujanSum 2 1 ≠
    ((ArithmeticFunction.moebius (1 / Nat.gcd 2 (1 : ℤ).natAbs) : ℤ) : ℂ) *
      ((Nat.gcd 2 (1 : ℤ).natAbs).totient : ℂ) := by
  rw [ramanujanSum_squarefree Nat.squarefree_two]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- LEAF. Unit U-1532. For `n ≠ 0` the series `Σ_q μ(q)²/φ(q)² c_q(n)` defining `𝔖(n)`
converges absolutely, p. 130. -/
theorem summable_singSeries {n : ℤ} (hn : n ≠ 0) :
    Summable fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n := by
  classical
  let B : ℝ := ∑ d ∈ n.natAbs.divisors, (d : ℝ)
  have hB : 0 ≤ B := sum_nonneg fun d hd => Nat.cast_nonneg d
  have hnn : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hR (q : ℕ) : ‖ramanujanSum q n‖ ≤ B := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simpa [ramanujanSum] using hB
    rw [ramanujanSum_eq_divisor_sum hq n]
    calc
      _ ≤ ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
          ‖(d : ℂ) * (moebius (q / d) : ℤ)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ (Nat.gcd q n.natAbs).divisors, (d : ℝ) := by
        apply sum_le_sum
        intro d hd
        rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
        have hmu := ArithmeticFunction.abs_moebius_le_one (n := q / d)
        have hmu' : |((moebius (q / d) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hmu
        exact mul_le_of_le_one_right (Nat.cast_nonneg d) hmu'
      _ ≤ B := sum_le_sum_of_subset_of_nonneg
        (Nat.divisors_subset_of_dvd hnn (Nat.gcd_dvd_right q n.natAbs)) (by intros; positivity)
  have hs : Summable (fun q : ℕ => (7 * B) * (q : ℝ) ^ (-(7 : ℝ) / 4)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(7 : ℝ) / 4 < -1)).mul_left _
  apply hs.of_norm_bounded
  intro q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hmu : ‖((moebius q : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
    have h : ‖((moebius q : ℤ) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_intCast] using
        (show |((moebius q : ℤ) : ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q))
    nlinarith [norm_nonneg (((moebius q : ℤ) : ℂ))]
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 2) * B :=
      mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) (hR q) (norm_nonneg _) (by positivity)
    _ ≤ (7 * (q : ℝ) ^ (-(7 : ℝ) / 4)) * B :=
      mul_le_mul_of_nonneg_right (LeanLab.Zinoviev1997.inv_totient_sq_seven q hq) hB
    _ = _ := by ring

/-- LEAF. Unit U-1532. For g = 2 the singular series vanishes at odd `n`: the Euler factor at
`p = 2` is `1 + c_2(n) = 0`; p. 134, the remark that only `n` with `D ∣ n` occur. -/
theorem singSeries_odd {n : ℤ} (hn : Odd n) : singSeries n = 0 := by
  classical
  let f : ℕ → ℂ := fun q => (μ q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n
  have hn0 : n ≠ 0 := by intro h; subst n; norm_num at hn
  have hs : Summable f := summable_singSeries hn0
  have hn2 : Nat.Coprime 2 n.natAbs := Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hn)
  have hzero {q : ℕ} (hq : ¬ Squarefree q) : f q = 0 := by
    simp [f, moebius_eq_zero_of_not_squarefree hq]
  have hfour (q : ℕ) : f (4 * q) = 0 := by
    apply hzero
    intro hsq
    have hdiv : 2 * 2 ∣ 4 * q := by omega
    exact (by norm_num : ¬IsUnit (2 : ℕ)) (hsq 2 hdiv)
  have hpair (r : ℕ) (hr : Odd r) : f (2 * r) = -f r := by
    by_cases hsq : Squarefree r
    · have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
      have hsq2 : Squarefree (2 * r) := (Nat.squarefree_mul hcop).mpr ⟨Nat.squarefree_two, hsq⟩
      have hg : Nat.gcd (2 * r) n.natAbs = Nat.gcd r n.natAbs := hn2.gcd_mul_left_cancel r
      have hcopdiv : Nat.Coprime 2 (r / Nat.gcd r n.natAbs) :=
        hcop.of_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r n.natAbs))
      have hdiv : 2 * r / Nat.gcd r n.natAbs = 2 * (r / Nat.gcd r n.natAbs) :=
        Nat.mul_div_assoc 2 (Nat.gcd_dvd_left r n.natAbs)
      have hm1 : (μ r : ℂ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
      have hm2 : (μ (2 * r) : ℂ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq2
      dsimp [f]
      rw [ramanujanSum_squarefree hsq2 n, ramanujanSum_squarefree hsq n, hg,
        Nat.totient_mul hcop, hdiv, isMultiplicative_moebius.map_mul_of_coprime hcopdiv,
        hm2, hm1]
      norm_num [moebius_apply_prime Nat.prime_two]
    · rw [hzero hsq, hzero (fun h => hsq h.of_mul_right), neg_zero]
  have he : Summable (fun k => f (2 * k)) := hs.comp_injective (i := fun k : ℕ => 2 * k) (by
    intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hs.comp_injective (i := fun k : ℕ => 2 * k + 1) (by
    intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hee : Summable (fun k => f (2 * (2 * k))) := hs.comp_injective (i := fun k : ℕ => 2 * (2 * k)) (by
    intro a b h; change 2 * (2 * a) = 2 * (2 * b) at h; omega)
  have heo : Summable (fun k => f (2 * (2 * k + 1))) := hs.comp_injective (i := fun k : ℕ => 2 * (2 * k + 1)) (by
    intro a b h; change 2 * (2 * a + 1) = 2 * (2 * b + 1) at h; omega)
  have hsplit := tsum_even_add_odd (f := f) he ho
  have hsplit2 := tsum_even_add_odd (f := fun k => f (2 * k)) hee heo
  have heq0 : (∑' k, f (2 * (2 * k))) = 0 := by simp [show ∀ k, 2 * (2 * k) = 4 * k by intro k; omega, hfour]
  have heqneg : (∑' k, f (2 * (2 * k + 1))) = -(∑' k, f (2 * k + 1)) := by
    simp_rw [hpair (2 * _ + 1) (by exact ⟨_, rfl⟩)]
    exact tsum_neg
  change (∑' q, f q) = 0
  rw [heq0, heqneg, zero_add] at hsplit2
  rw [hsplit2.symm] at hsplit
  simpa using hsplit.symm

/-- The diagonal identity for J of zero, p.127 and p.130. -/
theorem Jn_zero_eq_sum (N : ℕ) : Jn N 0 = ∑ a ∈ Ioc 1 N, 1 / Real.log a ^ 2 := by
  classical
  unfold Jn
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro a ha
  rw [sum_eq_single_of_mem a ha]
  · simp [pow_two]
  · intro b hb hba
    have hne : (a : ℤ) - b ≠ 0 := by omega
    simp [hne]


/-- LEAF. Unit U-1532. `J(n) ≤ J(0)` for every `n`, by Cauchy-Schwarz; p. 130, the line
`J(n) ≤ J(0) ∼ N/log² N`. -/
theorem Jn_le_J0 (N : ℕ) (n : ℤ) : Jn N n ≤ Jn N 0 := by
  classical
  let T := (Ioc 1 N ×ˢ Ioc 1 N).filter (fun m => (m.1 : ℤ) - m.2 = n)
  let f : ℕ → ℝ := fun a => 1 / Real.log a
  have hJ0 : Jn N 0 = ∑ a ∈ Ioc 1 N, f a ^ 2 := by
    unfold Jn
    rw [sum_filter, sum_product]
    apply sum_congr rfl
    intro a ha
    rw [sum_eq_single_of_mem a ha]
    · simp [f, pow_two]
    · intro b hb hba
      have hne : (a : ℤ) - b ≠ 0 := by omega
      simp [hne]
  have hfst : Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Prod.ext hab
    omega
  have hsnd : Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Prod.ext _ hab
    omega
  have hproj : ∀ (p : ℕ × ℕ → ℕ), Set.InjOn p (T : Set (ℕ × ℕ)) →
      (∀ a ∈ T, p a ∈ Ioc 1 N) → (∑ a ∈ T, f (p a) ^ 2) ≤ ∑ a ∈ Ioc 1 N, f a ^ 2 := by
    intro p hinj hmem
    apply sum_le_sum_of_injOn p hinj
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact hmem b hb
    · intro a ha; exact le_rfl
    · intro a ha _; positivity
  have hleft := hproj Prod.fst hfst (fun a ha => (mem_product.mp (mem_filter.mp ha).1).1)
  have hright := hproj Prod.snd hsnd (fun a ha => (mem_product.mp (mem_filter.mp ha).1).2)
  have hterm : Jn N n ≤ (∑ a ∈ T, (f a.1 ^ 2 + f a.2 ^ 2)) / 2 := by
    unfold Jn
    change (∑ a ∈ T, 1 / (Real.log a.1 * Real.log a.2)) ≤ _
    rw [sum_div]
    apply sum_le_sum
    intro a ha
    have hsq := sq_nonneg (f a.1 - f a.2)
    have heq : 1 / (Real.log a.1 * Real.log a.2) = f a.1 * f a.2 := by simp [f, mul_comm]
    rw [heq]
    nlinarith
  rw [hJ0]
  rw [sum_add_distrib] at hterm
  linarith

/-- The lower estimate underlying J of zero asymptotic, p.130. -/
theorem J0_lower {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ) - 1) / Real.log N ^ 2 ≤ Jn N 0 := by
  rw [Jn_zero_eq_sum]
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have heq : ((N : ℝ) - 1) / Real.log N ^ 2 = ∑ a ∈ Ioc 1 N, 1 / Real.log N ^ 2 := by
    simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    rw [Nat.cast_sub hN1, Nat.cast_one]
    ring
  rw [heq]
  apply sum_le_sum
  intro a ha
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
  have haN : (a : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp ha).2
  have hapos : 0 < Real.log a := Real.log_pos ha1
  have halog : Real.log a ≤ Real.log N := Real.log_le_log (by positivity) haN
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hapos.le halog 2)

/-- LEAF. Unit U-1532. `J(0) = Σ_{1 < m ≤ N} 1/log² m ∼ N/log² N`, p. 130. -/
theorem J0_asymp :
    Filter.Tendsto (fun N : ℕ => Jn N 0 / ((N : ℝ) / Real.log N ^ 2)) Filter.atTop (nhds 1) := by
  let F : ℕ → ℝ := fun n => (n : ℝ) / Real.log n ^ 2
  let g : ℕ → ℝ := fun n => 1 / Real.log (n + 1) ^ 2
  let d : ℕ → ℝ := fun n => F (n + 1) - F n
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (nhds 0) := hlog.inv_tendsto_atTop
  have hdiff := Real.tendsto_log_nat_add_one_sub_log
  let T : ℕ → ℝ := fun n => (n : ℝ) * (Real.log (n + 1) - Real.log n) *
    (Real.log (n + 1) + Real.log n) / Real.log n ^ 2
  have hb : Tendsto (fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log n ^ 2 + 2 / Real.log n)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hdiff.mul (hi.pow 2)).add (hi.const_mul 2)
  have hT : Tendsto T atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log n ^ 2 + 2 / Real.log n)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      dsimp [T]
      exact div_nonneg (mul_nonneg (mul_nonneg hn0.le (sub_nonneg.mpr hmono)) (by linarith)) (sq_nonneg _)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      have hbd : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (n : ℝ) + 1) hn0)
        rw [Real.log_div (by positivity) hn0.ne', show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at h
        have h' := (le_div_iff₀ hn0).mp h
        nlinarith
      dsimp [T]
      calc
        _ ≤ (Real.log ((n : ℝ) + 1) + Real.log n) / Real.log n ^ 2 := by
          exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (by linarith) hbd) (by positivity)
        _ = _ := by field_simp; ring
    · exact hb
  have hd : Tendsto (fun n => d n / g n) atTop (nhds 1) := by
    have hh : Tendsto (fun n => 1 - T n) atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hT
    norm_num only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    have hl1 : Real.log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    dsimp [d, g, F, T]
    push_cast
    field_simp
    <;> ring
  have herr : (fun n => d n - g n) =o[atTop] g := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · have hh : Tendsto (fun n => d n / g n - 1) atTop (nhds (1 - 1)) := hd.sub tendsto_const_nhds
      norm_num only [sub_self] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hg : g n ≠ 0 := by
        dsimp [g]
        exact one_div_ne_zero (pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne')
      dsimp [d]
      field_simp
      <;> ring
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hg : g n ≠ 0 := by
        dsimp [g]
        exact one_div_ne_zero (pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne')
      exact fun h => (hg h).elim
  have hsum (N : ℕ) : (∑ i ∈ range N, g i) = Jn N 0 := by
    rw [Jn_zero_eq_sum]
    have hshift : (∑ i ∈ range N, g i) = ∑ a ∈ Ico 1 (N + 1), 1 / Real.log a ^ 2 := by
      simpa only [g, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm] using
        (sum_Ico_eq_sum_range (fun a : ℕ => 1 / Real.log a ^ 2) 1 (N + 1)).symm
    rw [hshift]
    by_cases hN : N = 0
    · subst N; simp
    have hset : Ico 1 (N + 1) = insert 1 (Ioc 1 N) := by ext a; simp; omega
    rw [hset, sum_insert (by simp)]
    simp
  have hdiv0 : Tendsto (fun n : ℕ => Real.log n ^ 2 / ((n : ℝ) - 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, sub_eq_add_neg] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hdivpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n ^ 2 / ((n : ℝ) - 1) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hbig : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / Real.log n ^ 2) atTop atTop := by
    have hh := (tendsto_nhdsWithin_iff.mpr ⟨hdiv0, hdivpos⟩).inv_tendsto_nhdsGT_zero
    change Tendsto (fun n : ℕ => (Real.log n ^ 2 / ((n : ℝ) - 1))⁻¹) atTop atTop at hh
    simpa only [inv_div] using hh
  have hsumtop : Tendsto (fun N => ∑ i ∈ range N, g i) atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hbig
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [hsum]
    exact J0_lower hN
  have hsmall := (herr.sum_range (by intro n; dsimp [g]; positivity) hsumtop).tendsto_div_nhds_zero
  have hratio : Tendsto (fun N => F N / Jn N 0) atTop (nhds 1) := by
    have hh : Tendsto (fun N => (∑ i ∈ range N, (d i - g i)) / (∑ i ∈ range N, g i) + 1) atTop (nhds (0 + 1)) := hsmall.add tendsto_const_nhds
    norm_num only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [sum_sub_distrib, show (∑ i ∈ range N, d i) = F N - F 0 from sum_range_sub F N, hsum] 
    have hJ : Jn N 0 ≠ 0 := by
      have h := J0_lower hN
      have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
      have hl : 0 < Real.log (N : ℝ) := Real.log_pos hN1
      exact ne_of_gt (lt_of_lt_of_le (by positivity) h)
    have hf0 : F 0 = 0 := by simp [F]
    rw [hf0, sub_zero]
    field_simp
    <;> ring
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [F] using hinv

/-- LEAF. Unit U-1532. The geometric sum bound `|Σ_{m ≤ x} e(mβ)| ≤ 1/(2‖β‖)` for `β` not an
integer, `‖β‖` the distance to the nearest integer; p. 130, the estimate of `T(β)`. -/
theorem norm_geom_sum_le (x : ℕ) {β : ℝ} (hβ : Int.fract β ≠ 0) :
    ‖∑ m ∈ Icc 1 x, eC (m * β)‖ ≤ 1 / (2 * min (Int.fract β) (1 - Int.fract β)) := by
  simp_rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
  have hd : dist0 β = min (Int.fract β) (1 - Int.fract β) := abs_sub_round_eq_min β
  have hp : 0 < dist0 β := by
    rw [hd, lt_min_iff]
    exact ⟨lt_of_le_of_ne (Int.fract_nonneg β) (Ne.symm hβ), sub_pos.mpr (Int.fract_lt_one β)⟩
  have heq : (∑ m ∈ Icc 1 x, LeanLab.PNTPort.LargeSieve.e (m * β)) = LeanLab.PNTPort.LargeSieve.e β * ∑ m ∈ range x, LeanLab.PNTPort.LargeSieve.e (m * β) := by
    rw [show Icc 1 x = Ico 1 (x + 1) by ext k; simp]
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sum]
    apply sum_congr rfl
    intro m _
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [heq, norm_mul, norm_e, one_mul, ← hd]
  exact norm_geom_le x hp

/-- The weaker lab coefficient alone does not imply the sharp coefficient on p.131. -/
theorem weaker_large_sieve_constant_insufficient (N Q : ℕ) (hQ : 0 < Q) :
    ∃ B : ℝ, B ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2 ∧ (N : ℝ) + (Q : ℝ) ^ 2 < B := by
  refine ⟨(N : ℝ) + 2 * (Q : ℝ) ^ 2, le_rfl, ?_⟩
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := lt_add_of_pos_right ((N : ℝ) + (Q : ℝ) ^ 2) (sq_pos_of_pos hq)
  convert h using 1 <;> ring

/-- The modulus one case of the large sieve input on p.131, by Cauchy Schwarz. -/
theorem large_sieve_level_one (a : ℕ → ℂ) (M N : ℕ) :
    ∑ q ∈ Icc (1 : ℕ) 1, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + 1) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  have hchars : (univ : Finset (DirichletCharacter ℂ 1)) = {1} := by
    ext χ
    simp only [mem_univ, mem_singleton, true_iff]
    exact DirichletCharacter.level_one χ
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  simp only [Icc_self, sum_singleton, Nat.cast_one, Nat.totient_one, div_one, one_mul]
  rw [hchars]
  simp only [filter_singleton, DirichletCharacter.isPrimitive_one_level_one, ite_true, sum_singleton,
    hone, mul_one]
  have hnorm : ‖∑ n ∈ Ioc M (M + N), a n‖ ^ 2 ≤ (∑ n ∈ Ioc M (M + N), ‖a n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Ioc M (M + N)) (f := fun n => ‖a n‖)
  have hc' : (∑ n ∈ Ioc M (M + N), ‖a n‖) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by simpa using hc
  exact (hnorm.trans hc').trans (mul_le_mul_of_nonneg_right (by linarith) (sum_nonneg fun _ _ => sq_nonneg _))

/-- Gallagher p.131 character orthogonality reduces the multiplicative sieve to additive sums. -/
theorem primitive_sieve_le_additive (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), (starRingEnd ℂ) (a n) * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 := by
  classical
  apply sum_le_sum
  intro q hq
  letI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  let I : Finset ℤ := (Ioc M (M + N)).map emb
  let az : ℤ → ℂ := fun z => a z.toNat
  have h := LeanLab.PNTPort.LargeSieve.prim_chars_le I az (q := q)
  simpa only [I, az, sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast, Int.cast_ofNat] using h

/-- At real part at least one a primitive character has no zeros. This closes the endpoint
of the p.131 density estimate. -/
theorem zeroCount_eq_zero_of_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) : zeroCount χ σ T = 0 := by
  have hne (ρ : ℂ) (hρ : σ ≤ ρ.re) : χ.LFunction ρ ≠ 0 := by
    by_cases hχ : χ = 1
    · have hq : q = 1 := by
        have hh := hp
        rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at hh
        exact hh.symm
      subst q
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re (hσ.trans hρ)
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (hσ.trans hρ)
  have he : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} = ∅ := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, hβ, ht⟩
    exact hne ρ hβ hz
  simp only [zeroCount, he, Set.ncard_empty]

/-- The primitive family count vanishes at the sigma one endpoint of p.131. -/
theorem density_sum_at_one (T : ℝ) :
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ 1 T : ℝ) = 0 := by
  classical
  apply sum_eq_zero
  intro q hq
  apply sum_eq_zero
  intro χ hχ
  rw [zeroCount_eq_zero_of_one_le χ (mem_filter.mp hχ).2 le_rfl, Nat.cast_zero]

/-- Gallagher 1975 p.131. Auxiliary exact diagonal and off-diagonal Fourier energy identity. -/
theorem fourier_energy_split {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : Finset ℤ) (α : ι → ℝ) (b : ι → ℂ) :
    ∑ n ∈ t, ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 =
      (t.card : ℝ) * ∑ r ∈ s, ‖b r‖ ^ 2 +
      ∑ r ∈ s, ∑ r' ∈ s.erase r,
        (b r * (starRingEnd ℂ) (b r') *
          ∑ n ∈ t, LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
  classical
  have hn (n : ℤ) : ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 =
      ∑ r ∈ s, ∑ r' ∈ s, (b r * (starRingEnd ℂ) (b r') *
        LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
    have h := congrArg Complex.re (LeanLab.PNTPort.LargeSieve.normSq_dualSum s α b n)
    simpa only [LeanLab.PNTPort.LargeSieve.dualSum, Complex.ofReal_re, Complex.re_sum] using h
  simp_rw [hn]
  rw [sum_comm]
  have hr (r : ι) (hr : r ∈ s) :
      (∑ n ∈ t, ∑ r' ∈ s,
        (b r * (starRingEnd ℂ) (b r') *
          LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re) =
      (t.card : ℝ) * ‖b r‖ ^ 2 + ∑ r' ∈ s.erase r,
        (b r * (starRingEnd ℂ) (b r') *
          ∑ n ∈ t, LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
    rw [sum_comm]
    rw [← sum_erase_add _ _ hr]
    simp only [sub_self, mul_zero, LeanLab.PNTPort.LargeSieve.e_zero, mul_one,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, sum_const, nsmul_eq_mul]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro r' hr'
    rw [mul_sum, Complex.re_sum]
  rw [sum_congr rfl hr, sum_add_distrib, mul_sum]

/-- Montgomery and Vaughan 1974 pp.73 to 82. Auxiliary normalization of the circular kernel. -/
theorem circular_kernel_eq_cosecant (θ : ℝ) :
    LeanLab.PNTPort.LargeSieve.e (θ / 2) /
        (LeanLab.PNTPort.LargeSieve.e θ - 1) =
      1 / (2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
  have hx : LeanLab.PNTPort.LargeSieve.e θ =
      LeanLab.PNTPort.LargeSieve.e (θ / 2) ^ 2 := by
    rw [pow_two, ← e_add]
    congr 1
    ring
  have he : LeanLab.PNTPort.LargeSieve.e (θ / 2) ≠ 0 :=
    Complex.exp_ne_zero _
  have hs : LeanLab.PNTPort.LargeSieve.e (θ / 2) -
      (LeanLab.PNTPort.LargeSieve.e (θ / 2))⁻¹ =
      2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    have harg : Complex.I * ((2 * Real.pi * (θ / 2) : ℝ) : ℂ) =
        (Real.pi * θ : ℂ) * Complex.I := by push_cast; ring
    simp only [harg]
    rw [← Complex.exp_neg]
    rw [show -((Real.pi * θ : ℂ) * Complex.I) =
      (-((Real.pi * θ : ℂ))) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_mul, ← Complex.ofReal_sin]
    ring
  have hd : LeanLab.PNTPort.LargeSieve.e θ - 1 =
      LeanLab.PNTPort.LargeSieve.e (θ / 2) *
        (2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
    rw [← hs, mul_sub, mul_inv_cancel₀ he, ← pow_two, ← hx]
  rw [hd, div_mul_eq_div_div, div_self he]

/-- Gallagher 1975 p.131. Auxiliary absolute bound for the normalized circular kernel. -/
theorem circular_kernel_norm_le {θ δ : ℝ} (hδ : 0 < δ) (hθ : δ ≤ dist0 θ) :
    ‖LeanLab.PNTPort.LargeSieve.e (θ / 2) /
      (LeanLab.PNTPort.LargeSieve.e θ - 1)‖ ≤ 1 / (4 * δ) := by
  rw [norm_div, norm_e]
  apply one_div_le_one_div_of_le (by positivity)
  exact (mul_le_mul_of_nonneg_left hθ (by norm_num)).trans
    (LeanLab.PNTPort.LargeSieve.four_dist0_le θ)


/-- Gallagher 1975 p.131. The circular Hilbert constant for at most three spaced points
follows from the absolute kernel estimate and the proved symmetric Schur inequality. -/
theorem circular_hilbert_small_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ) (hcard : s.card ≤ 3) (b : ι → ℂ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  classical
  let K : ι → ι → ℝ := fun r r' => if r = r' then 0 else 1 / (4 * δ)
  have hK0 : ∀ r r', 0 ≤ K r r' := by intro r r'; dsimp [K]; split_ifs <;> positivity
  have hKsym : ∀ r r', K r r' = K r' r := by
    intro r r'
    simp only [K]
    split_ifs <;> simp_all
  have hrow (r : ι) (hr : r ∈ s) : ∑ r' ∈ s, K r r' ≤ 1 / (2 * δ) := by
    rw [← sum_erase_add _ _ hr]
    have he : ∑ r' ∈ s.erase r, K r r' = ((s.erase r).card : ℝ) * (1 / (4 * δ)) := by
      calc
        _ = ∑ _r' ∈ s.erase r, (1 / (4 * δ)) := by
          apply sum_congr rfl
          intro r' hr'
          exact if_neg (mem_erase.mp hr').1.symm
        _ = _ := by simp
    rw [he]
    simp only [K, if_pos rfl, add_zero]
    have hc : ((s.erase r).card : ℝ) ≤ 2 := by
      have hh := card_erase_of_mem hr
      exact_mod_cast (by omega : (s.erase r).card ≤ 2)
    calc
      _ ≤ 2 * (1 / (4 * δ)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hnorm : ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      ∑ r ∈ s, ∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * K r r' := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro r hr
    apply (norm_sum_le _ _).trans
    have heq : (∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * K r r') =
        ∑ r' ∈ s.erase r, ‖b r‖ * ‖b r'‖ * K r r' := by
      rw [← sum_erase_add _ _ hr]
      simp [K]
    rw [heq]
    apply sum_le_sum
    intro r' hr'
    rw [norm_mul, norm_mul, Complex.norm_conj]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change _ ≤ if r = r' then 0 else 1 / (4 * δ)
    rw [if_neg (mem_erase.mp hr').1.symm]
    exact circular_kernel_norm_le hδ (hs r hr r' (mem_erase.mp hr').2 (mem_erase.mp hr').1.symm)
  calc
    _ ≤ _ := hnorm
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * ∑ r' ∈ s, K r r' :=
      LeanLab.PNTPort.LargeSieve.sum_sum_mul_le s (fun r => ‖b r‖) K hK0 hKsym
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * (1 / (2 * δ)) :=
      sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hrow r hr) (sq_nonneg _))
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Gallagher 1975 p.131. Auxiliary endpoint form of the finite geometric kernel. -/
theorem geometric_kernel_endpoints (M : ℤ) (N : ℕ) {θ : ℝ}
    (hθ : 0 < dist0 θ) :
    ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * θ) =
      (LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + N + 1 / 2) * θ) -
        LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 / 2) * θ)) *
        (LeanLab.PNTPort.LargeSieve.e (θ / 2) /
          (LeanLab.PNTPort.LargeSieve.e θ - 1)) := by
  have hpos : 0 < ‖LeanLab.PNTPort.LargeSieve.e θ - 1‖ :=
    lt_of_lt_of_le (by linarith) (LeanLab.PNTPort.LargeSieve.four_dist0_le θ)
  have hne : LeanLab.PNTPort.LargeSieve.e θ ≠ 1 := by
    intro h
    simp [h] at hpos
  have hk : (∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * θ)) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) *
        ∑ k ∈ range N, LeanLab.PNTPort.LargeSieve.e (k * θ) := by
    rw [Int.Ioc_eq_finset_map, sum_map]
    simp only [add_sub_cancel_left, Int.toNat_natCast, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [← e_add]
    congr 1
    push_cast
    ring
  have he1 : LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + N + 1 / 2) * θ) *
        LeanLab.PNTPort.LargeSieve.e (θ / 2) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) *
        LeanLab.PNTPort.LargeSieve.e (N * θ) := by
    rw [← e_add, ← e_add]
    congr 1
    ring
  have he0 : LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 / 2) * θ) *
        LeanLab.PNTPort.LargeSieve.e (θ / 2) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) := by
    rw [← e_add]
    congr 1
    ring
  rw [hk]
  simp_rw [LeanLab.PNTPort.LargeSieve.e_nat_mul]
  rw [geom_sum_eq hne]
  simp only [← mul_div_assoc, sub_mul, mul_sub, mul_one]
  rw [← LeanLab.PNTPort.LargeSieve.e_nat_mul, he1, he0]

/-- Gallagher 1975 p.131. The circular Hilbert bound controls both endpoints of the
geometric kernel. CONDITIONAL ON the supplied circular Hilbert bound. -/
theorem offdiagonal_bound_of_hilbert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (hh : ∀ v : ι → ℂ,
      ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        v r * (starRingEnd ℂ) (v r') *
          (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
            (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
        (1 / (2 * δ)) * ∑ r ∈ s, ‖v r‖ ^ 2)
    (b : ι → ℂ) (M : ℤ) (N : ℕ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N),
          LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  classical
  let H : (ι → ℂ) → ℂ := fun v => ∑ r ∈ s, ∑ r' ∈ s.erase r,
    v r * (starRingEnd ℂ) (v r') *
      (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
        (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))
  let v : ℝ → ι → ℂ := fun u r => b r * LeanLab.PNTPort.LargeSieve.e (u * α r)
  have hphase (u : ℝ) (r r' : ι) :
      v u r * (starRingEnd ℂ) (v u r') = b r * (starRingEnd ℂ) (b r') *
        LeanLab.PNTPort.LargeSieve.e (u * (α r - α r')) := by
    simp only [v, map_mul, ← LeanLab.PNTPort.LargeSieve.e_neg]
    rw [show u * (α r - α r') = u * α r + -(u * α r') by ring, e_add]
    ring
  have henergy (u : ℝ) : ∑ r ∈ s, ‖v u r‖ ^ 2 = ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simp only [v, norm_mul, norm_e, mul_one]
  have hH (u : ℝ) : ‖H (v u)‖ ≤ (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [henergy] using hh (v u)
  have heq : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))) =
      H (v ((M : ℝ) + N + 1 / 2)) - H (v ((M : ℝ) + 1 / 2)) := by
    simp only [H, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro r' hr'
    have hθ : 0 < dist0 (α r - α r') :=
      hδ.trans_le (hs r hr r' (mem_erase.mp hr').2 (mem_erase.mp hr').1.symm)
    rw [geometric_kernel_endpoints M N hθ, hphase, hphase]
    ring
  rw [heq]
  calc
    _ ≤ ‖H (v ((M : ℝ) + N + 1 / 2))‖ + ‖H (v ((M : ℝ) + 1 / 2))‖ := norm_sub_le _ _
    _ ≤ (1 / (2 * δ)) * (∑ r ∈ s, ‖b r‖ ^ 2) +
        (1 / (2 * δ)) * (∑ r ∈ s, ‖b r‖ ^ 2) := add_le_add (hH _) (hH _)
    _ = _ := by ring

/-- Montgomery and Vaughan 1974 pp.73 to 82. The classical cosecant estimate gives the
normalized circular estimate with its exact factor one half. CONDITIONAL ON the supplied
cosecant estimate. Gallagher 1975 p.131 uses the resulting sampling bound. -/
theorem circular_hilbert_of_cosecant {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (b : ι → ℂ)
    (hh : ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        b r * (starRingEnd ℂ) (b r') /
          (Real.sin (Real.pi * (α r - α r')) : ℂ)‖ ≤
        (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have he : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))) =
      (1 / (2 * Complex.I)) * ∑ r ∈ s, ∑ r' ∈ s.erase r,
        b r * (starRingEnd ℂ) (b r') /
          (Real.sin (Real.pi * (α r - α r')) : ℂ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]
    apply sum_congr rfl
    intro r' hr'
    rw [circular_kernel_eq_cosecant]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hc : ‖(1 : ℂ) / (2 * Complex.I)‖ = 1 / 2 := by
    norm_num [norm_div, norm_mul]
  rw [he, norm_mul, hc]
  calc
    _ ≤ (1 / 2) * ((1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.131. Exact finite duality preserves the sharp constant.
CONDITIONAL ON the supplied circular Hilbert bound. -/
theorem spaced_sampling_of_hilbert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (hh : ∀ v : ι → ℂ,
      ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        v r * (starRingEnd ℂ) (v r') *
          (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
            (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
        (1 / (2 * δ)) * ∑ r ∈ s, ‖v r‖ ^ 2)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + 1 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  apply LeanLab.RieselVaughan1983.LargeSieveSchur.primal_of_dual (by positivity) M N
  intro b
  change (∑ n ∈ Ioc M (M + N),
    ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2) ≤ _
  rw [fourier_energy_split]
  have hcard : (Ioc M (M + (N : ℤ))).card = N :=
    LeanLab.RieselVaughan1983.LargeSieveSchur.card_Ioc_eq M N
  rw [hcard]
  have hre : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      (b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re) ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [Complex.re_sum] using
      (Complex.re_le_norm _).trans (offdiagonal_bound_of_hilbert s α hδ hs hh b M N)
  calc
    _ ≤ (N : ℝ) * (∑ r ∈ s, ‖b r‖ ^ 2) + (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 :=
      add_le_add le_rfl hre
    _ = _ := by ring

/-- Gallagher 1975 p.131. Farey spacing turns the sharp dual constant into N plus Q squared.
CONDITIONAL ON the supplied circular Hilbert bound at the reduced fractions. -/
theorem farey_sampling_of_hilbert (a : ℕ → ℂ) (M N Q : ℕ)
    (hh : ∀ b : ℕ × ℕ → ℂ,
      ‖∑ r ∈ LeanLab.PNTPort.LargeSieve.farey Q,
        ∑ r' ∈ (LeanLab.PNTPort.LargeSieve.farey Q).erase r,
          b r * (starRingEnd ℂ) (b r') *
            (LeanLab.PNTPort.LargeSieve.e
                ((LeanLab.PNTPort.LargeSieve.fareyPt r - LeanLab.PNTPort.LargeSieve.fareyPt r') / 2) /
              (LeanLab.PNTPort.LargeSieve.e
                (LeanLab.PNTPort.LargeSieve.fareyPt r - LeanLab.PNTPort.LargeSieve.fareyPt r') - 1))‖ ≤
        (1 / (2 * (1 / (Q : ℝ) ^ 2))) *
          ∑ r ∈ LeanLab.PNTPort.LargeSieve.farey Q, ‖b r‖ ^ 2) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp only [show Icc 1 (0 : ℕ) = ∅ by decide, sum_empty,
      Nat.cast_zero, zero_pow, add_zero]
    positivity
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  have hI : Ioc (M : ℤ) ((M : ℤ) + N) = (Ioc M (M + N)).map emb := by
    ext z
    simp only [Finset.mem_Ioc, Finset.mem_map, emb, Function.Embedding.coeFn_mk, Int.ofNat_eq_natCast]
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨z.toNat, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
      constructor <;> omega
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hbound := spaced_sampling_of_hilbert
    (LeanLab.PNTPort.LargeSieve.farey Q) LeanLab.PNTPort.LargeSieve.fareyPt
    hδ (LeanLab.PNTPort.LargeSieve.farey_spaced Q)
    hh
    (fun z : ℤ => a z.toNat) (M : ℤ) N
  rw [hI] at hbound
  simp only [sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast] at hbound
  have hconst : (1 : ℝ) / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by simp
  rw [hconst] at hbound
  rw [LeanLab.PNTPort.LargeSieve.farey_sum_eq] at hbound
  simpa only [LeanLab.PNTPort.LargeSieve.U, LeanLab.PNTPort.LargeSieve.fareyPt,
    Nat.coprime_comm] using hbound

/-- LEAF. Montgomery and Vaughan, Hilbert's inequality, 1974 pp.73 to 82.
The classical circular cosecant inequality for separated points is the remaining input.
The family size is at least four because smaller families are proved by the Schur estimate.
The quotient normalization, geometric endpoints, duality and Farey constant are separate.
This supplies the sharp sampling input behind Gallagher 1975 p.131 display 14. -/
theorem cosecant_hilbert_large_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ) (hcard : 4 ≤ s.card) (b : ι → ℂ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') /
        (Real.sin (Real.pi * (α r - α r')) : ℂ)‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  exact LeanLab.Linnik.HilbertCosecant.cosecant_hilbert s α hδ hs b

/-- Gallagher 1975 p.131. The circular Hilbert bound is proved for small families and is
CONDITIONAL ON cosecant_hilbert_large_family for every larger family. -/
theorem circular_hilbert_sharp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ) (b : ι → ℂ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  by_cases hc : s.card ≤ 3
  · exact circular_hilbert_small_family s α hδ hs hc b
  · exact circular_hilbert_of_cosecant s α hδ b
      (cosecant_hilbert_large_family s α hδ hs (by omega) b)

/-- Gallagher 1975 p.131. The general separated sampling estimate now has no supplied
Hilbert hypothesis. The additive interval coefficient is N plus reciprocal delta. -/
theorem spaced_sampling {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + 1 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  exact spaced_sampling_of_hilbert s α hδ hs
    (fun v => circular_hilbert_sharp s α hδ hs v) a M N

/-- LEAF. Montgomery 1971, Topics in multiplicative number theory, sharp additive large sieve.
Gallagher 1975 p.131, the input behind display 14. Only the sharp Fourier sampling bound
remains here. Primitive character orthogonality is proved separately. -/
theorem additive_large_sieve_sharp (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  apply farey_sampling_of_hilbert a M N Q
  intro b
  by_cases hQ : Q = 0
  · subst Q
    simp [LeanLab.PNTPort.LargeSieve.farey]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  exact circular_hilbert_sharp (LeanLab.PNTPort.LargeSieve.farey Q)
    LeanLab.PNTPort.LargeSieve.fareyPt hδ
    (LeanLab.PNTPort.LargeSieve.farey_spaced Q) b

/-- LEAF. Unit U-1532. The multiplicative large sieve over primitive characters,
`Σ_{q ≤ Q} q/φ(q) Σ*_χ |Σ_{M < n ≤ M+N} a_n χ(n)|² ≤ (N + Q²) Σ |a_n|²`, the input behind the
bound for `E` in display (14) p. 131 and behind the density estimate below. -/
theorem large_sieve (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  calc
    _ ≤ _ := primitive_sieve_le_additive a M N Q
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Ioc M (M + N), ‖(starRingEnd ℂ) (a n)‖ ^ 2 :=
      additive_large_sieve_sharp (fun n => (starRingEnd ℂ) (a n)) M N Q
    _ = _ := by simp only [Complex.norm_conj]

/-- The logarithm in the existing zero free region is bounded uniformly in the paper box. -/
theorem log_Bt_le_log_height : ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} [NeZero q] {T t : ℝ},
    2 ≤ T → (q : ℝ) ≤ T → |t| ≤ T → Real.log (Bt q t) ≤ K * Real.log T := by
  let A := Real.log (6 * Z)
  let K := A / Real.log 2 + 2
  have hZ := one_le_Z
  have hA : 0 ≤ A := Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro q _ T t hT hq ht
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hBt : Bt q t ≤ (6 * Z) * T ^ 2 := by
    unfold Bt
    have h1 := mul_le_mul hq (show |t| + 3 ≤ 3 * T by linarith) (by positivity) hT0.le
    nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ Z by linarith)]
  calc
    Real.log (Bt q t) ≤ Real.log ((6 * Z) * T ^ 2) :=
      Real.log_le_log (by unfold Bt; positivity) hBt
    _ = A + 2 * Real.log T := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num [A]
    _ ≤ K * Real.log T := by
      have hmul : A ≤ A / Real.log 2 * Real.log T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hlog hA
      dsimp [K]
      nlinarith

/-- The nonprincipal part of the exceptional zero reality assertion on p.127. -/
theorem height_box_real_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ {T : ℝ}, 2 ≤ T → (q : ℝ) ≤ T →
    ∀ ρ : ℂ, χ.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      χ ^ 2 = 1 ∧ ρ.im = 0 := by
  obtain ⟨K, hK, hlog⟩ := log_Bt_le_log_height
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  refine ⟨c / (2 * K), by positivity, ?_⟩
  intro q _ χ hχ T hT hq ρ hz hβ ht
  rcases (hreg q χ hχ).1 ρ hz with hleft | hright
  · have hlT : 0 < Real.log T := Real.log_pos (by linarith)
    have hlB : 0 < Real.log (Bt q ρ.im) := by linarith [one_le_log_Bt (N := q) ρ.im]
    have hd : c / (K * Real.log T) ≤ c / Real.log (Bt q ρ.im) :=
      div_le_div_of_nonneg_left hc.le hlB (hlog hT hq ht)
    have hpos : 0 < c / (2 * K) / Real.log T := by positivity
    have heq : c / (K * Real.log T) = 2 * (c / (2 * K) / Real.log T) := by field_simp
    rw [heq] at hd
    linarith
  · exact ⟨hright.2.2.1, hright.2.2.2⟩

/-- The principal primitive character has no zero in a uniform p.127 box. -/
theorem zeta_height_box_nonzero : ∃ b : ℝ, 0 < b ∧ ∀ {T : ℝ}, 2 ≤ T →
    ∀ ρ : ℂ, 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T → riemannZeta ρ ≠ 0 := by
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  obtain ⟨σ, hσ, hsmall⟩ := ZetaNoZerosInBox 3
  let b := min A ((1 - σ) * Real.log 2)
  have hb : 0 < b := lt_min hA.1 (mul_pos (by linarith) (Real.log_pos (by norm_num)))
  refine ⟨b, hb, ?_⟩
  intro T hT ρ hβ ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hrep : (ρ.re : ℂ) + ρ.im * Complex.I = ρ := by simp
  by_cases h1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  by_cases ht3 : |ρ.im| ≤ 3
  · have hcmp : b / Real.log T ≤ 1 - σ := by
      apply (div_le_iff₀ hlT).mpr
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
      have hmin : b ≤ (1 - σ) * Real.log 2 := min_le_right _ _
      nlinarith
    simpa only [hrep] using hsmall ρ.im ht3 ρ.re (by linarith)
  · have ht3' : 3 < |ρ.im| := lt_of_not_ge ht3
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hcomp : b / Real.log T ≤ A / Real.log |ρ.im| := by
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hlT.le).trans
        (div_le_div_of_nonneg_left hA.1.le hlogt (Real.log_le_log (by positivity) ht))
    have hh := hlarge ρ.re ρ.im ht3' ⟨by simpa only [Real.rpow_one] using (show 1 - A / Real.log |ρ.im| ≤ ρ.re by linarith), lt_of_not_ge h1⟩
    simpa only [hrep] using hh

/-- Equality of primitive characters follows from equality at a common multiple. -/
theorem primitive_sigma_eq_of_lift_eq {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ (q₁ + 1)) (χ₂ : DirichletCharacter ℂ (q₂ + 1))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (he : DirichletCharacter.changeLevel (Nat.dvd_mul_right (q₁ + 1) (q₂ + 1)) χ₁ =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left (q₂ + 1) (q₁ + 1)) χ₂) :
    (⟨q₁, χ₁⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q₂, χ₂⟩ := by
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    h₁, h₂] at hc
  have hq : q₁ = q₂ := by omega
  subst q₂
  have hχ := DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right (q₁ + 1) (q₁ + 1)) he
  subst χ₂
  rfl

/-- Narrowing the zero strip preserves membership in the exceptional family. -/
theorem excSet_mono {b₁ b₂ T : ℝ} (hb : b₁ ≤ b₂) (hT : 2 ≤ T) :
    excSet b₁ T ⊆ excSet b₂ T := by
  rintro x ⟨hq, hp, ρ, hz, hβ, ht⟩
  refine ⟨hq, hp, ρ, hz, ?_, ht⟩
  have hdiv := div_le_div_of_nonneg_right hb (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
  linarith

/-- No primitive principal character occurs in the uniform zero strip on p.127. -/
theorem excSet_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ x ∈ excSet b T, x.2 ≠ 1 := by
  obtain ⟨b, hb, hz⟩ := zeta_height_box_nonzero
  refine ⟨b, hb, ?_⟩
  intro T hT x hx he
  have hc := hx.2.1
  rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hc
  have hq : x.1 = 0 := by omega
  obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
  have hzeta : riemannZeta ρ = 0 := by
    rcases x with ⟨q, χ⟩
    dsimp at hq
    subst q
    simpa only [he, DirichletCharacter.LFunction_modOne_eq] using hρ
  exact hz hT ρ hβ ht hzeta


/-- LEAF. Unit U-1532. The exceptional zero is real and its character is real, p. 127: for
small `b > 0`, any zero in `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T` of `L(s, χ)`, `χ` primitive of
conductor at most `T`, has `Im ρ = 0`, and `χ² = 1`. -/
theorem page_real : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    x.2 ^ 2 = 1 ∧ ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      ρ.im = 0 := by
  obtain ⟨bn, hbn, hn⟩ := height_box_real_nonprincipal
  obtain ⟨bz, hbz, hz⟩ := zeta_height_box_nonzero
  let b := min bn bz
  refine ⟨b, lt_min hbn hbz, ?_⟩
  intro T hT x hx
  have hq : ((x.1 + 1 : ℕ) : ℝ) ≤ T := by simpa using hx.1
  have hprim := hx.2.1
  have hχ : x.2 ≠ 1 := by
    intro he
    have hlev : x.1 + 1 = 1 := by
      have hc := hprim
      rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
    have hzeta : riemannZeta ρ = 0 := by
      have hxp : x.1 = 0 := by omega
      rcases x with ⟨q, χ⟩
      dsimp at hxp
      subst q
      simpa only [he, DirichletCharacter.LFunction_modOne_eq] using hρ
    have hβz : 1 - bz / Real.log T ≤ ρ.re := by
      have hcmp := div_le_div_of_nonneg_right (min_le_right bn bz) (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
      linarith
    exact hz hT ρ hβz ht hzeta
  have hmono (ρ : ℂ) (hβ : 1 - b / Real.log T ≤ ρ.re) : 1 - bn / Real.log T ≤ ρ.re := by
    have hcmp := div_le_div_of_nonneg_right (min_le_left bn bz) (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
  refine ⟨(hn x.2 hχ hT hq ρ hρ (hmono ρ hβ) ht).1, ?_⟩
  intro ρ hρ hβ ht
  exact (hn x.2 hχ hT hq ρ hρ (hmono ρ hβ) ht).2

/-- The finite Fourier identity before the order split in Lemma 6 on pp.134 and 135. -/
theorem ramanujan_tuple_sum_eq (q k L : ℕ) :
    ∑ x : pairs k L, ramanujanSum q (dif x) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ((‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) := by
  classical
  unfold ramanujanSum
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hp : Gs L ((a : ℝ) / q) ^ k =
      ∑ ν : Fin k → Fin L, eC (sv ν * ((a : ℝ) / q)) :=
    LeanLab.Linnik.U1434Lemma21.Gs_pow k L _
  have hc (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
    simpa only [LeanLab.Linnik.U1434Lemma21.e_eq_eC] using
      (LeanLab.PNTPort.LargeSieve.e_neg x).symm
  have hn : ((‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) =
      Gs L ((a : ℝ) / q) ^ k * (starRingEnd ℂ) (Gs L ((a : ℝ) / q) ^ k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  rw [hn, hp, map_sum, sum_mul_sum, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro ν hν
  apply sum_congr rfl
  intro mu hmu
  rw [hc, ← LeanLab.Linnik.U1434Lemma21.eC_add]
  congr 1
  simp only [dif, Int.cast_sub, Int.cast_natCast]
  ring

/-- The q one main term in the finite expansion of Lemma 6. -/
theorem ramanujan_tuple_sum_one (k L : ℕ) :
    ∑ x : pairs k L, ramanujanSum 1 (dif x) = (L : ℂ) ^ (2 * k) := by
  have hR (n : ℤ) : ramanujanSum 1 n = 1 := by simp [ramanujanSum, eC]
  simp only [hR, sum_const, nsmul_eq_mul, mul_one]
  simp [pairs, Fintype.card_prod, ← pow_add, two_mul]

/-- The justified finite sum and singular series exchange at the start of Lemma 6. -/
theorem offdiag_singSeries_eq_tsum (k L : ℕ) :
    ∑ x : pairs k L with dif x ≠ 0, singSeries (dif x) =
      ∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x) := by
  classical
  have hs : ∀ x ∈ (univ : Finset (pairs k L)).filter (fun x => dif x ≠ 0),
      Summable (fun q : ℕ => ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 /
        (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)) := by
    intro x hx
    exact summable_singSeries (mem_filter.mp hx).2
  simp only [singSeries]
  rw [← Summable.tsum_finsetSum hs]
  apply tsum_congr
  intro q
  exact (mul_sum _ _ _).symm

/-- The zero frequency Ramanujan coefficient removed on p.134. -/
theorem ramanujanSum_zero (q : ℕ) : ramanujanSum q 0 = (q.totient : ℂ) := by
  simp [ramanujanSum, eC, Nat.totient, Nat.coprime_comm]

/-- The square root order series used in Lemma 10 on p.137 is uniformly bounded. -/
theorem half_order_totient_weight_le (S : Finset ℕ) :
    ∑ q ∈ S with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q)) ≤ 16 * Real.log 2 * Real.exp 27 := by
  classical
  have hpoint (q : ℕ) (hq : q ∈ S.filter Odd) :
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q)) ≤ LeanLab.Romanov.halfOrderTerm q := by
    have ho := (mem_filter.mp hq).2
    by_cases hs : Squarefree q
    · rw [LeanLab.Romanov.halfOrderTerm, ite_eq_left (show LeanLab.LPZ2007.OddSqf q from ⟨ho, hs⟩)]
      rw [div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right
        (LeanLab.Romanov.TotientWeights134.totientWeight_le_fd ⟨ho, hs⟩) (Real.sqrt_nonneg _)
    · simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, Int.cast_zero,
        zero_pow (by decide : 2 ≠ 0), zero_div]
      exact LeanLab.Romanov.halfOrderTerm_nonneg q
  exact (sum_le_sum hpoint).trans
    ((LeanLab.Romanov.halfOrder_summable.sum_le_tsum _
      (fun q _ => LeanLab.Romanov.halfOrderTerm_nonneg q)).trans LeanLab.Romanov.halfOrder_tsum_le)

/-- The least common multiple order kernel in Lemma 10 on p.137 gains a square root order. -/
theorem lcm_order_weight_le {f : ℕ} (hf : Odd f) (S : Finset ℕ) :
    ∑ q ∈ S with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (q.totient : ℝ) / ordTwo (Nat.lcm f q) ≤
      (16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f) := by
  classical
  have hfpos : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hsf : 0 < Real.sqrt (ordTwo f) := Real.sqrt_pos.mpr hfpos
  have hpoint (q : ℕ) (hq : q ∈ S.filter Odd) :
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) / ordTwo (Nat.lcm f q) ≤
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := by
    have hqo := (mem_filter.mp hq).2
    have hlo : Odd (Nat.lcm f q) :=
      (hf.mul hqo).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right f q) (dvd_mul_left q f))
    have hlpos : (0 : ℝ) < ordTwo (Nat.lcm f q) :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hlo
    have hqpos : (0 : ℝ) < ordTwo q :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hqo
    have hsqp : 0 < Real.sqrt (ordTwo q) := Real.sqrt_pos.mpr hqpos
    have hfle : (ordTwo f : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast LeanLab.Linnik.Decomp1537a.xi_le_of_dvd hlo (Nat.dvd_lcm_left f q)
    have hqle : (ordTwo q : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast LeanLab.Linnik.Decomp1537a.xi_le_of_dvd hlo (Nat.dvd_lcm_right f q)
    have hsqrt : Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q) ≤ ordTwo (Nat.lcm f q) := by
      calc
        _ = Real.sqrt ((ordTwo f : ℝ) * ordTwo q) := (Real.sqrt_mul hfpos.le _).symm
        _ ≤ Real.sqrt ((ordTwo (Nat.lcm f q) : ℝ) * ordTwo (Nat.lcm f q)) :=
          Real.sqrt_le_sqrt (mul_le_mul hfle hqle hqpos.le hlpos.le)
        _ = _ := Real.sqrt_mul_self hlpos.le
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) by positivity)
      (mul_pos hsf hsqp) hsqrt
    convert hh using 1 <;> rw [div_mul_eq_div_div] <;> ring
  calc
    _ ≤ ∑ q ∈ S with Odd q,
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := sum_le_sum hpoint
    _ = (∑ q ∈ S with Odd q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (half_order_totient_weight_le S) hsf.le

/-- The first divisor reduction of Lemma 10 on p.137 with an explicit factor eight. -/
theorem exceptional_gcd_totient_le {r s : ℕ} (hs : 0 < s)
    (hr : r = s ∨ r = 4 * s ∨ r = 8 * s) (n : ℕ) :
    (Nat.gcd r n).totient ≤ 8 * ∑ f ∈ (Nat.gcd s n).divisors, f.totient := by
  rw [Nat.sum_totient]
  have hg : 0 < Nat.gcd s n := Nat.gcd_pos_of_pos_left n hs
  have hbound (d : ℕ) (hd : 0 < d) : Nat.gcd (d * s) n ≤ d * Nat.gcd s n := by
    apply Nat.le_of_dvd (Nat.mul_pos hd hg)
    have hdiv : Nat.gcd (d * s) n ∣ Nat.gcd (d * s) (d * n) :=
      Nat.gcd_dvd_gcd_of_dvd_right (d * s) (dvd_mul_left n d)
    rwa [Nat.gcd_mul_left] at hdiv
  have hφ := Nat.totient_le (Nat.gcd r n)
  rcases hr with hr | hr | hr
  · subst r; omega
  · subst r; have hh := hbound 4 (by decide); omega
  · subst r; exact hφ.trans (hbound 8 (by decide))

/-- The direct Lemma 8 bound leaves a conductor factor and no logarithmic decay. -/
theorem twisted_totient_crude : ∃ C : ℝ, ∀ k N r : ℕ,
    1 ≤ k → k ≤ N → 2 ≤ N → 0 < r →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * ((r : ℝ) / r.totient) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hC⟩ := LeanLab.Linnik.Decomp1532a.lemma8
  refine ⟨C, ?_⟩
  intro k N r hk hkN hN hr
  have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr
  have hfactor (n : ℕ) :
      (r : ℝ) * (Nat.gcd r n).totient / (r.totient : ℝ) ^ 2 ≤ (r : ℝ) / r.totient := by
    have hdiv := Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left r n)
    have hle : ((Nat.gcd r n).totient : ℝ) ≤ r.totient := by
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hr) hdiv
    calc
      _ ≤ (r : ℝ) * r.totient / (r.totient : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg r)) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
        ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) * ((r : ℝ) / r.totient) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hfactor _) (by positivity)
    _ = ((r : ℝ) / r.totient) *
        (∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
          ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ)) := by rw [← sum_mul]; ring
    _ ≤ ((r : ℝ) / r.totient) * (C * (Nat.log 2 N : ℝ) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left (hC k N hk hkN hN) (by positivity)
    _ = _ := by ring

/-- LEAF. Unit U-1532. Page's theorem, p. 127: there is `b > 0` such that for every `T ≥ 2` at
most one primitive character of conductor at most `T` has an L-function with a zero in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`. -/
theorem page_subsingleton : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → (excSet b T).Subsingleton := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨cl, hcl, hl⟩ := landau
  let b := min (min br bn) cl
  have hbr' : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbn' : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hcl' : b ≤ cl := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) hcl, ?_⟩
  intro T hT x hx y hy
  have hxbr := excSet_mono hbr' hT hx
  have hybr := excSet_mono hbr' hT hy
  have hxne := hn T hT x (excSet_mono hbn' hT hx)
  have hyne := hn T hT y (excSet_mono hbn' hT hy)
  obtain ⟨ρ₁, hz₁, hb₁, ht₁⟩ := hx.2.2
  obtain ⟨ρ₂, hz₂, hb₂, ht₂⟩ := hy.2.2
  have hβbr₁ : 1 - br / Real.log T ≤ ρ₁.re := by
    have hd := div_le_div_of_nonneg_right hbr' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have hβbr₂ : 1 - br / Real.log T ≤ ρ₂.re := by
    have hd := div_le_div_of_nonneg_right hbr' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him₁ := (hr T hT x hxbr).2 ρ₁ hz₁ hβbr₁ ht₁
  have him₂ := (hr T hT y hybr).2 ρ₂ hz₂ hβbr₂ ht₂
  have he₁ : (ρ₁.re : ℂ) = ρ₁ := by apply Complex.ext <;> simp [him₁]
  have he₂ : (ρ₂.re : ℂ) = ρ₂ := by apply Complex.ext <;> simp [him₂]
  have hzreal₁ : x.2.LFunction (ρ₁.re : ℂ) = 0 := by rwa [he₁]
  have hzreal₂ : y.2.LFunction (ρ₂.re : ℂ) = 0 := by rwa [he₂]
  have hbtop₁ : ρ₁.re ≤ 1 := by
    by_contra hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re x.2 (Or.inl hxne) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz₁
  have hbtop₂ : ρ₂.re ≤ 1 := by
    by_contra hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re y.2 (Or.inl hyne) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz₂
  have hQ : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT)
  have hxQ : x.1 + 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hx.1)
  have hyQ : y.1 + 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hy.1)
  have hlogQ : 0 < Real.log (⌊T⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  have hlogT : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊T⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hcmp : b / Real.log T ≤ cl / Real.log (⌊T⌋₊ : ℝ) :=
    (div_le_div_of_nonneg_right hcl' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)).trans
      (div_le_div_of_nonneg_left hcl.le hlogQ hlogT)
  have hlift := hl ⌊T⌋₊ hQ (x.1 + 1) (y.1 + 1) hxQ hyQ x.2 y.2 hxne hyne
    ρ₁.re ρ₂.re hbtop₁ hbtop₂ hzreal₁ hzreal₂ (by linarith) (by linarith)
  exact primitive_sigma_eq_of_lift_eq x.2 y.2 hx.2.1 hy.2.1 hlift


/-- LEAF. Unit U-1532. Siegel's theorem, p. 127: for each `ε > 0` there is `c > 0` such that a
real zero `β` of `L(s, χ)`, `χ` real primitive of conductor `r`, has `1 - β ≥ c r^{-ε}`. -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ (q + 1),
    χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ, χ.LFunction β = 0 →
      β ≤ 1 - c * ((q : ℝ) + 1) ^ (-ε) := by
  intro ε hε
  obtain ⟨cs, hcs, hs⟩ := siegel_zero ε hε
  let c := min (cs * (8 : ℝ) ^ (-ε)) (1 / 2)
  have hc : 0 < c := lt_min (mul_pos hcs (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)
  refine ⟨c, hc, fun q χ hprim h2 β hz => ?_⟩
  by_cases hχ : χ = 1
  · have hlev : q + 1 = 1 := by
      have h := hprim
      rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at h
      exact h.symm
    have hq : q = 0 := by omega
    subst q
    have hzeta : riemannZeta (β : ℂ) = 0 := by rwa [DirichletCharacter.LFunction_modOne_eq] at hz
    have hβ : β ≤ 0 := by
      by_contra hh
      have hb0 : 0 < β := by linarith
      by_cases hb1 : 1 ≤ β
      · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hb1) hzeta
      · have hh := (riemannZeta_real_neg hb0 (by linarith)).2
        rw [hzeta] at hh
        norm_num at hh
    have hc2 : c ≤ 1 / 2 := min_le_right _ _
    norm_num
    linarith
  · have hb1 : β ≤ 1 := by
      by_contra hh
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz
    let M := 8 * (q + 1)
    have hM8 : 8 ≤ M := by dsimp [M]; omega
    haveI : NeZero M := ⟨by omega⟩
    have hd : q + 1 ∣ M := by exact ⟨8, by dsimp [M]; ring⟩
    have hz' : (DirichletCharacter.changeLevel hd χ).LFunction β = 0 := by
      rw [L_lift hd hχ, hz, zero_mul]
    have hbound := hs M hM8 (DirichletCharacter.changeLevel hd χ) (lift_ne_one hd hχ) (lift_sq hd h2) β hb1 hz'
    have hMr : (M : ℝ) = 8 * ((q : ℝ) + 1) := by dsimp [M]; push_cast; ring
    rw [hMr, Real.mul_rpow (by norm_num) (by positivity)] at hbound
    have hc' : c * ((q : ℝ) + 1) ^ (-ε) ≤ cs * ((8 : ℝ) ^ (-ε) * ((q : ℝ) + 1) ^ (-ε)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)
    linarith

/-- LEAF. Unit U-1532. Lemma 9, p. 136: the conductor `r` of a real primitive character is
`r₀`, `4r₀` or `8r₀` with `r₀` odd and squarefree. -/
theorem lemma9 {r : ℕ} (hr : 0 < r) (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) :
    ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀) := by
  exact LeanLab.Romanov.Decomp134.lemma9 hr χ hχ h2

open LeanLab.Linnik.Decomp1537a
open LeanLab.Linnik.U1466Display17 (hval FD sv_cons)

/-- Gallagher 1975 p.137. The stronger squarefree product weight has the same square root order bound. -/
theorem kf_lcm_order_weight_le {f : ℕ} (hf : Odd f) (S : Finset ℕ) :
    ∑ q ∈ S, kf q / (ordTwo (Nat.lcm f q) : ℝ) ≤
      (16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f) := by
  classical
  have hfpos : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hsf : 0 < Real.sqrt (ordTwo f) := Real.sqrt_pos.mpr hfpos
  have hpoint (q : ℕ) :
      kf q / (ordTwo (Nat.lcm f q) : ℝ) ≤
        LeanLab.Romanov.halfOrderTerm q / Real.sqrt (ordTwo f) := by
    by_cases hk : kf q = 0
    · rw [hk, zero_div]
      exact div_nonneg (LeanLab.Romanov.halfOrderTerm_nonneg q) hsf.le
    have hqo := odd_of_kf_ne hk
    have hqs : Squarefree q := by
      by_contra hs
      exact hk (by simp [kf, hs])
    have hlo : Odd (Nat.lcm f q) :=
      (hf.mul hqo).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right f q) (dvd_mul_left q f))
    have hlpos : (0 : ℝ) < ordTwo (Nat.lcm f q) :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hlo
    have hqpos : (0 : ℝ) < ordTwo q :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hqo
    have hsqp : 0 < Real.sqrt (ordTwo q) := Real.sqrt_pos.mpr hqpos
    have hfle : (ordTwo f : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast xi_le_of_dvd hlo (Nat.dvd_lcm_left f q)
    have hqle : (ordTwo q : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast xi_le_of_dvd hlo (Nat.dvd_lcm_right f q)
    have hsqrt : Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q) ≤ ordTwo (Nat.lcm f q) := by
      calc
        _ = Real.sqrt ((ordTwo f : ℝ) * ordTwo q) := (Real.sqrt_mul hfpos.le _).symm
        _ ≤ Real.sqrt ((ordTwo (Nat.lcm f q) : ℝ) * ordTwo (Nat.lcm f q)) :=
          Real.sqrt_le_sqrt (mul_le_mul hfle hqle hqpos.le hlpos.le)
        _ = _ := Real.sqrt_mul_self hlpos.le
    have hfd : kf q = LeanLab.LPZ2007.fd q := by
      rw [kf, ite_eq_left ⟨hqo, hqs⟩, LeanLab.LPZ2007.Lemma61Port.fd_eq ⟨hqo, hqs⟩]
    rw [LeanLab.Romanov.halfOrderTerm, ite_eq_left (show LeanLab.LPZ2007.OddSqf q from ⟨hqo, hqs⟩)]
    rw [← hfd]
    change kf q / (ordTwo (Nat.lcm f q) : ℝ) ≤ kf q / Real.sqrt (ordTwo q) / Real.sqrt (ordTwo f)
    have hh := div_le_div_of_nonneg_left (kf_nonneg q) (mul_pos hsf hsqp) hsqrt
    calc
      _ ≤ kf q / (Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q)) := hh
      _ = _ := by rw [div_mul_eq_div_div]; ring
  calc
    _ ≤ ∑ q ∈ S, LeanLab.Romanov.halfOrderTerm q / Real.sqrt (ordTwo f) :=
      sum_le_sum fun q _ => hpoint q
    _ = (∑ q ∈ S, LeanLab.Romanov.halfOrderTerm q) / Real.sqrt (ordTwo f) := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      ((LeanLab.Romanov.halfOrder_summable.sum_le_tsum S
        (fun q _ => LeanLab.Romanov.halfOrderTerm_nonneg q)).trans LeanLab.Romanov.halfOrder_tsum_le) hsf.le

/-- Gallagher 1975 p.137. A single weighted coordinate has a square root order main term and a logarithmic error. -/
theorem Aq_order_bound : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 2 ≤ L →
    ∀ f : ℕ, Odd f → ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
      Aq m f L ≤ (16 * Real.log 2 * Real.exp 27) * L / Real.sqrt (ordTwo f) + C * Real.log L := by
  classical
  obtain ⟨C, hC, hbound⟩ := sfac_Pm_le_log
  refine ⟨C, hC, fun L hL f hf m hm => ?_⟩
  have step1 : Aq m f L ≤
      ∑ d ∈ (Pm m L).divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d f)) + kf d) := by
    rw [Aq_eq_sum]
    apply sum_le_sum
    intro d _
    by_cases hk : kf d = 0
    · simp [hk]
    have hdodd := odd_of_kf_ne hk
    have hlo : Odd (Nat.lcm d f) :=
      (hdodd.mul hf).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right d f) (dvd_mul_left f d))
    have hc := card_nus_le m L hlo
    nlinarith [mul_le_mul_of_nonneg_left hc (kf_nonneg d)]
  have step2 : ∑ d ∈ (Pm m L).divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d f)) + kf d) =
      (L : ℝ) * ∑ d ∈ (Pm m L).divisors, kf d / xi (Nat.lcm d f) +
        sfac (Pm m L : ℤ) := by
    have he : sfac (Pm m L : ℤ) = ∑ d ∈ (Pm m L).divisors, kf d := by
      simpa using sfac_eq_sum_kf (Pm m L : ℤ) (by exact_mod_cast (Pm_pos m L).ne')
    rw [he, sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro d _
    ring
  have hs := kf_lcm_order_weight_le hf (Pm m L).divisors
  simp_rw [Nat.lcm_comm f] at hs
  change (∑ d ∈ (Pm m L).divisors, kf d / xi (Nat.lcm d f)) ≤ _ at hs
  calc
    _ ≤ _ := step1
    _ = _ := step2
    _ ≤ (L : ℝ) * ((16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f)) + C * Real.log L :=
      add_le_add (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg L)) (hbound L hL m hm)
    _ = _ := by ring

/-- Gallagher 1975 p.137. Splitting the divisor sum at the fourth root gives square root logarithmic decay. -/
theorem divisor_sqrt_log_sum_le {s : ℕ} (hs : 0 < s) :
    ∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f) ≤
      3 * s / Real.sqrt (1 + Real.log s) := by
  classical
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlogs : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
  let t : ℝ := Real.sqrt (Real.sqrt s)
  let D := Real.sqrt (1 + Real.log s)
  have hD : 0 < D := Real.sqrt_pos.mpr (by linarith)
  have ht1 : 1 ≤ t := by
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hs1)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht2 : t * t = Real.sqrt s := by simp [pow_two, t]
  have hlogt : Real.log t = Real.log s / 4 := by
    dsimp [t]
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hsR.le]
    ring
  let A : Finset ℕ := s.divisors.filter (fun f : ℕ => (f : ℝ) ≤ t)
  let B : Finset ℕ := s.divisors.filter (fun f : ℕ => ¬ (f : ℝ) ≤ t)
  have hlocal (f : ℕ) (hf : f ∈ s.divisors) : 1 ≤ Real.sqrt (1 + Real.log f) := by
    have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.pos_of_mem_divisors hf
    exact Real.one_le_sqrt.mpr (by linarith [Real.log_nonneg hf1])
  have hcard : (A.card : ℝ) ≤ t := by
    have hsub : A ⊆ Icc 1 ⌊t⌋₊ := by
      intro f hf
      obtain ⟨hfd, hft⟩ := mem_filter.mp hf
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hfd, Nat.le_floor hft⟩
    have hc := card_le_card hsub
    have hc' : A.card ≤ ⌊t⌋₊ := by simpa using hc
    exact (by exact_mod_cast hc' : (A.card : ℝ) ≤ ⌊t⌋₊).trans (Nat.floor_le ht0)
  have hsmall : (∑ f ∈ A, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤ Real.sqrt s := by
    calc
      _ ≤ ∑ _f ∈ A, t := by
        apply sum_le_sum
        intro f hf
        have hfd := (mem_filter.mp hf).1
        have ht := (mem_filter.mp hf).2
        calc
          _ ≤ (f.totient : ℝ) := div_le_self (Nat.cast_nonneg _) (hlocal f hfd)
          _ ≤ (f : ℝ) := by exact_mod_cast Nat.totient_le f
          _ ≤ t := ht
      _ = (A.card : ℝ) * t := by simp
      _ ≤ t * t := mul_le_mul_of_nonneg_right hcard ht0
      _ = _ := ht2
  have hpoint (f : ℕ) (hf : f ∈ B) :
      (f.totient : ℝ) / Real.sqrt (1 + Real.log f) ≤ (f.totient : ℝ) * (2 / D) := by
    have hfd := (mem_filter.mp hf).1
    have hft : t < (f : ℝ) := lt_of_not_ge (mem_filter.mp hf).2
    have hfpos : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_mem_divisors hfd
    have hlf : Real.log s / 4 ≤ Real.log f := by
      rw [← hlogt]
      exact Real.log_le_log (by linarith) hft.le
    have hlf0 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg (by linarith)
    have hd : D ≤ 2 * Real.sqrt (1 + Real.log f) := by
      have hsqD : D ^ 2 = 1 + Real.log s := Real.sq_sqrt (by linarith)
      have hsqf := Real.sq_sqrt (show 0 ≤ 1 + Real.log (f : ℝ) by linarith)
      nlinarith [Real.sqrt_nonneg (1 + Real.log (f : ℝ))]
    have hfp : 0 < Real.sqrt (1 + Real.log (f : ℝ)) := by linarith [hlocal f hfd]
    rw [← mul_div_assoc, div_le_div_iff₀ hfp hD]
    nlinarith [show (0 : ℝ) ≤ f.totient from Nat.cast_nonneg _]
  have hlarge : (∑ f ∈ B, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤ (s : ℝ) * (2 / D) := by
    calc
      _ ≤ ∑ f ∈ B, (f.totient : ℝ) * (2 / D) := sum_le_sum hpoint
      _ = (∑ f ∈ B, (f.totient : ℝ)) * (2 / D) := (sum_mul _ _ _).symm
      _ ≤ (∑ f ∈ s.divisors, (f.totient : ℝ)) * (2 / D) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = (s : ℝ) * (2 / D) := by norm_cast; rw [Nat.sum_totient]
  have hroot : Real.sqrt s ≤ (s : ℝ) / D := by
    have hDle : D ≤ Real.sqrt s := by
      apply Real.sqrt_le_sqrt
      linarith [Real.log_le_sub_one_of_pos hsR]
    rw [le_div_iff₀ hD]
    calc
      Real.sqrt s * D ≤ Real.sqrt s * Real.sqrt s :=
        mul_le_mul_of_nonneg_left hDle (Real.sqrt_nonneg _)
      _ = s := by rw [← pow_two, Real.sq_sqrt hsR.le]
  have he := sum_filter_add_sum_filter_not s.divisors (fun f : ℕ => (f : ℝ) ≤ t)
    (fun f : ℕ => (f.totient : ℝ) / Real.sqrt (1 + Real.log f))
  change (∑ f ∈ A, _) + (∑ f ∈ B, _) = _ at he
  rw [← he]
  change _ ≤ 3 * s / D
  calc
    _ ≤ (s : ℝ) / D + (s : ℝ) * (2 / D) := add_le_add (hsmall.trans hroot) hlarge
    _ = _ := by ring

/-- Gallagher 1975 p.137. Two powers of log log are absorbed by one sixth power of log. -/
theorem log_sq_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 / Real.sqrt (1 + x) ≤ 144 / x ^ (1 / 3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 12)
  have hsq : Real.log x ^ 2 ≤ 144 * x ^ (1 / 6 : ℝ) := by
    calc
      _ ≤ (12 * x ^ (1 / 12 : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ hlog0
        linarith
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 12 : ℝ)) 2, ← Real.rpow_mul hx0.le]
        norm_num
  have hmul : x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) = Real.sqrt x := by
    rw [← Real.rpow_add hx0]
    norm_num
    exact (Real.sqrt_eq_rpow x).symm
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)) (Real.rpow_pos_of_pos hx0 _)]
  calc
    _ ≤ (144 * x ^ (1 / 6 : ℝ)) * x ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hx0.le _)
    _ = 144 * Real.sqrt x := by rw [mul_assoc, hmul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)

/-- Gallagher 1975 p.137. The totient ratio leaves a one third logarithmic power after the square root decay. -/
theorem totient_ratio_sqrt_log_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 3 ≤ r →
    ((r : ℝ) / r.totient) ^ 2 / Real.sqrt (1 + Real.log r) ≤
      C / Real.log r ^ (1 / 3 : ℝ) := by
  obtain ⟨A, hA⟩ := LeanLab.Linnik.Decomp1532a.div_totient_le_loglog
  let B := max A 0
  refine ⟨144 * B ^ 2, by positivity, fun r hr => ?_⟩
  have hl : 1 ≤ Real.log (r : ℝ) := by
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    apply le_of_lt
    rw [Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < r)]
    linarith [Real.exp_one_lt_d9]
  have hll : 0 ≤ Real.log (Real.log r) := Real.log_nonneg hl
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / r.totient := by positivity
  have hb : (r : ℝ) / r.totient ≤ B * Real.log (Real.log r) :=
    (hA r hr).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hll)
  have hb2 : ((r : ℝ) / r.totient) ^ 2 ≤ B ^ 2 * Real.log (Real.log r) ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left₀ hr0 hb 2
  calc
    _ ≤ (B ^ 2 * Real.log (Real.log r) ^ 2) / Real.sqrt (1 + Real.log r) :=
      div_le_div_of_nonneg_right hb2 (Real.sqrt_nonneg _)
    _ = B ^ 2 * (Real.log (Real.log r) ^ 2 / Real.sqrt (1 + Real.log r)) := by ring
    _ ≤ B ^ 2 * (144 / Real.log r ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_sq_div_sqrt_le hl) (sq_nonneg _)
    _ = _ := by ring

/-- Gallagher 1975 p.137. The conductor divisor split has the final uniform logarithmic decay. -/
theorem exceptional_divisor_log_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ r s : ℕ,
    3 ≤ r → 0 < s → (r = s ∨ r = 4 * s ∨ r = 8 * s) →
    (r : ℝ) / (r.totient : ℝ) ^ 2 *
      (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤
      C / Real.log r ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := totient_ratio_sqrt_log_decay
  refine ⟨6 * C, by positivity, fun r s hr hs hrs => ?_⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  have hsr : s ≤ r := by rcases hrs with h | h | h <;> omega
  have hrs8 : r ≤ 8 * s := by rcases hrs with h | h | h <;> omega
  have hlogs : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hlog8 : Real.log (8 : ℝ) ≤ 3 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlog : Real.log (r : ℝ) ≤ 3 + Real.log s := by
    have hh := Real.log_le_log hr0 (show (r : ℝ) ≤ 8 * s by exact_mod_cast hrs8)
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hs0.ne'] at hh
    linarith
  have hDr : 0 < Real.sqrt (1 + Real.log (r : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hDs : 0 < Real.sqrt (1 + Real.log (s : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hcomp : Real.sqrt (1 + Real.log (r : ℝ)) ≤ 2 * Real.sqrt (1 + Real.log (s : ℝ)) := by
    have h1 := Real.sq_sqrt (show 0 ≤ 1 + Real.log (r : ℝ) by linarith)
    have h2 := Real.sq_sqrt (show 0 ≤ 1 + Real.log (s : ℝ) by linarith)
    nlinarith
  have hsum : (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤
      6 * r / Real.sqrt (1 + Real.log r) := by
    calc
      _ ≤ 3 * s / Real.sqrt (1 + Real.log s) := divisor_sqrt_log_sum_le hs
      _ ≤ 6 * s / Real.sqrt (1 + Real.log r) := by
        rw [div_le_div_iff₀ hDs hDr]
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hsr : (s : ℝ) ≤ r) (by norm_num)) hDr.le
  calc
    _ ≤ (r : ℝ) / (r.totient : ℝ) ^ 2 * (6 * r / Real.sqrt (1 + Real.log r)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 6 * (((r : ℝ) / r.totient) ^ 2 / Real.sqrt (1 + Real.log r)) := by ring
    _ ≤ 6 * (C / Real.log r ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound r hr) (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.137. A restricted free exponent has an explicit square root order term and logarithmic error. -/
theorem one_coordinate_totient_order : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
    ∀ f : ℕ, Odd f → ∀ m : ℤ, |m| ≤ 2 ^ (2 * L + 2) →
      ∑ x : Fin L with hval m (Fin.val x) ≠ 0 ∧ (f : ℤ) ∣ hval m (Fin.val x),
        ((hval m (Fin.val x)).natAbs : ℝ) / (hval m (Fin.val x)).natAbs.totient ≤
      2 * (16 * Real.log 2 * Real.exp 27) * (L + 1) / Real.sqrt (ordTwo f) +
        2 * C * Real.log (L + 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := Aq_order_bound
  refine ⟨C, hC, fun L hL f hf m hm => ?_⟩
  let S : Finset (Fin L) := (univ : Finset (Fin L)).filter (fun x : Fin L => hval m (Fin.val x) ≠ 0 ∧ (f : ℤ) ∣ hval m (Fin.val x))
  have hsfac (h : ℤ) (hh : h ≠ 0) : FD 0 h = sfac h := by
    rw [sfac_eq_sum_kf h hh, FD, ite_eq_right hh]
    have he : h.natAbs.divisors.filter (fun d => 0 < d) = h.natAbs.divisors :=
      filter_eq_self.mpr fun d hd => Nat.pos_of_mem_divisors hd
    rw [he]
    rfl
  have hinj : Set.InjOn (fun x : Fin L => (x : ℕ) + 1) (S : Set (Fin L)) := by
    intro x hx y hy hxy
    apply Fin.ext
    change (x : ℕ) + 1 = (y : ℕ) + 1 at hxy
    omega
  have hsub : S.image (fun x : Fin L => (x : ℕ) + 1) ⊆ nus m f (L + 1) := by
    intro ν hν
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hν
    have hx' := (mem_filter.mp hx).2
    have hsign : m - 2 ^ ((x : ℕ) + 1) = -(hval m (Fin.val x)) := by unfold hval; ring
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, by have := x.isLt; omega⟩, ?_, ?_⟩
    · rw [hsign, neg_ne_zero]
      exact hx'.1
    · rw [hsign]
      exact dvd_neg.mpr hx'.2
  have heq : (∑ x ∈ S, sfac (hval m (Fin.val x))) =
      ∑ ν ∈ S.image (fun x : Fin L => (x : ℕ) + 1), sfac (m - 2 ^ ν) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro x hx
    have hsign : m - 2 ^ ((x : ℕ) + 1) = -(hval m (Fin.val x)) := by unfold hval; ring
    simp only [hsign, sfac, Int.natAbs_neg]
  have hA : ∑ x ∈ S, sfac (hval m (Fin.val x)) ≤ Aq m f (L + 1) := by
    rw [heq]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun ν _ _ => sfac_nonneg _)
  have hhm : |m| ≤ 2 ^ (2 * (L + 1)) := by convert hm using 1
  have hAb := hbound (L + 1) (by omega) f hf m hhm
  simp only [Nat.cast_add, Nat.cast_one] at hAb
  change (∑ x ∈ S, _) ≤ _
  calc
    _ ≤ ∑ x ∈ S, 2 * sfac (hval m (Fin.val x)) := by
      apply sum_le_sum
      intro x hx
      have hh := LeanLab.Linnik.Decomp1532a.totient_ratio_le_weight (hval m (Fin.val x))
      rwa [hsfac _ (mem_filter.mp hx).2.1] at hh
    _ = 2 * ∑ x ∈ S, sfac (hval m (Fin.val x)) := (mul_sum _ _ _).symm
    _ ≤ 2 * Aq m f (L + 1) := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ 2 * ((16 * Real.log 2 * Real.exp 27) * (L + 1) / Real.sqrt (ordTwo f) +
        C * Real.log (L + 1)) := by exact mul_le_mul_of_nonneg_left hAb (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.137. The uniform weighted sum over multiples of an odd divisor has square root logarithmic decay. -/
theorem restricted_tuple_totient_bound : ∃ C : ℝ, 0 < C ∧ ∀ k N : ℕ,
    1 ≤ k → k ≤ N → 2 ≤ N → ∀ f : ℕ, Odd f → f ≤ N →
      ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0 ∧ (f : ℤ) ∣ dif x,
        ((dif x).natAbs : ℝ) / (dif x).natAbs.totient ≤
      C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.sqrt (1 + Real.log f) := by
  classical
  obtain ⟨C, hC, hcoord⟩ := one_coordinate_totient_order
  let K : ℝ := 16 * Real.log 2 * Real.exp 27
  have hK : 0 < K := by dsimp [K]; positivity
  let A : ℝ := 2 * (K + C)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨12 * A, by positivity, fun k N hk hkN hN f hf hfN => ?_⟩
  let L := Nat.log 2 N
  have hL : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hNpow : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf.pos
  have hlf : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf1
  let D := Real.sqrt (1 + Real.log f)
  have hD : 0 < D := Real.sqrt_pos.mpr (by linarith)
  have ho : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have ho1 : (1 : ℝ) ≤ ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hDo : 1 + Real.log f ≤ 2 * ordTwo f := by
    have hh := LeanLab.Linnik.Decomp1532a.log_le_ordTwo_mul_log_two hf
    nlinarith
  have hDf : 1 + Real.log f ≤ 2 * ((L : ℝ) + 1) := by
    have hb : (f : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast hfN.trans hNpow.le
    have hh := Real.log_le_log (by linarith : (0 : ℝ) < f) hb
    rw [Real.log_pow] at hh
    push_cast at hh
    nlinarith
  have hcompO : D ≤ 2 * Real.sqrt (ordTwo f) := by
    have hsD : D ^ 2 = 1 + Real.log f := Real.sq_sqrt (by linarith)
    have hso := Real.sq_sqrt ho.le
    nlinarith [Real.sqrt_nonneg (ordTwo f)]
  have hcompL : D ≤ 2 * Real.sqrt ((L : ℝ) + 1) := by
    have hsD : D ^ 2 = 1 + Real.log f := Real.sq_sqrt (by linarith)
    have hsL := Real.sq_sqrt (show 0 ≤ (L : ℝ) + 1 by positivity)
    nlinarith [Real.sqrt_nonneg ((L : ℝ) + 1)]
  have hlogL : Real.log ((L : ℝ) + 1) ≤ 2 * Real.sqrt ((L : ℝ) + 1) := by
    have hh := Real.log_le_rpow_div (show 0 ≤ (L : ℝ) + 1 by positivity)
      (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hlogL0 : 0 ≤ Real.log ((L : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hshape : (((L : ℝ) + 1) / Real.sqrt (ordTwo f) + Real.log ((L : ℝ) + 1)) ≤
      12 * L / D := by
    have hmain : (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) * D ≤ 2 * ((L : ℝ) + 1) := by
      calc
        _ ≤ (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) * (2 * Real.sqrt (ordTwo f)) :=
          mul_le_mul_of_nonneg_left hcompO (by positivity)
        _ = _ := by field_simp
    have herr : Real.log ((L : ℝ) + 1) * D ≤ 4 * ((L : ℝ) + 1) := by
      calc
        _ ≤ (2 * Real.sqrt ((L : ℝ) + 1)) * (2 * Real.sqrt ((L : ℝ) + 1)) :=
          mul_le_mul hlogL hcompL hD.le (by positivity)
        _ = _ := by nlinarith [Real.sq_sqrt (show 0 ≤ (L : ℝ) + 1 by positivity)]
    rw [le_div_iff₀ hD]
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkey (ν : Fin j → Fin L) (mu : Fin (j + 1) → Fin L) :
      (∑ x : Fin L, if (f : ℤ) ∣ dif (Fin.cons x ν, mu) then
        ((dif (Fin.cons x ν, mu)).natAbs : ℝ) / (dif (Fin.cons x ν, mu)).natAbs.totient else 0) ≤
        (12 * A) * L / D := by
    let m : ℤ := (sv mu : ℤ) - sv ν
    have he (x : Fin L) : dif (Fin.cons x ν, mu) = hval m (Fin.val x) := by
      rw [dif, sv_cons]
      dsimp [hval, m]
      ring
    have hm : |m| ≤ 2 ^ (2 * L + 2) := by
      have hmu := LeanLab.Linnik.U1434Lemma21.sv_le mu
      have hν := LeanLab.Linnik.U1434Lemma21.sv_le ν
      have hmu' : sv mu ≤ N * 2 ^ L := hmu.trans (Nat.mul_le_mul_right _ hkN)
      have hν' : sv ν ≤ N * 2 ^ L := hν.trans (Nat.mul_le_mul_right _ (by omega))
      have hnat : m.natAbs ≤ N * 2 ^ L := by dsimp [m]; omega
      have hb : m.natAbs ≤ 2 ^ (2 * L + 2) := by
        calc
          _ ≤ N * 2 ^ L := hnat
          _ ≤ 2 ^ (L + 1) * 2 ^ L := Nat.mul_le_mul_right _ hNpow.le
          _ ≤ 2 ^ (2 * L + 2) := by rw [← pow_add]; apply Nat.pow_le_pow_right (by norm_num); omega
      rw [← Int.natCast_natAbs]
      exact_mod_cast hb
    have hco := hcoord L hL f hf m hm
    have heq : (∑ x : Fin L, if (f : ℤ) ∣ dif (Fin.cons x ν, mu) then
        ((dif (Fin.cons x ν, mu)).natAbs : ℝ) / (dif (Fin.cons x ν, mu)).natAbs.totient else 0) =
        ∑ x : Fin L with hval m (Fin.val x) ≠ 0 ∧ (f : ℤ) ∣ hval m (Fin.val x),
          ((hval m (Fin.val x)).natAbs : ℝ) / (hval m (Fin.val x)).natAbs.totient := by
      rw [sum_filter]
      apply sum_congr rfl
      intro x hx
      rw [he]
      by_cases hh : hval m (Fin.val x) = 0 <;> simp [hh]
    rw [heq]
    have hcoef : 2 * K * ((L : ℝ) + 1) / Real.sqrt (ordTwo f) + 2 * C * Real.log ((L : ℝ) + 1) ≤
        A * (((L : ℝ) + 1) / Real.sqrt (ordTwo f) + Real.log ((L : ℝ) + 1)) := by
      dsimp [A]
      have hu : 0 ≤ ((L : ℝ) + 1) / Real.sqrt (ordTwo f) := by positivity
      calc
        _ = (2 * K) * (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) + 2 * C * Real.log ((L : ℝ) + 1) := by ring
        _ ≤ (2 * (K + C)) * (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) +
            (2 * (K + C)) * Real.log ((L : ℝ) + 1) :=
          add_le_add (mul_le_mul_of_nonneg_right (by linarith) hu)
            (mul_le_mul_of_nonneg_right (by linarith) hlogL0)
        _ = _ := by ring
    calc
      _ ≤ 2 * K * ((L : ℝ) + 1) / Real.sqrt (ordTwo f) + 2 * C * Real.log ((L : ℝ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hco
      _ ≤ _ := hcoef
      _ ≤ A * (12 * L / D) := mul_le_mul_of_nonneg_left hshape hA.le
      _ = _ := by ring
  have heq : (∑ x : pairs (j + 1) L with dif x ≠ 0 ∧ (f : ℤ) ∣ dif x,
      ((dif x).natAbs : ℝ) / (dif x).natAbs.totient) =
      ∑ x : pairs (j + 1) L, if (f : ℤ) ∣ dif x then
        ((dif x).natAbs : ℝ) / (dif x).natAbs.totient else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hh : dif x = 0 <;> simp [hh]
  change (∑ x : pairs (j + 1) L with _, _) ≤ _
  rw [heq, Fintype.sum_prod_type, LeanLab.Linnik.U1466Display17.sum_cons]
  calc
    _ = ∑ ν : Fin j → Fin L, ∑ mu : Fin (j + 1) → Fin L, ∑ x : Fin L,
        if (f : ℤ) ∣ dif (Fin.cons x ν, mu) then
          ((dif (Fin.cons x ν, mu)).natAbs : ℝ) / (dif (Fin.cons x ν, mu)).natAbs.totient else 0 := by
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ ≤ ∑ _ν : Fin j → Fin L, ∑ _mu : Fin (j + 1) → Fin L, (12 * A) * L / D :=
      sum_le_sum (fun ν _ => sum_le_sum (fun mu _ => hkey ν mu))
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have he : 2 * (j + 1) = j + (j + 1) + 1 := by omega
      rw [he, pow_add, pow_add]
      ring

/-- Gallagher 1975 p.137. The exceptional gcd factor reduces to weighted sums over odd conductor divisors. -/
theorem weighted_gcd_divisor_reduction {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (n : ι → ℕ) (w : ι → ℝ) (hw : ∀ x ∈ T, 0 ≤ w x)
    {r s : ℕ} (hs : 0 < s) (hrs : r = s ∨ r = 4 * s ∨ r = 8 * s) :
    ∑ x ∈ T, w x * ((r : ℝ) * (Nat.gcd r (n x)).totient / (r.totient : ℝ) ^ 2) ≤
      (8 * r / (r.totient : ℝ) ^ 2) *
        ∑ f ∈ s.divisors, (f.totient : ℝ) * ∑ x ∈ T with f ∣ n x, w x := by
  classical
  have he (x : ι) : (Nat.gcd s (n x)).divisors = s.divisors.filter (fun f => f ∣ n x) := by
    ext f
    have hg := (Nat.gcd_pos_of_pos_left (n x) hs).ne'
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_left s (n x)), hs.ne'⟩, hd.trans (Nat.gcd_dvd_right s (n x))⟩
    · rintro ⟨⟨hfs, _⟩, hfn⟩
      exact ⟨Nat.dvd_gcd hfs hfn, hg⟩
  have hswap : (∑ x ∈ T, w x * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) =
      ∑ f ∈ s.divisors, (f.totient : ℝ) * ∑ x ∈ T with f ∣ n x, w x := by
    simp_rw [he, sum_filter, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro f hf
    apply sum_congr rfl
    intro x hx
    by_cases h : f ∣ n x <;> simp [h, mul_comm]
  calc
    _ = ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ∑ x ∈ T, w x * (Nat.gcd r (n x)).totient := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      ring
    _ ≤ ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ∑ x ∈ T, w x * (8 * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hw x hx)
      exact_mod_cast exceptional_gcd_totient_le hs hrs (n x)
    _ = (8 * r / (r.totient : ℝ) ^ 2) *
        (∑ x ∈ T, w x * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) := by
      simp_rw [show ∀ x : ι, w x * (8 * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) =
        8 * (w x * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) by intro x; ring]
      rw [← mul_sum]
      ring
    _ = _ := by rw [hswap]

/-- Gallagher 1975 pp.134 and 135. The odd reciprocal totient coefficient sum is logarithmic. -/
theorem reciprocal_totient_sum_le_log {R : ℕ} (hR : 2 ≤ R) :
    ∑ q ∈ Icc 1 R with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ≤
      Real.exp 24 * Real.log R := by
  classical
  calc
    _ ≤ ∑ q ∈ Icc 1 R with Odd q,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 := by
      apply sum_le_sum
      intro q hq
      have hqp : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqp
      have hle : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
      calc
        _ = ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q.totient / (q.totient : ℝ) ^ 2 := by
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) (sq_nonneg _)
    _ ≤ _ := LeanLab.Linnik.Decomp1532a.totient_square_sum_le_log hR

/-- Gallagher 1975 p.134. Restoring zero tuple differences in the truncated series costs a logarithmic diagonal error. -/
theorem truncated_ramanujan_diagonal_le {k : ℕ} (hk : 2 ≤ k) (L : ℕ) {R : ℕ} (hR : 2 ≤ R) :
    ‖∑ q ∈ Icc 1 R with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)‖ ≤
      2 * Real.exp 24 * (L : ℝ) ^ (2 * k - 2) * Real.log R := by
  classical
  let D := #{x : pairs k L | dif x = 0}
  let S := (Icc 1 R).filter Odd
  have hinner (q : ℕ) : (∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) =
      (D : ℂ) * q.totient := by
    calc
      _ = ∑ _x : pairs k L with dif _x = 0, (q.totient : ℂ) := by
        apply sum_congr rfl
        intro x hx
        rw [(mem_filter.mp hx).2, ramanujanSum_zero]
      _ = _ := by simp [D, nsmul_eq_mul]
  have hterm (q : ℕ) (hq : q ∈ S) :
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x) =
      (((D : ℝ) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
    have hqp : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hqp).ne'
    rw [hinner]
    push_cast
    field_simp
  have heq : (∑ q ∈ S,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) =
      (((D : ℝ) * (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
    rw [sum_congr rfl hterm, ← Complex.ofReal_sum, ← mul_sum]
  have hsum0 : 0 ≤ ∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) := by positivity
  have hD : (D : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 2) := by
    exact_mod_cast LeanLab.Linnik.Decomp1532a.rkk_zero_le hk L
  have hsum := reciprocal_totient_sum_le_log hR
  change ‖∑ q ∈ S, _‖ ≤ _
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg D) hsum0)]
  calc
    _ ≤ (2 * (L : ℝ) ^ (2 * k - 2)) * (Real.exp 24 * Real.log R) :=
      mul_le_mul hD hsum hsum0 (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.134. The reciprocal totient square tail has a uniform three fourths power saving. -/
theorem reciprocal_totient_square_tail (Q M : ℕ) (hQ : 0 < Q) :
    ∑ q ∈ Ioc Q M, (1 / (q.totient : ℝ) ^ 2) ≤
      (28 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4) := by
  by_cases hQM : Q ≤ M
  · calc
      _ ≤ ∑ q ∈ Ioc Q M, 7 * (q : ℝ) ^ (-(7 : ℝ) / 4) := by
        apply sum_le_sum
        intro q hq
        exact LeanLab.Zinoviev1997.inv_totient_sq_seven q (by have := (mem_Ioc.mp hq).1; omega)
      _ = 7 * ∑ q ∈ Ioc Q M, (q : ℝ) ^ (-(7 : ℝ) / 4) := (mul_sum _ _ _).symm
      _ ≤ 7 * ((4 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (LeanLab.Zinoviev1997.powerTail_Ioc Q M hQ hQM) (by norm_num)
      _ = _ := by ring
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity

/-- Gallagher 1975 p.134. A shifted cutoff form also covers the zero cutoff. -/
theorem reciprocal_totient_square_tail_succ (Q M : ℕ) :
    ∑ q ∈ Ioc Q M, (1 / (q.totient : ℝ) ^ 2) ≤
      64 * ((Q : ℝ) + 1) ^ (-(3 : ℝ) / 4) := by
  rcases Q with _ | Q
  · have hsub : Ioc 0 M ⊆ insert 1 (Ioc 1 M) := by
      intro q hq
      simp only [mem_Ioc, mem_insert] at hq ⊢
      omega
    have hh : (∑ q ∈ Ioc 0 M, (1 / (q.totient : ℝ) ^ 2)) ≤ 1 + 28 / 3 := by
      calc
        _ ≤ ∑ q ∈ insert 1 (Ioc 1 M), (1 / (q.totient : ℝ) ^ 2) :=
          sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
        _ = 1 + ∑ q ∈ Ioc 1 M, (1 / (q.totient : ℝ) ^ 2) := by rw [sum_insert (by simp)]; simp
        _ ≤ 1 + 28 / 3 := by simpa using add_le_add_left (reciprocal_totient_square_tail 1 M (by decide)) 1
    norm_num at hh ⊢
    linarith
  · have hpow : (((Q + 1 : ℕ) : ℝ) + 1) ^ (3 / 4 : ℝ) ≤
        2 * ((Q + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      calc
        _ ≤ (2 * ((Q + 1 : ℕ) : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by norm_num)
        _ = (2 : ℝ) ^ (3 / 4 : ℝ) * ((Q + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * ((Q + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    have hneg : ((Q + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) ≤
        2 * (((Q + 1 : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4) := by
      rw [show -(3 : ℝ) / 4 = -(3 / 4 : ℝ) by ring, Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      rw [← one_div, ← one_div, ← mul_div_assoc]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpow)
    have hh := reciprocal_totient_square_tail (Q + 1) M (by omega)
    calc
      _ ≤ (28 / 3 : ℝ) * ((Q + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) := hh
      _ ≤ (28 / 3 : ℝ) * (2 * (((Q + 1 : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hneg (by norm_num)
      _ ≤ _ := by push_cast; nlinarith [Real.rpow_nonneg (show 0 ≤ (Q : ℝ) + 1 + 1 by positivity) (-(3 : ℝ) / 4)]

/-- Gallagher 1975 p.134. The divisor weight in the power tail is uniformly bounded. -/
theorem three_fourths_div_totient_le {d : ℕ} (hd : 0 < d) :
    (d : ℝ) ^ (3 / 4 : ℝ) / d.totient ≤ 3 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hpow : ((d : ℝ) ^ (3 / 4 : ℝ)) ^ 8 = (d : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg d)]
    norm_num
  have hh : (d : ℝ) ^ 7 ≤ 2401 * (d.totient : ℝ) ^ 8 := by
    exact_mod_cast LeanLab.Zinoviev1997.seventh_le_totient_eighth d hd
  have hbound : (d : ℝ) ^ (3 / 4 : ℝ) ≤ 3 * d.totient := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (8 : ℕ) ≠ 0)).mp
    calc
      _ = (d : ℝ) ^ 6 := hpow
      _ ≤ (d : ℝ) ^ 7 := pow_le_pow_right₀ hdR (by decide)
      _ ≤ 2401 * (d.totient : ℝ) ^ 8 := hh
      _ ≤ _ := by rw [mul_pow]; norm_num; nlinarith [show (0 : ℝ) ≤ (d.totient : ℝ) ^ 8 by positivity]
  exact (div_le_iff₀ hφ).mpr hbound

/-- Gallagher 1975 p.134. The totient weight along multiples of one divisor has a uniform tail. -/
theorem totient_square_multiples_tail {d R : ℕ} (hd : 0 < d) (hR : 0 < R) (M : ℕ) :
    ∑ q ∈ (Ioc R M).filter (fun q => d ∣ q), (d.totient : ℝ) / (q.totient : ℝ) ^ 2 ≤
      192 / (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hdφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have heq : (∑ q ∈ (Ioc R M).filter (fun q => d ∣ q), (d.totient : ℝ) / (q.totient : ℝ) ^ 2) =
      ∑ j ∈ Ioc (R / d : ℕ) (M / d : ℕ), (d.totient : ℝ) / ((d * j).totient : ℝ) ^ 2 := by
    apply sum_bij (fun q _ => q / d)
    · intro q hq
      obtain ⟨hqI, hdq⟩ := mem_filter.mp hq
      obtain ⟨hRq, hqM⟩ := mem_Ioc.mp hqI
      refine mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hqM⟩
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa [Nat.div_mul_cancel hdq] using hRq
    · intro q hq q' hq' hqq
      have h1 := Nat.div_mul_cancel (mem_filter.mp hq).2
      have h2 := Nat.div_mul_cancel (mem_filter.mp hq').2
      rw [hqq] at h1
      omega
    · intro j hj
      obtain ⟨hRj, hjM⟩ := mem_Ioc.mp hj
      have hl : R < d * j := by simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hRj
      have hu : d * j ≤ M := by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hjM
      refine ⟨d * j, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hl, hu⟩, dvd_mul_right d j⟩, ?_⟩
      exact Nat.mul_div_cancel_left j hd
    · intro q hq
      rw [Nat.mul_div_cancel' (mem_filter.mp hq).2]
  have hpoint (j : ℕ) (hj : j ∈ Ioc (R / d : ℕ) (M / d : ℕ)) :
      (d.totient : ℝ) / ((d * j).totient : ℝ) ^ 2 ≤
        (1 / (d.totient : ℝ)) * (1 / (j.totient : ℝ) ^ 2) := by
    have hj0 : 0 < j := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hj).1
    have hjφ : (0 : ℝ) < j.totient := by exact_mod_cast Nat.totient_pos.mpr hj0
    have hmul : (d.totient : ℝ) * j.totient ≤ (d * j).totient := by
      exact_mod_cast Nat.totient_super_multiplicative d j
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)
      (sq_pos_of_pos (mul_pos hdφ hjφ)) (pow_le_pow_left₀ (by positivity) hmul 2)
    calc
      _ ≤ (d.totient : ℝ) / ((d.totient : ℝ) * j.totient) ^ 2 := hh
      _ = _ := by field_simp
  have hcut : (R : ℝ) / d ≤ ((R / d : ℕ) : ℝ) + 1 := by
    have hn : R < (R / d + 1) * d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (R / d))
    apply (div_le_iff₀ hdR).mpr
    exact_mod_cast hn.le
  have hp : (((R / d : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4) ≤
      ((R : ℝ) / d) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hRR hdR) hcut (by norm_num)
  have hepow : ((R : ℝ) / d) ^ (-(3 : ℝ) / 4) =
      (d : ℝ) ^ (3 / 4 : ℝ) / (R : ℝ) ^ (3 / 4 : ℝ) := by
    rw [show -(3 : ℝ) / 4 = -(3 / 4 : ℝ) by ring, Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity), inv_div]
  calc
    _ = _ := heq
    _ ≤ ∑ j ∈ Ioc (R / d : ℕ) (M / d : ℕ), (1 / (d.totient : ℝ)) * (1 / (j.totient : ℝ) ^ 2) := sum_le_sum hpoint
    _ = (1 / (d.totient : ℝ)) * ∑ j ∈ Ioc (R / d : ℕ) (M / d : ℕ), (1 / (j.totient : ℝ) ^ 2) := (mul_sum _ _ _).symm
    _ ≤ (1 / (d.totient : ℝ)) * (64 * (((R / d : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (reciprocal_totient_square_tail_succ (R / d) (M / d)) (by positivity)
    _ ≤ (1 / (d.totient : ℝ)) * (64 * (((R : ℝ) / d) ^ (-(3 : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = (64 / (R : ℝ) ^ (3 / 4 : ℝ)) * ((d : ℝ) ^ (3 / 4 : ℝ) / d.totient) := by rw [hepow]; ring
    _ ≤ (64 / (R : ℝ) ^ (3 / 4 : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left (three_fourths_div_totient_le hd) (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.134. Expanding the gcd weight gives a uniform reciprocal totient square tail. -/
theorem gcd_totient_square_tail {n R : ℕ} (hn : 0 < n) (hR : 0 < R) (M : ℕ) :
    ∑ q ∈ Ioc R M, (Nat.gcd q n : ℝ) / (q.totient : ℝ) ^ 2 ≤
      192 * n.divisors.card / (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  have hdiv (q : ℕ) : (Nat.gcd q n).divisors = n.divisors.filter (fun d => d ∣ q) := by
    ext d
    have hg : Nat.gcd q n ≠ 0 := by
      simpa [Nat.gcd_comm] using (Nat.gcd_pos_of_pos_left q hn).ne'
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right q n), hn.ne'⟩, hd.trans (Nat.gcd_dvd_left q n)⟩
    · rintro ⟨⟨hdn, _⟩, hdq⟩
      exact ⟨Nat.dvd_gcd hdq hdn, hg⟩
  have hg (q : ℕ) : (Nat.gcd q n : ℝ) = ∑ d ∈ (Nat.gcd q n).divisors, (d.totient : ℝ) := by
    exact_mod_cast (Nat.sum_totient (Nat.gcd q n)).symm
  have heq : (∑ q ∈ Ioc R M, (Nat.gcd q n : ℝ) / (q.totient : ℝ) ^ 2) =
      ∑ d ∈ n.divisors, ∑ q ∈ (Ioc R M).filter (fun q => d ∣ q),
        (d.totient : ℝ) / (q.totient : ℝ) ^ 2 := by
    simp_rw [hg, hdiv, sum_filter, sum_div, ite_div, zero_div]
    rw [sum_comm]
  rw [heq]
  calc
    _ ≤ ∑ _d ∈ n.divisors, 192 / (R : ℝ) ^ (3 / 4 : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact totient_square_multiples_tail (Nat.pos_of_mem_divisors hd) hR M
    _ = _ := by simp; ring

/-- Gallagher 1975 p.134. Each singular series coefficient is bounded by its gcd majorant. -/
theorem singular_coefficient_norm_le_gcd {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n‖ ≤
      (Nat.gcd q n.natAbs : ℝ) / (q.totient : ℝ) ^ 2 := by
  by_cases hsf : Squarefree q
  · have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hRc : ‖ramanujanSum q n‖ ≤ (Nat.gcd q n.natAbs : ℝ) := by
      rw [ramanujanSum_squarefree hsf n, norm_mul, Complex.norm_intCast, Complex.norm_natCast]
      have hm : |((ArithmeticFunction.moebius (q / Nat.gcd q n.natAbs) : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / Nat.gcd q n.natAbs)
      calc
        _ ≤ ((Nat.gcd q n.natAbs).totient : ℝ) :=
          mul_le_of_le_one_left (Nat.cast_nonneg _) hm
        _ ≤ _ := by exact_mod_cast Nat.totient_le (Nat.gcd q n.natAbs)
    rw [hmu, one_div, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ ((q.totient : ℝ) ^ 2)⁻¹ * (Nat.gcd q n.natAbs : ℝ) :=
        mul_le_mul_of_nonneg_left hRc (by positivity)
      _ = _ := by ring
  · simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf, Int.cast_zero,
      zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, norm_zero]
    positivity

/-- Gallagher 1975 p.134. A uniform pointwise truncation error with an explicit power saving. -/
theorem singular_series_truncation_le {n : ℤ} (hn : n ≠ 0) {R : ℕ} (hR : 0 < R) :
    ‖singSeries n - ∑ q ∈ Icc 1 R,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n‖ ≤
      192 * n.natAbs.divisors.card / (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  let f : ℕ → ℂ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 /
    (q.totient : ℂ) ^ 2 * ramanujanSum q n
  have hs : Summable f := summable_singSeries hn
  have hf0 : f 0 = 0 := by simp [f]
  have htrunc : (∑ q ∈ range (R + 1), f q) = ∑ q ∈ Icc 1 R, f q := by
    have he : range (R + 1) = insert 0 (Icc 1 R) := by ext q; simp; omega
    rw [he, sum_insert (by simp), hf0, zero_add]
  have hlim : Tendsto (fun M : ℕ => ∑ q ∈ range M, f q) atTop (nhds (singSeries n)) :=
    hs.hasSum.tendsto_sum_nat
  have hnorm := (hlim.sub (tendsto_const_nhds (x := ∑ q ∈ range (R + 1), f q))).norm
  have hbound : ∀ᶠ M : ℕ in atTop, ‖(∑ q ∈ range M, f q) - ∑ q ∈ range (R + 1), f q‖ ≤
      192 * n.natAbs.divisors.card / (R : ℝ) ^ (3 / 4 : ℝ) := by
    filter_upwards [eventually_ge_atTop (R + 1)] with M hM
    have he : Ico (R + 1) M = Ioc R (M - 1) := by ext q; simp; omega
    rw [← sum_Ico_eq_sub f hM, he]
    calc
      _ ≤ ∑ q ∈ Ioc R (M - 1), ‖f q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Ioc R (M - 1), (Nat.gcd q n.natAbs : ℝ) / (q.totient : ℝ) ^ 2 := by
        apply sum_le_sum
        intro q hq
        exact singular_coefficient_norm_le_gcd (by have := (mem_Ioc.mp hq).1; omega) n
      _ ≤ _ := gcd_totient_square_tail (Int.natAbs_pos.mpr hn) hR (M - 1)
  have hh := le_of_tendsto hnorm hbound
  rw [htrunc] at hh
  exact hh

/-- Gallagher 1975 p.134. The moving tuple average has a uniform truncation error at every reciprocal integer power. -/
theorem tuple_singular_truncation_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ k N R : ℕ, 2 ≤ N → 0 < R →
      ‖(∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x)) -
          ∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
            ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)‖ ≤
      C * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) * (Nat.log 2 N : ℝ) ^ (2 * k) /
        (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨A, hA, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow m hm
  refine ⟨192 * A, by positivity, fun k N R hN hR => ?_⟩
  let L := Nat.log 2 N
  let T : Finset (pairs k L) := univ.filter (fun x => dif x ≠ 0)
  have hNpow : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hsize (x : pairs k L) : (dif x).natAbs ≤ k * N := by
    have hν := (LeanLab.Linnik.U1434Lemma21.sv_le x.1).trans (Nat.mul_le_mul_left k hNpow)
    have hμ := (LeanLab.Linnik.U1434Lemma21.sv_le x.2).trans (Nat.mul_le_mul_left k hNpow)
    dsimp [dif]
    omega
  have hpoint (x : pairs k L) (hx : x ∈ T) :
      ‖singSeries (dif x) - ∑ q ∈ Icc 1 R,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)‖ ≤
      (192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ) := by
    have hn := (mem_filter.mp hx).2
    have hnpos := Int.natAbs_pos.mpr hn
    have hc := hτ (dif x).natAbs (by omega)
    have hmon : ((dif x).natAbs : ℝ) ^ ((m : ℝ)⁻¹) ≤ ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsize x) (by positivity)
    have hd := hc.trans (mul_le_mul_of_nonneg_left hmon hA.le)
    exact (singular_series_truncation_le hn hR).trans
      (by apply div_le_div_of_nonneg_right _ (by positivity); nlinarith)
  have hcard : (T.card : ℝ) ≤ (L : ℝ) ^ (2 * k) := by
    calc
      _ ≤ (Fintype.card (pairs k L) : ℝ) := by
        have hc : T.card ≤ (univ : Finset (pairs k L)).card := card_filter_le _ _
        exact_mod_cast hc
      _ = _ := by simp [pairs, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add, two_mul]
  have hswap : (∑ q ∈ Icc 1 R,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x ∈ T, ramanujanSum q (dif x)) =
      ∑ x ∈ T, ∑ q ∈ Icc 1 R,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x) := by
    simp_rw [mul_sum]
    rw [sum_comm]
  change ‖(∑ x ∈ T, _) - (∑ q ∈ Icc 1 R, _)‖ ≤ _
  rw [hswap, ← sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ T, ‖singSeries (dif x) - ∑ q ∈ Icc 1 R,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _x ∈ T, (192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ) := sum_le_sum hpoint
    _ = (T.card : ℝ) * ((192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ)) := by simp
    _ ≤ (L : ℝ) ^ (2 * k) * ((192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 pp.134 and 135. The moving cutoff N to power one over k makes the normalized tuple truncation error vanish. -/
theorem tuple_truncation_eventually {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ‖(∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x)) -
          ∑ q ∈ Icc 1 ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊,
            ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
              ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)‖ ≤
      δ * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  obtain ⟨C, hC, hbound⟩ := tuple_singular_truncation_bound (4 * k) (by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  let e : ℝ := ((4 * k : ℕ) : ℝ)⁻¹
  let t : ℝ := (k : ℝ)⁻¹ * (3 / 4)
  have he : e - t = -((2 * (k : ℝ))⁻¹) := by
    dsimp [e, t]
    push_cast
    field_simp
    ring
  have hlim : Tendsto (fun N : ℕ => C * (k : ℝ) ^ e * (N : ℝ) ^ (-((2 * (k : ℝ))⁻¹)))
      atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop (show 0 < (2 * (k : ℝ))⁻¹ by positivity)).comp
      tendsto_natCast_atTop_atTop).const_mul (C * (k : ℝ) ^ e)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  refine ⟨max N0 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNbase : N0 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let R : ℕ := ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊
  have hR : 0 < R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hNpos _)
  have hden : (N : ℝ) ^ t ≤ (R : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ = ((N : ℝ) ^ ((k : ℝ)⁻¹)) ^ (3 / 4 : ℝ) := Real.rpow_mul hNpos.le _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) (by norm_num)
  have hratio : C * ((k * N : ℕ) : ℝ) ^ e / (R : ℝ) ^ (3 / 4 : ℝ) ≤
      C * (k : ℝ) ^ e * (N : ℝ) ^ (-((2 * (k : ℝ))⁻¹)) := by
    calc
      _ ≤ C * ((k * N : ℕ) : ℝ) ^ e / (N : ℝ) ^ t :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNpos _) hden
      _ = (C * (k : ℝ) ^ e) * ((N : ℝ) ^ e / (N : ℝ) ^ t) := by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg N)]
        ring
      _ = (C * (k : ℝ) ^ e) * (N : ℝ) ^ (e - t) := by rw [Real.rpow_sub hNpos]
      _ = _ := by rw [he]
  have hh := hbound k N R hN2 hR
  change ‖_‖ ≤ C * ((k * N : ℕ) : ℝ) ^ e * (Nat.log 2 N : ℝ) ^ (2 * k) / (R : ℝ) ^ (3 / 4 : ℝ) at hh
  change ‖_‖ ≤ δ * (Nat.log 2 N : ℝ) ^ (2 * k)
  calc
    _ ≤ _ := hh
    _ = (C * ((k * N : ℕ) : ℝ) ^ e / (R : ℝ) ^ (3 / 4 : ℝ)) * (Nat.log 2 N : ℝ) ^ (2 * k) := by ring
    _ ≤ (C * (k : ℝ) ^ e * (N : ℝ) ^ (-((2 * (k : ℝ))⁻¹))) * (Nat.log 2 N : ℝ) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hN0 N hNbase).le (by positivity)

/-- Gallagher 1975 p.135. The complete natural residue grid has the proved modular moment bound. -/
theorem complete_nat_grid_moment_le {q : ℕ} (hq : 0 < q) (ho : Odd q) {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    ∑ a ∈ range q, ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) ≤
      q * ((L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1)) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have heq : (∑ a ∈ range q, ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) =
      ∑ a : ZMod q, ‖Gs L ((a.val : ℝ) / q)‖ ^ (2 * k) := by
    apply sum_bij (fun (a : ℕ) (_ : a ∈ range q) => (a : ZMod q))
    · intro a ha; exact mem_univ _
    · intro a ha b hb hab
      have hh := congrArg ZMod.val hab
      simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha), ZMod.val_natCast_of_lt (mem_range.mp hb)] using hh
    · intro a ha
      exact ⟨a.val, mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha
      rw [ZMod.val_natCast_of_lt (mem_range.mp ha)]
  rw [heq]
  exact LeanLab.Linnik.Decomp1532a.Gs_grid_moment_le ho hk L

/-- Gallagher 1975 p.135. Reduced natural residues inherit a uniform small order moment gap. -/
theorem primitive_nat_grid_moment_le {q E L : ℕ} (hq : 1 < q) (ho : Odd q)
    (hE : 2 ≤ E) (heE : ordTwo q ≤ E) (hEL : E ≤ L) (k : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) ≤
      q.totient * (((1 - 1 / (16 * (E : ℝ))) * L) ^ (2 * k)) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have he2 : 2 ≤ ordTwo q := by
    have hepos := LeanLab.Linnik.Decomp1532a.ordTwo_pos ho
    by_contra hh
    have he1 : ordTwo q = 1 := by omega
    have hd := LeanLab.Linnik.Decomp1532a.dvd_two_pow_ordTwo_sub_one ho
    rw [he1] at hd
    have hq1 : q = 1 := by simpa using hd
    omega
  have hEp : (0 : ℝ) < E := by exact_mod_cast (by omega : 0 < E)
  have hep : (0 : ℝ) < ordTwo q := by exact_mod_cast (by omega : 0 < ordTwo q)
  have hdiv : 1 / (16 * (E : ℝ)) ≤ 1 / (16 * (ordTwo q : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast heE) (by norm_num))
  have hgap : (1 - 1 / (16 * (ordTwo q : ℝ))) * L ≤ (1 - 1 / (16 * (E : ℝ))) * L :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg L)
  have hpoint (a : ℕ) (ha : a ∈ (range q).filter (fun a => Nat.Coprime a q)) :
      ‖Gs L ((a : ℝ) / q)‖ ≤ (1 - 1 / (16 * (E : ℝ))) * L := by
    obtain ⟨haq, hac⟩ := mem_filter.mp ha
    have hg := (LeanLab.Linnik.Decomp1532a.rational_power_gap ho (ZMod.unitOfCoprime a hac) he2
      (heE.trans hEL)).le
    have hh : ‖Gs L ((a : ℝ) / q)‖ ≤ (1 - 1 / (16 * (ordTwo q : ℝ))) * L := by
      simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (mem_range.mp haq)] using hg
    exact hh.trans hgap
  have hc : #((range q).filter (fun a => Nat.Coprime a q)) = q.totient := by
    simp [Nat.totient, Nat.coprime_comm]
  calc
    _ ≤ ∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (((1 - 1 / (16 * (E : ℝ))) * L) ^ (2 * k)) := by
      apply sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _) (hpoint a ha) _
    _ = _ := by simp [hc]

/-- Gallagher 1975 p.135. The two finite order ranges have a uniform E and R bound. -/
theorem odd_moment_order_split : ∃ C : ℝ, 0 < C ∧ ∀ k L R E : ℕ,
    1 ≤ k → 2 ≤ R → 2 ≤ E → E ≤ L →
      (∑ q ∈ Icc 3 R with Odd q,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) ≤
      C * (L : ℝ) ^ (2 * k) *
        (Real.log E / E + (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E) +
      Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log R := by
  classical
  obtain ⟨A, hA⟩ := LeanLab.Linnik.Decomp1532a.lemma4
  obtain ⟨B, hB⟩ := LeanLab.Linnik.Decomp1532a.order_weight_tail_log
  let C := |A| + |B| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith [le_abs_self A, abs_nonneg B]
  have hBC : B ≤ C := by dsimp [C]; linarith [le_abs_self B, abs_nonneg A]
  refine ⟨C, hC, fun k L R E hk hR hE hEL => ?_⟩
  let S := (Icc 3 R).filter Odd
  let Slo := S.filter (fun q => ordTwo q ≤ E)
  let Shi := S.filter (fun q => ¬ ordTwo q ≤ E)
  let w : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2
  let v : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2
  let H : ℕ → ℝ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)
  let G : ℝ := (1 - 1 / (16 * (E : ℝ))) * L
  have hlogE : 0 ≤ Real.log (E : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E))
  have hEp : (0 : ℝ) < E := by exact_mod_cast (by omega : 0 < E)
  have hgap0 : 0 ≤ 1 - 1 / (16 * (E : ℝ)) := by
    have hEr : (2 : ℝ) ≤ E := by exact_mod_cast hE
    have hh : 1 / (16 * (E : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hG0 : 0 ≤ G := mul_nonneg hgap0 (Nat.cast_nonneg L)
  have hw0 (q : ℕ) : 0 ≤ w q := by dsimp [w]; positivity
  have hv0 (q : ℕ) : 0 ≤ v q := by dsimp [v]; positivity
  have hlowpoint (q : ℕ) (hq : q ∈ Slo) : v q * H q ≤ w q * G ^ (2 * k) := by
    obtain ⟨hqS, hqe⟩ := mem_filter.mp hq
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
    have hq3 := (mem_Icc.mp hqI).1
    have hm := primitive_nat_grid_moment_le (by omega : 1 < q) hqo hE hqe hEL k
    have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    calc
      _ ≤ v q * ((q.totient : ℝ) * G ^ (2 * k)) := mul_le_mul_of_nonneg_left hm (hv0 q)
      _ ≤ v q * ((q : ℝ) * G ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ (pow_nonneg hG0 _)) (hv0 q)
      _ = _ := by dsimp [v, w]; ring
  have hlowcoeff : ∑ q ∈ Slo, w q ≤ C * Real.log E := by
    have hsub : Slo ⊆ (Icc 1 R).filter (fun q => Odd q ∧ ordTwo q ≤ E) := by
      intro q hq
      obtain ⟨hqS, hqe⟩ := mem_filter.mp hq
      obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hqI).1; omega, (mem_Icc.mp hqI).2⟩, hqo, hqe⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)).trans
      ((hA E hE R).trans (mul_le_mul_of_nonneg_right hAC hlogE))
  have hlow : (∑ q ∈ Slo, v q * H q) ≤ C * Real.log E * G ^ (2 * k) := by
    calc
      _ ≤ ∑ q ∈ Slo, w q * G ^ (2 * k) := sum_le_sum hlowpoint
      _ = (∑ q ∈ Slo, w q) * G ^ (2 * k) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hlowcoeff (pow_nonneg hG0 _)
  have hhighpoint (q : ℕ) (hq : q ∈ Shi) : v q * H q ≤
      (L : ℝ) ^ (2 * k) * (w q / ordTwo q) + (L : ℝ) ^ (2 * k - 1) * w q := by
    have hqS := (mem_filter.mp hq).1
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
    have hq3 := (mem_Icc.mp hqI).1
    have hfull : H q ≤ ∑ a ∈ range q, ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    have hm := complete_nat_grid_moment_le (by omega : 0 < q) hqo hk L
    calc
      _ ≤ v q * ((q : ℝ) * ((L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1))) :=
        mul_le_mul_of_nonneg_left (hfull.trans hm) (hv0 q)
      _ = _ := by dsimp [v, w]; ring
  have htail : (∑ q ∈ Shi, w q / ordTwo q) ≤ C * Real.log E / E := by
    have he : Shi = (Icc 3 R).filter (fun q => Odd q ∧ E < ordTwo q) := by
      ext q
      simp only [Shi, S, mem_filter, not_le]
      tauto
    rw [he]
    exact (hB E hE (Icc 3 R)).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hlogE) hEp.le)
  have hhighcoeff : ∑ q ∈ Shi, w q ≤ Real.exp 24 * Real.log R := by
    have hsub : Shi ⊆ (Icc 1 R).filter Odd := by
      intro q hq
      obtain ⟨hqS, _⟩ := mem_filter.mp hq
      obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hqI).1; omega, (mem_Icc.mp hqI).2⟩, hqo⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)).trans
      (LeanLab.Linnik.Decomp1532a.totient_square_sum_le_log hR)
  have hhigh : (∑ q ∈ Shi, v q * H q) ≤
      (L : ℝ) ^ (2 * k) * (C * Real.log E / E) +
        (L : ℝ) ^ (2 * k - 1) * (Real.exp 24 * Real.log R) := by
    calc
      _ ≤ ∑ q ∈ Shi, ((L : ℝ) ^ (2 * k) * (w q / ordTwo q) + (L : ℝ) ^ (2 * k - 1) * w q) := sum_le_sum hhighpoint
      _ = (L : ℝ) ^ (2 * k) * (∑ q ∈ Shi, w q / ordTwo q) + (L : ℝ) ^ (2 * k - 1) * ∑ q ∈ Shi, w q := by
        rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left htail (by positivity))
        (mul_le_mul_of_nonneg_left hhighcoeff (by positivity))
  have heq : (∑ q ∈ S, v q * H q) = (∑ q ∈ Slo, v q * H q) + ∑ q ∈ Shi, v q * H q :=
    (sum_filter_add_sum_filter_not S (fun q => ordTwo q ≤ E) (fun q => v q * H q)).symm
  change (∑ q ∈ S, v q * H q) ≤ _
  rw [heq]
  calc
    _ ≤ C * Real.log E * G ^ (2 * k) +
        ((L : ℝ) ^ (2 * k) * (C * Real.log E / E) + (L : ℝ) ^ (2 * k - 1) * (Real.exp 24 * Real.log R)) :=
      add_le_add hlow hhigh
    _ = _ := by dsimp [G]; rw [mul_pow]; ring

/-- Gallagher 1975 p.135. Choosing the order cutoff proportional to k over log k gives the stated error scale. -/
theorem order_parameter_choice : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
    ∃ E : ℕ, 2 ≤ E ∧ E ≤ k ∧
      Real.log E / E + (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E ≤
        C * (Real.log k ^ 2 / k) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := 65536 / Real.log (2 : ℝ) ^ 2 + 65
  have hC : 0 < C := by dsimp [C]; positivity
  have hC65 : 65 ≤ C := by
    dsimp [C]
    have hd : 0 ≤ 65536 / Real.log (2 : ℝ) ^ 2 := by positivity
    linarith
  refine ⟨C, hC, fun k hk => ?_⟩
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlk : Real.log (2 : ℝ) ≤ Real.log k := Real.log_le_log (by norm_num) hkR
  have hlk0 : 0 < Real.log (k : ℝ) := hl2.trans_le hlk
  by_cases hlarge : 16384 ≤ k
  · have hkbig : (16384 : ℝ) ≤ k := by exact_mod_cast hlarge
    have hlk1 : 1 ≤ Real.log (k : ℝ) := by
      apply le_of_lt
      rw [Real.lt_log_iff_exp_lt hk0]
      linarith [Real.exp_one_lt_d9]
    have hroot : (128 : ℝ) ≤ Real.sqrt k := Real.le_sqrt_of_sq_le (by nlinarith)
    have hlogroot : Real.log (k : ℝ) ≤ 2 * Real.sqrt k := by
      have hh := Real.log_le_rpow_div (Nat.cast_nonneg k) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at hh
      linarith
    have h64 : 64 * Real.log (k : ℝ) ≤ k := by
      have hp := mul_nonneg (sub_nonneg.mpr hroot) (Real.sqrt_nonneg (k : ℝ))
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg k)]
    let x : ℝ := (k : ℝ) / (32 * Real.log k)
    let E : ℕ := ⌊x⌋₊
    have hx2 : 2 ≤ x := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hE2 : 2 ≤ E := Nat.le_floor hx2
    have hEreal : (2 : ℝ) ≤ E := by exact_mod_cast hE2
    have hEp : (0 : ℝ) < E := by linarith
    have hElo : (E : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hEhalf : x / 2 ≤ E := by
      have hh := Nat.lt_floor_add_one x
      change x < (E : ℝ) + 1 at hh
      linarith
    have hxk : x ≤ k := div_le_self hk0.le (by linarith)
    have hEk : E ≤ k := by exact_mod_cast hElo.trans hxk
    have hElog : Real.log (E : ℝ) ≤ Real.log k := Real.log_le_log hEp (by exact_mod_cast hEk)
    have hElog0 : 0 ≤ Real.log (E : ℝ) := Real.log_nonneg (by linarith)
    have hEden : (k : ℝ) / (64 * Real.log k) ≤ E := by
      calc _ = x / 2 := by dsimp [x]; ring
           _ ≤ _ := hEhalf
    have hmain : Real.log (E : ℝ) / E ≤ 64 * Real.log k ^ 2 / k := by
      calc
        _ ≤ Real.log (k : ℝ) / E := div_le_div_of_nonneg_right hElog hEp.le
        _ ≤ Real.log (k : ℝ) / ((k : ℝ) / (64 * Real.log k)) :=
          div_le_div_of_nonneg_left hlk0.le (by positivity) hEden
        _ = _ := by field_simp
    have hgap0 : 0 ≤ 1 - 1 / (16 * (E : ℝ)) := by
      have hh : 1 / (16 * (E : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      linarith
    have hbase : 1 - 1 / (16 * (E : ℝ)) ≤ Real.exp (-1 / (16 * (E : ℝ))) := by
      simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-1 / (16 * (E : ℝ)))
    have hprod : (E : ℝ) * (32 * Real.log k) ≤ k := (le_div_iff₀ (by positivity)).mp hElo
    have hexponent : -(k : ℝ) / (8 * E) ≤ -4 * Real.log k := by
      have hh : 4 * Real.log k ≤ (k : ℝ) / (8 * E) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
      simpa only [neg_div, neg_mul] using neg_le_neg hh
    have hpow : (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) ≤ 1 / (k : ℝ) := by
      calc
        _ ≤ Real.exp (-1 / (16 * (E : ℝ))) ^ (2 * k) := pow_le_pow_left₀ hgap0 hbase _
        _ = Real.exp (-(k : ℝ) / (8 * E)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        _ ≤ Real.exp (-4 * Real.log k) := Real.exp_le_exp.mpr hexponent
        _ = (k : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_def_of_pos hk0]; congr 1; ring
        _ ≤ (k : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ k by linarith) (by norm_num)
        _ = _ := by simp only [Real.rpow_neg_one, one_div]
    have hsmall : (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E ≤ Real.log k ^ 2 / k := by
      calc
        _ ≤ (1 / (k : ℝ)) * Real.log k := mul_le_mul hpow hElog hElog0 (by positivity)
        _ = Real.log k / k := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hk0.le
    refine ⟨E, hE2, hEk, ?_⟩
    calc
      _ ≤ 65 * (Real.log k ^ 2 / k) := by
        calc
          _ ≤ 64 * Real.log k ^ 2 / k + Real.log k ^ 2 / k := add_le_add hmain hsmall
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC65 (by positivity)
  · have hksmall : (k : ℝ) ≤ 16384 := by exact_mod_cast (by omega : k ≤ 16384)
    have hsq : Real.log (2 : ℝ) ^ 2 ≤ Real.log k ^ 2 := pow_le_pow_left₀ hl2.le hlk 2
    have hCprod : 65536 ≤ C * Real.log k ^ 2 := by
      calc
        _ = (65536 / Real.log (2 : ℝ) ^ 2) * Real.log (2 : ℝ) ^ 2 := by field_simp
        _ ≤ (65536 / Real.log (2 : ℝ) ^ 2) * Real.log k ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _)
    have htarget : 2 ≤ C * (Real.log k ^ 2 / k) := by
      rw [← mul_div_assoc, le_div_iff₀ hk0]
      nlinarith
    have hpow : (1 - 1 / (16 * (2 : ℝ))) ^ (2 * k) ≤ 1 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 - 1 / (16 * 2))
        (by norm_num : 1 - 1 / (16 * (2 : ℝ)) ≤ 1) (2 * k)
    have hl2le : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh : Real.log (2 : ℝ) / 2 + (1 - 1 / (16 * (2 : ℝ))) ^ (2 * k) * Real.log 2 ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_right hpow hl2.le
      nlinarith
    exact ⟨2, le_rfl, hk, hh.trans htarget⟩

/-- Gallagher 1975 p.134. At even frequencies the singular coefficients at odd q and twice q agree. -/
theorem singular_coefficient_double_even {r : ℕ} (hr : Odd r) {n : ℤ} (hn : Even n) :
    ((ArithmeticFunction.moebius (2 * r) : ℤ) : ℂ) ^ 2 / ((2 * r).totient : ℂ) ^ 2 * ramanujanSum (2 * r) n =
      ((ArithmeticFunction.moebius r : ℤ) : ℂ) ^ 2 / (r.totient : ℂ) ^ 2 * ramanujanSum r n := by
  by_cases hsf : Squarefree r
  · have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
    have hsf2 : Squarefree (2 * r) := (Nat.squarefree_mul hcop).mpr ⟨Nat.squarefree_two, hsf⟩
    obtain ⟨t, ht⟩ : ∃ t : ℕ, n.natAbs = 2 * t := by
      obtain ⟨t, ht⟩ := Int.natAbs_even.mpr hn
      exact ⟨t, by omega⟩
    have hcancel : Nat.gcd r (2 * t) = Nat.gcd r t := by
      simpa [Nat.gcd_comm] using hcop.gcd_mul_left_cancel t
    have hg : Nat.gcd (2 * r) n.natAbs = 2 * Nat.gcd r n.natAbs := by
      rw [ht, Nat.gcd_mul_left, hcancel]
    have hgodd : Odd (Nat.gcd r n.natAbs) := hr.of_dvd_nat (Nat.gcd_dvd_left r n.natAbs)
    have hquot : (2 * r) / (2 * Nat.gcd r n.natAbs) = r / Nat.gcd r n.natAbs :=
      Nat.mul_div_mul_left r (Nat.gcd r n.natAbs) (by decide)
    have hm1 : ((ArithmeticFunction.moebius r : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hm2 : ((ArithmeticFunction.moebius (2 * r) : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf2
    rw [ramanujanSum_squarefree hsf2 n, ramanujanSum_squarefree hsf n, hg, hquot,
      Nat.totient_mul hcop, Nat.totient_two_mul_of_odd hgodd, hm1, hm2]
    norm_num
  · have hsf2 : ¬ Squarefree (2 * r) := fun h => hsf h.of_mul_right
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf2]

/-- Gallagher 1975 p.134. Finite parity pairing costs at most a factor two and a doubled cutoff. -/
theorem finite_parity_pair_bound (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q)
    (hfour : ∀ q, A (4 * q) = 0) (hdouble : ∀ q, Odd q → A (2 * q) = A q)
    {R : ℕ} (hR : 1 ≤ R) :
    ∑ q ∈ Icc 1 R, A q ≤ 2 * ∑ q ∈ Icc 1 (2 * R) with Odd q, A q := by
  classical
  let O := (Icc 1 R).filter Odd
  let V := (Icc 1 R).filter (fun q => ¬ Odd q)
  let G := V.filter (fun q => Odd (q / 2))
  let T := (Icc 1 (2 * R)).filter Odd
  have heven (q : ℕ) (hq : q ∈ V) : 2 * (q / 2) = q := by
    have hn := (mem_filter.mp hq).2
    have he : Even q := (Nat.even_or_odd q).resolve_right hn
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp he)
  have hpoint (q : ℕ) (hq : q ∈ V) : A q = if Odd (q / 2) then A (q / 2) else 0 := by
    have hq2 := heven q hq
    by_cases ho : Odd (q / 2)
    · rw [ite_eq_left ho]
      calc _ = A (2 * (q / 2)) := congrArg A hq2.symm
           _ = _ := hdouble _ ho
    · rw [ite_eq_right ho]
      obtain ⟨u, hu⟩ := (Nat.even_or_odd (q / 2)).resolve_right ho
      have hh : q = 4 * u := by omega
      rw [hh, hfour]
  have hinj : Set.InjOn (fun q : ℕ => q / 2) (G : Set ℕ) := by
    intro a ha b hb hab
    have h1 := heven a (mem_filter.mp ha).1
    have h2 := heven b (mem_filter.mp hb).1
    change a / 2 = b / 2 at hab
    omega
  have hsub : G.image (fun q => q / 2) ⊆ T := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
    obtain ⟨hqV, hqo⟩ := mem_filter.mp hq
    have hqI := (mem_filter.mp hqV).1
    have hq2 := heven q hqV
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hqI).1; omega, ?_⟩, hqo⟩
    have hqR := (mem_Icc.mp hqI).2
    have hhalf := Nat.div_le_self q 2
    omega
  have heq : (∑ q ∈ V, A q) = ∑ r ∈ G.image (fun q => q / 2), A r := by
    rw [sum_congr rfl hpoint, ← sum_filter, sum_image hinj]
  have hV : (∑ q ∈ V, A q) ≤ ∑ q ∈ T, A q :=
    heq.trans_le (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hA q))
  have hO : (∑ q ∈ O, A q) ≤ ∑ q ∈ T, A q := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hA q)
    intro q hq
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hqI).1, by have := (mem_Icc.mp hqI).2; omega⟩, hqo⟩
  have hs := sum_filter_add_sum_filter_not (Icc 1 R) Odd A
  change (∑ q ∈ O, A q) + (∑ q ∈ V, A q) = _ at hs
  rw [← hs]
  change _ ≤ 2 * ∑ q ∈ T, A q
  linarith

/-- Gallagher 1975 p.135. The moving cutoff has the logarithmic size needed in the order split. -/
theorem l6_cutoff_bounds {k N : ℕ} (hk : 2 ≤ k) (hN : 2 ^ k ≤ N) :
    k ≤ Nat.log 2 N ∧ 2 ≤ ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊ ∧
      Real.log ((2 * ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊ : ℕ) : ℝ) ≤
        4 * Real.log 2 * (Nat.log 2 N : ℝ) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hN2 : 2 ≤ N := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
         _ ≤ N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let L := Nat.log 2 N
  let x : ℝ := (N : ℝ) ^ ((k : ℝ)⁻¹)
  let R : ℕ := ⌈x⌉₊
  have hL : k ≤ L := Nat.le_log_of_pow_le (by norm_num) hN
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hx2 : 2 ≤ x := by
    calc
      _ = ((2 : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (by norm_num) (by omega : k ≠ 0)).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by positivity)
  have hR2 : 2 ≤ R := by exact_mod_cast hx2.trans (Nat.le_ceil x)
  have hRup : (R : ℝ) ≤ 2 * x := by
    have hh : (R : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hNlog : Real.log (N : ℝ) ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have hb : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le
    have hh := Real.log_le_log hN0 hb
    rw [Real.log_pow] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have h4log : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hxlog : Real.log x = (k : ℝ)⁻¹ * Real.log N := Real.log_rpow hN0 _
  have hlogR : Real.log ((2 * R : ℕ) : ℝ) ≤ 2 * Real.log 2 + (k : ℝ)⁻¹ * Real.log N := by
    have hp : (0 : ℝ) < ((2 * R : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * R)
    have hb : ((2 * R : ℕ) : ℝ) ≤ 4 * x := by push_cast; linarith
    have hh := Real.log_le_log hp hb
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx0.ne', h4log, hxlog] at hh
    exact hh
  refine ⟨hL, hR2, ?_⟩
  change Real.log ((2 * R : ℕ) : ℝ) ≤ 4 * Real.log 2 * (L : ℝ) / k
  rw [le_div_iff₀ hk0]
  have hh := mul_le_mul_of_nonneg_right hlogR hk0.le
  have he : (2 * Real.log 2 + (k : ℝ)⁻¹ * Real.log N) * k = 2 * Real.log 2 * k + Real.log N := by
    field_simp <;> ring
  rw [he] at hh
  have hkL : (k : ℝ) ≤ L := by exact_mod_cast hL
  have hm := mul_le_mul_of_nonneg_left hkL (show 0 ≤ 2 * Real.log 2 by positivity)
  have hlN : Real.log (N : ℝ) ≤ 2 * L * Real.log 2 := by nlinarith
  nlinarith

/-- Gallagher 1975 p.135. The finite logarithm error is absorbed at the final k scale. -/
theorem l6_log_error_le {k L Q : ℕ} (hk : 2 ≤ k)
    (hlog : Real.log (Q : ℝ) ≤ 4 * Real.log 2 * (L : ℝ) / k) :
    Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log Q ≤
      (4 * Real.exp 24 / Real.log 2) * (Real.log k ^ 2 / k) * (L : ℝ) ^ (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogk : Real.log (2 : ℝ) ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hsq : Real.log (2 : ℝ) ^ 2 ≤ Real.log k ^ 2 := pow_le_pow_left₀ hl2.le hlogk 2
  have hcoef : 4 * Real.exp 24 * Real.log 2 / k ≤
      (4 * Real.exp 24 / Real.log 2) * (Real.log k ^ 2 / k) := by
    calc
      _ = (4 * Real.exp 24 / Real.log 2) * (Real.log (2 : ℝ) ^ 2 / k) := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq hk0.le) (by positivity)
  have hp : (L : ℝ) ^ (2 * k - 1) * L = (L : ℝ) ^ (2 * k) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ ≤ Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * (4 * Real.log 2 * L / k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (4 * Real.exp 24 * Real.log 2 / k) * ((L : ℝ) ^ (2 * k - 1) * L) := by ring
    _ = (4 * Real.exp 24 * Real.log 2 / k) * (L : ℝ) ^ (2 * k) := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- Gallagher 1975 pp.134 and 135. The restored weighted tuple sum is a nonnegative real rational moment. -/
theorem ramanujan_moment_coefficient (q k L : ℕ) :
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        (∑ x : pairs k L, ramanujanSum q (dif x)) =
      ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) : ℝ) : ℂ) := by
  rw [ramanujan_tuple_sum_eq, ← Complex.ofReal_sum]
  push_cast <;> rfl

/-- Gallagher 1975 p.134. The finite zero frequency contribution is its tuple count times the reciprocal totient coefficient sum. -/
theorem finite_singular_diagonal_eq (k L : ℕ) (S : Finset ℕ) :
    (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) =
    (((#{x : pairs k L | dif x = 0} : ℝ) *
      (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
  classical
  let D := #{x : pairs k L | dif x = 0}
  have hinner (q : ℕ) : (∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) = (D : ℂ) * q.totient := by
    calc
      _ = ∑ _x : pairs k L with dif _x = 0, (q.totient : ℂ) := by
        apply sum_congr rfl
        intro x hx
        rw [(mem_filter.mp hx).2, ramanujanSum_zero]
      _ = _ := by simp [D, nsmul_eq_mul]
  have hterm (q : ℕ) :
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x) =
      (((D : ℝ) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
    by_cases hq : q = 0
    · simp [hq]
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
    rw [hinner]
    push_cast
    field_simp
  rw [sum_congr rfl (fun q _ => hterm q), ← Complex.ofReal_sum, ← mul_sum]

/-- Gallagher 1975 p.134. The rational moment has the parity pairing and its first main term. -/
theorem rational_moment_parity (k L : ℕ) :
    let A : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)
    (∀ q, 0 ≤ A q) ∧ (∀ q, A (4 * q) = 0) ∧
      (∀ q, Odd q → A (2 * q) = A q) ∧ A 1 = (L : ℝ) ^ (2 * k) := by
  classical
  dsimp only
  refine ⟨fun q => by positivity, ?_, ?_, ?_⟩
  · intro q
    have hs : ¬ Squarefree (4 * q) := by
      intro h
      exact (by norm_num : ¬ IsUnit (2 : ℕ)) (h 2 (by omega))
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · intro q hq
    apply Complex.ofReal_injective
    rw [← ramanujan_moment_coefficient, ← ramanujan_moment_coefficient, mul_sum, mul_sum]
    apply sum_congr rfl
    intro x hx
    apply singular_coefficient_double_even hq
    have h1 : Even (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℤ) := by
      exact_mod_cast (Nat.even_iff.mpr (LeanLab.Linnik.U1434Lemma21.sv_even x.1))
    have h2 : Even (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℤ) := by
      exact_mod_cast (Nat.even_iff.mpr (LeanLab.Linnik.U1434Lemma21.sv_even x.2))
    exact h1.sub h2
  · apply Complex.ofReal_injective
    rw [← ramanujan_moment_coefficient, ramanujan_tuple_sum_one]
    push_cast
    simp

/-- Gallagher 1975 p.134. The diagonal reciprocal totient coefficient has the same parity pairing. -/
theorem reciprocal_totient_parity :
    let B : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)
    (∀ q, 0 ≤ B q) ∧ (∀ q, B (4 * q) = 0) ∧ (∀ q, Odd q → B (2 * q) = B q) := by
  refine ⟨fun q => by positivity, ?_, ?_⟩
  · intro q
    have hs : ¬ Squarefree (4 * q) := by
      intro h
      exact (by norm_num : ¬ IsUnit (2 : ℕ)) (h 2 (by omega))
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · intro q hq
    have hc : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq
    dsimp only
    rw [Nat.totient_mul hc, Nat.totient_two, one_mul]
    by_cases hs : Squarefree q
    · have hs2 : Squarefree (2 * q) := (Nat.squarefree_mul hc).mpr ⟨Nat.squarefree_two, hs⟩
      rw [show ((ArithmeticFunction.moebius (2 * q) : ℤ) : ℝ) ^ 2 = 1 by exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs2),
        show ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = 1 by exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs)]
    · have hs2 : ¬ Squarefree (2 * q) := fun h => hs h.of_mul_right
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs2]

/-- Gallagher 1975 pp.134 and 135. The growing finite truncation has the required main term estimate. -/
theorem finite_singular_main_bound : ∃ C : ℝ, 0 < C ∧ ∀ k N : ℕ, 2 ≤ k → 2 ^ k ≤ N →
    ‖(∑ q ∈ Icc 1 ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)) -
      2 * (Nat.log 2 N : ℂ) ^ (2 * k)‖ ≤
      C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C₁, hC₁, hsplit⟩ := odd_moment_order_split
  obtain ⟨C₂, hC₂, hparam⟩ := order_parameter_choice
  let D : ℝ := 4 * Real.exp 24 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨2 * C₁ * C₂ + 6 * D, by positivity, fun k N hk hN => ?_⟩
  let L := Nat.log 2 N
  let R := ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊
  let Q := 2 * R
  let a : ℝ := Real.log k ^ 2 / k
  let P : ℝ := (L : ℝ) ^ (2 * k)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨hkL, hR, hlog⟩ := l6_cutoff_bounds hk hN
  have hQ : 2 ≤ Q := by dsimp [Q]; omega
  obtain ⟨E, hE, hEk, hchoice⟩ := hparam k hk
  have hEL : E ≤ L := hEk.trans hkL
  let A : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)
  let B : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)
  obtain ⟨hA0, hA4, hA2, hA1⟩ := rational_moment_parity k L
  obtain ⟨hB0, hB4, hB2⟩ := reciprocal_totient_parity
  have hoddset : (Icc 1 Q).filter Odd = insert 1 ((Icc 3 Q).filter Odd) := by
    ext q
    simp only [mem_filter, mem_Icc, mem_insert]
    constructor
    · rintro ⟨⟨h1, hQq⟩, ho⟩
      by_cases he : q = 1
      · exact Or.inl he
      · right
        have hne : q ≠ 2 := by intro h; subst q; norm_num at ho
        exact ⟨⟨by omega, hQq⟩, ho⟩
    · rintro (rfl | ⟨⟨h3, hQq⟩, ho⟩)
      · exact ⟨⟨by omega, by omega⟩, by decide⟩
      · exact ⟨⟨by omega, hQq⟩, ho⟩
  have hodd : (∑ q ∈ (Icc 1 Q).filter Odd, A q) = P + ∑ q ∈ (Icc 3 Q).filter Odd, A q := by
    rw [hoddset, sum_insert (by simp)]
    rw [show A 1 = P from hA1]
  have herror := l6_log_error_le (L := L) (Q := Q) hk hlog
  change Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log Q ≤ D * a * P at herror
  have hoddle : (∑ q ∈ (Icc 3 Q).filter Odd, A q) ≤ (C₁ * C₂ + D) * a * P := by
    have hh := hsplit k L Q E (by omega) hQ hE hEL
    change (∑ q ∈ (Icc 3 Q).filter Odd, A q) ≤ _ at hh
    have hm := mul_le_mul_of_nonneg_left hchoice (show 0 ≤ C₁ * P by positivity)
    change C₁ * P * (Real.log E / E + (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E) ≤ C₁ * P * (C₂ * a) at hm
    change (∑ q ∈ (Icc 3 Q).filter Odd, A q) ≤ C₁ * P * _ + _ at hh
    nlinarith
  have hSupper : (∑ q ∈ Icc 1 R, A q) - 2 * P ≤ 2 * (C₁ * C₂ + D) * a * P := by
    have hh := finite_parity_pair_bound A hA0 hA4 hA2 (by omega : 1 ≤ R)
    change (∑ q ∈ Icc 1 R, A q) ≤ 2 * ∑ q ∈ (Icc 1 Q).filter Odd, A q at hh
    rw [hodd] at hh
    linarith
  have hSlower : 2 * P ≤ ∑ q ∈ Icc 1 R, A q := by
    have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 R := by intro q hq; simp only [mem_insert, mem_singleton] at hq; rcases hq with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hh := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hA0 q)
    have hA2one : A 2 = P := (hA2 1 (by decide)).trans hA1
    rw [sum_pair (by decide)] at hh
    change A 1 + A 2 ≤ _ at hh
    rw [show A 1 = P from hA1, hA2one] at hh
    linarith
  have hrest : ‖(∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k)‖ ≤ 2 * (C₁ * C₂ + D) * a * P := by
    have heq : (∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k) =
      (((∑ q ∈ Icc 1 R, A q) - 2 * P : ℝ) : ℂ) := by
      rw [sum_congr rfl (fun q _ => ramanujan_moment_coefficient q k L)]
      simp only [A, P, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_sum]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hSlower)]
    exact hSupper
  have hBsum : (∑ q ∈ Icc 1 R, B q) ≤ 2 * Real.exp 24 * Real.log Q := by
    have hh := finite_parity_pair_bound B hB0 hB4 hB2 (by omega : 1 ≤ R)
    have hb := reciprocal_totient_sum_le_log hQ
    change (∑ q ∈ (Icc 1 Q).filter Odd, B q) ≤ _ at hb
    change (∑ q ∈ Icc 1 R, B q) ≤ 2 * ∑ q ∈ (Icc 1 Q).filter Odd, B q at hh
    linarith
  have hdiag : ‖∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)‖ ≤ 4 * D * a * P := by
    rw [finite_singular_diagonal_eq, Complex.norm_real, Real.norm_eq_abs]
    have hb0 : 0 ≤ ∑ q ∈ Icc 1 R, B q := sum_nonneg (fun q _ => hB0 q)
    change |(#{x : pairs k L | dif x = 0} : ℝ) * (∑ q ∈ Icc 1 R, B q)| ≤ _
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb0)]
    have hd : (#{x : pairs k L | dif x = 0} : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 1) := by
      have hh : (#{x : pairs k L | dif x = 0} : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 2) := by exact_mod_cast LeanLab.Linnik.Decomp1532a.rkk_zero_le hk L
      have hp : (L : ℝ) ^ (2 * k - 2) ≤ (L : ℝ) ^ (2 * k - 1) := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) (by omega)
      linarith
    calc
      _ ≤ (2 * (L : ℝ) ^ (2 * k - 1)) * (2 * Real.exp 24 * Real.log Q) := mul_le_mul hd hBsum hb0 (by positivity)
      _ = 4 * (Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log Q) := by ring
      _ ≤ 4 * (D * a * P) := mul_le_mul_of_nonneg_left herror (by norm_num)
      _ = _ := by ring
  have hexpand : (∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k) =
    ((∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k)) -
    (∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) := by
    have hpart (q : ℕ) : (∑ x : pairs k L, ramanujanSum q (dif x)) =
      (∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x)) +
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x) := by
      simpa only [not_ne_iff] using (sum_filter_add_sum_filter_not univ (fun x : pairs k L => dif x ≠ 0) (fun x => ramanujanSum q (dif x))).symm
    simp_rw [hpart, mul_add]
    rw [sum_add_distrib]
    ring
  change ‖(∑ q ∈ Icc 1 R, _) - 2 * (L : ℂ) ^ (2 * k)‖ ≤ (2 * C₁ * C₂ + 6 * D) * a * P
  rw [hexpand]
  exact (norm_sub_le _ _).trans ((add_le_add hrest hdiag).trans_eq (by ring))

/-- LEAF. Unit U-1532. Lemma 10, display (8) p. 136: for `1 ≤ k ≤ N` and `r` of the form (7)
with `1 < r ≤ N`, `Σ_{n ≠ 0} r_{k,k}(n) |n|/φ(|n|) · r φ((r, n))/φ(r)² ≤ C L^{2k}/(log r)^{1/3}`
with an absolute `C`. -/
theorem lemma10 : ∃ C : ℝ, ∀ k N r : ℕ, 1 ≤ k → k ≤ N → 1 < r → r ≤ N →
    (∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀)) →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log r ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨A, hA, hrestrict⟩ := restricted_tuple_totient_bound
  obtain ⟨B, hB, hdecay⟩ := exceptional_divisor_log_decay
  refine ⟨8 * A * B, fun k N r hk hkN hr hrN hshape => ?_⟩
  obtain ⟨s, hsodd, hssf, hrs⟩ := hshape
  have hs : 0 < s := hsodd.pos
  have hsr : s ≤ r := by rcases hrs with h | h | h <;> omega
  have hr3 : 3 ≤ r := by
    have hs2 : s ≠ 2 := by rintro rfl; norm_num at hsodd
    rcases hrs with h | h | h <;> omega
  have hN : 2 ≤ N := by omega
  let L := Nat.log 2 N
  let T := (univ : Finset (pairs k L)).filter (fun x => dif x ≠ 0)
  let w : pairs k L → ℝ := fun x => ((dif x).natAbs : ℝ) / (dif x).natAbs.totient
  have hw (x : pairs k L) : 0 ≤ w x := by dsimp [w]; positivity
  have hred := weighted_gcd_divisor_reduction T (fun x => (dif x).natAbs) w
    (fun x _ => hw x) hs hrs
  have hsum : (∑ f ∈ s.divisors, (f.totient : ℝ) *
        ∑ x ∈ T with f ∣ (dif x).natAbs, w x) ≤
      A * (L : ℝ) ^ (2 * k) *
        (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) := by
    calc
      _ ≤ ∑ f ∈ s.divisors, (f.totient : ℝ) *
          (A * (L : ℝ) ^ (2 * k) / Real.sqrt (1 + Real.log f)) := by
        apply sum_le_sum
        intro f hfd
        have hdiv := Nat.dvd_of_mem_divisors hfd
        have hfo := hsodd.of_dvd_nat hdiv
        have hfN : f ≤ N := (Nat.le_of_dvd hs hdiv).trans (hsr.trans hrN)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hh := hrestrict k N hk hkN hN f hfo hfN
        simpa only [T, w, filter_filter, Int.natCast_dvd] using hh
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro f hf
        ring
  change (∑ x ∈ T, w x * _) ≤ _
  calc
    _ ≤ (8 * r / (r.totient : ℝ) ^ 2) *
        ∑ f ∈ s.divisors, (f.totient : ℝ) * ∑ x ∈ T with f ∣ (dif x).natAbs, w x := hred
    _ ≤ (8 * r / (r.totient : ℝ) ^ 2) *
        (A * (L : ℝ) ^ (2 * k) *
          (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (8 * A * (L : ℝ) ^ (2 * k)) *
        ((r : ℝ) / (r.totient : ℝ) ^ 2 *
          (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f))) := by ring
    _ ≤ (8 * A * (L : ℝ) ^ (2 * k)) * (B / Real.log r ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hdecay r s hr3 hs hrs) (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.127. The exceptional character has at most one zero in the height box. -/
theorem page_zero_unique : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    ∀ ρ₁ ρ₂ : ℂ, x.2.LFunction ρ₁ = 0 → x.2.LFunction ρ₂ = 0 →
      1 - b / Real.log T ≤ ρ₁.re → |ρ₁.im| ≤ T →
      1 - b / Real.log T ≤ ρ₂.re → |ρ₂.im| ≤ T → ρ₁ = ρ₂ := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨K, hK, hKlog⟩ := log_Bt_le_log_height
  obtain ⟨c, hc, hpage⟩ := page_two_zeros
  let b := min (min br bn) (c / K)
  have hbbr : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbbn : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hbc : b ≤ c / K := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) (by positivity), ?_⟩
  intro T hT x hx ρ₁ ρ₂ hz₁ hz₂ hb₁ ht₁ hb₂ ht₂
  have hχ := hn T hT x (excSet_mono hbbn hT hx)
  have hxbr := excSet_mono hbbr hT hx
  have hmono (ρ : ℂ) (hh : 1 - b / Real.log T ≤ ρ.re) :
      1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hbbr (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him₁ := (hr T hT x hxbr).2 ρ₁ hz₁ (hmono ρ₁ hb₁) ht₁
  have him₂ := (hr T hT x hxbr).2 ρ₂ hz₂ (hmono ρ₂ hb₂) ht₂
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlB : 0 < Real.log (Bt (x.1 + 1) 0) := by
    linarith [one_le_log_Bt (N := x.1 + 1) 0]
  have hcmp : b / Real.log T ≤ c / Real.log (Bt (x.1 + 1) 0) := by
    calc
      b / Real.log T ≤ (c / K) / Real.log T := div_le_div_of_nonneg_right hbc hlT.le
      _ = c / (K * Real.log T) := by rw [div_div]
      _ ≤ c / Real.log (Bt (x.1 + 1) 0) :=
        div_le_div_of_nonneg_left hc.le hlB
          (hKlog hT (by simpa using hx.1) (by simp; linarith : |(0 : ℝ)| ≤ T))
  exact hpage (x.1 + 1) x.2 hχ ρ₁ ρ₂ hz₁ hz₂ (by linarith)
    (by rw [him₁, abs_zero]; positivity) (by linarith)
    (by rw [him₂, abs_zero]; positivity)

/-- Gallagher 1975 p.127. Every exceptional zero in a sufficiently narrow height box is simple. -/
theorem page_zero_simple : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      analyticOrderNatAt x.2.LFunction ρ = 1 := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨K, hK, hKlog⟩ := log_Bt_le_log_height
  obtain ⟨c, hc, hc31, hcount⟩ := page_count
  let b := min (min br bn) (c / K)
  have hbbr : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbbn : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hbc : b ≤ c / K := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) (by positivity), ?_⟩
  intro T hT x hx ρ hz hb ht
  have hχ := hn T hT x (excSet_mono hbbn hT hx)
  have hxbr := excSet_mono hbbr hT hx
  have hβbr : 1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hbbr (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him := (hr T hT x hxbr).2 ρ hz hβbr ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlB : 0 < Real.log (Bt (x.1 + 1) 0) := by
    linarith [one_le_log_Bt (N := x.1 + 1) 0]
  have hcmp : b / Real.log T ≤ c / Real.log (Bt (x.1 + 1) 0) := by
    calc
      b / Real.log T ≤ (c / K) / Real.log T := div_le_div_of_nonneg_right hbc hlT.le
      _ = c / (K * Real.log T) := by rw [div_div]
      _ ≤ c / Real.log (Bt (x.1 + 1) 0) :=
        div_le_div_of_nonneg_left hc.le hlB
          (hKlog hT (by simpa using hx.1) (by simp; linarith : |(0 : ℝ)| ≤ T))
  have hβ : 1 - c / Real.log (Bt (x.1 + 1) 0) ≤ ρ.re := by linarith
  have hγ : |ρ.im| ≤ c / Real.log (Bt (x.1 + 1) 0) := by rw [him, abs_zero]; positivity
  have hη31 : c / Real.log (Bt (x.1 + 1) 0) ≤ 1 / 31 := by
    rw [div_le_iff₀ hlB]
    have hh := one_le_log_Bt (N := x.1 + 1) 0
    nlinarith
  have hm := mem_Tset_of_box hχ hη31 hz hβ hγ
  classical
  have hmem : ρ - 3 / 2 ∈ (Tset hχ 0).filter (fun w =>
      1 - c / Real.log (Bt (x.1 + 1) 0) ≤ w.re + 3 / 2 ∧
      |w.im| ≤ c / Real.log (Bt (x.1 + 1) 0)) := by
    refine Finset.mem_filter.mpr ⟨hm, ?_, ?_⟩
    · have he : (ρ - 3 / 2).re + 3 / 2 = ρ.re := by simp
      rw [he]
      exact hβ
    · have he : (ρ - 3 / 2).im = ρ.im := by simp
      rw [he]
      exact hγ
  have hu : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) ≤ 1 :=
    (Finset.single_le_sum (fun w _ => Nat.zero_le _) hmem).trans (hcount (x.1 + 1) x.2 hχ)
  have hzshift : fShift x.2 0 (ρ - 3 / 2) = 0 := by simpa [fShift] using hz
  have ho : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) = 1 :=
    Nat.le_antisymm hu (one_le_order hχ 0 hzshift)
  have hg : AnalyticAt ℂ (fun z : ℂ => z + 3 / 2) (ρ - 3 / 2) := by fun_prop
  have hd : deriv (fun z : ℂ => z + 3 / 2) (ρ - 3 / 2) ≠ 0 := by simp
  have hshift := analyticOrderAt_comp_of_deriv_ne_zero (f := x.2.LFunction) hg hd
  have hnat := congrArg ENat.toNat hshift
  have he : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) =
      analyticOrderNatAt x.2.LFunction ρ := by
    unfold analyticOrderNatAt
    have hf : fShift x.2 0 = fun z : ℂ => x.2.LFunction (z + 3 / 2) := by
      funext z
      simp [fShift]
    rw [hf]
    simpa only [Function.comp_def, sub_add_cancel] using hnat
  exact he.symm.trans ho

/-- Gallagher 1975 p.127. The exceptional conductor exceeds every fixed power of log T
up to a positive constant depending on that power. No effective constant is asserted. -/
theorem exceptional_conductor_log_growth : ∃ b : ℝ, 0 < b ∧
    ∀ B : ℝ, 0 < B → ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ x ∈ excSet b T, c * Real.log T ^ B ≤ (x.1 : ℝ) + 1 := by
  obtain ⟨b, hb, hreal⟩ := page_real
  refine ⟨b, hb, ?_⟩
  intro B hB
  obtain ⟨cs, hcs, hs⟩ := siegel (1 / B) (by positivity)
  refine ⟨(cs / b) ^ B, Real.rpow_pos_of_pos (div_pos hcs hb) _, ?_⟩
  intro T hT x hx
  obtain ⟨ρ, hz, hβ, ht⟩ := hx.2.2
  have hchi := (hreal T hT x hx).1
  have him := (hreal T hT x hx).2 ρ hz hβ ht
  have he : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
  have hzreal : x.2.LFunction (ρ.re : ℂ) = 0 := by rwa [he]
  have hS := hs x.1 x.2 hx.2.1 hchi ρ.re hzreal
  let r : ℝ := (x.1 : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hbound : cs * r ^ (-(1 / B)) ≤ b / Real.log T := by
    dsimp [r]
    linarith
  rw [Real.rpow_neg hr.le, ← div_eq_mul_inv] at hbound
  have hp : 0 < r ^ (1 / B) := Real.rpow_pos_of_pos hr _
  have hprod := (div_le_div_iff₀ hp hlT).mp hbound
  have hbase : cs / b * Real.log T ≤ r ^ (1 / B) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb]
    nlinarith
  have hraise := Real.rpow_le_rpow (by positivity : 0 ≤ cs / b * Real.log T) hbase hB.le
  rw [← Real.rpow_mul hr.le, one_div_mul_cancel hB.ne', Real.rpow_one] at hraise
  rw [Real.mul_rpow (div_nonneg hcs.le hb.le) hlT.le] at hraise
  exact hraise

/-- Gallagher 1975 pp.127 and 131. The entire primitive family has at most one counted zero in a fixed Page strip. -/
theorem density_sum_in_page_strip : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ σ : ℝ, 1 - b / Real.log T ≤ σ →
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ) ≤ 1 := by
  classical
  obtain ⟨bc, hbc, hchar⟩ := page_subsingleton
  obtain ⟨bz, hbz, hzero⟩ := page_zero_unique
  let b := min bc bz
  have hb : 0 < b := lt_min hbc hbz
  refine ⟨b, hb, fun T hT σ hσ => ?_⟩
  let chars (q : ℕ) := (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive)
  let S := (range ⌊T⌋₊).sigma chars
  have hprim (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S) : x.2.IsPrimitive :=
    (mem_filter.mp (mem_sigma.mp hx).2).2
  have hqT (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S) : (x.1 : ℝ) + 1 ≤ T := by
    have hq : x.1 < ⌊T⌋₊ := mem_range.mp (mem_sigma.mp hx).1
    have hh : ((x.1 + 1 : ℕ) : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast (by omega : x.1 + 1 ≤ ⌊T⌋₊)
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ T by linarith)
    push_cast at hh
    exact hh.trans hfloor
  have hmem (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S)
      (hc : zeroCount x.2 σ T ≠ 0) : x ∈ excSet b T := by
    have hne : {ρ : ℂ | x.2.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} ≠ ∅ := by
      intro he
      apply hc
      simp only [zeroCount, he, Set.ncard_empty]
    obtain ⟨ρ, hz, hβ, ht⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact ⟨hqT x hx, hprim x hx, ρ, hz, hσ.trans hβ, ht⟩
  have hcount (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S) : zeroCount x.2 σ T ≤ 1 := by
    by_cases hc : zeroCount x.2 σ T = 0
    · omega
    have hxE := excSet_mono (min_le_right bc bz) hT (hmem x hx hc)
    have hσz : 1 - bz / Real.log T ≤ σ := by
      have hd := div_le_div_of_nonneg_right (min_le_right bc bz)
        (show (0 : ℝ) ≤ Real.log T by apply Real.log_nonneg; linarith)
      dsimp [b] at hσ
      linarith
    have hsub : ({ρ : ℂ | x.2.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} : Set ℂ).Subsingleton := by
      intro ρ₁ hρ₁ ρ₂ hρ₂
      exact hzero T hT x hxE ρ₁ ρ₂ hρ₁.1 hρ₂.1
        (hσz.trans hρ₁.2.1) hρ₁.2.2 (hσz.trans hρ₂.2.1) hρ₂.2.2
    exact (Set.ncard_le_one hsub.finite).mpr (fun a ha b hb => hsub ha hb)
  let I := S.filter (fun x => zeroCount x.2 σ T ≠ 0)
  have hI : I.card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyS, hyc⟩ := mem_filter.mp hy
    exact hchar T hT (excSet_mono (min_le_left bc bz) hT (hmem x hxS hxc))
      (excSet_mono (min_le_left bc bz) hT (hmem y hyS hyc))
  have heq : (∑ x ∈ I, (zeroCount x.2 σ T : ℝ)) = ∑ x ∈ S, (zeroCount x.2 σ T : ℝ) := by
    apply sum_subset (filter_subset _ _)
    intro x hx hxI
    have hc : zeroCount x.2 σ T = 0 := by
      by_contra hn
      exact hxI (mem_filter.mpr ⟨hx, hn⟩)
    simp [hc]
  calc
    _ = ∑ x ∈ S, (zeroCount x.2 σ T : ℝ) := sum_sigma' _ _ _
    _ = ∑ x ∈ I, (zeroCount x.2 σ T : ℝ) := heq.symm
    _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
      apply sum_le_sum
      intro x hx
      exact_mod_cast hcount x (mem_filter.mp hx).1
    _ = (I.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hI

/-- Gallagher 1975 p.131. Auxiliary total count from the proved unit height estimate.
The constant is uniform in the primitive character, real part and height. -/
theorem zeroCount_le_unit_height : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ σ T : ℝ, 1 / 2 ≤ σ → 0 ≤ T →
      (zeroCount χ σ T : ℝ) ≤ (⌊T⌋₊ + 1 : ℕ) * A * Real.log (q * (T + 2)) := by
  obtain ⟨A, hA, huall⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  refine ⟨A, hA, fun q _ χ hp σ T hσ hT => ?_⟩
  have hu := huall q χ hp
  classical
  let W : ℕ → Finset ℂ := fun j => (hu j (Nat.cast_nonneg _)).1.toFinset
  have hψ : q = 1 ∨ χ ≠ 1 := by
    by_cases hq : q = 1
    · exact Or.inl hq
    · right
      intro hχ
      apply hq
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hh
      exact hh.symm
  have hnt {ρ : ℂ} (hz : χ.LFunction ρ = 0) (hβ : σ ≤ ρ.re) :
      LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ := by
    refine ⟨hz, by linarith, ?_⟩
    by_contra h
    have hre : 1 ≤ ρ.re := le_of_not_gt h
    rcases hψ with rfl | hχ
    · rw [DirichletCharacter.LFunction_modOne_eq] at hz
      exact riemannZeta_ne_zero_of_one_le_re hre hz
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre hz
  have horder {ρ : ℂ} (hρ : LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ) :
      1 ≤ LeanLab.HardyLittlewood1923.U1479.mult χ ρ := by
    have hw : ρ ≠ 1 := by
      intro he
      have hh := hρ.2.2
      simp [he] at hh
    have hz : analyticOrderNatAt χ.LFunction ρ ≠ 0 := by
      simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(LeanLab.HardyLittlewood1923.U1482.L_analyticAt χ hw).analyticOrderAt_ne_zero.mpr hρ.1,
        LeanLab.HardyLittlewood1923.U1482.L_ord_ne_top χ hψ hw⟩
    change (1 : ℝ) ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hcard (j : ℕ) : ((W j).card : ℝ) ≤ A * Real.log (q * ((j : ℝ) + 2)) := by
    have hmem (ρ : ℂ) (hρ : ρ ∈ W j) :
        LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ ∧
          (j : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ (j : ℝ) + 1 := by
      simpa only [W, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hρ
    calc
      _ = ∑ _ρ ∈ W j, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ W j, LeanLab.HardyLittlewood1923.U1479.mult χ ρ :=
        sum_le_sum (fun ρ hρ => horder (hmem ρ hρ).1)
      _ ≤ _ := (hu j (Nat.cast_nonneg _)).2 (W j) hmem
  let U : Finset ℂ := (range (⌊T⌋₊ + 1)).biUnion W
  have hsub : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} ⊆ (U : Set ℂ) := by
    intro ρ hρ
    have hj : ⌊|ρ.im|⌋₊ < ⌊T⌋₊ + 1 := by
      have := Nat.floor_mono hρ.2.2
      omega
    apply mem_biUnion.mpr
    refine ⟨⌊|ρ.im|⌋₊, mem_range.mpr hj, ?_⟩
    simp only [W, Set.Finite.mem_toFinset]
    exact ⟨hnt hρ.1 hρ.2.1, Nat.floor_le (abs_nonneg _), (Nat.lt_floor_add_one _).le⟩
  have hc : zeroCount χ σ T ≤ U.card := by
    simpa only [zeroCount, Set.ncard_coe_finset] using Set.ncard_le_ncard hsub U.finite_toSet
  calc
    _ ≤ (U.card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ j ∈ range (⌊T⌋₊ + 1), ((W j).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ j ∈ range (⌊T⌋₊ + 1), A * Real.log (q * (T + 2)) := by
      apply sum_le_sum
      intro j hj
      have hjT : (j : ℝ) ≤ T :=
        (show (j : ℝ) ≤ ⌊T⌋₊ by exact_mod_cast (by have := mem_range.mp hj; omega : j ≤ ⌊T⌋₊)).trans
          (Nat.floor_le hT)
      apply (hcard j).trans
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.log_le_log (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) (by positivity))
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

/-- Gallagher 1975 p.131. Auxiliary polynomial bound for the whole primitive family.
This uses the proved unit height count and no density estimate. -/
theorem density_sum_polynomial : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (4 : ℕ) := by
  classical
  obtain ⟨A, hA, hu⟩ := zeroCount_le_unit_height
  refine ⟨4 * A, by positivity, fun T hT σ hσ => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hK : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T := by
    have := Nat.floor_le hT0
    push_cast
    linarith
  have hsingle (q : ℕ) (hq : q ∈ range ⌊T⌋₊)
      (χ : DirichletCharacter ℂ (q + 1)) (hp : χ.IsPrimitive) :
      (zeroCount χ σ T : ℝ) ≤ 4 * A * T ^ 2 := by
    have hqT : ((q + 1 : ℕ) : ℝ) ≤ T := by
      have hn : q + 1 ≤ ⌊T⌋₊ := by have := mem_range.mp hq; omega
      exact (show ((q + 1 : ℕ) : ℝ) ≤ ⌊T⌋₊ by exact_mod_cast hn).trans (Nat.floor_le hT0)
    have hlog : Real.log ((q + 1 : ℕ) * (T + 2)) ≤ 2 * T := by
      calc
        _ ≤ Real.log (T * (T + 2)) :=
          Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hqT (by positivity))
        _ = Real.log T + Real.log (T + 2) :=
          Real.log_mul hTpos.ne' (by positivity)
        _ ≤ (T - 1) + (T + 2 - 1) := add_le_add
          (Real.log_le_sub_one_of_pos hTpos) (Real.log_le_sub_one_of_pos (by positivity))
        _ = 2 * T := by ring
    have hlog0 : 0 ≤ Real.log ((q + 1 : ℕ) * (T + 2)) := by
      apply Real.log_nonneg
      have hq1 : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ q + 1)
      have hmul := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ T + 2 by linarith)
      nlinarith
    calc
      _ ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) * A * Real.log ((q + 1 : ℕ) * (T + 2)) :=
        hu (q + 1) χ hp σ T hσ hT0
      _ ≤ (2 * T) * A * (2 * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hK hA) hlog hlog0 (by positivity)
      _ = _ := by ring
  have hfamily (q : ℕ) (hq : q ∈ range ⌊T⌋₊) :
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ)) ≤ T * (4 * A * T ^ 2) := by
    let S := (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive)
    have hcard : (S.card : ℝ) ≤ T := by
      have hc : S.card ≤ (q + 1).totient := by
        calc
          S.card ≤ Fintype.card (DirichletCharacter ℂ (q + 1)) := card_le_univ _
          _ = (q + 1).totient := by
            rw [← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      have hn : q + 1 ≤ ⌊T⌋₊ := by have := mem_range.mp hq; omega
      exact (show (S.card : ℝ) ≤ ⌊T⌋₊ by
        exact_mod_cast hc.trans ((Nat.totient_le _).trans hn)).trans (Nat.floor_le hT0)
    calc
      _ ≤ ∑ _χ ∈ S, (4 * A * T ^ 2) :=
        sum_le_sum (fun χ hχ => hsingle q hq χ (mem_filter.mp hχ).2)
      _ = (S.card : ℝ) * (4 * A * T ^ 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  calc
    _ ≤ ∑ _q ∈ range ⌊T⌋₊, T * (4 * A * T ^ 2) := sum_le_sum hfamily
    _ = (⌊T⌋₊ : ℝ) * (T * (4 * A * T ^ 2)) := by simp
    _ ≤ T * (T * (4 * A * T ^ 2)) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hT0) (by positivity)
    _ = _ := by ring


/-- Gallagher 1975 p.131. The region at most three quarters needs no density theorem. -/
theorem density_sum_away_from_one : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (16 * (1 - σ)) := by
  obtain ⟨C, hC, h⟩ := density_sum_polynomial
  refine ⟨C, hC, fun T hT σ hσ hσ' => (h T hT σ hσ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num at *; linarith)

/-- Gallagher 1970 p.335, reduction before Theorem 6. The polynomial count proves
any region with a fixed positive horizontal gap. The exponent is explicit in the gap. -/
theorem density_sum_fixed_gap (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 - η →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ ((4 / η) * (1 - σ)) := by
  obtain ⟨C, hC, h⟩ := density_sum_polynomial
  refine ⟨C, hC, fun T hT σ hσ hgap => (h T hT σ hσ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hη]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Finite interpolation identity behind Gallagher 1970 p.334, Turan step. -/
theorem power_sum_interpolation {n : ℕ} (z a b : Fin n → ℂ) (M : ℕ) :
    (∑ j, b j * ∑ i, a i * z i ^ (M + 1 + j.val)) =
      ∑ i, a i * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val := by
  simp only [Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [pow_add]
  ring



open scoped Classical
/-- Nonzero interpolation data force a nonzero power sum in the next n powers. -/
theorem power_sum_nonzero_of_injective {n : ℕ} (z a : Fin n → ℂ) (M : ℕ)
    (hz : Function.Injective z) (ha : ∃ i, a i ≠ 0 ∧ z i ≠ 0) :
    ∃ j : Fin n, (∑ i, a i * z i ^ (M + 1 + j.val)) ≠ 0 := by
  by_contra h
  push Not at h
  have hv : (fun i => a i * z i ^ (M + 1)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hz
    intro j
    simpa only [pow_add, mul_assoc] using h j
  obtain ⟨i, hai, hzi⟩ := ha
  have := congr_fun hv i
  exact (mul_ne_zero hai (pow_ne_zero _ hzi)) this


/-- The interpolation coefficient norm controls the largest power sum. -/
theorem power_sum_interpolation_bound {n : ℕ} (z a b : Fin n → ℂ) (M : ℕ)
    {B : ℝ} (hB : ∀ j : Fin n, ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ ≤ B) :
    ‖∑ i, a i * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val‖ ≤
      (∑ j, ‖b j‖) * B := by
  rw [← power_sum_interpolation]
  calc
    _ ≤ ∑ j, ‖b j * ∑ i, a i * z i ^ (M + 1 + j.val)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖b j‖ * B := by
      apply sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)
    _ = _ := (sum_mul ..).symm


/-- A bounded interpolant supplies a quantitative power sum lower bound. -/
theorem power_sum_lower_bound_of_interpolant {n : ℕ} (hn : 0 < n)
    (z a b : Fin n → ℂ) (M : ℕ) {A B : ℝ} (hB : 0 < B)
    (hcoeff : (∑ j, ‖b j‖) ≤ B)
    (hvalue : A ≤ ‖∑ i, a i * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val‖) :
    ∃ j : Fin n, A / B ≤ ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, _, hj⟩ := exists_max_image (univ : Finset (Fin n))
    (fun j => ‖∑ i, a i * z i ^ (M + 1 + j.val)‖) univ_nonempty
  refine ⟨j, (div_le_iff₀ hB).mpr ?_⟩
  calc
    A ≤ _ := hvalue
    _ ≤ (∑ j, ‖b j‖) * ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ :=
      power_sum_interpolation_bound z a b M (fun k => hj k (mem_univ k))
    _ ≤ B * ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ = _ := mul_comm _ _


/-- The pure single term Turan bound has no cancellation. -/
theorem turan_power_sum_single {z : ℂ} (hz : 1 ≤ ‖z‖) (M : ℕ) (hM : 1 ≤ M) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖z ^ ν‖ := by
  refine ⟨M + 1, by omega, by omega, ?_⟩
  calc
    (1 / 50 : ℝ) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤ ‖z ^ (M + 1)‖ := by rw [norm_pow]; exact one_le_pow₀ hz


/-- Repeated roots are combined with their positive multiplicities.
Qualitative finite part of Gallagher 1970 p.334, with no separation assumption. -/
theorem pure_power_sum_nonzero {n : ℕ} (z : Fin n → ℂ) (M : ℕ)
    (hz : ∃ i, z i ≠ 0) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ M + n ∧ (∑ i, z i ^ ν) ≠ 0 := by
  classical
  let s : Finset ℂ := univ.image z
  let LeanLab.PNTPort.LargeSieve.e : Fin s.card ≃ ↥s := s.equivFin.symm
  let v : Fin s.card → ℂ := fun i => (LeanLab.PNTPort.LargeSieve.e i).val
  let a : Fin s.card → ℂ := fun j => ((univ.filter (fun i => z i = v j)).card : ℂ)
  have hv : Function.Injective v := by
    intro i j hij
    apply LeanLab.PNTPort.LargeSieve.e.injective
    exact Subtype.ext hij
  have hsum (k : ℕ) : (∑ j, a j * v j ^ k) = ∑ i, z i ^ k := by
    calc
      _ = ∑ u : ↥s, ((univ.filter (fun i => z i = u.val)).card : ℂ) * u.val ^ k :=
        LeanLab.PNTPort.LargeSieve.e.sum_comp _
      _ = ∑ u ∈ s, ((univ.filter (fun i => z i = u)).card : ℂ) * u ^ k :=
        sum_coe_sort s (fun u : ℂ =>
          (((univ : Finset (Fin n)).filter (fun i => z i = u)).card : ℂ) * u ^ k)
      _ = ∑ u ∈ s, ∑ i ∈ univ.filter (fun i => z i = u), z i ^ k := by
        apply sum_congr rfl
        intro u _
        rw [show (∑ i ∈ univ.filter (fun i => z i = u), z i ^ k) =
            ∑ _i ∈ univ.filter (fun i => z i = u), u ^ k from
          sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2])]
        simp
      _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem z hi) _
  have ha : ∃ j, a j ≠ 0 ∧ v j ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    have hzi : z i ∈ s := mem_image_of_mem z (mem_univ i)
    let j := LeanLab.PNTPort.LargeSieve.e.symm ⟨z i, hzi⟩
    have hj : v j = z i := by simp [v, j]
    refine ⟨j, ?_, hj ▸ hi⟩
    dsimp [a]
    apply Nat.cast_ne_zero.mpr
    apply card_ne_zero.mpr
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hj.symm⟩⟩
  obtain ⟨j, hj⟩ := power_sum_nonzero_of_injective v a M hv ha
  have hcard : s.card ≤ n := by
    exact (card_image_le).trans (by simp)
  refine ⟨M + 1 + j.val, by omega, by have := j.isLt; omega, ?_⟩
  rwa [hsum] at hj


/-- Compactness gives a uniform lower bound at each fixed length and starting power.
This does not supply the exponential constant required by Turan's theorem. -/
theorem pure_power_sum_fixed_length {n : ℕ} (hn : 0 < n) (M : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin n → ℂ, ‖z‖ = 1 →
      ∃ ν : ℕ, M < ν ∧ ν ≤ M + n ∧ ε ≤ ‖∑ i, z i ^ ν‖ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let F : (Fin n → ℂ) → ℝ := fun z => ∑ j : Fin n, ‖∑ i, z i ^ (M + 1 + j.val)‖
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hpos (z : Fin n → ℂ) (hz : ‖z‖ = 1) : 0 < F z := by
    have hne : z ≠ 0 := by intro he; simp [he] at hz
    have hex : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨ν, hνM, hνn, hν⟩ := pure_power_sum_nonzero z M hex
    let j : Fin n := ⟨ν - (M + 1), by omega⟩
    have hj : M + 1 + j.val = ν := by dsimp [j]; omega
    have hle : ‖∑ i, z i ^ ν‖ ≤ F z := by
      dsimp [F]
      rw [← hj]
      exact single_le_sum (fun k _ => norm_nonneg (∑ i, z i ^ (M + 1 + k.val))) (mem_univ j)
    exact (norm_pos_iff.mpr hν).trans_le hle
  have hs : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨z₀, hz₀, hmin⟩ := hs.exists_isMinOn hne hF.continuousOn
  have hz₀norm : ‖z₀‖ = 1 := by simpa using hz₀
  have hε : 0 < F z₀ / (n : ℝ) := div_pos (hpos z₀ hz₀norm) (by exact_mod_cast hn)
  refine ⟨F z₀ / n, hε, ?_⟩
  intro z hz
  obtain ⟨j, _, hj⟩ := exists_max_image (univ : Finset (Fin n))
    (fun j => ‖∑ i, z i ^ (M + 1 + j.val)‖) univ_nonempty
  refine ⟨M + 1 + j.val, by omega, by have := j.isLt; omega, ?_⟩
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  have hlow : F z₀ ≤ F z := hmin (by simpa using hz)
  have hu : F z ≤ (n : ℝ) * ‖∑ i, z i ^ (M + 1 + j.val)‖ := by
    calc
      F z ≤ ∑ _k : Fin n, ‖∑ i, z i ^ (M + 1 + j.val)‖ :=
        sum_le_sum (fun k _ => hj k (mem_univ k))
      _ = _ := by simp
  nlinarith


/-- A singleton selector has unbounded coefficients as two roots coalesce.
This is a limitation of a fixed singleton interpolation route to Gallagher p.334. -/
theorem singleton_selector_unbounded (B : ℝ) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ b₀ b₁ : ℂ, b₀ + b₁ = 1 → b₀ + (r : ℂ) * b₁ = 0 → B < ‖b₁‖ := by
  let d : ℝ := 1 / (B + 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; rw [div_lt_one (by linarith)]; linarith
  have hdB : d * (B + 2) = 1 := by dsimp [d]; field_simp
  refine ⟨1 - d, by linarith, by linarith, ?_⟩
  intro b₀ b₁ h₀ h₁
  have he : (d : ℂ) * b₁ = 1 := by
    push_cast at h₁
    linear_combination h₀ - h₁
  have hn := congrArg norm he
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, norm_one] at hn
  nlinarith


/-- Quantitative two root auxiliary for the finite Turan step on Gallagher p.334.
It handles cancellation for one unit root and a second root in the closed unit disc. -/
theorem two_term_power_sum_bound (w : ℂ) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    1 / (4 * (k : ℝ) + 4) ≤ ‖1 + w ^ k‖ ∨
      1 / (4 * (k : ℝ) + 4) ≤ ‖1 + w ^ (k + 1)‖ := by
  let d : ℝ := 1 / (4 * (k : ℝ) + 4)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd4 : d ≤ 1 / 4 := by dsimp [d]; apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hdc : (4 * (k : ℝ) + 4) * d = 1 := by dsimp [d]; field_simp
  by_contra h
  push Not at h
  change ‖1 + w ^ k‖ < d ∧ ‖1 + w ^ (k + 1)‖ < d at h
  have hwp : (1 / 2 : ℝ) ≤ ‖w ^ k‖ := by
    have ht := norm_sub_le (1 + w ^ k) (w ^ k)
    simp only [add_sub_cancel_right, norm_one] at ht
    linarith [h.1]
  have hdiff : ‖w ^ k‖ * ‖w - 1‖ < 2 * d := by
    rw [← norm_mul]
    have he : w ^ k * (w - 1) = (1 + w ^ (k + 1)) - (1 + w ^ k) := by
      rw [pow_succ]; ring
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith [h.1, h.2])
  have hnear : ‖1 - w‖ < 4 * d := by
    rw [norm_sub_rev]
    nlinarith [mul_le_mul_of_nonneg_right hwp (norm_nonneg (w - 1))]
  have hsum : ‖∑ j ∈ range k, w ^ j‖ ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range k, ‖w ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range k, (1 : ℝ) := by
        apply sum_le_sum
        intro j _
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := by simp
  have htel : ‖1 - w ^ k‖ ≤ (k : ℝ) * ‖1 - w‖ := by
    rw [← geom_sum_mul_neg w k, norm_mul]
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have ht := norm_add_le (1 + w ^ k) (1 - w ^ k)
  have he : (1 + w ^ k) + (1 - w ^ k) = (2 : ℂ) := by ring
  rw [he] at ht
  norm_num only [Complex.norm_ofNat] at ht
  have hh := mul_le_mul_of_nonneg_left hnear.le (Nat.cast_nonneg k)
  nlinarith [h.1]


/-- The two root Turan bound with the explicit constant used on Gallagher p.334.
This finite case includes cancellation. The general finite interpolation leaf remains separate. -/
theorem turan_power_sum_pair (z w : ℂ) (hz : 1 ≤ ‖z‖) (hw : ‖w‖ ≤ ‖z‖)
    (M : ℕ) (hM : 2 ≤ M) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖z ^ ν + w ^ ν‖ := by
  have hz0 : z ≠ 0 := by intro he; norm_num [he] at hz
  have hr : ‖w / z‖ ≤ 1 := by rw [norm_div, div_le_one (by linarith : 0 < ‖z‖)]; exact hw
  have hp : ∀ m : ℕ, 1 ≤ m → 4 * (m : ℝ) + 8 ≤ (50 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m; norm_num
      · have hprev := ih (by omega)
        rw [pow_succ]
        push_cast
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 50) m]
  have hsmall : (1 / 50 : ℝ) ^ M ≤ 1 / (4 * ((M + 1 : ℕ) : ℝ) + 4) := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have := hp M (by omega)
    push_cast
    linarith
  have hscale (ν : ℕ) : ‖1 + (w / z) ^ ν‖ ≤ ‖z ^ ν + w ^ ν‖ := by
    have he : z ^ ν + w ^ ν = z ^ ν * (1 + (w / z) ^ ν) := by
      rw [div_pow]
      field_simp
    rw [he, norm_mul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hz)
  rcases two_term_power_sum_bound (w / z) hr (M + 1) with h | h
  · exact ⟨M + 1, by omega, by omega, hsmall.trans (h.trans (hscale _))⟩
  · exact ⟨M + 2, by omega, by omega, hsmall.trans (h.trans (hscale _))⟩


/-- LEAF. Finite interpolation construction in Turan's second power sum theorem.
Gallagher 1970 p.334 after display 21. Vaughan author notes, Vol.3 pp.351 to 353,
proof of Theorem K.3. Corollary K.5 and 16e less than 50 give this coefficient bound.
No L-function or analytic number theory assumption occurs in this finite statement. -/
theorem turan_interpolant {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hunit : ∃ i, ‖z i‖ = 1) :
    ∃ J : Finset (Fin n), J.Nonempty ∧ ∃ b : Fin n → ℂ,
      (∀ i, z i ^ (M + 1) * (∑ j, b j * z i ^ j.val) = if i ∈ J then 1 else 0) ∧
      (∑ j, ‖b j‖) ≤ (50 : ℝ) ^ M := by
  exact LeanLab.Linnik.Decomp1532b2.turan_interpolant_finite hn hnM z hz hunit


/-- Turan's finite lower bound used in Gallagher 1970 p.334.
CONDITIONAL ON the finite interpolation construction turan_interpolant. -/
theorem turan_power_sum_lower_bound_normalized {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hunit : ∃ i, ‖z i‖ = 1) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖ := by
  classical
  obtain ⟨J, hJ, b, hbi, hb⟩ := turan_interpolant hn hnM z hz hunit
  have hv : (1 : ℝ) ≤ ‖∑ i, (1 : ℂ) * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val‖ := by
    simp_rw [one_mul, hbi]
    simp only [sum_ite_mem, sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
    simp only [univ_inter]
    exact_mod_cast (Nat.succ_le_iff.mpr hJ.card_pos)
  obtain ⟨j, hj⟩ := power_sum_lower_bound_of_interpolant hn z (fun _ => 1) b M
    (by positivity : (0 : ℝ) < 50 ^ M) hb hv
  refine ⟨M + 1 + j.val, by omega, by have := j.isLt; omega, ?_⟩
  simpa only [one_mul, div_pow, one_pow] using hj


/-- General pure power sum form of the Turan input on Gallagher 1970 p.334.
CONDITIONAL ON turan_interpolant. Normalizing the largest root costs no lower bound. -/
theorem turan_power_sum_lower_bound {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∃ i, 1 ≤ ‖z i‖) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, _, hi⟩ := exists_max_image (univ : Finset (Fin n)) (fun j => ‖z j‖) univ_nonempty
  let R : ℝ := ‖z i‖
  have hR1 : 1 ≤ R := by
    obtain ⟨j, hj⟩ := hz
    exact hj.trans (hi j (mem_univ j))
  have hR : 0 < R := by linarith
  let w : Fin n → ℂ := fun j => z j / (R : ℂ)
  have hwnorm (j : Fin n) : ‖w j‖ = ‖z j‖ / R := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hw : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    rw [hwnorm, div_le_one hR]
    exact hi j (mem_univ j)
  have hwi : ∃ j, ‖w j‖ = 1 := ⟨i, by rw [hwnorm]; exact div_self hR.ne'⟩
  obtain ⟨ν, hνM, hν2, hν⟩ := turan_power_sum_lower_bound_normalized hn hnM w hw hwi
  refine ⟨ν, hνM, hν2, hν.trans ?_⟩
  have hsum : (∑ j, w j ^ ν) = (∑ j, z j ^ ν) / (R : ℂ) ^ ν := by
    dsimp [w]
    simp_rw [div_pow]
    exact (sum_div ..).symm
  rw [hsum, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hpow : 1 ≤ R ^ ν := one_le_pow₀ hR1
  rw [div_le_iff₀ (by positivity : 0 < R ^ ν)]
  nlinarith [mul_le_mul_of_nonneg_left hpow (norm_nonneg (∑ j, z j ^ ν))]


open FourierTransform
open LeanLab.Linnik.U1394Fejer
/-- Fourier inversion for the Fejer kernel used in Gallagher 1970 p.330. -/
theorem integral_fejer_exp (x : ℝ) :
    ∫ t : ℝ, LeanLab.PNTPort.LargeSieve.e (x * t) * (fej t : ℂ) = (tri x : ℂ) := by
  have hF : 𝓕 (fun u => (tri u : ℂ)) = fun t => (fej t : ℂ) := by
    funext t
    rw [fourier_tri, fej_eq_G]
  have hFi : Integrable (𝓕 (fun u => (tri u : ℂ))) := by
    rw [hF]
    exact integrable_fej.ofReal
  have hi := integrable_tri.fourierInv_fourier_eq hFi
    ((Complex.continuous_ofReal.comp continuous_tri).continuousAt (x := x))
  rw [Real.fourierInv_eq', hF] at hi
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Real.inner_apply, smul_eq_mul]
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 2
  push_cast
  ring


/-- The scaled Fourier kernel for Gallagher 1970 p.330 Lemma 1. -/
theorem integral_fejer_exp_scaled (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t : ℝ, LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ) = (δ⁻¹ * tri (x / δ) : ℝ) := by
  have heq : (fun t : ℝ => LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ)) =
      fun t => (fun u => LeanLab.PNTPort.LargeSieve.e ((x / δ) * u) * (fej u : ℂ)) (δ * t) := by
    ext t
    congr 2
    field_simp
  rw [heq, Measure.integral_comp_mul_left (fun u : ℝ => LeanLab.PNTPort.LargeSieve.e ((x / δ) * u) * (fej u : ℂ)) δ, integral_fejer_exp]
  simp only [abs_of_pos (inv_pos.mpr hδ), Complex.real_smul, Complex.ofReal_mul]


/-- Integrability of the phase times Fejer weight. -/
theorem integrable_fejer_phase (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ)) := by
  have hi := integrable_fej.comp_mul_left' hδ.ne'
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
    · exact Complex.continuous_ofReal.comp (continuous_fej.comp (continuous_const.mul continuous_id))
  · filter_upwards [] with t
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fej_nonneg _)]


/-- Exact smoothed Fourier energy for any finite real frequency family. -/
theorem fejer_exponential_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ((∫ t : ℝ, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) : ℝ) : ℂ) =
      (δ⁻¹ : ℂ) * ∑ i ∈ s, ∑ j ∈ s,
        a i * (starRingEnd ℂ) (a j) * (tri ((freq i - freq j) / δ) : ℂ) := by
  have heq (t : ℝ) : ((‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * (starRingEnd ℂ) (a j) * (LeanLab.PNTPort.LargeSieve.e ((freq i - freq j) * t) * (fej (δ * t) : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum,
      sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    rw [map_mul, ← LeanLab.PNTPort.LargeSieve.e_neg]
    rw [show (freq i - freq j) * t = freq i * t + -(freq j * t) by ring, e_add]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (integrable_fejer_phase (freq i - freq j) hδ).const_mul _)), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable_fejer_phase (freq i - freq j) hδ).const_mul _),
    mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_fejer_exp_scaled _ hδ]
  push_cast
  ring


/-- The Fejer weight has an explicit positive lower bound near zero. -/
theorem fejer_lower_half {u : ℝ} (hu : |u| ≤ 1 / 2) : 4 / Real.pi ^ 2 ≤ fej u := by
  by_cases hz : u = 0
  · subst u
    have h0 : fej 0 = 1 := by simp [fej, LeanLab.PNTPort.LargeSieve.e]
    rw [h0, div_le_one (by positivity : (0 : ℝ) < Real.pi ^ 2)]
    nlinarith [Real.pi_gt_three]
  · have hs := LeanLab.PNTPort.LargeSieve.two_abs_le_abs_sin hu
    have hs2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * |u|) hs 2
    simp only [mul_pow, sq_abs] at hs2
    rw [fej_ne hz, le_div_iff₀ (by positivity : (0 : ℝ) < (Real.pi * u) ^ 2)]
    calc
      4 / Real.pi ^ 2 * (Real.pi * u) ^ 2 = 4 * u ^ 2 := by field_simp
      _ ≤ _ := by norm_num at hs2; exact hs2


/-- Integrability of a finite Fourier energy with Fejer weight. -/
theorem integrable_fejer_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) := by
  have hsum (t : ℝ) : ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, norm_e, mul_one]
  have hi := (integrable_fej.comp_mul_left' hδ.ne').const_mul ((∑ i ∈ s, ‖a i‖) ^ 2)
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
    · exact continuous_fej.comp (continuous_const.mul continuous_id)
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (fej_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hsum t) 2) (fej_nonneg _)


/-- Finite frequency form of the smoothing step in Gallagher 1970 p.330 Lemma 1.
The triangle quadratic form is exactly the short interval energy kernel. -/
theorem gallagher_frequency_smoothing {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 2) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / (4 * δ)) *
        (∑ i ∈ s, ∑ j ∈ s, a i * (starRingEnd ℂ) (a j) *
          (tri ((freq i - freq j) / δ) : ℂ)).re := by
  have hc : Continuous (fun t : ℝ => ∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)) := by
    unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hw : Continuous (fun t : ℝ => ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) :=
    (hc.norm.pow 2).mul (continuous_fej.comp (continuous_const.mul continuous_id))
  have hpt (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 ≤
        (Real.pi ^ 2 / 4) * (‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) := by
    have ht' : |t| ≤ T := abs_le.mpr ht
    have hnear : |δ * t| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hδ]
      exact (mul_le_mul_of_nonneg_left ht' hδ.le).trans hδT
    have hlow := fejer_lower_half hnear
    have hone : (1 : ℝ) ≤ (Real.pi ^ 2 / 4) * fej (δ * t) := by
      calc
        1 = (Real.pi ^ 2 / 4) * (4 / Real.pi ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    have hh := mul_le_mul_of_nonneg_left hone (sq_nonneg ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖)
    nlinarith
  have he := congrArg Complex.re (fejer_exponential_energy s a freq hδ)
  simp only [← Complex.ofReal_inv, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  calc
    _ ≤ ∫ t in (-T)..T, (Real.pi ^ 2 / 4) *
        (‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) :=
      intervalIntegral.integral_mono_on (by linarith) ((hc.norm.pow 2).intervalIntegrable _ _)
        ((continuous_const.mul hw).intervalIntegrable _ _) hpt
    _ = (Real.pi ^ 2 / 4) * ∫ t in (-T)..T,
        ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi ^ 2 / 4) * ∫ t : ℝ,
        ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact setIntegral_le_integral (integrable_fejer_energy s a freq hδ)
        (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (fej_nonneg _)))
    _ = _ := by rw [he]; ring


/-- The real interval overlap kernel behind Gallagher 1970 p.330 Lemma 1. -/
theorem interval_window_overlap (a b δ : ℝ) (_hδ : 0 ≤ δ) :
    ∫ x : ℝ, (Set.Icc (a - δ) a).indicator (fun _ => (1 : ℝ)) x *
      (Set.Icc (b - δ) b).indicator (fun _ => (1 : ℝ)) x = max 0 (δ - |a - b|) := by
  have heq : (fun x : ℝ => (Set.Icc (a - δ) a).indicator (fun _ => (1 : ℝ)) x *
      (Set.Icc (b - δ) b).indicator (fun _ => (1 : ℝ)) x) =
      (Set.Icc (a - δ) a ∩ Set.Icc (b - δ) b).indicator (fun _ => 1) := by
    ext x
    simp only [← Set.inter_indicator_mul, one_mul]
  rw [heq, integral_indicator_const 1 (measurableSet_Icc.inter measurableSet_Icc),
    Set.Icc_inter_Icc, smul_eq_mul, mul_one, Real.volume_real_Icc]
  rw [max_comm]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right (by linarith : a - δ ≤ b - δ),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    congr 1; ring
  · rw [min_eq_right hba, max_eq_left (by linarith : b - δ ≤ a - δ),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    congr 1; ring


/-- A finite short interval sum in the frequency variable. -/
noncomputable def frequencyWindow {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (δ x : ℝ) : ℂ :=
  ∑ i ∈ s, (Set.Icc (freq i - δ) (freq i)).indicator (fun _ => a i) x


/-- Exact overlap identity for the short interval energy in Gallagher p.330. -/
theorem frequency_window_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ((∫ x : ℝ, ‖frequencyWindow s a freq δ x‖ ^ 2 : ℝ) : ℂ) =
      (δ : ℂ) * ∑ i ∈ s, ∑ j ∈ s, a i * (starRingEnd ℂ) (a j) *
        (tri ((freq i - freq j) / δ) : ℂ) := by
  let A : ι → Set ℝ := fun i => Set.Icc (freq i - δ) (freq i)
  have hAi (i j : ι) : Integrable (fun x => (A i ∩ A j).indicator
      (fun _ => a i * (starRingEnd ℂ) (a j)) x) := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_Icc.inter measurableSet_Icc)
    exact (continuous_const.integrableOn_Icc).mono_set Set.inter_subset_left
  have hpt (x : ℝ) : ((‖frequencyWindow s a freq δ x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator
        (fun _ => a i * (starRingEnd ℂ) (a j)) x := by
    unfold frequencyWindow
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    change (A i).indicator (fun _ => a i) x *
      (starRingEnd ℂ) ((A j).indicator (fun _ => a j) x) = _
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;>
      simp [hi, hj, Set.indicator_of_mem, Set.indicator_of_notMem]
  have hover (i j : ι) : volume.real (A i ∩ A j) =
      δ * tri ((freq i - freq j) / δ) := by
    have hi := interval_window_overlap (freq i) (freq j) δ hδ.le
    have he : (fun x : ℝ => (A i).indicator (fun _ => (1 : ℝ)) x *
        (A j).indicator (fun _ => (1 : ℝ)) x) =
        (A i ∩ A j).indicator (fun _ => (1 : ℝ)) := by
      ext x
      simp only [← Set.inter_indicator_mul, one_mul]
    change (∫ x : ℝ, (A i).indicator (fun _ => (1 : ℝ)) x *
      (A j).indicator (fun _ => (1 : ℝ)) x) = _ at hi
    rw [he, integral_indicator_const 1 (measurableSet_Icc.inter measurableSet_Icc),
      smul_eq_mul, mul_one] at hi
    rw [hi]
    unfold tri
    rw [abs_div, abs_of_pos hδ]
    by_cases h : |freq i - freq j| ≤ δ
    · rw [max_eq_right (by linarith), max_eq_right (by
        rw [sub_nonneg, div_le_one hδ]; exact h)]
      field_simp
    · have hh : δ < |freq i - freq j| := lt_of_not_ge h
      rw [max_eq_left (by linarith), max_eq_left (by
        rw [sub_nonpos, le_div_iff₀ hδ]; linarith)]
      ring
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j)), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hAi i j), mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_indicator_const _ (measurableSet_Icc.inter measurableSet_Icc), hover]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring


/-- Gallagher 1970 p.330 Lemma 1 for a finite family, with explicit constant.
Closed frequency windows change only finitely many endpoints in the outer integral. -/
theorem gallagher_window_smoothing {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 2) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / (4 * δ ^ 2)) * ∫ x : ℝ, ‖frequencyWindow s a freq δ x‖ ^ 2 := by
  have he := congrArg Complex.re (frequency_window_energy s a freq hδ)
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hh := gallagher_frequency_smoothing s a freq hδ hT hδT
  apply hh.trans_eq
  rw [he]
  field_simp


/-- Dropping the totient weights in Gallagher 1970 p.332 Lemma 3. -/
theorem large_sieve_unweighted
    (a : ℕ → ℂ) (M L Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + L), a n * χ n‖ ^ 2) ≤
      ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + L), ‖a n‖ ^ 2 := by
  apply le_trans _ (large_sieve a M L Q)
  apply sum_le_sum
  intro q hq
  have hq0 : 0 < q := (mem_Icc.mp hq).1
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hweight : (1 : ℝ) ≤ q / (q.totient : ℝ) := (le_div_iff₀ hφ0).mpr (by simpa using hφq)
  exact le_mul_of_one_le_left (sum_nonneg (fun _ _ => sq_nonneg _)) hweight


/-- The finite sieve applies to any subset of an integer interval. -/
theorem large_sieve_finset
    (s : Finset ℕ) (a : ℕ → ℂ) (M L Q : ℕ) (hs : s ⊆ Ioc M (M + L)) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
      ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  classical
  let b : ℕ → ℂ := fun n => if n ∈ s then a n else 0
  have hset : (Finset.Ioc M (M + L)).filter (fun n => n ∈ s) = s := by
    ext n
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hn => hs hn)
  have hsum {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ Ioc M (M + L), b n * χ n) = ∑ n ∈ s, a n * χ n := by
    simp only [b, ite_mul, zero_mul, ← sum_filter, hset]
  have henergy : (∑ n ∈ Ioc M (M + L), ‖b n‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    simp only [b, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
      ← sum_filter, hset]
  simpa only [hsum, henergy] using large_sieve_unweighted b M L Q


/-- Real endpoints cost at most two extra integers in the finite sieve. -/
theorem large_sieve_real_interval
    (s : Finset ℕ) (a : ℕ → ℂ) (Q : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ x ≤ n ∧ (n : ℝ) ≤ y) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
      (y - x + 2 + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  let M := ⌊x⌋₊ - 1
  let U := ⌊y⌋₊
  have hMU : M ≤ U := (Nat.sub_le _ _).trans (Nat.floor_mono hxy)
  have hs' : s ⊆ Ioc M (M + (U - M)) := by
    intro n hn
    have hn1 := (hs n hn).1
    have hxn : ⌊x⌋₊ ≤ n := by
      have := (Nat.floor_le hx).trans (hs n hn).2.1
      exact_mod_cast this
    have hny : n ≤ U := Nat.le_floor (hs n hn).2.2
    rw [Finset.mem_Ioc, Nat.add_sub_of_le hMU]
    dsimp [M]
    omega
  have hMlow : x - 2 ≤ (M : ℝ) := by
    have hfloor := Nat.lt_floor_add_one x
    have hnat : ⌊x⌋₊ ≤ M + 1 := by dsimp [M]; omega
    have hnatR : (⌊x⌋₊ : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  have hUL : ((U - M : ℕ) : ℝ) ≤ y - x + 2 := by
    rw [Nat.cast_sub hMU]
    have hu : (U : ℝ) ≤ y := Nat.floor_le (hx.trans hxy)
    linarith
  apply (large_sieve_finset s a M (U - M) Q hs').trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
  linarith


/-- Finite Dirichlet polynomial for Gallagher 1970 p.331 display 11. -/
noncomputable def characterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * χ n * Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)


/-- Primitive character mean square for Gallagher 1970 p.332 display 15. -/
noncomputable def hybridEnergy (Q N : ℕ) (a : ℕ → ℂ) (T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2


/-- The prime detector sum S of Gallagher 1970 p.333. -/
noncomputable def primeDetector {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x y v : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
    (Real.log p / (p : ℝ) : ℂ) * χ p *
      Complex.exp (-((Real.log p * v : ℝ) : ℂ) * Complex.I)


/-- Integrability of the finite frequency window energy. -/
theorem integrable_frequencyWindow_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (δ : ℝ) :
    Integrable (fun x : ℝ => ‖frequencyWindow s a freq δ x‖ ^ 2) := by
  have hi : Integrable (frequencyWindow s a freq δ) := by
    unfold frequencyWindow
    apply integrable_finsetSum
    intro i _
    exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hb (x : ℝ) : ‖frequencyWindow s a freq δ x‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    unfold frequencyWindow
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    by_cases hx : x ∈ Set.Icc (freq i - δ) (freq i)
    · simp [hx]
    · simp [hx]
  apply (hi.norm.const_mul (∑ i ∈ s, ‖a i‖)).mono'
  · exact hi.aestronglyMeasurable.norm.pow 2
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (frequencyWindow s a freq δ x))
    nlinarith


/-- The finite real interval sieve controls every logarithmic window. -/
theorem mellin_window_sieve
    (a : ℕ → ℂ) (Q N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2) ≤
      (Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n => u ∈ Set.Icc (Real.log n - δ) (Real.log n))
  have heq {q : ℕ} (χ : DirichletCharacter ℂ q) :
      frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u =
      ∑ n ∈ S, a n * χ n := by
    simp only [frequencyWindow, S, sum_filter, Set.indicator]
  have hnorm : (∑ n ∈ S, ‖a n‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
    simp only [S, sum_filter, Set.indicator]
  have hs : ∀ n ∈ S, 1 ≤ n ∧ Real.exp u ≤ n ∧ (n : ℝ) ≤ Real.exp (u + δ) := by
    intro n hn
    obtain ⟨hnN, hnu⟩ := mem_filter.mp hn
    have hn1 := (mem_Icc.mp hnN).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    refine ⟨hn1, ?_, ?_⟩
    · calc
        Real.exp u ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hnu.2
        _ = _ := Real.exp_log hnpos
    · calc
        (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp (u + δ) := Real.exp_le_exp.mpr (by linarith [hnu.1])
  simpa only [heq, hnorm] using large_sieve_real_interval S a Q
    (Real.exp_pos u).le (Real.exp_le_exp.mpr (by linarith)) hs


/-- The scalar logarithmic window integral in the proof of Gallagher Theorem 3. -/
theorem integral_mellin_window_weight (l B δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ u : ℝ, (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u =
      δ * (B + 2) + (Real.exp δ - 1) * (Real.exp l - Real.exp (l - δ)) := by
  have he : (fun u : ℝ => (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u) =
      (Set.Icc (l - δ) l).indicator (fun u => Real.exp (u + δ) - Real.exp u + 2 + B) := by
    ext u
    by_cases hu : u ∈ Set.Icc (l - δ) l <;> simp [hu]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : l - δ ≤ l)]
  have hd (u : ℝ) : HasDerivAt
      (fun u => (Real.exp δ - 1) * Real.exp u + (B + 2) * u)
      (Real.exp (u + δ) - Real.exp u + 2 + B) u := by
    convert ((Real.hasDerivAt_exp u).const_mul (Real.exp δ - 1)).add
      ((hasDerivAt_id u).const_mul (B + 2)) using 1 <;> first | rfl | (rw [Real.exp_add]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (u + δ) - Real.exp u + 2 + B)).intervalIntegrable _ _)]
  ring


/-- The scalar window coefficient has the hybrid scale, not the pointwise T loss. -/
theorem mellin_window_weight_bound (l B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ u : ℝ, (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u ≤
      δ * (B + 2) + 2 * δ ^ 2 * Real.exp l := by
  rw [integral_mellin_window_weight l B δ hδ]
  have habs : |δ| ≤ 1 := by rw [abs_of_nonneg hδ]; exact hδ1
  have h₁ : Real.exp δ - 1 ≤ 2 * δ := by
    have := Real.abs_exp_sub_one_le habs
    rw [abs_of_nonneg hδ] at this
    exact (le_abs_self _).trans this
  have h₂ : 1 - Real.exp (-δ) ≤ δ := by linarith [Real.add_one_le_exp (-δ)]
  have h₂0 : 0 ≤ 1 - Real.exp (-δ) := by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδ)
    linarith
  have hp := mul_le_mul h₁ h₂ h₂0 (by positivity : (0 : ℝ) ≤ 2 * δ)
  have he : Real.exp l - Real.exp (l - δ) = Real.exp l * (1 - Real.exp (-δ)) := by
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [he]
  have hpe := mul_le_mul_of_nonneg_right hp (Real.exp_pos l).le
  nlinarith


/-- Integrating the logarithmic windows gives Q squared delta plus n delta squared. -/
theorem integrated_mellin_window_sieve
    (a : ℕ → ℂ) (Q N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
          (fun n => Real.log n) δ u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 := by
  classical
  let K : ℝ → ℝ := fun u => Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2
  let W {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) :=
    ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have hiW {q : ℕ} (χ : DirichletCharacter ℂ q) : Integrable (W χ) :=
    integrable_frequencyWindow_energy _ _ _ _
  have hiR (n : ℕ) : Integrable (fun u => K u *
      (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u) := by
    have heq : (fun u => K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator
        (fun _ => ‖a n‖ ^ 2) u) =
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun u => K u * ‖a n‖ ^ 2) := by
      ext u
      by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n) <;> simp [hu]
    rw [heq]
    exact (by dsimp [K]; fun_prop : Continuous (fun u => K u * ‖a n‖ ^ 2)).integrableOn_Icc.integrable_indicator measurableSet_Icc
  have heq (q : ℕ) :
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) =
      ∫ u, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ u :=
    (integral_finsetSum _ (fun χ _ => hiW χ)).symm
  change (∑ q ∈ Finset.Icc 1 Q,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) ≤ _
  simp_rw [heq]
  rw [← integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun χ _ => hiW χ))]
  calc
    _ ≤ ∫ u, ∑ n ∈ Finset.Icc 1 N, K u *
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
      apply integral_mono
        (integrable_finsetSum _ (fun q _ => integrable_finsetSum _ (fun χ _ => hiW χ)))
        (integrable_finsetSum _ (fun n _ => hiR n))
      intro u
      dsimp only [W, K]
      rw [← mul_sum]
      exact mellin_window_sieve a Q N hδ.le u
    _ = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 *
        ∫ u : ℝ, K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => (1 : ℝ)) u := by
      rw [integral_finsetSum _ (fun n _ => hiR n)]
      apply sum_congr rfl
      intro n _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n)
      · simp [hu]; ring
      · simp [hu]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hb := mellin_window_weight_bound (Real.log n) ((Q : ℝ) ^ 2) hδ.le hδ1
      rw [Real.exp_log hnpos] at hb
      dsimp [K]
      have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a n‖)
      nlinarith


/-- Rescaling the Dirichlet polynomial height by two pi. -/
theorem characterPolynomial_time_integral {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) =
      (2 * Real.pi) * ∫ t in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
        ‖∑ n ∈ Finset.Icc 1 N, (a n * χ n) * LeanLab.PNTPort.LargeSieve.e (Real.log n * t)‖ ^ 2 := by
  let c : ℝ := -1 / (2 * Real.pi)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  let P : ℝ → ℝ := fun t => ‖∑ n ∈ Finset.Icc 1 N, (a n * χ n) * LeanLab.PNTPort.LargeSieve.e (Real.log n * t)‖ ^ 2
  have heq (v : ℝ) : ‖characterPolynomial χ a N v‖ ^ 2 = P (c * v) := by
    congr 2
    unfold characterPolynomial
    apply sum_congr rfl
    intro n _
    congr 1
    unfold LeanLab.PNTPort.LargeSieve.e
    congr 1
    dsimp [c]
    push_cast
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_comp_mul_left P hc]
  have h₁ : c * (-T) = T / (2 * Real.pi) := by dsimp [c]; ring
  have h₂ : c * T = -(T / (2 * Real.pi)) := by dsimp [c]; ring
  rw [h₁, h₂, intervalIntegral.integral_symm]
  dsimp [c, P]
  simp only [inv_div, inv_neg, inv_one, smul_eq_mul]
  ring


/-- Gallagher Theorem 3 from the sharp finite multiplicative large sieve. -/
theorem hybrid_mean_value_bound
    (Q N : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    hybridEnergy Q N a T ≤ (2 * Real.pi ^ 3) *
      ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  classical
  let δ : ℝ := 1 / T
  have hTpos : 0 < T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_one hTpos]; exact hT
  let C : ℝ := Real.pi ^ 3 / (2 * δ ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let W {q : ℕ} (χ : DirichletCharacter ℂ q) :=
    ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have htime {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) ≤ C * W χ := by
    rw [characterPolynomial_time_integral]
    have hnear : δ * (T / (2 * Real.pi)) ≤ 1 / 2 := by
      dsimp [δ]
      have he : (1 / T) * (T / (2 * Real.pi)) = 1 / (2 * Real.pi) := by field_simp
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Real.pi_gt_three]
    have hh := gallagher_window_smoothing (Finset.Icc 1 N) (fun n => a n * χ n)
      (fun n => Real.log n) hδ (div_nonneg hTpos.le (by positivity)) hnear
    apply (mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).trans_eq
    dsimp [C, W]
    ring
  unfold hybridEnergy
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), C * W χ :=
      sum_le_sum (fun q _ => sum_le_sum (fun χ _ => htime χ))
    _ = C * (∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ) := by
      simp only [mul_sum]
    _ ≤ C * ∑ n ∈ Finset.Icc 1 N, (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (integrated_mellin_window_sieve a Q N hδ hδ1) hC
    _ ≤ _ := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro n _
      rw [← mul_assoc, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hQsq : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
      have he : C * (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) =
          (Real.pi ^ 3 / 2) * T * ((Q : ℝ) ^ 2 + 2) + Real.pi ^ 3 * n := by
        dsimp [C, δ]
        field_simp
      rw [he]
      have hmult := mul_le_mul_of_nonneg_left
        (show (Q : ℝ) ^ 2 + 2 ≤ 3 * (Q : ℝ) ^ 2 by linarith)
        (show 0 ≤ (Real.pi ^ 3 / 2) * T by positivity)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hrest : 0 ≤ Real.pi ^ 3 * ((Q : ℝ) ^ 2 * T) := by positivity
      have hrest2 : 0 ≤ Real.pi ^ 3 * n := by positivity
      nlinarith


/-- Continuity in the height variable does not require an analytic number theory input. -/
theorem continuous_characterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) : Continuous (characterPolynomial χ a N) := by
  unfold characterPolynomial
  fun_prop


/-- Nonnegativity of the hybrid energy for nonnegative time. -/
theorem hybridEnergy_nonneg (Q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ hybridEnergy Q N a T := by
  unfold hybridEnergy
  apply sum_nonneg
  intro q _
  apply sum_nonneg
  intro χ _
  exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)


/-- Unit modulus of the height twist. -/
theorem norm_mellin_twist (n : ℕ) (t : ℝ) :
    ‖Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, neg_zero, mul_zero, zero_mul, sub_zero, Real.exp_zero]


/-- Integrating a fixed pointwise family bound gives the length of the time interval. -/
theorem hybridEnergy_le_of_pointwise (Q N : ℕ) (a : ℕ → ℂ) {T B : ℝ}
    (hT : 0 ≤ T)
    (hbound : ∀ t : ℝ, -T ≤ t → t ≤ T →
      ∑ q ∈ Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖characterPolynomial χ a N t‖ ^ 2 ≤ B) :
    hybridEnergy Q N a T ≤ 2 * T * B := by
  classical
  have hc {q : ℕ} (χ : DirichletCharacter ℂ q) :
      Continuous (fun t => ‖characterPolynomial χ a N t‖ ^ 2) :=
    (continuous_characterPolynomial χ a N).norm.pow 2
  have heq (q : ℕ) :
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) =
      ∫ t in (-T)..T,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖characterPolynomial χ a N t‖ ^ 2 :=
    (intervalIntegral.integral_finsetSum (fun χ _ => (hc χ).intervalIntegrable _ _)).symm
  unfold hybridEnergy
  simp_rw [heq]
  rw [← intervalIntegral.integral_finsetSum (fun q _ =>
    (continuous_finsetSum _ (fun χ _ => hc χ)).intervalIntegrable _ _)]
  calc
    _ ≤ ∫ t in (-T)..T, B := intervalIntegral.integral_mono_on (by linarith)
      ((continuous_finsetSum _ (fun q _ =>
        continuous_finsetSum _ (fun χ _ => hc χ))).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun t ht => hbound t ht.1 ht.2)
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring


/-- Pointwise application of the already proved multiplicative large sieve. -/
theorem characterPolynomial_pointwise_sieve
    (Q N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ q ∈ Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖characterPolynomial χ a N t‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  let b : ℕ → ℂ := fun n => a n * Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)
  have hI : Ioc 0 (0 + N) = Icc 1 N := by ext n; simp; omega
  have heq {q : ℕ} (χ : DirichletCharacter ℂ q) :
      characterPolynomial χ a N t = ∑ n ∈ Ioc 0 (0 + N), b n * χ n := by
    rw [hI]
    unfold characterPolynomial
    apply sum_congr rfl
    intro n _
    dsimp [b]
    ring
  have hnorm (n : ℕ) : ‖b n‖ = ‖a n‖ := by
    dsimp [b]
    rw [norm_mul, norm_mellin_twist, mul_one]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖characterPolynomial χ a N t‖ ^ 2 := by
      apply sum_le_sum
      intro q hq
      have hq0 : 0 < q := (mem_Icc.mp hq).1
      have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
      have hweight : (1 : ℝ) ≤ q / (q.totient : ℝ) := (le_div_iff₀ hφ0).mpr (by simpa using hφq)
      exact le_mul_of_one_le_left (sum_nonneg (fun _ _ => sq_nonneg _)) hweight
    _ = _ := by simp_rw [heq]
    _ ≤ _ := large_sieve b 0 N Q
    _ = _ := by rw [hI]; simp_rw [hnorm]


/-- Direct time integration of the pointwise sieve, with its full T loss visible. -/
theorem hybridEnergy_pointwise_bound
    (Q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    hybridEnergy Q N a T ≤
      2 * T * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
  have hh := hybridEnergy_le_of_pointwise Q N a hT
    (fun t _ _ => characterPolynomial_pointwise_sieve Q N a t)
  exact hh.trans_eq (by ring)


/-- The full hybrid coefficient follows for support length at most Q squared. -/
theorem hybridEnergy_short_support
    (Q N : ℕ) (a : ℕ → ℂ) (hN : N ≤ Q ^ 2) {T : ℝ} (hT : 0 ≤ T) :
    hybridEnergy Q N a T ≤
      4 * ∑ n ∈ Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  have hNr : (N : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hN
  calc
    _ ≤ 2 * T * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 :=
      hybridEnergy_pointwise_bound Q N a hT
    _ ≤ (4 * ((Q : ℝ) ^ 2 * T)) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
      nlinarith
    _ = 4 * ∑ n ∈ Icc 1 N, ((Q : ℝ) ^ 2 * T) * ‖a n‖ ^ 2 := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro n _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact le_add_of_nonneg_right (Nat.cast_nonneg n)


/-- The pointwise sieve coefficient does not imply the hybrid coefficient uniformly. -/
theorem pointwise_hybrid_coefficient_insufficient (C : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ C * ((N : ℝ) + N) < 2 * N * ((N : ℝ) + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 1)
  have hN1 : (1 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have hNC : C < (N : ℝ) := (le_max_left _ _).trans_lt hN
  refine ⟨N, by exact_mod_cast hN1.le, ?_⟩
  nlinarith


/-- Weighted Schwarz step in Gallagher 1970 p.336 before display 25. -/
theorem detector_weighted_cauchy {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (f w : α → ℝ) (hw : ∀ᵐ x ∂measure, 0 ≤ w x)
    (hwi : Integrable w measure) (hfi : Integrable (fun x => f x * w x) measure)
    (hf2i : Integrable (fun x => f x ^ 2 * w x) measure)
    (hwpos : 0 < ∫ x, w x ∂measure) :
    (∫ x, f x * w x ∂measure) ^ 2 ≤ (∫ x, w x ∂measure) * ∫ x, f x ^ 2 * w x ∂measure := by
  let c : ℝ := (∫ x, f x * w x ∂measure) / (∫ x, w x ∂measure)
  have heq : (fun x => (f x - c) ^ 2 * w x) =
      fun x => f x ^ 2 * w x - (2 * c) * (f x * w x) + c ^ 2 * w x := by
    ext x
    ring
  have _hi : Integrable (fun x => (f x - c) ^ 2 * w x) measure := by
    rw [heq]
    exact (hf2i.sub (hfi.const_mul _)).add (hwi.const_mul _)
  have hp : 0 ≤ ∫ x, (f x - c) ^ 2 * w x ∂measure :=
    integral_nonneg_of_ae (hw.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
  rw [heq] at hp
  rw [integral_add (f := fun x => f x ^ 2 * w x - (2 * c) * (f x * w x))
    (g := fun x => c ^ 2 * w x) (hf2i.sub (hfi.const_mul _)) (hwi.const_mul _),
    integral_sub (f := fun x => f x ^ 2 * w x)
    (g := fun x => (2 * c) * (f x * w x)) hf2i (hfi.const_mul _),
    integral_const_mul, integral_const_mul] at hp
  have hc : c * (∫ x, w x ∂measure) = ∫ x, f x * w x ∂measure := by
    dsimp [c]
    exact div_mul_cancel₀ _ hwpos.ne'
  nlinarith [mul_nonneg hp hwpos.le]


/-- Squaring a supplied L1 detector gives its weighted L2 lower bound. -/
theorem detector_l2_of_l1 {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (f w : α → ℝ) (hw : ∀ᵐ x ∂measure, 0 ≤ w x)
    (hwi : Integrable w measure) (hfi : Integrable (fun x => f x * w x) measure)
    (hf2i : Integrable (fun x => f x ^ 2 * w x) measure)
    (hwpos : 0 < ∫ x, w x ∂measure) {H : ℝ} (hH : 0 ≤ H)
    (hlower : H ≤ ∫ x, f x * w x ∂measure) :
    H ^ 2 / (∫ x, w x ∂measure) ≤ ∫ x, f x ^ 2 * w x ∂measure := by
  have hc := detector_weighted_cauchy measure f w hw hwi hfi hf2i hwpos
  rw [div_le_iff₀ hwpos]
  nlinarith


/-- Logarithmic mass in the Schwarz step before Gallagher 1970 display 25. -/
theorem logarithmic_window_mass {x : ℝ} (hx : 0 < x) (B : ℝ) :
    ∫ y in x..(x ^ B), (1 : ℝ) / y = (B - 1) * Real.log x := by
  rw [integral_one_div_of_pos hx (Real.rpow_pos_of_pos hx B),
    Real.log_div (Real.rpow_pos_of_pos hx B).ne' hx.ne', Real.log_rpow hx]
  ring


/-- Prime coefficient estimate in Gallagher 1970 p.336 after display 25. -/
theorem prime_log_sq_div_sum_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p ≤ Real.log N * (Real.log N + 7) := by
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, Real.log N * (Real.log p / p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hlog : Real.log p ≤ Real.log N :=
        Real.log_le_log hp0 (by exact_mod_cast hpN)
      have hlog0 : 0 ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
      have h := mul_le_mul_of_nonneg_right hlog (div_nonneg hlog0 hp0.le)
      convert h using 1; ring
    _ = Real.log N * LeanLab.PNTSieve.Mertens.C N := by
      rw [LeanLab.PNTSieve.Mertens.C_eq, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (LeanLab.PNTSieve.Mertens.C_le N hN) hL


/-- Large prime support removes the Q squared T part of the hybrid coefficient. -/
theorem prime_detector_coefficient_energy_le (N : ℕ) (hN : 1 ≤ N)
    (s : Finset ℕ) {K : ℝ}
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ N ∧ K ≤ p) :
    ∑ p ∈ s, (K + p) * (Real.log p / p) ^ 2 ≤
      2 * Real.log N * (Real.log N + 7) := by
  have hsub : s ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(hs p hp).2.1, (hs p hp).1⟩
  calc
    _ ≤ ∑ p ∈ s, 2 * (Real.log p ^ 2 / p) := by
      apply sum_le_sum
      intro p hp
      have hpp := hs p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.1.pos
      have hmul := mul_le_mul_of_nonneg_right hpp.2.2 (sq_nonneg (Real.log p / p))
      calc
        (K + p) * (Real.log p / p) ^ 2 ≤ ((p : ℝ) + p) * (Real.log p / p) ^ 2 := by
          nlinarith
        _ = 2 * (Real.log p ^ 2 / p) := by field_simp; ring
    _ ≤ ∑ p ∈ Nat.primesLE N, 2 * (Real.log p ^ 2 / p) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = 2 * ∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p := (mul_sum ..).symm
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left (prime_log_sq_div_sum_le N hN) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith


/-- Gallagher 1970 p.332 Theorem 3 display 15, derived here from
Theorem 1 and Lemma 3. The finite Dirichlet polynomial starts at one.
There is no unrestricted additive shift in the coefficient on the right. -/
theorem gallagher_hybrid_mean_value : ∃ C : ℝ, 0 < C ∧
    ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T → ∀ N : ℕ, ∀ a : ℕ → ℂ,
      hybridEnergy Q N a T ≤
        C * ∑ n ∈ Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  refine ⟨2 * Real.pi ^ 3, by positivity, ?_⟩
  intro Q hQ T hT N a
  exact hybrid_mean_value_bound Q N hQ a hT


section PortTuran
open Finset Complex


/-- Gallagher p.334 finite Turan applied to zeros repeated according to multiplicity. -/
private theorem pT_weighted_turan_power_sum {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ι → ℂ)
    {M : ℕ} (hM : (∑ i ∈ S, m i) ≤ M)
    (hz : ∃ i ∈ S, 0 < m i ∧ 1 ≤ ‖z i‖) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧
      (1 / 50 : ℝ) ^ M ≤ ‖∑ i ∈ S, (m i : ℂ) * z i ^ ν‖ := by
  classical
  let I := (i : S) × Fin (m i)
  let Z : I → ℂ := fun i => z i.1
  have hcard : Fintype.card I = ∑ i ∈ S, m i := by simp [I, Fintype.card_sigma, Finset.sum_attach]
  obtain ⟨i, hi, hm, hzi⟩ := hz
  let i₀ : I := ⟨⟨i, hi⟩, ⟨0, hm⟩⟩
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  let e := Fintype.equivFin I
  obtain ⟨ν, hν, hν', hsum⟩ := turan_power_sum_lower_bound hpos
    (by simpa [hcard] using hM) (fun j => Z (e.symm j))
    ⟨e i₀, by simpa [Z, i₀] using hzi⟩
  refine ⟨ν, hν, hν', ?_⟩
  have heq : (∑ j : Fin (Fintype.card I), Z (e.symm j) ^ ν) =
      ∑ i ∈ S, (m i : ℂ) * z i ^ ν := by
    calc
      _ = ∑ i : I, Z i ^ ν := e.symm.sum_comp _
      _ = _ := by
        simp only [I, Z, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Finset.sum_attach S (fun i => (m i : ℂ) * z i ^ ν)
  rwa [heq] at hsum

/-- Gallagher p.334 Turan lower bound for a finite reciprocal pole power sum. -/
private theorem pT_reciprocal_pole_turan {ι : Type*} (S : Finset ι) (m : ι → ℕ) (ρ : ι → ℂ)
    {M : ℕ} (hM : (∑ i ∈ S, m i) ≤ M) {r : ℝ} (hr : 0 < r) (s : ℂ)
    (hne : ∀ i ∈ S, s - ρ i ≠ 0)
    (hclose : ∃ i ∈ S, 0 < m i ∧ ‖s - ρ i‖ ≤ 2 * r) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧
      1 / (100 * r) ^ ν ≤ ‖∑ i ∈ S, (m i : ℂ) / (s - ρ i) ^ ν‖ := by
  classical
  let z : ι → ℂ := fun i => (2 * r : ℝ) / (s - ρ i)
  have hz : ∃ i ∈ S, 0 < m i ∧ 1 ≤ ‖z i‖ := by
    obtain ⟨i, hi, hm, hc⟩ := hclose
    refine ⟨i, hi, hm, ?_⟩
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      one_le_div (norm_pos_iff.mpr (hne i hi))]
    exact hc
  obtain ⟨ν, hν, hν', hsum⟩ := pT_weighted_turan_power_sum S m z hM hz
  refine ⟨ν, hν, hν', ?_⟩
  have heq : (∑ i ∈ S, (m i : ℂ) * z i ^ ν) =
      ((2 * r : ℝ) : ℂ) ^ ν * ∑ i ∈ S, (m i : ℂ) / (s - ρ i) ^ ν := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    dsimp [z]
    rw [div_pow]
    ring
  rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hsum
  have hp : (1 / 50 : ℝ) ^ ν ≤ (1 / 50 : ℝ) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hν.le
  have hl := hp.trans hsum
  have he : ((1 / 50 : ℝ) ^ ν) / (2 * r) ^ ν = 1 / (100 * r) ^ ν := by
    have hb : (1 / 50 : ℝ) / (2 * r) = 1 / (100 * r) := by field_simp; norm_num
    simpa only [div_pow, one_pow] using congrArg (fun x : ℝ => x ^ ν) hb
  rw [← he]
  exact (div_le_iff₀ (pow_pos (show 0 < 2 * r by positivity) ν)).2 (by simpa only [mul_comm] using hl)

section PortpC

open Finset Complex Set Metric
open scoped Classical
open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2

/-- Gallagher pp.333 and 334 local multiplicity bound in the global height scale.
The additive one in the local count is absorbed by r log T at least one.
No lower bound on r log of B q t is imposed. -/
private theorem pC_local_disc_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
        |t| ≤ T → 0 < r → 1 ≤ r * Real.log T →
        (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
          (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤ C * r * Real.log T := by
  obtain ⟨C₀, hC₀, hsmall⟩ := local_disc_order_sum_nonprincipal_add_one
  obtain ⟨K, hK, hheight⟩ := log_Bt_le_log_height
  let C : ℝ := max (C₀ * (1 + K)) (8 * K / Real.log (10 / 9))
  have hlog : 0 < Real.log (10 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := (by positivity : 0 ≤ C₀ * (1 + K)).trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T hT q hq hqT χ hχ t r ht hr hscale
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hB := hheight hT hqT ht
  by_cases hrl : r ≤ 1 / 8
  · have hcount := hsmall q χ hχ t r hr hrl
    have h1 : 1 + r * Real.log (Bt q t) ≤ (1 + K) * (r * Real.log T) := by
      have hh := mul_le_mul_of_nonneg_left hB hr.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC₀
    have h3 := mul_le_mul_of_nonneg_right (le_max_left (C₀ * (1 + K)) (8 * K / Real.log (10 / 9)))
      (mul_nonneg hr.le hL)
    exact hcount.trans (h2.trans (by dsimp [C]; nlinarith))
  · have htotal := zero_count_le hχ t
    have hsub : (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
        (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤
        ∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    apply hsub.trans (htotal.trans ?_)
    have hCr : K / Real.log (10 / 9 : ℝ) ≤ C * r := by
      have hcle : 8 * K / Real.log (10 / 9 : ℝ) ≤ C := le_max_right _ _
      have hr8 : 1 / 8 ≤ r := le_of_not_ge hrl
      have hh := mul_le_mul_of_nonneg_left hr8 (by positivity : 0 ≤ 8 * K / Real.log (10 / 9 : ℝ))
      have hh' := mul_le_mul_of_nonneg_right hcle hr.le
      have he : (8 * K / Real.log (10 / 9 : ℝ)) * (1 / 8) = K / Real.log (10 / 9 : ℝ) := by ring
      rw [he] at hh
      exact hh.trans hh'
    calc
      Real.log (Bt q t) / Real.log (10 / 9) ≤ (K * Real.log T) / Real.log (10 / 9) :=
        div_le_div_of_nonneg_right hB hlog.le
      _ ≤ C * r * Real.log T := by
        have hh := mul_le_mul_of_nonneg_right hCr hL
        convert hh using 1 <;> ring

/-- Gallagher p.334 the far zero power tail in the global height scale. -/
private theorem pC_far_zero_pole_power_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r cutoff : ℝ),
      |t| ≤ T → 0 ≤ r → 0 < cutoff → 1 ≤ cutoff * Real.log T → ∀ k : ℕ, 1 ≤ k →
      ‖∑ ρ ∈ (zset hχ t).filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖),
        (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
          C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, hlocal⟩ := pC_local_disc_order_sum_global
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro T hT q hq hqT χ hχ t r cutoff ht hr hcutoff hscale k hk
  let S := (zset hχ t).filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖)
  let w : ℂ → ℝ := fun ρ => analyticOrderNatAt (fShift χ t) ρ
  let R : ℂ → ℝ := fun ρ => ‖ρ + (1 / 2 : ℂ)‖
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hmass (u : ℝ) (hu : cutoff ≤ u) : (∑ ρ ∈ S.filter (fun ρ => R ρ ≤ u), w ρ) ≤
      (C₀ * Real.log T) * u := by
    have hsub : S.filter (fun ρ => R ρ ≤ u) ⊆ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ u) := by
      intro ρ hρ
      obtain ⟨hρS, hρR⟩ := mem_filter.mp hρ
      exact mem_filter.mpr ⟨(mem_filter.mp hρS).1, hρR⟩
    have hsc : 1 ≤ u * Real.log T := hscale.trans (mul_le_mul_of_nonneg_right hu hlog)
    have h := (sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ hρ' => Nat.cast_nonneg _)).trans
      (hlocal T hT q hqT χ hχ t u ht (hcutoff.trans_le hu) hsc)
    convert h using 1 <;> ring
  have htail := finite_dyadic_reciprocal_tail S w R (mul_nonneg hC₀ hlog) hcutoff
    (fun ρ hρ => Nat.cast_nonneg _) (fun ρ hρ => (mem_filter.mp hρ).2.le) hmass hk
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt (fShift χ t) ρ : ℂ) /
        ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, w ρ / R ρ ^ (k + 1) := by
      apply sum_le_sum
      intro ρ hρ
      have hρz := (mem_zset.mp (mem_filter.mp hρ).1).2
      have hre : (ρ + (1 / 2 : ℂ)).re ≤ 0 := by
        have hreal : (ρ + ((3 : ℂ) / 2 + I * t)).re < 1 := by
          by_contra h
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρz
        norm_num at hreal ⊢
        linarith
      have hdist : R ρ ≤ ‖(r : ℂ) - 1 / 2 - ρ‖ := by
        have h := norm_shift_right_ge hre hr
        convert h using 1 <;> congr 1 <;> ring
      have hRpos : 0 < R ρ := hcutoff.trans (mem_filter.mp hρ).2
      rw [norm_div, norm_pow, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hRpos _)
        (pow_le_pow_left₀ hRpos.le hdist _)
    _ ≤ _ := by convert htail using 1 <;> ring

/-- Gallagher p.334 display 21 in the global height scale for nonprincipal characters. -/
private theorem pC_near_zero_logDeriv_expansion_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r cutoff : ℝ),
      |t| ≤ T → 0 < r → r ≤ 1 / 8 → 0 < cutoff → cutoff ≤ 1 / 8 →
      1 ≤ cutoff * Real.log T → ∀ k : ℕ, 1 ≤ k →
      ‖iteratedDeriv k (logDeriv (fShift χ t)) ((r : ℂ) - 1 / 2) -
        (-1 : ℂ) ^ k * k.factorial *
          ∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff),
            (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) * C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, htail⟩ := pC_far_zero_pole_power_sum_global
  obtain ⟨K, hK, hheight⟩ := log_Bt_le_log_height
  refine ⟨K0 * K + C₀, by have := K0_pos; positivity, ?_⟩
  intro T hT q hq hqT χ hχ t r cutoff ht hr hrl hc hcl hscale k hk
  let z : ℂ := (r : ℂ) - 1 / 2
  let a : ℂ := (-1 : ℂ) ^ k * k.factorial
  let f : ℂ → ℂ := fShift χ t
  let P : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)
  let S := zset hχ t
  have hz : ‖z‖ ≤ 1 / 2 := by
    have he : z = ((r - 1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hne : f z ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    dsimp [z]
    norm_num
    linarith
  have hfull := iterated_logDeriv_pole_expansion_bound hχ t k hz hne
  have hlogBt : 0 ≤ Real.log (Bt q t) := Real.log_nonneg (one_lt_Bt t).le
  have hfull' := hfull.trans (show _ ≤ (k.factorial : ℝ) * K0 * (K * Real.log T) * 8 ^ k by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hheight hT hqT ht)
        (mul_nonneg (Nat.cast_nonneg k.factorial) K0_pos.le))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k)
    convert hh using 1 <;> ring)
  have hfar := htail T hT q hqT χ hχ t r cutoff ht hr.le hc hscale k hk
  have hsplit : (∑ ρ ∈ S, P ρ) =
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ) +
      (∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) := by
    simpa only [not_le] using (sum_filter_add_sum_filter_not S (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff) P).symm
  have ha : ‖a‖ = (k.factorial : ℝ) := by simp [a, norm_pow]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hp : (8 : ℝ) ^ k ≤ 1 / cutoff ^ k := by
    apply (le_div_iff₀ (pow_pos hc k)).2
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have htriangle : ‖iteratedDeriv k (logDeriv f) z -
      a * ∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ‖ ≤
      ‖iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ‖ +
        (k.factorial : ℝ) * ‖∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ‖ := by
    rw [← ha, ← norm_mul]
    convert norm_add_le (iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ)
      (a * ∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) using 1
    congr 1
    rw [hsplit]
    ring
  apply htriangle.trans
  have hb := add_le_add hfull' (mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg k.factorial))
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg k.factorial) (mul_nonneg (mul_nonneg K0_pos.le hK.le) hlog))
  convert add_le_add_right hh ((k.factorial : ℝ) * (C₀ * Real.log T / cutoff ^ k)) using 1 <;> ring

/-- Gallagher p.334 the nonprincipal large derivative in the global height scale.
This includes local logarithmic scales below one. -/
private theorem pC_nonprincipal_large_logDeriv_global : ∃ E : ℝ, 1 ≤ E ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      |t| ≤ T → 0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log T →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log T ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) ≤
            ‖iteratedDeriv k (logDeriv (fShift χ t)) ((r : ℂ) - 1 / 2)‖ := by
  obtain ⟨C₀, hC₀, hcount⟩ := pC_local_disc_order_sum_global
  obtain ⟨C₁, hC₁, hexp⟩ := pC_near_zero_logDeriv_expansion_global
  let E : ℝ := max 1 (max (200 * C₀) (200 * C₁))
  have hE : 1 ≤ E := le_max_left _ _
  refine ⟨E, hE, ?_⟩
  intro T hT q hq hqT χ hχ t r ht hr hrl hscale hroot M hM
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hc : 0 < 200 * r := by positivity
  have hcl : 200 * r ≤ 1 / 8 := by linarith
  have hscale' : 1 ≤ (200 * r) * Real.log T := by nlinarith
  let S := (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ 200 * r)
  let m : ℂ → ℕ := fun ρ => analyticOrderNatAt (fShift χ t) ρ
  let s : ℂ := (r : ℂ) - 1 / 2
  have hMcount : (∑ ρ ∈ S, m ρ) ≤ M := by
    have hc₀ : 200 * C₀ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
    have hbound := hcount T hT q hqT χ hχ t (200 * r) ht hc hscale'
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀ hr.le) hlog
    have hcast : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ M := hbound.trans (by nlinarith)
    exact_mod_cast hcast
  have hsne : fShift χ t s ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    dsimp [s]
    norm_num
    linarith
  have hne (ρ : ℂ) (hρ : ρ ∈ S) : s - ρ ≠ 0 := by
    intro he
    have hzero := (mem_zset.mp (mem_filter.mp hρ).1).2
    exact hsne (sub_eq_zero.mp he ▸ hzero)
  have hclose : ∃ ρ ∈ S, 0 < m ρ ∧ ‖s - ρ‖ ≤ 2 * r := by
    obtain ⟨ρ, hρ, hd⟩ := hroot
    let w := ρ - ((3 : ℂ) / 2 + I * t)
    have he : w + (1 / 2 : ℂ) = ρ - (1 + I * t) := by dsimp [w]; ring
    have hw : ‖w + (1 / 2 : ℂ)‖ ≤ r := by rwa [he]
    have hnorm : ‖w‖ ≤ 3 / 4 := by
      have hh := norm_sub_le (w + (1 / 2 : ℂ)) (1 / 2 : ℂ)
      norm_num at hh
      linarith
    have hzero : fShift χ t w = 0 := by simpa [fShift, w] using hρ
    have hwS : w ∈ S := mem_filter.mpr ⟨mem_zset.mpr ⟨hnorm, hzero⟩, by nlinarith⟩
    have hf : AnalyticOnNhd ℂ (fShift χ t) univ := fun z hz => fShift_analyticAt hχ t z
    have htop : analyticOrderAt (fShift χ t) w ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ w)
        (by rw [analyticOrderAt_eq_zero.mpr (Or.inr (fShift_zero_ne χ t))]; simp)
    have hm : m w ≠ 0 := by
      simp only [m, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(fShift_analyticAt hχ t w).analyticOrderAt_ne_zero.mpr hzero, htop⟩
    refine ⟨w, hwS, Nat.pos_of_ne_zero hm, ?_⟩
    have hh := norm_sub_le (r : ℂ) (w + (1 / 2 : ℂ))
    have he' : s - w = (r : ℂ) - (w + (1 / 2 : ℂ)) := by dsimp [s]; ring
    rw [he']
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  obtain ⟨ν, hν, hν', hpole⟩ := pT_reciprocal_pole_turan S m id hMcount hr s hne hclose
  let k := ν - 1
  have hν0 : 0 < ν := by omega
  have hkν : k + 1 = ν := Nat.sub_add_cancel hν0
  have hkM : M ≤ k := by dsimp [k]; omega
  have hklt : k < 2 * M := by dsimp [k]; omega
  have hMpos : 1 ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hr.le) hlog
    have hmreal : (1 : ℝ) ≤ M := hscale.trans (by nlinarith)
    exact_mod_cast hmreal
  have hk : 1 ≤ k := hMpos.trans hkM
  have hCM : 200 * C₁ * r * Real.log T ≤ (k : ℝ) := by
    have hc₁ : 200 * C₁ ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ hr.le) hlog
    have hm : (M : ℝ) ≤ k := by exact_mod_cast hkM
    linarith
  have habs := reciprocal_pole_error_absorbed hr hCM
  have herr := hexp T hT q hqT χ hχ t r (200 * r) ht hr (by linarith) hc hcl hscale' k hk
  let F : ℂ := iteratedDeriv k (logDeriv (fShift χ t)) s
  let P : ℂ := (-1 : ℂ) ^ k * k.factorial * ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) ^ (k + 1)
  have hPn : (k.factorial : ℝ) / (100 * r) ^ (k + 1) ≤ ‖P‖ := by
    have hh := mul_le_mul_of_nonneg_left hpole (Nat.cast_nonneg k.factorial)
    simpa [P, norm_mul, norm_pow, hkν, mul_div_assoc, div_eq_mul_inv] using hh
  have hFn : ‖F - P‖ ≤ (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) := by
    exact herr.trans (by convert mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg k.factorial) using 1 <;> ring)
  have htriangle : ‖P‖ ≤ ‖F‖ + ‖F - P‖ := by
    have hh := norm_add_le F (P - F)
    rw [norm_sub_rev P F] at hh
    simpa only [add_sub_cancel] using hh
  refine ⟨k, hkM, hklt, ?_⟩
  have heq : (k.factorial : ℝ) / (100 * r) ^ (k + 1) =
      2 * ((k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1))) := by ring
  rw [heq] at hPn
  linarith

/-- Gallagher p.334 principal Euler factor auxiliary. The sum of the
logarithms of the distinct prime divisors is at most the modulus logarithm. -/
private theorem pC_sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  have hp (p : ℕ) (hp : p ∈ q.primeFactors) : 0 < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.prod_primeFactors_dvd q)

/-- Gallagher p.334 principal Euler factor auxiliary. Every Euler power
has norm at most three quarters in the half plane of real part at least one half. -/
private theorem pC_norm_prime_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc
    (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / Real.sqrt p := by rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, one_div]
    _ ≤ 3 / 4 := by
      have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
      have hs2 := Real.sq_sqrt hp0.le
      have hsnn := Real.sqrt_nonneg (p : ℝ)
      apply (div_le_iff₀ hs0).mpr
      nlinarith

/-- Gallagher p.334 principal Euler factor auxiliary. The finite Euler
logarithmic derivative correction has norm at most three log q on real part
at least one half. The identity with L prime over L is a separate step. -/
private theorem pC_norm_euler_log_correction_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖∑ p ∈ q.primeFactors,
      (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))‖ ≤ 3 * Real.log q := by
  calc
    _ ≤ ∑ p ∈ q.primeFactors,
        ‖(Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, 3 * Real.log p := by
      apply sum_le_sum
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hz := pC_norm_prime_cpow_neg_le hpp hs
      have hden : (1 / 4 : ℝ) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
        have hh := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
        norm_num only [norm_one] at hh
        linarith
      have hlog := Real.log_natCast_nonneg p
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
      calc
        Real.log p * ‖(p : ℂ) ^ (-s)‖ / ‖1 - (p : ℂ) ^ (-s)‖ ≤
            (Real.log p * (3 / 4)) / (1 / 4) := by
          apply div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left hz hlog) (by norm_num) hden
        _ = 3 * Real.log p := by ring
    _ = 3 * ∑ p ∈ q.primeFactors, Real.log p := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (pC_sum_log_primeFactors_le q) (by norm_num)

/-- Gallagher p.334 principal Euler correction is analytic on the
closed half plane of real part at least one half. -/
private theorem pC_analyticAt_euler_log_correction (q : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))) s := by
  apply Finset.analyticAt_fun_sum
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  have hpow : AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hpn]
    fun_prop
  have hne : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    have hz := pC_norm_prime_cpow_neg_le hpp hs
    intro he
    have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hone, norm_one] at hz
    norm_num at hz
  exact (analyticAt_const.mul hpow).div (analyticAt_const.sub hpow) hne

/-- Gallagher p.334 differentiated principal Euler error auxiliary.
At every point of real part at least one, the kth derivative of the finite
Euler logarithmic correction is bounded by three k factorial log q times four to the k.
The identity with the principal logarithmic derivative remains separate. -/
private theorem pC_iteratedDeriv_euler_log_correction_le (q : ℕ) [NeZero q]
    (k : ℕ) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖iteratedDeriv k (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))) s‖ ≤
      (k.factorial : ℝ) * (3 * Real.log q) * 4 ^ k := by
  let f : ℂ → ℂ := fun z => ∑ p ∈ q.primeFactors,
    (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))
  have hhalf {z : ℂ} (hz : ‖z - s‖ ≤ 1 / 4) : 1 / 2 ≤ z.re := by
    have hh := (Complex.abs_re_le_norm (z - s)).trans hz
    rw [Complex.sub_re, abs_le] at hh
    linarith [hh.1]
  have hdc : DiffContOnCl ℂ f (ball s (1 / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    intro z hz
    have hn : ‖z - s‖ ≤ 1 / 4 := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact (pC_analyticAt_euler_log_correction q (hhalf hn)).differentiableAt.differentiableWithinAt
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 1 / 4) hdc (C := 3 * Real.log q) (by
      intro z hz
      have hn : ‖z - s‖ = 1 / 4 := by simpa [mem_sphere, dist_eq_norm] using hz
      exact pC_norm_euler_log_correction_le q (hhalf hn.le))
  simpa only [one_div, inv_pow, div_inv_eq_mul] using hh

/-- Gallagher p.334 principal logarithmic derivative identity.
Away from the pole and the zeta zeros in the right half plane, the
principal logarithmic derivative is the zeta logarithmic derivative plus
the finite Euler correction bounded above. -/
private theorem pC_principal_logDeriv_eq_zeta_add_euler (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hsne : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    logDeriv (1 : DirichletCharacter ℂ q).LFunction s = logDeriv riemannZeta s +
      ∑ p ∈ q.primeFactors,
        (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) := by
  let P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))
  have hfactor (p : ℕ) (hp : p ∈ q.primeFactors) : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    have hz := pC_norm_prime_cpow_neg_le (Nat.prime_of_mem_primeFactors hp) hs
    intro he
    have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hone, norm_one] at hz
    norm_num at hz
  have hderiv (p : ℕ) (hp : p ∈ q.primeFactors) :
      HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
        ((Real.log p : ℂ) * (p : ℂ) ^ (-s)) s := by
    have hp0 := (Nat.prime_of_mem_primeFactors hp).pos
    have hpn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp0)
    have hh := ((hasDerivAt_id s).neg.const_cpow (.inl hpn)).const_sub 1
    have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity : (0 : ℝ) ≤ p)]
    simpa only [Pi.neg_apply, id_eq, hlog, mul_neg, mul_one, neg_neg, neg_one_mul, one_mul, mul_comm] using hh
  have hP : P s ≠ 0 := prod_ne_zero_iff.mpr hfactor
  have hPd : DifferentiableAt ℂ P s :=
    DifferentiableAt.fun_finsetProd (fun p hp => (hderiv p hp).differentiableAt)
  have heq : (1 : DirichletCharacter ℂ q).LFunction =ᶠ[nhds s]
      (fun z => P z * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hsne] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz
  calc
    logDeriv (1 : DirichletCharacter ℂ q).LFunction s = logDeriv P s + logDeriv riemannZeta s := by
      rw [(logDeriv_congr_nhds heq).self_of_nhds,
        logDeriv_fun_mul s hP hzeta hPd (analyticAt_riemannZeta hsne).differentiableAt]
    _ = _ := by
      dsimp only [P]
      rw [logDeriv_fun_prod hfactor (fun p hp => (hderiv p hp).differentiableAt), add_comm]
      congr 1
      apply sum_congr rfl
      intro p hp
      rw [logDeriv_apply, (hderiv p hp).deriv]

/-- Gallagher pp.333 and 334 principal ambient multiplicity bound.
The finite zeta zero window has total multiplicity at most C log T.
The height exclusion is retained. -/
private theorem pC_zeta_window_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      ∀ hfin : (ZeroWindow t).Finite,
        (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log T := by
  obtain ⟨A, hA, hnorm⟩ := norm_logDeriv_right_halfplane
  obtain ⟨K, hK, herr⟩ := SumBoundI
  refine ⟨4 * (2 + A) + 2 * K, by positivity, ?_⟩
  intro T t hT ht htT hfin
  let s : ℂ := 1 + (1 / 2 : ℝ) + I * t
  let F : ℂ := deriv riemannZeta s / riemannZeta s
  let V : ℂ := ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)
  have hkey : ‖F - V‖ ≤ K * Real.log |t| := herr (1 / 2) (by constructor <;> norm_num) t ht hfin
  have hF : ‖F‖ ≤ 2 + A := by
    simpa [F, s, DirichletCharacter.LFunction_modOne_eq] using
      hnorm 1 1 t (1 / 2) (by constructor <;> norm_num)
  have hV : V.re ≤ 2 + A + K * Real.log |t| := by
    calc
      V.re ≤ ‖V‖ := Complex.re_le_norm _
      _ = ‖F - (F - V)‖ := by congr 1; ring
      _ ≤ ‖F‖ + ‖F - V‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hF hkey
  have hnear (ρ : ℂ) (hρ : ρ ∈ hfin.toFinset) :
      (analyticOrderNatAt riemannZeta ρ : ℝ) / 2 ≤
        ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re := by
    have hp := (Set.Finite.mem_toFinset hfin).mp hρ
    have hre : 1 / 2 ≤ (s - ρ).re := by
      have hrho : ρ.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hp.1)
      dsimp [s]
      norm_num
      linarith
    have hn : ‖s - ρ‖ ≤ 3 / 4 := by
      rw [norm_sub_rev]
      simpa only [s, show (1 : ℂ) + (1 / 2 : ℝ) = 3 / 2 by norm_num] using hp.2
    have hsq : Complex.normSq (s - ρ) ≤ (3 / 4 : ℝ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (s - ρ)]
    have hsqpos : 0 < Complex.normSq (s - ρ) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (s - ρ).im]
    simp only [Complex.div_re, Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    apply (le_div_iff₀ hsqpos).mpr
    have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
    have hlow := mul_le_mul_of_nonneg_left hre hm
    have hupp := mul_le_mul_of_nonneg_left hsq (div_nonneg hm (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have hsum : (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) / 2 ≤ V.re := by
    dsimp only [V]
    rw [Complex.re_sum, sum_div]
    exact sum_le_sum hnear
  have hlog : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) htT
  have hhalf : (1 / 2 : ℝ) ≤ Real.log T := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith [Real.log_two_gt_d9]
  have hmass := mul_le_mul_of_nonneg_left hlog hK.le
  have hconst := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * (2 + A) by linarith)
  nlinarith

/-- Gallagher pp.333 and 334 principal local density in the global height scale.
The bound is valid for every radius in the fixed ambient zeta window. -/
private theorem pC_zeta_disc_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T → 0 < r → 1 ≤ r * Real.log T →
      ∀ hfin : (ZeroWindow t).Finite,
        (∑ ρ ∈ hfin.toFinset.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r),
          (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * r * Real.log T := by
  obtain ⟨C₀, hC₀, hsmall⟩ := local_disc_order_sum_zeta_add_one
  obtain ⟨C₁, hC₁, htotal⟩ := pC_zeta_window_order_sum_global
  let C : ℝ := max (2 * C₀) (8 * C₁)
  refine ⟨C, (by positivity : 0 ≤ 2 * C₀).trans (le_max_left _ _), ?_⟩
  intro T t r hT ht htT hr hscale hfin
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  by_cases hrl : r ≤ 1 / 8
  · have hs := hsmall t r ht hr hrl hfin
    have hlogs := Real.log_le_log (by linarith : 0 < |t|) htT
    have h1 := mul_le_mul_of_nonneg_left hlogs hr.le
    have h2 := mul_le_mul_of_nonneg_left (show 1 + r * Real.log |t| ≤ 2 * (r * Real.log T) by nlinarith) hC₀
    have h3 := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) (8 * C₁)) (mul_nonneg hr.le hL)
    dsimp only [C]
    nlinarith
  · have hsub := sum_le_sum_of_subset_of_nonneg
      (filter_subset (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r) hfin.toFinset)
      (fun ρ _ _ => (Nat.cast_nonneg (analyticOrderNatAt riemannZeta ρ) : (0 : ℝ) ≤ _))
    have hs := htotal T t hT ht htT hfin
    have hcoeff : C₁ ≤ C * r := by
      have hh := mul_le_mul_of_nonneg_left (show 1 / 8 ≤ r by linarith) (show 0 ≤ 8 * C₁ by positivity)
      have hh' := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) (8 * C₁)) hr.le
      dsimp only [C]
      nlinarith
    exact hsub.trans (hs.trans (by convert mul_le_mul_of_nonneg_right hcoeff hL using 1 <;> ring))

/-- Gallagher p.334 the global principal local count in shifted coordinates.
The statement applies to any finite set of zeros in the fixed ambient disc. -/
private theorem pC_zeta_shift_local_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T → 0 < r → 1 ≤ r * Real.log T →
      ∀ S : Finset ℂ,
        (∀ ρ ∈ S, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4) →
        (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
          (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℝ)) ≤
            C * r * Real.log T := by
  obtain ⟨C, hC, hcount⟩ := pC_zeta_disc_order_sum_global
  refine ⟨C, hC, ?_⟩
  intro T t r hT ht htT hr hscale S hS
  let c : ℂ := 3 / 2 + I * t
  let V := S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r)
  let U := V.image (fun ρ => ρ + c)
  let hfin := ZeroWindowFinite ht
  have hsub : U ⊆ hfin.toFinset.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r) := by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hz
    obtain ⟨hρS, hρnear⟩ := mem_filter.mp hρ
    apply mem_filter.mpr
    constructor
    · apply (Set.Finite.mem_toFinset hfin).mpr
      constructor
      · simpa [c, add_assoc] using (hS ρ hρS).1
      · simpa [c] using (hS ρ hρS).2
    · have he : ρ + c - (1 + I * t) = ρ + 1 / 2 := by dsimp [c]; ring
      rwa [he]
  have hord (ρ : ℂ) :
      analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ =
        analyticOrderNatAt riemannZeta (ρ + c) := by
    have hf : (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) =
        (fun w : ℂ => riemannZeta (w + c)) := by
      funext w
      dsimp [c]
      congr 1
      ring
    rw [hf, analyticOrderNatAt_fun_comp_add_right]
  have heq : (∑ ρ ∈ V,
      (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℝ)) =
        ∑ z ∈ U, (analyticOrderNatAt riemannZeta z : ℝ) := by
    dsimp only [U]
    rw [sum_image (fun a ha b hb h => by exact add_right_cancel h)]
    simp only [hord]
  change (∑ ρ ∈ V, _) ≤ _
  rw [heq]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
    (hcount T t r hT ht htT hr hscale hfin)

/-- Gallagher p.334 the principal far zero power tail in the global height scale. -/
private theorem pC_zeta_far_zero_pole_power_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r cutoff : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      0 ≤ r → 0 < cutoff → 1 ≤ cutoff * Real.log T → ∀ k : ℕ, 1 ≤ k →
      ∀ S₀ : Finset ℂ,
        (∀ ρ ∈ S₀, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4) →
        ‖∑ ρ ∈ S₀.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖),
          (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℂ) /
            ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤ C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, hlocal⟩ := pC_zeta_shift_local_order_sum_global
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro T t r cutoff hT ht htT hr hcutoff hscale k hk S₀ hS
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  let S := S₀.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖)
  let w : ℂ → ℝ := fun ρ => analyticOrderNatAt f ρ
  let R : ℂ → ℝ := fun ρ => ‖ρ + (1 / 2 : ℂ)‖
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hmass (u : ℝ) (hu : cutoff ≤ u) : (∑ ρ ∈ S.filter (fun ρ => R ρ ≤ u), w ρ) ≤
      (C₀ * Real.log T) * u := by
    have hsub : S.filter (fun ρ => R ρ ≤ u) ⊆ S₀.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ u) := by
      intro ρ hρ
      obtain ⟨hρS, hρR⟩ := mem_filter.mp hρ
      exact mem_filter.mpr ⟨(mem_filter.mp hρS).1, hρR⟩
    have hsc : 1 ≤ u * Real.log T := hscale.trans (mul_le_mul_of_nonneg_right hu hlog)
    have hh := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
      (hlocal T t u hT ht htT (hcutoff.trans_le hu) hsc S₀ hS)
    convert hh using 1 <;> ring
  have htail := finite_dyadic_reciprocal_tail S w R (mul_nonneg hC₀ hlog) hcutoff
    (fun _ _ => Nat.cast_nonneg _) (fun _ hρ => (mem_filter.mp hρ).2.le) hmass hk
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt f ρ : ℂ) /
        ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, w ρ / R ρ ^ (k + 1) := by
      apply sum_le_sum
      intro ρ hρ
      have hρz := (hS ρ (mem_filter.mp hρ).1).1
      have hre : (ρ + (1 / 2 : ℂ)).re ≤ 0 := by
        have hreal : (ρ + 3 / 2 + I * t).re < 1 :=
          lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hρz)
        norm_num at hreal ⊢
        linarith
      have hdist : R ρ ≤ ‖(r : ℂ) - 1 / 2 - ρ‖ := by
        have hh := norm_shift_right_ge hre hr
        convert hh using 1 <;> congr 1 <;> ring
      have hRpos : 0 < R ρ := hcutoff.trans (mem_filter.mp hρ).2
      rw [norm_div, norm_pow, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hRpos _)
        (pow_le_pow_left₀ hRpos.le hdist _)
    _ ≤ _ := by convert htail using 1 <;> ring

/-- Gallagher p.334 display 21 in the global height scale for zeta.
The principal height exclusion is retained. -/
private theorem pC_zeta_near_zero_logDeriv_expansion_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r cutoff : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      0 < r → r ≤ 1 / 8 → 0 < cutoff → cutoff ≤ 1 / 8 →
      1 ≤ cutoff * Real.log T →
      ∀ hfin : (SetOfZeros 1 (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t))).Finite,
      ∀ k : ℕ, 1 ≤ k →
      ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t))) ((r : ℂ) - 1 / 2) -
        (-1 : ℂ) ^ k * k.factorial *
          ∑ ρ ∈ ((finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset).filter
              (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff),
            (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℂ) /
              ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) * C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, htail⟩ := pC_zeta_far_zero_pole_power_sum_global
  obtain ⟨A, hA, hfullbound⟩ := iterated_zeta_logDeriv_pole_expansion_bound
  refine ⟨A + C₀, by positivity, ?_⟩
  intro T t r cutoff hT ht htT hr hrl hc hcl hscale hfin k hk
  let z : ℂ := (r : ℂ) - 1 / 2
  let a : ℂ := (-1 : ℂ) ^ k * k.factorial
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  let P : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)
  let S := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset
  have hS : ∀ ρ ∈ S, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4 := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset _).mp hρ
    exact ⟨hh.2, hh.1⟩
  have hz : ‖z‖ ≤ 1 / 2 := by
    have he : z = ((r - 1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hne : f z ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [z]
    norm_num
    linarith
  have hfull := hfullbound t ht hfin k z hz hne
  have hfull' := hfull.trans (show _ ≤ (k.factorial : ℝ) * A * Real.log T * 8 ^ k by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith : 0 < |t|) htT)
        (mul_nonneg (Nat.cast_nonneg k.factorial) hA.le))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k)
    convert hh using 1 <;> ring)
  have hfar := htail T t r cutoff hT ht htT hr.le hc hscale k hk S hS
  have hsplit : (∑ ρ ∈ S, P ρ) =
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ) +
      (∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) := by
    simpa only [not_le] using (sum_filter_add_sum_filter_not S (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff) P).symm
  have ha : ‖a‖ = (k.factorial : ℝ) := by simp [a, norm_pow]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hp : (8 : ℝ) ^ k ≤ 1 / cutoff ^ k := by
    apply (le_div_iff₀ (pow_pos hc k)).2
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have htriangle : ‖iteratedDeriv k (logDeriv f) z -
      a * ∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ‖ ≤
      ‖iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ‖ +
        (k.factorial : ℝ) * ‖∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ‖ := by
    rw [← ha, ← norm_mul]
    convert norm_add_le (iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ)
      (a * ∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) using 1
    congr 1
    rw [hsplit]
    ring
  apply htriangle.trans
  have hb := add_le_add hfull' (mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg k.factorial))
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg k.factorial) (mul_nonneg hA.le hlog))
  convert add_le_add_right hh ((k.factorial : ℝ) * (C₀ * Real.log T / cutoff ^ k)) using 1 <;> ring


/-- Gallagher p.334 the principal zeta large derivative in the global height scale.
The height exclusion is retained and there are no character Euler factors in this step. -/
private theorem pC_zeta_large_logDeriv_global : ∃ E : ℝ, 1 ≤ E ∧
    ∀ T t r : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log T →
      (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log T ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) ≤
            ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)))
              ((r : ℂ) - 1 / 2)‖ := by
  obtain ⟨C₀, hC₀, hcount⟩ := pC_zeta_shift_local_order_sum_global
  obtain ⟨C₁, hC₁, hexp⟩ := pC_zeta_near_zero_logDeriv_expansion_global
  let E : ℝ := max 1 (max (200 * C₀) (200 * C₁))
  have hE : 1 ≤ E := le_max_left _ _
  refine ⟨E, hE, ?_⟩
  intro T t r hT ht htT hr hrl hscale hroot M hM
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hc : 0 < 200 * r := by positivity
  have hcl : 200 * r ≤ 1 / 8 := by linarith
  have hscale' : 1 ≤ (200 * r) * Real.log T := by nlinarith
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  let hfin := ZetaShiftFiniteZeros ht (f := f) rfl
  let S₀ := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset
  have hS₀ : ∀ ρ ∈ S₀, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4 := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset _).mp hρ
    exact ⟨hh.2, hh.1⟩
  let S := S₀.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ 200 * r)
  let m : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ
  let s : ℂ := (r : ℂ) - 1 / 2
  have hMcount : (∑ ρ ∈ S, m ρ) ≤ M := by
    have hc₀ : 200 * C₀ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
    have hbound := hcount T t (200 * r) hT ht htT hc hscale' S₀ hS₀
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀ hr.le) hlog
    have hcast : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ M := hbound.trans (by nlinarith)
    exact_mod_cast hcast
  have hsne : f s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [s]
    norm_num
    linarith
  have hne (ρ : ℂ) (hρ : ρ ∈ S) : s - ρ ≠ 0 := by
    intro he
    have hzero := (hS₀ ρ (mem_filter.mp hρ).1).1
    exact hsne (sub_eq_zero.mp he ▸ hzero)
  have hclose : ∃ ρ ∈ S, 0 < m ρ ∧ ‖s - ρ‖ ≤ 2 * r := by
    obtain ⟨ρ, hρ, hd⟩ := hroot
    let w := ρ - ((3 : ℂ) / 2 + I * t)
    have he : w + (1 / 2 : ℂ) = ρ - (1 + I * t) := by dsimp [w]; ring
    have hw : ‖w + (1 / 2 : ℂ)‖ ≤ r := by rwa [he]
    have hnorm : ‖w‖ ≤ 3 / 4 := by
      have hh := norm_sub_le (w + (1 / 2 : ℂ)) (1 / 2 : ℂ)
      norm_num at hh
      linarith
    have hew : w + 3 / 2 + I * t = ρ := by dsimp [w]; ring
    have hzero : f w = 0 := by simpa only [f, hew] using hρ
    have hwS : w ∈ S := mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hnorm, hzero⟩, by nlinarith⟩
    have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) := by
      intro u hu
      have hnormu : ‖u‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hu
      have hsne' : u + 3 / 2 + I * (t : ℂ) ≠ 1 := by
        intro he'
        have hi := congrArg Complex.im he'
        simp only [add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, I_re, ofReal_im,
          mul_zero, I_im, ofReal_re, one_mul, zero_add, one_im] at hi
        have habs := Complex.abs_im_le_norm u
        have hh : u.im = -t := by linarith
        rw [hh, abs_neg] at habs
        linarith
      exact AnalyticAt.fun_comp (analyticAt_riemannZeta hsne')
        ((analyticAt_id.fun_add analyticAt_const).fun_add analyticAt_const)
    have h0 : f 0 ≠ 0 := by
      dsimp [f]
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    have hwball : w ∈ closedBall (0 : ℂ) 1 := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have htop : analyticOrderAt f w ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected Metric.isPreconnected_closedBall
        (show (0 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp) hwball
        (by rw [analyticOrderAt_eq_zero.mpr (Or.inr h0)]; simp)
    have hm : m w ≠ 0 := by
      simp only [m, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(hf w hwball).analyticOrderAt_ne_zero.mpr hzero, htop⟩
    refine ⟨w, hwS, Nat.pos_of_ne_zero hm, ?_⟩
    have hh := norm_sub_le (r : ℂ) (w + (1 / 2 : ℂ))
    have he' : s - w = (r : ℂ) - (w + (1 / 2 : ℂ)) := by dsimp [s]; ring
    rw [he']
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  obtain ⟨ν, hν, hν', hpole⟩ := pT_reciprocal_pole_turan S m id hMcount hr s hne hclose
  let k := ν - 1
  have hν0 : 0 < ν := by omega
  have hkν : k + 1 = ν := Nat.sub_add_cancel hν0
  have hkM : M ≤ k := by dsimp [k]; omega
  have hklt : k < 2 * M := by dsimp [k]; omega
  have hMpos : 1 ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hr.le) hlog
    have hmreal : (1 : ℝ) ≤ M := hscale.trans (by nlinarith)
    exact_mod_cast hmreal
  have hk : 1 ≤ k := hMpos.trans hkM
  have hCM : 200 * C₁ * r * Real.log T ≤ (k : ℝ) := by
    have hc₁ : 200 * C₁ ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ hr.le) hlog
    have hm : (M : ℝ) ≤ k := by exact_mod_cast hkM
    linarith
  have habs := reciprocal_pole_error_absorbed hr hCM
  have herr := hexp T t r (200 * r) hT ht htT hr (by linarith) hc hcl hscale' hfin k hk
  let F : ℂ := iteratedDeriv k (logDeriv (f)) s
  let P : ℂ := (-1 : ℂ) ^ k * k.factorial * ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) ^ (k + 1)
  have hPn : (k.factorial : ℝ) / (100 * r) ^ (k + 1) ≤ ‖P‖ := by
    have hh := mul_le_mul_of_nonneg_left hpole (Nat.cast_nonneg k.factorial)
    simpa [P, norm_mul, norm_pow, hkν, mul_div_assoc, div_eq_mul_inv] using hh
  have hFn : ‖F - P‖ ≤ (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) := by
    exact herr.trans (by convert mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg k.factorial) using 1 <;> ring)
  have htriangle : ‖P‖ ≤ ‖F‖ + ‖F - P‖ := by
    have hh := norm_add_le F (P - F)
    rw [norm_sub_rev P F] at hh
    simpa only [add_sub_cancel] using hh
  refine ⟨k, hkM, hklt, ?_⟩
  have heq : (k.factorial : ℝ) / (100 * r) ^ (k + 1) =
      2 * ((k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1))) := by ring
  rw [heq] at hPn
  linarith

end PortpC

section PortpA

open Complex MeasureTheory Finset
open scoped Classical LSeries.notation
open LeanLab.Linnik.Decomp1532b2

/-- Gallagher p.334 display 22. The arithmetic series norm is exactly the
normalized logarithmic derivative norm in the right half plane. -/
private theorem pA_poisson_norm_eq_derivative_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) {r : ℝ} (hr : 0 < r) (v : ℝ) :
    ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
      (n : ℂ) ^ (1 + I * v)) * (poissonKernel k (r * Real.log n) : ℂ)‖ =
      (r ^ k / (k.factorial : ℝ)) *
        ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z)
          (1 + r + I * v)‖ := by
  rw [← normalized_log_series_eq_poisson]
  have hs : 1 < (1 + (r : ℂ) + I * v).re := by simp; linarith
  rw [iterated_neg_logDeriv_eq_LSeries χ k hs]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- Gallagher p.334 display 22. A derivative lower bound supplies the
arithmetic lower bound by an exact identity. No zero premise is needed. -/
private theorem pA_poisson_lower_of_derivative_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) {r D η : ℝ} (hr : 0 < r) (hD : 0 < D) (v : ℝ)
    (h : η * (k.factorial : ℝ) / (D ^ k * r ^ (k + 1)) ≤
      ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z)
        (1 + r + I * v)‖) :
    η / (D ^ k * r) ≤
      ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
        (n : ℂ) ^ (1 + I * v)) * (poissonKernel k (r * Real.log n) : ℂ)‖ := by
  rw [pA_poisson_norm_eq_derivative_norm χ k hr v]
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ r ^ k / (k.factorial : ℝ) by positivity)
  convert hh using 1
  simp only [pow_succ]
  field_simp
  <;> ring

/-- Gallagher p.334 translating the shifted logarithmic derivative back to
minus L prime over L preserves the norm of every derivative. -/
private theorem pA_shifted_logDeriv_norm_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) (r v : ℝ) :
    ‖iteratedDeriv k (logDeriv (LeanLab.PNTPort.DirichletZF.fShift χ v)) ((r : ℂ) - 1 / 2)‖ =
      ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z) (1 + r + I * v)‖ := by
  have hfun : logDeriv (LeanLab.PNTPort.DirichletZF.fShift χ v) =
      (fun z => logDeriv χ.LFunction (z + ((3 : ℂ) / 2 + I * v))) := by
    funext z
    change deriv (fun w => χ.LFunction (w + ((3 : ℂ) / 2 + I * v))) z /
      χ.LFunction (z + ((3 : ℂ) / 2 + I * v)) = _
    rw [deriv_comp_add_const]
    rfl
  rw [hfun, iteratedDeriv_comp_add_const]
  have hpoint : ((r : ℂ) - 1 / 2) + ((3 : ℂ) / 2 + I * v) = 1 + r + I * v := by ring
  dsimp only
  rw [hpoint]
  have hneg : (fun z => -deriv χ.LFunction z / χ.LFunction z) =
      (fun z => -logDeriv χ.LFunction z) := by funext z; simp [logDeriv_apply, neg_div]
  rw [hneg, iteratedDeriv_fun_neg, norm_neg]

/-- Gallagher p.334 display 22 for every nonprincipal character in the global
height scale. This includes local logarithmic scales below one. -/
private theorem pA_nonprincipal_poisson_global : ∃ E : ℝ, 1 ≤ E ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ v r : ℝ,
        |v| ≤ T → 0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log T →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            (1 / 200 : ℝ) / ((100 : ℝ) ^ k * r) ≤
              ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ (1 + I * v)) * (poissonKernel k (r * Real.log n) : ℂ)‖ := by
  obtain ⟨E, hE, hlarge⟩ := pC_nonprincipal_large_logDeriv_global
  refine ⟨E, hE, ?_⟩
  intro T hT q hq hqT χ hχ v r hv hr hrhi hscale hz M hM
  obtain ⟨k, hklo, hkhi, hk⟩ := hlarge T hT q hqT χ hχ v r hv hr hrhi hscale hz M hM
  rw [pA_shifted_logDeriv_norm_eq] at hk
  refine ⟨k, hklo, hkhi, pA_poisson_lower_of_derivative_lower χ k hr (by norm_num) v ?_⟩
  convert hk using 1
  simp only [mul_pow, pow_succ]
  field_simp
  <;> ring

/-- Gallagher 1970 p.334 display 21 and the derivative lower bound
immediately before display 22, restricted to principal characters.
There is no arithmetic series, smoothing kernel, finite window or integral.
The height exclusion and the differentiated finite Euler factors are retained. -/
private theorem pA_principal_large_logarithmic_derivative :
    ∃ r₀ E D η : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ E ∧ 1 ≤ D ∧ 0 < η ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ v r : ℝ,
        |v| ≤ T → 2 ≤ |v| → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            η * (k.factorial : ℝ) / (D ^ k * r ^ (k + 1)) ≤
              ‖iteratedDeriv k (fun z => -deriv χ.LFunction z / χ.LFunction z)
                (1 + r + I * v)‖ := by
  obtain ⟨Eζ, hEζ, hzetaLarge⟩ := pC_zeta_large_logDeriv_global
  refine ⟨1 / 1600, max Eζ 1200, 100, 1 / 400,
    by norm_num, by norm_num, hEζ.trans (le_max_left _ _), by norm_num, by norm_num, ?_⟩
  intro T hT q hq hqT χ hχ v r hv hvlo hrlo hrhi hz M hM
  subst χ
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlog).trans_le hrlo
  have hscale : 1 ≤ r * Real.log T := by
    have hh := mul_le_mul_of_nonneg_right hrlo hlog.le
    have he : (1 / Real.log T) * Real.log T = 1 := by field_simp
    rwa [he] at hh
  have hMζ : Eζ * r * Real.log T ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left Eζ 1200) (mul_nonneg hr.le hlog.le)
    nlinarith
  have hroot : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ r := by
    obtain ⟨ρ, hρ, hnear⟩ := hz
    have hreabs := (Complex.abs_re_le_norm (ρ - (1 + v * I))).trans hnear
    have himabs := (Complex.abs_im_le_norm (ρ - (1 + v * I))).trans hnear
    have hre : 1 / 2 ≤ ρ.re := by
      norm_num at hreabs
      have hh := (abs_le.mp hreabs).1
      linarith
    have hρne : ρ ≠ 1 := by
      intro he
      rw [he] at himabs
      norm_num at himabs
      linarith
    have hprod : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-ρ))) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro p hp
      have hnorm := pC_norm_prime_cpow_neg_le (Nat.prime_of_mem_primeFactors hp) hre
      intro he
      have hone : (p : ℂ) ^ (-ρ) = 1 := (sub_eq_zero.mp he).symm
      rw [hone, norm_one] at hnorm
      norm_num at hnorm
    change DirichletCharacter.LFunctionTrivChar q ρ = 0 at hρ
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hρne] at hρ
    have hζ : riemannZeta ρ = 0 := (mul_eq_zero.mp hρ).resolve_left hprod
    exact ⟨ρ, hζ, by simpa only [mul_comm (v : ℂ) I] using hnear⟩
  obtain ⟨k, hklo, hkhi, hkζ⟩ := hzetaLarge T v r hT hvlo hv hr hrhi hscale hroot M hMζ
  let s : ℂ := 1 + r + I * v
  let e : ℂ → ℂ := fun z => ∑ p ∈ q.primeFactors,
    (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))
  have hs : 1 < s.re := by dsimp [s]; norm_num; linarith
  have hsne : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have heζ :
      ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * v))) ((r : ℂ) - 1 / 2)‖ =
        ‖iteratedDeriv k (fun z => -deriv riemannZeta z / riemannZeta z) s‖ := by
    have hh := pA_shifted_logDeriv_norm_eq (1 : DirichletCharacter ℂ 1) k r v
    have hshift : LeanLab.PNTPort.DirichletZF.fShift (1 : DirichletCharacter ℂ 1) v =
        (fun w : ℂ => riemannZeta (w + 3 / 2 + I * v)) := by
      funext w
      change (1 : DirichletCharacter ℂ 1).LFunction (w + ((3 : ℂ) / 2 + I * v)) = _
      rw [DirichletCharacter.LFunction_modOne_eq]
      congr 1
      ring
    rw [hshift] at hh
    simpa only [DirichletCharacter.LFunction_modOne_eq, s] using hh
  rw [heζ] at hkζ
  have heq : (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
      (1 : DirichletCharacter ℂ q).LFunction z) =ᶠ[nhds s]
        (fun z => -deriv riemannZeta z / riemannZeta z - e z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    have hzne : z ≠ 1 := by intro he; rw [he] at hz; norm_num at hz
    have hh := pC_principal_logDeriv_eq_zeta_add_euler q
      (by linarith : 1 / 2 ≤ z.re) hzne (riemannZeta_ne_zero_of_one_lt_re hz)
    simpa only [e, logDeriv_apply, neg_add, neg_div, sub_eq_add_neg] using congrArg (fun w : ℂ => -w) hh
  have hζan : AnalyticAt ℂ (fun z => -deriv riemannZeta z / riemannZeta z) s :=
    ((analyticAt_riemannZeta hsne).deriv.neg).div (analyticAt_riemannZeta hsne)
      (riemannZeta_ne_zero_of_one_lt_re hs)
  have hean : AnalyticAt ℂ e s :=
    pC_analyticAt_euler_log_correction q (by linarith)
  have hder := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_fun_sub hζan.contDiffAt hean.contDiffAt] at hder
  have hEuler := pC_iteratedDeriv_euler_log_correction_le q k
    (s := s) hs.le
  have hlogq : Real.log q ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) hqT
  have hErr : ‖iteratedDeriv k e s‖ ≤ (k.factorial : ℝ) * 3 * Real.log T * 4 ^ k := by
    apply hEuler.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogq (show 0 ≤ (k.factorial : ℝ) * 3 by positivity))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) k)
    convert hh using 1 <;> ring
  have h1200 : 1200 * r * Real.log T ≤ (k : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right Eζ 1200) (mul_nonneg hr.le hlog.le)
    have hk : (M : ℝ) ≤ k := by exact_mod_cast hklo
    nlinarith
  have habs := reciprocal_pole_error_absorbed (C := 6) (massLog := Real.log T) hr
    (show 200 * 6 * r * Real.log T ≤ (k : ℝ) by nlinarith)
  have hp : (4 : ℝ) ^ k ≤ 1 / (200 * r) ^ k := by
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 200 * r) k)).mpr
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have hquarter : ‖iteratedDeriv k e s‖ ≤ (k.factorial : ℝ) / (4 * (100 * r) ^ (k + 1)) := by
    apply hErr.trans
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (k.factorial : ℝ) * 3 * Real.log T by positivity)
    apply hh.trans
    convert mul_le_mul_of_nonneg_left habs (show 0 ≤ (k.factorial : ℝ) / 2 by positivity) using 1 <;> ring
  have htri : ‖iteratedDeriv k (fun z => -deriv riemannZeta z / riemannZeta z) s‖ ≤
      ‖iteratedDeriv k (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
        (1 : DirichletCharacter ℂ q).LFunction z) s‖ + ‖iteratedDeriv k e s‖ := by
    calc
      _ = ‖iteratedDeriv k (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
          (1 : DirichletCharacter ℂ q).LFunction z) s + iteratedDeriv k e s‖ := by
            rw [hder, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have htarget : (k.factorial : ℝ) / (4 * (100 * r) ^ (k + 1)) ≤
      ‖iteratedDeriv k (fun z => -deriv (1 : DirichletCharacter ℂ q).LFunction z /
        (1 : DirichletCharacter ℂ q).LFunction z) s‖ := by
    have he : (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) =
        2 * ((k.factorial : ℝ) / (4 * (100 * r) ^ (k + 1))) := by ring
    rw [he] at hkζ
    linarith
  refine ⟨k, hklo, hkhi, ?_⟩
  convert htarget using 1
  simp only [mul_pow, pow_succ]
  field_simp
  <;> ring

/-- Gallagher p.334 monotonicity of the detector constants.
The numerator decreases and the exponential denominator increases. -/
private theorem pA_detector_constant_mono {η η' D D' r : ℝ} (k : ℕ)
    (hη : η ≤ η') (hη' : 0 ≤ η') (hD : 1 ≤ D) (hDD' : D ≤ D') (hr : 0 < r) :
    η / (D' ^ k * r) ≤ η' / (D ^ k * r) := by
  have hD0 : 0 < D := by linarith
  have hD'0 : 0 < D' := hD0.trans_le hDD'
  calc
    η / (D' ^ k * r) ≤ η' / (D' ^ k * r) :=
      div_le_div_of_nonneg_right hη (by positivity)
    _ ≤ η' / (D ^ k * r) :=
      div_le_div_of_nonneg_left hη' (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD0.le hDD' k) hr.le)

/-- Gallagher p.334 display 22. Exact sealed series statement assembled from
the principal derivative estimate and the global nonprincipal detector. -/
private theorem pA_poisson_series_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ E D η : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ E ∧ 1 ≤ D ∧ 0 < η ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            η / (D ^ k * r) ≤
              ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ (1 + I * v)) * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ := by
  obtain ⟨rₚ, Eₚ, Dₚ, ηₚ, hrₚ, hrₚhi, hEₚ, hDₚ, hηₚ, hprincipal⟩ :=
    pA_principal_large_logarithmic_derivative
  obtain ⟨Eₙ, hEₙ, hnonprincipal⟩ := pA_nonprincipal_poisson_global
  refine ⟨min rₚ (1 / 1600), max Eₚ Eₙ, max Dₚ 100, min ηₚ (1 / 200),
    lt_min hrₚ (by norm_num), (min_le_left _ _).trans hrₚhi,
    hEₚ.trans (le_max_left _ _), hDₚ.trans (le_max_left _ _),
    lt_min hηₚ (by norm_num), ?_⟩
  intro T hT q hq hqT χ v r hv hχ hrlo hrhi hz M hM
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlog).trans_le hrlo
  have hscale : 1 ≤ r * Real.log T := by
    have hh := mul_le_mul_of_nonneg_right hrlo hlog.le
    have he : (1 / Real.log T) * Real.log T = 1 := by field_simp
    rwa [he] at hh
  have hMp : Eₚ * r * Real.log T ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left Eₚ Eₙ) (mul_nonneg hr.le hlog.le)
    nlinarith
  have hMn : Eₙ * r * Real.log T ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right Eₚ Eₙ) (mul_nonneg hr.le hlog.le)
    nlinarith
  by_cases hp : χ = 1
  · obtain ⟨k, hklo, hkhi, hk⟩ := hprincipal T hT q hqT χ hp v r hv (hχ hp) hrlo
      (hrhi.trans (min_le_left _ _)) hz M hMp
    refine ⟨k, hklo, hkhi, ?_⟩
    exact (pA_detector_constant_mono k (min_le_left _ _) hηₚ.le hDₚ (le_max_left _ _) hr).trans
      (pA_poisson_lower_of_derivative_lower χ k hr (by linarith) v hk)
  · have hz' : ∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ r := by
      simpa only [mul_comm (v : ℂ) I] using hz
    obtain ⟨k, hklo, hkhi, hk⟩ := hnonprincipal T hT q hqT χ hp v r hv hr
      (hrhi.trans (min_le_right _ _)) hscale hz' M hMn
    refine ⟨k, hklo, hkhi, ?_⟩
    exact (pA_detector_constant_mono k (min_le_right _ _) (by norm_num) (by norm_num : (1 : ℝ) ≤ 100)
      (le_max_right _ _) hr).trans hk

end PortpA

section PortpW

open Finset MeasureTheory Complex
open scoped Classical
open LeanLab.Linnik.Decomp1532b2

/-- Gallagher p.335 the smoothing kernel is smooth on the real line. -/
private theorem pW_contDiff_poissonKernel (k : ℕ) : ContDiff ℝ 2 (Decomp1532b2.poissonKernel k) := by
  unfold Decomp1532b2.poissonKernel
  fun_prop

/-- Gallagher p.335 chain rule for the logarithmic smoothing kernel. -/
private theorem pW_poisson_log_hasDerivAt (k : ℕ) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ))
      ((deriv (Decomp1532b2.poissonKernel k) (r * Real.log t) * (r / t) : ℝ) : ℂ) t := by
  have hk : DifferentiableAt ℝ (Decomp1532b2.poissonKernel k) (r * Real.log t) :=
    ((pW_contDiff_poissonKernel k).differentiable (by norm_num)).differentiableAt
  convert (hk.hasDerivAt.comp t ((Real.hasDerivAt_log ht.ne').const_mul r)).ofReal_comp using 1 <;> congr 1

/-- Gallagher p.335 the logarithmic smoothing derivative is bounded by r over t. -/
private theorem pW_norm_deriv_poisson_log_le (k : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : 1 ≤ t) :
    ‖deriv (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ)) t‖ ≤ r / t := by
  have ht0 : 0 < t := by linarith
  rw [(pW_poisson_log_hasDerivAt k r ht0).deriv, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (div_nonneg hr ht0.le)]
  simpa using mul_le_mul_of_nonneg_right
    (abs_deriv_poissonKernel_le_one k (mul_nonneg hr (Real.log_nonneg ht)))
    (div_nonneg hr ht0.le)

/-- Gallagher p.335 integrability of the smoothing derivative on a positive interval. -/
private theorem pW_integrableOn_deriv_poisson_log (k : ℕ) (r : ℝ) {x y : ℝ} (hx : 0 < x) :
    IntegrableOn (deriv (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ)))
      (Set.Icc x y) := by
  have hl : ContDiffOn ℝ 2 Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono (by intro t ht; simpa using ht.ne')
  have hp : ContDiffOn ℝ 2 (fun u : ℝ => Decomp1532b2.poissonKernel k (r * Real.log u)) (Set.Ioi 0) :=
    (pW_contDiff_poissonKernel k).comp_contDiffOn (contDiffOn_const.mul hl)
  have hc : ContDiffOn ℝ 2 (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ)) (Set.Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  exact ((hc.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
    (by intro t ht; exact hx.trans_le ht.1)).integrableOn_Icc

/-- Gallagher p.335 the supported partial sum norm divided by height is integrable. -/
private theorem pW_integrableOn_partial_sum_norm_div (a : ℕ → ℂ) {x y : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t) (Set.Icc x y) := by
  have hi : IntegrableOn (fun t : ℝ => ((1 / t : ℝ) : ℂ)) (Set.Icc x y) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div continuousOn_id (by intro t ht; exact (hx.trans_le ht.1).ne'))).integrableOn_Icc
  have hh : IntegrableOn (fun t : ℝ => ‖((1 / t : ℝ) : ℂ) * ∑ n ∈ Icc 0 ⌊t⌋₊, a n‖)
      (Set.Icc x y) := (integrableOn_mul_sum_Icc (m := 0) a hx.le hi).norm
  apply hh.congr_fun _ measurableSet_Icc
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hx.trans_le ht.1))]
  ring

/-- Gallagher p.335 partial summation with its endpoint term retained.
This calculus statement has no zero or character hypothesis. -/
private theorem pW_poisson_partial_summation_bound (a : ℕ → ℂ) (k : ℕ) {r x y : ℝ}
    (hr : 0 ≤ r) (hx : 1 ≤ x) (hxy : x ≤ y)
    (ha : ∀ n ≤ ⌊x⌋₊, a n = 0) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * a n‖ -
        Decomp1532b2.poissonKernel k (r * Real.log y) * ‖∑ n ∈ Icc 0 ⌊y⌋₊, a n‖ ≤
      r * ∫ t in x..y, ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t := by
  have hx0 : 0 < x := by linarith
  have hh := detector_partial_summation_lower a
    (fun t : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log t) : ℂ)) hx0 hxy ha
    (fun t ht => (pW_poisson_log_hasDerivAt k r (hx0.trans_le ht.1)).differentiableAt)
    (pW_integrableOn_deriv_poisson_log k r hx0)
    (show ‖(Decomp1532b2.poissonKernel k (r * Real.log y) : ℂ)‖ ≤ Decomp1532b2.poissonKernel k (r * Real.log y) by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (poissonKernel_nonneg k (mul_nonneg hr (Real.log_nonneg (hx.trans hxy))))])
    (fun t ht => pW_norm_deriv_poisson_log_le k hr (hx.trans ht.1.le))
    ((pW_integrableOn_partial_sum_norm_div a hx0).mono_set Set.Ioc_subset_Icc_self)
    (le_refl _)
  rw [intervalIntegral.integral_of_le hxy]
  linarith


/-- Gallagher p.333 the supported coefficient sum is exactly the prime detector. -/
private theorem pW_sum_primeWindowCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x y v : ℝ) :
    (∑ n ∈ Icc 0 ⌊y⌋₊, (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n) = primeDetector χ x y v := by
  classical
  have hset : (Icc 0 ⌊y⌋₊).filter (fun n => ⌊x⌋₊ < n ∧ n.Prime)
      = (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime := by
    ext n
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨-, hu⟩, hl, hp⟩
      exact ⟨⟨hl, hu⟩, hp⟩
    · rintro ⟨⟨hl, hu⟩, hp⟩
      exact ⟨⟨Nat.zero_le _, hu⟩, hl, hp⟩
  rw [primeDetector]
  dsimp only
  rw [← Finset.sum_filter, hset]

/-- Gallagher p.335 the full von Mangoldt reciprocal mass has logarithmic size. -/
private theorem pW_mangoldt_reciprocal_sum_le_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    (∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤ Real.log x + C := by
  obtain ⟨C, hC, htail⟩ := prime_power_reciprocal_tail
  refine ⟨C + 7, by positivity, ?_⟩
  have hnat (N : ℕ) (hN : 1 ≤ N) :
      (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤ Real.log N + (C + 7) := by
    have hp : (∑ n ∈ (Icc 1 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) = LeanLab.PNTSieve.Mertens.C N := by
      simp only [sum_filter, LeanLab.PNTSieve.Mertens.C, LeanLab.PNTSieve.Mertens.c]
      apply sum_congr rfl
      intro n hn
      by_cases hnp : n.Prime <;> simp [hnp, ArithmeticFunction.vonMangoldt_apply_prime]
    have hn : (∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) =
        ∑ n ∈ (Ioc 1 N).filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      symm
      apply sum_subset
      · intro n hn
        obtain ⟨hn, hnp⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Ioc.mp hn).1.le, (mem_Ioc.mp hn).2⟩, hnp⟩
      · intro n hn hnot
        obtain ⟨hn, hnp⟩ := mem_filter.mp hn
        have hnlo : 1 ≤ n := (mem_Icc.mp hn).1
        have hn1 : n = 1 := by
          by_contra hne
          exact hnot (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩, hnp⟩)
        subst n
        simp
    have ht := htail 1 (N : ℝ) (by norm_num) (by exact_mod_cast hN)
    norm_num only [Nat.floor_one, Nat.floor_natCast, Real.sqrt_one, div_one] at ht
    rw [← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
      (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ)), hp, hn]
    linarith [LeanLab.PNTSieve.Mertens.C_le N hN]
  intro x hx
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff _).mpr hx
  have hlog : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) (Nat.floor_le (by linarith))
  exact (hnat ⌊x⌋₊ hN).trans (by linarith)

/-- Gallagher p.335 the finite small Poisson tail, with a von Mangoldt majorant. -/
private theorem pW_poisson_small_cutoff_norm : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, 0 < D →
    ∃ B₁ : ℝ, 0 < B₁ ∧ ∀ (a : ℕ → ℂ) (k : ℕ) (r x : ℝ),
      0 ≤ r → 1 ≤ x → r * Real.log x ≤ B₁ * k →
      (∀ n ∈ Icc 1 ⌊x⌋₊, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ)) →
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ ≤
        (1 / (2 * D)) ^ k * (Real.log x + C) := by
  obtain ⟨C, hC, hmass⟩ := pW_mangoldt_reciprocal_sum_le_log
  refine ⟨C, hC, ?_⟩
  intro D hD
  obtain ⟨B₁, hB₁, htail⟩ := poissonKernel_small_tail D hD
  refine ⟨B₁, hB₁, ?_⟩
  intro a k r x hr hx hscale ha
  calc
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊,
        ‖a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / (n : ℝ)) * (1 / (2 * D)) ^ k := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnx : (n : ℝ) ≤ x :=
        (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast (mem_Icc.mp hn).2).trans
          (Nat.floor_le (by linarith))
      have hu : 0 ≤ r * Real.log n := mul_nonneg hr (Real.log_natCast_nonneg n)
      have hscale' : r * Real.log n ≤ B₁ * k :=
        (mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hnx) hr).trans hscale
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonKernel_nonneg k hu)]
      exact mul_le_mul (ha n hn) (htail k _ hu hscale') (poissonKernel_nonneg k hu)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
    _ = (1 / (2 * D)) ^ k *
        ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmass x hx) (by positivity)

/-- Gallagher p.335 the positive real Dirichlet series majorant for the upper tail. -/
private theorem pW_mangoldt_rpow_series_bound : ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℝ, 0 < d → d < 1 →
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) ∧
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) ≤ 1 / d + A := by
  obtain ⟨A, hA, hbound⟩ := _root_.ShiftZeroBound
  refine ⟨A, hA, ?_⟩
  intro d hd hd1
  have hs : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith
  have hm := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have he (n : ℕ) :
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + d : ℝ) : ℂ) n).re =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d) := by
    by_cases hn : n = 0
    · subst n
      simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcp : (n : ℂ) ^ ((1 + d : ℝ) : ℂ) = (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    rw [LSeries.term_of_ne_zero hn, hcp, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) :=
    (Complex.reCLM.summable hm).congr he
  refine ⟨hsum, ?_⟩
  have ht : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) =
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + d : ℝ) : ℂ)).re := by
    rw [LSeries, Complex.re_tsum hm]
    exact tsum_congr (fun n => (he n).symm)
  rw [ht, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simpa only [Complex.ofReal_add, Complex.ofReal_one, neg_div, neg_re] using hbound d ⟨hd, hd1⟩

/-- Gallagher p.335 the infinite upper Poisson tail, with absolute convergence. -/
private theorem pW_poisson_large_cutoff_norm : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, 0 < D →
    ∃ B₂ : ℝ, 0 < B₂ ∧ ∀ (a : ℕ → ℂ) (k : ℕ) (r x : ℝ),
      0 < r → r ≤ 1 → 1 ≤ x → B₂ * k ≤ r * Real.log x →
      (∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ)) →
      Summable (fun n : ℕ => if x < (n : ℝ) then
        a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) else 0) ∧
      ‖∑' n : ℕ, if x < (n : ℝ) then
        a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) else 0‖ ≤
        (1 / (2 * D)) ^ k * ((C : ℝ) / r) := by
  obtain ⟨A, hA, hseries⟩ := pW_mangoldt_rpow_series_bound
  have hA0 : 0 ≤ A := by linarith
  refine ⟨A + 2, by positivity, ?_⟩
  intro D hD
  obtain ⟨B₂, hB₂, htail⟩ := poissonKernel_large_tail D hD
  refine ⟨B₂, hB₂, ?_⟩
  intro a k r x hr hr1 hx hscale ha
  obtain ⟨hsum, hmass⟩ := hseries (r / 2) (by positivity) (by linarith)
  have hmass' : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2)) ≤
      (A + 2) / r := by
    have he : 1 / (r / 2) = 2 / r := by ring
    rw [he] at hmass
    apply hmass.trans
    apply (le_div_iff₀ hr).mpr
    rw [add_mul, div_mul_cancel₀ _ hr.ne']
    nlinarith [mul_le_mul_of_nonneg_left hr1 hA0]
  let b : ℕ → ℝ := fun n => (1 / (2 * D)) ^ k *
    (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2))
  have hb : Summable b := hsum.mul_left _
  have hnorm (n : ℕ) : ‖if x < (n : ℝ) then
      a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) else 0‖ ≤ b n := by
    dsimp only [b]
    split_ifs with hnx
    · have hn0 : (0 : ℝ) < n := by linarith
      have hu : 0 ≤ r * Real.log n := mul_nonneg hr.le (Real.log_nonneg (by linarith))
      have hscale' : B₂ * k ≤ r * Real.log n :=
        hscale.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hnx.le) hr.le)
      have he : (ArithmeticFunction.vonMangoldt n / (n : ℝ)) * Real.exp (-(r * Real.log n) / 2) =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2) := by
        rw [Real.rpow_add hn0, Real.rpow_one, Real.rpow_def_of_pos hn0]
        rw [show -(r * Real.log n) / 2 = -(Real.log n * (r / 2)) by ring, Real.exp_neg]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonKernel_nonneg k hu)]
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
            ((1 / (2 * D)) ^ k * Real.exp (-(r * Real.log n) / 2)) :=
          mul_le_mul (ha n) (htail k _ hu hscale') (poissonKernel_nonneg k hu)
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
        _ = _ := by rw [mul_left_comm, he]
    · rw [norm_zero]
      positivity
  have hf := hb.of_norm_bounded hnorm
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, b n := (norm_tsum_le_tsum_norm hf.norm).trans (hf.norm.tsum_le_tsum hnorm hb)
    _ = (1 / (2 * D)) ^ k *
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass' (by positivity)

/-- Gallagher p.334 principal Euler factors add no zeros in the positive half plane. -/
private theorem pW_principal_zero_iff_zeta (q : ℕ) [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction s = 0 ↔ riemannZeta s = 0 := by
  change DirichletCharacter.LFunctionTrivChar q s = 0 ↔ _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1]
  have hprod : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    intro he
    have hpone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hpone, norm_one] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  simp only [mul_eq_zero, hprod, false_or]


set_option maxHeartbeats 4000000

/-- The `n`-th factor `χ n · n^{-I v}` has norm at most one, so the prime power removal applies. -/
private theorem pW_norm_chi_cpow_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (v : ℝ) (n : ℕ) :
    ‖χ n * (n : ℂ) ^ (-(I * v))‖ ≤ 1 := by
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  have hn : ‖(n : ℂ) ^ (-(I * v))‖ ≤ 1 := by
    rcases eq_or_ne n 0 with h | h
    · subst h
      by_cases hv : v = 0
      · subst hv; simp
      · have hz : (-(I * (v : ℂ))) ≠ 0 := by
          simp [Complex.ext_iff, hv]
        rw [Nat.cast_zero, Complex.zero_cpow hz]
        simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero h
      rw [Complex.norm_natCast_cpow_of_pos hpos]
      simp
  rw [norm_mul]
  exact mul_le_one₀ hχ (norm_nonneg _) hn

/-- `n ^ (-(1 + I v)) = n ^ (-(I v)) / n`, the bridge between the leaf's series term and the
coefficient shape of `poisson_weighted_prime_power_removal`. -/
private theorem pW_cpow_neg_one_add {n : ℕ} (hn : n ≠ 0) (v : ℝ) :
    (n : ℂ) ^ (-(1 + I * v)) = (n : ℂ) ^ (-(I * v)) / (n : ℂ) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 : (-(1 + I * v) : ℂ) = (-(I * v)) + (-1) := by
    push_cast
    ring
  rw [h1, Complex.cpow_add _ _ hnc, Complex.cpow_neg_one, div_eq_mul_inv]

/-- The leaf's series term, written with the coefficient `χ n · n^{-I v}` that the prime power
removal of `Decomp1532b2` consumes. -/
private theorem pW_seriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (v r : ℝ) (k : ℕ) {n : ℕ}
    (hn : n ≠ 0) :
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
        (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
      = (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [div_eq_mul_inv, ← Complex.cpow_neg, pW_cpow_neg_one_add hn v]
  push_cast
  field_simp

/-- The full Poisson series of the leaf is summable, given the tail bound. -/
private theorem pW_summable_series {q : ℕ} (χ : DirichletCharacter ℂ q) (v r : ℝ) (k : ℕ)
    {x' : ℝ} (hx' : 1 ≤ x')
    (htail : Summable (fun n : ℕ => if x' < (n : ℝ) then
      (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) else 0)) :
    Summable (fun n : ℕ => (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
      (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)) := by
  let F : ℕ → ℂ := fun n =>
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
      (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
  let G : ℕ → ℂ := fun n => if x' < (n : ℝ) then
      (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) else 0
  have htail' : Summable G := htail
  have hgs : Summable (fun n : ℕ => G (n + (⌊x'⌋₊ + 1))) :=
    (summable_nat_add_iff _).mpr htail'
  have hfs : Summable (fun n : ℕ => F (n + (⌊x'⌋₊ + 1))) := by
    refine hgs.congr (fun n => ?_)
    have hne : n + (⌊x'⌋₊ + 1) ≠ 0 := by omega
    have hlt : x' < ((n + (⌊x'⌋₊ + 1) : ℕ) : ℝ) := by
      have h1 : x' < (⌊x'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x'
      have h2 : (⌊x'⌋₊ : ℝ) + 1 ≤ ((n + (⌊x'⌋₊ + 1) : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    show G (n + (⌊x'⌋₊ + 1)) = F (n + (⌊x'⌋₊ + 1))
    dsimp only [G, F]
    rw [if_pos hlt, pW_seriesTerm_eq χ v r k hne]
  exact (summable_nat_add_iff _).mp hfs

/-- The three way split of the leaf's full series: below `⌊x⌋`, the window, and above `⌊y⌋`. -/
private theorem pW_tsum_three_split {q : ℕ} (χ : DirichletCharacter ℂ q) (v r : ℝ) (k : ℕ)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ∀ (F : ℕ → ℂ),
      (∀ n : ℕ, F n = (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
          (n : ℂ) ^ (1 + I * v)) *
          (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)) →
      Summable F →
      (∑' n : ℕ, F n)
        = (∑ n ∈ Icc 0 ⌊x⌋₊, F n) + (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, F n)
          + ∑' n : ℕ, (if ⌊y⌋₊ < n then F n else 0) := by
  have hfy : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  intro F hF hsum
  have hh : Summable (fun n : ℕ => if n ≤ ⌊y⌋₊ then F n else 0) :=
    summable_of_ne_finset_zero (s := Icc 0 ⌊y⌋₊) (fun b hb => by
      rw [if_neg]
      intro hle
      exact hb (mem_Icc.mpr ⟨Nat.zero_le b, hle⟩))
  have hfg : F = fun n => (if n ≤ ⌊y⌋₊ then F n else 0)
      + (if ⌊y⌋₊ < n then F n else 0) := by
    funext n
    by_cases h : n ≤ ⌊y⌋₊
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hg : Summable (fun n : ℕ => if ⌊y⌋₊ < n then F n else 0) := by
    refine (hsum.sub hh).congr (fun n => ?_)
    show F n - (if n ≤ ⌊y⌋₊ then F n else 0) = (if ⌊y⌋₊ < n then F n else 0)
    by_cases h : n ≤ ⌊y⌋₊
    · rw [if_pos h, if_neg (by omega), sub_self]
    · rw [if_neg h, if_pos (by omega), sub_zero]
  have htsum : (∑' n : ℕ, (if n ≤ ⌊y⌋₊ then F n else 0)) = ∑ n ∈ Icc 0 ⌊y⌋₊, F n := by
    rw [tsum_eq_sum (s := Icc 0 ⌊y⌋₊)]
    · apply sum_congr rfl
      intro b hb
      rw [if_pos (mem_Icc.mp hb).2]
    · intro b hb
      rw [if_neg]
      intro hle
      exact hb (mem_Icc.mpr ⟨Nat.zero_le b, hle⟩)
  have hset : Icc 0 ⌊y⌋₊ = Icc 0 ⌊x⌋₊ ∪ Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc, mem_union]
    omega
  have hdisj : Disjoint (Icc 0 ⌊x⌋₊) (Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_Icc] at ha
    simp only [mem_Ioc] at hb
    omega
  have hset' : (∑ n ∈ Icc 0 ⌊y⌋₊, F n)
      = (∑ n ∈ Icc 0 ⌊x⌋₊, F n) + (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, F n) := by
    rw [hset, sum_union hdisj]
  conv_lhs => rw [hfg]
  rw [Summable.tsum_add hh hg, htsum, hset']

/-- The prime detector has at most logarithmic mass. -/
private theorem pW_detector_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (x y v : ℝ), 1 ≤ x → x ≤ y →
      ‖primeDetector χ x y v‖ ≤ Real.log y + C := by
  obtain ⟨C, hC, hmass⟩ := pW_mangoldt_reciprocal_sum_le_log
  refine ⟨C, hC, fun q χ x y v hx hxy => ?_⟩
  have hx1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hsub : (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime ⊆ Icc 1 ⌊y⌋₊ := by
    intro n hn
    obtain ⟨hnw, hnp⟩ := mem_filter.mp hn
    exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hnw).1; omega, (mem_Ioc.mp hnw).2⟩
  unfold primeDetector
  calc ‖∑ p ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        (Real.log p / (p : ℝ) : ℂ) * χ p * Complex.exp (-((Real.log p * v : ℝ) : ℂ) * I)‖
      ≤ ∑ p ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ‖(Real.log p / (p : ℝ) : ℂ) * χ p * Complex.exp (-((Real.log p * v : ℝ) : ℂ) * I)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpp : Nat.Prime p := (mem_filter.mp hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hlog : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
        rw [norm_mul, norm_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hlog hp0.le), ArithmeticFunction.vonMangoldt_apply_prime hpp]
        have hre : (-((Real.log p * v : ℝ) : ℂ) * I).re = 0 := by
          rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        have hexp : ‖Complex.exp (-((Real.log p * v : ℝ) : ℂ) * I)‖ = 1 := by
          rw [Complex.norm_exp, hre, Real.exp_zero]
        rw [hexp, mul_one]
        calc Real.log ↑p / ↑p * ‖χ p‖ ≤ Real.log ↑p / ↑p * 1 := by
              exact mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ (p : ZMod q))
                (div_nonneg hlog hp0.le)
          _ = Real.log ↑p / ↑p := mul_one _
    _ ≤ ∑ n ∈ Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi1 hi2 => ?_)
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg i)
    _ ≤ Real.log y + C := hmass y (by linarith)

/-- The window sum of the prime window coefficient is the prime detector. -/
private theorem pW_sum_windowCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (x y v : ℝ) :
    (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n) = primeDetector χ x y v := by
  classical
  unfold primeDetector
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  have hlt : ⌊x⌋₊ < n := (mem_Ioc.mp hn).1
  by_cases hnp : n.Prime
  · simp [hlt, hnp]
  · simp [hnp]

/-- Absorption: for `k ≥ t / B₁` the kernel decay `(1/2)^k` beats any linear growth `t + S`,
uniformly for `t` past an explicit threshold. No smallness of `B₁` is needed. -/
private theorem pW_absorption {η B1 S : ℝ} (hη : 0 < η) (hB1 : 0 < B1) (hS : 0 ≤ S) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, A ≤ t → ∀ k : ℕ, t ≤ B1 * k →
      (1 / 2 : ℝ) ^ k * (t + S) ≤ η / 8 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2h : (1 / 2 : ℝ) ≤ Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  refine ⟨16 + 16 * S + 4 * Real.sqrt S + 128 * B1 ^ 2 + 8 * B1 * Real.sqrt S +
      max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) + 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  intro t ht k hk
  have hA1 : 8 ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAS : 16 * S ≤ t := by
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAsqrt : 4 * Real.sqrt S ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAB1 : 128 * B1 ^ 2 ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAB1S : 8 * B1 * Real.sqrt S ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAlog : 2 * Real.log (8 / η) * B1 / Real.log 2 ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : 2 * Real.log (8 / η) * B1 / Real.log 2 ≤
        max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_right _ _
    linarith
  have hpow : (1 / 2 : ℝ) ^ k = Real.exp (-((k : ℝ) * Real.log 2)) := by
    have h1 : (1 / 2 : ℝ) = Real.exp (Real.log (1 / 2)) := (Real.exp_log (by norm_num)).symm
    rw [h1, ← Real.exp_nat_mul]
    congr 1
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    push_cast
    ring
  have hkB : t / B1 ≤ (k : ℝ) := by
    rw [div_le_iff₀ hB1]
    simpa [mul_comm] using hk
  have hexp : Real.exp (-((k : ℝ) * Real.log 2)) ≤ Real.exp (-(t / B1 * Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [hpow]
  refine le_trans (mul_le_mul_of_nonneg_right hexp (by linarith : (0:ℝ) ≤ t + S)) ?_
  have hsplit : Real.exp (-(t / B1 * Real.log 2)) * (t + S)
      = Real.exp (-(t / B1 * Real.log 2) / 2)
        * (Real.exp (-(t / B1 * Real.log 2) / 2) * (t + S)) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hsplit]
  have hc1 : Real.exp (-(t / B1 * Real.log 2) / 2) ≤ η / 8 := by
    rw [show η / 8 = Real.exp (Real.log (η / 8)) from (Real.exp_log (by positivity)).symm]
    apply Real.exp_le_exp.mpr
    have hb : Real.log (η / 8) = -Real.log (8 / η) := by
      rw [Real.log_div hη.ne' (by norm_num), Real.log_div (by norm_num) hη.ne']
      ring
    rw [hb]
    have hstep : t * (Real.log 2 / B1) ≥ 2 * Real.log (8 / η) := by
      have hpos : 0 < Real.log 2 / B1 := by positivity
      have heq : 2 * Real.log (8 / η) * B1 / Real.log 2 * (Real.log 2 / B1) =
          2 * Real.log (8 / η) := by
        field_simp
      calc 2 * Real.log (8 / η)
          = (2 * Real.log (8 / η) * B1 / Real.log 2) * (Real.log 2 / B1) := heq.symm
        _ ≤ t * (Real.log 2 / B1) := mul_le_mul_of_nonneg_right hAlog hpos.le
    have hrew : -(t / B1 * Real.log 2) / 2 = -(t * (Real.log 2 / B1)) / 2 := by
      field_simp
    rw [hrew]
    linarith
  have hc2 : Real.exp (-(t / B1 * Real.log 2) / 2) * (t + S) ≤ 1 := by
    have hcpos : 0 < Real.log 2 / B1 := by positivity
    have hquad : (t / B1 * Real.log 2 / 2) ^ 2 / 2 ≤ Real.exp (t / B1 * Real.log 2 / 2) := by
      have h := Real.pow_div_factorial_le_exp (t / B1 * Real.log 2 / 2) (by positivity) 2
      simpa using h
    have hbig : t + S ≤ (t / B1 * Real.log 2 / 2) ^ 2 / 2 := by
      -- `t ≤ c²t²/8` and `2S ≤ c²t²/8`, with `c = log2 / B1`
      have hconv : (t / B1 * Real.log 2 / 2) ^ 2 / 2 = (t * (Real.log 2 / B1)) ^ 2 / 8 := by
        field_simp
        ring
      rw [hconv]
      have hB1sq : B1 ^ 2 * (Real.log 2 / B1) ^ 2 = (Real.log 2) ^ 2 := by
        field_simp
      have hcoef : (0:ℝ) ≤ (Real.log 2 / B1) ^ 2 := by positivity
      have hct : 16 ≤ t * (Real.log 2 / B1) ^ 2 := by
        have h4 := mul_le_mul_of_nonneg_right hAB1 hcoef
        rw [mul_assoc, hB1sq] at h4
        have h5 : 4 * (Real.log 2) ^ 2 ≥ 1 := by nlinarith [hlog2h]
        nlinarith
      have hcS : 16 * S ≤ t ^ 2 * (Real.log 2 / B1) ^ 2 := by
        have h5 : 4 * Real.sqrt S ≤ t * (Real.log 2 / B1) := by
          have h9 : (0:ℝ) < Real.log 2 / B1 := hcpos
          have h11 : 8 * B1 * Real.sqrt S * (Real.log 2 / B1) ≤ t * (Real.log 2 / B1) :=
            mul_le_mul_of_nonneg_right hAB1S h9.le
          have h12 : 8 * B1 * Real.sqrt S * (Real.log 2 / B1) =
              8 * Real.sqrt S * Real.log 2 := by
            field_simp
          have h13 : 4 * Real.sqrt S ≤ 8 * Real.sqrt S * Real.log 2 := by
            have h14 : (0:ℝ) ≤ Real.sqrt S := Real.sqrt_nonneg S
            nlinarith [hlog2h]
          linarith
        have h9 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
        have h11 : (4 * Real.sqrt S) ^ 2 ≤ (t * (Real.log 2 / B1)) ^ 2 :=
          pow_le_pow_left₀ h9 h5 2
        have h12 : (4 * Real.sqrt S) ^ 2 = 16 * S := by
          rw [mul_pow, Real.sq_sqrt hS]; norm_num
        rw [h12, mul_pow] at h11
        exact h11
      have htpos : (0:ℝ) < t := by linarith
      have hsq : t ^ 2 * (Real.log 2 / B1) ^ 2 = t * (t * (Real.log 2 / B1) ^ 2) := by ring
      have hgt : 8 * t ≤ t ^ 2 * (Real.log 2 / B1) ^ 2 := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_left hct htpos.le
        linarith
      rw [mul_pow]
      nlinarith [hgt, hcS]
    have hexp3 : Real.exp (-(t / B1 * Real.log 2) / 2)
        = (Real.exp (t / B1 * Real.log 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hexp3, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    exact hbig.trans hquad
  exact le_trans (mul_le_mul hc1 hc2 (by positivity) (by positivity)) (by norm_num)

/-- The floor threshold and the real threshold agree at natural numbers. -/
private theorem pW_floor_lt_iff {y : ℝ} {n : ℕ} (hy : 0 ≤ y) : y < (n : ℝ) ↔ ⌊y⌋₊ < n := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : (n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hcon
    have h3 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    linarith
  · intro h
    have h1 : (⌊y⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h
    have h2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    linarith



/-! ## Numeric lemmas for the assembly

Each of these has a small goal on purpose: the previous pass died of elaboration cost when the
whole assembly's numeric goal was attacked at once. `set_option maxHeartbeats` is inherited from
the head of this file. -/

/-- The kernel decay `(1/2)^k` against `D ^ k` with a `1 / r` in the tail term. -/
private theorem pW_kernel_engine1 {D η r Z : ℝ} (hD : 0 < D) (hr : 0 < r) (hη : 0 < η) (k : ℕ)
    (h : (1 / 2 : ℝ) ^ k * Z ≤ η / 8) :
    (1 / (2 * D)) ^ k * (Z / r) ≤ η / (8 * (D ^ k * r)) := by
  have hb : (1:ℝ) / (2 * D) = (1 / 2) * (1 / D) := by field_simp
  have hZ : (0:ℝ) ≤ (1 / D) ^ k := by positivity
  have h1 : (1 / 2) ^ k * Z * r⁻¹ * (1 / D) ^ k ≤ η / 8 * r⁻¹ * (1 / D) ^ k := by
    apply mul_le_mul_of_nonneg_right _ hZ
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hgoal : (1 / (2 * D)) ^ k * (Z / r) = (1 / 2) ^ k * Z * r⁻¹ * (1 / D) ^ k := by
    rw [hb, mul_pow, div_eq_mul_inv]
    ring
  have h2 : η / 8 * r⁻¹ * (1 / D) ^ k = η / (8 * (D ^ k * r)) := by
    rw [one_div, inv_pow]
    field_simp
  rw [hgoal]
  exact h1.trans h2.le

/-- The kernel decay against `D ^ k` with no `1 / r` factor. -/
private theorem pW_kernel_engine2 {D η r Z : ℝ} (hD : 0 < D) (hr : 0 < r) (hr2 : r ≤ 2) (hη : 0 < η)
    (k : ℕ) (h : (1 / 2 : ℝ) ^ k * Z ≤ η / 16) :
    (1 / (2 * D)) ^ k * Z ≤ η / (8 * (D ^ k * r)) := by
  have hb : (1:ℝ) / (2 * D) = (1 / 2) * (1 / D) := by field_simp
  have hZ : (0:ℝ) ≤ (1 / D) ^ k := by positivity
  have h1 : (1 / 2) ^ k * Z * (1 / D) ^ k ≤ η / 16 * (1 / D) ^ k :=
    mul_le_mul_of_nonneg_right h hZ
  have hgoal : (1 / (2 * D)) ^ k * Z = (1 / 2) ^ k * Z * (1 / D) ^ k := by
    rw [hb, mul_pow]; ring
  have h2 : η / 16 * (1 / D) ^ k ≤ η / (8 * (D ^ k * r)) := by
    have h3 : η / 16 ≤ η / (8 * r) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have h4 : η / 16 * (1 / D) ^ k ≤ η / (8 * r) * (1 / D) ^ k :=
      mul_le_mul_of_nonneg_right h3 hZ
    have h5 : η / (8 * r) * (1 / D) ^ k = η / (8 * (D ^ k * r)) := by
      rw [one_div, inv_pow]
      field_simp
    linarith
  rw [hgoal]
  exact h1.trans h2

/-- The kernel decay against `D ^ k` in the `1 / r` shape needed by the small part. -/
private theorem pW_kernel_engine3 {D η r Z : ℝ} (hD : 0 < D) (hr : 0 < r) (hη : 0 < η) (k : ℕ)
    (h : (1 / 2 : ℝ) ^ k * Z ≤ η / (8 * r)) :
    (1 / (2 * D)) ^ k * Z ≤ η / (8 * (D ^ k * r)) := by
  have hb : (1:ℝ) / (2 * D) = (1 / 2) * (1 / D) := by field_simp
  have hZ : (0:ℝ) ≤ (1 / D) ^ k := by positivity
  have h1 : (1 / 2) ^ k * Z * (1 / D) ^ k ≤ η / (8 * r) * (1 / D) ^ k :=
    mul_le_mul_of_nonneg_right h hZ
  have hgoal : (1 / (2 * D)) ^ k * Z = (1 / 2) ^ k * Z * (1 / D) ^ k := by
    rw [hb, mul_pow]; ring
  have h2 : η / (8 * r) * (1 / D) ^ k = η / (8 * (D ^ k * r)) := by
    rw [one_div, inv_pow]
    field_simp
  rw [hgoal]
  exact h1.trans h2.le

/-- `D ^ k` against an exponential once `k log D` is bounded. -/
private theorem pW_pow_le_exp_of_log {D : ℝ} (hD : 0 < D) (k : ℕ) {X : ℝ}
    (h : (k : ℝ) * Real.log D ≤ X) : D ^ k ≤ Real.exp X := by
  have h1 : D ^ k = Real.exp ((k : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hD]
  rw [h1]
  exact Real.exp_le_exp.mpr h

/-- `t ^ 2` against the exponential once `t` is past `8` and the rate is at least one. -/
private theorem pW_sq_le_exp {Cc t : ℝ} (hCc : 1 ≤ Cc) (ht : 8 ≤ t) :
    t ^ 2 ≤ 32 * Real.exp (Cc * t / 2) := by
  have h1 : (0:ℝ) ≤ Cc * t / 2 := by nlinarith
  have h2 := Real.pow_div_factorial_le_exp (Cc * t / 2) h1 2
  have h3 : (0:ℝ) ≤ t := by linarith
  have h4 : t / 2 ≤ Cc * t / 2 := by nlinarith
  have h5 : (t / 2) ^ 2 / 2 ≤ (Cc * t / 2) ^ 2 / 2 := by
    have h6 : (0:ℝ) ≤ t / 2 := by linarith
    nlinarith
  have h7 : t ^ 2 ≤ 32 * ((t / 2) ^ 2 / 2) := by nlinarith
  have h8 : 32 * ((t / 2) ^ 2 / 2) ≤ 32 * ((Cc * t / 2) ^ 2 / 2) := by linarith
  linarith [h2, h7, h8]

/-- `k log D ≤ Cc t / 2`: the index bound `k ≤ 2 t (Mx + 1)` against `Cc`. -/
private theorem pW_k_logD_le {k t Ld Mx Cc logD : ℝ} (h : k ≤ 2 * t * (Mx + 1)) (ht : 1 ≤ t)
    (hlogD : logD ≤ Ld) (hlogD0 : 0 ≤ logD) (hLd0 : 0 ≤ Ld) (hMx1 : 1 ≤ Mx)
    (hCc : Cc = 8 * Ld * (Mx + 1) + 1) : k * logD ≤ Cc * t / 2 := by
  have h1 : k * logD ≤ (2 * t * (Mx + 1)) * Ld := by
    have h2 : (0:ℝ) ≤ logD := hlogD0
    have h3 : (0:ℝ) ≤ 2 * t * (Mx + 1) := by nlinarith
    nlinarith
  have h4 : Cc * t / 2 = (4 * Ld * (Mx + 1) + 1 / 2) * t := by
    rw [hCc]; ring
  have h5 : (0:ℝ) ≤ t := by linarith
  have h6 : (0:ℝ) ≤ Ld * (Mx + 1) := by positivity
  rw [h4]
  nlinarith

/-- `Lb * k ≤ Bc * t`: the large cutoff scale against `Bc`. -/
private theorem pW_lb_k_le {k t Lb Mx Bc : ℝ} (h : k ≤ 2 * t * (Mx + 1)) (ht : 1 ≤ t) (hLb0 : 0 ≤ Lb)
    (hMx1 : 1 ≤ Mx) (hBc : Bc = 16 + 32 * Lb * (Mx + 1)) : Lb * k ≤ Bc * t := by
  have h1 : (0:ℝ) ≤ t := by linarith
  have h2 : (0:ℝ) ≤ Lb * (Mx + 1) := by positivity
  rw [hBc]
  nlinarith

/-- The scaled final comparison: `e ^ (-(Cc t)) t ^ 2 D ^ k ≤ 32`. -/
private theorem pW_final_scaled {Cc t Dk : ℝ} (hDk : Dk ≤ Real.exp (Cc * t / 2))
    (ht2 : t ^ 2 ≤ 32 * Real.exp (Cc * t / 2)) :
    Real.exp (-(Cc * t)) * t ^ 2 * Dk ≤ 32 := by
  have h5 : (0:ℝ) ≤ Real.exp (-(Cc * t)) * t ^ 2 := by positivity
  have h4 : Real.exp (-(Cc * t)) * t ^ 2 * Dk ≤ Real.exp (-(Cc * t)) * t ^ 2 *
      Real.exp (Cc * t / 2) := mul_le_mul_of_nonneg_left hDk h5
  refine h4.trans ?_
  have heq : Real.exp (-(Cc * t)) * t ^ 2 * Real.exp (Cc * t / 2)
      = (Real.exp (-(Cc * t)) * Real.exp (Cc * t / 2)) * t ^ 2 := by ring
  rw [heq]
  have h2 : Real.exp (-(Cc * t)) * Real.exp (Cc * t / 2) = Real.exp (-(Cc * t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  have h7 : (0:ℝ) ≤ Real.exp (-(Cc * t / 2)) := (Real.exp_pos _).le
  have h8 := mul_le_mul_of_nonneg_left ht2 h7
  have h9 : Real.exp (-(Cc * t / 2)) * (32 * Real.exp (Cc * t / 2)) = 32 := by
    have h10 : Real.exp (-(Cc * t / 2)) * Real.exp (Cc * t / 2) = 1 := by
      rw [← Real.exp_add]
      have h11 : -(Cc * t / 2) + Cc * t / 2 = 0 := by ring
      rw [h11, Real.exp_zero]
    calc Real.exp (-(Cc * t / 2)) * (32 * Real.exp (Cc * t / 2))
        = 32 * (Real.exp (-(Cc * t / 2)) * Real.exp (Cc * t / 2)) := by ring
      _ = 32 := by rw [h10]; ring
  linarith [h8, h9]

/-- The division step: the scaled comparison gives the leaf's target term. -/
private theorem pW_final_div {η Cc t Dk r c Lg xs : ℝ} (hη : 0 < η) (hr : 0 < r) (hcc : c = η / 64)
    (ht : t = r * Lg) (hxs : xs = Real.exp (-(Cc * t))) (hDk : 0 < Dk)
    (hscaled : Real.exp (-(Cc * t)) * t ^ 2 * Dk ≤ 32) :
    c * xs * Lg ^ 2 * r ≤ η / (2 * (Dk * r)) := by
  have h2 : Real.exp (-(Cc * t)) * t ^ 2 ≤ 32 / Dk := by
    rw [le_div_iff₀ hDk]
    linarith
  have h1 : η / 64 * Real.exp (-(Cc * t)) * Lg ^ 2 * r
      = η / 64 * (Real.exp (-(Cc * t)) * t ^ 2) / r := by
    rw [ht]
    field_simp
  rw [hcc, hxs, h1]
  have h4 : η / 64 * (Real.exp (-(Cc * t)) * t ^ 2) / r ≤ η / 64 * (32 / Dk) / r := by
    apply div_le_div_of_nonneg_right _ hr.le
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h4.trans ?_
  field_simp
  norm_num

/-- The leaf's series term at a prime above the window threshold is the window coefficient. -/
private theorem pW_seriesTerm_eq_coefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (x v r : ℝ) (k : ℕ)
    {n : ℕ} (hn : n.Prime) (hk : ⌊x⌋₊ < n) :
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
        (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
      = (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn.pos
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (le_of_lt hn0)]
  have hpow : (n : ℂ) ^ (1 + I * v) =
      (n : ℂ) * Complex.exp (((Real.log n * v : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_add _ _ hnc, Complex.cpow_one, Complex.cpow_def_of_ne_zero hnc, hlog]
    congr 2
    push_cast
    ring
  have hinv : (Complex.exp (((Real.log n * v : ℝ) : ℂ) * I))⁻¹ =
      Complex.exp (-(((Real.log n * v : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_neg]
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℂ) = (Real.log n : ℂ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
  rw [hpow, hΛ, div_eq_mul_inv, mul_inv, hinv]
  dsimp only
  rw [if_pos ⟨hk, hn⟩]
  push_cast
  field_simp

/-- A norm lower bound for a difference. -/
private theorem pW_norm_sub_ge (a b : ℂ) : ‖a‖ - ‖b‖ ≤ ‖a - b‖ :=
  (le_abs_self (‖a‖ - ‖b‖)).trans (abs_norm_sub_norm_le a b)



/-- Lower bound for the fourth of four pieces from an additive decomposition. -/
private theorem pW_norm_three_lower (a b c d : ℂ) (h : a = b + c + d) : ‖a‖ - ‖b‖ - ‖c‖ ≤ ‖d‖ := by
  have h1 : d = a - b - c := by rw [h]; abel
  have h2 : ‖a - b - c‖ ≥ ‖a - b‖ - ‖c‖ := pW_norm_sub_ge _ _
  have h3 : ‖a - b‖ ≥ ‖a‖ - ‖b‖ := pW_norm_sub_ge _ _
  rw [h1]
  linarith

/-- The closing arithmetic of the leaf: nine comparisons give the target term. -/
private theorem pW_chain_arith {η Dk r X Lx C1 C2 C0 Bc C3 sq Sn An Pn Wn Wc Ep : ℝ}
    (hr : 0 < r) (hDk : 0 < Dk) (hsq : 0 < sq)
    (h1 : η / (Dk * r) ≤ Sn) (h2 : Sn - An - Pn ≤ Wn) (h3 : Wn - C3 / sq ≤ Wc)
    (h4 : An ≤ X * (Lx + C1)) (h5 : Pn ≤ X * (C2 / r)) (h6 : Ep ≤ X * (Bc * Lx + C0))
    (h7 : X * (Lx + C1) ≤ η / (8 * (Dk * r)))
    (h8 : X * (C2 / r) ≤ η / (8 * (Dk * r)))
    (h9 : X * (Bc * Lx + C0) ≤ η / (8 * (Dk * r)))
    (h10 : C3 / sq ≤ η / (8 * (Dk * r))) :
    η / (2 * (Dk * r)) ≤ Wc - Ep := by
  have hbr : η / (8 * (Dk * r)) = η / (Dk * r) / 8 := by
    field_simp
  rw [hbr] at h7 h8 h9 h10
  have h11 : η / (2 * (Dk * r)) = η / (Dk * r) / 2 := by
    field_simp
  rw [h11]
  linarith

/-- The small part: shifting the sum from `Icc 1` to `Icc 0` costs nothing when `A 0 = 0`. -/
private theorem pW_small_part_le {D x C1 : ℝ} {k : ℕ} (A : ℕ → ℂ) (K : ℕ → ℂ) (hA0 : A 0 = 0)
    (h : ‖∑ n ∈ Icc 1 ⌊x⌋₊, A n * K n‖ ≤ (1 / (2 * D)) ^ k * (Real.log x + C1)) :
    ‖∑ n ∈ Icc 0 ⌊x⌋₊, A n * K n‖ ≤ (1 / (2 * D)) ^ k * (Real.log x + C1) := by
  have hset : Icc 0 ⌊x⌋₊ = insert 0 (Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [mem_Icc, mem_insert]
    omega
  rw [hset, sum_insert (by simp), hA0, zero_mul, zero_add]
  exact h

/-- The tail part: the floor and real thresholds agree, so the tail bound transfers. -/
private theorem pW_tail_part_le {D x C2 Bc r0 : ℝ} {k : ℕ} (A : ℕ → ℂ) (K : ℕ → ℂ)
    (hx : 0 ≤ x ^ Bc)
    (h : ‖∑' n : ℕ, (if x ^ Bc < (n : ℝ) then A n * K n else 0)‖ ≤
      (1 / (2 * D)) ^ k * (C2 / r0)) :
    ‖∑' n : ℕ, (if ⌊x ^ Bc⌋₊ < n then A n * K n else 0)‖ ≤
      (1 / (2 * D)) ^ k * (C2 / r0) := by
  have hiff : ∀ n : ℕ, (x ^ Bc < (n : ℝ)) ↔ (⌊x ^ Bc⌋₊ < n) := fun n => pW_floor_lt_iff hx
  have hcongr : (∑' n : ℕ, (if ⌊x ^ Bc⌋₊ < n then A n * K n else 0))
      = ∑' n : ℕ, (if x ^ Bc < (n : ℝ) then A n * K n else 0) := by
    apply tsum_congr
    intro n
    by_cases hh : ⌊x ^ Bc⌋₊ < n
    · simp only [if_pos hh, if_pos ((hiff n).mpr hh)]
    · simp only [if_neg hh, if_neg (fun h2 => hh ((hiff n).mp h2))]
  rw [hcongr]
  exact h

/-- The von Mangoldt coefficient of the leaf's series is majorised by `Λ n / n`. -/
private theorem pW_norm_series_coef {q : ℕ} (χ : DirichletCharacter ℂ q) (v : ℝ) (n : ℕ) :
    ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)‖ ≤
      ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  rcases eq_or_ne n 0 with hh | hh
  · subst hh
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hh
    have hΛ : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnorm : ‖(n : ℂ) ^ (1 + I * v)‖ = (n : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hpos]; simp
    have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have hn0 : (0:ℝ) < n := by exact_mod_cast hpos
    have h1 : ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)‖
        = ‖χ n‖ * ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      rw [norm_div, norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
    rw [h1]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hΛ hχ) hn0.le

/-- The endpoint kernel is below the `k`-th kernel decay once its argument is past `Bk k`. -/
private theorem pW_kernel_endpoint_le {D Bk r y : ℝ} (hD : 0 < D) (hBk : 0 < Bk)
    (htail : ∀ k : ℕ, ∀ u : ℝ, 0 ≤ u → Bk * k ≤ u →
      Decomp1532b2.poissonKernel k u ≤ (1 / (2 * D)) ^ k * Real.exp (-u / 2))
    {k : ℕ} (hy : 0 ≤ r * Real.log y) (h : Bk * k ≤ r * Real.log y) :
    Decomp1532b2.poissonKernel k (r * Real.log y) ≤ (1 / (2 * D)) ^ k := by
  have h1 := htail k _ hy h
  have h2 : Real.exp (-(r * Real.log y) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (1 / (2 * D)) ^ k)
  linarith [h1, h3]

/-- The endpoint term, from the kernel decay and the detector mass. -/
private theorem pW_endpoint_bound {D Kd Ly C0 : ℝ} {k : ℕ} (hD : 0 < D) (hKd : 0 ≤ Kd)
    (hk : Decomp1532b2.poissonKernel k Ly ≤ (1 / (2 * D)) ^ k) (hd : Kd ≤ Ly + C0) :
    Decomp1532b2.poissonKernel k Ly * Kd ≤ (1 / (2 * D)) ^ k * (Ly + C0) :=
  mul_le_mul hk hd hKd (by positivity)

/-- The prime power step: the window sum is within `C3 / sqrt x` of the von Mangoldt sum. -/
private theorem pW_pp_bound {C3 sq : ℝ} (Ww Wc : ℂ) (hpp : ‖Ww - Wc‖ ≤ C3 / sq) :
    ‖Ww‖ - C3 / sq ≤ ‖Wc‖ := by
  have h := pW_norm_sub_ge Ww Wc
  linarith

/-- `8 C₃ r ≤ η` from the `r₁` bound. -/
private theorem pW_eight_C3_r_le {C3 r η : ℝ} (hC3 : 0 ≤ C3) (hr : 0 < r) (hr3 : r ≤ η / (8 * C3 + 1)) :
    8 * C3 * r ≤ η := by
  have h3C : (0:ℝ) < 8 * C3 + 1 := by linarith
  have h2 : r * (8 * C3 + 1) ≤ η := by
    have h := mul_le_mul_of_nonneg_right hr3 h3C.le
    have h4 : (η / (8 * C3 + 1)) * (8 * C3 + 1) = η := by field_simp
    linarith [h, h4]
  have h5 : 8 * C3 * r ≤ r * (8 * C3 + 1) := by
    have h7 : 8 * C3 * r = r * (8 * C3) := by ring
    rw [h7]
    exact mul_le_mul_of_nonneg_left (by linarith) hr.le
  linarith [h2, h5]

/-- `8 C₃ D^k r ≤ η √x` from `D^k ≤ √x` and `8 C₃ r ≤ η`. -/
private theorem pW_pp_scaled {C3 Dk r η s : ℝ} (hC3 : 0 ≤ C3) (hr : 0 ≤ r) (h8 : 8 * C3 * r ≤ η)
    (hDk : Dk ≤ s) (hs0 : 0 ≤ s) : 8 * C3 * Dk * r ≤ η * s := by
  have h1 : 8 * C3 * Dk ≤ 8 * C3 * s :=
    mul_le_mul_of_nonneg_left hDk (by linarith)
  have h2 : 8 * C3 * Dk * r ≤ 8 * C3 * s * r := mul_le_mul_of_nonneg_right h1 hr
  have h3 : 8 * C3 * s * r = (8 * C3 * r) * s := by ring
  have h4 : (8 * C3 * r) * s ≤ η * s := mul_le_mul_of_nonneg_right h8 hs0
  linarith [h2, h3, h4]

/-- The prime power term against the main term. -/
private theorem pW_pp_div {C3 Dk r η s : ℝ} (hs : 0 < s) (hDk : 0 < Dk) (hr : 0 < r)
    (h : 8 * C3 * Dk * r ≤ η * s) : C3 / s ≤ η / (8 * (Dk * r)) := by
  have h8D : (0:ℝ) < 8 * (Dk * r) := by
    have h1 : (0:ℝ) < Dk * r := mul_pos hDk hr
    linarith
  rw [div_le_div_iff₀ hs h8D]
  nlinarith [h]

/-- The prime power comparison of the assembly, in one step (this is where the closing `nlinarith`
used to time out). -/
private theorem pW_pp_comparison {C3 Dk r η s : ℝ} (hC3 : 0 ≤ C3) (hs : 0 < s) (hDk : 0 < Dk)
    (hr : 0 < r) (hr3 : r ≤ η / (8 * C3 + 1)) (hDkle : Dk ≤ s) :
    C3 / s ≤ η / (8 * (Dk * r)) := by
  refine pW_pp_div hs hDk hr ?_
  exact pW_pp_scaled hC3 hr.le (pW_eight_C3_r_le hC3 hr hr3) hDkle hs.le

/-- `k log D ≤ (log x)/4` from `Cc r ≤ 1/2`. -/
private theorem pW_k_logD_quarter {k D Cc r x : ℝ} (hCcrmul : Cc * r ≤ 1 / 2) (hlogx : 0 ≤ Real.log x)
    (hkD : k * Real.log D ≤ Cc * (r * Real.log x) / 2) : k * Real.log D ≤ Real.log x / 4 := by
  have h1 : Cc * (r * Real.log x) = (Cc * r) * Real.log x := by ring
  have h2 : (Cc * r) * Real.log x ≤ (1 / 2) * Real.log x :=
    mul_le_mul_of_nonneg_right hCcrmul hlogx
  linarith [hkD, h1, h2]

/-- `D ^ k ≤ √x` from `k log D ≤ (log x)/4`. -/
private theorem pW_Dk_le_sqrt {D x : ℝ} (hD : 0 < D) (hx : 1 ≤ x) {k : ℕ}
    (h : (k : ℝ) * Real.log D ≤ Real.log x / 4) : D ^ k ≤ Real.sqrt x := by
  have h1 : D ^ k ≤ Real.exp (Real.log x / 4) := pW_pow_le_exp_of_log hD k h
  have h2 : Real.exp (Real.log x / 4) ≤ Real.sqrt x := by
    have h3 : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : (0:ℝ) < x)]
      congr 1
      ring
    rw [h3]
    exact Real.exp_le_exp.mpr (by linarith [Real.log_nonneg hx])
  linarith

/-- The small-part comparison: the `r`-rescaling and the kernel engine in one step. -/
private theorem pW_comp_small {D η r Lx C1 : ℝ} (hD : 0 < D) (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 < η)
    {k : ℕ} (hL : 0 ≤ Lx) (hC1 : 0 ≤ C1) (h : (1 / 2 : ℝ) ^ k * (r * Lx + C1) ≤ η / 8) :
    (1 / (2 * D)) ^ k * (Lx + C1) ≤ η / (8 * (D ^ k * r)) := by
  apply pW_kernel_engine3 hD hr hη k
  have h5 : Lx * r ≤ Lx := by nlinarith
  have h3 : (Lx + C1) * r ≤ r * Lx + C1 := by nlinarith [h5, hC1]
  have h2 : (1 / 2 : ℝ) ^ k * (Lx + C1) * r ≤ (1 / 2 : ℝ) ^ k * (r * Lx + C1) := by
    have h6 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc (1 / 2 : ℝ) ^ k * (Lx + C1) * r = (1 / 2 : ℝ) ^ k * ((Lx + C1) * r) := by ring
      _ ≤ (1 / 2 : ℝ) ^ k * (r * Lx + C1) := mul_le_mul_of_nonneg_left h3 h6
  have h4 : (1 / 2 : ℝ) ^ k * (Lx + C1) * r ≤ η / 8 := h2.trans h
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * r)]
  linarith

/-- The tail comparison. -/
private theorem pW_comp_tail {D η r Lx C2 : ℝ} (hD : 0 < D) (hr : 0 < r) (hη : 0 < η) {k : ℕ}
    (hL : 0 ≤ Lx) (h : (1 / 2 : ℝ) ^ k * (r * Lx + C2) ≤ η / 8) :
    (1 / (2 * D)) ^ k * (C2 / r) ≤ η / (8 * (D ^ k * r)) := by
  apply pW_kernel_engine1 hD hr hη k
  have h4 : (0:ℝ) ≤ r * Lx := mul_nonneg hr.le hL
  have h3 : C2 ≤ r * Lx + C2 := by linarith
  exact (mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k)).trans h

/-- The endpoint comparison. -/
private theorem pW_comp_endpoint {D η r Lx C0 Bc : ℝ} (hD : 0 < D) (hr : 0 < r) (hr1 : r ≤ 1)
    (hη : 0 < η) {k : ℕ} (hL : 0 ≤ Lx) (hBc : 1 ≤ Bc) (hC0 : 0 ≤ C0)
    (h : (1 / 2 : ℝ) ^ k * (r * Lx + C0) ≤ η / (8 * Bc)) :
    (1 / (2 * D)) ^ k * (Bc * Lx + C0) ≤ η / (8 * (D ^ k * r)) := by
  apply pW_kernel_engine3 hD hr hη k
  have h5 : Bc * (r * Lx + C0) = Bc * (r * Lx) + Bc * C0 := by ring
  have h6 : (Bc * Lx + C0) * r ≤ Bc * (r * Lx + C0) := by
    have h7 : (Bc * Lx + C0) * r = Bc * (Lx * r) + C0 * r := by ring
    have h8 : Bc * (Lx * r) = Bc * (r * Lx) := by ring
    have h9 : C0 * r ≤ Bc * C0 := by
      have h10 : C0 * r ≤ C0 * Bc := mul_le_mul_of_nonneg_left (le_trans hr1 hBc) hC0
      linarith
    have h12 : Bc * (r * Lx) + Bc * C0 = Bc * (r * Lx + C0) := by ring
    linarith [h7, h8, h9, h12]
  have h4 : (1 / 2 : ℝ) ^ k * (Bc * Lx + C0) * r ≤
      Bc * ((1 / 2 : ℝ) ^ k * (r * Lx + C0)) := by
    have h10 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc (1 / 2 : ℝ) ^ k * (Bc * Lx + C0) * r
        = (1 / 2 : ℝ) ^ k * ((Bc * Lx + C0) * r) := by ring
      _ ≤ (1 / 2 : ℝ) ^ k * (Bc * (r * Lx + C0)) := mul_le_mul_of_nonneg_left h6 h10
      _ = Bc * ((1 / 2 : ℝ) ^ k * (r * Lx + C0)) := by ring
  have h11 : Bc * ((1 / 2 : ℝ) ^ k * (r * Lx + C0)) ≤ Bc * (η / (8 * Bc)) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h12 : Bc * (η / (8 * Bc)) = η / 8 := by field_simp
  have h13 : (1 / 2 : ℝ) ^ k * (Bc * Lx + C0) * r ≤ η / 8 := by
    linarith [h4, h11, h12]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * r)]
  linarith

private theorem pW_poisson_window_localization_proof :
    ∀ E D η : ℝ, 1 ≤ E → 1 ≤ D → 0 < η →
      ∃ r₁ A B C c : ℝ, 0 < r₁ ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
        ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
          |v| ≤ T → 1 / Real.log T ≤ r → r ≤ r₁ →
          (∀ M : ℕ, E * r * Real.log T ≤ M →
            ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
              η / (D ^ k * r) ≤
                ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                  (n : ℂ) ^ (1 + I * v)) *
                  (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖) →
          ∀ x : ℝ, T ^ A ≤ x → ∃ k : ℕ,
            c * x ^ (-C * r) * Real.log x ^ 2 * r ≤
              ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ B⌋₊,
                (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) *
                  (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n‖ -
                Decomp1532b2.poissonKernel k (r * Real.log (x ^ B)) *
                  ‖primeDetector χ x (x ^ B) v‖ := by
  intro E D η hE hD hη
  obtain ⟨C1, hC1, hsmall⟩ := pW_poisson_small_cutoff_norm
  obtain ⟨C2, hC2, hlarge⟩ := pW_poisson_large_cutoff_norm
  obtain ⟨C3, hC3, hpp⟩ := Decomp1532b2.poisson_weighted_prime_power_removal
  obtain ⟨C0, hC0, hdet⟩ := pW_detector_norm_le
  have hD0 : (0:ℝ) < D := by linarith
  obtain ⟨Bk, hBk, hBktail⟩ := poissonKernel_large_tail D hD0
  obtain ⟨Bs, hBs, hsmallB⟩ := hsmall D hD0
  obtain ⟨Bl, hBl, hlargeB⟩ := hlarge D hD0
  set Bcx : ℝ := 16 + 32 * (Bl + Bk) * (1 / Bs + E + 2 + 1) with hBcx
  set Ccx : ℝ := 8 * (max (Real.log D) 0) * (1 / Bs + E + 2 + 1) + 1 with hCcx
  have hBcaux : (0:ℝ) ≤ 32 * (Bl + Bk) * (1 / Bs + E + 2 + 1) := by positivity
  have hBcpos : (0:ℝ) ≤ Bcx := by rw [hBcx]; linarith
  have hBc1 : (1:ℝ) ≤ Bcx := by rw [hBcx]; linarith
  have hBc2 : (2:ℝ) ≤ Bcx := by linarith
  have hBcne : Bcx ≠ 0 := by linarith
  have hCcp : (0:ℝ) < Ccx := by rw [hCcx]; positivity
  have hCc1 : (1:ℝ) ≤ Ccx := by
    rw [hCcx]
    have h1 : (0:ℝ) ≤ 8 * (max (Real.log D) 0) * (1 / Bs + E + 2 + 1) := by positivity
    linarith
  obtain ⟨Aabs1, hAabs1b, hAabs1⟩ := pW_absorption (η := η) (B1 := Bs) (S := C1) hη hBs hC1
  obtain ⟨Aabs2, hAabs2b, hAabs2⟩ := pW_absorption (η := η) (B1 := Bs) (S := C2) hη hBs hC2
  obtain ⟨Aabs3, hAabs3b, hAabs3⟩ := pW_absorption (η := η / Bcx) (B1 := Bs) (S := C0)
    (by positivity) hBs hC0
  refine ⟨1 / (4 + 2 * Ccx + (8 * C3 + 1) / η),
    Aabs1 + Aabs2 + Aabs3 + 8 + 1, Bcx, Ccx, η / 64, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) < 4 + 2 * Ccx + (8 * C3 + 1) / η := by positivity
    positivity
  · linarith
  · linarith
  · linarith
  · positivity
  intro T hT q hq hqT χ v r hv hrlo hrhi hseries x hx
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlT).trans_le hrlo
  have hrq : 1 ≤ r * Real.log T := by
    have h3 := mul_le_mul_of_nonneg_right hrlo hlT.le
    have h4 : (1 / Real.log T) * Real.log T = 1 := by field_simp
    linarith
  have hK0 : (0:ℝ) < (8 * C3 + 1) / η := by
    have h1 : (0:ℝ) < 8 * C3 + 1 := by linarith
    positivity
  have hsum3 : (0:ℝ) < 4 + 2 * Ccx + (8 * C3 + 1) / η := by linarith
  have hr1 : r ≤ 1 := by
    have h2 : r ≤ 1 / (4 + 2 * Ccx + (8 * C3 + 1) / η) := hrhi
    have h3 : (1:ℝ) / (4 + 2 * Ccx + (8 * C3 + 1) / η) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hsum3 (by norm_num)]
      linarith [hK0.le, hCcp.le]
    linarith
  have hrCc : r ≤ 1 / (2 * Ccx) := by
    have h2 : r ≤ 1 / (4 + 2 * Ccx + (8 * C3 + 1) / η) := hrhi
    have h3 : (1:ℝ) / (4 + 2 * Ccx + (8 * C3 + 1) / η) ≤ 1 / (2 * Ccx) := by
      rw [div_le_div_iff₀ hsum3 (by linarith)]
      linarith [hK0.le]
    linarith
  have hrC3 : r ≤ η / (8 * C3 + 1) := by
    have h2 : r ≤ 1 / (4 + 2 * Ccx + (8 * C3 + 1) / η) := hrhi
    have h3 : (1:ℝ) / (4 + 2 * Ccx + (8 * C3 + 1) / η) ≤ η / (8 * C3 + 1) := by
      rw [div_le_div_iff₀ hsum3 (by linarith)]
      have h4 : (8 * C3 + 1) / η * η = 8 * C3 + 1 := by field_simp
      nlinarith [h4, hK0, hCcp, hη]
    linarith
  have hxT : 1 ≤ T := by linarith
  have hx1 : 1 ≤ x := by
    have h1 : (1:ℝ) ≤ T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1) := Real.one_le_rpow hxT (by linarith)
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogTle : Real.log T ≤ Real.log x := by
    have h1 : T ≤ x := by
      calc T = T ^ (1:ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1) :=
            Real.rpow_le_rpow_of_exponent_le hxT (by linarith)
        _ ≤ x := hx
    exact Real.log_le_log (by linarith) h1
  have ht1 : 1 ≤ r * Real.log x := hrq.trans (mul_le_mul_of_nonneg_left hlogTle hr.le)
  have hA_le_t : Aabs1 + Aabs2 + Aabs3 + 8 + 1 ≤ r * Real.log x := by
    have h1 : Real.log (T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1)) ≤ Real.log x :=
      Real.log_le_log (by positivity) hx
    have h2 : Real.log (T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1))
        = (Aabs1 + Aabs2 + Aabs3 + 8 + 1) * Real.log T :=
      Real.log_rpow (by linarith : (0:ℝ) < T) _
    rw [h2] at h1
    have h3 : r * ((Aabs1 + Aabs2 + Aabs3 + 8 + 1) * Real.log T) ≤ r * Real.log x :=
      mul_le_mul_of_nonneg_left h1 hr.le
    have h4 : (1:ℝ) ≤ r * Real.log T := hrq
    have h5 : (0:ℝ) ≤ r * Real.log T := le_trans (by norm_num) h4
    nlinarith [h3, h4, h5]
  have hA1t : Aabs1 ≤ r * Real.log x := by linarith [hAabs1b, hAabs2b, hAabs3b, hA_le_t]
  have hA2t : Aabs2 ≤ r * Real.log x := by linarith [hAabs1b, hAabs2b, hAabs3b, hA_le_t]
  have hA3t : Aabs3 ≤ r * Real.log x := by linarith [hAabs1b, hAabs2b, hAabs3b, hA_le_t]
  set M : ℕ := ⌈max (r * Real.log x / Bs) (E * r * Real.log T)⌉₊ with hM
  have hMcast : (M : ℝ) = (⌈max (r * Real.log x / Bs) (E * r * Real.log T)⌉₊ : ℝ) := by rw [hM]
  have hMceil : max (r * Real.log x / Bs) (E * r * Real.log T) ≤ (M : ℝ) := by
    have h := Nat.le_ceil (max (r * Real.log x / Bs) (E * r * Real.log T))
    linarith [hMcast]
  obtain ⟨k, hMk, hk2M, hser⟩ := hseries M ((le_max_right _ _).trans hMceil)
  have hkM : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hMk
  have hkup : (k : ℝ) ≤ 2 * max (r * Real.log x / Bs) (E * r * Real.log T) + 2 := by
    have h6 : (⌈max (r * Real.log x / Bs) (E * r * Real.log T)⌉₊ : ℝ) ≤
        max (r * Real.log x / Bs) (E * r * Real.log T) + 1 :=
      (Nat.ceil_lt_add_one (le_trans (by positivity) (le_max_left _ _))).le
    have h7 : ((k : ℕ) : ℝ) < 2 * ((M : ℕ) : ℝ) := by exact_mod_cast hk2M
    linarith [hMcast]
  have hmax : max (r * Real.log x / Bs) (E * r * Real.log T) ≤
      (r * Real.log x) * (1 / Bs + E + 2) := by
    apply max_le
    · have h4 : r * Real.log x / Bs = (r * Real.log x) * (1 / Bs) := by ring
      rw [h4]
      have h5 : (0:ℝ) ≤ r * Real.log x := by positivity
      have h6 : (0:ℝ) ≤ r * Real.log x * E := by positivity
      nlinarith [h5, h6]
    · have h6 : (0:ℝ) ≤ r * Real.log x * (1 / Bs) := by positivity
      have h7 : (0:ℝ) ≤ r * Real.log x := by positivity
      have h8 : r * Real.log T ≤ r * Real.log x := mul_le_mul_of_nonneg_left hlogTle hr.le
      nlinarith [h6, h8]
  have hkt : (k : ℝ) ≤ 2 * (r * Real.log x) * (1 / Bs + E + 2 + 1) := by
    have h1 : (0:ℝ) ≤ r * Real.log x := by positivity
    have h2 : (0:ℝ) ≤ r * Real.log x * (1 / Bs + E + 2) := by positivity
    nlinarith [hkup, hmax, h1, ht1]
  have hsm : r * Real.log x ≤ Bs * (k : ℝ) := by
    have h2 : r * Real.log x / Bs ≤ (k : ℝ) :=
      (le_trans (le_max_left _ _) hMceil).trans hkM
    rw [div_le_iff₀ hBs] at h2
    linarith
  have hMx1 : (1:ℝ) ≤ 1 / Bs + E + 2 := by
    have h1 : (0:ℝ) < 1 / Bs := by positivity
    linarith
  have hkD : (k : ℝ) * Real.log D ≤ Ccx * (r * Real.log x) / 2 :=
    pW_k_logD_le (k := (k : ℝ)) (t := r * Real.log x) (Ld := max (Real.log D) 0)
      (Mx := 1 / Bs + E + 2) (Cc := Ccx) (logD := Real.log D) hkt ht1
      (le_max_left (Real.log D) 0) (Real.log_nonneg hD) (le_max_right (Real.log D) 0) hMx1 hCcx.symm
  have hLb_k : (Bl + Bk) * (k : ℝ) ≤ Bcx * (r * Real.log x) :=
    pW_lb_k_le (k := (k : ℝ)) (t := r * Real.log x) (Lb := Bl + Bk) (Mx := 1 / Bs + E + 2)
      (Bc := Bcx) hkt ht1 (by linarith) hMx1 hBcx.symm
  have hy1 : 1 ≤ x ^ Bcx := Real.one_le_rpow hx1 (by linarith)
  have hxy : x ≤ x ^ Bcx := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hBc1
  have hlogy : Real.log (x ^ Bcx) = Bcx * Real.log x := Real.log_rpow (by linarith) Bcx
  have hlgB : (Bl + Bk) * (k : ℝ) ≤ r * Real.log (x ^ Bcx) := by
    have h6 : r * Real.log (x ^ Bcx) = r * Bcx * Real.log x := by rw [hlogy]; ring
    have h5 : r * Bcx * Real.log x = Bcx * (r * Real.log x) := by ring
    rw [h6, h5]
    exact hLb_k
  let Acoef : ℕ → ℂ := fun n =>
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)
  let Kk : ℕ → ℂ := fun n => (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
  have hAnorm : ∀ n : ℕ, ‖Acoef n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    fun n => pW_norm_series_coef χ v n
  have hAcoef0 : Acoef 0 = 0 := by
    dsimp only [Acoef]
    simp
  have hsmall' : ‖∑ n ∈ Icc 1 ⌊x⌋₊, Acoef n * Kk n‖ ≤
      (1 / (2 * D)) ^ k * (Real.log x + C1) :=
    hsmallB Acoef k r x hr.le hx1 hsm (fun n _ => hAnorm n)
  have hAb : ‖∑ n ∈ Icc 0 ⌊x⌋₊, Acoef n * Kk n‖ ≤
      (1 / (2 * D)) ^ k * (Real.log x + C1) :=
    pW_small_part_le Acoef Kk hAcoef0 hsmall'
  have hlg : Bl * (k : ℝ) ≤ r * Real.log (x ^ Bcx) := by
    have hk0 : (0:ℝ) ≤ (k : ℝ) := by positivity
    have h1 : Bl * (k : ℝ) ≤ (Bl + Bk) * (k : ℝ) := by nlinarith [hBl.le, hBk.le, hk0]
    linarith [hlgB, h1]
  obtain ⟨hsumtail, htailb⟩ := hlargeB Acoef k r (x ^ Bcx) hr hr1 hy1 hlg hAnorm
  have hPb : ‖∑' n : ℕ, (if ⌊x ^ Bcx⌋₊ < n then Acoef n * Kk n else 0)‖ ≤
      (1 / (2 * D)) ^ k * (C2 / r) :=
    pW_tail_part_le (Bc := Bcx) Acoef Kk (by positivity) htailb
  have htail'' : Summable (fun n : ℕ => if x ^ Bcx < (n : ℝ) then
      (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) else 0) := by
    refine hsumtail.congr (fun n => ?_)
    by_cases hh : x ^ Bcx < (n : ℝ)
    · rw [if_pos hh, if_pos hh]
      by_cases hn : n = 0
      · subst hn
        simp [Acoef, Kk, Complex.zero_cpow]
      · exact pW_seriesTerm_eq χ v r k hn
    · rw [if_neg hh, if_neg hh]
  have hsumF : Summable (fun n : ℕ => Acoef n * Kk n) :=
    pW_summable_series χ v r k hy1 htail''
  have hsplit := pW_tsum_three_split χ v r k hx1 hxy (fun n => Acoef n * Kk n)
    (fun n => rfl) hsumF
  have hWrel : ‖∑' n : ℕ, Acoef n * Kk n‖ - ‖∑ n ∈ Icc 0 ⌊x⌋₊, Acoef n * Kk n‖ -
      ‖∑' n : ℕ, (if ⌊x ^ Bcx⌋₊ < n then Acoef n * Kk n else 0)‖ ≤
      ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n‖ := by
    refine pW_norm_three_lower _ _ _ _ ?_
    rw [hsplit]
    abel
  let aa : ℕ → ℂ := fun n => χ n * (n : ℂ) ^ (-(I * v))
  let Wc : ℂ := ∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Kk n * (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n
  let Ep : ℝ := Decomp1532b2.poissonKernel k (r * Real.log (x ^ Bcx)) *
    ‖primeDetector χ x (x ^ Bcx) v‖
  have hppw := hpp x (x ^ Bcx) r hx1 hxy hr.le k aa (fun n => pW_norm_chi_cpow_le_one χ v n)
  have hS1 : (∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, aa n *
      (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
        Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ))
      = ∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have h2 := (mem_Ioc.mp hn).1
      omega
    exact (pW_seriesTerm_eq χ v r k hn0).symm
  have hS2 : (∑ n ∈ (Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊).filter Nat.Prime, aa n *
      (((Real.log n / (n : ℝ)) * Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ))
      = Wc := by
    show _ = ∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Kk n * (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n
    rw [sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnp : n.Prime
    · rw [if_pos hnp]
      have hlt : ⌊x⌋₊ < n := (mem_Ioc.mp hn).1
      have h1 := pW_seriesTerm_eq_coefficient χ x v r k hnp hlt
      have h2 := pW_seriesTerm_eq χ v r k hnp.ne_zero
      rw [ArithmeticFunction.vonMangoldt_apply_prime hnp] at h1 h2
      exact h2.symm.trans h1
    · rw [if_neg hnp]
      simp [hnp]
  have hPw : ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n‖ - C3 / Real.sqrt x ≤ ‖Wc‖ := by
    rw [← hS1, ← hS2]
    exact pW_pp_bound _ _ hppw
  have hBk_le : Bk * (k : ℝ) ≤ r * Real.log (x ^ Bcx) := by
    have hk0 : (0:ℝ) ≤ (k : ℝ) := by positivity
    have h1 : Bk * (k : ℝ) ≤ (Bl + Bk) * (k : ℝ) := by nlinarith [hBl.le, hBk.le, hk0]
    linarith [hlgB, h1]
  have hkend := pW_kernel_endpoint_le hD0 hBk hBktail (k := k) (r := r)
    (y := x ^ Bcx) (mul_nonneg hr.le (Real.log_nonneg hy1)) hBk_le
  have hdetb := hdet q χ x (x ^ Bcx) v hx1 hxy
  have hEp : Ep ≤ (1 / (2 * D)) ^ k * (Bcx * Real.log x + C0) := by
    show Decomp1532b2.poissonKernel k (r * Real.log (x ^ Bcx)) *
      ‖primeDetector χ x (x ^ Bcx) v‖ ≤ _
    have h2 : Decomp1532b2.poissonKernel k (r * Real.log (x ^ Bcx)) *
        ‖primeDetector χ x (x ^ Bcx) v‖ ≤
        (1 / (2 * D)) ^ k * (Real.log (x ^ Bcx) + C0) :=
      mul_le_mul hkend hdetb (norm_nonneg _) (by positivity)
    have h3 : Real.log (x ^ Bcx) + C0 ≤ Bcx * Real.log x + C0 := by rw [hlogy]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have hDkpos : (0:ℝ) < D ^ k := pow_pos hD0 k
  have hsqx : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h8r : (0:ℝ) < 8 * r := by linarith
  have hcomp1 := pW_comp_small (D := D) (η := η) (r := r) (Lx := Real.log x) (C1 := C1)
    hD0 hr hr1 hη (k := k) hlogx hC1 (hAabs1 (r * Real.log x) hA1t k hsm)
  have hcomp2 := pW_comp_tail (D := D) (η := η) (r := r) (Lx := Real.log x) (C2 := C2)
    hD0 hr hη (k := k) hlogx (hAabs2 (r * Real.log x) hA2t k hsm)
  have h3abs : (1 / 2 : ℝ) ^ k * (r * Real.log x + C0) ≤ η / (8 * Bcx) := by
    have h1 := hAabs3 (r * Real.log x) hA3t k hsm
    have h2 : η / Bcx / 8 = η / (8 * Bcx) := by field_simp
    rw [h2] at h1
    exact h1
  have hcomp3 := pW_comp_endpoint (D := D) (η := η) (r := r) (Lx := Real.log x) (C0 := C0)
    (Bc := Bcx) hD0 hr hr1 hη (k := k) hlogx hBc1 hC0 h3abs
  have hCcrmul : Ccx * r ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hrCc hCcp.le
    have h3 : (1 / (2 * Ccx)) * Ccx = 1 / 2 := by field_simp
    rw [mul_comm Ccx r]
    linarith [h2, h3]
  have hkD4 : (k : ℝ) * Real.log D ≤ Real.log x / 4 :=
    pW_k_logD_quarter hCcrmul hlogx hkD
  have hDk_le : D ^ k ≤ Real.sqrt x := pW_Dk_le_sqrt hD0 hx1 hkD4
  have hcomp4 := pW_pp_comparison (C3 := C3) (Dk := D ^ k) (r := r) (η := η)
    (s := Real.sqrt x) hC3 hsqx hDkpos hr hrC3 hDk_le
  have ht8 : (8:ℝ) ≤ r * Real.log x := by
    have h1 : (0:ℝ) ≤ Aabs1 := by linarith
    linarith [hA_le_t]
  have hDkexp : D ^ k ≤ Real.exp (Ccx * (r * Real.log x) / 2) :=
    pW_pow_le_exp_of_log hD0 k (by linarith [hkD])
  have hscaled : Real.exp (-(Ccx * (r * Real.log x))) * (r * Real.log x) ^ 2 * D ^ k ≤ 32 :=
    pW_final_scaled hDkexp (pW_sq_le_exp hCc1 ht8)
  have hxs : x ^ (-Ccx * r) = Real.exp (-(Ccx * (r * Real.log x))) := by
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < x)]
    congr 1
    ring
  have hfin : η / 64 * x ^ (-Ccx * r) * Real.log x ^ 2 * r ≤ η / (2 * (D ^ k * r)) :=
    pW_final_div hη hr rfl (by ring) hxs hDkpos hscaled
  exact ⟨k, hfin.trans (pW_chain_arith (Dk := D ^ k) (r := r) (X := (1 / (2 * D)) ^ k)
    (Lx := Real.log x) (C1 := C1) (C2 := C2) (C0 := C0) (Bc := Bcx) (C3 := C3)
    (sq := Real.sqrt x) (Sn := ‖∑' n : ℕ, Acoef n * Kk n‖)
    (An := ‖∑ n ∈ Icc 0 ⌊x⌋₊, Acoef n * Kk n‖)
    (Pn := ‖∑' n : ℕ, (if ⌊x ^ Bcx⌋₊ < n then Acoef n * Kk n else 0)‖)
    (Wn := ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n‖)
    (Wc := ‖Wc‖) (Ep := Ep) hr hDkpos hsqx hser hWrel hPw hAb hPb hEp
    hcomp1 hcomp2 hcomp3 hcomp4)⟩

/-- LEAF, REPAIRED (U-1619, omos_tick 20261105T0144Z; changes only this statement).
Gallagher 1970 p.335 display 23 and the endpoint estimate below it.
Localization of a supplied dyadic Poisson series lower bound to a finite prime sum.
The endpoint term is subtracted before partial summation. No zero is assumed here.
REPAIR: `r` is bounded by a constant `r₁` chosen together with `A, B, C, c`. The old form allowed
`r ≤ 1/4` for every `D`, but this p.335 route removes the prime square terms by taking `k` about
`E r log T`, which needs `r log D` bounded (here `r ≤ r₁`), not `r ≤ 1/4`. See
`Linnik/Audit1619`. `pW_gallagher_zero_detector_of_turan` below keeps its statement and takes
`min r₀ r₁`. -/
private theorem pW_poisson_window_localization :
    ∀ E D η : ℝ, 1 ≤ E → 1 ≤ D → 0 < η →
      ∃ r₁ A B C c : ℝ, 0 < r₁ ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
        ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
          |v| ≤ T → 1 / Real.log T ≤ r → r ≤ r₁ →
          (∀ M : ℕ, E * r * Real.log T ≤ M →
            ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
              η / (D ^ k * r) ≤
                ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                  (n : ℂ) ^ (1 + I * v)) * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖) →
          ∀ x : ℝ, T ^ A ≤ x → ∃ k : ℕ,
            c * x ^ (-C * r) * Real.log x ^ 2 * r ≤
              ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ B⌋₊,
                (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n‖ -
                Decomp1532b2.poissonKernel k (r * Real.log (x ^ B)) * ‖primeDetector χ x (x ^ B) v‖ := by
  exact pW_poisson_window_localization_proof

/-- Gallagher 1970 p.335 the calculus bound for the finite prime window.
The arithmetic lower bound and its zero hypothesis are absent. -/
private theorem pW_prime_poisson_partial_summation {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) {r x y : ℝ} (v : ℝ) (hr : 0 ≤ r) (hx : 1 ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊,
        (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n‖ -
        Decomp1532b2.poissonKernel k (r * Real.log y) * ‖primeDetector χ x y v‖ ≤
      r * ∫ t in x..y, ‖primeDetector χ x t v‖ / t := by
  have ha : ∀ n ≤ ⌊x⌋₊, (fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0) n = 0 := by
    intro n hn
    simp [not_lt.mpr hn]
  simpa only [pW_sum_primeWindowCoefficient] using
    pW_poisson_partial_summation_bound ((fun m => if ⌊x⌋₊ < m ∧ m.Prime then (Real.log m / (m : ℝ) : ℂ) * χ m * Complex.exp (-((Real.log m * v : ℝ) : ℂ) * I) else 0)) k hr hx hxy ha

/-- Gallagher 1970 Theorem 5 display 20.
Exact sealed detector statement assembled from the two smaller arithmetic leaves.
CONDITIONAL ON those leaves. This theorem has no proof hole of its own. -/
private theorem pW_gallagher_zero_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  obtain ⟨r₀, E, D, η, hr₀, hr₀hi, hE, hD, hη, hseries⟩ :=
    pA_poisson_series_detector_of_turan hpower
  obtain ⟨r₁, A, B, C, c, hr₁, hA, hB, hC, hc, hwindow⟩ :=
    pW_poisson_window_localization E D η hE hD hη
  refine ⟨min r₀ r₁, A, B, C, c, lt_min hr₀ hr₁, (min_le_left _ _).trans hr₀hi,
    hA, hB, hC, hc, ?_⟩
  intro T hT q hq hqT χ v r hv hχ hrlo hrhi hz x hx
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hl).trans_le hrlo
  have hx1 : 1 ≤ x :=
    (Real.one_le_rpow (by linarith : 1 ≤ T) (by linarith : 0 ≤ A)).trans hx
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  obtain ⟨k, hk⟩ := hwindow T hT q hqT χ v r hv hrlo (hrhi.trans (min_le_right _ _))
    (hseries T hT q hqT χ v r hv hχ hrlo (hrhi.trans (min_le_left _ _)) hz) x hx
  have hh := hk.trans (pW_prime_poisson_partial_summation χ k v hr.le hx1 hxy)
  exact (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_comm r] using hh)

end PortpW

end PortTuran


/-- LEAF. Gallagher 1970 pp.333 to 335, Theorem 5 display 20.
CONDITIONAL ON the finite Turan power bound. The remaining proof is the analytic
logarithmic derivative expansion, its tail estimate, prime power removal and partial summation.
The principal character height exclusion is part of the source statement. -/
theorem gallagher_zero_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  exact pW_gallagher_zero_detector_of_turan hpower


/-- Gallagher 1970 p.333 Theorem 5 display 20.
CONDITIONAL ON turan_interpolant and gallagher_zero_detector_of_turan. -/
theorem gallagher_zero_detector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  exact gallagher_zero_detector_of_turan
    (fun n M hn hnM z hz => turan_power_sum_lower_bound hn hnM z hz)


/-- Complex coefficient form of the finite Gauss identity in Gallagher 1970 p.333.
The conjugated additive coefficients account for the conjugate character in the Gauss sum.
This identity is one finite input to display 18. -/
theorem weighted_gauss_parseval {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ)
    (hs : ∀ n ∈ s, IsUnit (n : ZMod q)) :
    (q.totient : ℝ) * ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
      ‖∑ n ∈ s, star (a n) * stdAddChar (b * (n : ZMod q))‖ ^ 2 =
    ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
  rw [← LeanLab.RieselVaughan1983.GaussImprim.sum_norm_sq_twist]
  apply sum_congr rfl
  intro χ _
  have he : ∑ b, χ b * ∑ n ∈ s, star (a n) * stdAddChar (b * (n : ZMod q)) =
      gaussSum χ stdAddChar * star (∑ n ∈ s, a n * χ (n : ZMod q)) := by
    calc
      _ = ∑ n ∈ s, star (a n) * ∑ b, χ b * stdAddChar (b * (n : ZMod q)) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro b _
        ring
      _ = ∑ n ∈ s, star (a n) * (gaussSum χ stdAddChar * star (χ (n : ZMod q))) := by
        apply sum_congr rfl
        intro n hn
        congr 1
        have hu := hs n hn
        have h := gaussSum_mulShift_eq χ stdAddChar hu.unit
        rw [hu.unit_spec, gaussSum] at h
        rw [MulChar.star_apply', mul_comm (gaussSum χ stdAddChar), ← h]
        apply sum_congr rfl
        intro b _
        rw [AddChar.mulShift_apply, mul_comm (n : ZMod q) b]
      _ = _ := by
        rw [star_sum, mul_sum]
        apply sum_congr rfl
        intro n _
        rw [star_mul]
        ring
  rw [he, norm_mul, mul_pow, norm_star]


/-- Complex coefficient conductor regrouping in Gallagher 1970 p.333 display 19.
The support is prime to the larger modulus so changing level preserves every term. -/
theorem weighted_character_conductor_fiber (s : Finset ℕ) (a : ℕ → ℂ)
    {q r : ℕ} [NeZero q] (hrq : r ∣ q) (hs : ∀ n ∈ s, n.Coprime q) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = r),
      ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2) =
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
      ‖∑ n ∈ s, a n * ψ (n : ZMod r)‖ ^ 2 := by
  classical
  have hr : r ≠ 0 := by
    rintro rfl
    exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hrq)
  letI : NeZero r := ⟨hr⟩
  symm
  apply sum_bij (fun ψ _ => DirichletCharacter.changeLevel hrq ψ)
  · intro ψ hψ
    rw [mem_filter] at hψ ⊢
    exact ⟨mem_univ _, by rw [DirichletCharacter.conductor_changeLevel]; exact hψ.2⟩
  · intro ψ1 _ ψ2 _ h
    exact DirichletCharacter.changeLevel_injective hrq h
  · intro χ hχ
    rw [mem_filter] at hχ
    have hf : χ.FactorsThrough r := by
      have := χ.factorsThrough_conductor
      rwa [hχ.2] at this
    obtain ⟨_, χ₀, hχ₀⟩ := hf
    refine ⟨χ₀, ?_, hχ₀.symm⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← DirichletCharacter.conductor_changeLevel χ₀ hrq, ← hχ₀, hχ.2]
  · intro ψ _
    congr 2
    apply sum_congr rfl
    intro n hn
    congr 1
    have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr (hs n hn)
    have he := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hrq hu.unit
    rw [hu.unit_spec] at he
    rw [he, ZMod.cast_natCast hrq]

/-- Finite conductor lower bound in Gallagher 1970 p.333 display 19.
Only squarefree conductor multiples prime to the conductor are retained. -/
theorem weighted_gauss_conductor_lower (s : Finset ℕ) (a : ℕ → ℂ)
    {q : ℕ} [NeZero q] (hs : ∀ n ∈ s, n.Coprime q) :
    (∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
      ((μ (q / r) : ℤ) : ℝ) ^ 2 * r *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
          ‖∑ n ∈ s, a n * ψ (n : ZMod r)‖ ^ 2) ≤
    ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
  classical
  have hq : q ≠ 0 := NeZero.ne q
  let E : ℕ → ℝ := fun r =>
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
      ‖∑ n ∈ s, a n * ψ (n : ZMod r)‖ ^ 2
  change (∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
    ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r) ≤ _
  set good : DirichletCharacter ℂ q → Prop :=
    fun χ => Squarefree (q / χ.conductor) ∧ χ.conductor.Coprime (q / χ.conductor)
  calc ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r
      = ∑ r ∈ q.divisors.filter (fun r => Squarefree (q / r) ∧ r.Coprime (q / r)),
          ∑ χ ∈ (univ.filter good).filter (fun χ => χ.conductor = r),
            ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
        rw [sum_filter, sum_filter]
        refine sum_congr rfl fun r hr => ?_
        have hrq : r ∣ q := Nat.dvd_of_mem_divisors hr
        by_cases hsq : Squarefree (q / r)
        · by_cases hc : r.Coprime (q / r)
          · rw [if_pos hc.symm, if_pos ⟨hsq, hc⟩, filter_filter]
            have hf : univ.filter (fun χ : DirichletCharacter ℂ q => good χ ∧ χ.conductor = r) =
                univ.filter (fun χ => χ.conductor = r) := by
              ext χ; simp only [mem_filter, mem_univ, true_and, good]
              constructor
              · exact fun h => h.2
              · intro h; refine ⟨?_, h⟩; rw [h]; exact ⟨hsq, hc⟩
            rw [hf]
            dsimp only [E]
            rw [← weighted_character_conductor_fiber s a hrq hs, mul_sum]
            refine sum_congr rfl fun χ hχ => ?_
            rw [mem_filter] at hχ
            have hg : good χ := by simp only [good]; rw [hχ.2]; exact ⟨hsq, hc⟩
            have hm : ((μ (q / r) : ℤ) : ℝ) ^ 2 = 1 := by
              exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
            rw [LeanLab.RieselVaughan1983.GaussImprim.norm_sq_gaussSum_eq_conductor χ hg.1 hg.2, hχ.2, hm]
            ring
          · rw [if_neg (fun h => hc h.symm), if_neg (fun h => hc h.2)]
        · have hm0 : ((μ (q / r) : ℤ) : ℝ) = 0 := by
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
          simp [hsq]
      _ = ∑ χ ∈ univ.filter good,
            ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
        refine sum_fiberwise_of_maps_to
          (g := fun χ : DirichletCharacter ℂ q => χ.conductor) (fun χ hχ => ?_) _
        rw [mem_filter] at hχ ⊢
        exact ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq⟩, hχ.2⟩
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The logarithmic conductor gain in Gallagher 1970 p.333 after display 19.
The proof uses the coprime Moebius over totient lower bound already proved in the lab. -/
theorem logarithmic_conductor_weight_le
    (Q : ℕ) (E : ℕ → ℝ) (hE : ∀ r ∈ Finset.Icc 1 Q, 0 ≤ E r) :
    (∑ r ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / r) * E r) ≤
    ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ *
      ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r := by
  let F : ℕ → ℕ → ℝ := fun r m => ((μ m : ℤ) : ℝ) ^ 2 * r / ((r * m).totient : ℝ) * E r
  have heq : (∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ *
      ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r), F r (q / r) := by
    apply sum_congr rfl
    intro q _
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    have hrd : r ∣ q := Nat.dvd_of_mem_divisors (mem_filter.mp hr).1
    dsimp [F]
    rw [Nat.mul_div_cancel' hrd]
    ring
  rw [heq, LeanLab.RieselVaughan1983.Page65.sum_swap]
  apply sum_le_sum
  intro r hr
  have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hlog := mul_le_mul_of_nonneg_right
    (LeanLab.RieselVaughan1983.MuPhi.log_le_mu_phi_sum r hr1 ((Q : ℝ) / r) (div_nonneg (Nat.cast_nonneg _) hrpos.le)) (hE r hr)
  apply hlog.trans_eq
  have hset := LeanLab.RieselVaughan1983.Page65.m_range hr1 (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)
  simp only [Nat.floor_natCast] at hset
  rw [hset, mul_sum, sum_mul]
  apply sum_congr rfl
  intro m hm
  simp only [mem_filter, mem_Icc] at hm
  have hφr : (r.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  have hφm : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  dsimp [F]
  rw [Nat.totient_mul hm.2.2.symm]
  push_cast
  field_simp

/-- The finite rough support character sieve reduces to the sharp additive sieve.
Gallagher 1970 pp.332 and 333, displays 17 through 19. -/
theorem rough_character_sieve_le_additive
    (s : Finset ℕ) (a : ℕ → ℂ) (Q : ℕ)
    (hs : ∀ n ∈ s, ∀ q ∈ Finset.Icc 1 Q, n.Coprime q) :
    (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
    ∑ q ∈ Finset.Icc 1 Q, ∑ c ∈ (range q).filter (fun c => c.Coprime q),
      ‖∑ n ∈ s, star (a n) * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 := by
  classical
  let E : ℕ → ℝ := fun q =>
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q),
      ‖∑ n ∈ s, a n * χ n‖ ^ 2
  have hEeq (q : ℕ) : E q =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2 := by
    dsimp only [E]
    rw [sum_filter, sum_filter]
    apply sum_congr rfl
    intro χ _
    by_cases hχ : χ.conductor = q
    · simp [DirichletCharacter.IsPrimitive, hχ]
    · simp [DirichletCharacter.IsPrimitive, hχ]
  simp_rw [← hEeq]
  apply (logarithmic_conductor_weight_le Q E (fun q _ => sum_nonneg (fun χ _ => sq_nonneg _))).trans
  apply sum_le_sum
  intro q hq
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  letI : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlow := weighted_gauss_conductor_lower s a (fun n hn => hs n hn q hq)
  have hunit : ∀ n ∈ s, IsUnit (n : ZMod q) :=
    fun n hn => (ZMod.isUnit_iff_coprime n q).mpr (hs n hn q hq)
  rw [← weighted_gauss_parseval s a hunit] at hlow
  have hdiv : (q.totient : ℝ)⁻¹ *
      (∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r) ≤
      ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
        ‖∑ n ∈ s, star (a n) * stdAddChar (b * (n : ZMod q))‖ ^ 2 := by
    rw [inv_mul_le_iff₀ hφ]
    exact hlow
  apply hdiv.trans_eq
  rw [sum_filter, LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, sum_filter]
  apply sum_congr rfl
  intro c _
  by_cases hc : c.Coprime q
  · rw [if_pos ((ZMod.isUnit_iff_coprime c q).mpr hc), if_pos hc]
    congr 2
    apply sum_congr rfl
    intro n _
    congr 1
    rw [mul_comm (c : ZMod q) (n : ZMod q)]
    simpa only [Int.cast_natCast] using
      LeanLab.PNTPort.LargeSieve.stdAddChar_mul_natCast (q := q) (n : ℤ) c
  · rw [if_neg (fun h => hc ((ZMod.isUnit_iff_coprime c q).mp h)), if_neg hc]

/-- Gallagher 1970 p.332 Lemma 4 display 17, proved using the complex coefficient
Gauss identity, conductor regrouping and the coprime Moebius over totient lower bound
on p.333 displays 18 and 19. For integer endpoints the constant can be one. -/
theorem gallagher_rough_finite_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ (a : ℕ → ℂ) (M L : ℕ),
      (∀ n ∈ Finset.Ioc M (M + L), ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), a n * χ n‖ ^ 2) ≤
        C * ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + L), ‖a n‖ ^ 2 := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro Q hQ a M L hrough
  let S : Finset ℕ := (Finset.Ioc M (M + L)).filter (fun n => a n ≠ 0)
  have hs : ∀ n ∈ S, ∀ q ∈ Finset.Icc 1 Q, n.Coprime q := by
    intro n hn q hq
    obtain ⟨hnI, hna⟩ := mem_filter.mp hn
    by_contra hc
    obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpQ : p ≤ Q := (Nat.le_of_dvd (by have := (mem_Icc.mp hq).1; omega) hpq).trans (mem_Icc.mp hq).2
    exact hna (hrough n hnI p hp hpQ hpn)
  have hsum (f : ℕ → ℂ) : (∑ n ∈ S, a n * f n) = ∑ n ∈ Finset.Ioc M (M + L), a n * f n := by
    dsimp [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : a n = 0 <;> simp [hn]
  have hstar (f : ℕ → ℂ) : (∑ n ∈ S, star (a n) * f n) =
      ∑ n ∈ Finset.Ioc M (M + L), star (a n) * f n := by
    dsimp [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : a n = 0 <;> simp [hn]
  have hb := rough_character_sieve_le_additive S a Q hs
  simp_rw [hsum, hstar] at hb
  apply hb.trans
  simpa only [norm_star, one_mul] using additive_large_sieve_sharp (fun n => star (a n)) M L Q

/-- Gallagher 1970 p.332 Theorem 4 from its finite Lemma 4 input.
CONDITIONAL ON the supplied finite rough support sieve. The time smoothing is proved here. -/
theorem hybrid_of_weighted_finite_sieve
    (Q : ℕ) (hQ : 1 ≤ Q) (C : ℝ) (hC : 0 ≤ C) (weight : ℕ → ℝ)
    (hw : ∀ q ∈ Finset.Icc 1 Q, 0 ≤ weight q)
    (hfinite : ∀ (b : ℕ → ℂ) (M L : ℕ),
      (∀ n ∈ Finset.Ioc M (M + L), ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → b n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), b n * χ n‖ ^ 2) ≤
        C * ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + L), ‖b n‖ ^ 2)
    (N : ℕ) (a : ℕ → ℂ)
    (hrough : ∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0)
    {T : ℝ} (hT : 1 ≤ T) :
    (∑ q ∈ Finset.Icc 1 Q, weight q *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
      (2 * Real.pi ^ 3 * C) *
        ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  have hsieve (s : Finset ℕ) (M L : ℕ) (hs : s ⊆ Finset.Ioc M (M + L))
      (hsN : s ⊆ Finset.Icc 1 N) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
        C * ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
    let b : ℕ → ℂ := fun n => if n ∈ s then a n else 0
    have hb : ∀ n ∈ Finset.Ioc M (M + L), ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → b n = 0 := by
      intro n _ p hp hpQ hpn
      by_cases hn : n ∈ s
      · simp only [b, if_pos hn]
        exact hrough n (hsN hn) p hp hpQ hpn
      · simp [b, hn]
    have hset : (Finset.Ioc M (M + L)).filter (fun n => n ∈ s) = s := by
      ext n
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hn => hs hn)
    have hsum {q : ℕ} (χ : DirichletCharacter ℂ q) :
        (∑ n ∈ Finset.Ioc M (M + L), b n * χ n) = ∑ n ∈ s, a n * χ n := by
      simp only [b, ite_mul, zero_mul, ← sum_filter, hset]
    have henergy : (∑ n ∈ Finset.Ioc M (M + L), ‖b n‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [b, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
        ← sum_filter, hset]
    simpa only [hsum, henergy] using hfinite b M L hb
  have hreal (s : Finset ℕ) (hsN : s ⊆ Finset.Icc 1 N) {x y : ℝ}
      (hx : 0 ≤ x) (hxy : x ≤ y)
      (hs : ∀ n ∈ s, 1 ≤ n ∧ x ≤ n ∧ (n : ℝ) ≤ y) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
        C * (y - x + 2 + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
    let M := ⌊x⌋₊ - 1
    let U := ⌊y⌋₊
    have hMU : M ≤ U := (Nat.sub_le _ _).trans (Nat.floor_mono hxy)
    have hs' : s ⊆ Finset.Ioc M (M + (U - M)) := by
      intro n hn
      have hn1 := (hs n hn).1
      have hxn : ⌊x⌋₊ ≤ n := by
        have := (Nat.floor_le hx).trans (hs n hn).2.1
        exact_mod_cast this
      have hny : n ≤ U := Nat.le_floor (hs n hn).2.2
      rw [Finset.mem_Ioc, Nat.add_sub_of_le hMU]
      dsimp [M]
      omega
    have hMlow : x - 2 ≤ (M : ℝ) := by
      have hfloor := Nat.lt_floor_add_one x
      have hnat : ⌊x⌋₊ ≤ M + 1 := by dsimp [M]; omega
      have hnatR : (⌊x⌋₊ : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hnat
      linarith
    have hUL : ((U - M : ℕ) : ℝ) ≤ y - x + 2 := by
      rw [Nat.cast_sub hMU]
      have hu : (U : ℝ) ≤ y := Nat.floor_le (hx.trans hxy)
      linarith
    apply (hsieve s M (U - M) hs' hsN).trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hwindow {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2) ≤
        C * (Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
    let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n => u ∈ Set.Icc (Real.log n - δ) (Real.log n))
    have heq {q : ℕ} (χ : DirichletCharacter ℂ q) :
        frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u =
        ∑ n ∈ S, a n * χ n := by
      simp only [frequencyWindow, S, sum_filter, Set.indicator]
    have hnorm : (∑ n ∈ S, ‖a n‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
      simp only [S, sum_filter, Set.indicator]
    have hs : ∀ n ∈ S, 1 ≤ n ∧ Real.exp u ≤ n ∧ (n : ℝ) ≤ Real.exp (u + δ) := by
      intro n hn
      obtain ⟨hnN, hnu⟩ := mem_filter.mp hn
      have hn1 := (mem_Icc.mp hnN).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      refine ⟨hn1, ?_, ?_⟩
      · calc
          Real.exp u ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hnu.2
          _ = _ := Real.exp_log hnpos
      · calc
          (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
          _ ≤ Real.exp (u + δ) := Real.exp_le_exp.mpr (by linarith [hnu.1])
    simpa only [heq, hnorm] using hreal S (filter_subset _ _) (Real.exp_pos u).le
      (Real.exp_le_exp.mpr (by linarith)) hs
  have hintegrated {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
            (fun n => Real.log n) δ u‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 := by
    let K : ℝ → ℝ := fun u => Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2
    let W {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) :=
      ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
    have hiW {q : ℕ} (χ : DirichletCharacter ℂ q) : Integrable (W χ) :=
      integrable_frequencyWindow_energy _ _ _ _
    have hiR (n : ℕ) : Integrable (fun u => K u *
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u) := by
      have heq : (fun u => K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator
          (fun _ => ‖a n‖ ^ 2) u) =
          (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun u => K u * ‖a n‖ ^ 2) := by
        ext u
        by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n) <;> simp [hu]
      rw [heq]
      exact (by dsimp [K]; fun_prop : Continuous (fun u => K u * ‖a n‖ ^ 2)).integrableOn_Icc.integrable_indicator measurableSet_Icc
    have heq (q : ℕ) :
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) =
        ∫ u, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ u :=
      (integral_finsetSum _ (fun χ _ => hiW χ)).symm
    change (∑ q ∈ Finset.Icc 1 Q, weight q *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) ≤ _
    simp_rw [heq, ← integral_const_mul]
    rw [← integral_finsetSum _ (fun q _ => (integrable_finsetSum _ (fun χ _ => hiW χ)).const_mul _)]
    calc
      _ ≤ ∫ u, C * ∑ n ∈ Finset.Icc 1 N, K u *
          (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
        apply integral_mono
          (integrable_finsetSum _ (fun q _ => (integrable_finsetSum _ (fun χ _ => hiW χ)).const_mul _))
          ((integrable_finsetSum _ (fun n _ => hiR n)).const_mul _)
        intro u
        dsimp only [W, K]
        rw [← mul_sum, ← mul_assoc]
        exact hwindow hδ.le u
      _ = C * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 *
          ∫ u : ℝ, K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => (1 : ℝ)) u := by
        rw [integral_const_mul, integral_finsetSum _ (fun n _ => hiR n)]
        congr 1
        apply sum_congr rfl
        intro n _
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with u
        by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n)
        · simp [hu]; ring
        · simp [hu]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply sum_le_sum
        intro n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hb := mellin_window_weight_bound (Real.log n) ((Q : ℝ) ^ 2) hδ.le hδ1
        rw [Real.exp_log hnpos] at hb
        dsimp [K]
        have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a n‖)
        nlinarith
  let δ : ℝ := 1 / T
  have hTpos : 0 < T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_one hTpos]; exact hT
  let D : ℝ := Real.pi ^ 3 / (2 * δ ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let W {q : ℕ} (χ : DirichletCharacter ℂ q) :=
    ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have htime {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) ≤ D * W χ := by
    rw [characterPolynomial_time_integral]
    have hnear : δ * (T / (2 * Real.pi)) ≤ 1 / 2 := by
      dsimp [δ]
      have he : (1 / T) * (T / (2 * Real.pi)) = 1 / (2 * Real.pi) := by field_simp
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Real.pi_gt_three]
    have hh := gallagher_window_smoothing (Finset.Icc 1 N) (fun n => a n * χ n)
      (fun n => Real.log n) hδ (div_nonneg hTpos.le (by positivity)) hnear
    apply (mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).trans_eq
    dsimp [D, W]
    ring
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), D * W χ := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun χ _ => htime χ)) (hw q hq)
    _ = D * (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro χ _
      ring
    _ ≤ D * (C * ∑ n ∈ Finset.Icc 1 N,
        (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hintegrated hδ hδ1) hD
    _ ≤ _ := by
      simp only [mul_sum]
      apply sum_le_sum
      intro n _
      have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hQsq : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
      have he : D * (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) =
          (Real.pi ^ 3 / 2) * T * ((Q : ℝ) ^ 2 + 2) + Real.pi ^ 3 * n := by
        dsimp [D, δ]
        field_simp
      have hmult := mul_le_mul_of_nonneg_left
        (show (Q : ℝ) ^ 2 + 2 ≤ 3 * (Q : ℝ) ^ 2 by linarith)
        (show 0 ≤ (Real.pi ^ 3 / 2) * T by positivity)
      have hrest : 0 ≤ Real.pi ^ 3 * ((Q : ℝ) ^ 2 * T) := by positivity
      have hrest2 : 0 ≤ Real.pi ^ 3 * n := by positivity
      have hb : D * (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) ≤
          2 * Real.pi ^ 3 * ((Q : ℝ) ^ 2 * T + n) := by rw [he]; nlinarith
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC) (sq_nonneg ‖a n‖)
      convert hh using 1 <;> ring

/-- Gallagher 1970 p.332 Theorem 4 display 16. The rough support hypothesis
is essential. Its finite input is Lemma 4 display 17, proved using imprimitive Gauss sums
and the coprime Moebius over totient lower bound on p.333 displays 18 and 19.
The already proved smoothing for Theorem 3 supplies the time variable argument. -/
theorem gallagher_prime_hybrid_mean_value : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hfinite⟩ := gallagher_rough_finite_sieve
  refine ⟨2 * Real.pi ^ 3 * C, by positivity, ?_⟩
  intro Q hQ T hT N a hrough
  apply hybrid_of_weighted_finite_sieve Q hQ C hC.le (fun q => Real.log ((Q : ℝ) / q))
    _ (hfinite Q hQ) N a hrough hT
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  apply Real.log_nonneg
  rw [le_div_iff₀ hq0, one_mul]
  exact_mod_cast (Finset.mem_Icc.mp hq).2


section PortGallagherDensity

open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
open Finset MeasureTheory Complex
open scoped Classical

/-! ## Port of Decomp340a: endpoint integration and the scalar normalization -/

/-- Endpoint functions on natural floors are integrable with logarithmic weight
on every compact interval with positive lower endpoint. -/
private theorem pG_integrableOn_floor_div (F : ℕ → ℝ) {x y : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => F ⌊t⌋₊ / t) (Set.Icc x y) := by
  have hm : Measurable (fun t : ℝ => F ⌊t⌋₊ / t) :=
    ((measurable_of_countable F).comp Nat.measurable_floor).div measurable_id
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hm.aestronglyMeasurable
    ((∑ n ∈ range (⌊y⌋₊ + 1), ‖F n‖) / x)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 < t := hx.trans_le ht.1
  have hn : ⌊t⌋₊ ∈ range (⌊y⌋₊ + 1) :=
    mem_range.mpr (by have := Nat.floor_le_floor ht.2; omega)
  have hF : ‖F ⌊t⌋₊‖ ≤ ∑ n ∈ range (⌊y⌋₊ + 1), ‖F n‖ :=
    single_le_sum (fun n _ => norm_nonneg (F n)) hn
  rw [norm_div, Real.norm_of_nonneg ht0.le]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hx ht.1).trans
    (div_le_div_of_nonneg_right hF hx.le)

/-- Uniform scalar normalization of the fixed character count. -/
private theorem pG_detector_count_scale {n a c₀ C K B l d r E : ℝ}
    (hn : 0 ≤ n) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (hK : 0 < K) (hl : 0 < l)
    (hr : r ≤ d + 1 / (2 * l))
    (hcount : n * (c₀ * Real.exp (-2 * C * K * r * l) * (K * l) ^ 2) ^ 2 ≤
      a * l * ((B - 1) * K * l) * E) :
    n ≤ (a * (B - 1) / (c₀ ^ 2 * K ^ 3) * Real.exp (2 * C * K)) *
      Real.exp (4 * C * K * d * l) * E / l ^ 2 := by
  have hrl : r * l ≤ d * l + 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hr hl.le
    have he : (1 / (2 * l)) * l = 1 / 2 := by field_simp
    nlinarith
  have hex : Real.exp (-4 * C * K * d * l - 2 * C * K) ≤
      Real.exp (-4 * C * K * r * l) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hrl (show 0 ≤ 4 * C * K by positivity)
    nlinarith
  have hg : 1 ≤ Real.exp (-4 * C * K * r * l) *
      Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K) := by
    calc
      1 = Real.exp (-4 * C * K * d * l - 2 * C * K) *
          Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K) := by
        rw [← Real.exp_add, ← Real.exp_add]
        have he : (-4 * C * K * d * l - 2 * C * K) + 4 * C * K * d * l + 2 * C * K = 0 := by ring
        rw [he, Real.exp_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hex (Real.exp_pos _).le) (Real.exp_pos _).le
  have hsq : (c₀ * Real.exp (-2 * C * K * r * l) * (K * l) ^ 2) ^ 2 =
      c₀ ^ 2 * Real.exp (-4 * C * K * r * l) * K ^ 4 * l ^ 4 := by
    have he : Real.exp (-2 * C * K * r * l) ^ 2 = Real.exp (-4 * C * K * r * l) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = c₀ ^ 2 * Real.exp (-2 * C * K * r * l) ^ 2 * K ^ 4 * l ^ 4 := by ring
      _ = _ := by rw [he]
  have hm := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K) by positivity)
  rw [hsq] at hm
  have hlo := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ n * c₀ ^ 2 * K ^ 4 * l ^ 4 by positivity)
  have hb : n * (c₀ ^ 2 * K ^ 4 * l ^ 4) ≤
      (a * l * ((B - 1) * K * l) * E) *
        (Real.exp (4 * C * K * d * l) * Real.exp (2 * C * K)) := by
    nlinarith [hm, hlo]
  apply (mul_le_mul_iff_right₀ (show 0 < c₀ ^ 2 * K ^ 4 * l ^ 4 by positivity)).mp
  convert hb using 1 <;> field_simp [hc₀.ne', hK.ne', hl.ne']

/-! ## Port of the two local-count inputs declared later in the file

`primitive_local_zero_order_sum` and `principal_low_height_zero_count` are declared *below*
the leaf in Decomp1532b, so the leaf cannot use them; the two lemmas are restated here
(identical statements, same short proofs from inputs declared above the leaf). -/

/-- Local density lemma in the uniform height box, including multiplicities. -/
private theorem pG_local_zero_order_sum : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ t r : ℝ,
      |t| ≤ T → (χ = 1 → 2 ≤ |t|) → 1 / Real.log T ≤ r → r ≤ 1 / 8 →
      ∀ S : Finset ℂ, (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + Complex.I * t)‖ ≤ r) →
      (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * r * Real.log T := by
  obtain ⟨C, hC, hc⟩ := LeanLab.Linnik.Decomp1532b2.local_zero_order_sum_primitive
  obtain ⟨K, hK, hk⟩ := log_Bt_le_log_height
  refine ⟨C * (1 + K), by positivity, ?_⟩
  intro T hT q hq hqT χ hp t r ht hχ hrlo hrhi S hS
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlT).trans_le hrlo
  have hrlog : 1 ≤ r * Real.log T := (div_le_iff₀ hlT).mp hrlo
  have hlog := hk hT hqT ht
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have h := hc q χ hp t r hχ hr hrhi S hS
  apply h.trans
  have hs : 1 + r * Real.log (LeanLab.PNTPort.DirichletZF.Bt q t) ≤
      (1 + K) * r * Real.log T := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hC
  nlinarith

/-- The bounded principal low height contribution. -/
private theorem pG_principal_low_height_zero_count : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 / 2 ≤ σ →
    (zeroCount (1 : DirichletCharacter ℂ 1) σ 3 : ℝ) ≤ C := by
  obtain ⟨A, hA, h⟩ := zeroCount_le_unit_height
  refine ⟨4 * A * Real.log 5, by positivity, ?_⟩
  intro σ hσ
  have hc := h 1 1 DirichletCharacter.isPrimitive_one_level_one σ 3 hσ (by norm_num)
  convert hc using 1; norm_num

/-! ## Port of Decomp340c: finite zero families and local occupancy -/

/-- Primitive zero counts are the cardinalities of finite families with the `zeroCount`
predicates. -/
private theorem pG_exists_zeroCount_finset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) :
    ∃ S : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ S ↔ χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
      S.card = zeroCount χ σ T := by
  have hψ : q = 1 ∨ χ ≠ 1 := by
    by_cases hq : q = 1
    · exact Or.inl hq
    · right
      intro hχ
      apply hq
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hh
      exact hh.symm
  have hnt {ρ : ℂ} (hz : χ.LFunction ρ = 0) (hβ : σ ≤ ρ.re) :
      LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ := by
    refine ⟨hz, by linarith, ?_⟩
    by_contra h
    have hre : 1 ≤ ρ.re := le_of_not_gt h
    rcases hψ with rfl | hχ
    · rw [DirichletCharacter.LFunction_modOne_eq] at hz
      exact riemannZeta_ne_zero_of_one_le_re hre hz
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre hz
  obtain ⟨S₀, hS₀⟩ := LeanLab.HardyLittlewood1923.U1479.exists_zero_finset
    LeanLab.HardyLittlewood1923.U1482.zeroCountUnit hp hT
  let S := S₀.filter (fun ρ => σ ≤ ρ.re)
  have hS (ρ : ℂ) : ρ ∈ S ↔ χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    simp only [S, mem_filter, hS₀]
    constructor
    · rintro ⟨⟨hρ, hγ⟩, hβ⟩
      exact ⟨hρ.1, hβ, hγ⟩
    · rintro ⟨hz, hβ, hγ⟩
      exact ⟨⟨hnt hz hβ, hγ⟩, hβ⟩
  refine ⟨S, hS, ?_⟩
  have heq : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} = (S : Set ℂ) := by
    ext ρ
    exact (hS ρ).symm
  rw [zeroCount, heq, Set.ncard_coe_finset]

/-- The proved local multiplicity bound also bounds the number of distinct
primitive zeros in the same disc. -/
private theorem pG_primitive_local_zero_card : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ t r : ℝ,
      |t| ≤ T → (χ = 1 → 2 ≤ |t|) → 1 / Real.log T ≤ r → r ≤ 1 / 8 →
      ∀ S : Finset ℂ, (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      (S.card : ℝ) ≤ C * r * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := pG_local_zero_order_sum
  refine ⟨C, hC, ?_⟩
  intro T hT q hq hqT χ hp t r ht hχ hrlo hrhi S hS
  have hψ : q = 1 ∨ χ ≠ 1 := by
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      intro he
      apply hq1
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, he, DirichletCharacter.conductor_one] at hh
      exact hh.symm
  have horder (ρ : ℂ) (hρ : ρ ∈ S) :
      (1 : ℝ) ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ) := by
    have hw : ρ ≠ 1 := by
      intro he
      have hz := (hS ρ hρ).1
      rw [he] at hz
      rcases hψ with rfl | hχ1
      · rw [DirichletCharacter.LFunction_modOne_eq] at hz
        exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp) hz
    have hz : analyticOrderNatAt χ.LFunction ρ ≠ 0 := by
      simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(LeanLab.HardyLittlewood1923.U1482.L_analyticAt χ hw).analyticOrderAt_ne_zero.mpr
          (hS ρ hρ).1,
        LeanLab.HardyLittlewood1923.U1482.L_ord_ne_top χ hψ hw⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  calc
    _ = ∑ _ρ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) := sum_le_sum horder
    _ ≤ _ := hbound T hT q hqT χ hp t r ht hχ hrlo hrhi S hS

/-- Distinct zeros in a narrow right strip have bounded occupancy in each vertical
height window. -/
private theorem pG_primitive_height_window_occupancy : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ v r : ℝ,
      |v| ≤ T → (χ = 1 → 2 ≤ |v|) →
      1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 →
      ∀ S : Finset ℂ,
      (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ 1 - r ≤ ρ.re ∧ ρ.re ≤ 1) →
      (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ C * r * Real.log T := by
  obtain ⟨C, hC, hcard⟩ := pG_primitive_local_zero_card
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT q hq hqT χ hp v r hv hχ hrlo hrhi S hS
  let Z := S.filter (fun ρ => v ∈ Set.Icc (ρ.im - r) (ρ.im + r))
  have hZ (ρ : ℂ) (hρ : ρ ∈ Z) : χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r := by
    obtain ⟨hρS, hρv⟩ := mem_filter.mp hρ
    obtain ⟨hz, hβlo, hβhi⟩ := hS ρ hρS
    have hre : |ρ.re - 1| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hρv.2], by linarith [hρv.1]⟩
    refine ⟨hz, ?_⟩
    calc
      _ ≤ |(ρ - (1 + I * v)).re| + |(ρ - (1 + I * v)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 1| + |ρ.im - v| := by simp
      _ ≤ _ := by linarith
  have heq : (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
      (fun _ => (1 : ℝ)) v) = (Z.card : ℝ) := by
    simp only [Z, Set.indicator, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [heq]
  have hh := hcard T hT q hqT χ hp v (2 * r) hv hχ hrlo hrhi Z hZ
  convert hh using 1; ring

end PortGallagherDensity



section PortGallagherEnergy

open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
open Finset MeasureTheory Complex
open scoped Classical

/-! ## Port of Decomp307b: prime window coefficients and the detector energy

`primeWindowWeight x n` of the original is written out as
`if ⌊x⌋₊ < n ∧ n.Prime then ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0`
and `detectorEnergy T x y` as the explicit double sum over `q ∈ Icc 1 ⌊T⌋₊` and primitive
characters of `∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2`. -/

/-- The prime window polynomial is the prime detector. -/
private theorem pG_charPoly_primeWindow {q : ℕ} (χ : DirichletCharacter ℂ q) (x y v : ℝ) :
    characterPolynomial χ
        (fun n => if ⌊x⌋₊ < n ∧ n.Prime then ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0)
        ⌊y⌋₊ v = primeDetector χ x y v := by
  classical
  unfold characterPolynomial primeDetector
  simp only [ite_mul, zero_mul, Complex.ofReal_div]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hn, hp⟩
    exact ⟨⟨hn, hu⟩, hp⟩
  · rintro ⟨⟨hn, hu⟩, hp⟩
    exact ⟨⟨by omega, hu⟩, hn, hp⟩

/-- The prime window coefficients satisfy Gallagher's rough support condition. -/
private theorem pG_primeWindow_rough {x : ℝ} {Q : ℕ} (hQ : (Q : ℝ) ≤ x)
    (n p : ℕ) (hp : p.Prime) (hpQ : p ≤ Q) (hpn : p ∣ n) :
    (if ⌊x⌋₊ < n ∧ n.Prime then ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0) = 0 := by
  classical
  split_ifs with hn
  · have hpeq : p = n := ((Nat.dvd_prime hn.2).mp hpn).resolve_left hp.ne_one
    have hnx : x < (n : ℝ) := Nat.lt_of_floor_lt hn.1
    have hnQ : (n : ℝ) ≤ Q := by exact_mod_cast (hpeq ▸ hpQ)
    linarith
  · rfl

/-- The large prime coefficients absorb a bounded multiple of `x`. -/
private theorem pG_primeWindow_energy (N : ℕ) (hN : 1 ≤ N) {x K : ℝ}
    (hK : K ≤ 4 * x) :
    (∑ n ∈ Icc 1 N, (K + n) * ‖(if ⌊x⌋₊ < n ∧ n.Prime then
      ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0)‖ ^ 2) ≤
      5 * Real.log N * (Real.log N + 7) := by
  classical
  let S := (Icc 1 N).filter (fun n => ⌊x⌋₊ < n ∧ n.Prime)
  have hsq : ∀ n : ℕ,
      ‖(if ⌊x⌋₊ < n ∧ n.Prime then ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0)‖ ^ 2 =
        if ⌊x⌋₊ < n ∧ n.Prime then (Real.log n / n) ^ 2 else 0 := by
    intro n
    by_cases h : ⌊x⌋₊ < n ∧ n.Prime
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast h.2.pos
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
      have hnorm : ‖((Real.log n / (n : ℝ) : ℝ) : ℂ)‖ = Real.log n / n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog0 hn0.le)]
      rw [if_pos h, if_pos h, hnorm]
    · rw [if_neg h, if_neg h]
      simp
  have heq : (∑ n ∈ Icc 1 N, (K + n) * ‖(if ⌊x⌋₊ < n ∧ n.Prime then
      ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0)‖ ^ 2) =
      ∑ n ∈ S, (K + n) * (Real.log n / n) ^ 2 := by
    simp only [hsq, S, mul_ite, mul_zero]
    exact (sum_filter (s := Icc 1 N) (p := fun n => ⌊x⌋₊ < n ∧ n.Prime)
      (f := fun n => (K + n) * (Real.log n / n) ^ 2)).symm
  have hsub : S ⊆ Nat.primesLE N := by
    intro n hn
    obtain ⟨hnN, hnx, hnp⟩ := mem_filter.mp hn
    exact Nat.mem_primesLE.mpr ⟨(mem_Icc.mp hnN).2, hnp⟩
  rw [heq]
  calc
    _ ≤ ∑ n ∈ S, 5 * (Real.log n ^ 2 / n) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnN, hnx, hnp⟩ := mem_filter.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hnp.pos
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnx
      have hKn : K + n ≤ 5 * (n : ℝ) := by linarith
      calc
        _ ≤ (5 * (n : ℝ)) * (Real.log n / n) ^ 2 :=
          mul_le_mul_of_nonneg_right hKn (sq_nonneg _)
        _ = _ := by field_simp
    _ ≤ ∑ n ∈ Nat.primesLE N, 5 * (Real.log n ^ 2 / n) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ = 5 * ∑ n ∈ Nat.primesLE N, Real.log n ^ 2 / n := (mul_sum ..).symm
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (prime_log_sq_div_sum_le N hN)
        (by norm_num : (0 : ℝ) ≤ 5)
      nlinarith

/-- Every fixed prime detector energy is nonnegative. -/
private theorem pG_energy_nonneg {T : ℝ} (hT : 0 ≤ T) (x y : ℝ) :
    0 ≤ ∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2 := by
  apply sum_nonneg
  intro q hq
  apply sum_nonneg
  intro χ hχ
  exact intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _)

/-- The finite rough hybrid estimate before choosing the sieve level. -/
private theorem pG_energy_le_of_prime_hybrid
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ Q : ℕ, 1 ≤ Q →
      ∀ x y L : ℝ, 1 ≤ ⌊y⌋₊ → ⌊T⌋₊ ≤ Q → (Q : ℝ) ≤ x →
        (∀ q ∈ Icc 1 ⌊T⌋₊, L ≤ Real.log ((Q : ℝ) / q)) →
        (Q : ℝ) ^ 2 * T ≤ 4 * x →
        L * (∑ q ∈ Icc 1 ⌊T⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) ≤
          C * Real.log ⌊y⌋₊ * (Real.log ⌊y⌋₊ + 7) := by
  obtain ⟨C, hC, hhybrid⟩ := hprime
  refine ⟨5 * C, by positivity, ?_⟩
  intro T hT Q hQ x y L hy hTQ hQx hL hscale
  let a : ℕ → ℂ := fun n =>
    if ⌊x⌋₊ < n ∧ n.Prime then ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0
  let e : ℕ → ℝ := fun q =>
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ∫ v in (-T)..T, ‖characterPolynomial χ a ⌊y⌋₊ v‖ ^ 2
  have he : ∀ q : ℕ, 0 ≤ e q := by
    intro q
    apply sum_nonneg
    intro χ hχ
    exact intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _)
  have hrough : ∀ n ∈ Icc 1 ⌊y⌋₊, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0 := by
    intro n hn p hp hpQ hpn
    exact pG_primeWindow_rough hQx n p hp hpQ hpn
  have hbound := hhybrid Q hQ T hT ⌊y⌋₊ a hrough
  have hcoeff := pG_primeWindow_energy ⌊y⌋₊ hy hscale
  have hid : (∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) = ∑ q ∈ Icc 1 ⌊T⌋₊, e q := by
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro χ _
    simp only [← pG_charPoly_primeWindow χ x y]
    rfl
  rw [hid, mul_sum]
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊T⌋₊, Real.log ((Q : ℝ) / q) * e q := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hL q hq) (he q)
    _ ≤ ∑ q ∈ Icc 1 Q, Real.log ((Q : ℝ) / q) * e q := by
      apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hTQ)
      intro q hq hqnot
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
      have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hq).2
      exact mul_nonneg (Real.log_nonneg ((le_div_iff₀ hq0).mpr (by simpa using hqQ))) (he q)
    _ ≤ C * ∑ n ∈ Icc 1 ⌊y⌋₊, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := hbound
    _ ≤ C * (5 * Real.log ⌊y⌋₊ * (Real.log ⌊y⌋₊ + 7)) :=
      mul_le_mul_of_nonneg_left hcoeff hC.le
    _ = _ := by ring

/-- Rounding the sieve level `T` squared preserves its scale and weight. -/
private theorem pG_rounded_square_sieve_level {T : ℝ} (hT : 2 ≤ T) :
    1 ≤ ⌈T ^ 2⌉₊ ∧ ⌊T⌋₊ ≤ ⌈T ^ 2⌉₊ ∧
      (⌈T ^ 2⌉₊ : ℝ) ^ 2 * T ≤ 4 * T ^ (5 : ℝ) ∧
      ∀ q ∈ Icc 1 ⌊T⌋₊, Real.log T ≤ Real.log ((⌈T ^ 2⌉₊ : ℝ) / q) := by
  have hT0 : 0 < T := by linarith
  have hlo : T ^ 2 ≤ (⌈T ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈T ^ 2⌉₊ : ℝ) < T ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg _)
  have hsq : T ≤ T ^ 2 := by nlinarith
  have hQ1 : 1 ≤ ⌈T ^ 2⌉₊ := by
    have hh : (1 : ℝ) ≤ ⌈T ^ 2⌉₊ := by linarith
    exact_mod_cast hh
  have hTQ : ⌊T⌋₊ ≤ ⌈T ^ 2⌉₊ := by
    have hh : (⌊T⌋₊ : ℝ) ≤ ⌈T ^ 2⌉₊ := (Nat.floor_le hT0.le).trans (hsq.trans hlo)
    exact_mod_cast hh
  have hhi' : (⌈T ^ 2⌉₊ : ℝ) ≤ 2 * T ^ 2 := by nlinarith
  refine ⟨hQ1, hTQ, ?_, ?_⟩
  · norm_num only [Real.rpow_ofNat]
    have hh := mul_self_le_mul_self (Nat.cast_nonneg ⌈T ^ 2⌉₊) hhi'
    have hh' := mul_le_mul_of_nonneg_right hh hT0.le
    nlinarith
  · intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hqT : (q : ℝ) ≤ T :=
      (show (q : ℝ) ≤ ⌊T⌋₊ by exact_mod_cast (mem_Icc.mp hq).2).trans (Nat.floor_le hT0.le)
    apply Real.log_le_log hT0
    apply (le_div_iff₀ hq0).mpr
    nlinarith

/-- The rough hybrid bound gives energy of order `log T` at every `y`. -/
private theorem pG_energy_log_bound
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ K B : ℝ, 5 ≤ K → 1 < B → ∀ T : ℝ, 2 ≤ T →
      ∀ y : ℝ, T ^ K ≤ y → y ≤ (T ^ K) ^ B →
        (∑ q ∈ Icc 1 ⌊T⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) ≤
          C * (K * B) * (K * B + 7 / Real.log 2) * Real.log T := by
  obtain ⟨C, hC, hfinite⟩ := pG_energy_le_of_prime_hybrid hprime
  refine ⟨C, hC, ?_⟩
  intro K B hK hB T hT y hxy hyy
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hx1 : 1 ≤ T ^ K := Real.one_le_rpow hT1 hK0
  have hx0 : 0 < T ^ K := Real.rpow_pos_of_pos hT0 _
  have hy1 : 1 ≤ y := hx1.trans hxy
  have hN : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff _).mpr hy1
  have hN0 : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast (by omega : 0 < ⌊y⌋₊)
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨hQ1, hTQ, hscale, hweight⟩ := pG_rounded_square_sieve_level hT
  have hQhi : (⌈T ^ 2⌉₊ : ℝ) ≤ 2 * T ^ 2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg T)
    nlinarith
  have hQcube : (⌈T ^ 2⌉₊ : ℝ) ≤ T ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hT (sq_nonneg T)
    nlinarith
  have hQx : (⌈T ^ 2⌉₊ : ℝ) ≤ T ^ K := hQcube.trans (by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show (3 : ℝ) ≤ K by linarith))
  have h5x : T ^ (5 : ℝ) ≤ T ^ K :=
    Real.rpow_le_rpow_of_exponent_le hT1 hK
  have hs : (⌈T ^ 2⌉₊ : ℝ) ^ 2 * T ≤ 4 * T ^ K :=
    hscale.trans (mul_le_mul_of_nonneg_left h5x (by norm_num))
  have hf := hfinite T (by linarith) ⌈T ^ 2⌉₊ hQ1 (T ^ K) y (Real.log T)
    hN hTQ hQx hweight hs
  have hlogN0 : 0 ≤ Real.log ⌊y⌋₊ := Real.log_nonneg (by exact_mod_cast hN)
  have hlogN : Real.log ⌊y⌋₊ ≤ K * B * Real.log T := by
    calc
      _ ≤ Real.log y := Real.log_le_log hN0 (Nat.floor_le (by linarith))
      _ ≤ Real.log ((T ^ K) ^ B) := Real.log_le_log (by linarith) hyy
      _ = _ := by rw [Real.log_rpow hx0, Real.log_rpow hT0]; ring
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h7 : (7 : ℝ) ≤ (7 / Real.log 2) * Real.log T := by
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT)
      (show 0 ≤ 7 / Real.log 2 by positivity)
    have heq : (7 / Real.log (2 : ℝ)) * Real.log 2 = 7 := by field_simp
    linarith
  have hlogN7 : Real.log ⌊y⌋₊ + 7 ≤ (K * B + 7 / Real.log 2) * Real.log T := by nlinarith
  have hm := mul_le_mul hlogN hlogN7 (by linarith : 0 ≤ Real.log ⌊y⌋₊ + 7)
    (show 0 ≤ K * B * Real.log T by positivity)
  have hh := hf.trans (by
    have ht := mul_le_mul_of_nonneg_left hm hC.le
    convert ht using 1; ring)
  apply (mul_le_mul_iff_left₀ hl).mp
  convert hh using 1 <;> ring

/-- The detector energy is measurable as a function of the prime window endpoint. -/
private theorem pG_measurable_energy (T x : ℝ) :
    Measurable (fun y : ℝ => ∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) := by
  have heq : (fun y : ℝ => ∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ x (⌊y⌋₊ : ℝ) v‖ ^ 2) =
      (fun y : ℝ => ∑ q ∈ Icc 1 ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) := by
    funext y
    simp only [primeDetector, Nat.floor_natCast]
  rw [← heq]
  exact (measurable_of_countable (fun n : ℕ => ∑ q ∈ Icc 1 ⌊T⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ∫ v in (-T)..T, ‖primeDetector χ x (n : ℝ) v‖ ^ 2)).comp Nat.measurable_floor

/-- Joint measurability for the height and prime endpoint integrations. -/
private theorem pG_measurable_primeDetector_uncurry {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) : Measurable (fun z : ℝ × ℝ => primeDetector χ x z.1 z.2) := by
  have hm : Measurable (fun z : ℕ × ℝ =>
      characterPolynomial χ (fun n =>
        if ⌊x⌋₊ < n ∧ n.Prime then ((Real.log n / (n : ℝ) : ℝ) : ℂ) else 0) z.1 z.2) :=
    measurable_from_prod_countable_right
      (fun N => (continuous_characterPolynomial χ _ N).measurable)
  have hg : Measurable (fun z : ℝ × ℝ => (⌊z.1⌋₊, z.2)) :=
    (Nat.measurable_floor.comp measurable_fst).prodMk measurable_snd
  simpa only [Function.comp_def, pG_charPoly_primeWindow] using hm.comp hg

/-- The rough hybrid bound at sieve level `T` squared gives a logarithmic square bound
for the averaged detector energy. -/
private theorem pG_integrated_energy_of_prime_hybrid
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∀ K B : ℝ, 5 ≤ K → 1 < B → ∃ H : ℝ, 0 ≤ H ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ y in (T ^ K)..((T ^ K) ^ B),
        (∑ q ∈ Icc 1 ⌊T⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) ≤
        H * Real.log T ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ := pG_energy_log_bound hprime
  intro K B hK hB
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hBm0 : 0 ≤ B - 1 := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let M : ℝ := C * (K * B) * (K * B + 7 / Real.log 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M * (B - 1) * K, by positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hx1 : 1 ≤ T ^ K := Real.one_le_rpow (by linarith) (by linarith)
  have hx0 : 0 < T ^ K := Real.rpow_pos_of_pos hT0 _
  have hxy : T ^ K ≤ (T ^ K) ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  have hg : Measurable (fun y : ℝ => (∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) :=
    (pG_measurable_energy T (T ^ K)).div measurable_id
  have hi : IntegrableOn (fun y : ℝ => (∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y)
      (Set.Icc (T ^ K) ((T ^ K) ^ B)) := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hg.aestronglyMeasurable
      (M * Real.log T)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hy1 : 1 ≤ y := hx1.trans hy.1
    have hen : 0 ≤ ∑ q ∈ Icc 1 ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2 :=
      pG_energy_nonneg (by linarith) _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hen (by linarith))]
    have hh : (∑ q ∈ Icc 1 ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) ≤ M * Real.log T :=
      hpoint K B hK hB T hT y hy.1 hy.2
    exact (div_le_self hen hy1).trans hh
  have hm : IntegrableOn (fun y : ℝ => M * Real.log T / y)
      (Set.Icc (T ^ K) ((T ^ K) ^ B)) := by
    exact (continuousOn_const.div continuousOn_id
      (by intro y hy; exact (hx0.trans_le hy.1).ne')).integrableOn_Icc
  have hh := intervalIntegral.integral_mono_on hxy
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hi)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hm)
    (fun y hy => div_le_div_of_nonneg_right (hpoint K B hK hB T hT y hy.1 hy.2)
      (hx0.trans_le hy.1).le)
  calc
    _ ≤ ∫ y in (T ^ K)..((T ^ K) ^ B), M * Real.log T / y := hh
    _ = (M * (B - 1) * K) * Real.log T ^ 2 := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      have he := logarithmic_window_mass hx0 B
      simp only [one_div] at he
      rw [he, Real.log_rpow hT0]
      ring

end PortGallagherEnergy



section PortGallagherCounting

open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
open Finset MeasureTheory Complex
open scoped Classical

/-! ## Port of Decomp307b and Decomp340b: the p.336 integrated counting step -/

/-- Local detection and a local occupancy bound imply a global finite count. -/
private theorem pG_finite_height_count_from_local_detector {ι : Type*} (S : Finset ι)
    (height : ι → ℝ) {T r H L : ℝ} (hr : 0 < r) (hrT : r ≤ T)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hheight : ∀ i ∈ S, height i ∈ Set.Icc (-T) T)
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc (-T) T))
    (hg0 : ∀ v ∈ Set.Icc (-T) T, 0 ≤ g v)
    (hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ i ∈ S, (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v) ≤ L)
    (hdetect : ∀ i ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (height i - r) (height i + r) → H ≤ g v) :
    (S.card : ℝ) * r * H ≤ L * ∫ v in Set.Icc (-T) T, g v := by
  classical
  apply Decomp1532b2.finite_height_cover_bound S height hr.le hrT hH hheight g hg
  intro v hv
  by_cases hh : ∃ i ∈ S, v ∈ Set.Icc (height i - r) (height i + r)
  · obtain ⟨i, hi, hvi⟩ := hh
    calc
      _ ≤ H * L := mul_le_mul_of_nonneg_left (hlocal v hv) hH
      _ ≤ L * g v := by nlinarith [mul_le_mul_of_nonneg_right (hdetect i hi v hv hvi) hL]
  · have hzero : (∑ i ∈ S,
        (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v) = 0 := by
      apply sum_eq_zero
      intro i hi
      exact Set.indicator_of_notMem (fun hvi => hh ⟨i, hi, hvi⟩) _
    rw [hzero, mul_zero]
    exact mul_nonneg hL (hg0 v hv)

/-- Every natural power of a prime detector norm is integrable in the endpoint with
logarithmic weight on a compact positive interval. -/
private theorem pG_integrableOn_primeDetector_norm_pow_div {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x v : ℝ) (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => ‖primeDetector χ x y v‖ ^ k / y) (Set.Icc a b) := by
  simpa only [primeDetector, Nat.floor_natCast] using
    pG_integrableOn_floor_div
      (fun n : ℕ => ‖primeDetector χ x (n : ℝ) v‖ ^ k) (y := b) ha

/-- A supplied logarithmic L1 lower bound gives a squared detector lower bound. -/
private theorem pG_primeDetector_logarithmic_l2_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x B H : ℝ} (hx : 1 < x) (hB : 1 < B) (v : ℝ) (hH : 0 ≤ H)
    (hlower : H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    H ^ 2 / ((B - 1) * Real.log x) ≤
      ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ ^ 2 / y := by
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  have hmass : (∫ y in Set.Icc x (x ^ B), (1 : ℝ) / y) =
      (B - 1) * Real.log x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
    exact logarithmic_window_mass hx0 B
  have hw : ∀ᵐ y ∂volume.restrict (Set.Icc x (x ^ B)), 0 ≤ (1 : ℝ) / y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact div_nonneg (by norm_num) (hx0.trans_le hy.1).le
  have hwi : IntegrableOn (fun y : ℝ => (1 : ℝ) / y) (Set.Icc x (x ^ B)) := by
    exact (continuousOn_const.div continuousOn_id
      (by intro y hy; exact (hx0.trans_le hy.1).ne')).integrableOn_Icc
  have hfi : IntegrableOn (fun y : ℝ => ‖primeDetector χ x y v‖ * (1 / y))
      (Set.Icc x (x ^ B)) := by
    simpa only [pow_one, div_eq_mul_inv, one_mul] using
      pG_integrableOn_primeDetector_norm_pow_div χ x v 1 hx0
  have hf2i : IntegrableOn (fun y : ℝ => ‖primeDetector χ x y v‖ ^ 2 * (1 / y))
      (Set.Icc x (x ^ B)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      pG_integrableOn_primeDetector_norm_pow_div χ x v 2 hx0
  have hlower' : H ≤ ∫ y in Set.Icc x (x ^ B), ‖primeDetector χ x y v‖ * (1 / y) := by
    simpa only [div_eq_mul_inv, one_mul, intervalIntegral.integral_of_le hxy,
      integral_Icc_eq_integral_Ioc] using hlower
  have hh := detector_l2_of_l1 (volume.restrict (Set.Icc x (x ^ B)))
    (fun y => ‖primeDetector χ x y v‖) (fun y => 1 / y) hw hwi hfi hf2i
    (by rw [hmass]; exact mul_pos (by linarith) (Real.log_pos hx)) hH hlower'
  rw [hmass] at hh
  simpa only [div_eq_mul_inv, one_mul, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hxy] using hh

/-- The squared prime detector with logarithmic endpoint weight is integrable on each
compact endpoint and height rectangle with positive endpoint lower bound. -/
private theorem pG_integrableOn_primeDetector_energy_rectangle {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) {a b U V : ℝ} (ha : 0 < a) :
    IntegrableOn (fun z : ℝ × ℝ => ‖primeDetector χ x z.1 z.2‖ ^ 2 / z.1)
      (Set.Icc a b ×ˢ Set.Icc U V) := by
  let M : ℝ := ∑ n ∈ Icc 1 ⌊b⌋₊, ‖(Real.log n / (n : ℝ) : ℂ)‖
  have hbound (y v : ℝ) (hy : y ≤ b) : ‖primeDetector χ x y v‖ ≤ M := by
    unfold primeDetector
    calc
      _ ≤ ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ‖(Real.log n / (n : ℝ) : ℂ) * χ n *
            Complex.exp (-((Real.log n * v : ℝ) : ℂ) * I)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ‖(Real.log n / (n : ℝ) : ℂ)‖ := by
        apply sum_le_sum
        intro n hn
        have he : ‖Complex.exp (-((Real.log n * v : ℝ) : ℂ) * I)‖ = 1 := by
          rw [Complex.norm_exp]
          norm_num only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, mul_one, sub_zero, neg_zero, Real.exp_zero]
        rw [norm_mul, norm_mul, he, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      _ ≤ M := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn, hp⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
            (mem_Ioc.mp hn).2.trans (Nat.floor_le_floor hy)⟩
        · intro n _ _
          exact norm_nonneg _
  have hm : Measurable (fun z : ℝ × ℝ => ‖primeDetector χ x z.1 z.2‖ ^ 2 / z.1) :=
    ((pG_measurable_primeDetector_uncurry χ x).norm.pow_const 2).div measurable_fst
  apply IntegrableOn.of_bound (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    hm.aestronglyMeasurable (M ^ 2 / a)
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
  have hz0 : 0 < z.1 := ha.trans_le hz.1.1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hz0.le)]
  exact (div_le_div_of_nonneg_left (sq_nonneg _) ha hz.1.1).trans
    (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hbound z.1 z.2 hz.1.2) 2) ha.le)

/-- The endpoint and height integrations in the detector energy commute. -/
private theorem pG_primeDetector_energy_swap {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    {a b U V : ℝ} (ha : 0 < a) (hab : a ≤ b) (hUV : U ≤ V) :
    (∫ v in U..V, ∫ y in a..b, ‖primeDetector χ x y v‖ ^ 2 / y) =
      ∫ y in a..b, (∫ v in U..V, ‖primeDetector χ x y v‖ ^ 2) / y := by
  have hi : IntegrableOn
      (Function.uncurry (fun y v : ℝ => ‖primeDetector χ x y v‖ ^ 2 / y))
      (Set.uIoc a b ×ˢ Set.uIoc U V) := by
    apply (pG_integrableOn_primeDetector_energy_rectangle χ x ha).mono_set
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le hUV]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  simpa only [intervalIntegral.integral_div] using
    (intervalIntegral_intervalIntegral_swap hi).symm

/-- The logarithmically weighted squared detector integral is integrable as a function
of height on each compact height interval. -/
private theorem pG_integrableOn_primeDetector_height_energy {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) {a b U V : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun v : ℝ => ∫ y in a..b, ‖primeDetector χ x y v‖ ^ 2 / y)
      (Set.Icc U V) := by
  have hi := pG_integrableOn_primeDetector_energy_rectangle χ x (U := U) (V := V) (b := b) ha
  have hp : Integrable (fun z : ℝ × ℝ => ‖primeDetector χ x z.1 z.2‖ ^ 2 / z.1)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc U V))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hi
  simpa only [IntegrableOn, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab] using hp.integral_prod_right

/-- A finite height family with local occupancy and logarithmic L1 detection is
controlled by the averaged squared prime detector energy. -/
private theorem pG_finite_height_count_from_log_detector {ι : Type*} (S : Finset ι)
    (height : ι → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {T r x B H L : ℝ} (hr : 0 < r) (hrT : r ≤ T)
    (hx : 1 < x) (hB : 1 < B) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hheight : ∀ i ∈ S, height i ∈ Set.Icc (-T) T)
    (hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ i ∈ S, (Set.Icc (height i - r) (height i + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ L)
    (hdetect : ∀ i ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (height i - r) (height i + r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    (S.card : ℝ) * r * H ^ 2 ≤ L * ((B - 1) * Real.log x) *
      (∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y) := by
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  have hTT : -T ≤ T := by linarith
  have hmass : 0 < (B - 1) * Real.log x :=
    mul_pos (by linarith) (Real.log_pos hx)
  let g : ℝ → ℝ := fun v => ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ ^ 2 / y
  have hg : IntegrableOn g (Set.Icc (-T) T) :=
    pG_integrableOn_primeDetector_height_energy χ x hx0 hxy
  have hg0 : ∀ v ∈ Set.Icc (-T) T, 0 ≤ g v := by
    intro v hv
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg (sq_nonneg _) (hx0.trans_le hy.1).le
  have hd : ∀ i ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (height i - r) (height i + r) →
      H ^ 2 / ((B - 1) * Real.log x) ≤ g v := by
    intro i hi v hv hvi
    exact pG_primeDetector_logarithmic_l2_lower χ hx hB v hH (hdetect i hi v hv hvi)
  have hh := pG_finite_height_count_from_local_detector S height hr hrT
    (div_nonneg (sq_nonneg H) hmass.le) hL hheight g hg hg0 hlocal hd
  have hh' : ((S.card : ℝ) * r * H ^ 2) / ((B - 1) * Real.log x) ≤
      L * ∫ v in Set.Icc (-T) T, g v := by
    convert hh using 1 <;> ring
  have hmul := (div_le_iff₀ hmass).mp hh'
  calc
    _ ≤ (L * ∫ v in Set.Icc (-T) T, g v) * ((B - 1) * Real.log x) := hmul
    _ = L * ((B - 1) * Real.log x) * (∫ v in (-T)..T, g v) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTT]
      ring
    _ = _ := by rw [pG_primeDetector_energy_swap χ x hx0 hxy hTT]

/-- A fixed nonprincipal primitive character in a narrow strip satisfies the integrated
count bound once its local L1 detector lower bound is supplied. -/
private theorem pG_nonprincipal_zero_count_from_local_l1 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      ∀ x B r H : ℝ, 1 < x → 1 < B → 0 < r →
      1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 → 0 ≤ H →
      (∀ v : ℝ, |v| ≤ T →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
        H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) →
      (zeroCount χ (1 - r) T : ℝ) * H ^ 2 ≤
        C * Real.log T * ((B - 1) * Real.log x) *
          (∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y) := by
  obtain ⟨C, hC, hocc⟩ := pG_primitive_height_window_occupancy
  refine ⟨C, hC, ?_⟩
  intro T hT q hq hqT χ hp hχ x B r H hx hB hr hrlo hrhi hH hdetect
  obtain ⟨S, hS, hcard⟩ := pG_exists_zeroCount_finset χ hp
    (show 1 / 2 ≤ 1 - r by linarith) (show 0 ≤ T by linarith)
  have hstrip (ρ : ℂ) (hρ : ρ ∈ S) :
      χ.LFunction ρ = 0 ∧ 1 - r ≤ ρ.re ∧ ρ.re ≤ 1 := by
    obtain ⟨hz, hβ, hγ⟩ := (hS ρ).mp hρ
    refine ⟨hz, hβ, le_of_lt ?_⟩
    by_contra hn
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hz
  have hheight : ∀ ρ ∈ S, ρ.im ∈ Set.Icc (-T) T := by
    intro ρ hρ
    exact abs_le.mp ((hS ρ).mp hρ).2.2
  have hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ C * r * Real.log T := by
    intro v hv
    exact hocc T hT q hqT χ hp v r (abs_le.mpr hv)
      (fun he => (hχ he).elim) hrlo hrhi S hstrip
  have hd : ∀ ρ ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (ρ.im - r) (ρ.im + r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
    intro ρ hρ v hv hρv
    obtain ⟨hz, hβlo, hβhi⟩ := hstrip ρ hρ
    apply hdetect v (abs_le.mpr hv)
    refine ⟨ρ, hz, ?_⟩
    have hre : |ρ.re - 1| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hρv.2], by linarith [hρv.1]⟩
    calc
      _ ≤ |(ρ - (1 + I * v)).re| + |(ρ - (1 + I * v)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 1| + |ρ.im - v| := by simp
      _ ≤ _ := by linarith
  have hh := pG_finite_height_count_from_log_detector S (fun ρ => ρ.im) χ hr
    (show r ≤ T by linarith) hx hB hH
    (mul_nonneg (mul_nonneg hC hr.le) (Real.log_nonneg (by linarith))) hheight hlocal hd
  rw [hcard] at hh
  apply (mul_le_mul_iff_left₀ hr).mp
  convert hh using 1 <;> ring

/-- Principal zeros above absolute height three satisfy the same finite integrated
counting estimate. -/
private theorem pG_principal_high_count_from_local_l1 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T x B r H : ℝ, 2 ≤ T → 1 < x → 1 < B → 0 < r →
      1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 → 0 ≤ H →
      ∀ S : Finset ℂ,
      (∀ ρ ∈ S, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
        1 - r ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 3 ≤ |ρ.im| ∧ |ρ.im| ≤ T) →
      (∀ v : ℝ, |v| ≤ T → 2 ≤ |v| →
        (∃ ρ : ℂ, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
          ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
        H ≤ ∫ y in x..(x ^ B), ‖primeDetector (1 : DirichletCharacter ℂ 1) x y v‖ / y) →
      (S.card : ℝ) * H ^ 2 ≤ C * Real.log T * ((B - 1) * Real.log x) *
        (∫ y in x..(x ^ B),
          (∫ v in (-T)..T, ‖primeDetector (1 : DirichletCharacter ℂ 1) x y v‖ ^ 2) / y) := by
  obtain ⟨C, hC, hocc⟩ := pG_primitive_height_window_occupancy
  refine ⟨C, hC, ?_⟩
  intro T x B r H hT hx hB hr hrlo hrhi hH S hS hdetect
  have hstrip : ∀ ρ ∈ S, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
      1 - r ≤ ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    obtain ⟨hz, hlo, hhi, h3, hγ⟩ := hS ρ hρ
    exact ⟨hz, hlo, hhi⟩
  have hheight : ∀ ρ ∈ S, ρ.im ∈ Set.Icc (-T) T := by
    intro ρ hρ
    exact abs_le.mp (hS ρ hρ).2.2.2.2
  have hvlarge (ρ : ℂ) (hρ : ρ ∈ S) (v : ℝ)
      (hvρ : v ∈ Set.Icc (ρ.im - r) (ρ.im + r)) : 2 ≤ |v| := by
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hvρ.2], by linarith [hvρ.1]⟩
    have htri : |ρ.im| ≤ |ρ.im - v| + |v| := by
      simpa only [sub_add_cancel] using abs_add_le (ρ.im - v) v
    have h3 := (hS ρ hρ).2.2.2.1
    linarith
  have hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ C * r * Real.log T := by
    intro v hv
    by_cases hex : ∃ ρ ∈ S, v ∈ Set.Icc (ρ.im - r) (ρ.im + r)
    · obtain ⟨ρ, hρ, hvρ⟩ := hex
      exact hocc T hT 1 (by norm_num; linarith) 1 DirichletCharacter.isPrimitive_one_level_one
        v r (abs_le.mpr hv) (fun _ => hvlarge ρ hρ v hvρ) hrlo hrhi S hstrip
    · have hz : (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
          (fun _ => (1 : ℝ)) v) = 0 := by
        apply sum_eq_zero
        intro ρ hρ
        exact Set.indicator_of_notMem (fun hvρ => hex ⟨ρ, hρ, hvρ⟩) _
      rw [hz]
      exact mul_nonneg (mul_nonneg hC hr.le) (Real.log_nonneg (by linarith))
  have hd : ∀ ρ ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (ρ.im - r) (ρ.im + r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector (1 : DirichletCharacter ℂ 1) x y v‖ / y := by
    intro ρ hρ v hv hvρ
    obtain ⟨hz, hlo, hhi⟩ := hstrip ρ hρ
    apply hdetect v (abs_le.mpr hv) (hvlarge ρ hρ v hvρ)
    refine ⟨ρ, hz, ?_⟩
    have hre : |ρ.re - 1| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hvρ.2], by linarith [hvρ.1]⟩
    calc
      _ ≤ |(ρ - (1 + I * v)).re| + |(ρ - (1 + I * v)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 1| + |ρ.im - v| := by simp
      _ ≤ _ := by linarith
  have hh := pG_finite_height_count_from_log_detector S (fun ρ => ρ.im)
    (1 : DirichletCharacter ℂ 1) hr (show r ≤ T by linarith) hx hB hH
    (mul_nonneg (mul_nonneg hC hr.le) (Real.log_nonneg (by linarith))) hheight hlocal hd
  apply (mul_le_mul_iff_left₀ hr).mp
  convert hh using 1 <;> ring

/-- Fixed character counting with the bounded principal low height term retained at
modulus one. -/
private theorem pG_primitive_count_from_local_l1 : ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ x B r H σ : ℝ, 1 < x → 1 < B → 0 < r →
    1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 → 0 ≤ H → 1 - r ≤ σ →
    (∀ v : ℝ, |v| ≤ T → (χ = 1 → 2 ≤ |v|) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) →
    (zeroCount χ σ T : ℝ) * H ^ 2 ≤ (if q = 1 then D else 0) * H ^ 2 +
      A * Real.log T * ((B - 1) * Real.log x) *
        (∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y) := by
  obtain ⟨Aₙ, hAₙ, hnp⟩ := pG_nonprincipal_zero_count_from_local_l1
  obtain ⟨Aₚ, hAₚ, hpr⟩ := pG_principal_high_count_from_local_l1
  obtain ⟨D, hD, hlow⟩ := pG_principal_low_height_zero_count
  refine ⟨max Aₙ Aₚ, D, le_max_of_le_left hAₙ, hD, ?_⟩
  intro T hT q hq hqT χ hp x B r H σ hx hB hr hrlo hrhi hH hσ hdetect
  have hσr : 1 / 2 ≤ 1 - r := by linarith
  have hσ0 : 1 / 2 ≤ σ := hσr.trans hσ
  have hT0 : 0 ≤ T := by linarith
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x ^ B := by simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  let E : ℝ := ∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y
  have hE : 0 ≤ E := by
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg
      (intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _))
      (hx0.trans_le hy.1).le
  have hcoef : 0 ≤ Real.log T * ((B - 1) * Real.log x) * E :=
    mul_nonneg (mul_nonneg (Real.log_nonneg (by linarith))
      (mul_nonneg (by linarith) (Real.log_pos hx).le)) hE
  have hAn : Aₙ * Real.log T * ((B - 1) * Real.log x) * E ≤
      max Aₙ Aₚ * Real.log T * ((B - 1) * Real.log x) * E := by
    convert mul_le_mul_of_nonneg_right (le_max_left Aₙ Aₚ) hcoef using 1 <;> ring
  have hAp : Aₚ * Real.log T * ((B - 1) * Real.log x) * E ≤
      max Aₙ Aₚ * Real.log T * ((B - 1) * Real.log x) * E := by
    convert mul_le_mul_of_nonneg_right (le_max_right Aₙ Aₚ) hcoef using 1 <;> ring
  by_cases hq1 : q = 1
  · subst q
    have heχ : χ = 1 := Subsingleton.elim _ _
    subst χ
    obtain ⟨S, hS, hcard⟩ := pG_exists_zeroCount_finset (1 : DirichletCharacter ℂ 1) hp hσ0 hT0
    let Sh := S.filter (fun ρ => 3 ≤ |ρ.im|)
    let Sl := S.filter (fun ρ => |ρ.im| ≤ 3)
    have hsub : S ⊆ Sh ∪ Sl := by
      intro ρ hρ
      by_cases hh : 3 ≤ |ρ.im|
      · exact mem_union_left _ (mem_filter.mpr ⟨hρ, hh⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hρ, (lt_of_not_ge hh).le⟩)
    have hcardle : (S.card : ℝ) ≤ (Sh.card : ℝ) + Sl.card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le Sh Sl)
    obtain ⟨S₃, hS₃, hc₃⟩ := pG_exists_zeroCount_finset (1 : DirichletCharacter ℂ 1) hp hσ0
      (by norm_num : (0 : ℝ) ≤ 3)
    have hSl : Sl ⊆ S₃ := by
      intro ρ hρ
      obtain ⟨hρS, hρ3⟩ := mem_filter.mp hρ
      obtain ⟨hz, hβ, hγ⟩ := (hS ρ).mp hρS
      exact (hS₃ ρ).mpr ⟨hz, hβ, hρ3⟩
    have hlowcard : (Sl.card : ℝ) ≤ D := by
      have hh : (Sl.card : ℝ) ≤ zeroCount (1 : DirichletCharacter ℂ 1) σ 3 := by
        rw [← hc₃]
        exact_mod_cast card_le_card hSl
      exact hh.trans (hlow σ hσ0)
    have hmem : ∀ ρ ∈ Sh, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
        1 - r ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 3 ≤ |ρ.im| ∧ |ρ.im| ≤ T := by
      intro ρ hρ
      obtain ⟨hρS, h3⟩ := mem_filter.mp hρ
      obtain ⟨hz, hβ, hγ⟩ := (hS ρ).mp hρS
      refine ⟨hz, hσ.trans hβ, ?_, h3, hγ⟩
      by_contra hn
      rw [DirichletCharacter.LFunction_modOne_eq] at hz
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_ge hn) hz
    have hh := hpr T x B r H hT hx hB hr hrlo hrhi hH Sh hmem
      (fun v hv hv2 hz => hdetect v hv (fun _ => hv2) hz)
    change (zeroCount (1 : DirichletCharacter ℂ 1) σ T : ℝ) * H ^ 2 ≤ D * H ^ 2 +
      max Aₙ Aₚ * Real.log T * ((B - 1) * Real.log x) * E
    rw [← hcard]
    have hh' := hh.trans hAp
    have hm := mul_le_mul_of_nonneg_right hcardle (sq_nonneg H)
    have hlm := mul_le_mul_of_nonneg_right hlowcard (sq_nonneg H)
    nlinarith
  · have hχ : χ ≠ 1 := by
      intro he
      apply hq1
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, he, DirichletCharacter.conductor_one] at hh
      exact hh.symm
    obtain ⟨S₀, hS₀, hc₀⟩ := pG_exists_zeroCount_finset χ hp hσr hT0
    have hsub : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} ⊆ (S₀ : Set ℂ) := by
      intro ρ hρ
      exact (hS₀ ρ).mpr ⟨hρ.1, hσ.trans hρ.2.1, hρ.2.2⟩
    have hmono : (zeroCount χ σ T : ℝ) ≤ zeroCount χ (1 - r) T := by
      have hh := Set.ncard_le_ncard hsub S₀.finite_toSet
      rw [Set.ncard_coe_finset, hc₀] at hh
      exact_mod_cast hh
    have hh := hnp T hT q hqT χ hp hχ x B r H hx hB hr hrlo hrhi hH
      (fun v hv hz => hdetect v hv (fun he => (hχ he).elim) hz)
    simp only [hq1, ite_false, zero_mul, zero_add]
    exact (mul_le_mul_of_nonneg_right hmono (sq_nonneg H)).trans (hh.trans hAn)

end PortGallagherCounting



section PortGallagherAssembly

open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
open Finset MeasureTheory Complex
open scoped Classical

/-- The finite primitive character sum can be moved through the endpoint integral. -/
private theorem pG_integral_energy_eq_sum (T a : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∫ u in x..y, (∑ q ∈ Icc 1 ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u) =
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          ∫ u in x..y, (∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u := by
  have hid (u : ℝ) : (∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) =
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2 := by
    symm
    apply sum_bij (fun q _ => q + 1)
    · intro q hq
      have hh := mem_range.mp hq
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro q hq q' hq' he
      omega
    · intro q hq
      have hh := mem_Icc.mp hq
      exact ⟨q - 1, mem_range.mpr (by omega), by omega⟩
    · intro q hq
      rfl
  have hi {q : ℕ} (χ : DirichletCharacter ℂ q) :
      IntervalIntegrable (fun u : ℝ => (∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u)
        volume x y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
    simpa only [primeDetector, Nat.floor_natCast] using
      pG_integrableOn_floor_div
        (fun n : ℕ => ∫ v in (-T)..T, ‖primeDetector χ a (n : ℝ) v‖ ^ 2) (y := y) hx
  simp_rw [hid, sum_div]
  have hiq (q : ℕ) : IntervalIntegrable
      (fun u : ℝ => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter
        (fun χ => χ.IsPrimitive), (∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u)
      volume x y := by
    convert IntervalIntegrable.sum
      ((univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive))
      (fun χ hχ => hi χ) using 1
    ext u
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum (fun q hq => hiq q)]
  apply sum_congr rfl
  intro q hq
  exact intervalIntegral.integral_finsetSum (fun χ hχ => hi χ)

/-- The fixed character integrated counting inequality before display 25 at large `T`
and a fixed narrow strip, retaining the bounded principal low height term at modulus one. -/
private theorem pG_fixed_character_narrow_count_from_detector
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    ∃ K B c C D η T₀ : ℝ,
      5 ≤ K ∧ 1 < B ∧ 0 < c ∧ 0 ≤ C ∧ 0 ≤ D ∧
      0 < η ∧ η ≤ 1 / 16 ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 - η ≤ σ → σ < 1 →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        (zeroCount χ σ T : ℝ) ≤ (if q = 1 then D else 0) +
          C * T ^ (c * (1 - σ)) *
            (∫ y in (T ^ K)..((T ^ K) ^ B),
              (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
            Real.log T ^ 2 := by
  obtain ⟨r₀, A, B, C₀, c₀, hr₀, hr₀hi, hA, hB, hC₀, hc₀, hdet⟩ := hdetector
  obtain ⟨M, D, hM, hD, hcount⟩ := pG_primitive_count_from_local_l1
  let K : ℝ := max A 5
  let η : ℝ := min (r₀ / 2) (1 / 16)
  let T₀ : ℝ := Real.exp (1 / η)
  let C : ℝ := M * (B - 1) / (c₀ ^ 2 * K ^ 3) * Real.exp (2 * C₀ * K)
  have hK : 5 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηhi : η ≤ 1 / 16 := min_le_right _ _
  have hηr : η ≤ r₀ / 2 := min_le_left _ _
  have hηinv : (1 : ℝ) ≤ 1 / η := by
    apply (le_div_iff₀ hη).mpr
    linarith
  have hT₀ : 2 ≤ T₀ := by
    dsimp [T₀]
    linarith [Real.add_one_le_exp (1 / η)]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K, B, 4 * C₀ * K, C, D, η, T₀, hK, hB, by positivity, hC,
    hD, hη, hηhi, hT₀, ?_⟩
  intro T hlarge σ hσn hσ1 q hq hqT χ hp
  have hT : 2 ≤ T := hT₀.trans hlarge
  have hT0 : 0 < T := by linarith
  let l : ℝ := Real.log T
  let d : ℝ := 1 - σ
  let p : ℝ := 1 / (2 * l)
  let r : ℝ := max d p
  let x : ℝ := T ^ K
  let H : ℝ := c₀ * Real.exp (-2 * C₀ * K * r * l) * (K * l) ^ 2
  let E : ℝ := ∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y
  let N : ℝ := (zeroCount χ σ T : ℝ)
  let Dq : ℝ := if q = 1 then D else 0
  have hl : 0 < l := Real.log_pos (by linarith)
  have hd : 0 < d := by dsimp [d]; linarith
  have hdη : d ≤ η := by dsimp [d]; linarith
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hlogη : 1 / η ≤ l := by
    have hh := Real.log_le_log (Real.exp_pos (1 / η)) hlarge
    simpa only [l, T₀, Real.log_exp] using hh
  have hηl : 1 ≤ l * η := (div_le_iff₀ hη).mp hlogη
  have hpη : p ≤ η := by
    dsimp [p]
    apply (div_le_iff₀ (show 0 < 2 * l by positivity)).mpr
    nlinarith
  have hr : 0 < r := hp0.trans_le (le_max_right _ _)
  have hrη : r ≤ η := max_le hdη hpη
  have hp_id : 2 * p = 1 / l := by dsimp [p]; field_simp
  have hrlo : 1 / Real.log T ≤ 2 * r := by
    change 1 / l ≤ 2 * r
    have hh : p ≤ r := le_max_right _ _
    linarith
  have hrhi : 2 * r ≤ 1 / 8 := by linarith
  have hrr₀ : 2 * r ≤ r₀ := by linarith
  have hrpad : r ≤ d + 1 / (2 * l) := by
    change max d p ≤ d + p
    exact max_le (by linarith) (by linarith)
  have hσr : 1 - r ≤ σ := by
    have hh : d ≤ r := le_max_left _ _
    dsimp [d] at hh
    linarith
  have hx : 1 < x := Real.one_lt_rpow (by linarith) hK0
  have hx0 : 0 < x := by linarith
  have hxA : T ^ A ≤ x :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hlogx : Real.log x = K * l := by
    dsimp [x, l]
    exact Real.log_rpow hT0 K
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hH_eq : H = c₀ * x ^ (-C₀ * (2 * r)) * Real.log x ^ 2 := by
    dsimp [H]
    rw [Real.rpow_def_of_pos hx0, hlogx]
    have he : (K * l) * (-C₀ * (2 * r)) = -2 * C₀ * K * r * l := by ring
    rw [he]
  have hdet' : ∀ v : ℝ, |v| ≤ T → (χ = 1 → 2 ≤ |v|) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
    intro v hv hχ hz
    rw [hH_eq]
    apply hdet T hT q hqT χ v (2 * r) hv hχ hrlo hrr₀
    · obtain ⟨ρ, hρ, hnorm⟩ := hz
      exact ⟨ρ, hρ, by simpa only [mul_comm] using hnorm⟩
    · exact hxA
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  have hE : 0 ≤ E := by
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg (intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _))
      (hx0.trans_le hy.1).le
  change N ≤ Dq + C * T ^ ((4 * C₀ * K) * (1 - σ)) * E / Real.log T ^ 2
  by_cases hsmall : N ≤ Dq
  · exact hsmall.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hT0.le _)) hE) (sq_nonneg _)))
  · have hn : 0 ≤ N - Dq := by linarith
    have hraw := hcount T hT q hqT χ hp x B r H σ hx hB hr hrlo hrhi hH hσr hdet'
    change N * H ^ 2 ≤ Dq * H ^ 2 + M * l * ((B - 1) * Real.log x) * E at hraw
    rw [hlogx] at hraw
    have hraw' : (N - Dq) * (c₀ * Real.exp (-2 * C₀ * K * r * l) * (K * l) ^ 2) ^ 2 ≤
        M * l * ((B - 1) * K * l) * E := by
      change (N - Dq) * H ^ 2 ≤ M * l * ((B - 1) * K * l) * E
      nlinarith only [hraw]
    have hs := pG_detector_count_scale hn hc₀ hC₀.le hK0 hl hrpad hraw'
    have hpow : Real.exp (4 * C₀ * K * d * l) = T ^ ((4 * C₀ * K) * (1 - σ)) := by
      rw [Real.rpow_def_of_pos hT0]
      dsimp [d, l]
      congr 1
      ring
    rw [hpow] at hs
    change N - Dq ≤ C * T ^ ((4 * C₀ * K) * (1 - σ)) * E / Real.log T ^ 2 at hs
    linarith only [hs]

/-- Gallagher 1970 p.336 Theorem 6 counting assembly before display 25. -/
private theorem pG_zero_count_from_integrated_detector
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    ∀ b : ℝ, 0 < b → ∃ K B c C : ℝ, 5 ≤ K ∧ 1 < B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
      (∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ)) ≤
        C * T ^ (c * (1 - σ)) *
          (1 + (∫ y in (T ^ K)..((T ^ K) ^ B),
            (∑ q ∈ Icc 1 ⌊T⌋₊,
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
                ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
            Real.log T ^ 2) := by
  obtain ⟨K, B, c, C, D, η, T₀, hK, hB, hc, hC, hD, hη, hηhi, hT₀, hfixed⟩ :=
    pG_fixed_character_narrow_count_from_detector hdetector
  obtain ⟨P, hP, hpoly⟩ := density_sum_polynomial
  obtain ⟨W, hW, hwide⟩ := density_sum_fixed_gap η hη
  intro b hb
  let c' : ℝ := max c (4 / η)
  let C' : ℝ := D + P * T₀ ^ 4 + W + C
  have hc' : 0 < c' := hc.trans_le (le_max_left _ _)
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨K, B, c', C', hK, hB, hc', hC', ?_⟩
  intro T hT σ hσ hσb
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hσ1 : σ < 1 := by linarith [div_pos hb hl]
  have hδ : 0 ≤ 1 - σ := by linarith
  have hx1 : 1 ≤ T ^ K := Real.one_le_rpow hT1 (by linarith)
  have hx0 : 0 < T ^ K := Real.rpow_pos_of_pos hT0 _
  have hxy : T ^ K ≤ (T ^ K) ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  let E : ℝ := ∫ y in (T ^ K)..((T ^ K) ^ B),
    (∑ q ∈ Icc 1 ⌊T⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y
  let Z : ℝ := E / Real.log T ^ 2
  let N : ℝ := ∑ q ∈ range ⌊T⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
      (zeroCount χ σ T : ℝ)
  change N ≤ C' * T ^ (c' * (1 - σ)) * (1 + Z)
  have hE : 0 ≤ E := by
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg (pG_energy_nonneg hT0.le _ _) (hx0.trans_le hy.1).le
  have hZ : 0 ≤ Z := div_nonneg hE (sq_nonneg _)
  have htp : 1 ≤ T ^ (c' * (1 - σ)) :=
    Real.one_le_rpow hT1 (mul_nonneg hc'.le hδ)
  have htp0 : 0 ≤ T ^ (c' * (1 - σ)) := Real.rpow_nonneg hT0.le _
  have hbase : C' * T ^ (c' * (1 - σ)) ≤
      C' * T ^ (c' * (1 - σ)) * (1 + Z) :=
    le_mul_of_one_le_right (mul_nonneg hC' htp0) (by linarith)
  have hCtp : C' ≤ C' * T ^ (c' * (1 - σ)) := le_mul_of_one_le_right hC' htp
  have hDP : D ≤ C' ∧ P * T₀ ^ 4 ≤ C' ∧ W ≤ C' ∧ C ≤ C' := by
    dsimp [C']
    have hPT : 0 ≤ P * T₀ ^ 4 := mul_nonneg hP (by positivity)
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  by_cases hlarge : T₀ ≤ T
  · by_cases hnarrow : 1 - η ≤ σ
    · have hfloor : 1 ≤ ⌊T⌋₊ := (Nat.one_le_floor_iff _).mpr hT1
      have hzero : 0 ∈ range ⌊T⌋₊ := mem_range.mpr (by omega)
      have hprincipal :
          (∑ q ∈ range ⌊T⌋₊,
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
              (if q + 1 = 1 then D else 0)) ≤ D := by
        rw [sum_eq_single_of_mem 0 hzero]
        · simp only [Nat.zero_add, ite_true]
          have hcard : Fintype.card (DirichletCharacter ℂ 1) = 1 := by
            rw [← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
            norm_num
          calc
            _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ 1)), D :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hD)
            _ = D := by simp [hcard]
        · intro q hq hq0
          have hne : q + 1 ≠ 1 := by omega
          simp only [hne, ite_false, sum_const_zero]
      have hsumE :
          (∑ q ∈ range ⌊T⌋₊,
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
              ∫ y in (T ^ K)..((T ^ K) ^ B),
                (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) = E :=
        (pG_integral_energy_eq_sum T (T ^ K) hx0 hxy).symm
      have hcount : N ≤ D + C * T ^ (c * (1 - σ)) * Z := by
        calc
          N ≤ ∑ q ∈ range ⌊T⌋₊,
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
                ((if q + 1 = 1 then D else 0) + C * T ^ (c * (1 - σ)) *
                  (∫ y in (T ^ K)..((T ^ K) ^ B),
                    (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
                    Real.log T ^ 2) := by
            apply sum_le_sum
            intro q hq
            apply sum_le_sum
            intro χ hχ
            have hqT : ((q + 1 : ℕ) : ℝ) ≤ T :=
              (show ((q + 1 : ℕ) : ℝ) ≤ ⌊T⌋₊ by
                exact_mod_cast (show q + 1 ≤ ⌊T⌋₊ by have := mem_range.mp hq; omega)).trans
                (Nat.floor_le hT0.le)
            exact hfixed T hlarge σ hnarrow hσ1 (q + 1) hqT χ (mem_filter.mp hχ).2
          _ = (∑ q ∈ range ⌊T⌋₊,
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
                (if q + 1 = 1 then D else 0)) +
              C * T ^ (c * (1 - σ)) *
                (∑ q ∈ range ⌊T⌋₊,
                  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter
                    (fun χ => χ.IsPrimitive),
                    ∫ y in (T ^ K)..((T ^ K) ^ B),
                      (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
                        Real.log T ^ 2 := by
            simp only [sum_add_distrib, div_eq_mul_inv, mul_sum, sum_mul, mul_assoc]
          _ ≤ D + C * T ^ (c * (1 - σ)) * Z := by
            rw [hsumE]
            simp only [Z, div_eq_mul_inv, mul_assoc]
            exact add_le_add hprincipal le_rfl
      have hp : T ^ (c * (1 - σ)) ≤ T ^ (c' * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hT1
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ)
      calc
        N ≤ D + C * T ^ (c * (1 - σ)) * Z := hcount
        _ ≤ C' * T ^ (c' * (1 - σ)) + C' * T ^ (c' * (1 - σ)) * Z :=
          add_le_add (hDP.1.trans hCtp)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hDP.2.2.2 hp (Real.rpow_nonneg hT0.le _) hC') hZ)
        _ = _ := by ring
    · have hw : N ≤ W * T ^ ((4 / η) * (1 - σ)) :=
        hwide T hT σ (by linarith) (le_of_not_ge hnarrow)
      have hp : T ^ ((4 / η) * (1 - σ)) ≤ T ^ (c' * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hT1
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ)
      exact hw.trans ((mul_le_mul_of_nonneg_left hp hW).trans
        ((mul_le_mul_of_nonneg_right hDP.2.2.1 htp0).trans hbase))
  · have hpoly' : N ≤ P * T ^ (4 : ℕ) := hpoly T hT σ (by linarith)
    have hp : T ^ (4 : ℕ) ≤ T₀ ^ 4 :=
      pow_le_pow_left₀ hT0.le (lt_of_not_ge hlarge).le 4
    exact hpoly'.trans ((mul_le_mul_of_nonneg_left hp hP).trans
      (hDP.2.1.trans (hCtp.trans hbase)))

end PortGallagherAssembly

/-- LEAF. Gallagher 1970 p.336, passage from Theorem 5 to display 25 and then
Theorem 6 display 24. CONDITIONAL ON the supplied L1 detector and rough hybrid bound.
The remaining proof requires the local zero count from p.333 and the interval covering
and integration argument on p.336, including the bounded principal low height contribution.
The original polynomial region and Page strip are not repeated in this input. -/
theorem gallagher_density_from_detector_and_prime_hybrid
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y)
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  intro b hb
  obtain ⟨K, B, c, C, hK, hB, hc, hC, hcount⟩ :=
    pG_zero_count_from_integrated_detector hdetector b hb
  obtain ⟨H, hH, henergy⟩ := pG_integrated_energy_of_prime_hybrid hprime K B hK hB
  refine ⟨c, C * (1 + H), hc, by positivity, ?_⟩
  intro T hT σ hσ hσb
  have hl : 0 < Real.log T ^ 2 := sq_pos_of_pos (Real.log_pos (by linarith))
  have he : (∫ y in (T ^ K)..((T ^ K) ^ B),
      (∑ q ∈ Icc 1 ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
      Real.log T ^ 2 ≤ H := (div_le_iff₀ hl).mpr (henergy T hT)
  calc
    _ ≤ C * T ^ (c * (1 - σ)) *
        (1 + (∫ y in (T ^ K)..((T ^ K) ^ B),
          (∑ q ∈ Icc 1 ⌊T⌋₊,
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
              ∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
          Real.log T ^ 2) := hcount T hT σ hσ hσb
    _ ≤ C * T ^ (c * (1 - σ)) * (1 + H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring


/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339, Theorem 6. Montgomery and Vaughan 1975 p.366 Section 7.
Gallagher 1975 p.131 display 14. The polynomial range at most three quarters and the
fixed Page strip are proved separately. Only the intervening band remains. -/
theorem gallagher_density_transition : ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  exact gallagher_density_from_detector_and_prime_hybrid
    gallagher_zero_detector gallagher_prime_hybrid_mean_value

/-- Gallagher 1975 p.131. Auxiliary obstruction to removing a logarithmic density loss
uniformly in the band below a Page strip. This is not a counterexample to the density theorem. -/
theorem logarithmic_loss_not_uniformly_absorbable (b : ℝ) (hb : 0 < b) (c C : ℝ) :
    ∃ T σ : ℝ, 2 ≤ T ∧ 3 / 4 < σ ∧ σ < 1 - b / Real.log T ∧
      C * T ^ (c * (1 - σ)) < Real.log T := by
  let x : ℝ := max (max (Real.log 2 + 1) (8 * b + 1))
    (C * Real.exp (2 * b * c) + 1)
  have hxlog : Real.log 2 + 1 ≤ x :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxb : 8 * b + 1 ≤ x :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hxC : C * Real.exp (2 * b * c) + 1 ≤ x := le_max_right _ _
  have hx : 0 < x := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have hbdiv : 0 < b / x := div_pos hb hx
  refine ⟨Real.exp x, 1 - 2 * b / x, ?_, ?_, ?_, ?_⟩
  · calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  · have hsmall : 2 * b / x < 1 / 4 := (div_lt_iff₀ hx).mpr (by nlinarith)
    linarith
  · rw [Real.log_exp, mul_div_assoc]
    linarith
  · rw [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have he : x * (c * (1 - (1 - 2 * b / x))) = 2 * b * c := by
      field_simp
      ring
    rw [he]
    linarith

/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339. Montgomery and Vaughan 1975 Section 7.
Gallagher 1975 p.131 display 14. The primitive family count inside a fixed Page strip
is proved separately. Only zeros strictly below that strip remain in this input. -/
theorem gallagher_density_away_from_one : ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  intro b hb
  obtain ⟨c, C, hc, hC, h⟩ := gallagher_density_transition b hb
  obtain ⟨D, hD, haway⟩ := density_sum_away_from_one
  refine ⟨max c 16, max C D, lt_max_of_lt_left hc,
    hC.trans (le_max_left _ _), fun T hT σ hσ hσb => ?_⟩
  have hσ1 : σ < 1 := by
    have hl : 0 < Real.log T := Real.log_pos (by linarith)
    have := div_pos hb hl
    linarith
  have hp (d : ℝ) (hd : d ≤ max c 16) :
      T ^ (d * (1 - σ)) ≤ T ^ (max c 16 * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith)
      (mul_le_mul_of_nonneg_right hd (by linarith))
  by_cases hs : σ ≤ 3 / 4
  · exact (haway T hT σ hσ hs).trans
      (mul_le_mul (le_max_right C D) (hp 16 (le_max_right c 16)) (by positivity)
        (hD.trans (le_max_right _ _)))
  · exact (h T hT σ (lt_of_not_ge hs) hσb).trans
      (mul_le_mul (le_max_left C D) (hp c (le_max_left c 16)) (by positivity)
        (hC.trans (le_max_left _ _)))

/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339. Montgomery and Vaughan 1975 Section 7.
Gallagher 1975 p.131 display 14.
The endpoint sigma one is proved separately by nonvanishing. -/
theorem gallagher_density_lt_one : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  obtain ⟨b, hb, hpage⟩ := density_sum_in_page_strip
  obtain ⟨c, C, hc, hC, hbound⟩ := gallagher_density_away_from_one b hb
  refine ⟨c, max C 1, hc, (by linarith [le_max_right C (1 : ℝ)]), fun T hT σ hσ hσ1 => ?_⟩
  have hp : 1 ≤ T ^ (c * (1 - σ)) :=
    Real.one_le_rpow (by linarith) (mul_nonneg hc.le (by linarith))
  by_cases hs : σ < 1 - b / Real.log T
  · exact (hbound T hT σ hσ hs).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity))
  · have hh := hpage T hT σ (le_of_not_gt hs)
    apply hh.trans
    have hmul := mul_le_mul (le_max_right C (1 : ℝ)) hp zero_le_one
      (show 0 ≤ max C 1 by linarith [le_max_right C (1 : ℝ)])
    simpa using hmul

/-- LEAF. Unit U-1532. Gallagher's density estimate for zeros near `σ = 1`: for `T ≥ 2` and
`1/2 ≤ σ ≤ 1`, the zeros with `Re ρ ≥ σ`, `|Im ρ| ≤ T` of all `L(s, χ)`, `χ` primitive of
conductor at most `T`, number at most `C T^{c(1-σ)}`; the input to display (14), p. 131, by the
method of §7 of the 1970 large sieve density paper. -/
theorem gallagher_density : ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  classical
  obtain ⟨c, C, hc, hC, h⟩ := gallagher_density_lt_one
  refine ⟨c, C, hc, ?_⟩
  intro T hT σ hσ hσ1
  by_cases hs : σ = 1
  · subst σ
    rw [density_sum_at_one]
    simpa using hC
  · exact h T hT σ hσ (lt_of_le_of_ne hσ1 hs)

/-- LEAF. Unit U-1532. Lemma 6, display (6) p. 134, for g = 2 where `D/φ(D) = 2`: for
`k ≥ 2` and `N ≥ N_k`, `Σ_{n ≠ 0} r_{k,k}(n) 𝔖(n) = 2 L^{2k} (1 + O(log² k / k))`. -/
theorem lemma6 : ∃ C : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ‖∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x) -
        2 * ((Nat.log 2 N : ℕ) : ℂ) ^ (2 * k)‖ ≤
      C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hC, hfinite⟩ := finite_singular_main_bound
  refine ⟨C + 1, fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have ha : 0 < Real.log k ^ 2 / k := div_pos (sq_pos_of_pos hlk) hk0
  obtain ⟨N0, htail⟩ := tuple_truncation_eventually (k := k) (by omega) ha
  refine ⟨max N0 (2 ^ k), fun N hN => ?_⟩
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hNk : 2 ^ k ≤ N := (le_max_right _ _).trans hN
  have ht := htail N hN0
  have hf := hfinite k N hk hNk
  let F : ℂ := ∑ q ∈ Icc 1 ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊,
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)
  calc
    _ ≤ ‖(∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x)) - F‖ +
        ‖F - 2 * (Nat.log 2 N : ℂ) ^ (2 * k)‖ := norm_sub_le_norm_sub_add_norm_sub _ F _
    _ ≤ (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) +
        C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := add_le_add ht hf
    _ = _ := by ring


/-- Gallagher 1970 p.333 local density lemma in the uniform height box.
The count includes multiplicities and retains the principal character height restriction. -/
theorem primitive_local_zero_order_sum : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ t r : ℝ,
      |t| ≤ T → (χ = 1 → 2 ≤ |t|) → 1 / Real.log T ≤ r → r ≤ 1 / 8 →
      ∀ S : Finset ℂ, (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + Complex.I * t)‖ ≤ r) →
      (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * r * Real.log T := by
  obtain ⟨C, hC, hc⟩ := LeanLab.Linnik.Decomp1532b2.local_zero_order_sum_primitive
  obtain ⟨K, hK, hk⟩ := log_Bt_le_log_height
  refine ⟨C * (1 + K), by positivity, ?_⟩
  intro T hT q hq hqT χ hp t r ht hχ hrlo hrhi S hS
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlT).trans_le hrlo
  have hrlog : 1 ≤ r * Real.log T := (div_le_iff₀ hlT).mp hrlo
  have hlog := hk hT hqT ht
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have h := hc q χ hp t r hχ hr hrhi S hS
  apply h.trans
  have hs : 1 + r * Real.log (LeanLab.PNTPort.DirichletZF.Bt q t) ≤
      (1 + K) * r * Real.log T := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hC
  nlinarith

/-- Gallagher 1970 p.336 the bounded principal low height contribution.
A fixed height of three also covers the endpoints used by the local disc argument. -/
theorem principal_low_height_zero_count : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 / 2 ≤ σ →
    (zeroCount (1 : DirichletCharacter ℂ 1) σ 3 : ℝ) ≤ C := by
  obtain ⟨A, hA, h⟩ := zeroCount_le_unit_height
  refine ⟨4 * A * Real.log 5, by positivity, ?_⟩
  intro σ hσ
  have hc := h 1 1 DirichletCharacter.isPrimitive_one_level_one σ 3 hσ (by norm_num)
  convert hc using 1; norm_num

end LeanLab.Linnik.Decomp1532b

open Finset Complex
namespace LeanLab.Linnik.Decomp1532b
/-- Gallagher p.334 finite Turan applied to zeros repeated according to multiplicity. -/
theorem weighted_turan_power_sum {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ι → ℂ)
    {M : ℕ} (hM : (∑ i ∈ S, m i) ≤ M)
    (hz : ∃ i ∈ S, 0 < m i ∧ 1 ≤ ‖z i‖) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧
      (1 / 50 : ℝ) ^ M ≤ ‖∑ i ∈ S, (m i : ℂ) * z i ^ ν‖ := by
  classical
  let I := (i : S) × Fin (m i)
  let Z : I → ℂ := fun i => z i.1
  have hcard : Fintype.card I = ∑ i ∈ S, m i := by simp [I, Fintype.card_sigma, Finset.sum_attach]
  obtain ⟨i, hi, hm, hzi⟩ := hz
  let i₀ : I := ⟨⟨i, hi⟩, ⟨0, hm⟩⟩
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  let e := Fintype.equivFin I
  obtain ⟨ν, hν, hν', hsum⟩ := turan_power_sum_lower_bound hpos
    (by simpa [hcard] using hM) (fun j => Z (e.symm j))
    ⟨e i₀, by simpa [Z, i₀] using hzi⟩
  refine ⟨ν, hν, hν', ?_⟩
  have heq : (∑ j : Fin (Fintype.card I), Z (e.symm j) ^ ν) =
      ∑ i ∈ S, (m i : ℂ) * z i ^ ν := by
    calc
      _ = ∑ i : I, Z i ^ ν := e.symm.sum_comp _
      _ = _ := by
        simp only [I, Z, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Finset.sum_attach S (fun i => (m i : ℂ) * z i ^ ν)
  rwa [heq] at hsum
end LeanLab.Linnik.Decomp1532b

open Finset Complex
namespace LeanLab.Linnik.Decomp1532b
/-- Gallagher p.334 Turan lower bound for a finite reciprocal pole power sum. -/
theorem reciprocal_pole_turan {ι : Type*} (S : Finset ι) (m : ι → ℕ) (ρ : ι → ℂ)
    {M : ℕ} (hM : (∑ i ∈ S, m i) ≤ M) {r : ℝ} (hr : 0 < r) (s : ℂ)
    (hne : ∀ i ∈ S, s - ρ i ≠ 0)
    (hclose : ∃ i ∈ S, 0 < m i ∧ ‖s - ρ i‖ ≤ 2 * r) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧
      1 / (100 * r) ^ ν ≤ ‖∑ i ∈ S, (m i : ℂ) / (s - ρ i) ^ ν‖ := by
  classical
  let z : ι → ℂ := fun i => (2 * r : ℝ) / (s - ρ i)
  have hz : ∃ i ∈ S, 0 < m i ∧ 1 ≤ ‖z i‖ := by
    obtain ⟨i, hi, hm, hc⟩ := hclose
    refine ⟨i, hi, hm, ?_⟩
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      one_le_div (norm_pos_iff.mpr (hne i hi))]
    exact hc
  obtain ⟨ν, hν, hν', hsum⟩ := weighted_turan_power_sum S m z hM hz
  refine ⟨ν, hν, hν', ?_⟩
  have heq : (∑ i ∈ S, (m i : ℂ) * z i ^ ν) =
      ((2 * r : ℝ) : ℂ) ^ ν * ∑ i ∈ S, (m i : ℂ) / (s - ρ i) ^ ν := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    dsimp [z]
    rw [div_pow]
    ring
  rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hsum
  have hp : (1 / 50 : ℝ) ^ ν ≤ (1 / 50 : ℝ) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hν.le
  have hl := hp.trans hsum
  have he : ((1 / 50 : ℝ) ^ ν) / (2 * r) ^ ν = 1 / (100 * r) ^ ν := by
    have hb : (1 / 50 : ℝ) / (2 * r) = 1 / (100 * r) := by field_simp; norm_num
    simpa only [div_pow, one_pow] using congrArg (fun x : ℝ => x ^ ν) hb
  rw [← he]
  exact (div_le_iff₀ (pow_pos (show 0 < 2 * r by positivity) ν)).2 (by simpa only [mul_comm] using hl)
end LeanLab.Linnik.Decomp1532b

open Finset Complex Set Metric
open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b
/-- Gallagher p.334 the large logarithmic derivative step for nonprincipal characters. -/
theorem nonprincipal_large_logDeriv : ∃ E : ℝ, 1 ≤ E ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log (Bt q t) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log (Bt q t) ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) ≤
            ‖iteratedDeriv k (logDeriv (fShift χ t)) ((r : ℂ) - 1 / 2)‖ := by
  obtain ⟨C₀, hC₀, hcount⟩ := local_disc_order_sum_nonprincipal_all_radii
  obtain ⟨C₁, hC₁, hexp⟩ := near_zero_logDeriv_expansion_nonprincipal
  let E : ℝ := max 1 (max (200 * C₀) (200 * C₁))
  have hE : 1 ≤ E := le_max_left _ _
  refine ⟨E, hE, ?_⟩
  intro q hq χ hχ t r hr hrl hscale hroot M hM
  have hlog : 0 ≤ Real.log (Bt q t) := Real.log_nonneg (one_lt_Bt t).le
  have hc : 0 < 200 * r := by positivity
  have hcl : 200 * r ≤ 1 / 8 := by linarith
  have hscale' : 1 ≤ (200 * r) * Real.log (Bt q t) := by nlinarith
  let S := (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ 200 * r)
  let m : ℂ → ℕ := fun ρ => analyticOrderNatAt (fShift χ t) ρ
  let s : ℂ := (r : ℂ) - 1 / 2
  have hMcount : (∑ ρ ∈ S, m ρ) ≤ M := by
    have hc₀ : 200 * C₀ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
    have hbound := hcount q χ hχ t (200 * r) hc hscale'
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀ hr.le) hlog
    have hcast : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ M := hbound.trans (by nlinarith)
    exact_mod_cast hcast
  have hsne : fShift χ t s ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    dsimp [s]
    norm_num
    linarith
  have hne (ρ : ℂ) (hρ : ρ ∈ S) : s - ρ ≠ 0 := by
    intro he
    have hzero := (mem_zset.mp (mem_filter.mp hρ).1).2
    exact hsne (sub_eq_zero.mp he ▸ hzero)
  have hclose : ∃ ρ ∈ S, 0 < m ρ ∧ ‖s - ρ‖ ≤ 2 * r := by
    obtain ⟨ρ, hρ, hd⟩ := hroot
    let w := ρ - ((3 : ℂ) / 2 + I * t)
    have he : w + (1 / 2 : ℂ) = ρ - (1 + I * t) := by dsimp [w]; ring
    have hw : ‖w + (1 / 2 : ℂ)‖ ≤ r := by rwa [he]
    have hnorm : ‖w‖ ≤ 3 / 4 := by
      have hh := norm_sub_le (w + (1 / 2 : ℂ)) (1 / 2 : ℂ)
      norm_num at hh
      linarith
    have hzero : fShift χ t w = 0 := by simpa [fShift, w] using hρ
    have hwS : w ∈ S := mem_filter.mpr ⟨mem_zset.mpr ⟨hnorm, hzero⟩, by nlinarith⟩
    have hf : AnalyticOnNhd ℂ (fShift χ t) univ := fun z hz => fShift_analyticAt hχ t z
    have htop : analyticOrderAt (fShift χ t) w ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ w)
        (by rw [analyticOrderAt_eq_zero.mpr (Or.inr (fShift_zero_ne χ t))]; simp)
    have hm : m w ≠ 0 := by
      simp only [m, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(fShift_analyticAt hχ t w).analyticOrderAt_ne_zero.mpr hzero, htop⟩
    refine ⟨w, hwS, Nat.pos_of_ne_zero hm, ?_⟩
    have hh := norm_sub_le (r : ℂ) (w + (1 / 2 : ℂ))
    have he' : s - w = (r : ℂ) - (w + (1 / 2 : ℂ)) := by dsimp [s]; ring
    rw [he']
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  obtain ⟨ν, hν, hν', hpole⟩ := reciprocal_pole_turan S m id hMcount hr s hne hclose
  let k := ν - 1
  have hν0 : 0 < ν := by omega
  have hkν : k + 1 = ν := Nat.sub_add_cancel hν0
  have hkM : M ≤ k := by dsimp [k]; omega
  have hklt : k < 2 * M := by dsimp [k]; omega
  have hMpos : 1 ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hr.le) hlog
    have hmreal : (1 : ℝ) ≤ M := hscale.trans (by nlinarith)
    exact_mod_cast hmreal
  have hk : 1 ≤ k := hMpos.trans hkM
  have hCM : 200 * C₁ * r * Real.log (Bt q t) ≤ (k : ℝ) := by
    have hc₁ : 200 * C₁ ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ hr.le) hlog
    have hm : (M : ℝ) ≤ k := by exact_mod_cast hkM
    linarith
  have habs := reciprocal_pole_error_absorbed hr hCM
  have herr := hexp q χ hχ t r (200 * r) hr (by linarith) hc hcl hscale' k hk
  let F : ℂ := iteratedDeriv k (logDeriv (fShift χ t)) s
  let P : ℂ := (-1 : ℂ) ^ k * k.factorial * ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) ^ (k + 1)
  have hPn : (k.factorial : ℝ) / (100 * r) ^ (k + 1) ≤ ‖P‖ := by
    have hh := mul_le_mul_of_nonneg_left hpole (Nat.cast_nonneg k.factorial)
    simpa [P, norm_mul, norm_pow, hkν, mul_div_assoc, div_eq_mul_inv] using hh
  have hFn : ‖F - P‖ ≤ (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) := by
    exact herr.trans (by convert mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg k.factorial) using 1 <;> ring)
  have htriangle : ‖P‖ ≤ ‖F‖ + ‖F - P‖ := by
    have hh := norm_add_le F (P - F)
    rw [norm_sub_rev P F] at hh
    simpa only [add_sub_cancel] using hh
  refine ⟨k, hkM, hklt, ?_⟩
  have heq : (k.factorial : ℝ) / (100 * r) ^ (k + 1) =
      2 * ((k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1))) := by ring
  rw [heq] at hPn
  linarith
end LeanLab.Linnik.Decomp1532b

open Complex LSeries
open scoped LSeries.notation
open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b
/-- Gallagher p.334 display 22 in normalized L series form for nonprincipal characters. -/
theorem nonprincipal_series_detector : ∃ E : ℝ, 1 ≤ E ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log (Bt q t) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log (Bt q t) ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          1 / (200 * (100 : ℝ) ^ k * r) ≤
            ‖((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
              LSeries (LSeries.logMul^[k] (↗χ * ↗ArithmeticFunction.vonMangoldt))
                (1 + r + I * t)‖ := by
  obtain ⟨E, hE, hlarge⟩ := nonprincipal_large_logDeriv
  refine ⟨E, hE, ?_⟩
  intro q hq χ hχ t r hr hrl hscale hroot M hM
  obtain ⟨k, hkM, hklt, hlarge⟩ := hlarge q χ hχ t r hr hrl hscale hroot M hM
  refine ⟨k, hkM, hklt, ?_⟩
  have hfun : logDeriv (fShift χ t) =
      (fun z => logDeriv χ.LFunction (z + ((3 : ℂ) / 2 + I * t))) := by
    funext z
    change deriv (fun w => χ.LFunction (w + ((3 : ℂ) / 2 + I * t))) z /
      χ.LFunction (z + ((3 : ℂ) / 2 + I * t)) = _
    rw [deriv_comp_add_const]
    rfl
  rw [hfun, iteratedDeriv_comp_add_const] at hlarge
  have hpoint : ((r : ℂ) - 1 / 2) + ((3 : ℂ) / 2 + I * t) = 1 + r + I * t := by ring
  dsimp only at hlarge
  rw [hpoint] at hlarge
  have hs : 1 < (1 + (r : ℂ) + I * t).re := by norm_num; linarith
  have he := iterated_neg_logDeriv_eq_LSeries χ k hs
  have hneg : (fun z => -deriv χ.LFunction z / χ.LFunction z) =
      (fun z => -logDeriv χ.LFunction z) := by funext z; simp [logDeriv_apply, neg_div]
  rw [hneg, iteratedDeriv_fun_neg] at he
  have hn := congrArg norm he
  simp only [norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hn
  rw [hn] at hlarge
  have hnorm : ‖((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ = r ^ k / (k.factorial : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, hnorm]
  have hh := mul_le_mul_of_nonneg_left hlarge
    (show 0 ≤ r ^ k / (k.factorial : ℝ) by positivity)
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  convert hh using 1
  field_simp [hf, hr.ne', mul_pow, pow_succ]
  <;> ring
end LeanLab.Linnik.Decomp1532b

open Complex LSeries
open scoped LSeries.notation
open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b2
namespace LeanLab.Linnik.Decomp1532b
/-- Gallagher p.334 display 22 for nonprincipal characters, with an explicit lower bound. -/
theorem nonprincipal_poisson_detector : ∃ E : ℝ, 1 ≤ E ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log (Bt q t) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log (Bt q t) ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          1 / (200 * (100 : ℝ) ^ k * r) ≤
            ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
              (n : ℂ) ^ (1 + I * t)) * (poissonKernel k (r * Real.log n) : ℂ)‖ := by
  obtain ⟨E, hE, hseries⟩ := nonprincipal_series_detector
  refine ⟨E, hE, ?_⟩
  intro q hq χ hχ t r hr hrl hscale hroot M hM
  obtain ⟨k, hkM, hklt, hbound⟩ := hseries q χ hχ t r hr hrl hscale hroot M hM
  rw [normalized_log_series_eq_poisson] at hbound
  exact ⟨k, hkM, hklt, hbound⟩
end LeanLab.Linnik.Decomp1532b
