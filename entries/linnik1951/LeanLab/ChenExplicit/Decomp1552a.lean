module

public import LeanLab.ChenExplicit.Bridge
public import LeanLab.ChenExplicit.Decomp94
public import LeanLab.PNTSieve.MertensLower

/-!
AI-written Lean code, Claude, 2026-10-26, run 20261026T1219Z-15327, unit U-1552, track T1, DECOMPOSE.
T. Yamada 2015, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, proof of Theorem 7.1.

Codex task186 proof additions, 2026-10-30. AI wrote the Lean code.
Five original leaves and the supporting lemmas below have unconditional proofs.
The eq109_pi application is CONDITIONAL ON the existing cited prime counting input.
Codex task212 proof additions, 2026-11-01. AI wrote the Lean code.
Three general finite Abel lemmas are PROVED with committed build and axiom evidence.
The head, corrected tail and H sum applications are CONDITIONAL ON prime_reciprocal_eq7.
That cited display 7 estimate is the only remaining local placeholder proof.

Part a of the decomposition of Yamada's Theorem 7.1, the bound for `S(B, P(y))`:
the blocks `B^(j)` of (105), (106) and the leaves of Lemma 7.3, (108) to (116).
The lab holds Theorem 7.1 only as the cited hypothesis `Thm71W` (Thm71Fix.lean, F-0028).
The remaining placeholder proof of the lab file is the cited prime reciprocal LEAF; the assembly `lemma73_corr` is in
Decomp1552c.lean, CONDITIONAL ON these leaves.

Corrections built in, see ChenExplicit/STATEMENTS.md, U-1552 block:
* (106) prints `j₀ = [log(y/z)/log(1+ε)] - 1`; the blocks `j ≤ j₀` then miss the primes
  `p₁ ∈ [z(1+ε)^{j₀+1}, y)`. We use `J = ⌈log(y/z)/log(1+ε)⌉` blocks, which cover `[z, y)`.
* (112) is stated on `y ≤ p₂ < (N/p₁)^{1/2}`, the range of `H(p₁)` in (110); the primes
  `(N/p₁)^{1/2} ≤ p₂ < w = ((1+ε)N/p₁)^{1/2}` of (109) get their own leaf `eq112_tail`.
* (116) uses `H(z) = (8/7) log(13/8) / log N`, finding F-0014, not the printed `log(26/21)/log N`.
Chen's theorem is known; binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.D1552

/-- `z = N^{1/8}`, Section 4; definitionally the lab's `zN`. -/
abbrev z8 (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)

/-- `y = N^{1/3}`, Section 4; definitionally the lab's `yN`. -/
abbrev y3 (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)

/-- `w_j = z (1+ε)^j`, (106). -/
def wj (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ := z8 N * (1 + ε) ^ j

/-- Number of blocks, `⌈log(y/z) / log(1+ε)⌉`; corrected from (106), see the header. -/
def Jblk (N : ℕ) (ε : ℝ) : ℕ := ⌈log (y3 N / z8 N) / log (1 + ε)⌉₊

/-- `m = p₁p₂p₃` with `N - m ∈ B^(j)`, (105): `z ≤ p₁ < y ≤ p₂ ≤ p₃`, `w_j p₂p₃ < N`,
`(p₂p₃, N) = 1`, `w_j ≤ p₁ < (1+ε)w_j`. The printed `u p₂p₃ < N` is read as `w_j p₂p₃ < N`,
as the proof uses it. -/
def InBj (N : ℕ) (ε : ℝ) (j m : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z8 N ≤ p₁ ∧ (p₁ : ℝ) < y3 N ∧
    y3 N ≤ p₂ ∧ p₂ ≤ p₃ ∧ wj N ε j * p₂ * p₃ < N ∧ Nat.Coprime (p₂ * p₃) N ∧
    wj N ε j ≤ p₁ ∧ (p₁ : ℝ) < (1 + ε) * wj N ε j ∧ m = p₁ * p₂ * p₃

/-- The block `B^(j)` of (105), as the finite set of products `m = p₁p₂p₃`; its element of
`B^(j)` is the integer `N - m`, which can be negative. For `ε < 1`, `m < (1+ε)N < 2N`. -/
def Bj (N : ℕ) (ε : ℝ) (j : ℕ) : Finset ℕ := (range (2 * N)).filter (InBj N ε j)

/-- Primes `p` with `a ≤ p < b`. -/
def primesIco (a b : ℝ) : Finset ℕ := (range ⌈b⌉₊).filter fun p => p.Prime ∧ a ≤ (p : ℝ)

/-- `w = w(p₁) = ((1+ε)N/p₁)^{1/2}`, (109). -/
def wP (N : ℕ) (ε : ℝ) (p₁ : ℕ) : ℝ := √((1 + ε) * N / p₁)

/-- `h_{p₁}(t) = 1 / log(N/(p₁ t))`, proof of Lemma 7.3. -/
def hP (N : ℕ) (p₁ : ℕ) (t : ℝ) : ℝ := 1 / log (N / (p₁ * t))

/-- `H(u) = ∫_y^{(N/u)^{1/2}} dt / (t log t log(N/(ut)))`, (110); the same integrand as
`Yamada.Hfun` of Eq111.lean. -/
def H (N : ℕ) (u : ℝ) : ℝ :=
  ∫ t in y3 N..((N : ℝ) / u) ^ ((1 : ℝ) / 2), 1 / (t * log t * log (N / (u * t)))

/-- `c₂ - 10⁻⁸ = ∫_{1/8}^{1/3} log(2 - 3β) / (β(1-β)) dβ`, Lemma 7.3. -/
def I73 : ℝ := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))

/-- Finite Abel identity with real sample points and a continuously differentiable weight. -/
theorem finite_abel_identity {ι : Type*} (s : Finset ι) (v c : ι → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hv : ∀ i ∈ s, v i ∈ Set.Icc a b)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Set.Icc a b)) :
    ∑ i ∈ s, c i * f (v i) = f b * ∑ i ∈ s, c i -
      ∫ t in a..b, f' t * ∑ i ∈ s.filter (fun i => v i < t), c i := by
  have hint : IntervalIntegrable f' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hinti (i : ι) : IntervalIntegrable
      (fun t => if v i < t then f' t else 0) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint.1.indicator measurableSet_Ioi
  have hi (i : ι) (his : i ∈ s) :
      (∫ t in a..b, if v i < t then f' t else 0) = f b - f (v i) := by
    have hp := hv i his
    have hset : Set.Ioi (v i) ∩ Set.Ioc a b = Set.Ioc (v i) b := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · tauto
      · rintro ⟨ht, htb⟩
        exact ⟨ht, lt_of_le_of_lt hp.1 ht, htb⟩
    have heq : (∫ t in a..b, if v i < t then f' t else 0) = ∫ t in v i..b, f' t := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hp.2]
      change (∫ t in Set.Ioc a b, (Set.Ioi (v i)).indicator f' t) = _
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset]
    rw [heq]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hp.2] at ht
      exact hf t ⟨hp.1.trans ht.1, ht.2⟩
    · apply hint.mono_set
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hp.2]
      exact Set.Icc_subset_Icc hp.1 le_rfl
  have hs : (∫ t in a..b, f' t * ∑ i ∈ s.filter (fun i => v i < t), c i) =
      ∑ i ∈ s, c i * (f b - f (v i)) := by
    calc
      _ = ∫ t in a..b, ∑ i ∈ s, c i * (if v i < t then f' t else 0) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [sum_filter, mul_sum]
        apply sum_congr rfl
        intro i hi
        split_ifs <;> ring
      _ = ∑ i ∈ s, ∫ t in a..b, c i * (if v i < t then f' t else 0) :=
        intervalIntegral.integral_finsetSum (fun i hi => (hinti i).const_mul _)
      _ = _ := by
        apply sum_congr rfl
        intro i his
        rw [intervalIntegral.integral_const_mul, hi i his]
  rw [hs]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul]
  ring
/-- A prefix error transfers to a decreasing nonnegative smooth weight without enlarging the error. -/
theorem finite_abel_antitone {ι : Type*} (s : Finset ι) (v c : ι → ℝ)
    (a b E : ℝ) (hab : a ≤ b) (hv : ∀ i ∈ s, v i ∈ Set.Ico a b)
    (f f' g g' : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b)) (hgc : ContinuousOn g' (Set.Icc a b))
    (hfb : 0 ≤ f b) (hf' : ∀ t ∈ Set.Icc a b, f' t ≤ 0)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ∑ i ∈ s.filter (fun i => v i < t), c i ≤ g t - g a + E) :
    ∑ i ∈ s, c i * f (v i) ≤ (∫ t in a..b, f t * g' t) + E * f a := by
  have hu (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ∈ Set.Icc a b := by
    rwa [Set.uIcc_of_le hab] at ht
  have hfi : IntervalIntegrable f' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hgi : IntervalIntegrable g' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hcontf : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hcontg : ContinuousOn g (Set.Icc a b) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hstep (i : ι) : IntervalIntegrable
      (fun t => c i * (if v i < t then f' t else 0)) volume a b := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hfi.1.indicator measurableSet_Ioi
  have hpi : IntervalIntegrable
      (fun t => f' t * ∑ i ∈ s.filter (fun i => v i < t), c i) volume a b := by
    have hh := IntervalIntegrable.sum s (fun i hi => hstep i)
    apply hh.congr
    intro t ht
    simp only [Finset.sum_apply]
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have hbi : IntervalIntegrable (fun t => f' t * (g t - g a + E)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hfc.mul ((hcontg.sub continuousOn_const).add continuousOn_const)
  have hi := intervalIntegral.integral_mono_on hab hbi hpi (fun t ht =>
    mul_le_mul_of_nonpos_left (hprefix t ht) (hf' t ht))
  have htotal : ∑ i ∈ s, c i ≤ g b - g a + E := by
    have hh := hprefix b ⟨hab, le_rfl⟩
    have he : s.filter (fun i => v i < b) = s := filter_eq_self.mpr (fun i hi => (hv i hi).2)
    rwa [he] at hh
  have hid := finite_abel_identity s v c a b hab
    (fun i hi => ⟨(hv i hi).1, (hv i hi).2.le⟩) f f' hf hfc
  have hmain := mul_le_mul_of_nonneg_left htotal hfb
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hf t (hu t ht))
    (fun t ht => (hg t (hu t ht)).sub_const (g a - E)) hfi hgi
  have heq : (∫ t in a..b, f' t * (g t - g a + E)) =
      f b * (g b - g a + E) - f a * E - ∫ t in a..b, f t * g' t := by
    have hgeq : (fun t => f' t * (g t - (g a - E))) = (fun t => f' t * (g t - g a + E)) := by
      funext t
      ring
    rw [hgeq] at hparts
    linarith
  rw [heq] at hi
  linarith

/-- A suffix error transfers to an increasing nonnegative smooth weight. -/
theorem finite_abel_monotone {ι : Type*} (s : Finset ι) (v c : ι → ℝ)
    (a b E : ℝ) (hab : a ≤ b) (hv : ∀ i ∈ s, v i ∈ Set.Ico a b)
    (f f' g g' : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b)) (hgc : ContinuousOn g' (Set.Icc a b))
    (hfa : 0 ≤ f a) (hf' : ∀ t ∈ Set.Icc a b, 0 ≤ f' t)
    (hsuffix : ∀ t ∈ Set.Icc a b,
      ∑ i ∈ s.filter (fun i => t ≤ v i), c i ≤ g b - g t + E) :
    ∑ i ∈ s, c i * f (v i) ≤ (∫ t in a..b, f t * g' t) + E * f b := by
  have hu (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ∈ Set.Icc a b := by
    rwa [Set.uIcc_of_le hab] at ht
  have hfi : IntervalIntegrable f' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hgi : IntervalIntegrable g' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hcontg : ContinuousOn g (Set.Icc a b) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hstep (i : ι) : IntervalIntegrable
      (fun t => c i * (if t ≤ v i then f' t else 0)) volume a b := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hfi.1.indicator measurableSet_Iic
  have hsi : IntervalIntegrable
      (fun t => f' t * ∑ i ∈ s.filter (fun i => t ≤ v i), c i) volume a b := by
    have hh := IntervalIntegrable.sum s (fun i hi => hstep i)
    apply hh.congr
    intro t ht
    simp only [Finset.sum_apply]
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have hbi : IntervalIntegrable (fun t => f' t * (g b - g t + E)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hfc.mul ((continuousOn_const.sub hcontg).add continuousOn_const)
  have hi := intervalIntegral.integral_mono_on hab hsi hbi (fun t ht =>
    mul_le_mul_of_nonneg_left (hsuffix t ht) (hf' t ht))
  have htotal : ∑ i ∈ s, c i ≤ g b - g a + E := by
    have hh := hsuffix a ⟨le_rfl, hab⟩
    have he : s.filter (fun i => a ≤ v i) = s := filter_eq_self.mpr (fun i hi => (hv i hi).1)
    rwa [he] at hh
  have hid := finite_abel_identity s v c a b hab
    (fun i hi => ⟨(hv i hi).1, (hv i hi).2.le⟩) f f' hf hfc
  have hsplit (t : ℝ) :
      f' t * ∑ i ∈ s.filter (fun i => v i < t), c i =
        f' t * ∑ i ∈ s, c i - f' t * ∑ i ∈ s.filter (fun i => t ≤ v i), c i := by
    rw [sum_filter, sum_filter, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases h : v i < t
    · simp [h, not_le.mpr h]
    · simp [h, le_of_not_gt h]
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hf t (hu t ht)) hfi
  have hidentity : ∑ i ∈ s, c i * f (v i) = f a * ∑ i ∈ s, c i +
      ∫ t in a..b, f' t * ∑ i ∈ s.filter (fun i => t ≤ v i), c i := by
    simp_rw [hsplit] at hid
    rw [intervalIntegral.integral_sub (hfi.mul_const _) hsi,
      intervalIntegral.integral_mul_const, hft] at hid
    linarith
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hf t (hu t ht))
    (fun t ht => ((hg t (hu t ht)).const_sub (g b + E))) hfi hgi.neg
  have heq : (∫ t in a..b, f' t * (g b - g t + E)) =
      (∫ t in a..b, f t * g' t) + f b * E - f a * (g b - g a + E) := by
    have hgeq : (fun t => f' t * (g b + E - g t)) =
        (fun t => f' t * (g b - g t + E)) := by funext t; ring
    rw [hgeq] at hparts
    rw [show (fun t => f t * -g' t) = (fun t => -(f t * g' t)) by funext t; ring,
      intervalIntegral.integral_neg] at hparts
    linarith
  have hmain := mul_le_mul_of_nonneg_left htotal hfa
  rw [heq] at hi
  linarith

/-- Prime Abel comparison for a decreasing smooth weight, conditional on an interval estimate. -/
theorem prime_abel_antitone (a b E : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b))
    (hfb : 0 ≤ f b) (hf' : ∀ t ∈ Set.Icc a b, f' t ≤ 0)
    (hM : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      ∑ p ∈ primesIco x y, (1 : ℝ) / p ≤ log (log y) - log (log x) + E) :
    ∑ p ∈ s, f p / p ≤ (∫ t in a..b, f t / (t * log t)) + E * f a := by
  have hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => log (log t)) (1 / (t * log t)) t := by
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    convert ((hasDerivAt_log (by linarith : t ≠ 0)).log (log_pos ht1).ne') using 1 <;> field_simp
  have hgc : ContinuousOn (fun t => 1 / (t * log t)) (Set.Icc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_log.mono ?_))
    · intro t ht
      have : 1 < t := ha.trans_le ht.1
      exact mul_ne_zero (ne_of_gt (by linarith : 0 < t)) (log_pos this).ne'
    · intro t ht
      have : 1 < t := ha.trans_le ht.1
      exact ne_of_gt (by linarith)
  have hh := finite_abel_antitone s (fun p => (p : ℝ)) (fun p => (1 : ℝ) / p)
    a b E hab (fun p hp => ⟨(hs p hp).2.1, (hs p hp).2.2⟩)
    f f' (fun t => log (log t)) (fun t => 1 / (t * log t)) hf hg hfc hgc hfb hf' ?_
  · simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  · intro t ht
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun p hp hn => by positivity))
      (hM a t le_rfl ht.1 ht.2)
    intro p hp
    obtain ⟨hps, hpt⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpt), (hs p hps).1, (hs p hps).2.1⟩

/-- Prime Abel comparison for an increasing smooth weight, conditional on an interval estimate. -/
theorem prime_abel_monotone (a b E : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b))
    (hfa : 0 ≤ f a) (hf' : ∀ t ∈ Set.Icc a b, 0 ≤ f' t)
    (hM : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      ∑ p ∈ primesIco x y, (1 : ℝ) / p ≤ log (log y) - log (log x) + E) :
    ∑ p ∈ s, f p / p ≤ (∫ t in a..b, f t / (t * log t)) + E * f b := by
  have hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => log (log t)) (1 / (t * log t)) t := by
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    convert ((hasDerivAt_log (by linarith : t ≠ 0)).log (log_pos ht1).ne') using 1 <;> field_simp
  have hgc : ContinuousOn (fun t => 1 / (t * log t)) (Set.Icc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_log.mono ?_))
    · intro t ht
      have : 1 < t := ha.trans_le ht.1
      exact mul_ne_zero (ne_of_gt (by linarith : 0 < t)) (log_pos this).ne'
    · intro t ht
      have : 1 < t := ha.trans_le ht.1
      exact ne_of_gt (by linarith)
  have hh := finite_abel_monotone s (fun p => (p : ℝ)) (fun p => (1 : ℝ) / p)
    a b E hab (fun p hp => ⟨(hs p hp).2.1, (hs p hp).2.2⟩)
    f f' (fun t => log (log t)) (fun t => 1 / (t * log t)) hf hg hfc hgc hfa hf' ?_
  · simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  · intro t ht
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun p hp hn => by positivity))
      (hM t b ht.1 ht.2 le_rfl)
    intro p hp
    obtain ⟨hps, hpt⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr (hs p hps).2.2), (hs p hps).1, hpt⟩


/-- Closed form of H at a real power, Yamada page 25 eq 111. -/
theorem H_rpow_eq (N : ℕ) (hN : (1 : ℝ) < N) (α : ℝ) (hα : α ≤ 1 / 3) :
    H N ((N : ℝ) ^ α) = log (2 - 3 * α) / ((1 - α) * log N) := by
  have hNp : (0 : ℝ) < N := by linarith
  set L := log (N : ℝ) with hLdef
  have hL : 0 < L := log_pos hN
  set c := (1 - α) * L with hc
  have hcpos : 0 < c := by dsimp [c]; exact mul_pos (by linarith) hL
  have hcmin : 2 * L / 3 ≤ c := by dsimp [c]; nlinarith
  have hy : y3 N = exp (L / 3) := by
    rw [y3, rpow_def_of_pos hNp, ← hLdef]; congr 1; ring
  have hu : (N : ℝ) ^ α = exp (α * L) := by
    rw [rpow_def_of_pos hNp, ← hLdef]; congr 1; ring
  have htop : ((N : ℝ) / (N : ℝ) ^ α) ^ ((1 : ℝ) / 2) = exp (c / 2) := by
    rw [hu, show (N : ℝ) = exp L by exact (exp_log hNp).symm,
      ← exp_sub, rpow_def_of_pos (exp_pos _), log_exp]
    congr 1
    dsimp [c]
    ring
  unfold H
  rw [hy, htop, hu]
  set a := exp (L / 3) with ha
  set b := exp (c / 2) with hb
  have hab : a ≤ b := exp_le_exp.mpr (by linarith)
  have hI : ∀ t ∈ Set.uIcc a b, 0 < t ∧ 0 < log t ∧ 0 < c - log t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 := (exp_pos (L / 3)).trans_le ht.1
    have hlo : L / 3 ≤ log t := by
      simpa only [log_exp] using log_le_log (exp_pos _) ht.1
    have hhi : log t ≤ c / 2 := by
      simpa only [hb, log_exp] using log_le_log ht0 ht.2
    exact ⟨ht0, by linarith, by linarith⟩
  have hlogarg (t : ℝ) (ht : 0 < t) :
      log (N / (exp (α * L) * t)) = c - log t := by
    rw [log_div hNp.ne' (by positivity), log_mul (exp_pos _).ne' ht.ne', log_exp]
    dsimp [c, L]
    ring
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => (log (log t) - log (c - log t)) / c)
        (1 / (t * log t * (c - log t))) t := by
    intro t ht
    obtain ⟨ht0, hlt, hct⟩ := hI t ht
    have d := (((hasDerivAt_log ht0.ne').log hlt.ne').sub
      (((hasDerivAt_log ht0.ne').const_sub c).log hct.ne')).div_const c
    convert d using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun t => 1 / (t * log t * (c - log t))) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.mul (continuousOn_log.mono fun t ht => (hI t ht).1.ne')).mul
        (continuousOn_const.sub (continuousOn_log.mono fun t ht => (hI t ht).1.ne'))
    · intro t ht
      obtain ⟨ht0, hlt, hct⟩ := hI t ht
      positivity
  rw [intervalIntegral.integral_congr (fun t ht => by rw [hlogarg t (hI t ht).1]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  have hla : log a = L / 3 := by rw [ha, log_exp]
  have hlb : log b = c / 2 := by rw [hb, log_exp]
  rw [hla, hlb, show c - c / 2 = c / 2 by ring, sub_self, zero_div, zero_sub]
  have hp : 0 < 2 - 3 * α := by linarith
  have he : c - L / 3 = (2 - 3 * α) * (L / 3) := by dsimp [c]; ring
  rw [he, log_mul hp.ne' (by positivity)]
  dsimp [c]
  ring

open LeanLab.PNTSieve.Mertens in
/-- A reciprocal prime block estimate from elementary Mertens bounds, for page 26 eq 115. -/
theorem reciprocal_prime_block_le (y w : ℕ) (hy : 2 ≤ y) (hyw : y ≤ w) :
    E w - E y ≤ log (log w) - log (log y) + 14 / log y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hly : 0 < log y := log_pos (by exact_mod_cast (by omega : 1 < y))
  have habel : E w - E y = C w / log w - C y / log y +
      ∑ n ∈ Ico y w, C n * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
    induction w, hyw using Nat.le_induction with
    | base => simp
    | succ w hw ih =>
      have he : E (w + 1) = E w + c (w + 1) / log ((w : ℝ) + 1) := by
        unfold E
        rw [sum_Icc_succ_top (by omega)]
        push_cast
        rfl
      have hc : C (w + 1) = C w + c (w + 1) := by
        unfold C
        rw [sum_Icc_succ_top (by omega)]
      rw [he, hc, sum_Ico_succ_top hw]
      push_cast
      rw [show E w = E w - E y + E y by ring, ih]
      ring
  have hlw : 0 < log w := log_pos (by exact_mod_cast (by omega : 1 < w))
  have hterm : ∀ n ∈ Ico y w,
      C n * (1 / log n - 1 / log ((n : ℝ) + 1)) ≤
        (log (log ((n : ℝ) + 1)) - log (log n)) +
          7 * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
    intro n hn
    have hn2 : 2 ≤ n := hy.trans (mem_Ico.mp hn).1
    have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hl : 0 < log n := log_pos hnp
    have hl1 : 0 < log ((n : ℝ) + 1) := log_pos (by linarith)
    have hd := diff_nonneg hn2
    have hC := C_le n (by omega)
    have h1 := mul_le_mul_of_nonneg_right hC hd
    have h2 : log n * (1 / log n - 1 / log ((n : ℝ) + 1)) ≤
        log (log ((n : ℝ) + 1)) - log (log n) := by
      rw [← log_div hl1.ne' hl.ne']
      have hh := one_sub_inv_le_log_of_pos (div_pos hl1 hl)
      rw [inv_div] at hh
      have he : log n * (1 / log n - 1 / log ((n : ℝ) + 1)) =
          1 - log n / log ((n : ℝ) + 1) := by field_simp
      rw [he]
      exact hh
    nlinarith only [h1, h2]
  have hs := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hs
  have ht1 : ∑ n ∈ Ico y w, (log (log ((n : ℝ) + 1)) - log (log n)) =
      log (log w) - log (log y) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      sum_Ico_sub (fun n : ℕ => log (log (n : ℝ))) hyw
  have ht2 : ∑ n ∈ Ico y w, (1 / log n - 1 / log ((n : ℝ) + 1)) =
      1 / log y - 1 / log w := by
    have ht := sum_Ico_sub (fun n : ℕ => -(1 / log (n : ℝ))) hyw
    simpa only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add, neg_add_eq_sub] using ht
  rw [ht1, ht2] at hs
  have hb1 : C w / log w ≤ 1 + 7 / log w := by
    apply (div_le_iff₀ hlw).2
    have hh := C_le w (by omega)
    field_simp
    linarith
  have hb2 : 1 - 7 / log y ≤ C y / log y := by
    apply (le_div_iff₀ hly).2
    have hh := C_ge y
    field_simp
    linarith
  rw [habel]
  simp only [div_eq_mul_inv] at hs hb1 hb2 ⊢
  linarith only [hs, hb1, hb2]

/-- H decreases between z and y, Yamada page 26 before eq 116. -/
theorem H_antitoneOn (N : ℕ) (hN : (1 : ℝ) < N) :
    AntitoneOn (H N) (Set.Icc (z8 N) (y3 N)) := by
  have hNp : (0 : ℝ) < N := by linarith
  have hL : 0 < log (N : ℝ) := log_pos hN
  let F : ℝ → ℝ := fun α => log (2 - 3 * α) / (1 - α)
  let F' : ℝ → ℝ := fun α =>
    ((-3 / (2 - 3 * α)) * (1 - α) + log (2 - 3 * α)) / (1 - α) ^ 2
  have hderiv : ∀ α ∈ Set.Icc (1 / 8 : ℝ) (1 / 3), HasDerivAt F (F' α) α := by
    intro α hα
    have hp : 0 < 2 - 3 * α := by have := hα.2; linarith
    have hd : 0 < 1 - α := by have := hα.2; linarith
    have d1 := (((hasDerivAt_id α).const_mul 3).const_sub 2).log hp.ne'
    have d2 := (hasDerivAt_id α).const_sub 1
    convert d1.div d2 hd.ne' using 1
    · rfl
    · dsimp [F']
      ring
  have hnonpos : ∀ α ∈ Set.Icc (1 / 8 : ℝ) (1 / 3), F' α ≤ 0 := by
    intro α hα
    have hp : 0 < 2 - 3 * α := by have := hα.2; linarith
    have hl := log_le_sub_one_of_pos hp
    have hlg : log (2 - 3 * α) ≤ 1 := by have := hα.1; linarith
    have hr : (-3 / (2 - 3 * α)) * (1 - α) ≤ -1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp).2
      linarith
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hant : AntitoneOn F (Set.Icc (1 / 8 : ℝ) (1 / 3)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun α hα => (hderiv α hα).continuousAt.continuousWithinAt)
      (fun α hα => (hderiv α (interior_subset hα)).hasDerivWithinAt)
      (fun α hα => hnonpos α (interior_subset hα))
  have hz : log (z8 N) = log N / 8 := by rw [log_rpow hNp]; ring
  have hy : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hfacts : ∀ u ∈ Set.Icc (z8 N) (y3 N),
      0 < u ∧ log u / log N ∈ Set.Icc (1 / 8 : ℝ) (1 / 3) := by
    intro u hu
    have hu0 := hzpos.trans_le hu.1
    have hlo := log_le_log hzpos hu.1
    have hhi := log_le_log hu0 hu.2
    rw [hz] at hlo
    rw [hy] at hhi
    exact ⟨hu0, (le_div_iff₀ hL).2 (by linarith), (div_le_iff₀ hL).2 (by linarith)⟩
  have hformula : ∀ u ∈ Set.Icc (z8 N) (y3 N), H N u = F (log u / log N) / log N := by
    intro u hu
    obtain ⟨hu0, _, hhi⟩ := hfacts u hu
    have he : (N : ℝ) ^ (log u / log N) = u := by
      rw [rpow_def_of_pos hNp]
      have hh : log (N : ℝ) * (log u / log N) = log u := by field_simp
      rw [hh, exp_log hu0]
    have hh := H_rpow_eq N hN (log u / log N) hhi
    rw [he] at hh
    rw [hh]
    dsimp [F]
    rw [div_div]
  intro u hu v hv huv
  rw [hformula u hu, hformula v hv]
  exact div_le_div_of_nonneg_right
    (hant (hfacts u hu).2 (hfacts v hv).2
      (div_le_div_of_nonneg_right (log_le_log (hfacts u hu).1 huv) hL.le)) hL.le

/-- The increasing weight in Yamada page 26 eq 112. -/
theorem hP_monotoneOn (N : ℕ) (hN : exp (exp 36) < N) (p : ℕ)
    (hp : p ∈ primesIco (z8 N) (y3 N)) :
    MonotoneOn (hP N p) (Set.Icc (y3 N) (√((N : ℝ) / p))) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log (N : ℝ) := (exp_pos _).trans hL
  have hpp : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
  have hylog : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hlp : log (p : ℝ) < log N / 3 := by
    have hh := log_lt_log hpp hpy
    rw [hylog] at hh
    exact hh
  have hypos : 0 < y3 N := rpow_pos_of_pos hNp _
  have hq : 0 < (N : ℝ) / p := div_pos hNp hpp
  have hs : 0 < √((N : ℝ) / p) := sqrt_pos_of_pos hq
  have hlogpos : ∀ t ∈ Set.Icc (y3 N) (√((N : ℝ) / p)), 0 < log (N / (p * t)) := by
    intro t ht
    have ht0 := hypos.trans_le ht.1
    have hlt := log_le_log ht0 ht.2
    rw [log_sqrt hq.le, log_div hNp.ne' hpp.ne'] at hlt
    rw [log_div hNp.ne' (mul_pos hpp ht0).ne', log_mul hpp.ne' ht0.ne']
    linarith
  intro t ht u hu htu
  have ht0 := hypos.trans_le ht.1
  have hu0 := hypos.trans_le hu.1
  apply one_div_le_one_div_of_le (hlogpos u hu)
  apply log_le_log (div_pos hNp (mul_pos hpp hu0))
  apply div_le_div_of_nonneg_left hNp.le (mul_pos hpp ht0)
  exact mul_le_mul_of_nonneg_left htu hpp.le

/-- The weight bound on the enlarged tail interval, for the correction to page 26 eq 112. -/
theorem hP_le_301 (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1 / 100) (p : ℕ) (hp : p ∈ primesIco (z8 N) (y3 N)) (t : ℝ)
    (ht : t ∈ Set.Icc (y3 N) (wP N ε p)) :
    hP N p t ≤ (301 / 100 : ℝ) / log N := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hL37 : (37 : ℝ) < log N := by linarith [add_one_le_exp (36 : ℝ)]
  have hLp : 0 < log (N : ℝ) := by linarith
  have hpp : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
  have hplog : log (p : ℝ) < log N / 3 := by
    have hh := log_lt_log hpp hpy
    rw [show log (y3 N) = (1 / 3 : ℝ) * log N from log_rpow hNp _] at hh
    linarith
  have hep : 0 < 1 + ε := by linarith
  have helog : log (1 + ε) ≤ ε := by linarith [log_le_sub_one_of_pos hep]
  have ht0 : 0 < t := (rpow_pos_of_pos hNp ((1 : ℝ) / 3)).trans_le ht.1
  have hlt := log_le_log ht0 ht.2
  change log t ≤ log (√((1 + ε) * N / p)) at hlt
  have harg : 0 < (1 + ε) * N / p := div_pos (mul_pos hep hNp) hpp
  rw [log_sqrt harg.le, log_div (mul_pos hep hNp).ne' hpp.ne',
    log_mul hep.ne' hNp.ne'] at hlt
  have hlogarg : log (N / (p * t)) = log N - log p - log t := by
    rw [log_div hNp.ne' (mul_pos hpp ht0).ne', log_mul hpp.ne' ht0.ne']
    ring
  have hd : 0 < log N - log (p : ℝ) - log t := by linarith
  unfold hP
  rw [hlogarg]
  apply (div_le_div_iff₀ hd hLp).2
  linarith

/-- The logarithmic length of the added interval in the correction to page 26 eq 112. -/
theorem loglog_tail_gap_le (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1 / 100) (p : ℕ) (hp : p ∈ primesIco (z8 N) (y3 N)) :
    log (log (wP N ε p)) - log (log (√((N : ℝ) / p))) ≤ 3 * ε / (2 * log N) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log (N : ℝ) := (exp_pos _).trans hL
  have hpp : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
  have hplog : log (p : ℝ) < log N / 3 := by
    have hh := log_lt_log hpp hpy
    rw [show log (y3 N) = (1 / 3 : ℝ) * log N from log_rpow hNp _] at hh
    linarith
  have hep : 0 < 1 + ε := by linarith
  have helog : log (1 + ε) ≤ ε := by linarith [log_le_sub_one_of_pos hep]
  have helog0 : 0 ≤ log (1 + ε) := log_nonneg (by linarith)
  have hq : 0 < (N : ℝ) / p := div_pos hNp hpp
  have harg : 0 < (1 + ε) * N / p := div_pos (mul_pos hep hNp) hpp
  have ha : log (√((N : ℝ) / p)) = (log N - log p) / 2 := by
    rw [log_sqrt hq.le, log_div hNp.ne' hpp.ne']
  have hb : log (wP N ε p) = (log N - log p + log (1 + ε)) / 2 := by
    unfold wP
    rw [log_sqrt harg.le, log_div (mul_pos hep hNp).ne' hpp.ne', log_mul hep.ne' hNp.ne']
    ring
  have hcap : 0 < log N - log (p : ℝ) := by linarith
  have hla : 0 < log (√((N : ℝ) / p)) := by rw [ha]; positivity
  have hlb : 0 < log (wP N ε p) := by rw [hb]; positivity
  rw [← log_div hlb.ne' hla.ne']
  calc
    _ ≤ log (wP N ε p) / log (√((N : ℝ) / p)) - 1 :=
      log_le_sub_one_of_pos (div_pos hlb hla)
    _ = log (1 + ε) / (log N - log p) := by rw [ha, hb]; field_simp; ring
    _ ≤ ε / (log N - log p) := div_le_div_of_nonneg_right helog hcap.le
    _ ≤ ε / (2 * log N / 3) :=
      div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
    _ = _ := by field_simp

/-- The integral part of the corrected tail, for Yamada page 26 eq 112. -/
theorem tail_integral_le (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1 / 100) (p : ℕ) (hp : p ∈ primesIco (z8 N) (y3 N)) :
    (∫ t in √((N : ℝ) / p)..wP N ε p, 1 / (t * log t * log (N / (p * t)))) ≤
      5 * ε / log N ^ 2 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hL37 : (37 : ℝ) < log N := by linarith [add_one_le_exp (36 : ℝ)]
  have hLp : 0 < log (N : ℝ) := by linarith
  have hpp : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
  have hylog : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hplog : log (p : ℝ) < log N / 3 := by
    have hh := log_lt_log hpp hpy
    rw [hylog] at hh
    exact hh
  have hep : 0 < 1 + ε := by linarith
  have helog : log (1 + ε) ≤ ε := by linarith [log_le_sub_one_of_pos hep]
  have hq : 0 < (N : ℝ) / p := div_pos hNp hpp
  have harg : 0 < (1 + ε) * N / p := div_pos (mul_pos hep hNp) hpp
  set a := √((N : ℝ) / p) with ha
  set b := wP N ε p with hb
  have hapos : 0 < a := sqrt_pos_of_pos hq
  have hab : a ≤ b := by
    apply sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hpp.le
    nlinarith
  have hla : log a = (log N - log p) / 2 := by rw [ha, log_sqrt hq.le, log_div hNp.ne' hpp.ne']
  have hlb : log b = (log N - log p + log (1 + ε)) / 2 := by
    rw [hb, wP, log_sqrt harg.le, log_div (mul_pos hep hNp).ne' hpp.ne', log_mul hep.ne' hNp.ne']
    ring
  have hya : y3 N ≤ a := by
    have hh : log (y3 N) ≤ log a := by rw [hylog, hla]; linarith
    have he := exp_le_exp.mpr hh
    simpa only [exp_log (rpow_pos_of_pos hNp ((1 : ℝ) / 3)), exp_log hapos] using he
  have he (t : ℝ) (ht : 0 < t) : log (N / (p * t)) = log N - log p - log t := by
    rw [log_div hNp.ne' (mul_pos hpp ht).ne', log_mul hpp.ne' ht.ne']
    ring
  have hfacts : ∀ t ∈ Set.uIcc a b, 0 < t ∧ 0 < log t ∧ 0 < log (N / (p * t)) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 := hapos.trans_le ht.1
    have hlo := log_le_log hapos ht.1
    have hhi := log_le_log ht0 ht.2
    rw [hla] at hlo
    rw [hlb] at hhi
    refine ⟨ht0, by linarith, ?_⟩
    rw [he t ht0]
    linarith
  have hcontbase : ContinuousOn (fun t : ℝ => 1 / (t * log t)) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul (continuousOn_log.mono fun t ht => (hfacts t ht).1.ne')
    · intro t ht
      have hh := hfacts t ht
      exact (mul_pos hh.1 hh.2.1).ne'
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * log t * log (N / (p * t)))) (Set.uIcc a b) := by
    have heq : Set.EqOn (fun t : ℝ => 1 / (t * log t * log (N / (p * t))))
        (fun t : ℝ => 1 / (t * log t * (log N - log p - log t))) (Set.uIcc a b) := by
      intro t ht
      dsimp only
      rw [he t (hfacts t ht).1]
    apply ContinuousOn.congr _ heq
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.mul (continuousOn_log.mono fun t ht => (hfacts t ht).1.ne')).mul
        (continuousOn_const.sub (continuousOn_log.mono fun t ht => (hfacts t ht).1.ne'))
    · intro t ht
      obtain ⟨ht0, hlt, hct⟩ := hfacts t ht
      rw [he t ht0] at hct
      positivity
  have hG : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => log (log t)) (1 / (t * log t)) t := by
    intro t ht
    obtain ⟨ht0, hlt, _⟩ := hfacts t ht
    convert (hasDerivAt_log ht0.ne').log hlt.ne' using 1
    field_simp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hcontbase.intervalIntegrable
  have hmono : (∫ t in a..b, 1 / (t * log t * log (N / (p * t)))) ≤
      ∫ t in a..b, ((301 / 100 : ℝ) / log N) * (1 / (t * log t)) := by
    apply intervalIntegral.integral_mono_on hab hcont.intervalIntegrable (hcontbase.intervalIntegrable.const_mul _)
    intro t ht
    have ht' : t ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact ht
    have hh := hfacts t ht'
    have hw := hP_le_301 N hN ε hε hε1 p hp t ⟨hya.trans ht.1, ht.2⟩
    calc
      _ = hP N p t * (1 / (t * log t)) := by
        simp only [hP, one_div, mul_inv, mul_assoc, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hw
        (div_nonneg (by norm_num) (mul_pos hh.1 hh.2.1).le)
  rw [intervalIntegral.integral_const_mul, hint] at hmono
  have hgap := loglog_tail_gap_le N hN ε hε hε1 p hp
  change log (log b) - log (log a) ≤ 3 * ε / (2 * log N) at hgap
  have hgap' := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ (301 / 100 : ℝ) / log N)
  have hsmall : ((301 / 100 : ℝ) / log N) * (3 * ε / (2 * log N)) ≤ 5 * ε / log N ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < log (N : ℝ) ^ 2 by positivity)).mp
    field_simp
    nlinarith only [hε.le]
  exact hmono.trans (hgap'.trans hsmall)

/-- The endpoint error for the corrected tail, for Yamada page 26 eq 112. -/
theorem tail_endpoint_error_le (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1 / 100) (p : ℕ) (hp : p ∈ primesIco (z8 N) (y3 N)) :
    hP N p (wP N ε p) / (4 * log (√((N : ℝ) / p)) ^ 2) ≤ 7 / log N ^ 3 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log (N : ℝ) := (exp_pos _).trans hL
  have hpp : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
  have hylog : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hplog : log (p : ℝ) < log N / 3 := by
    have hh := log_lt_log hpp hpy
    rw [hylog] at hh
    exact hh
  have hq : 0 < (N : ℝ) / p := div_pos hNp hpp
  have ha : log (√((N : ℝ) / p)) = (log N - log p) / 2 := by
    rw [log_sqrt hq.le, log_div hNp.ne' hpp.ne']
  have hla : log N / 3 ≤ log (√((N : ℝ) / p)) := by rw [ha]; linarith
  have hlap : 0 < log (√((N : ℝ) / p)) := by linarith
  have hya : y3 N ≤ √((N : ℝ) / p) := by
    have hh : log (y3 N) ≤ log (√((N : ℝ) / p)) := by rw [hylog]; exact hla
    have he := exp_le_exp.mpr hh
    simpa only [exp_log (rpow_pos_of_pos hNp ((1 : ℝ) / 3)), exp_log (sqrt_pos_of_pos hq)] using he
  have hab : √((N : ℝ) / p) ≤ wP N ε p := by
    apply sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hpp.le
    nlinarith
  have hw := hP_le_301 N hN ε hε hε1 p hp (wP N ε p) ⟨hya.trans hab, le_rfl⟩
  have hrecip : 1 / (4 * log (√((N : ℝ) / p)) ^ 2) ≤ 9 / (4 * log N ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [sq_nonneg (log (√((N : ℝ) / p)) - log N / 3)]
  calc
    _ ≤ ((301 / 100 : ℝ) / log N) / (4 * log (√((N : ℝ) / p)) ^ 2) :=
      div_le_div_of_nonneg_right hw (by positivity)
    _ = ((301 / 100 : ℝ) / log N) * (1 / (4 * log (√((N : ℝ) / p)) ^ 2)) := by ring
    _ ≤ ((301 / 100 : ℝ) / log N) * (9 / (4 * log N ^ 2)) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ ≤ _ := by
      apply (mul_le_mul_iff_left₀ (show 0 < log (N : ℝ) ^ 3 by positivity)).mp
      field_simp
      norm_num

/-- LEAF. Unit U-1552. Yamada 2015, (109), first inequality, Section 7, proof of Lemma 7.3.
For `0 < ε < 1/100`, the blocks satisfy `Σ_j |B^(j)| ≤ Σ_{z ≤ p₁ < y} Σ_{y ≤ p₂ < w(p₁)}
π((1+ε)N/(p₁p₂))`: each `m = p₁p₂p₃` has `p₁p₂p₃ < (1+ε)N`, so `p₂ < w(p₁)` and
`p₃ ≤ (1+ε)N/(p₁p₂)`, and the block index is fixed by `p₁`. -/
theorem eq109_count (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) ≤
      ∑ p₁ ∈ primesIco (z8 N) (y3 N), ∑ p₂ ∈ primesIco (y3 N) (wP N ε p₁),
        (Nat.primeCounting ⌊(1 + ε) * N / (p₁ * p₂)⌋₊ : ℝ) := by
  classical
  let S := (range (Jblk N ε)).sigma (Bj N ε)
  let T := (primesIco (z8 N) (y3 N)).sigma fun p₁ =>
    (primesIco (y3 N) (wP N ε p₁)).sigma fun p₂ =>
      Nat.primesLE ⌊(1 + ε) * N / (p₁ * p₂)⌋₊
  have hwit : ∀ x ∈ S, ∃ p₁ p₂ p₃ : ℕ,
      p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z8 N ≤ p₁ ∧ (p₁ : ℝ) < y3 N ∧
      y3 N ≤ p₂ ∧ p₂ ≤ p₃ ∧ wj N ε x.1 * p₂ * p₃ < N ∧
      wj N ε x.1 ≤ p₁ ∧ (p₁ : ℝ) < (1 + ε) * wj N ε x.1 ∧ x.2 = p₁ * p₂ * p₃ := by
    intro x hx
    obtain ⟨hj, hm⟩ := mem_sigma.mp hx
    obtain ⟨_, p, q, r, hp, hq, hr, hzp, hpy, hyq, hqr, hprod, hcop, hlo, hhi, he⟩ := mem_filter.mp hm
    exact ⟨p, q, r, hp, hq, hr, hzp, hpy, hyq, hqr, hprod, hlo, hhi, he⟩
  choose p q r hp hq hr hzp hpy hyq hqr hprod hlo hhi he using hwit
  let f : S → T := fun x => ⟨⟨p x.1 x.2, ⟨q x.1 x.2, r x.1 x.2⟩⟩, by
    have hpp : (0 : ℝ) < p x.1 x.2 := by exact_mod_cast (hp x.1 x.2).pos
    have hqp : (0 : ℝ) < q x.1 x.2 := by exact_mod_cast (hq x.1 x.2).pos
    have hrp : (0 : ℝ) < r x.1 x.2 := by exact_mod_cast (hr x.1 x.2).pos
    have hbound : (p x.1 x.2 : ℝ) * q x.1 x.2 * r x.1 x.2 < (1 + ε) * N := by
      have hh := mul_lt_mul_of_pos_right (hhi x.1 x.2) (mul_pos hqp hrp)
      have hh2 := mul_lt_mul_of_pos_left (hprod x.1 x.2) (show 0 < 1 + ε by linarith)
      nlinarith
    have hqb : (q x.1 x.2 : ℝ) < wP N ε (p x.1 x.2) := by
      unfold wP
      apply (lt_sqrt (by positivity)).2
      apply (lt_div_iff₀ hpp).2
      have hqr' : (q x.1 x.2 : ℝ) ≤ r x.1 x.2 := by exact_mod_cast hqr x.1 x.2
      have hh := mul_le_mul_of_nonneg_left hqr' (mul_pos hpp hqp).le
      nlinarith only [hbound, hh]
    have hrb : r x.1 x.2 ≤ ⌊(1 + ε) * N / (p x.1 x.2 * q x.1 x.2)⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ (mul_pos hpp hqp)).2
      nlinarith
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr (hpy x.1 x.2)),
      hp x.1 x.2, hzp x.1 x.2⟩, mem_sigma.mpr ⟨mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_ceil.mpr hqb), hq x.1 x.2, hyq x.1 x.2⟩,
        Nat.mem_primesLE.mpr ⟨hrb, hr x.1 x.2⟩⟩⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hpq : p x.1 x.2 = p y.1 y.2 := by exact congrArg (fun z : T => z.1.1) hxy
    have hqq : q x.1 x.2 = q y.1 y.2 := by exact congrArg (fun z : T => z.1.2.1) hxy
    have hrq : r x.1 x.2 = r y.1 y.2 := by exact congrArg (fun z : T => z.1.2.2) hxy
    have hm : x.1.2 = y.1.2 := by rw [he x.1 x.2, he y.1 y.2, hpq, hqq, hrq]
    have hj : x.1.1 = y.1.1 := by
      by_contra hne
      have hb : 1 < 1 + ε := by linarith
      have hw (a b : ℕ) (hab : a < b) : (1 + ε) * wj N ε a ≤ wj N ε b := by
        unfold wj
        have hw := pow_le_pow_right₀ hb.le (show a + 1 ≤ b by omega)
        have hh := mul_le_mul_of_nonneg_left hw (rpow_nonneg (Nat.cast_nonneg N) ((1 : ℝ) / 8))
        simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh
      have hxlo := hlo x.1 x.2
      have hxhi := hhi x.1 x.2
      have hylo := hlo y.1 y.2
      have hyhi := hhi y.1 y.2
      rw [hpq] at hxlo hxhi
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hw _ _ hlt; linarith
      · have := hw _ _ hlt; linarith
    apply Subtype.ext
    exact Sigma.ext hj (by simpa only [heq_eq_eq] using hm)
  have hc := Finset.card_le_card_of_injective hinj
  have hc' : (S.card : ℝ) ≤ T.card := by exact_mod_cast hc
  simpa only [S, T, card_sigma, Nat.primesLE_card_eq_primeCounting, Nat.cast_sum] using hc'

/-- LEAF. Unit U-1552. Yamada 2015, (113), Section 7: for `N > exp exp 36` and a prime
`z ≤ p₁ < y`, `h_{p₁}((N/p₁)^{1/2}) / (4 log² y) ≤ 9(1 + e^{-50}) / (4 log² N)`.
Here `h_{p₁}((N/p₁)^{1/2}) = 2 / log(N/p₁) ≤ 3 / log N`. -/
theorem eq113 (N : ℕ) (hN : exp (exp 36) < N) (p₁ : ℕ) (hp₁ : p₁ ∈ primesIco (z8 N) (y3 N)) :
    hP N p₁ (√(N / p₁)) / (4 * log (y3 N) ^ 2) ≤ 9 * (1 + exp (-50)) / (4 * log N ^ 2) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log N := (exp_pos _).trans hL
  have hp := (mem_filter.mp hp₁).2
  have hp0 : (0 : ℝ) < p₁ := by exact_mod_cast hp.1.pos
  have hplt : (p₁ : ℝ) < y3 N := by
    have hh := (mem_range.mp (mem_filter.mp hp₁).1)
    exact (Nat.lt_ceil.mp hh)
  have hly : log (y3 N) = (1 / 3 : ℝ) * log N := log_rpow hNp _
  have hlp : log (p₁ : ℝ) < log N / 3 := by
    have := log_lt_log hp0 hplt
    rw [hly] at this
    linarith
  have hq : 0 < (N : ℝ) / p₁ := div_pos hNp hp0
  have hs : 0 < √((N : ℝ) / p₁) := sqrt_pos_of_pos hq
  have he : log (N / (p₁ * √(N / p₁))) = (log N - log p₁) / 2 := by
    rw [log_div hNp.ne' (mul_pos hp0 hs).ne', log_mul hp0.ne' hs.ne',
      log_sqrt hq.le, log_div hNp.ne' hp0.ne']
    ring
  have hd : 0 < log N - log (p₁ : ℝ) := by linarith
  unfold hP
  rw [he, hly]
  have hmain : 1 / ((log N - log (p₁ : ℝ)) / 2) ≤ 3 / log N := by
    apply (div_le_div_iff₀ (by positivity) hLp).2
    linarith
  have hsmall : 3 ≤ log (N : ℝ) := by
    have := add_one_le_exp (36 : ℝ)
    linarith
  have hbound : (3 / log (N : ℝ)) / (4 * ((1 / 3 : ℝ) * log N) ^ 2) ≤
      9 / (4 * log N ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    field_simp
    nlinarith [sq_nonneg (log (N : ℝ))]
  calc
    _ ≤ (3 / log (N : ℝ)) / (4 * ((1 / 3 : ℝ) * log N) ^ 2) :=
      div_le_div_of_nonneg_right hmain (by positivity)
    _ ≤ 9 / (4 * log N ^ 2) := hbound
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [exp_pos (-50 : ℝ)]

/-- LEAF. Unit U-1552. Yamada 2015, (115), Section 7, from (7):
for `N > exp exp 36`, `9(1 + e^{-50})/4 · Σ_{z ≤ p₁ < y} 1/p₁ ≤ 2.2069`; the sum is close to
`log(8/3) ≈ 0.98083`, and `9/4 · log(8/3) ≈ 2.20687`. -/
theorem eq115 (N : ℕ) (hN : exp (exp 36) < N) :
    9 * (1 + exp (-50)) / 4 * ∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 / (p₁ : ℝ)) ≤ 22069 / 10000 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have he36 : (10 ^ 12 : ℝ) < exp 36 := by
    have hh := pow_div_factorial_le_exp 36 (by norm_num : (0 : ℝ) ≤ 36) 18
    norm_num at hh
    linarith
  have hLp : 0 < log N := (exp_pos _).trans hL
  have hN1 : (1 : ℝ) < N := by
    have := add_one_le_exp (exp 36)
    have := exp_pos (36 : ℝ)
    linarith
  have hzlog : log (z8 N) = log N / 8 := by rw [log_rpow hNp]; ring
  have hylog : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hypos : 0 < y3 N := rpow_pos_of_pos hNp _
  have hzy : z8 N ≤ y3 N := rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  have hz8 : 8 ≤ z8 N := by
    have hh := add_one_le_exp (log (z8 N))
    rw [exp_log hzpos] at hh
    rw [hzlog] at hh
    linarith
  have hy1 : 1 ≤ y3 N := by linarith
  let A : ℕ := ⌊z8 N / 2⌋₊
  let B : ℕ := ⌈y3 N⌉₊
  have hAlo : z8 N / 4 ≤ (A : ℝ) := by
    have hh := Nat.lt_floor_add_one (z8 N / 2)
    change z8 N / 2 < (A : ℝ) + 1 at hh
    linarith
  have hAhi : (A : ℝ) ≤ z8 N / 2 := Nat.floor_le (by positivity)
  have hA2 : 2 ≤ A := by exact_mod_cast (show (2 : ℝ) ≤ A by linarith)
  have hAp : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hBlo : y3 N ≤ (B : ℝ) := Nat.le_ceil _
  have hBhi : (B : ℝ) ≤ 2 * y3 N := by
    have hh := Nat.ceil_lt_add_one hypos.le
    change (B : ℝ) < y3 N + 1 at hh
    linarith
  have hAB : A ≤ B := by exact_mod_cast (show (A : ℝ) ≤ B by linarith)
  have hlog4 : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num only [Nat.cast_ofNat]
    have := log_two_lt_d9
    linarith
  have hlogA : log N / 8 - 2 ≤ log (A : ℝ) := by
    have hh := log_le_log (div_pos hzpos (by norm_num)) hAlo
    rw [log_div hzpos.ne' (by norm_num), hzlog] at hh
    linarith
  have hlogB : log (B : ℝ) ≤ log N / 3 + 1 := by
    have hh := log_le_log (hypos.trans_le hBlo) hBhi
    rw [log_mul (by norm_num) hypos.ne', hylog] at hh
    have := log_two_lt_d9
    linarith
  have hla : 0 < log (A : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < A))
  have hlb : 0 < log (B : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < B))
  have hratio : log (B : ℝ) / log A ≤ (8 / 3 : ℝ) * (1 + 1 / 10 ^ 6) := by
    apply (div_le_iff₀ hla).2
    linarith
  have hlogratio : log (log B) - log (log A) ≤ log (8 / 3 : ℝ) + 1 / 10 ^ 6 := by
    rw [← log_div hlb.ne' hla.ne']
    have hh := log_le_log (div_pos hlb hla) hratio
    rw [log_mul (by norm_num) (by norm_num)] at hh
    have hh2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 10 ^ 6)
    linarith
  have herr : 14 / log (A : ℝ) ≤ 1 / 10 ^ 6 := by
    apply (div_le_iff₀ hla).2
    linarith
  have hsumle : ∑ p ∈ primesIco (z8 N) (y3 N), (1 / (p : ℝ)) ≤
      LeanLab.PNTSieve.Mertens.E B - LeanLab.PNTSieve.Mertens.E A := by
    have hsub : primesIco (z8 N) (y3 N) ⊆ (Ioc A B).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpr, hzp⟩ := (mem_filter.mp hp).2
      have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨?_, ?_⟩, hpr⟩
      · exact_mod_cast (show (A : ℝ) < p by linarith)
      · exact_mod_cast (show (p : ℝ) ≤ B by linarith)
    have hh := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity :
      ∀ p ∈ (Ioc A B).filter Nat.Prime, p ∉ primesIco (z8 N) (y3 N) → 0 ≤ 1 / (p : ℝ))
    have hsplit : Icc 1 B = Icc 1 A ∪ Ioc A B := by
      ext n
      simp only [mem_Icc, mem_union, mem_Ioc]
      omega
    have hd : Disjoint (Icc 1 A) (Ioc A B) := by
      apply disjoint_left.mpr
      intro n hn hm
      simp only [mem_Icc, mem_Ioc] at hn hm
      omega
    have hre : LeanLab.PNTSieve.Mertens.E B = LeanLab.PNTSieve.Mertens.E A +
        ∑ p ∈ (Ioc A B).filter Nat.Prime, (1 / (p : ℝ)) := by
      unfold LeanLab.PNTSieve.Mertens.E
      rw [hsplit, sum_union hd, sum_filter]
      congr 1
      apply sum_congr rfl
      intro p hp
      unfold LeanLab.PNTSieve.Mertens.c
      split_ifs with hpr
      · have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpr.one_lt)
        field_simp
      · simp
    linarith
  have hsum : ∑ p ∈ primesIco (z8 N) (y3 N), (1 / (p : ℝ)) ≤ (98084 / 100000 : ℝ) := by
    have hm := reciprocal_prime_block_le A B hA2 hAB
    have hlog : log (8 / 3 : ℝ) ≤ 98083 / 100000 := by
      apply (log_le_iff_le_exp (by norm_num)).2
      have hh := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 98083 / 100000) 11
      norm_num [Finset.sum_range_succ] at hh
      linarith
    linarith
  have he50 : (10 ^ 12 : ℝ) ≤ exp 50 := by
    have hh := pow_div_factorial_le_exp 50 (by norm_num : (0 : ℝ) ≤ 50) 14
    norm_num at hh
    linarith
  have hem50 : exp (-50 : ℝ) ≤ 1 / 10 ^ 12 := by
    rw [exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 ^ 12) he50
  have hc : 9 * (1 + exp (-50 : ℝ)) / 4 ≤ (9 : ℝ) * (1 + 1 / 10 ^ 12) / 4 := by linarith
  have hmul := mul_le_mul hsum hc (by positivity) (by norm_num : (0 : ℝ) ≤ 98084 / 100000)
  norm_num at hmul ⊢
  linarith

/-- LEAF. Unit U-1552. Yamada 2015, (111) and (116), Section 7: for `N > exp exp 36`,
`∫_z^y H(u) d log log u = (1/log N) ∫_{1/8}^{1/3} log(2 - 3β)/(β(1-β)) dβ`, by `u = N^α`,
`t = N^β` and (111), `H(N^α) = log(2 - 3α) / ((1-α) log N)`. -/
theorem eq116_integral (N : ℕ) (hN : exp (exp 36) < N) :
    (∫ u in z8 N..y3 N, H N u / (u * log u)) = I73 / log N := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  have hLp : 0 < log N := (exp_pos _).trans hL
  have hN1 : (1 : ℝ) < N := by
    have := add_one_le_exp (exp 36)
    have := exp_pos (36 : ℝ)
    linarith
  set L := log (N : ℝ) with hLdef
  have hz : log (z8 N) = L / 8 := by rw [log_rpow hNp]; ring
  have hy : log (y3 N) = L / 3 := by rw [log_rpow hNp]; ring
  have hzpos : 0 < z8 N := rpow_pos_of_pos hNp _
  have hzy : z8 N ≤ y3 N := rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  have hfacts : ∀ u ∈ Set.uIcc (z8 N) (y3 N),
      0 < u ∧ 1 / 8 ≤ log u / L ∧ log u / L ≤ 1 / 3 := by
    intro u hu
    rw [Set.uIcc_of_le hzy] at hu
    have hu0 := hzpos.trans_le hu.1
    have hlo := log_le_log hzpos hu.1
    have hhi := log_le_log hu0 hu.2
    rw [hz] at hlo
    rw [hy] at hhi
    exact ⟨hu0, (le_div_iff₀ hLp).2 (by linarith), (div_le_iff₀ hLp).2 (by linarith)⟩
  let g : ℝ → ℝ := fun β => log (2 - 3 * β) / (β * (1 - β))
  have hg : ContinuousOn g (Set.Icc (1 / 8) (1 / 3)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · fun_prop
      · intro β hβ
        have : 0 < 2 - 3 * β := by obtain ⟨_, h⟩ := hβ; linarith
        exact this.ne'
    · fun_prop
    · intro β hβ
      obtain ⟨hlo, hhi⟩ := hβ
      have : 0 < β := by linarith
      have : 0 < 1 - β := by linarith
      positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (f := fun u : ℝ => log u / L) (f' := fun u : ℝ => u⁻¹ / L) (g := g)
    (a := z8 N) (b := y3 N)
    (fun u hu => (hasDerivAt_log (hfacts u hu).1.ne').div_const L)
    ((continuousOn_inv₀.mono fun u hu => (hfacts u hu).1.ne').div_const L)
    (hg.mono (by
      rintro β ⟨u, hu, rfl⟩
      exact ⟨(hfacts u hu).2.1, (hfacts u hu).2.2⟩))
  have hze : log (z8 N) / L = (1 / 8 : ℝ) := by rw [hz]; field_simp
  have hye : log (y3 N) / L = (1 / 3 : ℝ) := by rw [hy]; field_simp
  rw [hze, hye] at hsub
  calc
    _ = ∫ u in z8 N..y3 N, (1 / L) * ((g ∘ (fun u : ℝ => log u / L)) u * (u⁻¹ / L)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      obtain ⟨hu0, hlo, hhi⟩ := hfacts u hu
      have he : (N : ℝ) ^ (log u / L) = u := by
        rw [rpow_def_of_pos hNp]
        have : log (N : ℝ) * (log u / L) = log u := by rw [← hLdef]; field_simp
        rw [this, exp_log hu0]
      have hH := H_rpow_eq N hN1 (log u / L) hhi
      rw [he, ← hLdef] at hH
      dsimp only
      rw [hH]
      dsimp [g, Function.comp_def]
      field_simp
    _ = (1 / L) * I73 := by rw [intervalIntegral.integral_const_mul, hsub]; rfl
    _ = _ := by dsimp [L]; ring

/-- LEAF. Unit U-1552. Yamada 2015, (111) at `α = 1/8`, CORRECTED value, finding F-0014:
for `N > exp exp 36`, `H(z) = (8/7) log(13/8) / log N`. The printed `log(26/21)/log N` is wrong;
the lab PROVED `H(z) ≥ (16/7) log(26/21) / log N` in Eq111.lean, `Hz_gt`. -/
theorem Hz_eq (N : ℕ) (hN : exp (exp 36) < N) :
    H N (z8 N) = 8 / 7 * log (13 / 8) / log N := by
  have hN1 : (1 : ℝ) < N := by
    have := add_one_le_exp (exp 36)
    have := exp_pos (36 : ℝ)
    linarith
  have hh := H_rpow_eq N hN1 (1 / 8) (by norm_num)
  change H N ((N : ℝ) ^ ((1 : ℝ) / 8)) = _
  rw [hh]
  norm_num
  ring

end LeanLab.ChenExplicit.D1552
