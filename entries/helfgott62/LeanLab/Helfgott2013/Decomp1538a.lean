module

public import Mathlib

/-!
# Lemma 6.1 of Helfgott's ternary Goldbach paper

H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Lemma 6.1 on page 46,
the summation by parts bound used in Section 6.1 to combine l2 bounds over arcs with l-infinity
bounds on the minor arcs. The paper's proof goes through display 6.2 and Abel summation 6.3 on
pages 46 to 47. Here the same chain uses running maxima, discrete summation by parts, a
rearrangement, and integrals of step functions over unit intervals.

Lab unit U-1538: Claude, Anthropic, an AI agent, wrote the statements and the skeleton of this
file. Later AI prover agents of the lab closed the leaves, as listed in PORTING.md. Checked only
by the Lean kernel; no human expert has reviewed it. Binary Goldbach is open. This file does not
formalize the ternary Goldbach theorem.

Encoding choices.
* `a b : ℕ`, sums over `Finset.Icc a b`; the paper has `a, b ∈ ℤ⁺`.
* `max_{n ≥ u} g(n)` over integers `u ≤ n ≤ b` is `hmax g b ⌈u⌉₊`, where `hmax` is the running
  maximum floored at `0`; for `g ≥ 0`, as in the paper, it is the plain maximum.
* "F continuous, piecewise differentiable, non-decreasing" is `NondecFTC F F' a b`: `F' ≥ 0` on
  `[a, b]`, `F'` integrable there, and `F y - F x = ∫_x^y F'`.
* Hypothesis 6.1 is asked only at integers `x = n ∈ [a, b]` in `lemma61`, which is weaker than
  the paper's hypothesis for all real `x`; `lemma61_paper` restates it with the paper's real `x`.
-/

@[expose] public section

namespace LeanLab.Helfgott2013.U1538

open Finset MeasureTheory intervalIntegral

/-- Running maximum of `g` over the integers `n, n+1, ..., b`, floored at `0`. For `n > b` it is
`0`. For `g ≥ 0` this is `max_{n ≤ m ≤ b} g(m)` of the paper, p. 46. -/
noncomputable def hmax (g : ℕ → ℝ) (b n : ℕ) : ℝ := (Finset.Icc n b).fold max 0 g

/-- `F` is non-decreasing and absolutely continuous on `[a, b]` with density `F' ≥ 0`: the
encoding of "continuous, piecewise differentiable and non-decreasing" in Lemma 6.1, p. 46, and
Prop. 6.2, p. 47. -/
def NondecFTC (F F' : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ u ∈ Set.Icc a b, 0 ≤ F' u) ∧ IntervalIntegrable F' volume a b ∧
    ∀ x y, a ≤ x → x ≤ y → y ≤ b → F y - F x = ∫ u in x..y, F' u

/-! ### Auxiliary lemmas -/

/-- The running maximum `hmax g b n` is nonnegative, since the fold starts
at `0`; p. 46, the function `h` in the proof of Lemma 6.1. -/
theorem hmax_nonneg (g : ℕ → ℝ) (b n : ℕ) : 0 ≤ hmax g b n := by
  dsimp [hmax]
  rw [Finset.le_fold_max]
  left
  rfl

/-- Every value `g m` with `n ≤ m ≤ b` is at most `hmax g b n`; p. 46, proof
of Lemma 6.1, `h(x) = max_{x ≤ n ≤ b} g(n)`. -/
theorem le_hmax (g : ℕ → ℝ) {b n m : ℕ} (h1 : n ≤ m) (h2 : m ≤ b) : g m ≤ hmax g b n := by
  dsimp [hmax]
  rw [Finset.le_fold_max]
  right
  use m
  refine ⟨?_, le_rfl⟩
  rw [Finset.mem_Icc]
  exact ⟨h1, h2⟩

/-- The running maximum is non-increasing in its start point: `n ≤ n'`
gives `hmax g b n' ≤ hmax g b n`; p. 46, "Then h is non-increasing". -/
theorem hmax_anti (g : ℕ → ℝ) {b n n' : ℕ} (h : n ≤ n') : hmax g b n' ≤ hmax g b n := by
  dsimp [hmax]
  have H : Icc n' b ⊆ Icc n b := Icc_subset_Icc h le_rfl
  rcases Finset.le_fold_max (c := fold max 0 g (Icc n' b)) |>.mp le_rfl with h0 | ⟨x, hx, hg⟩
  · rw [Finset.le_fold_max]
    left; exact h0
  · rw [Finset.le_fold_max]
    right
    use x
    exact ⟨H hx, hg⟩

/-- For `f ≥ 0`, replacing `g n` by the running maximum `hmax g b n`
does not decrease `∑_{a ≤ n ≤ b} f(n) g(n)`; p. 46, first inequality of the display after
display 6.2. -/
theorem sum_mul_le_sum_mul_hmax (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (a b : ℕ) :
    ∑ n ∈ Icc a b, f n * g n ≤ ∑ n ∈ Icc a b, f n * hmax g b n := by
  apply sum_le_sum
  intro n hn
  rw [mem_Icc] at hn
  apply mul_le_mul_of_nonneg_left
  · exact le_hmax g le_rfl hn.2
  · exact hf n

/-- Discrete summation by parts, an identity: with `S(n) = ∑_{a ≤ m ≤ n} f(m)`,
`∑_{n=a}^{b} f(n) h(n) = S(b) h(b) + ∑_{n=a}^{b-1} S(n) (h(n) - h(n+1))` for `a ≤ b`;
p. 46, display display 6.2, here with equality. -/
theorem sum_by_parts (f h : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc a b, f n * h n =
      (∑ m ∈ Icc a b, f m) * h b + ∑ n ∈ Ico a b, (∑ m ∈ Icc a n, f m) * (h n - h (n + 1)) := by
  induction' b, hab using Nat.le_induction with k hk ih
  · rw [Icc_self, Ico_self, sum_singleton, sum_singleton, sum_empty, add_zero]
  · have h1 : a ≤ k + 1 := le_trans hk (Nat.le_succ k)
    rw [sum_Icc_succ_top h1, ih, sum_Icc_succ_top h1, sum_Ico_succ_top hk]
    ring

/-- Monotone replacement in the summation by parts: if `S(n) ≤ F(n)` on
`[a, b]`, `h` is non-increasing on `[a, b]` and `h(b) ≥ 0`, then
`S(b)h(b) + ∑_{n=a}^{b-1} S(n)(h(n) - h(n+1)) ≤ F(b)h(b) + ∑_{n=a}^{b-1} F(n)(h(n) - h(n+1))`;
p. 46, last inequality of the display after display 6.2. -/
theorem by_parts_mono (S F h : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hS : ∀ n ∈ Icc a b, S n ≤ F n) (hh : ∀ n ∈ Ico a b, h (n + 1) ≤ h n) (hb : 0 ≤ h b) :
    S b * h b + ∑ n ∈ Ico a b, S n * (h n - h (n + 1)) ≤
      F b * h b + ∑ n ∈ Ico a b, F n * (h n - h (n + 1)) := by
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact hS b (by rw [mem_Icc]; exact ⟨hab, le_rfl⟩)
    · exact hb
  · apply sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_right
    · exact hS n (Ico_subset_Icc_self hn)
    · linarith [hh n hn]

/-- Rearrangement, an identity for `a ≤ b`:
`F(b)h(b) + ∑_{n=a}^{b-1} F(n)(h(n) - h(n+1)) = h(a)F(a) + ∑_{n=a}^{b-1} h(n+1)(F(n+1) - F(n))`;
p. 47, the Abel summation step display 6.3 in its discrete form. -/
theorem by_parts_rearrange (F h : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    F b * h b + ∑ n ∈ Ico a b, F n * (h n - h (n + 1)) =
      h a * F a + ∑ n ∈ Ico a b, h (n + 1) * (F (n + 1) - F n) := by
  induction' b, hab using Nat.le_induction with k hk ih
  · rw [Ico_self, sum_empty, sum_empty, add_zero, add_zero, mul_comm]
  · rw [sum_Ico_succ_top hk, sum_Ico_succ_top hk]
    calc F (k + 1) * h (k + 1) + (∑ n ∈ Ico a k, F n * (h n - h (n + 1)) + F k * (h k - h (k + 1)))
      _ = (F (k + 1) * h (k + 1) + F k * (h k - h (k + 1))) - F k * h k + (F k * h k + ∑ n ∈ Ico a k, F n * (h n - h (n + 1))) := by ring
      _ = (F (k + 1) * h (k + 1) + F k * (h k - h (k + 1))) - F k * h k + (h a * F a + ∑ n ∈ Ico a k, h (n + 1) * (F (n + 1) - F n)) := by rw [ih]
      _ = h a * F a + (∑ n ∈ Ico a k, h (n + 1) * (F (n + 1) - F n) + h (k + 1) * (F (k + 1) - F k)) := by ring

/-- On the unit interval `(n, n+1]` the ceiling is `n + 1`; p. 47,
"since `h(⌊u⌋ + 1) = h(u)` for `u ∉ ℤ`". -/
theorem ceil_eq_of_mem_Ioc (n : ℕ) {u : ℝ} (hu : u ∈ Set.Ioc (n : ℝ) (n + 1)) :
    ⌈u⌉₊ = n + 1 := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    push_cast
    exact hu.2
  · by_contra h
    push Not at h
    have h1 : ⌈u⌉₊ ≤ n := Nat.le_of_lt_succ h
    have h2 : u ≤ n := Nat.ceil_le.mp h1
    exact not_le_of_gt hu.1 h2

/-- On `[n, n+1]` the step function `φ(⌈u⌉)` may be replaced by the constant
`φ(n+1)` inside the integral, since they agree off the single point `u = n`; p. 47, the step
from `h(⌊u⌋ + 1)` to `h(u)`. -/
theorem integral_unit_step (φ : ℕ → ℝ) (F' : ℝ → ℝ) (n : ℕ) :
    ∫ u in (n : ℝ)..(n + 1), φ ⌈u⌉₊ * F' u = ∫ u in (n : ℝ)..(n + 1), φ (n + 1) * F' u := by
  apply intervalIntegral.integral_congr_ae
  have H : ∀ u, u ∈ Set.Ioc (n : ℝ) (n + 1) → φ ⌈u⌉₊ * F' u = φ (n + 1) * F' u := by
    intro u hu
    rw [ceil_eq_of_mem_Ioc n hu]
  have H2 : ∀ u, u ∈ Set.uIoc (n : ℝ) (n + 1) → φ ⌈u⌉₊ * F' u = φ (n + 1) * F' u := by
    rw [Set.uIoc_of_le (by linarith)]
    exact H
  exact ae_of_all _ H2

/-- With `F' ` a density of `F` on `[a, b]` and `a ≤ n`, `n + 1 ≤ b`:
`∫_n^{n+1} c F'(u) du = c (F(n+1) - F(n))`; p. 47, last lines of the proof of Lemma 6.1. -/
theorem integral_const_mul_unit (F F' : ℝ → ℝ) {a b : ℝ} (hF : NondecFTC F F' a b) (c : ℝ)
    (n : ℕ) (han : a ≤ n) (hnb : (n : ℝ) + 1 ≤ b) :
    ∫ u in (n : ℝ)..(n + 1), c * F' u = c * (F (n + 1) - F n) := by
  rw [intervalIntegral.integral_const_mul, ← hF.2.2]
  · exact han
  · linarith
  · exact hnb

/-- Adjacent unit intervals add up: for `φ` integrable on `[a, b]`,
`∑_{n=a}^{b-1} ∫_n^{n+1} φ = ∫_a^b φ`; p. 47, the integral `∫_a^b h(u) F'(u) du`. -/
theorem sum_integral_unit (φ : ℝ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hφ : IntervalIntegrable φ volume (a : ℝ) b) :
    ∑ n ∈ Ico a b, ∫ u in (n : ℝ)..(n + 1), φ u = ∫ u in (a : ℝ)..b, φ u := by
  induction' b, hab using Nat.le_induction with k hk ih
  · rw [Ico_self, sum_empty, integral_same]
  · have hk1 : (a : ℝ) ≤ k := by exact_mod_cast hk
    have hk2 : (a : ℝ) ≤ ↑(k + 1) := by exact_mod_cast (le_trans hk (Nat.le_succ k))
    have h_a_k1 : Set.uIcc (a : ℝ) k = Set.Icc (a : ℝ) k := Set.uIcc_of_le hk1
    have h_a_k2 : Set.uIcc (a : ℝ) ↑(k + 1) = Set.Icc (a : ℝ) ↑(k + 1) := Set.uIcc_of_le hk2
    have h_k_k1 : Set.uIcc (k : ℝ) ↑(k + 1) = Set.Icc (k : ℝ) ↑(k + 1) := Set.uIcc_of_le (by exact_mod_cast Nat.le_succ k)
    have h1 : IntervalIntegrable φ volume (a : ℝ) k := by
      refine IntervalIntegrable.mono_set hφ ?_
      rw [h_a_k1, h_a_k2]
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast Nat.le_succ k)
    have h2 : IntervalIntegrable φ volume (k : ℝ) ↑(k + 1) := by
      refine IntervalIntegrable.mono_set hφ ?_
      rw [h_k_k1, h_a_k2]
      exact Set.Icc_subset_Icc hk1 le_rfl
    rw [sum_Ico_succ_top hk, ih h1]
    have H : (k : ℝ) + 1 = ↑(k + 1) := by push_cast; rfl
    rw [H]
    exact integral_add_adjacent_intervals h1 h2

/-- A step function `φ(⌈u⌉)` times an integrable `F'` is integrable on a
bounded interval, since on it `⌈u⌉` takes finitely many values; p. 46, the integrand
`(max_{n ≥ u} g(n)) F'(u)` of Lemma 6.1. -/
theorem intervalIntegrable_ceil_mul (φ : ℕ → ℝ) (F' : ℝ → ℝ) {a b : ℝ}
    (hF' : IntervalIntegrable F' volume a b) :
    IntervalIntegrable (fun u => φ ⌈u⌉₊ * F' u) volume a b := by
  have H_meas1 : AEStronglyMeasurable (fun u : ℝ => φ ⌈u⌉₊) (volume.restrict (Set.Ioc a b)) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.comp (measurable_of_countable _) (Measurable.nat_ceil measurable_id)
  have H_meas2 : AEStronglyMeasurable (fun u : ℝ => φ ⌈u⌉₊) (volume.restrict (Set.Ioc b a)) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.comp (measurable_of_countable _) (Measurable.nat_ceil measurable_id)
  let S := (Set.Icc ⌈min a b⌉₊ ⌈max a b⌉₊).image (fun x => ‖φ x‖)
  have H_fin : S.Finite := Set.Finite.image _ (Set.finite_Icc _ _)
  rcases Set.Finite.bddAbove H_fin with ⟨c, hc⟩
  constructor
  · apply MeasureTheory.Integrable.bdd_mul hF'.1 H_meas1 (c := c)
    rw [ae_restrict_iff']
    · apply ae_of_all
      intro u hu
      apply hc
      apply Set.mem_image_of_mem
      rw [Set.mem_Icc]
      constructor
      · exact Nat.ceil_mono (by linarith [hu.1, min_le_left a b])
      · exact Nat.ceil_mono (by linarith [hu.2, le_max_right a b])
    · exact measurableSet_Ioc
  · apply MeasureTheory.Integrable.bdd_mul hF'.2 H_meas2 (c := c)
    rw [ae_restrict_iff']
    · apply ae_of_all
      intro u hu
      apply hc
      apply Set.mem_image_of_mem
      rw [Set.mem_Icc]
      constructor
      · exact Nat.ceil_mono (by linarith [hu.1, min_le_right a b])
      · exact Nat.ceil_mono (by linarith [hu.2, le_max_left a b])
    · exact measurableSet_Ioc

/-! ### Main statements -/

/-- One unit interval of the Abel step:
`hmax(n+1)(F(n+1) - F(n)) = ∫_n^{n+1} hmax(⌈u⌉) F'(u) du`; p. 47. -/
theorem unit_term (g : ℕ → ℝ) (F F' : ℝ → ℝ) {a b : ℕ} (hF : NondecFTC F F' a b) (n : ℕ)
    (hn : n ∈ Ico a b) :
    hmax g b (n + 1) * (F ((n + 1 : ℕ) : ℝ) - F (n : ℝ)) =
      ∫ u in (n : ℝ)..(n + 1), hmax g b ⌈u⌉₊ * F' u := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
  have han : (a : ℝ) ≤ n := by exact_mod_cast h1
  have hnb : (n : ℝ) + 1 ≤ b := by exact_mod_cast h2
  rw [integral_unit_step (hmax g b) F' n, integral_const_mul_unit F F' hF _ n han hnb]
  push_cast
  ring

/-- Lemma 6.1, p. 46: for `f, g ≥ 0` on
`{a, ..., b}` and `F` non-decreasing with density `F'` on `[a, b]`, if
`∑_{a ≤ m ≤ n} f(m) ≤ F(n)` for every integer `n ∈ [a, b]`, then
`∑_{n=a}^{b} f(n) g(n) ≤ (max_{n ≥ a} g(n)) F(a) + ∫_a^b (max_{n ≥ u} g(n)) F'(u) du`. -/
theorem lemma61 {a b : ℕ} (hab : a ≤ b) (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (_hg : ∀ n ∈ Icc a b, 0 ≤ g n) (F F' : ℝ → ℝ) (hF : NondecFTC F F' a b)
    (h61 : ∀ n ∈ Icc a b, ∑ m ∈ Icc a n, f m ≤ F n) :
    ∑ n ∈ Icc a b, f n * g n ≤
      hmax g b a * F a + ∫ u in (a : ℝ)..b, hmax g b ⌈u⌉₊ * F' u := by
  set h : ℕ → ℝ := hmax g b with hh
  have step1 := sum_mul_le_sum_mul_hmax f g hf a b
  rw [sum_by_parts f h hab] at step1
  have step2 := by_parts_mono (fun n => ∑ m ∈ Icc a n, f m) (fun n => F n) h hab h61
    (fun n _ => hmax_anti g (Nat.le_succ n)) (hmax_nonneg g b b)
  rw [by_parts_rearrange (fun n => F n) h hab] at step2
  have step3 : ∑ n ∈ Ico a b, h (n + 1) * (F ((n + 1 : ℕ) : ℝ) - F (n : ℝ)) =
      ∫ u in (a : ℝ)..b, h ⌈u⌉₊ * F' u := by
    rw [← sum_integral_unit _ hab (intervalIntegrable_ceil_mul h F' hF.2.1)]
    exact Finset.sum_congr rfl fun n hn => unit_term g F F' hF n hn
  have := le_trans step1 step2
  rw [step3] at this
  exact this

/-- Lemma 6.1 with hypothesis display 6.1 exactly
as on p. 46, for every real `x ∈ [a, b]`: `∑_{a ≤ n ≤ x} f(n) ≤ F(x)`. -/
theorem lemma61_paper {a b : ℕ} (hab : a ≤ b) (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hg : ∀ n ∈ Icc a b, 0 ≤ g n) (F F' : ℝ → ℝ) (hF : NondecFTC F F' a b)
    (h61 : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → ∑ m ∈ Icc a ⌊x⌋₊, f m ≤ F x) :
    ∑ n ∈ Icc a b, f n * g n ≤
      hmax g b a * F a + ∫ u in (a : ℝ)..b, hmax g b ⌈u⌉₊ * F' u := by
  refine lemma61 hab f g hf hg F F' hF fun n hn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have := h61 n (by exact_mod_cast h1) (by exact_mod_cast h2)
  rwa [Nat.floor_natCast] at this

end LeanLab.Helfgott2013.U1538
