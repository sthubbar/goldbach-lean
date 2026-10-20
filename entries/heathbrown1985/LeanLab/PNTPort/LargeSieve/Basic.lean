module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Field.GeomSum

/-!
# The analytic large sieve inequality

Lab proof, unit U-5000. AI wrote this file. Known mathematics, a weak constant form of the
large sieve of Linnik, Renyi, Roth, Bombieri, Davenport and Halberstam. No cited input.

For points `α r`, `r ∈ s`, pairwise at distance at least `δ` modulo one, and any complex
`a n` on `M < n ≤ M + N`,

  `∑ r, ‖∑ n, a n e(n α r)‖² ≤ (N + 2/δ) ∑ n, ‖a n‖²`.

The proof is the dual form with a Fejer type majorant: average the interval sum over `L`
shifts of a longer interval, so the kernel is a product of two geometric sums, each at most
`1/(2‖θ‖)`; then sum `1/‖θ‖²` over the spaced points by an injective floor map. The sharp
constant `N - 1 + 1/δ` is not needed for Bombieri-Vinogradov type uses.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

/-- `e x = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (I * ((2 * π * x : ℝ) : ℂ))

/-- Distance from `x` to the nearest integer. -/
noncomputable def dist0 (x : ℝ) : ℝ := |x - round x|

lemma dist0_nonneg (x : ℝ) : 0 ≤ dist0 x := abs_nonneg _

lemma dist0_le_half (x : ℝ) : dist0 x ≤ 1 / 2 := abs_sub_round x

lemma dist0_le_abs_sub_int (x : ℝ) (z : ℤ) : dist0 x ≤ |x - z| := round_le x z

lemma dist0_neg (x : ℝ) : dist0 (-x) = dist0 x := by
  apply le_antisymm
  · have := dist0_le_abs_sub_int (-x) (-round x)
    rw [show (-x - ((-round x : ℤ) : ℝ)) = -(x - round x) by push_cast; ring, abs_neg] at this
    exact this
  · have := dist0_le_abs_sub_int x (-round (-x))
    rw [show (x - ((-round (-x) : ℤ) : ℝ)) = -(-x - round (-x)) by push_cast; ring,
      abs_neg] at this
    exact this

lemma dist0_sub_comm (x y : ℝ) : dist0 (x - y) = dist0 (y - x) := by
  rw [← dist0_neg, neg_sub]

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma e_int (z : ℤ) : e z = 1 := by
  unfold e
  rw [show I * ((2 * π * (z : ℝ) : ℝ) : ℂ) = (z : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

lemma e_sub_round (x : ℝ) : e (x - round x) = e x := by
  rw [sub_eq_add_neg, e_add, show (-(round x : ℝ)) = ((-round x : ℤ) : ℝ) by push_cast; ring,
    e_int, mul_one]

lemma e_nat_mul (k : ℕ) (x : ℝ) : e (k * x) = e x ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `|sin(πt)| ≥ 2|t|` for `|t| ≤ 1/2`. -/
lemma two_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ 1 / 2) : 2 * |t| ≤ |Real.sin (π * t)| := by
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → 2 * u ≤ Real.sin (π * u) := by
    intro u hu0 hu1
    have h1 := Real.mul_le_sin (x := π * u) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * u) = 2 * u := by field_simp
    linarith
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact (key t h ht).trans (le_abs_self _)
  · rw [abs_of_neg h] at ht ⊢
    have := key (-t) (by linarith) ht
    rw [show π * -t = -(π * t) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

lemma four_dist0_le (θ : ℝ) : 4 * dist0 θ ≤ ‖e θ - 1‖ := by
  rw [← e_sub_round]
  set t := θ - round θ with ht
  have hb : |t| ≤ 1 / 2 := abs_sub_round θ
  unfold e
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have := two_abs_le_abs_sin hb
  rw [show 2 * π * t / 2 = π * t by ring]
  unfold dist0
  rw [← ht]
  linarith

/-- The geometric sum bound `|∑_{k<m} e(kθ)| ≤ 1/(2‖θ‖)`. -/
lemma norm_geom_le (m : ℕ) {θ : ℝ} (h : 0 < dist0 θ) :
    ‖∑ k ∈ range m, e (k * θ)‖ ≤ 1 / (2 * dist0 θ) := by
  have hpos : 0 < ‖e θ - 1‖ := lt_of_lt_of_le (by linarith) (four_dist0_le θ)
  have hne : e θ ≠ 1 := by
    intro h1; rw [h1, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  simp_rw [e_nat_mul]
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖e θ ^ m - 1‖ ≤ 2 := by
    calc ‖e θ ^ m - 1‖ ≤ ‖e θ ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  calc ‖e θ ^ m - 1‖ / ‖e θ - 1‖ ≤ 2 / ‖e θ - 1‖ :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ ≤ 2 / (4 * dist0 θ) := div_le_div_of_nonneg_left (by norm_num) (by linarith)
        (four_dist0_le θ)
    _ = 1 / (2 * dist0 θ) := by field_simp; ring

/-- Sum of `1/t²` over a `δ`-separated set of reals that are at least `δ`. -/
lemma sum_inv_sq_sep {ι : Type*} (T : Finset ι) (t : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ i ∈ T, δ ≤ t i)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |t i - t j|) :
    ∑ i ∈ T, 1 / t i ^ 2 ≤ 2 / δ ^ 2 := by
  set k : ι → ℕ := fun i => ⌊t i / δ⌋₊ with hk
  have hk1 : ∀ i ∈ T, 1 ≤ k i := by
    intro i hi
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ, one_mul]; exact hpos i hi)
  have hkle : ∀ i ∈ T, (k i : ℝ) * δ ≤ t i := by
    intro i hi
    have := Nat.floor_le (div_nonneg (hδ.le.trans (hpos i hi)) hδ.le)
    exact (le_div_iff₀ hδ).1 this
  have hinj : Set.InjOn k T := by
    intro i hi j hj hij
    by_contra hne
    have hs := hsep i hi j hj hne
    have hi0 : 0 ≤ t i / δ := div_nonneg (hδ.le.trans (hpos i hi)) hδ.le
    have hj0 : 0 ≤ t j / δ := div_nonneg (hδ.le.trans (hpos j hj)) hδ.le
    have a1 := Nat.floor_le hi0
    have a2 := Nat.lt_floor_add_one (t i / δ)
    have b1 := Nat.floor_le hj0
    have b2 := Nat.lt_floor_add_one (t j / δ)
    have hij' : (⌊t i / δ⌋₊ : ℝ) = ⌊t j / δ⌋₊ := by exact_mod_cast hij
    have : |t i / δ - t j / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
    linarith
  have step1 : ∑ i ∈ T, 1 / t i ^ 2 ≤ ∑ i ∈ T, (1 / δ ^ 2) * (((k i : ℕ) : ℝ) ^ 2)⁻¹ := by
    apply sum_le_sum
    intro i hi
    have hk0 : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
    rw [← one_div, one_div_mul_one_div, ← mul_pow, mul_comm δ]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (hkle i hi) 2
  have step2 : ∑ i ∈ T, (((k i : ℕ) : ℝ) ^ 2)⁻¹ = ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ :=
    (sum_image (f := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) hinj).symm
  set K := (T.image k).sup id
  have hsub : T.image k ⊆ Ioo 0 (K + 1) := by
    intro j hj
    rw [mem_Ioo]
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
    exact ⟨hk1 i hi, Nat.lt_succ_of_le (le_sup (f := id) hj)⟩
  have step3 : ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ ≤ ∑ j ∈ Ioo 0 (K + 1), ((j : ℝ) ^ 2)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have step4 := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
  rw [← mul_sum, step2] at step1
  calc ∑ i ∈ T, 1 / t i ^ 2 ≤ 1 / δ ^ 2 * ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ := step1
    _ ≤ 1 / δ ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (2 : ℝ) / ((0 : ℕ) + 1) = 2 := by norm_num
        linarith
    _ = 2 / δ ^ 2 := by ring

/-- Points pairwise at distance at least `δ` modulo one. -/
def Spaced {ι : Type*} (s : Finset ι) (α : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ dist0 (α r - α r')

/-- For `δ`-spaced points, `∑_{r' ≠ r} 1/‖α r - α r'‖² ≤ 4/δ²`. -/
lemma sum_off_diag {ι : Type*} [DecidableEq ι] {s : Finset ι} {α : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hs : Spaced s α δ) {r : ι} (hr : r ∈ s) :
    ∑ r' ∈ s.erase r, 1 / dist0 (α r - α r') ^ 2 ≤ 4 / δ ^ 2 := by
  set t : ι → ℝ := fun r' => α r' - α r - round (α r' - α r) with ht
  have hdt : ∀ r', dist0 (α r - α r') = |t r'| := by
    intro r'; rw [dist0_sub_comm]; rfl
  have hge : ∀ r' ∈ s.erase r, δ ≤ |t r'| := by
    intro r' hr'
    rw [← hdt]
    exact hs r hr r' (mem_of_mem_erase hr') (ne_of_mem_erase hr').symm
  have hsep : ∀ r1 ∈ s.erase r, ∀ r2 ∈ s.erase r, r1 ≠ r2 → δ ≤ |t r1 - t r2| := by
    intro r1 h1 r2 h2 hne
    have := hs r1 (mem_of_mem_erase h1) r2 (mem_of_mem_erase h2) hne
    refine this.trans ?_
    have h := dist0_le_abs_sub_int (α r1 - α r2)
      (round (α r1 - α r) - round (α r2 - α r))
    convert h using 2
    simp only [ht]
    push_cast
    ring
  rw [← sum_filter_add_sum_filter_not (s.erase r) (fun r' => 0 < t r')]
  have hP : ∑ r' ∈ (s.erase r).filter (fun r' => 0 < t r'), 1 / dist0 (α r - α r') ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((s.erase r).filter (fun r' => 0 < t r')) t hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have := hge i hi.1
        rwa [abs_of_pos hi.2] at this)
      (by
        intro i hi j hj hne
        exact hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne)
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs]
  have hN : ∑ r' ∈ (s.erase r).filter (fun r' => ¬ 0 < t r'), 1 / dist0 (α r - α r') ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((s.erase r).filter (fun r' => ¬ 0 < t r')) (fun r' => -t r') hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have h1 := hge i hi.1
        have h2 : t i ≤ 0 := not_lt.1 hi.2
        rw [abs_of_nonpos h2] at h1
        exact h1)
      (by
        intro i hi j hj hne
        have := hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne
        rwa [show -t i - -t j = -(t i - t j) by ring, abs_neg])
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs, neg_sq]
  calc _ ≤ 2 / δ ^ 2 + 2 / δ ^ 2 := add_le_add hP hN
    _ = 4 / δ ^ 2 := by ring

end LeanLab.PNTPort.LargeSieve
