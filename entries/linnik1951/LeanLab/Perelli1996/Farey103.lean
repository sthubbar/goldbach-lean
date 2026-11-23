module

public import LeanLab.Perelli1996.Definitions103

/-!
P0083 Perelli 1996, page 483 equations 12 through 14.
A direct two interval covering argument for the enlarged rational arcs.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Farey103
open Finset Real Polynomial MeasureTheory
noncomputable section

/-- Dirichlet approximation with a real order and a strict enclosing radius. -/
theorem dirichlet_real_order (x Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ a : ℤ,
      Nat.Coprime a.natAbs q ∧ |x - (a : ℝ) / q| < 1 / ((q : ℝ) * Q) := by
  have hQ0 : 0 < Q := by linarith
  have hn : 0 < ⌊Q⌋₊ := by
    have : 1 ≤ ⌊Q⌋₊ := (Nat.le_floor_iff hQ0.le).mpr (by simpa using hQ)
    omega
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hn
  refine ⟨r.den, r.den_pos, ?_, r.num, r.reduced, ?_⟩
  · exact (show (r.den : ℝ) ≤ ⌊Q⌋₊ by exact_mod_cast hden).trans (Nat.floor_le hQ0.le)
  · rw [Rat.cast_def] at hr
    refine hr.trans_lt ?_
    have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    apply one_div_lt_one_div_of_lt (by positivity)
    have hfloor := Nat.lt_floor_add_one Q
    nlinarith

/-- A finite cover by intervals longer than the query has a two interval subcover. -/
theorem two_interval_subcover {ι : Type*} (s : Finset ι) (left right : ι → ℝ)
    {x y : ℝ} (hxy : x ≤ y)
    (hwidth : ∀ i ∈ s, y - x < right i - left i)
    (hcover : ∀ z ∈ Set.Icc x y, ∃ i ∈ s, z ∈ Set.Icc (left i) (right i)) :
    ∃ i ∈ s, ∃ j ∈ s,
      Set.Icc x y ⊆ Set.Icc (left i) (right i) ∪ Set.Icc (left j) (right j) := by
  classical
  let a := s.filter (fun i => x ∈ Set.Icc (left i) (right i))
  let b := s.filter (fun i => y ∈ Set.Icc (left i) (right i))
  have ha : a.Nonempty := by
    obtain ⟨i, hi, hx⟩ := hcover x ⟨le_rfl, hxy⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩⟩
  have hb : b.Nonempty := by
    obtain ⟨i, hi, hy⟩ := hcover y ⟨hxy, le_rfl⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hy⟩⟩
  obtain ⟨i, hi, hmax⟩ := a.exists_max_image right ha
  obtain ⟨j, hj, hmin⟩ := b.exists_min_image left hb
  obtain ⟨his, hix⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjs, hjy⟩ := Finset.mem_filter.mp hj
  refine ⟨i, his, j, hjs, ?_⟩
  intro z hz
  by_cases hzi : z ≤ right i
  · exact Or.inl ⟨hix.1.trans hz.1, hzi⟩
  · obtain ⟨k, hks, hzk⟩ := hcover z hz
    have hkleft : x < left k := by
      by_contra hnot
      have hka : k ∈ a := Finset.mem_filter.mpr ⟨hks, le_of_not_gt hnot, hz.1.trans hzk.2⟩
      have := hmax k hka
      linarith [hzk.2]
    have hkright : y ≤ right k := by have := hwidth k hks; linarith
    have hkb : k ∈ b := Finset.mem_filter.mpr ⟨hks, hzk.1.trans hz.2, hkright⟩
    exact Or.inr ⟨(hmin k hkb).trans hzk.1, hz.2.trans hjy.2⟩

/-- Every sufficiently short real interval is covered by two rational arcs of order Q. -/
theorem rational_two_cover (t Q : ℝ) (hQ : 2 ≤ Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ a : ℤ, Nat.Coprime a.natAbs q ∧
    ∃ r : ℕ, 0 < r ∧ (r : ℝ) ≤ Q ∧ ∃ b : ℤ, Nat.Coprime b.natAbs r ∧
      Set.Icc t (t + 1 / (4 * Q ^ 2)) ⊆
        Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * Q)) ((a : ℝ) / q + 1 / ((q : ℝ) * Q)) ∪
        Set.Icc ((b : ℝ) / r - 1 / ((r : ℝ) * Q)) ((b : ℝ) / r + 1 / ((r : ℝ) * Q)) := by
  let ι := {p : ℕ × ℤ // 0 < p.1 ∧ (p.1 : ℝ) ≤ Q ∧ Nat.Coprime p.2.natAbs p.1}
  let left (i : ι) := (i.1.2 : ℝ) / i.1.1 - 1 / ((i.1.1 : ℝ) * Q)
  let right (i : ι) := (i.1.2 : ℝ) / i.1.1 + 1 / ((i.1.1 : ℝ) * Q)
  have hQ0 : 0 < Q := by linarith
  have hcover : Set.Icc t (t + 1 / (4 * Q ^ 2)) ⊆ ⋃ i : ι, Set.Ioo (left i) (right i) := by
    intro x hx
    obtain ⟨q, hq, hqQ, a, hcop, happ⟩ := dirichlet_real_order x Q (by linarith)
    refine Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hqQ, hcop⟩, ?_⟩
    dsimp [left, right]
    rw [abs_lt] at happ
    constructor <;> linarith [happ.1, happ.2]
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun i : ι => Set.Ioo (left i) (right i)) (fun _ => isOpen_Ioo) hcover
  have hfinite : ∀ x ∈ Set.Icc t (t + 1 / (4 * Q ^ 2)),
      ∃ i ∈ s, x ∈ Set.Icc (left i) (right i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨i, hi, hxi.1.le, hxi.2.le⟩
  have hwidth : ∀ i ∈ s, (t + 1 / (4 * Q ^ 2)) - t < right i - left i := by
    intro i hi
    have hq0 : (0 : ℝ) < i.1.1 := by exact_mod_cast i.2.1
    have hqQ := i.2.2.1
    dsimp [left, right]
    have hfrac : 1 / (4 * Q ^ 2) < 2 / ((i.1.1 : ℝ) * Q) := by
      apply (div_lt_div_iff₀ (by positivity : 0 < 4 * Q ^ 2) (by positivity : 0 < (i.1.1 : ℝ) * Q)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hqQ hQ0.le]
    convert hfrac using 1 <;> ring
  obtain ⟨i, hi, j, hj, htwo⟩ := two_interval_subcover s left right
    (le_add_of_nonneg_right (by positivity)) hwidth hfinite
  exact ⟨i.1.1, i.2.1, i.2.2.1, i.1.2, i.2.2.2,
    j.1.1, j.2.1, j.2.2.1, j.1.2, j.2.2.2, htwo⟩
/-- A nonnegative integral over a two set cover is bounded by the two set integrals. -/
theorem integral_two_cover (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (s a b : Set ℝ) (hma : MeasurableSet a) (hmb : MeasurableSet b)
    (ha : IntegrableOn f a) (hb : IntegrableOn f b) (hcover : s ⊆ a ∪ b) :
    (∫ x in s, f x) ≤ (∫ x in a, f x) + ∫ x in b, f x := by
  have hunion : a ∪ b = a ∪ (b \ a) := by ext x; simp
  calc
    _ ≤ ∫ x in a ∪ b, f x := setIntegral_mono_set (ha.union hb)
      (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall (fun _ h => hcover h))
    _ = (∫ x in a, f x) + ∫ x in b \ a, f x := by
      rw [hunion, setIntegral_union disjoint_sdiff_self_right (hmb.diff hma) ha
        (hb.mono_set Set.diff_subset)]
    _ ≤ (∫ x in a, f x) + ∫ x in b, f x := by
      apply add_le_add le_rfl
      exact setIntegral_mono_set (s := b \ a) hb (Filter.Eventually.of_forall hf)
        (Filter.Eventually.of_forall (fun _ h => h.1))

/-- The prime exponential sum is bounded by the sum of its nonnegative coefficients. -/
theorem primeSum_norm_le (M : ℕ) (α : ℝ) :
    ‖Decomp88.primeSum M α‖ ≤ ∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n := by
  unfold Decomp88.primeSum
  calc
    _ ≤ ∑ n ∈ range (M + 1), ‖(ArithmeticFunction.vonMangoldt n : ℂ) * Kernel.e ((n : ℝ) * α)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [norm_mul, Kernel.e, Complex.norm_exp, Real.norm_eq_abs,
        abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

/-- All punctured arc prime second moments are uniformly bounded when Q is at least two. -/
theorem punctured_moment_le (M : ℕ) (N B Q : ℝ) (q : ℕ) (a : ℤ)
    (hQ : 2 ≤ Q) (hq : 0 < q) :
    (∫ α in Decomp88.puncturedArc N B Q q a, ‖Decomp88.primeSum M α‖ ^ 2) ≤
      (∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n) ^ 2 := by
  let K := (∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n) ^ 2
  let δ := 1 / ((q : ℝ) * Q)
  have hQ0 : 0 < Q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlength : 2 * δ ≤ 1 := by
    dsimp [δ]
    rw [mul_one_div, div_le_one (by positivity : 0 < (q : ℝ) * Q)]
    nlinarith
  have hcont : Continuous (fun α : ℝ => ‖Decomp88.primeSum M α‖ ^ 2) := by
    unfold Decomp88.primeSum Kernel.e
    fun_prop
  calc
    _ ≤ ∫ α in Set.Icc ((a : ℝ) / q - δ) ((a : ℝ) / q + δ), ‖Decomp88.primeSum M α‖ ^ 2 := by
      apply setIntegral_mono_set hcont.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => h.1)
    _ ≤ ∫ α in Set.Icc ((a : ℝ) / q - δ) ((a : ℝ) / q + δ), K := by
      apply integral_mono hcont.integrableOn_Icc continuous_const.integrableOn_Icc
      intro α
      exact pow_le_pow_left₀ (norm_nonneg _) (primeSum_norm_le M α) 2
    _ = K * (2 * δ) := by
      rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith :
        0 ≤ (a : ℝ) / q + δ - ((a : ℝ) / q - δ)), smul_eq_mul]
      ring
    _ ≤ _ := by dsimp [K]; nlinarith [sq_nonneg (∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n)]

/-- The supremum defining the local mass is bounded above for every admissible order. -/
theorem localMass_bddAbove (M : ℕ) (N B Q : ℝ) (hQ : 2 ≤ Q) :
    BddAbove {x | ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ a : ℤ,
      Nat.Coprime a.natAbs q ∧ x = ∫ α in Decomp88.puncturedArc N B Q q a,
        ‖Decomp88.primeSum M α‖ ^ 2} := by
  refine ⟨(∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n) ^ 2, ?_⟩
  rintro x ⟨q, hq, hqQ, a, hcop, rfl⟩
  exact punctured_moment_le M N B Q q a hQ hq


end
end LeanLab.Perelli1996.Farey103
